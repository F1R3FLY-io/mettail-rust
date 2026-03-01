//! Category dispatch and cross-category rule handling.
//!
//! Generates the top-level entry points for parsing each category, including:
//! - Cross-category rules (e.g., `Int "==" Int → Bool`)
//! - Cast rules (e.g., `Int → Proc`)
//! - Prediction-based dispatch using FIRST set analysis

use std::collections::HashMap;
use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::prediction::{CrossCategoryOverlap, FirstSet};

/// Deterministic cross-category arms grouped by (source_category, token).
/// Each entry maps to a list of (label, op_variant, operator) tuples.
type DeterministicArmMap = HashMap<(String, String), Vec<(String, String, String)>>;

/// A cross-category rule that produces a result in one category from
/// operands in another category.
#[derive(Debug, Clone)]
pub struct CrossCategoryRule {
    /// Constructor label (e.g., "Eq", "Lt").
    pub label: String,
    /// Source category (operand type, e.g., "Int").
    pub source_category: String,
    /// Result category (e.g., "Bool").
    pub result_category: String,
    /// The infix operator terminal (e.g., "==", "<").
    pub operator: String,
    /// Whether save/restore is needed (ambiguous FIRST overlap).
    pub needs_backtrack: bool,
}

/// A cast rule that embeds one category into another.
#[derive(Debug, Clone)]
pub struct CastRule {
    /// Constructor label (e.g., "CastInt", "CastBool").
    pub label: String,
    /// Source category (e.g., "Int").
    pub source_category: String,
    /// Target category (e.g., "Proc").
    pub target_category: String,
}

/// Write a token match pattern string for a given token name.
fn write_token_pattern(buf: &mut String, token: &str) {
    match token {
        "Ident" => buf.push_str("Token::Ident(_)"),
        "Integer" => buf.push_str("Token::Integer(_)"),
        "Float" => buf.push_str("Token::Float(_)"),
        "Boolean" => buf.push_str("Token::Boolean(_)"),
        "StringLit" => buf.push_str("Token::StringLit(_)"),
        _ => write!(buf, "Token::{}", token).unwrap(),
    }
}

/// Write weight-ordered dispatch code for a category using WFST prediction.
///
/// Consults the prediction WFST to order and resolve ambiguous alternatives.
/// When `composed_resolutions` is `Some`, ambiguous tokens are resolved
/// deterministically via the precomputed composed dispatch table — no
/// save/restore backtracking is emitted.
pub fn write_category_dispatch(
    buf: &mut String,
    category: &str,
    cross_category_rules: &[CrossCategoryRule],
    cast_rules: &[CastRule],
    overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    first_sets: &HashMap<String, FirstSet>,
    prediction_wfst: &crate::wfst::PredictionWfst,
    composed_resolutions: Option<&HashMap<(String, String), (String, f64)>>,
    weight_map: Option<&HashMap<(String, String), f64>>,
) {
    if cross_category_rules.is_empty() && cast_rules.is_empty() {
        return;
    }

    // Arms carry (code_string, weight) for sorting by weight before emission.
    let mut dispatch_arms: Vec<(String, f64)> = Vec::new();

    // Collect all ambiguous tokens and their cross-category rules,
    // then sort by WFST weight
    let mut ambiguous_by_token: HashMap<String, Vec<(&CrossCategoryRule, String)>> =
        HashMap::new();
    // Collect deterministic arms grouped by (source_category, token) to avoid
    // duplicate match arms when multiple rules share the same source category.
    let mut deterministic_by_token: DeterministicArmMap = DeterministicArmMap::new();

    // Track ambiguous tokens already handled by composed dispatch
    let mut composed_handled: std::collections::HashSet<String> = std::collections::HashSet::new();

    for rule in cross_category_rules {
        let overlap_key = (rule.source_category.clone(), category.to_string());
        let overlap = overlaps.get(&overlap_key);
        let source_first = first_sets.get(&rule.source_category);

        if let Some(source_first) = source_first {
            let target_first = first_sets.get(category);

            if let Some(target_first) = target_first {
                let unique_to_source = source_first.difference(target_first);
                let op_variant = terminal_to_variant_name(&rule.operator);

                // Deterministic: group by (source_category, token)
                for token in &unique_to_source.tokens {
                    deterministic_by_token
                        .entry((rule.source_category.clone(), token.clone()))
                        .or_default()
                        .push((rule.label.clone(), op_variant.clone(), rule.operator.clone()));
                }

                // Ambiguous tokens
                if let Some(overlap) = overlap {
                    for token in &overlap.ambiguous_tokens.tokens {
                        // Check if composed dispatch has resolved this
                        if let Some(resolutions) = composed_resolutions {
                            let key = (category.to_string(), token.clone());
                            if let Some((winning_rule, weight)) = resolutions.get(&key) {
                                if !composed_handled.contains(token) {
                                    composed_handled.insert(token.clone());
                                    if winning_rule == &rule.label {
                                        let mut arm = String::new();
                                        write_token_pattern(&mut arm, token);
                                        write!(
                                            arm,
                                            " => {{ \
                                                let left = parse_{}(tokens, pos, 0)?; \
                                                expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?; \
                                                let right = parse_{}(tokens, pos, 0)?; \
                                                Ok({}::{}(Box::new(left), Box::new(right))) \
                                            }}",
                                            rule.source_category,
                                            op_variant,
                                            rule.operator,
                                            rule.source_category,
                                            category,
                                            rule.label,
                                        )
                                        .unwrap();
                                        dispatch_arms.push((arm, *weight));
                                    }
                                    /* else: winning rule is own-category — handled by fallback */
                                }
                                continue;
                            }
                        }

                        // No composed resolution — collect for weight-ordered emission
                        ambiguous_by_token
                            .entry(token.clone())
                            .or_default()
                            .push((rule, op_variant.clone()));
                    }
                }
            }
        }
    }

    // Emit deterministic arms — one arm per (source_category, token)
    for ((source_cat, token), rules) in &deterministic_by_token {
        // Look up weight from complete weight map, composed resolutions, or WFST
        let arm_weight = weight_map
            .and_then(|wm| wm.get(&(category.to_string(), token.clone())).copied())
            .or_else(|| {
                composed_resolutions
                    .and_then(|cr| cr.get(&(category.to_string(), token.clone())))
                    .map(|(_, w)| *w)
            })
            .unwrap_or(f64::INFINITY);

        let mut arm = String::new();
        write_token_pattern(&mut arm, token);

        if rules.len() == 1 {
            let (label, op_variant, operator) = &rules[0];
            write!(
                arm,
                " => {{ \
                    let left = parse_{}(tokens, pos, 0)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?; \
                    let right = parse_{}(tokens, pos, 0)?; \
                    Ok({}::{}(Box::new(left), Box::new(right))) \
                }}",
                source_cat, op_variant, operator, source_cat, category, label,
            )
            .unwrap();
        } else {
            write!(arm, " => {{ let left = parse_{}(tokens, pos, 0)?; ", source_cat).unwrap();
            arm.push_str("if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof { expected: \"operator\", range: eof_range }); \
            } ");
            arm.push_str("match &tokens[*pos].0 { ");

            for (label, op_variant, _operator) in rules {
                write!(
                    arm,
                    "Token::{} => {{ \
                        *pos += 1; \
                        let right = parse_{}(tokens, pos, 0)?; \
                        Ok({}::{}(Box::new(left), Box::new(right))) \
                    }},",
                    op_variant, source_cat, category, label,
                )
                .unwrap();
            }

            arm.push_str(
                "other => { \
                let range = tokens[*pos].1; \
                Err(ParseError::UnexpectedToken { \
                    expected: \"comparison operator\", \
                    found: format!(\"{:?}\", other), \
                    range, \
                }) \
            }",
            );
            arm.push_str(" } }");
        }
        dispatch_arms.push((arm, arm_weight));
    }

    // Emit ambiguous arms (only those NOT resolved by composed dispatch)
    for (token, mut rules_and_ops) in ambiguous_by_token {
        // Sort rules by WFST weight for this token
        rules_and_ops.sort_by(|(rule_a, _), (rule_b, _)| {
            let weight_a = prediction_wfst.predict(&token)
                .iter()
                .find(|wa| matches!(&wa.action, crate::prediction::DispatchAction::CrossCategory { rule_label, .. } if *rule_label == rule_a.label))
                .map(|wa| wa.weight)
                .unwrap_or(crate::automata::semiring::TropicalWeight::new(f64::INFINITY));
            let weight_b = prediction_wfst.predict(&token)
                .iter()
                .find(|wa| matches!(&wa.action, crate::prediction::DispatchAction::CrossCategory { rule_label, .. } if *rule_label == rule_b.label))
                .map(|wa| wa.weight)
                .unwrap_or(crate::automata::semiring::TropicalWeight::new(f64::INFINITY));
            weight_a.cmp(&weight_b)
        });

        // Emit: first rule gets no save/restore overhead (most likely)
        if let Some((first_rule, first_op)) = rules_and_ops.first() {
            let ambig_weight = prediction_wfst.predict(&token)
                .first()
                .map(|wa| wa.weight.value())
                .unwrap_or(f64::INFINITY);

            let mut arm = String::new();
            write_token_pattern(&mut arm, &token);
            write!(
                arm,
                " => {{ \
                    let saved = *pos; \
                    if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                            *pos += 1; \
                            let right = parse_{}(tokens, pos, 0)?; \
                            return Ok({}::{}(Box::new(left), Box::new(right))); \
                        }} \
                    }} \
                    *pos = saved; \
                    parse_{}_own(tokens, pos, min_bp) \
                }}",
                first_rule.source_category,
                first_op,
                first_rule.source_category,
                category,
                first_rule.label,
                category,
            )
            .unwrap();
            dispatch_arms.push((arm, ambig_weight));
        }
    }

    // Generate cast rule dispatch
    for rule in cast_rules {
        let source_first = first_sets.get(&rule.source_category);
        let target_first = first_sets.get(category);

        if let (Some(source_first), Some(target_first)) = (source_first, target_first) {
            let unique_to_source = source_first.difference(target_first);

            for token in &unique_to_source.tokens {
                let arm_weight = weight_map
                    .and_then(|wm| wm.get(&(category.to_string(), token.clone())).copied())
                    .unwrap_or(f64::INFINITY);

                let mut arm = String::new();
                write_token_pattern(&mut arm, token);
                write!(
                    arm,
                    " => {{ \
                        let val = parse_{}(tokens, pos, 0)?; \
                        Ok({}::{}(Box::new(val))) \
                    }}",
                    rule.source_category, category, rule.label,
                )
                .unwrap();
                dispatch_arms.push((arm, arm_weight));
            }
        }
    }

    if dispatch_arms.is_empty() {
        return;
    }

    // Sort by weight: lowest (most likely) first → improves CPU branch prediction.
    dispatch_arms.sort_by(|(_, wa), (_, wb)|
        wa.partial_cmp(wb).unwrap_or(std::cmp::Ordering::Equal));

    // Fallback always last (INFINITY weight ensures it stays at the end)
    dispatch_arms.push((
        format!("_ => parse_{}_own(tokens, pos, min_bp)", category),
        f64::INFINITY,
    ));

    let arms: Vec<&str> = dispatch_arms.iter().map(|(text, _)| text.as_str()).collect();

    // Generate the wrapping dispatch function
    write!(
        buf,
        "fn parse_{cat}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
        ) -> Result<{cat}, ParseError> {{ \
            if *pos >= tokens.len() {{ \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof {{ \
                    expected: \"{cat}\", \
                    range: eof_range, \
                }}); \
            }} \
            match &tokens[*pos].0 {{ {arms} }} \
        }}",
        cat = category,
        arms = arms.join(","),
    )
    .unwrap();
}

/// Determine which categories need cross-category dispatch wrappers.
///
/// Only cross-category *infix* rules (e.g., `Int "==" Int → Bool`) need
/// dispatch wrappers. Cast rules (e.g., `Int → Proc`) are handled by the
/// Pratt prefix handler so the Pratt infix loop can continue after the cast.
pub fn categories_needing_dispatch(
    cross_category_rules: &[CrossCategoryRule],
    _cast_rules: &[CastRule],
) -> Vec<String> {
    let mut categories = std::collections::HashSet::new();

    for rule in cross_category_rules {
        categories.insert(rule.result_category.clone());
    }

    categories.into_iter().collect()
}
