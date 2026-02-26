//! Category dispatch and cross-category rule handling.
//!
//! Generates the top-level entry points for parsing each category, including:
//! - Cross-category rules (e.g., `Int "==" Int → Bool`)
//! - Cast rules (e.g., `Int → Proc`)
//! - Prediction-based dispatch using FIRST set analysis

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::prediction::{CrossCategoryOverlap, FirstSet};

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

/// Write the dispatch code for a category that includes cross-category
/// and cast rules.
///
/// This wraps the core Pratt parser with additional dispatch logic for:
/// 1. Tokens that unambiguously belong to a cross-category parse path
/// 2. Tokens that need save/restore backtracking
/// 3. Cast rules that wrap one category into another
pub fn write_category_dispatch(
    buf: &mut String,
    category: &str,
    cross_category_rules: &[CrossCategoryRule],
    cast_rules: &[CastRule],
    overlaps: &BTreeMap<(String, String), CrossCategoryOverlap>,
    first_sets: &BTreeMap<String, FirstSet>,
) {
    if cross_category_rules.is_empty() && cast_rules.is_empty() {
        return;
    }

    let mut dispatch_arms: Vec<String> = Vec::new();

    // Collect deterministic cross-category arms grouped by (source_category, token)
    // to avoid duplicate match arms when multiple rules share the same source
    // (e.g., EqInt, GtInt, LtInt all dispatch from Int's FIRST tokens).
    let mut deterministic_by_token: BTreeMap<(String, String), Vec<(String, String, String)>> =
        BTreeMap::new();

    // Generate cross-category dispatch
    for rule in cross_category_rules {
        let overlap_key = (rule.source_category.clone(), category.to_string());
        let overlap = overlaps.get(&overlap_key);

        let source_first = first_sets.get(&rule.source_category);

        if let Some(source_first) = source_first {
            let target_first = first_sets.get(category);

            if let Some(target_first) = target_first {
                let unique_to_source = source_first.difference(target_first);
                let op_variant = terminal_to_variant_name(&rule.operator);

                // Deterministic tokens: group by (source_category, token)
                for token in &unique_to_source.tokens {
                    deterministic_by_token
                        .entry((rule.source_category.clone(), token.clone()))
                        .or_default()
                        .push((rule.label.clone(), op_variant.clone(), rule.operator.clone()));
                }

                // Ambiguous tokens: save/restore backtracking (unchanged)
                if let Some(overlap) = overlap {
                    for token in &overlap.ambiguous_tokens.tokens {
                        let mut arm = String::new();
                        write_token_pattern(&mut arm, token);
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
                            rule.source_category,
                            op_variant,
                            rule.source_category,
                            category,
                            rule.label,
                            category,
                        )
                        .unwrap();
                        dispatch_arms.push(arm);
                    }
                }
            }
        }
    }

    // Emit deterministic arms — one arm per (source_category, token)
    for ((source_cat, token), rules) in &deterministic_by_token {
        let mut arm = String::new();
        write_token_pattern(&mut arm, token);

        if rules.len() == 1 {
            // Single rule for this token — emit direct parse
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
            // Multiple rules share this token — parse left, then match operator
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

            // Fallback for unexpected operator
            arm.push_str("other => { \
                let range = tokens[*pos].1; \
                Err(ParseError::UnexpectedToken { \
                    expected: \"comparison operator\", \
                    found: format!(\"{:?}\", other), \
                    range, \
                }) \
            }");
            arm.push_str(" } }");
        }
        dispatch_arms.push(arm);
    }

    // Generate cast rule dispatch
    for rule in cast_rules {
        let source_first = first_sets.get(&rule.source_category);
        let target_first = first_sets.get(category);

        if let (Some(source_first), Some(target_first)) = (source_first, target_first) {
            // Tokens unique to the source category trigger deterministic cast
            let unique_to_source = source_first.difference(target_first);

            for token in &unique_to_source.tokens {
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
                dispatch_arms.push(arm);
            }
        }
    }

    if dispatch_arms.is_empty() {
        return;
    }

    // Add fallback to own-category parsing
    dispatch_arms.push(format!("_ => parse_{}_own(tokens, pos, min_bp)", category));

    // Generate the wrapping dispatch function
    write!(
        buf,
        "fn parse_{cat}<'a>(\
            tokens: &[(Token<'a>, Span)], \
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
        arms = dispatch_arms.join(","),
    )
    .unwrap();
}

/// Write weight-ordered dispatch code for a category using WFST prediction.
///
/// Like `write_category_dispatch()` but consults the prediction WFST to order
/// backtracking alternatives by weight (lowest first = most likely). For
/// deterministic tokens (unique to source category), the behavior is identical.
/// For ambiguous tokens, the WFST determines which path is tried first in
/// save/restore backtracking.
///
/// The first (lowest-weight) path has no save/restore overhead. Subsequent
/// paths use save/restore.
#[cfg(feature = "wfst")]
pub fn write_category_dispatch_weighted(
    buf: &mut String,
    category: &str,
    cross_category_rules: &[CrossCategoryRule],
    cast_rules: &[CastRule],
    overlaps: &BTreeMap<(String, String), CrossCategoryOverlap>,
    first_sets: &BTreeMap<String, FirstSet>,
    prediction_wfst: &crate::wfst::PredictionWfst,
) {
    if cross_category_rules.is_empty() && cast_rules.is_empty() {
        return;
    }

    let mut dispatch_arms: Vec<String> = Vec::new();

    // Collect all ambiguous tokens and their cross-category rules,
    // then sort by WFST weight
    let mut ambiguous_by_token: BTreeMap<String, Vec<(&CrossCategoryRule, String)>> =
        BTreeMap::new();
    // Collect deterministic arms grouped by (source_category, token) to avoid
    // duplicate match arms when multiple rules share the same source category.
    let mut deterministic_by_token: BTreeMap<(String, String), Vec<(String, String, String)>> =
        BTreeMap::new();

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

                // Ambiguous: collect for weight-ordered emission
                if let Some(overlap) = overlap {
                    for token in &overlap.ambiguous_tokens.tokens {
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

            arm.push_str("other => { \
                let range = tokens[*pos].1; \
                Err(ParseError::UnexpectedToken { \
                    expected: \"comparison operator\", \
                    found: format!(\"{:?}\", other), \
                    range, \
                }) \
            }");
            arm.push_str(" } }");
        }
        dispatch_arms.push(arm);
    }

    // Emit ambiguous arms, sorted by WFST weight within each token group
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
            dispatch_arms.push(arm);
        }
    }

    // Generate cast rule dispatch (identical to unweighted — deterministic)
    for rule in cast_rules {
        let source_first = first_sets.get(&rule.source_category);
        let target_first = first_sets.get(category);

        if let (Some(source_first), Some(target_first)) = (source_first, target_first) {
            let unique_to_source = source_first.difference(target_first);

            for token in &unique_to_source.tokens {
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
                dispatch_arms.push(arm);
            }
        }
    }

    if dispatch_arms.is_empty() {
        return;
    }

    // Add fallback to own-category parsing
    dispatch_arms.push(format!("_ => parse_{}_own(tokens, pos, min_bp)", category));

    // Emit WFST weight summary as comment
    writeln!(
        buf,
        "// WFST-ordered dispatch for {cat}: {n} arms",
        cat = category,
        n = dispatch_arms.len(),
    )
    .unwrap();

    // Generate the wrapping dispatch function
    write!(
        buf,
        "fn parse_{cat}<'a>(\
            tokens: &[(Token<'a>, Span)], \
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
        arms = dispatch_arms.join(","),
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
    let mut categories = std::collections::BTreeSet::new();

    for rule in cross_category_rules {
        categories.insert(rule.result_category.clone());
    }

    categories.into_iter().collect()
}
