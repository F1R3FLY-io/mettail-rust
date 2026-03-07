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
use crate::recursive::RDRuleInfo;

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

/// G1 Phase 1: Check whether the fallback `parse_Cat_own` is dead code for a
/// deterministic cross-category arm dispatching on token T.
///
/// Returns `true` when T cannot be handled by `parse_Cat_own` — meaning the
/// save/restore can be eliminated and the arm can commit directly.
///
/// The fallback is dead when:
/// 1. T ∉ FIRST(target_category) — already guaranteed by deterministic classification
/// 2. T is not in any cast rule source's unique-to-source tokens for this target
/// 3. T is not an RD rule dispatch token for this target category
///
/// When any of these fail, `parse_Cat_own` could handle T via a cast arm or
/// RD rule, so save/restore must be retained.
fn is_deterministic_fallback_dead(
    token: &str,
    target_category: &str,
    cast_rules: &[CastRule],
    first_sets: &HashMap<String, FirstSet>,
    rd_rules: &[RDRuleInfo],
) -> bool {
    let target_first = match first_sets.get(target_category) {
        Some(f) => f,
        None => return true, // No FIRST set → nothing can catch T
    };

    // Check 1: T should not be in target's own FIRST set (already guaranteed
    // by deterministic classification, but verify defensively)
    if target_first.contains(token) {
        return false;
    }

    // Check 2: Could any cast rule targeting this category catch T?
    // A cast arm for source S is emitted when T ∈ FIRST(S) \ FIRST(target).
    // Since T ∉ FIRST(target) (check 1), we only need T ∈ FIRST(S).
    for cast in cast_rules {
        if cast.target_category != target_category {
            continue;
        }
        if let Some(source_first) = first_sets.get(&cast.source_category) {
            if source_first.contains(token) {
                return false; // Cast arm would catch T
            }
        }
    }

    // Check 3: Could an RD rule in the target category dispatch on T?
    // RD rules dispatch on their first terminal, which appears in FIRST(target).
    // Since we already checked T ∉ FIRST(target), this is redundant — but
    // verify defensively in case FIRST set computation misses an RD token.
    for rd_rule in rd_rules {
        if rd_rule.category != target_category {
            continue;
        }
        if let Some(crate::recursive::RDSyntaxItem::Terminal(t)) = rd_rule.items.first() {
            if terminal_to_variant_name(t) == token {
                return false;
            }
        }
    }

    true
}

/// Write weight-ordered dispatch code for a category using WFST prediction.
///
/// Consults the prediction WFST to order dispatch arms by weight.
/// `composed_resolutions` (when `Some`) provides weight lookups for ambiguous
/// tokens; `weight_map` provides weights for deterministic tokens.  Both are
/// used for arm ordering only — save/restore is always emitted for both
/// deterministic (defense-in-depth) and ambiguous (backtracking) arms.
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
    optimization_gates: &crate::cost_benefit::OptimizationGates,
    dead_rules: &std::collections::HashSet<String>,
    rd_rules: &[RDRuleInfo],
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

    // (composed_handled removed: all ambiguous tokens are now grouped by source_category)

    for rule in cross_category_rules {
        // A4: Skip dead cross-category rules when enhanced DCE is enabled
        if optimization_gates.enhanced_dce && dead_rules.contains(&rule.label) {
            continue;
        }

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

                // Ambiguous tokens — collect all for grouped source-category emission.
                // Unlike the old composed-dispatch path (which emitted only the
                // single "winning" rule per token), we group by source_category
                // and emit an inner operator match so that ALL operators sharing
                // the same FIRST token are tried.
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
    //
    // G1 Phase 1: When backtracking_elimination is enabled and the fallback
    // `parse_Cat_own` is provably dead (token T cannot be handled by any
    // cast arm or RD rule in the target category), emit committed codegen
    // without save/restore. Otherwise, retain defense-in-depth save/restore.
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

        // C3: Thread parent weight into child category
        let src_upper = source_cat.to_uppercase();

        // G1: Check if fallback is provably dead
        let fallback_dead = optimization_gates.backtracking_elimination
            && is_deterministic_fallback_dead(token, category, cast_rules, first_sets, rd_rules);

        if rules.len() == 1 {
            let (label, op_variant, _operator) = &rules[0];
            if fallback_dead {
                // G1: Committed codegen — no save/restore needed
                write!(
                    arm,
                    " => {{ \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        let left = parse_{}(tokens, pos, 0)?; \
                        expect_token(tokens, pos, |t| matches!(t, Token::{}), \"operator after cross-category expression\")?; \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        let right = parse_{}(tokens, pos, 0)?; \
                        return Ok({}::{}(Box::new(left), Box::new(right))); \
                    }}",
                    source_cat, op_variant, source_cat, category, label,
                )
                .unwrap();
            } else {
                // Defense-in-depth: save/restore with fallback
                write!(
                    arm,
                    " => {{ \
                        let saved = *pos; \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                            if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                                *pos += 1; \
                                PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                                let right = parse_{}(tokens, pos, 0)?; \
                                return Ok({}::{}(Box::new(left), Box::new(right))); \
                            }} \
                        }} \
                        *pos = saved; \
                        parse_{}_own(tokens, pos, min_bp) \
                    }}",
                    source_cat, op_variant, source_cat, category, label, category,
                )
                .unwrap();
            }
        } else {
            if fallback_dead {
                // G1: Committed codegen for multi-operator arms — no save/restore
                write!(
                    arm,
                    " => {{ \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        let left = parse_{}(tokens, pos, 0)?; \
                        if *pos < tokens.len() {{ \
                            match &tokens[*pos].0 {{",
                    source_cat,
                )
                .unwrap();

                for (label, op_variant, _operator) in rules {
                    write!(
                        arm,
                        "                Token::{} => {{ \
                            *pos += 1; \
                            PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                            let right = parse_{}(tokens, pos, 0)?; \
                            return Ok({}::{}(Box::new(left), Box::new(right))); \
                        }},",
                        op_variant, source_cat, category, label,
                    )
                    .unwrap();
                }

                write!(
                    arm,
                    "                _ => {{ return Err(ParseError::UnexpectedToken {{ \
                        expected: Cow::Borrowed(\"operator after cross-category expression\"), \
                        found: format_token_friendly(&tokens[*pos].0), \
                        range: tokens[*pos].1, \
                        hint: None, \
                    }}); }} \
                                }} \
                            }} else {{ \
                                return Err(ParseError::UnexpectedEof {{ \
                                    expected: Cow::Borrowed(\"operator after cross-category expression\"), \
                                    range: tokens[tokens.len()-1].1, \
                                    hint: None, \
                                }}); \
                            }} \
                        }}",
                )
                .unwrap();
            } else {
                // Defense-in-depth: save/restore with fallback
                write!(
                    arm,
                    " => {{ \
                        let saved = *pos; \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                            if *pos < tokens.len() {{ \
                                match &tokens[*pos].0 {{",
                    source_cat,
                )
                .unwrap();

                for (label, op_variant, _operator) in rules {
                    write!(
                        arm,
                        "                Token::{} => {{ \
                            *pos += 1; \
                            PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                            let right = parse_{}(tokens, pos, 0)?; \
                            return Ok({}::{}(Box::new(left), Box::new(right))); \
                        }},",
                        op_variant, source_cat, category, label,
                    )
                    .unwrap();
                }

                arm.push_str(
                    "                _ => {} \
                                } \
                            } \
                        } \
                        *pos = saved;",
                );
                write!(arm, " parse_{}_own(tokens, pos, min_bp) }}", category).unwrap();
            }
        }
        dispatch_arms.push((arm, arm_weight));
    }

    // Emit ambiguous arms — group by source_category so ALL operators
    // sharing the same FIRST token and source category are tried.
    // E.g., for `(Bool, Ident)` with source Int: EqInt(==), GtInt(>), LtInt(<), etc.
    // are all emitted in an inner operator match after a single parse_Int attempt.
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

        // Best weight for arm ordering: prefer composed resolution, else WFST
        let ambig_weight = composed_resolutions
            .and_then(|cr| cr.get(&(category.to_string(), token.clone())))
            .map(|(_, w)| *w)
            .or_else(|| {
                prediction_wfst.predict(&token)
                    .first()
                    .map(|wa| wa.weight.value())
            })
            .unwrap_or(f64::INFINITY);

        // Group rules by source_category, preserving weight order:
        // the first occurrence of each source_category (from the weight-sorted
        // rules_and_ops) determines the group's position in the try-order.
        let mut by_source: Vec<(String, Vec<(&CrossCategoryRule, String)>)> = Vec::new();
        let mut seen_sources: HashMap<String, usize> = HashMap::new();
        for (rule, op) in &rules_and_ops {
            if let Some(&idx) = seen_sources.get(&rule.source_category) {
                by_source[idx].1.push((*rule, op.clone()));
            } else {
                seen_sources.insert(rule.source_category.clone(), by_source.len());
                by_source.push((rule.source_category.clone(), vec![(*rule, op.clone())]));
            }
        }

        let mut arm = String::new();
        write_token_pattern(&mut arm, &token);
        arm.push_str(" => {");
        arm.push_str("let saved = *pos;");

        // C3: Thread parent weight into child category for globally coherent
        // disambiguation. Before calling parse_SourceCat, set its PARENT_WEIGHT
        // to the current category's running weight.
        for (source_cat, source_rules) in &by_source {
            let source_upper = source_cat.to_uppercase();
            let cat_lower = category;

            write!(
                arm,
                "PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                 if let Ok(left) = parse_{}(tokens, pos, 0) {{",
                source_cat,
            )
            .unwrap();

            if source_rules.len() == 1 {
                // Single operator for this source category — peek check
                let (rule, op) = &source_rules[0];
                write!(
                    arm,
                    "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                        *pos += 1; \
                        PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                        let right = parse_{}(tokens, pos, 0)?; \
                        return Ok({}::{}(Box::new(left), Box::new(right))); \
                    }}",
                    op, source_cat, category, rule.label,
                )
                .unwrap();
            } else {
                // Multiple operators for this source category — inner match
                arm.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");
                for (rule, op) in source_rules {
                    write!(
                        arm,
                        "Token::{} => {{ \
                            *pos += 1; \
                            PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                            let right = parse_{}(tokens, pos, 0)?; \
                            return Ok({}::{}(Box::new(left), Box::new(right))); \
                        }},",
                        op, source_cat, category, rule.label,
                    )
                    .unwrap();
                }
                arm.push_str("_ => {} } }");
            }

            // Close `if let Ok` and restore position for next source_category
            arm.push_str("} *pos = saved;");
        }

        // Final fallback: no cross-category rule matched — try own parser
        write!(arm, "parse_{}_own(tokens, pos, min_bp)", category).unwrap();
        arm.push_str("}");

        dispatch_arms.push((arm, ambig_weight));
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
                // C3: Thread parent weight into child category for cast calls.
                let source_upper = rule.source_category.to_uppercase();
                let cat_lower = category;
                write!(
                    arm,
                    " => {{ \
                        PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                        let val = parse_{}(tokens, pos, 0)?; \
                        Ok({}::{}(Box::new(val))) \
                    }}",
                    rule.source_category, rule.target_category, rule.label,
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

    // A2 (Hot/Cold Path Splitting): Partition dispatch arms by weight threshold.
    // Hot arms (weight < threshold) are inlined in the main dispatch function for
    // L1 i-cache locality. Cold arms (weight ≥ threshold) are emitted in a separate
    // #[cold] #[inline(never)] helper to reduce the main function's instruction
    // footprint. NFA-ambiguous categories have inherently cold arms (weight ≥ 0.5).
    //
    // Weight scale:  Direct/Grouping=0.0, Cast/Backtrack=0.5, Lookahead=1.0+, Variable=2.0
    // Threshold 1.0: Lookahead and Variable paths are cold; Direct/Cast are hot.
    //
    // A3: Gated by `optimization_gates.hot_cold_splitting`. When disabled, all arms
    // are inlined regardless of weight (no split emitted).
    const COLD_THRESHOLD: f64 = 1.0;

    let cold_start_idx = if optimization_gates.hot_cold_splitting {
        dispatch_arms
            .iter()
            .position(|(_, w)| *w >= COLD_THRESHOLD)
    } else {
        None // A3: hot/cold splitting disabled — all arms inline
    };

    // Only split when there are both hot AND cold arms. If all arms are cold
    // (cold_idx == 0), there's no benefit to splitting — just emit everything inline.
    let has_split = cold_start_idx
        .map_or(false, |idx| idx > 0 && idx < dispatch_arms.len());

    if has_split {
        let cold_idx = cold_start_idx.expect("has_split checked above");
        let cold_arms: Vec<&str> = dispatch_arms[cold_idx..]
            .iter()
            .map(|(text, _)| text.as_str())
            .collect();

        // Emit cold helper with fallback
        write!(
            buf,
            "#[cold] #[inline(never)] \
            fn parse_{cat}_cold<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                min_bp: u8, \
            ) -> Result<{cat}, ParseError> {{ \
                match &tokens[*pos].0 {{ {cold_arms}, \
                    _ => parse_{cat}_own(tokens, pos, min_bp) \
                }} \
            }}",
            cat = category,
            cold_arms = cold_arms.join(","),
        )
        .unwrap();

        // Hot arms only + wildcard routing to cold helper
        let hot_arms: Vec<&str> = dispatch_arms[..cold_idx]
            .iter()
            .map(|(text, _)| text.as_str())
            .collect();

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
                        expected: Cow::Borrowed(\"{cat}\"), \
                        range: eof_range, \
                        hint: None, \
                    }}); \
                }} \
                match &tokens[*pos].0 {{ {hot_arms}, \
                    _ => parse_{cat}_cold(tokens, pos, min_bp) \
                }} \
            }}",
            cat = category,
            hot_arms = hot_arms.join(","),
        )
        .unwrap();
    } else {
        // No cold arms — emit all arms inline with fallback (original path)
        dispatch_arms.push((
            format!("_ => parse_{}_own(tokens, pos, min_bp)", category),
            f64::INFINITY,
        ));

        let arms: Vec<&str> = dispatch_arms.iter().map(|(text, _)| text.as_str()).collect();

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
                        expected: Cow::Borrowed(\"{cat}\"), \
                        range: eof_range, \
                        hint: None, \
                    }}); \
                }} \
                match &tokens[*pos].0 {{ {arms} }} \
            }}",
            cat = category,
            arms = arms.join(","),
        )
        .unwrap();
    }
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
