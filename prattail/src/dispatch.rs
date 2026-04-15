//! Category dispatch and cross-category rule handling.
//!
//! Generates the top-level entry points for parsing each category, including:
//! - Cross-category rules (e.g., `Int "==" Int → Bool`)
//! - Cast rules (e.g., `Int → Proc`)
//! - Prediction-based dispatch using FIRST set analysis

use std::collections::HashMap;
use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::lint::DiagnosticId;
use crate::prediction::{CrossCategoryOverlap, FirstSet};
use crate::recursive::RDRuleInfo;
use crate::token_id::TokenIdMap;

/// CD03: Threshold for computed goto dispatch activation.
///
/// Categories with dispatch arm counts at or above this threshold use a function
/// pointer table indexed by `token_to_id()` for guaranteed O(1) dispatch.
/// Below this threshold, the compiler's `match` optimization (branch prediction,
/// potential jump table) is sufficient.
const COMPUTED_GOTO_THRESHOLD: usize = 20;

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
pub fn write_token_pattern(buf: &mut String, token: &str) {
    match token {
        "Ident" => buf.push_str("Token::Ident(_)"),
        "Integer" => buf.push_str("Token::Integer(_)"),
        "Float" => buf.push_str("Token::Float(_)"),
        "Boolean" => buf.push_str("Token::Boolean(_)"),
        "StringLit" => buf.push_str("Token::StringLit(_)"),
        _ => write!(buf, "Token::{}", token).unwrap(),
    }
}

/// Generate a `#[cold] #[inline(never)]` helper function for cross-category
/// infix continuation, plus the call site that invokes it.
///
/// The helper runs a mini Pratt infix loop that consumes any subsequent
/// same-category infix operators. It is `#[cold] #[inline(never)]` so its
/// Cat-sized locals (`__lhs`, `rhs`) are NOT pre-allocated in the dispatch
/// wrapper's stack frame — critical for stack safety since the dispatch
/// wrapper is called recursively for every grouping nesting level.
///
/// Must be called once per category before the dispatch arms are emitted.
fn write_cross_cat_continue_fn(buf: &mut String, category: &str) {
    write!(
        buf,
        "#[cold] #[inline(never)] \
        fn cross_cat_continue_{category}<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
            initial_lhs: {category}, \
        ) -> Result<{category}, ParseError> {{ \
            let mut __lhs = initial_lhs; \
            loop {{ \
                if *pos >= tokens.len() {{ break; }} \
                if let Some((l_bp, r_bp)) = infix_bp_{category}(&tokens[*pos].0) {{ \
                    if l_bp < min_bp {{ break; }} \
                    let __op_pos = *pos; \
                    *pos += 1; \
                    match parse_{category}_own(tokens, pos, r_bp) {{ \
                        Ok(rhs) => {{ __lhs = make_infix_{category}(&tokens[__op_pos].0, __lhs, rhs); }} \
                        Err(e) => return Err(e), \
                    }} \
                }} else {{ \
                    break; \
                }} \
            }} \
            Ok(__lhs) \
        }}",
    )
    .unwrap();
}

/// Generate the cross-category infix continuation call site.
///
/// Calls the `#[cold]` helper function to consume subsequent same-category
/// infix operators. Zero Cat-sized locals added to the caller's stack frame.
fn write_cross_cat_continuation(buf: &mut String, category: &str, result_expr: &str) {
    write!(
        buf,
        "return cross_cat_continue_{category}(tokens, pos, min_bp, {result_expr})",
    )
    .unwrap();
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
    token_id_map: Option<&TokenIdMap>,
) {
    if cross_category_rules.is_empty() && cast_rules.is_empty() {
        return;
    }

    // Emit the #[cold] cross-category infix continuation helper function.
    // Must be emitted before the dispatch wrapper so it's visible from match arms.
    if !cross_category_rules.is_empty() {
        write_cross_cat_continue_fn(buf, category);
    }

    // Arms carry (code_string, weight, token_variant_name) for sorting by weight
    // before emission. `token_variant_name` is used by CD03 computed goto to map
    // arms to token IDs in the function pointer table.
    let mut dispatch_arms: Vec<(String, f64, Option<String>)> = Vec::new();

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
                // G1: Committed codegen — no save/restore needed.
                // Peek-then-decide: only enter infix loop if next token is same-cat operator.
                write!(
                    arm,
                    " => {{ \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        let left = parse_{}(tokens, pos, 0)?; \
                        expect_token(tokens, pos, |t| matches!(t, Token::{}), \"operator after cross-category expression\")?; \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        let right = parse_{}(tokens, pos, 0)?; ",
                    source_cat, op_variant, source_cat,
                )
                .unwrap();
                let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, label);
                write_cross_cat_continuation(&mut arm, category, &result_expr);
                arm.push_str(" }");

            } else {
                // Defense-in-depth: save/restore with fallback.
                // On cross-cat success, peek-then-decide: return Ok immediately if
                // no subsequent operator, or enter infix loop if there is one.
                // On RHS parse failure, restore pos and fall through normally.
                write!(
                    arm,
                    " => {{ \
                        let saved = *pos; \
                        PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                        if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                            if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                                let saved_op = *pos; \
                                *pos += 1; \
                                PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                                match parse_{}(tokens, pos, 0) {{ \
                                    Ok(right) => ",
                    source_cat, op_variant, source_cat,
                )
                .unwrap();
                let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, label);
                write_cross_cat_continuation(&mut arm, category, &result_expr);
                write!(
                    arm,
                    "               , \
                                    Err(_) => {{ *pos = saved_op; }} \
                                }} \
                            }} \
                        }} \
                        *pos = saved; \
                        parse_{}_own(tokens, pos, min_bp) \
                    }}",
                    category,
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
                            let right = parse_{}(tokens, pos, 0)?; ",
                        op_variant, source_cat,
                    )
                    .unwrap();
                    let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, label);
                    write_cross_cat_continuation(&mut arm, category, &result_expr);
                    arm.push_str(" },");
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
                // Defense-in-depth: save/restore with fallback.
                // On RHS parse failure, restore pos before operator
                // consumption and fall through to the own-parser fallback
                // (fixes cross-category backtracking).
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
                            let saved_op = *pos; \
                            *pos += 1; \
                            PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                            match parse_{}(tokens, pos, 0) {{ \
                                Ok(right) => ",
                        op_variant, source_cat,
                    )
                    .unwrap();
                    let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, label);
                    write_cross_cat_continuation(&mut arm, category, &result_expr);
                    write!(
                        arm,
                        "               , \
                                Err(_) => {{ *pos = saved_op; }} \
                            }} \
                        }},",
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
        dispatch_arms.push((arm, arm_weight, Some(token.clone())));
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
                // Single operator for this source category — peek check.
                // Peek-then-decide: return Ok immediately if no subsequent operator.
                let (rule, op) = &source_rules[0];
                write!(
                    arm,
                    "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                        let saved_op = *pos; \
                        *pos += 1; \
                        PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                        match parse_{}(tokens, pos, 0) {{ \
                            Ok(right) => ",
                    op, source_cat,
                )
                .unwrap();
                let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, rule.label);
                write_cross_cat_continuation(&mut arm, category, &result_expr);
                write!(
                    arm,
                    "           , \
                            Err(_) => {{ *pos = saved_op; }} \
                        }} \
                    }}",
                )
                .unwrap();
            } else {
                // Multiple operators for this source category — inner match
                // On RHS parse failure, restore pos and fall through to try
                // the next source category (fixes cross-category backtracking).
                arm.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");
                for (rule, op) in source_rules {
                    write!(
                        arm,
                        "Token::{} => {{ \
                            let saved_op = *pos; \
                            *pos += 1; \
                            PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{cat_lower}())); \
                            match parse_{}(tokens, pos, 0) {{ \
                                Ok(right) => ",
                        op, source_cat,
                    )
                    .unwrap();
                    let result_expr = format!("{}::{}(Box::new(left), Box::new(right))", category, rule.label);
                    write_cross_cat_continuation(&mut arm, category, &result_expr);
                    write!(
                        arm,
                        "               , \
                                Err(_) => {{ *pos = saved_op; }} \
                            }} \
                        }},",
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

        dispatch_arms.push((arm, ambig_weight, Some(token.clone())));
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
                dispatch_arms.push((arm, arm_weight, Some(token.clone())));
            }
        }
    }

    if dispatch_arms.is_empty() {
        return;
    }

    // Sort by weight: lowest (most likely) first → improves CPU branch prediction.
    dispatch_arms.sort_by(|(_, wa, _), (_, wb, _)|
        wa.partial_cmp(wb).unwrap_or(std::cmp::Ordering::Equal));

    // ── CD03: Computed Goto Dispatch via Function Pointer Tables ────────
    //
    // When the computed_goto gate is enabled and the category has ≥ COMPUTED_GOTO_THRESHOLD
    // dispatch arms, emit a function pointer table indexed by `token_to_id()` for
    // guaranteed O(1) dispatch. Each dispatch arm becomes a standalone handler function
    // with a unified signature, and unmapped token IDs route to the fallback handler.
    //
    // This supersedes hot/cold splitting (A2) for the dispatch function when active —
    // the function pointer table inherently provides O(1) regardless of arm weight.
    let use_computed_goto = optimization_gates.computed_goto
        && dispatch_arms.len() >= COMPUTED_GOTO_THRESHOLD
        && token_id_map.is_some();

    if use_computed_goto {
        write_computed_goto_dispatch(buf, category, &dispatch_arms, token_id_map.expect("checked above"));
    } else {
        write_match_dispatch(buf, category, &dispatch_arms, optimization_gates);
    }
}

/// CD03: Emit function pointer table dispatch for a category.
///
/// For each dispatch arm, generates a standalone handler function with signature
/// `fn<'a>(&[(Token<'a>, Range)], &mut usize, u8) -> Result<Cat, ParseError>`.
/// Builds a function pointer table indexed by `token_to_id()` where unmapped
/// entries point to the fallback `parse_Cat_own` handler.
///
/// The table is constructed as a local `const`-eligible array inside `parse_Cat`,
/// avoiding static lifetime issues with the generic `'a` parameter.
fn write_computed_goto_dispatch(
    buf: &mut String,
    category: &str,
    dispatch_arms: &[(String, f64, Option<String>)],
    token_id_map: &TokenIdMap,
) {
    let table_size = token_id_map.len();
    let cat_lower = category.to_lowercase();

    // Emit the fallback handler function.
    write!(
        buf,
        "fn dispatch_{cat_lower}_fallback<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            min_bp: u8, \
        ) -> Result<{cat}, ParseError> {{ \
            parse_{cat}_own(tokens, pos, min_bp) \
        }}",
        cat = category,
    )
    .unwrap();

    // Emit one handler function per dispatch arm, extracting the body from the
    // arm string. The arm string format is: "Token::Pattern => { body }"
    // We need to extract the body portion.
    //
    // Build a mapping: token_variant_name → handler_function_name
    let mut token_to_handler: HashMap<String, String> = HashMap::new();

    for (idx, (arm_code, _weight, token_name)) in dispatch_arms.iter().enumerate() {
        let token_variant = match token_name {
            Some(name) => name.clone(),
            None => continue, // Wildcard arm — handled by fallback
        };

        let handler_name = format!("dispatch_{cat_lower}_{idx}");

        // Extract the body from the arm code: find ` => {` and strip the pattern prefix.
        // The arm code starts with the token pattern (e.g., "Token::Plus") followed by
        // " => { ... }". We need just the body (the `{ ... }` block contents).
        let body = extract_arm_body(arm_code);

        write!(
            buf,
            "fn {handler_name}<'a>(\
                tokens: &[(Token<'a>, Range)], \
                pos: &mut usize, \
                min_bp: u8, \
            ) -> Result<{cat}, ParseError> {{ \
                {body} \
            }}",
            cat = category,
        )
        .unwrap();

        token_to_handler.insert(token_variant, handler_name);
    }

    // Build the table entries: for each token ID in [0..table_size), either
    // the handler function or the fallback.
    let fallback_name = format!("dispatch_{cat_lower}_fallback");
    let mut table_entries = Vec::with_capacity(table_size);
    for id in 0..table_size {
        let name = token_id_map.name(id as u16);
        let handler = name
            .and_then(|n| token_to_handler.get(n))
            .map(|h| h.as_str())
            .unwrap_or(&fallback_name);
        table_entries.push(handler.to_string());
    }

    // Emit the dispatch function using the function pointer table.
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
            type DispatchFn<'b> = fn(&[(Token<'b>, Range)], &mut usize, u8) -> Result<{cat}, ParseError>; \
            let table: [DispatchFn<'a>; {table_size}] = [{entries}]; \
            let id = token_to_id(&tokens[*pos].0) as usize; \
            if id < {table_size} {{ \
                table[id](tokens, pos, min_bp) \
            }} else {{ \
                dispatch_{cat_lower}_fallback(tokens, pos, min_bp) \
            }} \
        }}",
        cat = category,
        entries = table_entries.join(","),
    )
    .unwrap();

    // Emit I17 diagnostic
    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
        id: DiagnosticId::I17,
        name: "computed-goto-dispatch",
        severity: crate::lint::LintSeverity::Info,
        category: Some(category.to_string()),
        rule: None,
        message: format!(
            "CD03: computed goto dispatch activated for category `{}`: {} arm(s), table size {}",
            category, dispatch_arms.len(), table_size,
        ),
        hint: None,
        grammar_name: None,
        source_location: None,
    });
}

/// Extract the body of a dispatch arm from its code string.
///
/// The arm code string has the format: `"Token::Pattern => { body }"` or
/// `"Token::Pattern(_) => { body }"`. This function extracts `body` — the
/// content between the first `=> {` and the final `}`.
///
/// If the pattern is not found, returns the entire string as a fallback
/// (safe but may produce suboptimal codegen).
fn extract_arm_body(arm_code: &str) -> &str {
    // Find " => {" which separates the match pattern from the body
    if let Some(arrow_pos) = arm_code.find(" => {") {
        let body_start = arrow_pos + " => {".len();
        // The body extends to the last `}` (which closes the arm block)
        if let Some(body_end) = arm_code.rfind('}') {
            if body_end > body_start {
                return arm_code[body_start..body_end].trim();
            }
        }
    }
    // Fallback: return the whole thing (shouldn't happen for well-formed arms)
    arm_code
}

/// Emit match-based dispatch (the original A2/A3 path).
///
/// Factored out of `write_category_dispatch` to keep the CD03 branch clean.
fn write_match_dispatch(
    buf: &mut String,
    category: &str,
    dispatch_arms: &[(String, f64, Option<String>)],
    optimization_gates: &crate::cost_benefit::OptimizationGates,
) {
    // A2 (Hot/Cold Path Splitting): Partition dispatch arms by weight threshold.
    // Hot arms (weight < threshold) are inlined in the main dispatch function for
    // L1 i-cache locality. Cold arms (weight >= threshold) are emitted in a separate
    // #[cold] #[inline(never)] helper to reduce the main function's instruction
    // footprint. NFA-ambiguous categories have inherently cold arms (weight >= 0.5).
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
            .position(|(_, w, _)| *w >= COLD_THRESHOLD)
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
            .map(|(text, _, _)| text.as_str())
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
            .map(|(text, _, _)| text.as_str())
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
        let mut all_arms = dispatch_arms.to_vec();
        all_arms.push((
            format!("_ => parse_{}_own(tokens, pos, min_bp)", category),
            f64::INFINITY,
            None,
        ));

        let arms: Vec<&str> = all_arms.iter().map(|(text, _, _)| text.as_str()).collect();

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

/// A cross-category prefix arm for inline emission in `_impl`'s prefix match.
///
/// Used by the PDA merge: cross-category dispatch logic is inlined into the
/// trampolined parser so that grouping `(` can use `GroupClose` frames
/// instead of cross-function recursion through a separate dispatch wrapper.
#[derive(Debug, Clone)]
pub struct CrossCatPrefixArm {
    /// Rust match pattern (e.g., "Token::Float(_)").
    pub token_pattern: String,
    /// The arm body code, using `__CC_OK_BEGIN__ expr __CC_OK_END__` for success.
    /// Contains `__SAME_CAT_FALLBACK__` sentinel for same-category fallback.
    pub body: String,
    /// WFST weight for ordering (lower = more likely).
    pub weight: f64,
    /// Token variant name for dedup tracking.
    pub token_variant: Option<String>,
    /// Whether this arm handles an ambiguous token that also appears in the
    /// target category's own FIRST set (needs same-category fallback inline).
    pub is_ambiguous: bool,
}

/// Compute cross-category prefix arms for inline emission in `_impl`.
///
/// Returns arms that can be merged into the trampolined parser's prefix
/// `match` block. Each arm's `body` uses `__CC_OK_BEGIN__ expr __CC_OK_END__` for success
/// and `__SAME_CAT_FALLBACK__` as a sentinel for the same-category fallback
/// path that `trampoline.rs` will replace with the appropriate logic.
///
/// This replaces the standalone dispatch wrapper: instead of `parse_Cat`
/// delegating to `parse_Cat_own`, ALL dispatch logic lives inside `_impl`.
pub fn compute_cross_cat_prefix_arms(
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
) -> Vec<CrossCatPrefixArm> {
    let mut arms = Vec::new();

    // Phase 16F-0: also check for NT-first foreign rules — rules in
    // `category` whose first syntax item is NT(foreign_cat). These
    // need speculative dispatch arms even when no traditional
    // cross-category or cast rules exist.
    let has_nt_first_foreign = rd_rules.iter().any(|rd| {
        if rd.category != category {
            return false;
        }
        // Exclude single-item rules (cast rules) — those are handled
        // by the existing cast-rule arm generation.
        if rd.items.len() <= 1 {
            return false;
        }
        matches!(
            rd.items.first(),
            Some(crate::recursive::RDSyntaxItem::NonTerminal { category: ref nt_cat, .. })
            if nt_cat != category
        )
    });

    if cross_category_rules.is_empty() && cast_rules.is_empty() && !has_nt_first_foreign {
        return arms;
    }

    // Build implicit cast map from RD rules: (source_cat, target_cat) → label.
    // These are function-style cast rules like `IntToBool . a:Int |- "bool" "(" a ")" : Bool`
    // that can wrap a bare source value when no comparison operator follows.
    let mut implicit_cast_labels: HashMap<(String, String), String> = HashMap::new();
    for rd in rd_rules {
        if rd.category != category { continue; }
        let cross_nts: Vec<String> = rd.items.iter()
            .filter_map(|item| match item {
                crate::recursive::RDSyntaxItem::NonTerminal { category: nt_cat, .. }
                    if *nt_cat != category => Some(nt_cat.clone()),
                _ => None,
            })
            .collect();
        if cross_nts.len() == 1 {
            implicit_cast_labels
                .entry((cross_nts[0].clone(), category.to_string()))
                .or_insert_with(|| rd.label.clone());
        }
    }

    // Build the set of cross-category comparison operator token variants.
    // Used by chain detection: if the token after a successful comparison is
    // another comparison operator, the expression is chained and should be
    // handled by the Pratt infix loop instead.
    let comparison_op_variants: std::collections::HashSet<String> = cross_category_rules
        .iter()
        .filter(|r| r.result_category == category)
        .map(|r| crate::automata::codegen::terminal_to_variant_name(&r.operator))
        .collect();

    // Collect ambiguous tokens
    let mut ambiguous_by_token: HashMap<String, Vec<(&CrossCategoryRule, String)>> =
        HashMap::new();
    let mut deterministic_arms: DeterministicArmMap = HashMap::new();

    for rule in cross_category_rules {
        if rule.result_category != category {
            continue;
        }
        if optimization_gates.enhanced_dce && dead_rules.contains(&rule.label) {
            continue;
        }
        let op_variant = terminal_to_variant_name(&rule.operator);
        let source_first = first_sets.get(&rule.source_category);
        let target_first = first_sets.get(category);

        if let (Some(source_first), Some(target_first)) = (source_first, target_first) {
            let unique_to_source = source_first.difference(target_first);
            for token in &unique_to_source.tokens {
                deterministic_arms
                    .entry((rule.source_category.clone(), token.clone()))
                    .or_default()
                    .push((rule.label.clone(), op_variant.clone(), rule.operator.clone()));
            }
        }

        if let Some(overlap) = overlaps.get(&(rule.source_category.clone(), category.to_string())) {
            for token in &overlap.ambiguous_tokens.tokens {
                ambiguous_by_token
                    .entry(token.clone())
                    .or_default()
                    .push((rule, op_variant.clone()));
            }
        }
    }

    // Generate deterministic cross-category arms
    let mut by_source_and_token: HashMap<String, Vec<(&str, &Vec<(String, String, String)>)>> =
        HashMap::new();
    for ((source_cat, token), rules) in &deterministic_arms {
        by_source_and_token
            .entry(token.clone())
            .or_default()
            .push((source_cat.as_str(), rules));
    }

    for (token, source_rules_list) in &by_source_and_token {
        let arm_weight = weight_map
            .and_then(|wm| wm.get(&(category.to_string(), token.clone())).copied())
            .unwrap_or(f64::INFINITY);

        // Merge all source categories for this token into a SINGLE match arm.
        // Without merging, duplicate match patterns (one per source) would make
        // all but the first arm unreachable dead code in Rust's match.
        let mut body = String::new();
        body.push_str("{ let saved = *pos; ");

        for (source_cat, rules) in source_rules_list {
            let src_upper = source_cat.to_uppercase();

            // Find a cast rule from this source to the target category.
            // Check both single-NT cast rules and RD function-style casts
            // (e.g., IntToBool . a:Int |- "bool" "(" a ")" : Bool).
            // When no comparison operator follows the parsed LHS, we wrap it
            // in this cast instead of discarding the result.
            let cast_fallback: Option<String> = cast_rules.iter()
                .find(|cr| cr.source_category == *source_cat && cr.target_category == category)
                .map(|cr| format!(
                    "__CC_OK_BEGIN__ {}::{}(Box::new(left)) __CC_OK_END__",
                    cr.target_category, cr.label
                ))
                .or_else(|| {
                    implicit_cast_labels.get(&(source_cat.to_string(), category.to_string()))
                        .map(|label| format!(
                            "__CC_OK_BEGIN__ {}::{}(Box::new(left)) __CC_OK_END__",
                            category, label
                        ))
                });

            write!(
                body,
                "PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); ",
            ).unwrap();

            if rules.len() == 1 {
                let (label, op_variant, _operator) = &rules[0];
                write!(
                    body,
                    "if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                        let pre_op = *pos; \
                        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                            let saved_op = *pos; \
                            *pos += 1; \
                            PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                            match parse_{}(tokens, pos, 0) {{ \
                                Ok(right) => {{ __CC_OK_BEGIN__ {}::{}(Box::new(left), Box::new(right)) __CC_OK_END__ }}, \
                                Err(_) => {{ *pos = saved_op; }} \
                            }} \
                        }}",
                    source_cat, op_variant, source_cat, category, label,
                ).unwrap();
                // Cast fallback: fires when no comparison committed (pos still at pre_op).
                // Only at cur_bp > 0 (infix RHS) — at cur_bp == 0, the NFA handles it.
                if let Some(ref fallback) = cast_fallback {
                    write!(body, " if *pos == pre_op && cur_bp > 0 {{ {} }}", fallback).unwrap();
                }
                body.push_str(" }");
            } else {
                write!(
                    body,
                    "if let Ok(left) = parse_{}(tokens, pos, 0) {{ \
                        let pre_op = *pos; \
                        if *pos < tokens.len() {{ match &tokens[*pos].0 {{",
                    source_cat,
                ).unwrap();
                for (label, op_variant, _operator) in rules.iter() {
                    write!(
                        body,
                        " Token::{} => {{ \
                            let saved_op = *pos; \
                            *pos += 1; \
                            PARENT_WEIGHT_{src_upper}.with(|c| c.set(running_weight_{category}())); \
                            match parse_{}(tokens, pos, 0) {{ \
                                Ok(right) => {{ __CC_OK_BEGIN__ {}::{}(Box::new(left), Box::new(right)) __CC_OK_END__ }}, \
                                Err(_) => {{ *pos = saved_op; }} \
                            }} \
                        }},",
                        op_variant, source_cat, category, label,
                    ).unwrap();
                }
                body.push_str(" _ => {} } }");
                // Cast fallback: fires when no comparison committed (pos still at pre_op).
                // Handles: (a) no operator matched, (b) operator matched but RHS failed.
                if let Some(ref fallback) = cast_fallback {
                    write!(body, " if *pos == pre_op && cur_bp > 0 {{ {} }}", fallback).unwrap();
                }
                body.push_str(" }");
            }

            // Restore position before trying the next source category
            body.push_str(" *pos = saved; ");
        }

        body.push_str("__SAME_CAT_FALLBACK__ }");

        let mut pattern = String::new();
        write_token_pattern(&mut pattern, token);

        arms.push(CrossCatPrefixArm {
            token_pattern: pattern,
            body,
            weight: arm_weight,
            token_variant: Some(token.clone()),
            is_ambiguous: false,
        });
    }

    // Generate ambiguous cross-category arms
    for (token, mut rules_and_ops) in ambiguous_by_token {
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

        let ambig_weight = composed_resolutions
            .and_then(|cr| cr.get(&(category.to_string(), token.clone())))
            .map(|(_, w)| *w)
            .or_else(|| {
                prediction_wfst.predict(&token)
                    .first()
                    .map(|wa| wa.weight.value())
            })
            .unwrap_or(f64::INFINITY);

        // Group by source category
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

        // Build chain detection match pattern from comparison operator variants
        let chain_pattern: String = comparison_op_variants.iter()
            .map(|v| format!("Token::{}", v))
            .collect::<Vec<_>>()
            .join(" | ");

        let mut body = String::new();
        // Longest match: try ALL source categories and pick the one that
        // advances pos the furthest. This ensures that e.g. `c > a ++ ""`
        // picks the Str source (which consumes `a ++ ""`) over Int (which
        // stops at `a`). After picking the best, apply chain detection.
        body.push_str("{ let saved = *pos; \
            let mut __best_pos: usize = saved; \
            let mut __best_found = false; ");

        for (source_cat, source_rules) in &by_source {
            let source_upper = source_cat.to_uppercase();
            write!(
                body,
                "PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{category}())); \
                 if let Ok(left) = parse_{}(tokens, pos, 0) {{",
                source_cat,
            ).unwrap();

            // Generate operator matching — on success, compare position with best
            let success_action = format!(
                "if *pos > __best_pos {{ \
                    __best_pos = *pos; \
                    __best_found = true; \
                    __CC_OK_WRITE__ \
                }}"
            );

            if source_rules.len() == 1 {
                let (rule, op) = &source_rules[0];
                write!(
                    body,
                    "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                        let saved_op = *pos; \
                        *pos += 1; \
                        PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{category}())); \
                        match parse_{}(tokens, pos, 0) {{ \
                            Ok(right) => {{ \
                                let __result = {}::{}(Box::new(left), Box::new(right)); \
                                {success} \
                            }}, \
                            Err(_) => {{ *pos = saved_op; }} \
                        }} \
                    }}",
                    op, source_cat, category, rule.label,
                    success = success_action,
                ).unwrap();
            } else {
                body.push_str("if *pos < tokens.len() { match &tokens[*pos].0 {");
                for (rule, op) in source_rules {
                    write!(
                        body,
                        "Token::{} => {{ \
                            let saved_op = *pos; \
                            *pos += 1; \
                            PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{category}())); \
                            match parse_{}(tokens, pos, 0) {{ \
                                Ok(right) => {{ \
                                    let __result = {}::{}(Box::new(left), Box::new(right)); \
                                    {success} \
                                }}, \
                                Err(_) => {{ *pos = saved_op; }} \
                            }} \
                        }},",
                        op, source_cat, category, rule.label,
                        success = success_action,
                    ).unwrap();
                }
                body.push_str("_ => {} } }");
            }

            body.push_str("} *pos = saved; ");
        }

        // After trying all sources: if a match was found, check for chaining.
        // Chain detection: if the token after the best match is another comparison
        // operator, the expression is chained and the Pratt infix loop should
        // handle it via same-category binding powers instead.
        if !chain_pattern.is_empty() {
            write!(
                body,
                "if __best_found {{ \
                    if __best_pos < tokens.len() && matches!(&tokens[__best_pos].0, {chain_pattern}) {{ \
                        __SAME_CAT_FALLBACK__ \
                    }} else {{ \
                        *pos = __best_pos; \
                        return true; \
                    }} \
                }} \
                __SAME_CAT_FALLBACK__ }}",
            ).unwrap();
        } else {
            body.push_str(
                "if __best_found { \
                    *pos = __best_pos; \
                    return true; \
                } \
                __SAME_CAT_FALLBACK__ }",
            );
        }

        let mut pattern = String::new();
        write_token_pattern(&mut pattern, &token);

        arms.push(CrossCatPrefixArm {
            token_pattern: pattern,
            body,
            weight: ambig_weight,
            token_variant: Some(token.clone()),
            is_ambiguous: true,
        });
    }

    // Generate cast rule arms (for tokens unique to source category)
    for rule in cast_rules {
        let source_first = first_sets.get(&rule.source_category);
        let target_first = first_sets.get(category);

        if let (Some(source_first), Some(target_first)) = (source_first, target_first) {
            let unique_to_source = source_first.difference(target_first);
            for token in &unique_to_source.tokens {
                let arm_weight = weight_map
                    .and_then(|wm| wm.get(&(category.to_string(), token.clone())).copied())
                    .unwrap_or(f64::INFINITY);

                let source_upper = rule.source_category.to_uppercase();
                let mut body = String::new();
                // Phase 16F-0: use match instead of ? so the arm works
                // in both Result-returning dispatch wrappers AND
                // bool-returning trampoline cold functions.
                write!(
                    body,
                    "{{ PARENT_WEIGHT_{source_upper}.with(|c| c.set(running_weight_{category}())); \
                       match parse_{}(tokens, pos, 0) {{ \
                           Ok(val) => {{ __CC_OK_BEGIN__ {}::{}(Box::new(val)) __CC_OK_END__ }}, \
                           Err(_) => {{ __SAME_CAT_FALLBACK__ }} \
                       }} }}",
                    rule.source_category, rule.target_category, rule.label,
                ).unwrap();

                let mut pattern = String::new();
                write_token_pattern(&mut pattern, token);

                arms.push(CrossCatPrefixArm {
                    token_pattern: pattern,
                    body,
                    weight: arm_weight,
                    token_variant: Some(token.clone()),
                    is_ambiguous: false,
                });
            }
        }
    }

    // ── Phase 16F-0: NT-first foreign prefix arms ──────────────────────
    //
    // Rules in `category` whose first syntax item is NT(foreign_cat)
    // where foreign_cat != category need speculative dispatch arms.
    // For each such rule, we collect tokens from FIRST(foreign_cat)
    // (excluding Ident, which is handled by the ident-lookahead
    // mechanism) and generate an arm that:
    //   1. Saves *pos
    //   2. Calls parse_{rule_label_lowercase}(tokens, pos) — the
    //      standalone parse function routed by should_use_standalone_fn
    //   3. On success: wraps in __CC_OK_BEGIN__ result __CC_OK_END__
    //   4. On failure: restores *pos, falls through to __SAME_CAT_FALLBACK__
    {
        let mut nt_first_handled: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        // Collect token variants already covered by earlier arms to
        // avoid generating duplicate match patterns.
        for arm in &arms {
            if let Some(ref tv) = arm.token_variant {
                nt_first_handled.insert(tv.clone());
            }
        }

        for rd_rule in rd_rules {
            if rd_rule.category != category {
                continue;
            }

            // Check if the rule starts with a foreign-category NonTerminal
            // AND has more than 1 item (exclude single-item cast rules).
            if rd_rule.items.len() <= 1 {
                continue;
            }
            let source_cat = match rd_rule.items.first() {
                Some(crate::recursive::RDSyntaxItem::NonTerminal {
                    category: ref nt_cat,
                    ..
                }) if nt_cat != category => nt_cat.clone(),
                _ => continue,
            };

            // Skip dead rules.
            if optimization_gates.enhanced_dce && dead_rules.contains(&rd_rule.label) {
                continue;
            }

            let source_first = match first_sets.get(&source_cat) {
                Some(fs) => fs,
                None => continue,
            };

            let parse_fn = format!("parse_{}", rd_rule.label.to_lowercase());

            for token in &source_first.tokens {
                // Skip Ident — handled by the ident-lookahead mechanism.
                if token == "Ident" {
                    continue;
                }
                // Skip tokens already covered by earlier arms.
                if nt_first_handled.contains(token) {
                    continue;
                }
                nt_first_handled.insert(token.clone());

                let arm_weight = weight_map
                    .and_then(|wm| {
                        wm.get(&(category.to_string(), token.clone()))
                            .copied()
                    })
                    .unwrap_or(f64::INFINITY);

                let mut body = String::new();
                write!(
                    body,
                    "{{ let __nt_first_saved = *pos; \
                       match {parse_fn}(tokens, pos) {{ \
                           Ok(v) => {{ __CC_OK_BEGIN__ v __CC_OK_END__ }}, \
                           Err(_) => {{ *pos = __nt_first_saved; __SAME_CAT_FALLBACK__ }} \
                       }} }}",
                )
                .unwrap();

                let mut pattern = String::new();
                write_token_pattern(&mut pattern, token);

                arms.push(CrossCatPrefixArm {
                    token_pattern: pattern,
                    body,
                    weight: arm_weight,
                    token_variant: Some(token.clone()),
                    is_ambiguous: false,
                });
            }
        }
    }

    // Sort by weight
    arms.sort_by(|a, b| a.weight.partial_cmp(&b.weight).unwrap_or(std::cmp::Ordering::Equal));
    arms
}

/// Determine which categories need cross-category dispatch wrappers.
///
/// Cross-category *infix* rules (e.g., `Int "==" Int → Bool`), cast rules
/// (e.g., `Int → Proc`), and **NT-first foreign rules** (rules whose
/// first syntax item is `NT(foreign_cat)`, e.g., `POutput . n:Name ...`)
/// all require the cold dispatch function in their target category.
pub fn categories_needing_dispatch(
    cross_category_rules: &[CrossCategoryRule],
    _cast_rules: &[CastRule],
    rd_rules: &[crate::recursive::RDRuleInfo],
    category_names: &[String],
) -> Vec<String> {
    let mut categories = std::collections::HashSet::new();

    for rule in cross_category_rules {
        categories.insert(rule.result_category.clone());
    }

    // Phase 16F-0: also include categories with NT-first foreign rules
    // (excluding single-item cast rules).
    for rd in rd_rules {
        if rd.items.len() <= 1 {
            continue;
        }
        if let Some(crate::recursive::RDSyntaxItem::NonTerminal {
            category: ref nt_cat,
            ..
        }) = rd.items.first()
        {
            if nt_cat != &rd.category && category_names.contains(nt_cat) {
                categories.insert(rd.category.clone());
            }
        }
    }

    categories.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_arm_body_simple() {
        let arm = r#"Token::Plus => { parse_Int_own(tokens, pos, min_bp) }"#;
        let body = extract_arm_body(arm);
        assert_eq!(body, "parse_Int_own(tokens, pos, min_bp)");
    }

    #[test]
    fn test_extract_arm_body_with_nested_braces() {
        let arm = r#"Token::Ident(_) => { let saved = *pos; if let Ok(left) = parse_Int(tokens, pos, 0) { return Ok(Bool::Eq(Box::new(left), Box::new(right))); } *pos = saved; parse_Bool_own(tokens, pos, min_bp) }"#;
        let body = extract_arm_body(arm);
        assert!(
            body.starts_with("let saved = *pos;"),
            "body should start with 'let saved = *pos;', got: {}",
            body,
        );
        assert!(
            body.ends_with("parse_Bool_own(tokens, pos, min_bp)"),
            "body should end with 'parse_Bool_own(tokens, pos, min_bp)', got: {}",
            body,
        );
    }

    #[test]
    fn test_extract_arm_body_fallback() {
        // If no " => {" is present, the whole string is returned as fallback.
        let arm = "something without arrow";
        let body = extract_arm_body(arm);
        assert_eq!(body, arm);
    }

    #[test]
    fn test_computed_goto_threshold_below() {
        // 19 arms should NOT trigger computed goto
        let mut dispatch_arms: Vec<(String, f64, Option<String>)> = Vec::new();
        let mut token_id_map = TokenIdMap::new();
        for i in 0..19 {
            let token_name = format!("Tok{}", i);
            token_id_map.get_or_insert(&token_name);
            dispatch_arms.push((
                format!("Token::{} => {{ Ok(Cat::V{}) }}", token_name, i),
                0.0,
                Some(token_name),
            ));
        }

        let gates = crate::cost_benefit::OptimizationGates::all_enabled();
        let use_computed_goto = gates.computed_goto
            && dispatch_arms.len() >= COMPUTED_GOTO_THRESHOLD
            && true; // token_id_map present
        assert!(
            !use_computed_goto,
            "19 arms (< threshold {}) should not trigger computed goto",
            COMPUTED_GOTO_THRESHOLD,
        );
    }

    #[test]
    fn test_computed_goto_threshold_at() {
        // 20 arms should trigger computed goto when the gate is enabled
        let mut dispatch_arms: Vec<(String, f64, Option<String>)> = Vec::new();
        let mut token_id_map = TokenIdMap::new();
        for i in 0..20 {
            let token_name = format!("Tok{}", i);
            token_id_map.get_or_insert(&token_name);
            dispatch_arms.push((
                format!("Token::{} => {{ Ok(Cat::V{}) }}", token_name, i),
                0.0,
                Some(token_name),
            ));
        }

        let gates = crate::cost_benefit::OptimizationGates::all_enabled();
        let use_computed_goto = gates.computed_goto
            && dispatch_arms.len() >= COMPUTED_GOTO_THRESHOLD
            && true; // token_id_map present
        assert!(
            use_computed_goto,
            "20 arms (= threshold {}) should trigger computed goto",
            COMPUTED_GOTO_THRESHOLD,
        );
    }

    #[test]
    fn test_computed_goto_disabled_gate() {
        // Even with 20+ arms, computed goto should not trigger if gate is disabled
        let mut dispatch_arms: Vec<(String, f64, Option<String>)> = Vec::new();
        let mut token_id_map = TokenIdMap::new();
        for i in 0..25 {
            let token_name = format!("Tok{}", i);
            token_id_map.get_or_insert(&token_name);
            dispatch_arms.push((
                format!("Token::{} => {{ Ok(Cat::V{}) }}", token_name, i),
                0.0,
                Some(token_name),
            ));
        }

        let gates = crate::cost_benefit::OptimizationGates::none_enabled();
        let use_computed_goto = gates.computed_goto
            && dispatch_arms.len() >= COMPUTED_GOTO_THRESHOLD
            && true; // token_id_map present
        assert!(
            !use_computed_goto,
            "computed goto should not activate when gate is disabled",
        );
    }

    #[test]
    fn test_write_computed_goto_dispatch_emits_table() {
        // Build a token_id_map with known IDs
        let mut token_id_map = TokenIdMap::new();
        token_id_map.get_or_insert("Alpha"); // id 0
        token_id_map.get_or_insert("Beta"); // id 1
        token_id_map.get_or_insert("Gamma"); // id 2

        // Build 3 dispatch arms (using threshold-independent test)
        let dispatch_arms: Vec<(String, f64, Option<String>)> = vec![
            ("Token::Alpha => { Ok(()) }".into(), 0.0, Some("Alpha".into())),
            ("Token::Beta => { Ok(()) }".into(), 0.5, Some("Beta".into())),
            // Gamma has no dispatch arm — should use fallback
        ];

        let mut buf = String::new();
        write_computed_goto_dispatch(&mut buf, "TestCat", &dispatch_arms, &token_id_map);

        // Verify: fallback handler is emitted
        assert!(
            buf.contains("fn dispatch_testcat_fallback"),
            "should emit fallback handler, got:\n{}",
            buf,
        );

        // Verify: per-arm handler functions are emitted
        assert!(
            buf.contains("fn dispatch_testcat_0"),
            "should emit handler for arm 0 (Alpha), got:\n{}",
            buf,
        );
        assert!(
            buf.contains("fn dispatch_testcat_1"),
            "should emit handler for arm 1 (Beta), got:\n{}",
            buf,
        );

        // Verify: dispatch function with table is emitted
        assert!(
            buf.contains("type DispatchFn"),
            "should emit DispatchFn type alias, got:\n{}",
            buf,
        );
        assert!(
            buf.contains("let table:"),
            "should emit table array, got:\n{}",
            buf,
        );
        assert!(
            buf.contains("token_to_id"),
            "should use token_to_id for indexing, got:\n{}",
            buf,
        );

        // Verify: table has 3 entries (matching token_id_map.len())
        assert!(
            buf.contains("[DispatchFn<'a>; 3]"),
            "table should have 3 entries, got:\n{}",
            buf,
        );
    }

    #[test]
    fn test_write_computed_goto_dispatch_unmapped_tokens_use_fallback() {
        // Create a token_id_map with 5 tokens, but only 2 have dispatch arms.
        // The other 3 should use the fallback handler.
        let mut token_id_map = TokenIdMap::new();
        token_id_map.get_or_insert("A"); // id 0
        token_id_map.get_or_insert("B"); // id 1
        token_id_map.get_or_insert("C"); // id 2
        token_id_map.get_or_insert("D"); // id 3
        token_id_map.get_or_insert("E"); // id 4

        let dispatch_arms: Vec<(String, f64, Option<String>)> = vec![
            ("Token::B => { Ok(()) }".into(), 0.0, Some("B".into())),
            ("Token::D => { Ok(()) }".into(), 0.5, Some("D".into())),
        ];

        let mut buf = String::new();
        write_computed_goto_dispatch(&mut buf, "X", &dispatch_arms, &token_id_map);

        // The table should have 5 entries with the pattern:
        // [fallback, handler_B, fallback, handler_D, fallback]
        assert!(
            buf.contains("[DispatchFn<'a>; 5]"),
            "table should have 5 entries, got:\n{}",
            buf,
        );

        // Check that the out-of-bounds guard is present
        assert!(
            buf.contains("if id < 5"),
            "should have bounds check for table size 5, got:\n{}",
            buf,
        );
    }
}
