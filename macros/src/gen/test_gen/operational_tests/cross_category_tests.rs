//! Phase 3a: Cross-category test generation.
//!
//! Scans `language.terms` for cast rules (parameter category differs from result
//! category) and cross-category operations. Generates tests that construct cast
//! terms, display them, parse them, and evaluate them.
//!
//! Enhanced to derive ALL cast paths from the spec, build a directed cast graph,
//! generate cast chain tests (single-hop, roundtrip, multi-hop), cross-category
//! operation with cast tests, and mixed-type nested expression tests.
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use crate::gen::native::native_type_to_string;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum::{self, ParamInfo};
use super::symbolic_eval::{self, SymValue};

/// Maximum cross-category tests per language.
/// Raised from 40 to 200 to allow comprehensive cross-category coverage.
const MAX_CROSS_CAT_TESTS: usize = 200;

/// A cast rule: a rule where a parameter category differs from the result category.
/// Includes both pure structural casts (no rust_code) and typed conversion casts
/// (with rust_code, e.g. `IntToFloat`).
#[derive(Debug, Clone)]
struct CastRule {
    label: String,
    result_category: String,
    param_name: String,
    param_category: String,
    /// Whether this cast rule has rust_code (typed conversion) vs pure structural.
    has_rust_code: bool,
}

/// A cross-category eval rule: a rule with rust_code where at least one
/// parameter category differs from the result category.
#[derive(Debug, Clone)]
struct CrossCatEvalRule {
    label: String,
    result_category: String,
    params: Vec<(String, String)>, // (param_name, param_category)
}

/// An edge in the cast graph: from source category to target category via a rule.
#[derive(Debug, Clone)]
struct CastEdge {
    from_category: String,
    to_category: String,
    rule_label: String,
}

/// Generate cross-category tests for the language.
///
/// Returns a vector of `TestCase` suitable for code generation.
///
/// The test generation strategy:
/// 1. Derive ALL cast paths from the spec (1E)
/// 2. Generate cast chain tests — single-hop, roundtrip, multi-hop (1A)
/// 3. Generate cross-category operation with cast tests (1B)
/// 4. Generate mixed-type nested expression tests (1C)
/// 5. Generate composite tests: cast wrapped in eval rule (existing Step 5)
pub fn generate_cross_category_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_CROSS_CAT_TESTS);

    // ═══════════════════════════════════════════════════════════
    // Step 1E: Derive ALL cast paths from the spec
    // ═══════════════════════════════════════════════════════════
    //
    // A cast rule is any rule where a parameter category differs from the
    // result category. This includes:
    //   - Pure structural casts (no rust_code): e.g., Proc::CastInt(Int) → Proc
    //   - Typed conversion casts (with rust_code): e.g., IntToFloat(Int) → Float

    let cast_rules = find_all_cast_rules(language, ambiguous_prefix_rules);
    let cast_graph = build_cast_graph(&cast_rules);

    // Build leaf map for constructing representative terms.
    let leaf_map = super::nested_expr_gen::build_simple_leaf_map_pub(language);

    // Build rule lookup for symbolic evaluation.
    let rule_lookup: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .map(|r| (r.label.to_string(), r))
        .collect();

    // ═══════════════════════════════════════════════════════════
    // Step 1A: Cast chain tests
    // ═══════════════════════════════════════════════════════════

    // 1A-i: Single-hop cast tests (one per cast edge in the graph)
    for cast in &cast_rules {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        if let Some(leaf) = leaf_map.get(&cast.param_category) {
            let construction = format!(
                "{}::{}(Box::new({}))",
                cast.result_category, cast.label, leaf.construction
            );

            let test_name = format!(
                "cross_cat_{}_cast_{}_from_{}_to_{}",
                lang_name_lower,
                cast.label.to_lowercase(),
                cast.param_category.to_lowercase(),
                cast.result_category.to_lowercase(),
            );

            // For casts with rust_code, try symbolic eval for expected value
            let expected = if cast.has_rust_code {
                if let Some(rule) = rule_lookup.get(&cast.label) {
                    let param_info = ground_term_enum::extract_param_info(rule, language);
                    try_symbolic_eval_cross(
                        rule,
                        &param_info,
                        &[(cast.param_name.clone(), cast.param_category.clone())],
                        &leaf_map,
                        language,
                    )
                } else {
                    None
                }
            } else {
                None
            };

            test_cases.push(TestCase {
                test_name,
                construction_code: construction,
                lang_struct: lang_struct.clone(),
                expected,
            });
        }
    }

    // 1A-ii: Roundtrip cast tests (A → B → A where both edges exist)
    let reverse_pairs = find_roundtrip_cast_pairs(&cast_rules);
    for (forward, reverse) in &reverse_pairs {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        if let Some(leaf) = leaf_map.get(&forward.param_category) {
            // Build A → B → A: reverse(forward(leaf))
            let inner = format!(
                "{}::{}(Box::new({}))",
                forward.result_category, forward.label, leaf.construction
            );
            let outer = format!(
                "{}::{}(Box::new({}))",
                reverse.result_category, reverse.label, inner
            );

            let test_name = format!(
                "cross_cat_{}_roundtrip_{}_to_{}_via_{}_{}",
                lang_name_lower,
                forward.param_category.to_lowercase(),
                forward.result_category.to_lowercase(),
                forward.label.to_lowercase(),
                reverse.label.to_lowercase(),
            );

            test_cases.push(TestCase {
                test_name,
                construction_code: outer,
                lang_struct: lang_struct.clone(),
                expected: None, // Roundtrip semantics are complex; smoke test
            });
        }
    }

    // 1A-iii: Multi-hop chain tests (A → B → C where A→B and B→C exist)
    let multi_hop_chains = find_multi_hop_chains(&cast_graph, &cast_rules);
    for chain in &multi_hop_chains {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        // chain is a Vec of CastRule representing hops: [A→B, B→C, ...]
        if chain.is_empty() {
            continue;
        }

        let first_param_cat = &chain[0].param_category;
        if let Some(leaf) = leaf_map.get(first_param_cat) {
            // Build the nested chain: C(B(leaf))
            let mut current = leaf.construction.clone();
            let mut labels: Vec<String> = Vec::with_capacity(chain.len());

            for hop in chain {
                current = format!(
                    "{}::{}(Box::new({}))",
                    hop.result_category, hop.label, current
                );
                labels.push(hop.label.to_lowercase());
            }

            let test_name = format!(
                "cross_cat_{}_chain_{}",
                lang_name_lower,
                labels.join("_"),
            );

            test_cases.push(TestCase {
                test_name,
                construction_code: current,
                lang_struct: lang_struct.clone(),
                expected: None, // Multi-hop chains are smoke tests
            });
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Step 2: Cross-category eval rules (existing behavior, enhanced)
    // ═══════════════════════════════════════════════════════════

    let cross_eval_rules = find_cross_cat_eval_rules(language, ambiguous_prefix_rules);

    for cross in &cross_eval_rules {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        let rule = match rule_lookup.get(&cross.label) {
            Some(r) => *r,
            None => continue,
        };

        // Construct the term with leaves for each param
        let mut parts: Vec<String> = Vec::with_capacity(cross.params.len());
        let mut all_filled = true;

        for (_pname, pcat) in &cross.params {
            if let Some(leaf) = leaf_map.get(pcat.as_str()) {
                parts.push(format!("Box::new({})", leaf.construction));
            } else {
                all_filled = false;
                break;
            }
        }

        if !all_filled {
            continue;
        }

        // Opt-Group: append `None` for each Optional inner Simple field
        // (variant flat-field count includes them after top-level params).
        for _ in 0..ground_term_enum::count_optional_inner_simples(rule) {
            parts.push("None".to_string());
        }

        let construction = format!(
            "{}::{}({})",
            cross.result_category, cross.label, parts.join(", ")
        );

        // Try symbolic evaluation
        let param_info = ground_term_enum::extract_param_info(rule, language);
        let expected = try_symbolic_eval_cross(
            rule,
            &param_info,
            &cross.params,
            &leaf_map,
            language,
        );

        let test_name = if expected.is_some() {
            format!(
                "cross_cat_{}_eval_{}",
                lang_name_lower,
                cross.label.to_lowercase(),
            )
        } else {
            format!(
                "cross_cat_{}_eval_{}_smoke",
                lang_name_lower,
                cross.label.to_lowercase(),
            )
        };

        test_cases.push(TestCase {
            test_name,
            construction_code: construction,
            lang_struct: lang_struct.clone(),
            expected,
        });
    }

    // ═══════════════════════════════════════════════════════════
    // Step 1B: Cross-category operation with cast
    // ═══════════════════════════════════════════════════════════
    //
    // For each eval rule in category B that takes params of type B,
    // and for each cast rule A → B, generate a test that applies
    // the eval rule to cast values.
    // e.g., sin(float(42)), cos(float(0)), len(str(42))

    for cast in &cast_rules {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        let result_cat = &cast.result_category;

        // Find eval rules in the cast's result category that accept the result category
        for eval_rule in language.terms.iter() {
            if test_cases.len() >= MAX_CROSS_CAT_TESTS {
                break;
            }

            if eval_rule.rust_code.is_none() {
                continue;
            }
            if eval_rule.category.to_string() != *result_cat {
                continue;
            }
            if ambiguous_prefix_rules.contains(&eval_rule.label.to_string()) {
                continue;
            }

            let eval_params = extract_simple_params(eval_rule);
            if eval_params.is_empty() {
                continue;
            }

            // Check if at least one param matches the cast's result category
            // (so we can substitute a cast expression there)
            let has_matching_param = eval_params.iter().any(|(_, pcat)| pcat == result_cat);
            if !has_matching_param {
                continue;
            }

            // Build: for params matching result_cat, use a Cast(leaf);
            // for params of other categories, use direct leaf
            if let Some(source_leaf) = leaf_map.get(&cast.param_category) {
                let cast_term = format!(
                    "{}::{}(Box::new({}))",
                    cast.result_category, cast.label, source_leaf.construction
                );

                let mut eval_parts: Vec<String> = Vec::with_capacity(eval_params.len());
                let mut all_filled = true;

                for (_pname, pcat) in &eval_params {
                    if pcat == result_cat {
                        eval_parts.push(format!("Box::new({})", cast_term));
                    } else if let Some(leaf) = leaf_map.get(pcat.as_str()) {
                        eval_parts.push(format!("Box::new({})", leaf.construction));
                    } else {
                        all_filled = false;
                        break;
                    }
                }

                if !all_filled {
                    continue;
                }

                // Opt-Group: append `None` per Optional inner Simple.
                for _ in 0..ground_term_enum::count_optional_inner_simples(eval_rule) {
                    eval_parts.push("None".to_string());
                }

                let construction = format!(
                    "{}::{}({})",
                    result_cat,
                    eval_rule.label,
                    eval_parts.join(", ")
                );

                let test_name = format!(
                    "cross_cat_{}_castop_{}_{}_smoke",
                    lang_name_lower,
                    eval_rule.label.to_string().to_lowercase(),
                    cast.label.to_lowercase(),
                );

                test_cases.push(TestCase {
                    test_name,
                    construction_code: construction,
                    lang_struct: lang_struct.clone(),
                    expected: None,
                });
            }
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Step 1C: Mixed-type nested expressions
    // ═══════════════════════════════════════════════════════════
    //
    // Mix cast values with native values in the same operation.
    // e.g., float(1) + 2.5 — cast value combined with native value
    // e.g., int(1.5) + 2 — cast from float to int, then int arithmetic
    //
    // For each binary eval rule in category B (with 2 params of type B),
    // and for each cast A → B, generate:
    //   EvalB(CastAtoB(leafA), leafB) — mixed cast + native
    //   EvalB(leafB, CastAtoB(leafA)) — native + mixed cast

    for cast in &cast_rules {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        let result_cat = &cast.result_category;

        // Find binary eval rules in the result category where both params are in result_cat
        for eval_rule in language.terms.iter() {
            if test_cases.len() >= MAX_CROSS_CAT_TESTS {
                break;
            }

            if eval_rule.rust_code.is_none() {
                continue;
            }
            if eval_rule.category.to_string() != *result_cat {
                continue;
            }
            if ambiguous_prefix_rules.contains(&eval_rule.label.to_string()) {
                continue;
            }

            let eval_params = extract_simple_params(eval_rule);
            // Want binary rules where both params are in the result category
            if eval_params.len() != 2 {
                continue;
            }
            if eval_params[0].1 != *result_cat || eval_params[1].1 != *result_cat {
                continue;
            }

            // Skip dangerous operations (division, power, modulo)
            if is_dangerous_eval_rule(eval_rule) {
                continue;
            }

            let source_leaf = match leaf_map.get(&cast.param_category) {
                Some(l) => l,
                None => continue,
            };
            let native_leaf = match leaf_map.get(result_cat.as_str()) {
                Some(l) => l,
                None => continue,
            };

            let cast_term = format!(
                "{}::{}(Box::new({}))",
                cast.result_category, cast.label, source_leaf.construction
            );

            // Opt-Group: build the optional-None tail once for both lhs/rhs.
            let optional_tail: String = {
                let n = ground_term_enum::count_optional_inner_simples(eval_rule);
                if n == 0 { String::new() } else { ", ".to_string() + &vec!["None"; n].join(", ") }
            };

            // Mixed test: cast value as first param, native as second
            let construction_lhs = format!(
                "{}::{}(Box::new({}), Box::new({}){})",
                result_cat, eval_rule.label, cast_term, native_leaf.construction, optional_tail
            );

            let test_name_lhs = format!(
                "cross_cat_{}_mixed_{}_cast_{}_lhs_smoke",
                lang_name_lower,
                eval_rule.label.to_string().to_lowercase(),
                cast.label.to_lowercase(),
            );

            test_cases.push(TestCase {
                test_name: test_name_lhs,
                construction_code: construction_lhs,
                lang_struct: lang_struct.clone(),
                expected: None,
            });

            if test_cases.len() >= MAX_CROSS_CAT_TESTS {
                break;
            }

            // Mixed test: native as first param, cast value as second
            let construction_rhs = format!(
                "{}::{}(Box::new({}), Box::new({}){})",
                result_cat, eval_rule.label, native_leaf.construction, cast_term, optional_tail
            );

            let test_name_rhs = format!(
                "cross_cat_{}_mixed_{}_cast_{}_rhs_smoke",
                lang_name_lower,
                eval_rule.label.to_string().to_lowercase(),
                cast.label.to_lowercase(),
            );

            test_cases.push(TestCase {
                test_name: test_name_rhs,
                construction_code: construction_rhs,
                lang_struct: lang_struct.clone(),
                expected: None,
            });

            // Only generate one pair per cast × eval combination for mixed tests
            break;
        }
    }

    // ═══════════════════════════════════════════════════════════
    // Step 5: Composite tests: cast wrapped in eval rule (enhanced)
    // ═══════════════════════════════════════════════════════════
    //
    // For each cast rule and each eval rule in the cast's result category,
    // generate a test wrapping all params as cast expressions.
    // Now iterates across ALL eval rules (not just first per cast).

    for cast in &cast_rules {
        if test_cases.len() >= MAX_CROSS_CAT_TESTS {
            break;
        }

        let result_cat = &cast.result_category;
        for eval_rule in language.terms.iter() {
            if test_cases.len() >= MAX_CROSS_CAT_TESTS {
                break;
            }

            if eval_rule.rust_code.is_none() {
                continue;
            }
            if eval_rule.category.to_string() != *result_cat {
                continue;
            }
            if ambiguous_prefix_rules.contains(&eval_rule.label.to_string()) {
                continue;
            }

            let eval_params = extract_simple_params(eval_rule);
            // Check if all params are in the result category
            if !eval_params.iter().all(|(_, pcat)| pcat == result_cat) {
                continue;
            }
            if eval_params.is_empty() {
                continue;
            }

            // Build: each param is a Cast wrapping a leaf
            if let Some(leaf) = leaf_map.get(&cast.param_category) {
                let cast_term = format!(
                    "{}::{}(Box::new({}))",
                    cast.result_category, cast.label, leaf.construction
                );

                let mut eval_parts: Vec<String> = eval_params
                    .iter()
                    .map(|_| format!("Box::new({})", cast_term))
                    .collect();

                // Opt-Group: append `None` per Optional inner Simple.
                for _ in 0..ground_term_enum::count_optional_inner_simples(eval_rule) {
                    eval_parts.push("None".to_string());
                }

                let construction = format!(
                    "{}::{}({})",
                    result_cat,
                    eval_rule.label,
                    eval_parts.join(", ")
                );

                let test_name = format!(
                    "cross_cat_{}_composite_{}_{}_smoke",
                    lang_name_lower,
                    eval_rule.label.to_string().to_lowercase(),
                    cast.label.to_lowercase(),
                );

                test_cases.push(TestCase {
                    test_name,
                    construction_code: construction,
                    lang_struct: lang_struct.clone(),
                    expected: None,
                });
            }
        }
    }

    test_cases
}

// ═══════════════════════════════════════════════════════════════════════════════
// Cast graph construction and path finding (1E)
// ═══════════════════════════════════════════════════════════════════════════════

/// Find ALL cast rules from the spec.
///
/// A cast rule is any rule where:
/// - It has exactly one parameter whose category differs from the result category
/// - It is not in the ambiguous prefix set
///
/// This includes both pure structural casts (no rust_code) AND typed conversion
/// casts (with rust_code, e.g., IntToFloat, FloatToInt).
fn find_all_cast_rules(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<CastRule> {
    language
        .terms
        .iter()
        .filter(|r| !ambiguous_prefix_rules.contains(&r.label.to_string()))
        .filter_map(|rule| {
            let result_cat = rule.category.to_string();
            let params = extract_simple_params(rule);
            // A cast rule: exactly one param whose category differs from result
            if params.len() == 1 && params[0].1 != result_cat {
                Some(CastRule {
                    label: rule.label.to_string(),
                    result_category: result_cat,
                    param_name: params[0].0.clone(),
                    param_category: params[0].1.clone(),
                    has_rust_code: rule.rust_code.is_some(),
                })
            } else {
                None
            }
        })
        .collect()
}

/// Build a directed cast graph from the cast rules.
///
/// Each edge represents a cast from one category to another.
fn build_cast_graph(cast_rules: &[CastRule]) -> Vec<CastEdge> {
    cast_rules
        .iter()
        .map(|cr| CastEdge {
            from_category: cr.param_category.clone(),
            to_category: cr.result_category.clone(),
            rule_label: cr.label.clone(),
        })
        .collect()
}

/// Find roundtrip cast pairs: (A → B, B → A) where both directions exist.
fn find_roundtrip_cast_pairs(cast_rules: &[CastRule]) -> Vec<(CastRule, CastRule)> {
    let mut pairs: Vec<(CastRule, CastRule)> = Vec::new();
    let mut seen: HashSet<(String, String)> = HashSet::new();

    for forward in cast_rules {
        for reverse in cast_rules {
            if forward.param_category == reverse.result_category
                && forward.result_category == reverse.param_category
                && forward.param_category != forward.result_category
            {
                let key = (
                    forward.param_category.clone().min(forward.result_category.clone()),
                    forward.param_category.clone().max(forward.result_category.clone()),
                );
                if !seen.contains(&key) {
                    seen.insert(key);
                    pairs.push((forward.clone(), reverse.clone()));
                }
            }
        }
    }

    pairs
}

/// Find multi-hop chain paths (length 2) in the cast graph using BFS.
///
/// For each pair of edges A→B and B→C where A ≠ C, yield [A→B, B→C].
fn find_multi_hop_chains(_cast_graph: &[CastEdge], cast_rules: &[CastRule]) -> Vec<Vec<CastRule>> {
    let mut chains: Vec<Vec<CastRule>> = Vec::new();
    let mut seen: HashSet<(String, String, String)> = HashSet::new();

    // Build adjacency map: from_category → list of cast rules
    let mut adj: HashMap<String, Vec<&CastRule>> = HashMap::new();
    for cr in cast_rules {
        adj.entry(cr.param_category.clone())
            .or_insert_with(Vec::new)
            .push(cr);
    }

    // For each first hop A→B, find second hops B→C where C ≠ A
    for first_hop in cast_rules {
        if let Some(second_hops) = adj.get(&first_hop.result_category) {
            for second_hop in second_hops {
                if second_hop.result_category != first_hop.param_category {
                    let key = (
                        first_hop.param_category.clone(),
                        first_hop.result_category.clone(),
                        second_hop.result_category.clone(),
                    );
                    if !seen.contains(&key) {
                        seen.insert(key);
                        chains.push(vec![first_hop.clone(), (*second_hop).clone()]);
                    }
                }
            }
        }
    }

    chains
}

/// Find cross-category eval rules (rules with rust_code where at least one
/// parameter category differs from the result category).
fn find_cross_cat_eval_rules(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<CrossCatEvalRule> {
    language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .filter(|r| !ambiguous_prefix_rules.contains(&r.label.to_string()))
        .filter_map(|rule| {
            let result_cat = rule.category.to_string();
            let params = extract_simple_params(rule);
            // Cross-category: at least one param from a different category
            let has_cross = params.iter().any(|(_, pcat)| *pcat != result_cat);
            if has_cross && !params.is_empty() {
                Some(CrossCatEvalRule {
                    label: rule.label.to_string(),
                    result_category: result_cat,
                    params,
                })
            } else {
                None
            }
        })
        .collect()
}

// ═══════════════════════════════════════════════════════════════════════════════
// Helper functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Extract simple parameters from a rule.
fn extract_simple_params(rule: &GrammarRule) -> Vec<(String, String)> {
    let mut params = Vec::new();
    if let Some(ctx) = &rule.term_context {
        for p in ctx {
            if let TermParam::Simple { name, ty } = p {
                if let TypeExpr::Base(type_ident) = ty {
                    params.push((name.to_string(), type_ident.to_string()));
                }
            }
        }
    }
    params
}

/// Try symbolic evaluation for a cross-category eval rule.
fn try_symbolic_eval_cross(
    rule: &GrammarRule,
    param_info: &[ParamInfo],
    params: &[(String, String)],
    leaf_map: &HashMap<String, super::nested_expr_gen::SimpleLeaf>,
    language: &LanguageDef,
) -> Option<String> {
    let rust_code = rule.rust_code.as_ref()?;
    let mut env: HashMap<String, SymValue> = HashMap::new();

    for (i, pi) in param_info.iter().enumerate() {
        if i >= params.len() {
            return None;
        }
        let (_pname, pcat) = &params[i];
        let leaf = leaf_map.get(pcat.as_str())?;
        let sv = ground_term_enum::raw_value_to_sym_value(&leaf.raw_value, &leaf.native_type)?;
        env.insert(pi.name.clone(), sv);
    }

    let result = symbolic_eval::symbolic_eval(&rust_code.code, &env)?;

    let result_native_type = language
        .types
        .iter()
        .find(|t| t.name.to_string() == rule.category.to_string())
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| native_type_to_string(nt));

    if let Some(ref rnt) = result_native_type {
        result.to_display_string(rnt)
    } else {
        None
    }
}

/// Check if an eval rule involves dangerous operations (division, modulo, power, product range).
///
/// Uses the label as a heuristic since the actual expression analysis functions
/// are private to the parent module. Checks label suffixes commonly associated with
/// dangerous arithmetic operations.
fn is_dangerous_eval_rule(rule: &GrammarRule) -> bool {
    let label = rule.label.to_string().to_lowercase();
    // Skip division, modulo, power, and factorial rules
    if label.contains("div")
        || label.contains("mod")
        || label.contains("pow")
        || label.contains("fact")
        || label.contains("rem")
    {
        return true;
    }
    // Also delegate to the parent module's check with dummy values
    super::is_dangerous_input(rule, &[])
}
