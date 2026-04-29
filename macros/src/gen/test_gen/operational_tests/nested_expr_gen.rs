//! Phase 2a: Nested expression test generation.
//!
//! For each pair of rules where the output category of rule A matches an input
//! category of rule B, composes them to create depth-2 expressions. For example,
//! `AddInt(NumLit(1), MulInt(NumLit(2), NumLit(3)))` tests that `1 + 2 * 3 = 7`.
//!
//! All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use crate::gen::native::native_type_to_string;
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;
use super::ground_term_enum::{self, GroundTerm, ParamInfo};
use super::symbolic_eval::{self, SymValue};

/// Maximum nested tests to generate per language (to avoid explosion).
const MAX_NESTED_TESTS_PER_LANGUAGE: usize = 50;
/// Maximum leaves per parameter during nested cross-product.
const MAX_LEAVES_PER_PARAM: usize = 3;

/// A composable rule: a rule with rust_code that takes parameters of known categories.
#[derive(Debug, Clone)]
struct ComposableRule {
    label: String,
    category: String,
    /// (param_name, param_category) for each Simple parameter.
    params: Vec<(String, String)>,
}

/// Generate nested expression tests for the language.
///
/// Returns a vector of `TestCase` suitable for code generation.
/// Uses an iterative work-stack to enumerate compositions.
pub fn generate_nested_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> Vec<TestCase> {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    // Step 1: Collect composable rules (rules with rust_code and Simple params)
    let composable: Vec<ComposableRule> = language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .filter(|r| !ambiguous_prefix_rules.contains(&r.label.to_string()))
        .filter_map(|rule| {
            let params = extract_simple_params(rule);
            if params.is_empty() {
                return None;
            }
            Some(ComposableRule {
                label: rule.label.to_string(),
                category: rule.category.to_string(),
                params,
            })
        })
        .collect();

    if composable.is_empty() {
        return Vec::new();
    }

    // Step 2: Build a lookup of rules by output category for inner terms.
    let mut rules_by_output_cat: HashMap<String, Vec<&ComposableRule>> =
        HashMap::with_capacity(composable.len());
    for cr in &composable {
        rules_by_output_cat
            .entry(cr.category.clone())
            .or_insert_with(Vec::new)
            .push(cr);
    }

    // Step 3: Build leaf bank for ground terms at the innermost level.
    let ground_terms_all = ground_term_enum::enumerate_ground_terms(language);
    let mut ground_terms_by_rule: HashMap<String, Vec<&GroundTerm>> =
        HashMap::with_capacity(ground_terms_all.len());
    for gt in &ground_terms_all {
        ground_terms_by_rule
            .entry(gt.rule_label.clone())
            .or_insert_with(Vec::new)
            .push(gt);
    }

    // Step 4: Rule lookup for symbolic evaluation
    let rule_lookup: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.rust_code.is_some())
        .map(|r| (r.label.to_string(), r))
        .collect();

    // Step 5: Enumerate compositions using an iterative work-stack.
    // For each outer rule B, for each param slot i whose category matches
    // the output category of some inner rule A, pick a ground term of A
    // to plug into slot i of B (other slots get simple ground leaves).
    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_NESTED_TESTS_PER_LANGUAGE);

    // Work items: (outer_rule_index, inner_slot, inner_rule_index, inner_ground_term_index)
    struct WorkItem {
        outer_idx: usize,
        inner_slot: usize,
        inner_rule_label: String,
        inner_gt_idx: usize,
    }

    let mut work_stack: Vec<WorkItem> = Vec::new();

    // Populate work stack: for each outer rule, for each param, find matching inner rules
    for (outer_idx, outer) in composable.iter().enumerate() {
        for (slot_idx, (_pname, pcat)) in outer.params.iter().enumerate() {
            if let Some(inner_rules) = rules_by_output_cat.get(pcat) {
                for inner_rule in inner_rules {
                    // Skip self-composition at same label (already covered by Phase 1)
                    // But allow cross-rule composition
                    if inner_rule.label == outer.label {
                        continue;
                    }
                    // Find a ground term for this inner rule
                    if let Some(inner_gts) = ground_terms_by_rule.get(&inner_rule.label) {
                        // Take only the first few to avoid explosion
                        let cap = MAX_LEAVES_PER_PARAM.min(inner_gts.len());
                        for gt_idx in 0..cap {
                            work_stack.push(WorkItem {
                                outer_idx,
                                inner_slot: slot_idx,
                                inner_rule_label: inner_rule.label.clone(),
                                inner_gt_idx: gt_idx,
                            });
                        }
                    }
                }
            }
        }
    }

    // Process work items
    while let Some(wi) = work_stack.pop() {
        if test_cases.len() >= MAX_NESTED_TESTS_PER_LANGUAGE {
            break;
        }

        let outer = &composable[wi.outer_idx];
        let outer_rule = match rule_lookup.get(&outer.label) {
            Some(r) => *r,
            None => continue,
        };

        let inner_gts = match ground_terms_by_rule.get(&wi.inner_rule_label) {
            Some(gts) => gts,
            None => continue,
        };
        if wi.inner_gt_idx >= inner_gts.len() {
            continue;
        }
        let inner_gt = inner_gts[wi.inner_gt_idx];

        // Filter out dangerous inner ground terms (div-by-zero, overflow, etc.)
        let inner_rule_ref = rule_lookup.get(&wi.inner_rule_label);
        if let Some(inner_rule) = inner_rule_ref {
            if super::is_dangerous_input(inner_rule, &inner_gt.param_values) {
                continue;
            }
        }

        // Also filter out dangerous outer+inner combos:
        // If the outer rule has division and the inner result might be zero
        if super::is_dangerous_input(outer_rule, &inner_gt.param_values) {
            continue;
        }

        // Build the nested term: outer rule where slot `inner_slot` uses inner_gt,
        // and other slots use simple leaves.
        let simple_leaves = build_simple_leaf_map(language);

        let mut construction_parts: Vec<String> = Vec::with_capacity(outer.params.len());
        let mut all_slots_filled = true;

        for (slot_idx, (_pname, pcat)) in outer.params.iter().enumerate() {
            if slot_idx == wi.inner_slot {
                // Use the inner ground term
                construction_parts.push(format!("Box::new({})", inner_gt.construction_code));
            } else {
                // Use a simple leaf for this category
                if let Some(leaf) = simple_leaves.get(pcat.as_str()) {
                    construction_parts.push(format!("Box::new({})", leaf.construction));
                } else {
                    all_slots_filled = false;
                    break;
                }
            }
        }

        if !all_slots_filled {
            continue;
        }

        // Opt-Group: append `None` for each Optional inner param of the
        // outer rule. `extract_simple_params` only includes top-level
        // Simple params, so `construction_parts` has fewer entries than
        // the variant's flat field count when Optional groups exist.
        let optional_count: usize = outer_rule
            .term_context
            .as_ref()
            .map(|ctx| {
                fn count_one(
                    p: &mettail_ast::grammar::TermParam,
                    in_optional: bool,
                ) -> usize {
                    use mettail_ast::grammar::TermParam;
                    match p {
                        TermParam::Optional { params: inner } => {
                            inner.iter().map(|q| count_one(q, true)).sum()
                        }
                        TermParam::Simple { .. } => {
                            if in_optional { 1 } else { 0 }
                        }
                        TermParam::GuardBody { .. }
                        | TermParam::Abstraction { .. }
                        | TermParam::MultiAbstraction { .. } => 0,
                    }
                }
                ctx.iter().map(|p| count_one(p, false)).sum()
            })
            .unwrap_or(0);
        for _ in 0..optional_count {
            construction_parts.push("None".to_string());
        }
        let construction_code = format!(
            "{}::{}({})",
            outer.category,
            outer.label,
            construction_parts.join(", ")
        );

        // Attempt symbolic evaluation of the nested expression
        let expected = try_nested_symbolic_eval(
            outer_rule,
            &outer.params,
            wi.inner_slot,
            inner_gt,
            &simple_leaves,
            language,
            &rule_lookup,
        );

        // Check for ambiguous prefix in inner rule too
        if ambiguous_prefix_rules.contains(&wi.inner_rule_label) {
            continue;
        }

        // Filter dangerous inputs (div by zero, etc.)
        if super::is_dangerous_nested_construction(outer_rule, &construction_code) {
            continue;
        }

        let inner_hint = &inner_gt.display_hint;
        let outer_lower = outer.label.to_lowercase();
        let inner_lower = wi.inner_rule_label.to_lowercase();
        let suffix = super::sanitize_test_name(&format!(
            "{}_{}_in_slot{}",
            inner_lower, inner_hint, wi.inner_slot
        ));

        let test_name = if expected.is_some() {
            format!("nested_{}_{}_{}",
                lang_name_lower, outer_lower, suffix)
        } else {
            format!("nested_{}_{}_{}__smoke",
                lang_name_lower, outer_lower, suffix)
        };

        test_cases.push(TestCase {
            test_name,
            construction_code,
            lang_struct: lang_struct.clone(),
            expected,
        });
    }

    test_cases
}

/// Simple leaf value for a category.
#[derive(Debug, Clone)]
pub struct SimpleLeaf {
    pub construction: String,
    pub raw_value: String,
    pub native_type: Option<String>,
}

/// Public wrapper for other modules.
pub fn build_simple_leaf_map_pub(language: &LanguageDef) -> HashMap<String, SimpleLeaf> {
    build_simple_leaf_map(language)
}

/// Build a map from category name to a single representative leaf value.
///
/// Uses the first available leaf per category. Iterative, no recursion.
fn build_simple_leaf_map(language: &LanguageDef) -> HashMap<String, SimpleLeaf> {
    let mut map: HashMap<String, SimpleLeaf> = HashMap::with_capacity(language.types.len());

    for lt in &language.types {
        let cat = lt.name.to_string();
        if let Some(native_type) = &lt.native_type {
            let type_str = native_type_to_string(native_type);
            let lit_label = crate::gen::generate_literal_label(native_type).to_string();

            // Pick a "safe" representative value (non-zero for divisors)
            let (raw_val, construction) = pick_safe_representative(language, &cat, &lit_label, &type_str);

            map.insert(
                cat,
                SimpleLeaf {
                    construction,
                    raw_value: raw_val,
                    native_type: Some(type_str),
                },
            );
        }
    }
    map
}

/// Pick a safe representative value for a native type.
/// Returns (raw_value, construction_code).
///
/// N1: spec-derived. Integer types route through
/// `spec_admitted_integer_samples(language, Safe)` to project the
/// "safe" representative onto the language's effective Integer
/// pattern. Non-integer types use values from the universally-
/// admitted domain of their Float/Bool/StringLit patterns.
fn pick_safe_representative(language: &LanguageDef, cat: &str, lit_label: &str, type_str: &str) -> (String, String) {
    let int_safe = || -> String {
        crate::gen::spec_admitted_integer_samples(
            language, crate::gen::SamplePurpose::Safe,
        ).into_iter().next().unwrap_or_else(|| "1".to_string())
    };
    match type_str {
        "i32" => {
            let raw = format!("{}i32", int_safe());
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        "i64" => {
            let raw = format!("{}i64", int_safe());
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        "u32" => {
            let raw = format!("{}u32", int_safe());
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        "u64" => {
            let raw = format!("{}u64", int_safe());
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        "f32" => {
            let raw = "2.0f32".to_string();
            let cons = format!(
                "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
                cat, lit_label, raw
            );
            (raw, cons)
        },
        "f64" => {
            let raw = "2.0f64".to_string();
            let cons = format!(
                "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
                cat, lit_label, raw
            );
            (raw, cons)
        },
        "bool" => {
            let raw = "true".to_string();
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        "str" | "String" => {
            let raw = "String::from(\"a\")".to_string();
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
        _ => {
            let raw = "Default::default()".to_string();
            let cons = format!("{}::{}({})", cat, lit_label, raw);
            (raw, cons)
        },
    }
}

/// Extract simple parameters from a rule, returning (name, category).
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

/// Attempt symbolic evaluation of a nested expression.
///
/// Evaluates the inner ground term symbolically, then uses that result
/// as input to the outer rule's rust_code.
fn try_nested_symbolic_eval(
    outer_rule: &GrammarRule,
    outer_params: &[(String, String)],
    inner_slot: usize,
    inner_gt: &GroundTerm,
    simple_leaves: &HashMap<String, SimpleLeaf>,
    language: &LanguageDef,
    rule_lookup: &HashMap<String, &GrammarRule>,
) -> Option<String> {
    // First, symbolically evaluate the inner ground term
    let inner_rule = rule_lookup.get(&inner_gt.rule_label)?;
    let inner_param_info = ground_term_enum::extract_param_info(inner_rule, language);

    let mut inner_env: HashMap<String, SymValue> = HashMap::new();
    for (i, pi) in inner_param_info.iter().enumerate() {
        if i < inner_gt.param_values.len() {
            let sv = ground_term_enum::raw_value_to_sym_value(
                &inner_gt.param_values[i],
                &pi.native_type,
            )?;
            inner_env.insert(pi.name.clone(), sv);
        } else {
            return None;
        }
    }

    let inner_result = symbolic_eval::symbolic_eval(
        &inner_rule.rust_code.as_ref()?.code,
        &inner_env,
    )?;

    // Now build the outer environment
    let outer_param_info = ground_term_enum::extract_param_info(outer_rule, language);
    let mut outer_env: HashMap<String, SymValue> = HashMap::new();

    for (slot_idx, pi) in outer_param_info.iter().enumerate() {
        if slot_idx == inner_slot {
            // Use the inner_result
            outer_env.insert(pi.name.clone(), inner_result.clone());
        } else {
            // Use the simple leaf value
            if slot_idx < outer_params.len() {
                let (_pname, pcat) = &outer_params[slot_idx];
                if let Some(leaf) = simple_leaves.get(pcat.as_str()) {
                    let sv = ground_term_enum::raw_value_to_sym_value(
                        &leaf.raw_value,
                        &leaf.native_type,
                    )?;
                    outer_env.insert(pi.name.clone(), sv);
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }

    // Symbolically evaluate the outer rule
    let outer_result = symbolic_eval::symbolic_eval(
        &outer_rule.rust_code.as_ref()?.code,
        &outer_env,
    )?;

    // Convert to display string
    let result_native_type = language
        .types
        .iter()
        .find(|t| t.name.to_string() == outer_rule.category.to_string())
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| native_type_to_string(nt));

    if let Some(ref rnt) = result_native_type {
        outer_result.to_display_string(rnt)
    } else {
        None
    }
}
