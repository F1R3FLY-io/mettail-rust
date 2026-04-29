//! Ground-term enumeration for operational semantics test derivation.
//!
//! Enumerates ground (no free variables) input terms for each rule with `rust_code`.
//! Leaf values are derived from the spec's `native_type` annotations, not hard-coded
//! per language. Non-native categories use nullary constructors as leaves.
//!
//! All recursive operations use iterative work-stacks (trampolines).

use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use crate::gen::native::native_type_to_string;
use crate::gen::generate_literal_label;
use std::collections::HashMap;

/// A ground term suitable for testing operational semantics.
#[derive(Debug, Clone)]
pub struct GroundTerm {
    /// The label of the grammar rule this term was generated from.
    pub rule_label: String,
    /// The category (result type) of the rule.
    pub category: String,
    /// Rust code string that constructs the AST term.
    pub construction_code: String,
    /// Display-friendly parameter values (for test naming).
    pub param_values: Vec<String>,
    /// A short suffix for test function naming (e.g., "1_2" for params 1,2).
    pub display_hint: String,
}

/// A leaf value for a category: the Rust code to construct it, and a display hint.
#[derive(Debug, Clone)]
struct LeafValue {
    /// Rust expression constructing the term (e.g., `Int::NumLit(1i32)`).
    construction: String,
    /// Short display string for test naming (e.g., "1").
    display: String,
    /// The raw value for symbolic evaluation (e.g., "1" for Int(1)).
    raw_value: String,
    /// The native type string if this is a literal leaf (e.g., "i32").
    #[allow(dead_code)]
    native_type: Option<String>,
}

/// Build the leaf bank: for each category, a list of leaf values.
///
/// Uses an iterative work-stack to avoid recursion.
fn build_leaf_bank(language: &LanguageDef) -> HashMap<String, Vec<LeafValue>> {
    let mut bank: HashMap<String, Vec<LeafValue>> = HashMap::with_capacity(language.types.len());

    // Work-stack: list of categories to process.
    // No recursion needed for leaf bank since leaves are by definition non-recursive.
    let mut work_stack: Vec<String> = language
        .types
        .iter()
        .map(|t| t.name.to_string())
        .collect();

    while let Some(cat) = work_stack.pop() {
        if bank.contains_key(&cat) {
            continue;
        }

        let mut leaves = Vec::new();

        // Check if category has a native type
        let lang_type = language.types.iter().find(|t| t.name.to_string() == cat);

        if let Some(lt) = lang_type {
            if let Some(native_type) = &lt.native_type {
                let type_str = native_type_to_string(native_type);
                let lit_label = generate_literal_label(native_type).to_string();

                // Check if this category has a prefix negation rule (syntax starts with "-")
                // so we know whether negative literal values can be parsed back.
                let has_prefix_neg = language.terms.iter().any(|r| {
                    r.category.to_string() == cat && {
                        // Check new syntax: first syntax element is "-"
                        let new_has_neg = r.syntax_pattern.as_ref().map_or(false, |pats| {
                            pats.first().map_or(false, |p| {
                                matches!(p, mettail_ast::grammar::SyntaxExpr::Literal(t) if t == "-")
                            })
                        });
                        // Check old syntax: first item is Terminal("-")
                        let old_has_neg = r.items.first().map_or(false, |item| {
                            matches!(item, mettail_ast::grammar::GrammarItem::Terminal(t) if t == "-")
                        });
                        new_has_neg || old_has_neg
                    }
                });

                // Derive representative values from the TYPE
                let representative_values = representative_values_for_type(language, &type_str, has_prefix_neg);

                for (raw_val, display_val) in representative_values {
                    let construction = construct_literal_code(
                        &cat,
                        &lit_label,
                        &type_str,
                        &raw_val,
                    );
                    leaves.push(LeafValue {
                        construction,
                        display: display_val.clone(),
                        raw_value: raw_val,
                        native_type: Some(type_str.clone()),
                    });
                }
            }
        }

        // Also look for nullary constructors (rules with zero non-terminal items)
        for rule in &language.terms {
            if rule.category.to_string() != cat {
                continue;
            }
            // Check new syntax: term_context is Some and empty
            let is_nullary_new = rule
                .term_context
                .as_ref()
                .map_or(false, |ctx| ctx.is_empty());
            // Check old syntax: items list is empty
            let is_nullary_old = rule.term_context.is_none() && rule.items.is_empty();

            if is_nullary_new || is_nullary_old {
                let label = rule.label.to_string();
                let construction = format!("{}::{}", cat, label);
                leaves.push(LeafValue {
                    construction,
                    display: label.clone(),
                    raw_value: label.clone(),
                    native_type: None,
                });
            }
        }

        // If no leaves found (non-native, no nullary), add a variable fallback
        // but skip it since we want ground terms only (no free variables)
        // Instead, just leave this category empty — rules depending on it won't
        // get operational tests.

        bank.insert(cat, leaves);
    }

    bank
}

/// Derive representative values from a Rust native type.
/// Returns (raw_value_string, display_hint_string) pairs.
///
/// G1: spec-derived. Integer-family types route through
/// `spec_admitted_integer_samples(language, GroundEnum)`. Negative
/// values are emitted only when both `has_prefix_neg` (rule has prefix
/// negation) AND the spec's Integer pattern admits the leading dash
/// (the helper handles this internally).
///
/// `has_prefix_neg`: kept for compatibility with the caller, but the
/// underlying integer-sample helper already gates negatives on the
/// pattern's signedness — passing `has_prefix_neg=false` filters out
/// negatives even if the pattern is signed.
fn representative_values_for_type(language: &LanguageDef, type_str: &str, has_prefix_neg: bool) -> Vec<(String, String)> {
    let int_samples = |suffix: &str| -> Vec<(String, String)> {
        crate::gen::spec_admitted_integer_samples(language, crate::gen::SamplePurpose::GroundEnum)
            .into_iter()
            .filter(|s| has_prefix_neg || !s.starts_with('-'))
            .map(|s| {
                let display_hint = if s.starts_with('-') {
                    format!("neg{}", &s[1..])
                } else {
                    s.clone()
                };
                (format!("{}{}", s, suffix), display_hint)
            })
            .collect()
    };
    match type_str {
        "i32" => int_samples("i32"),
        "i64" => int_samples("i64"),
        "u32" => int_samples("u32"),
        "u64" => int_samples("u64"),
        "f32" => vec![
            ("0.0f32".to_string(), "0_0".to_string()),
            ("1.0f32".to_string(), "1_0".to_string()),
            ("0.5f32".to_string(), "0_5".to_string()),
            ("2.0f32".to_string(), "2_0".to_string()),
            ("2.5f32".to_string(), "2_5".to_string()),
        ],
        "f64" => vec![
            ("0.0f64".to_string(), "0_0".to_string()),
            ("1.0f64".to_string(), "1_0".to_string()),
            ("0.5f64".to_string(), "0_5".to_string()),
            ("2.0f64".to_string(), "2_0".to_string()),
            ("2.5f64".to_string(), "2_5".to_string()),
        ],
        "bool" => vec![
            ("true".to_string(), "true".to_string()),
            ("false".to_string(), "false".to_string()),
        ],
        "str" | "String" => vec![
            ("String::new()".to_string(), "empty".to_string()),
            ("String::from(\"a\")".to_string(), "a".to_string()),
            ("String::from(\"hello\")".to_string(), "hello".to_string()),
        ],
        // Fallback for unknown types
        _ => vec![("Default::default()".to_string(), "default".to_string())],
    }
}

/// Construct the Rust code for a literal value in a given category.
fn construct_literal_code(
    cat: &str,
    lit_label: &str,
    type_str: &str,
    raw_val: &str,
) -> String {
    match type_str {
        "f64" => format!(
            "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
            cat, lit_label, raw_val
        ),
        "f32" => format!(
            "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
            cat, lit_label, raw_val
        ),
        "str" | "String" => format!("{}::{}({})", cat, lit_label, raw_val),
        _ => format!("{}::{}({})", cat, lit_label, raw_val),
    }
}

/// Extract parameter categories from a rule's term_context (new syntax) or items (old syntax).
///
/// Returns a list of (param_name, category_name) pairs for each Simple parameter.
/// Abstraction/MultiAbstraction/Binder/Collection parameters are skipped (too complex).
fn extract_simple_params(rule: &GrammarRule, _language: &LanguageDef) -> Vec<(String, String)> {
    let mut params = Vec::new();

    if let Some(ctx) = &rule.term_context {
        for p in ctx {
            match p {
                TermParam::Simple { name, ty } => {
                    if let TypeExpr::Base(type_ident) = ty {
                        params.push((name.to_string(), type_ident.to_string()));
                    }
                    // Skip Collection types — they need non-trivial setup
                },
                // Skip Abstraction, MultiAbstraction, GuardBody
                _ => {},
            }
        }
    }
    // For old syntax rules with rust_code, we don't extract params because old syntax
    // rules generally don't have rust_code (HOL syntax requires new syntax).

    params
}

/// Generate all ground terms for rules with `rust_code` in the language.
///
/// Uses an iterative work-stack to enumerate cross-products.
pub fn enumerate_ground_terms(language: &LanguageDef) -> Vec<GroundTerm> {
    let leaf_bank = build_leaf_bank(language);
    let mut ground_terms = Vec::new();

    // Process each rule with rust_code
    for rule in &language.terms {
        if rule.rust_code.is_none() {
            continue;
        }

        let label = rule.label.to_string();
        let category = rule.category.to_string();

        // Extract simple parameters
        let params = extract_simple_params(rule, language);

        if params.is_empty() {
            // Nullary rule with rust_code (rare but possible)
            ground_terms.push(GroundTerm {
                rule_label: label.clone(),
                category: category.clone(),
                construction_code: format!("{}::{}", category, label),
                param_values: Vec::new(),
                display_hint: "nullary".to_string(),
            });
            continue;
        }

        // Look up leaves for each parameter category
        let param_leaves: Vec<(&str, &str, Vec<&LeafValue>)> = params
            .iter()
            .map(|(name, cat)| {
                let leaves = leaf_bank
                    .get(cat.as_str())
                    .map(|v| v.iter().collect::<Vec<_>>())
                    .unwrap_or_default();
                (name.as_str(), cat.as_str(), leaves)
            })
            .collect();

        // Check if any parameter has no leaves — skip this rule
        if param_leaves.iter().any(|(_, _, leaves)| leaves.is_empty()) {
            continue;
        }

        // Compute cross-product using iterative work-stack.
        // Cap at 5 leaves per parameter, and 20 total terms per rule.
        let capped_leaves: Vec<Vec<&LeafValue>> = param_leaves
            .iter()
            .map(|(_, _, leaves)| {
                let cap = 5.min(leaves.len());
                leaves[..cap].to_vec()
            })
            .collect();

        // Iterative cross-product enumeration using a work-stack.
        // Each work item is a partial selection: Vec of indices into capped_leaves[i].
        let param_count = capped_leaves.len();
        let mut results: Vec<Vec<usize>> = Vec::new();

        // Stack of (current_depth, partial_indices)
        let mut stack: Vec<(usize, Vec<usize>)> = Vec::new();
        stack.push((0, Vec::with_capacity(param_count)));

        while let Some((depth, partial)) = stack.pop() {
            if results.len() >= 20 {
                break;
            }
            if depth == param_count {
                results.push(partial);
                continue;
            }
            // Push children in reverse order so the first combination is processed first
            let leaf_count = capped_leaves[depth].len();
            for i in (0..leaf_count).rev() {
                let mut next = partial.clone();
                next.push(i);
                stack.push((depth + 1, next));
            }
        }

        // Convert index combinations to GroundTerms
        for indices in results {
            let selected_leaves: Vec<&LeafValue> = indices
                .iter()
                .enumerate()
                .map(|(param_idx, &leaf_idx)| capped_leaves[param_idx][leaf_idx])
                .collect();

            // Build construction code: Cat::Label(Box::new(leaf1), Box::new(leaf2), ...)
            let mut field_exprs: Vec<String> = selected_leaves
                .iter()
                .map(|leaf| format!("Box::new({})", leaf.construction))
                .collect();

            // Opt-Group: append `None` for each Optional inner non-terminal
            // of the rule. `extract_simple_params` only returns top-level
            // Simple params, so `field_exprs` is short by `optional_count`
            // when the rule has `*opt(...)` groups. The variant's flat
            // field count expects `Option<Box<T>>` slots.
            for _ in 0..count_optional_inner_simples(rule) {
                field_exprs.push("None".to_string());
            }

            let construction_code = format!(
                "{}::{}({})",
                category,
                label,
                field_exprs.join(", ")
            );

            let param_values: Vec<String> = selected_leaves
                .iter()
                .map(|leaf| leaf.raw_value.clone())
                .collect();

            let display_hint = selected_leaves
                .iter()
                .map(|leaf| leaf.display.clone())
                .collect::<Vec<_>>()
                .join("_");

            ground_terms.push(GroundTerm {
                rule_label: label.clone(),
                category: category.clone(),
                construction_code,
                param_values,
                display_hint,
            });
        }
    }

    ground_terms
}

/// Opt-Group: count the number of inner Simple non-terminals nested inside
/// any `*opt(...)` group in this rule's `term_context`. The variant emission
/// flattens these inner Simples into `Option<Box<T>>` fields appearing
/// AFTER all top-level Simple fields, so test-generation construction code
/// (which gets only the top-level Simples from `extract_simple_params`)
/// must append exactly `count_optional_inner_simples(rule)` `None` literals
/// to satisfy the variant's flat field count.
///
/// Returns 0 when the rule has no Optional groups (the common case for
/// shipped grammars), so non-Optional rules pay zero cost.
pub fn count_optional_inner_simples(rule: &GrammarRule) -> usize {
    fn count_one(p: &TermParam, in_optional: bool) -> usize {
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
    rule.term_context
        .as_ref()
        .map(|ctx| ctx.iter().map(|p| count_one(p, false)).sum())
        .unwrap_or(0)
}

/// For a given rule, return the list of parameter names used in the rust_code expression.
/// This is needed by the symbolic evaluator to build the environment.
pub fn extract_param_info(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> Vec<ParamInfo> {
    let mut info = Vec::new();

    if let Some(ctx) = &rule.term_context {
        for p in ctx {
            match p {
                TermParam::Simple { name, ty } => {
                    if let TypeExpr::Base(type_ident) = ty {
                        let cat = type_ident.to_string();
                        // Determine the native type of this category
                        let native_type = language
                            .types
                            .iter()
                            .find(|t| t.name.to_string() == cat)
                            .and_then(|t| t.native_type.as_ref())
                            .map(|nt| native_type_to_string(nt));

                        info.push(ParamInfo {
                            name: name.to_string(),
                            category: cat,
                            native_type,
                        });
                    }
                },
                _ => {},
            }
        }
    }

    info
}

/// Information about a parameter for symbolic evaluation.
#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    #[allow(dead_code)]
    pub category: String,
    pub native_type: Option<String>,
}

/// Convert a raw value string to a `SymValue` for the symbolic evaluator.
/// The raw value is the Rust literal expression (e.g., "1i32", "true", "0.5f64").
pub fn raw_value_to_sym_value(
    raw: &str,
    native_type: &Option<String>,
) -> Option<super::symbolic_eval::SymValue> {
    use super::symbolic_eval::SymValue;

    let nt = native_type.as_deref()?;

    match nt {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
            // Strip type suffix and parse
            let stripped = raw
                .trim_end_matches("i32")
                .trim_end_matches("i64")
                .trim_end_matches("u32")
                .trim_end_matches("u64")
                .trim_end_matches("isize")
                .trim_end_matches("usize");
            stripped.parse::<i64>().ok().map(SymValue::Int)
        },
        "f32" | "f64" => {
            let stripped = raw
                .trim_end_matches("f32")
                .trim_end_matches("f64");
            stripped.parse::<f64>().ok().map(SymValue::Float)
        },
        "bool" => match raw {
            "true" => Some(SymValue::Bool(true)),
            "false" => Some(SymValue::Bool(false)),
            _ => None,
        },
        "str" | "String" => {
            // Extract string content from String::from("...") or String::new()
            if raw == "String::new()" {
                Some(SymValue::Str(String::new()))
            } else if raw.starts_with("String::from(\"") && raw.ends_with("\")") {
                let inner = &raw["String::from(\"".len()..raw.len() - "\")".len()];
                Some(SymValue::Str(inner.to_string()))
            } else {
                None
            }
        },
        _ => None,
    }
}
