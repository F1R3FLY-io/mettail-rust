//! Proptest-based expression string generator from `LanguageSpec`.
//!
//! Walks grammar rules to produce syntactically valid expression strings
//! for benchmarking and property testing. Works directly from grammar structure
//! — no generated AST types needed.
//!
//! # Usage
//!
//! ```ignore
//! use mettail_prattail::grammar_gen::{arb_expression, generate_bench_inputs};
//!
//! let inputs = generate_bench_inputs(&spec, "Expr", 5, 50);
//! ```

use std::collections::BTreeMap;

use proptest::prelude::*;
use proptest::test_runner::TestRunner;

use crate::{LanguageSpec, RuleSpec, SyntaxItemSpec};

// ══════════════════════════════════════════════════════════════════════════════
// Identifier pools for generated expressions
// ══════════════════════════════════════════════════════════════════════════════

const IDENT_POOL: &[&str] = &["a", "b", "c", "x", "y", "z"];
const BINDER_POOL: &[&str] = &["x", "y", "z"];

fn arb_ident() -> BoxedStrategy<String> {
    prop::sample::select(IDENT_POOL)
        .prop_map(|s| s.to_string())
        .boxed()
}

fn arb_binder() -> BoxedStrategy<String> {
    prop::sample::select(BINDER_POOL)
        .prop_map(|s| s.to_string())
        .boxed()
}

fn fallback_ident() -> String {
    IDENT_POOL[0].to_string()
}

// ══════════════════════════════════════════════════════════════════════════════
// Public API
// ══════════════════════════════════════════════════════════════════════════════

/// Build a proptest strategy that generates syntactically valid expression
/// strings for a given category within a `LanguageSpec` grammar.
///
/// # Arguments
/// - `spec`: The language specification
/// - `category`: The target category (e.g., "Expr", "Proc")
/// - `max_depth`: Maximum nesting depth for recursive rules
///
/// # Returns
/// A boxed proptest strategy producing `String` expressions.
pub fn arb_expression(
    spec: &LanguageSpec,
    category: &str,
    max_depth: u32,
) -> BoxedStrategy<String> {
    // Group rules by category
    let rules_by_cat = group_rules_by_category(spec);
    let cat_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();

    arb_expression_inner(&rules_by_cat, category, max_depth, &cat_names)
}

/// Pre-generate a batch of deterministic expression strings for benchmarking.
///
/// Uses `TestRunner::deterministic()` for reproducible output across runs.
///
/// # Arguments
/// - `spec`: The language specification
/// - `category`: The target category
/// - `max_depth`: Maximum nesting depth
/// - `count`: Number of expressions to generate
///
/// # Returns
/// A vector of `count` expression strings.
pub fn generate_bench_inputs(
    spec: &LanguageSpec,
    category: &str,
    max_depth: u32,
    count: usize,
) -> Vec<String> {
    let strategy = arb_expression(spec, category, max_depth);
    let mut runner = TestRunner::deterministic();
    let mut inputs = Vec::with_capacity(count);

    for _ in 0..count {
        let value = strategy
            .new_tree(&mut runner)
            .expect("failed to generate expression")
            .current();
        inputs.push(value);
    }

    inputs
}

// ══════════════════════════════════════════════════════════════════════════════
// Internal implementation
// ══════════════════════════════════════════════════════════════════════════════

/// Group rules by their category for efficient lookup.
fn group_rules_by_category(spec: &LanguageSpec) -> BTreeMap<String, Vec<&RuleSpec>> {
    let mut map: BTreeMap<String, Vec<&RuleSpec>> = BTreeMap::new();
    for rule in &spec.rules {
        map.entry(rule.category.clone()).or_default().push(rule);
    }
    map
}

/// Check if a rule is a "leaf" rule (produces no recursive NonTerminal children
/// in the same or any other grammar category).
fn is_leaf_rule(rule: &RuleSpec, cat_names: &[String]) -> bool {
    if rule.is_var || rule.is_literal {
        return true;
    }
    // A rule is a leaf if none of its syntax items are NonTerminals referencing
    // grammar categories (which would require recursive generation).
    !rule
        .syntax
        .iter()
        .any(|item| has_nonterminal(item, cat_names))
}

/// Check if a syntax item contains a NonTerminal referencing a grammar category.
fn has_nonterminal(item: &SyntaxItemSpec, cat_names: &[String]) -> bool {
    match item {
        SyntaxItemSpec::NonTerminal { category, .. } => cat_names.contains(category),
        SyntaxItemSpec::Collection { element_category, .. } => cat_names.contains(element_category),
        SyntaxItemSpec::ZipMapSep { body_items, .. } => {
            body_items.iter().any(|bi| has_nonterminal(bi, cat_names))
        },
        SyntaxItemSpec::Optional { inner } => inner.iter().any(|i| has_nonterminal(i, cat_names)),
        SyntaxItemSpec::Terminal(_)
        | SyntaxItemSpec::IdentCapture { .. }
        | SyntaxItemSpec::Binder { .. }
        | SyntaxItemSpec::BinderCollection { .. } => false,
    }
}

/// Build a strategy for a category, using `prop_recursive` for depth-bounded
/// recursive generation.
fn arb_expression_inner(
    rules_by_cat: &BTreeMap<String, Vec<&RuleSpec>>,
    category: &str,
    max_depth: u32,
    cat_names: &[String],
) -> BoxedStrategy<String> {
    let rules = match rules_by_cat.get(category) {
        Some(rules) => rules.clone(),
        None => return Just(format!("__unknown_cat_{}", category)).boxed(),
    };

    // Partition into leaf and recursive rules
    let leaf_rules: Vec<&RuleSpec> = rules
        .iter()
        .filter(|r| is_leaf_rule(r, cat_names))
        .copied()
        .collect();
    let recursive_rules: Vec<&RuleSpec> = rules
        .iter()
        .filter(|r| !is_leaf_rule(r, cat_names))
        .copied()
        .collect();

    // Build leaf strategy
    let leaf_strategy = if leaf_rules.is_empty() {
        arb_ident()
    } else {
        let leaf_strats: Vec<BoxedStrategy<String>> = leaf_rules
            .iter()
            .map(|r| rule_to_leaf_strategy(r))
            .collect();
        prop::strategy::Union::new(leaf_strats).boxed()
    };

    if recursive_rules.is_empty() || max_depth == 0 {
        return leaf_strategy;
    }

    // Use prop_recursive to build depth-bounded recursive strategies.
    // The closure receives an `inner` strategy representing the current depth level.
    let rules_by_cat_owned: BTreeMap<String, Vec<RuleSpecOwned>> = rules_by_cat
        .iter()
        .map(|(k, v)| (k.clone(), v.iter().map(|r| RuleSpecOwned::from(*r)).collect()))
        .collect();
    let cat_names_owned = cat_names.to_vec();
    let category_owned = category.to_string();

    leaf_strategy
        .prop_recursive(
            max_depth, // depth
            256,       // max size
            4,         // items per collection
            move |inner| {
                build_recursive_strategy(
                    &rules_by_cat_owned,
                    &category_owned,
                    &cat_names_owned,
                    inner,
                )
            },
        )
        .boxed()
}

/// Build a strategy for a single leaf rule (no recursive NonTerminals).
fn rule_to_leaf_strategy(rule: &RuleSpec) -> BoxedStrategy<String> {
    if rule.is_var {
        return arb_ident();
    }
    if rule.is_literal {
        // Generate a native literal based on the rule label
        let label_lower = rule.label.to_lowercase();
        if label_lower.contains("bool") {
            return prop_oneof![Just("true".to_string()), Just("false".to_string())].boxed();
        }
        if label_lower.contains("str") {
            return prop_oneof![Just("\"hello\"".to_string()), Just("\"world\"".to_string()),]
                .boxed();
        }
        if label_lower.contains("float") {
            return prop_oneof![Just("1.0".to_string()), Just("3.14".to_string()),].boxed();
        }
        // Default: integer literal
        return (1..100i64).prop_map(|n| n.to_string()).boxed();
    }

    // Terminal-only rule: concatenate terminals with spaces
    let parts: Vec<String> = rule
        .syntax
        .iter()
        .filter_map(|item| match item {
            SyntaxItemSpec::Terminal(t) => Some(t.clone()),
            SyntaxItemSpec::IdentCapture { .. } | SyntaxItemSpec::Binder { .. } => {
                Some(fallback_ident())
            },
            _ => None,
        })
        .collect();

    if parts.is_empty() {
        Just(fallback_ident()).boxed()
    } else {
        Just(join_with_spacing(&parts)).boxed()
    }
}

/// Build the recursive strategy from all rules for a category.
///
/// Called by `prop_recursive`'s closure with the `inner` strategy for same-category
/// recursive references.
fn build_recursive_strategy(
    rules_by_cat: &BTreeMap<String, Vec<RuleSpecOwned>>,
    category: &str,
    cat_names: &[String],
    inner: BoxedStrategy<String>,
) -> BoxedStrategy<String> {
    let rules = match rules_by_cat.get(category) {
        Some(rules) => rules,
        None => return Just(format!("__unknown_cat_{}", category)).boxed(),
    };

    let strats: Vec<BoxedStrategy<String>> = rules
        .iter()
        .map(|r| rule_to_strategy(r, rules_by_cat, cat_names, &inner, category))
        .collect();

    if strats.is_empty() {
        Just(fallback_ident()).boxed()
    } else {
        prop::strategy::Union::new(strats).boxed()
    }
}

/// Convert a single rule to a proptest strategy.
///
/// For each syntax item, builds a sub-strategy and composes them into a
/// space-separated string.
fn rule_to_strategy(
    rule: &RuleSpecOwned,
    rules_by_cat: &BTreeMap<String, Vec<RuleSpecOwned>>,
    cat_names: &[String],
    inner: &BoxedStrategy<String>,
    current_cat: &str,
) -> BoxedStrategy<String> {
    if rule.is_var {
        return arb_ident();
    }
    if rule.is_literal {
        let label_lower = rule.label.to_lowercase();
        if label_lower.contains("bool") {
            return prop_oneof![Just("true".to_string()), Just("false".to_string())].boxed();
        }
        if label_lower.contains("str") {
            return Just("\"hello\"".to_string()).boxed();
        }
        if label_lower.contains("float") {
            return prop_oneof![Just("1.0".to_string()), Just("3.14".to_string())].boxed();
        }
        return (1..100i64).prop_map(|n| n.to_string()).boxed();
    }

    // Build strategies for each syntax item
    let item_strats: Vec<BoxedStrategy<String>> = rule
        .syntax
        .iter()
        .map(|item| syntax_item_strategy(item, rules_by_cat, cat_names, inner, current_cat))
        .collect();

    match item_strats.len() {
        0 => Just(fallback_ident()).boxed(),
        1 => item_strats.into_iter().next().expect("checked len == 1"),
        _ => {
            // Compose multiple strategies into a space-separated string
            item_strats
                .into_iter()
                .fold(Just(String::new()).boxed(), |acc, next| {
                    (acc, next)
                        .prop_map(|(a, b)| if a.is_empty() { b } else { smart_join(&a, &b) })
                        .boxed()
                })
        },
    }
}

/// Build a strategy for a single syntax item.
fn syntax_item_strategy(
    item: &SyntaxItemSpec,
    rules_by_cat: &BTreeMap<String, Vec<RuleSpecOwned>>,
    cat_names: &[String],
    inner: &BoxedStrategy<String>,
    current_cat: &str,
) -> BoxedStrategy<String> {
    match item {
        SyntaxItemSpec::Terminal(t) => Just(t.clone()).boxed(),

        SyntaxItemSpec::NonTerminal { category, .. } => {
            if category == current_cat {
                inner.clone()
            } else if cat_names.contains(category) {
                cross_category_leaf_strategy(rules_by_cat, category)
            } else {
                Just(fallback_ident()).boxed()
            }
        },

        SyntaxItemSpec::IdentCapture { .. } => arb_ident(),

        SyntaxItemSpec::Binder { .. } => arb_binder(),

        SyntaxItemSpec::BinderCollection { separator, .. } => {
            let sep = separator.clone();
            prop::collection::vec(arb_binder(), 1..=3)
                .prop_map(move |v| v.join(&format!(" {} ", sep)))
                .boxed()
        },

        SyntaxItemSpec::Collection { element_category, separator, .. } => {
            let elem_strat = if element_category == current_cat {
                inner.clone()
            } else if cat_names.contains(element_category) {
                cross_category_leaf_strategy(rules_by_cat, element_category)
            } else {
                Just(fallback_ident()).boxed()
            };

            let sep = separator.clone();
            prop::collection::vec(elem_strat, 1..=3)
                .prop_map(move |v| v.join(&format!(" {} ", sep)))
                .boxed()
        },

        SyntaxItemSpec::ZipMapSep { body_items, separator, .. } => {
            // Generate each body element then join with separator
            let body_strat: Vec<BoxedStrategy<String>> = body_items
                .iter()
                .map(|bi| syntax_item_strategy(bi, rules_by_cat, cat_names, inner, current_cat))
                .collect();

            let sep = separator.clone();
            if body_strat.is_empty() {
                Just(fallback_ident()).boxed()
            } else {
                // Generate 1-3 copies of the body pattern
                let body_vec_strat: BoxedStrategy<String> =
                    body_strat
                        .into_iter()
                        .fold(Just(String::new()).boxed(), |acc, next| {
                            (acc, next)
                                .prop_map(
                                    |(a, b)| {
                                        if a.is_empty() {
                                            b
                                        } else {
                                            smart_join(&a, &b)
                                        }
                                    },
                                )
                                .boxed()
                        });

                prop::collection::vec(body_vec_strat, 1..=3)
                    .prop_map(move |v| v.join(&format!(" {} ", sep)))
                    .boxed()
            }
        },

        SyntaxItemSpec::Optional { inner: opt_items } => {
            let inner_strats: Vec<BoxedStrategy<String>> = opt_items
                .iter()
                .map(|i| syntax_item_strategy(i, rules_by_cat, cat_names, inner, current_cat))
                .collect();

            if inner_strats.is_empty() {
                Just(String::new()).boxed()
            } else {
                let combined =
                    inner_strats
                        .into_iter()
                        .fold(Just(String::new()).boxed(), |acc, next| {
                            (acc, next)
                                .prop_map(
                                    |(a, b)| {
                                        if a.is_empty() {
                                            b
                                        } else {
                                            smart_join(&a, &b)
                                        }
                                    },
                                )
                                .boxed()
                        });

                prop_oneof![Just(String::new()), combined,].boxed()
            }
        },
    }
}

/// Build a leaf-only strategy for a cross-category reference.
fn cross_category_leaf_strategy(
    rules_by_cat: &BTreeMap<String, Vec<RuleSpecOwned>>,
    category: &str,
) -> BoxedStrategy<String> {
    let cat_names_empty: Vec<String> = Vec::new();
    let rules = match rules_by_cat.get(category) {
        Some(rules) => rules,
        None => return Just(fallback_ident()).boxed(),
    };

    let leaf_rules: Vec<&RuleSpecOwned> = rules
        .iter()
        .filter(|r| is_leaf_rule_owned(r, &cat_names_empty))
        .collect();

    if leaf_rules.is_empty() {
        return arb_ident();
    }

    let strats: Vec<BoxedStrategy<String>> = leaf_rules
        .iter()
        .map(|r| rule_to_leaf_strategy_owned(r))
        .collect();

    prop::strategy::Union::new(strats).boxed()
}

fn is_leaf_rule_owned(rule: &RuleSpecOwned, _cat_names: &[String]) -> bool {
    rule.is_var
        || rule.is_literal
        || rule.syntax.iter().all(|item| {
            matches!(
                item,
                SyntaxItemSpec::Terminal(_)
                    | SyntaxItemSpec::IdentCapture { .. }
                    | SyntaxItemSpec::Binder { .. }
            )
        })
}

fn rule_to_leaf_strategy_owned(rule: &RuleSpecOwned) -> BoxedStrategy<String> {
    if rule.is_var {
        return arb_ident();
    }
    if rule.is_literal {
        let label_lower = rule.label.to_lowercase();
        if label_lower.contains("bool") {
            return prop_oneof![Just("true".to_string()), Just("false".to_string())].boxed();
        }
        if label_lower.contains("str") {
            return Just("\"hello\"".to_string()).boxed();
        }
        if label_lower.contains("float") {
            return Just("1.0".to_string()).boxed();
        }
        return (1..100i64).prop_map(|n| n.to_string()).boxed();
    }

    let parts: Vec<String> = rule
        .syntax
        .iter()
        .filter_map(|item| match item {
            SyntaxItemSpec::Terminal(t) => Some(t.clone()),
            SyntaxItemSpec::IdentCapture { .. } | SyntaxItemSpec::Binder { .. } => {
                Some(fallback_ident())
            },
            _ => None,
        })
        .collect();

    if parts.is_empty() {
        Just(fallback_ident()).boxed()
    } else {
        Just(join_with_spacing(&parts)).boxed()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Spacing helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Join two string fragments with smart spacing.
///
/// Inserts a space between items except around structural delimiters
/// where no space is needed.
fn smart_join(left: &str, right: &str) -> String {
    if left.is_empty() {
        return right.to_string();
    }
    if right.is_empty() {
        return left.to_string();
    }

    let last_char = left.chars().last().unwrap_or(' ');
    let first_char = right.chars().next().unwrap_or(' ');

    // No space needed after opening delimiters or before closing delimiters/comma
    let no_space_after = matches!(last_char, '(' | '{' | '[');
    let no_space_before = matches!(first_char, ')' | '}' | ']' | ',');

    if no_space_after || no_space_before {
        format!("{}{}", left, right)
    } else {
        format!("{} {}", left, right)
    }
}

/// Join a slice of strings with smart spacing.
fn join_with_spacing(parts: &[String]) -> String {
    if parts.is_empty() {
        return String::new();
    }
    let mut result = parts[0].clone();
    for part in &parts[1..] {
        result = smart_join(&result, part);
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Owned RuleSpec for use in closures (avoids lifetime issues with prop_recursive)
// ══════════════════════════════════════════════════════════════════════════════

/// Lightweight owned copy of the fields from `RuleSpec` needed for generation.
///
/// `prop_recursive` requires `'static` closures, so we can't hold `&RuleSpec`
/// references. This struct holds just the fields we need.
#[derive(Clone, Debug)]
struct RuleSpecOwned {
    label: String,
    syntax: Vec<SyntaxItemSpec>,
    is_var: bool,
    is_literal: bool,
}

impl RuleSpecOwned {
    fn from(rule: &RuleSpec) -> Self {
        RuleSpecOwned {
            label: rule.label.clone(),
            syntax: rule.syntax.clone(),
            is_var: rule.is_var,
            is_literal: rule.is_literal,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BeamWidthConfig, CategorySpec, DispatchStrategy, LanguageSpec, LiteralPatterns, RuleSpec,
        SyntaxItemSpec,
    };

    /// Build a minimal calculator spec for testing.
    fn calculator_spec() -> LanguageSpec {
        let cat_names = vec!["Expr".to_string()];
        LanguageSpec {
            name: "Calc".to_string(),
            types: vec![CategorySpec {
                name: "Expr".to_string(),
                native_type: Some("i64".to_string()),
                is_primary: true,
            }],
            rules: vec![
                RuleSpec::classified("NumLit", "Expr", vec![], &cat_names),
                RuleSpec::classified(
                    "EVar",
                    "Expr",
                    vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                    &cat_names,
                ),
                RuleSpec::classified(
                    "Add",
                    "Expr",
                    vec![
                        SyntaxItemSpec::NonTerminal {
                            category: "Expr".to_string(),
                            param_name: "a".to_string(),
                        },
                        SyntaxItemSpec::Terminal("+".to_string()),
                        SyntaxItemSpec::NonTerminal {
                            category: "Expr".to_string(),
                            param_name: "b".to_string(),
                        },
                    ],
                    &cat_names,
                ),
                RuleSpec::classified(
                    "Neg",
                    "Expr",
                    vec![
                        SyntaxItemSpec::Terminal("-".to_string()),
                        SyntaxItemSpec::NonTerminal {
                            category: "Expr".to_string(),
                            param_name: "a".to_string(),
                        },
                    ],
                    &cat_names,
                ),
            ],
            beam_width: BeamWidthConfig::Disabled,
            log_semiring_model_path: None,
            dispatch_strategy: DispatchStrategy::Static,
            literal_patterns: LiteralPatterns::default(),
        }
    }

    #[test]
    fn test_nonempty_expressions() {
        let spec = calculator_spec();
        let inputs = generate_bench_inputs(&spec, "Expr", 3, 20);
        assert_eq!(inputs.len(), 20, "should generate exactly 20 inputs");
        for (i, expr) in inputs.iter().enumerate() {
            assert!(!expr.is_empty(), "expression {} should be non-empty: {:?}", i, expr);
        }
    }

    #[test]
    fn test_deterministic_generation() {
        let spec = calculator_spec();
        let a = generate_bench_inputs(&spec, "Expr", 3, 10);
        let b = generate_bench_inputs(&spec, "Expr", 3, 10);
        assert_eq!(a, b, "same seed should produce same output");
    }

    #[test]
    fn test_depth_zero_produces_leaves() {
        let spec = calculator_spec();
        let inputs = generate_bench_inputs(&spec, "Expr", 0, 20);
        for expr in &inputs {
            assert!(
                !expr.contains('+'),
                "depth 0 should produce only leaves (no '+' operator): {:?}",
                expr
            );
        }
    }

    #[test]
    fn test_depth_positive_produces_operators() {
        let spec = calculator_spec();
        let inputs = generate_bench_inputs(&spec, "Expr", 5, 100);
        let has_operator = inputs.iter().any(|e| e.contains('+') || e.contains('-'));
        assert!(has_operator, "depth 5 with 100 samples should produce at least one operator");
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(50))]

        #[test]
        fn prop_expressions_nonempty(
            expr in arb_expression(&calculator_spec(), "Expr", 3)
        ) {
            proptest::prop_assert!(!expr.is_empty());
        }
    }
}
