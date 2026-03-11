//! Shared arbitrary grammar generators for property-based tests.
//!
//! Provides reusable `proptest` strategies for generating random grammars,
//! categories, rules, and syntax items.  Used across all analysis module
//! proptest suites.
//!
//! # Design principles
//!
//! * **Depth-bounded recursion** — `arb_syntax_item(depth)` bottoms out at
//!   leaf variants (`Terminal`, `IdentCapture`) when `depth == 0`, preventing
//!   unbounded strategy expansion.
//! * **Category-coherent grammars** — `arb_grammar` first selects a set of
//!   category names, then passes those names into `arb_rule` so that every
//!   `NonTerminal` / `Binder` / `Collection` reference targets an actual
//!   category.
//! * **Deterministic labels** — rule labels are constructed as
//!   `"<Category>::R<index>"` to guarantee uniqueness within a category.
//! * **Bias toward simplicity** — the item strategy is weighted 50 % Terminal,
//!   25 % NonTerminal, 25 % other to keep generated grammars tractable while
//!   still exercising structural variety.

use proptest::prelude::*;

use crate::pipeline::CategoryInfo;
use crate::recursive::CollectionKind;
use crate::SyntaxItemSpec;

// ══════════════════════════════════════════════════════════════════════════════
// Leaf strategies
// ══════════════════════════════════════════════════════════════════════════════

/// Fixed pool of terminal token strings.
///
/// Includes single-character operators, parentheses, and common keywords so
/// that generated grammars look vaguely realistic.
pub fn arb_terminal() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("a".to_string()),
        Just("b".to_string()),
        Just("c".to_string()),
        Just("d".to_string()),
        Just("+".to_string()),
        Just("-".to_string()),
        Just("*".to_string()),
        Just("/".to_string()),
        Just("(".to_string()),
        Just(")".to_string()),
        Just("if".to_string()),
        Just("while".to_string()),
        Just("let".to_string()),
        Just("fn".to_string()),
    ]
}

/// Fixed pool of category names.
///
/// Kept small (6 entries) so that cross-category references are likely to
/// overlap, exercising graph-connectivity code paths in analysis modules.
pub fn arb_category_name() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("Expr".to_string()),
        Just("Stmt".to_string()),
        Just("Decl".to_string()),
        Just("Type".to_string()),
        Just("Pat".to_string()),
        Just("Name".to_string()),
    ]
}

/// Generate a separator token for `Collection` / `Sep` / `BinderCollection`.
fn arb_separator() -> impl Strategy<Value = String> {
    prop_oneof![
        Just(",".to_string()),
        Just(";".to_string()),
        Just("|".to_string()),
    ]
}

/// Generate a param name for captures, binders, and nonterminals.
fn arb_param_name() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("lhs".to_string()),
        Just("rhs".to_string()),
        Just("body".to_string()),
        Just("cond".to_string()),
        Just("name".to_string()),
        Just("arg".to_string()),
        Just("val".to_string()),
        Just("pat".to_string()),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════
// SyntaxItemSpec strategy
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a depth-bounded [`SyntaxItemSpec`].
///
/// At `depth == 0` only leaf items are produced (`Terminal`, `IdentCapture`).
/// At `depth > 0` the strategy can additionally produce `NonTerminal`,
/// `Binder`, `Collection`, `Sep`, `Map`, `Zip`, `BinderCollection`, and
/// `Optional`, each of which may recurse with `depth - 1`.
///
/// Weight distribution at depth > 0:
/// - 50 % `Terminal`
/// - 25 % `NonTerminal`
/// - 25 % other compound variants
pub fn arb_syntax_item(depth: u32) -> BoxedStrategy<SyntaxItemSpec> {
    arb_syntax_item_with_cats(depth, None)
}

/// Like [`arb_syntax_item`] but restricts `NonTerminal`, `Binder`, and
/// `Collection` references to the supplied category names.  When `cats` is
/// `None` the full [`arb_category_name`] pool is used.
pub fn arb_syntax_item_with_cats(
    depth: u32,
    cats: Option<Vec<String>>,
) -> BoxedStrategy<SyntaxItemSpec> {
    if depth == 0 {
        // Leaf items only.
        prop_oneof![
            8 => arb_terminal().prop_map(SyntaxItemSpec::Terminal),
            2 => arb_param_name().prop_map(|p| SyntaxItemSpec::IdentCapture { param_name: p }),
        ]
        .boxed()
    } else {
        // Clone cat_strategy via sharing.  We build separate boxed copies for
        // each branch that needs a category reference.
        let cats_owned: Option<Vec<String>> = cats;
        let cats_for_nt = cats_owned.clone();
        let cats_for_binder = cats_owned.clone();
        let cats_for_collection = cats_owned.clone();
        let cats_for_sep = cats_owned.clone();
        let cats_for_map = cats_owned.clone();
        let cats_for_zip = cats_owned.clone();
        let cats_for_optional = cats_owned;

        let cat_nt = cat_box(cats_for_nt.clone());
        let cat_binder = cat_box(cats_for_binder.clone());
        let cat_collection = cat_box(cats_for_collection.clone());

        let d = depth - 1;

        prop_oneof![
            // ── 50 % leaf ────────────────────────────────────────────────
            10 => arb_terminal().prop_map(SyntaxItemSpec::Terminal),

            // ── 25 % NonTerminal ─────────────────────────────────────────
            5 => (cat_nt, arb_param_name()).prop_map(|(category, param_name)| {
                SyntaxItemSpec::NonTerminal { category, param_name }
            }),

            // ── 25 % compound (split evenly across variants) ─────────────
            1 => arb_param_name().prop_map(|p| SyntaxItemSpec::IdentCapture { param_name: p }),

            1 => (arb_param_name(), cat_binder, prop::bool::ANY).prop_map(
                |(param_name, category, is_multi)| SyntaxItemSpec::Binder {
                    param_name,
                    category,
                    is_multi,
                },
            ),

            1 => (arb_param_name(), cat_collection, arb_separator()).prop_map(
                |(param_name, element_category, separator)| SyntaxItemSpec::Collection {
                    param_name,
                    element_category,
                    separator,
                    kind: CollectionKind::Vec,
                },
            ),

            1 => {
                let c = cats_for_sep;
                (arb_syntax_item_with_cats(d, c), arb_separator()).prop_map(
                    |(body, separator)| SyntaxItemSpec::Sep {
                        body: Box::new(body),
                        separator,
                        kind: CollectionKind::Vec,
                    },
                )
            },

            1 => {
                let c = cats_for_map;
                prop::collection::vec(arb_syntax_item_with_cats(d, c), 1..=3)
                    .prop_map(|body_items| SyntaxItemSpec::Map { body_items })
            },

            1 => {
                let c = cats_for_zip.clone();
                let c2 = cats_for_zip;
                (
                    arb_param_name(),
                    arb_param_name(),
                    cat_box(c),
                    cat_box(c2),
                    arb_syntax_item_with_cats(d, None),
                )
                    .prop_map(
                        |(left_name, right_name, left_category, right_category, body)| {
                            SyntaxItemSpec::Zip {
                                left_name,
                                right_name,
                                left_category,
                                right_category,
                                body: Box::new(body),
                            }
                        },
                    )
            },

            1 => (arb_param_name(), arb_separator()).prop_map(|(param_name, separator)| {
                SyntaxItemSpec::BinderCollection {
                    param_name,
                    separator,
                }
            }),

            1 => {
                let c = cats_for_optional;
                prop::collection::vec(arb_syntax_item_with_cats(d, c), 1..=3)
                    .prop_map(|inner| SyntaxItemSpec::Optional { inner })
            },
        ]
        .boxed()
    }
}

/// Helper: produce a boxed category strategy from an optional name list.
fn cat_box(cats: Option<Vec<String>>) -> BoxedStrategy<String> {
    match cats {
        Some(names) if !names.is_empty() => prop::sample::select(names).boxed(),
        _ => arb_category_name().boxed(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Rule strategy
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a single rule tuple `(label, category_name, items)`.
///
/// * `cat_names` — the set of category names that `NonTerminal` / `Binder` /
///   `Collection` references may target.
/// * Labels are of the form `"<Category>::R<n>"` where `n` is drawn from
///   `0..100` so that collisions are unlikely across a small set of generated
///   rules for the same category.
pub fn arb_rule(
    cat_names: Vec<String>,
) -> impl Strategy<Value = (String, String, Vec<SyntaxItemSpec>)> {
    let cats_for_pick = cat_names.clone();
    let cats_for_items = cat_names;

    (
        prop::sample::select(cats_for_pick),
        0..100u32,
        prop::collection::vec(arb_syntax_item_with_cats(2, Some(cats_for_items)), 1..=5),
    )
        .prop_map(|(cat, idx, items)| {
            let label = format!("{}::R{}", cat, idx);
            (label, cat, items)
        })
}

/// Generate multiple rules for a single category.
///
/// Each rule receives a deterministic label `"<cat_name>::R<i>"` where `i` is
/// its zero-based index within the category, guaranteeing uniqueness.
pub fn arb_rules_for_category(
    cat_name: String,
    cat_names: Vec<String>,
    num_rules: std::ops::Range<usize>,
) -> impl Strategy<Value = Vec<(String, String, Vec<SyntaxItemSpec>)>> {
    prop::collection::vec(
        prop::collection::vec(arb_syntax_item_with_cats(2, Some(cat_names.clone())), 1..=5),
        num_rules,
    )
    .prop_map(move |items_vec| {
        items_vec
            .into_iter()
            .enumerate()
            .map(|(i, items)| {
                let label = format!("{}::R{}", cat_name, i);
                (label, cat_name.clone(), items)
            })
            .collect()
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Grammar strategy
// ══════════════════════════════════════════════════════════════════════════════

/// All six category names from [`arb_category_name`] in a fixed order.
const ALL_CATEGORY_NAMES: [&str; 6] = ["Expr", "Stmt", "Decl", "Type", "Pat", "Name"];

/// Generate a complete grammar: a list of [`CategoryInfo`] and a flat list of
/// rule tuples suitable for passing to `analyze_from_bundle`.
///
/// Invariants:
/// - `num_cats` categories are sampled (without replacement) from the fixed
///   pool.
/// - The **first** category always has `is_primary: true`; all others have
///   `is_primary: false`.
/// - Every rule's `NonTerminal` / `Binder` / `Collection` references target
///   only the categories present in this grammar.
/// - Rule labels are unique: `"<Category>::R<index>"`.
pub fn arb_grammar(
    num_cats: std::ops::Range<usize>,
    rules_per_cat: std::ops::Range<usize>,
) -> impl Strategy<Value = (Vec<CategoryInfo>, Vec<(String, String, Vec<SyntaxItemSpec>)>)> {
    // Clamp the upper bound to the pool size.
    let max_cats = num_cats.end.min(ALL_CATEGORY_NAMES.len());
    let min_cats = num_cats.start.max(1).min(max_cats);

    let pool: Vec<String> = ALL_CATEGORY_NAMES.iter().map(|s| s.to_string()).collect();

    // Step 1: choose a subsequence of the pool (min_cats..=max_cats elements).
    prop::sample::subsequence(pool, min_cats..=max_cats).prop_flat_map(move |cat_names| {
        let rpc = rules_per_cat.clone();
        let cat_names_inner = cat_names.clone();

        // Step 2: for each category, generate `rules_per_cat` rules.
        let rule_strategies: Vec<_> = cat_names
            .iter()
            .map(|name| {
                arb_rules_for_category(name.clone(), cat_names_inner.clone(), rpc.clone())
            })
            .collect();

        // Combine all per-category rule vectors.
        rule_strategies.prop_map(move |per_cat_rules| {
            let categories: Vec<CategoryInfo> = cat_names
                .iter()
                .enumerate()
                .map(|(i, name)| CategoryInfo {
                    name: name.clone(),
                    native_type: None,
                    is_primary: i == 0,
                })
                .collect();

            let all_rules: Vec<(String, String, Vec<SyntaxItemSpec>)> =
                per_cat_rules.into_iter().flatten().collect();

            (categories, all_rules)
        })
    })
}

/// Convenience wrapper: small grammar with 1-3 categories and 1-4 rules each.
///
/// Suitable for quick proptest runs that need a structurally valid grammar
/// without excessive combinatorial blowup.
pub fn arb_small_grammar(
) -> impl Strategy<Value = (Vec<CategoryInfo>, Vec<(String, String, Vec<SyntaxItemSpec>)>)> {
    arb_grammar(1..4, 1..5)
}

// ══════════════════════════════════════════════════════════════════════════════
// CategoryInfo strategy
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a single [`CategoryInfo`] with a name from the fixed pool.
pub fn arb_category_info() -> impl Strategy<Value = CategoryInfo> {
    (arb_category_name(), prop::bool::ANY).prop_map(|(name, is_primary)| CategoryInfo {
        name,
        native_type: None,
        is_primary,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests — verify the generators themselves produce valid data
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(50))]

        /// Every terminal strategy value is a non-empty string.
        #[test]
        fn terminal_is_nonempty(t in arb_terminal()) {
            prop_assert!(!t.is_empty());
        }

        /// Category names are always from the fixed pool.
        #[test]
        fn category_name_in_pool(name in arb_category_name()) {
            prop_assert!(ALL_CATEGORY_NAMES.contains(&name.as_str()));
        }

        /// Depth-0 items are always leaves (Terminal or IdentCapture).
        #[test]
        fn depth0_is_leaf(item in arb_syntax_item(0)) {
            match item {
                SyntaxItemSpec::Terminal(_) | SyntaxItemSpec::IdentCapture { .. } => {}
                other => prop_assert!(false, "depth-0 produced non-leaf: {:?}", other),
            }
        }

        /// Grammar invariant: first category is primary, rest are not.
        #[test]
        fn grammar_primary_invariant(
            (cats, rules) in arb_grammar(1..4, 1..3),
        ) {
            prop_assert!(!cats.is_empty(), "grammar must have at least one category");
            prop_assert!(cats[0].is_primary, "first category must be primary");
            for c in &cats[1..] {
                prop_assert!(!c.is_primary, "non-first category must not be primary");
            }

            // Every rule references a category that exists in the grammar.
            let cat_set: std::collections::HashSet<&str> =
                cats.iter().map(|c| c.name.as_str()).collect();
            for (label, cat_name, _) in &rules {
                prop_assert!(
                    cat_set.contains(cat_name.as_str()),
                    "rule {} references unknown category {}",
                    label,
                    cat_name,
                );
            }
        }

        /// Rule labels are unique across the entire grammar.
        #[test]
        fn grammar_labels_unique(
            (_cats, rules) in arb_grammar(2..5, 1..4),
        ) {
            let mut seen = std::collections::HashSet::new();
            for (label, _, _) in &rules {
                prop_assert!(seen.insert(label.clone()), "duplicate label: {}", label);
            }
        }

        /// Every rule has at least one syntax item.
        #[test]
        fn rules_nonempty_items(
            (_cats, rules) in arb_small_grammar(),
        ) {
            for (label, _, items) in &rules {
                prop_assert!(!items.is_empty(), "rule {} has no items", label);
            }
        }
    }
}
