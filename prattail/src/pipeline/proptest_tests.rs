use super::*;
use crate::prediction::RuleInfo;
use proptest::prelude::*;
use std::collections::{HashMap, HashSet};

/// Helper: create a RuleInfo with sensible defaults.
#[allow(dead_code)]
fn rule(label: &str, category: &str) -> RuleInfo {
    RuleInfo {
        label: label.to_string(),
        category: category.to_string(),
        first_items: Vec::new(),
        is_infix: false,
        is_var: false,
        is_literal: false,
        is_cross_category: false,
        is_cast: false,
    }
}

/// Helper: create a CategoryInfo.
fn category(name: &str, is_primary: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: None,
        is_primary,
        has_var: true,
    }
}

/// Helper: construct an empty AdvancedAnalysisBundle (all fields None).
fn empty_bundle<'a>() -> super::AdvancedAnalysisBundle<'a> {
    super::AdvancedAnalysisBundle {
        symbolic: None,
        alternating: None,
        #[cfg(feature = "oslf-bisimulation")]
        bisimulation: None,
        vpa: None,
        register: None,
        probabilistic: None,
        multi_tape: None,
        buchi: None,
        _phantom: std::marker::PhantomData,
    }
}

/// Helper: call build_pipeline_analysis with minimal inputs and a given bundle.
fn run_build_pipeline(
    dead_rules: &HashSet<String>,
    prediction_wfsts: &HashMap<String, crate::wfst::PredictionWfst>,
    categories: &[CategoryInfo],
    rule_infos: &[RuleInfo],
    bundle: &super::AdvancedAnalysisBundle<'_>,
) -> crate::PipelineAnalysis {
    super::build_pipeline_analysis(
        dead_rules,
        prediction_wfsts,
        categories,
        rule_infos,
        HashMap::new(), // decision_trees
        bundle,
    )
}

/// Helper: build a single-state, single-action PredictionWfst for the given
/// category and rule label, with the specified tropical weight.
fn make_wfst(cat: &str, rule_label: &str, weight: f64) -> crate::wfst::PredictionWfst {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    let mut w = PredictionWfst {
        category: cat.into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: rule_label.into(),
                parse_fn: format!("parse_{rule_label}"),
            },
            weight: TropicalWeight::new(weight),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    w.states[0].is_final = true;
    w
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint A3: Bisimilar weight discount (feature = "alternating")
// ══════════════════════════════════════════════════════════════════════════

/// Strategy: generate a pair of distinct category names (ASCII alpha, 1..8 chars)
/// where `first < second` lexicographically. Both names start with an uppercase
/// letter to mimic real grammar category names.
fn arb_category_pair() -> impl Strategy<Value = (String, String)> {
    // Generate two distinct uppercase-starting names, then sort them.
    ("[A-Z][a-z]{0,6}", "[A-Z][a-z]{0,6}")
        .prop_filter("category names must differ", |(a, b)| a != b)
        .prop_map(|(a, b)| {
            let mut pair = [a, b];
            pair.sort();
            (pair[0].clone(), pair[1].clone())
        })
}

/// Strategy: generate a sorted, deduplicated Vec of 2..=5 distinct category names
/// (uppercase-starting, 1..8 chars).
fn arb_category_names(min: usize, max: usize) -> impl Strategy<Value = Vec<String>> {
    proptest::collection::hash_set("[A-Z][a-z]{0,6}", min..=max).prop_map(|s| {
        let mut v: Vec<String> = s.into_iter().collect();
        v.sort();
        v
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    // ── A3.1: Bisimilar pair — lexicographic second gets +0.5 penalty ────

    /// For two bisimilar categories (a, b) where a < b lexicographically,
    /// the second (b) receives an additional +0.5 tropical weight penalty.
    #[test]
    fn prop_bisimilar_discount_lexicographic_second(
        (first, second) in arb_category_pair(),
        base_weight in 0.1_f64..100.0,
    ) {
        let alt = crate::alternating::AlternatingAnalysis {
            non_bisimilar_pairs: Vec::new(), // all pairs bisimilar
            state_count: 2,
        };
        let mut bundle = empty_bundle();
        bundle.alternating = Some(&alt);

        let r_first = format!("r_{first}");
        let r_second = format!("r_{second}");

        let mut prediction_wfsts = HashMap::new();
        prediction_wfsts.insert(first.clone(), make_wfst(&first, &r_first, base_weight));
        prediction_wfsts.insert(second.clone(), make_wfst(&second, &r_second, base_weight));

        let categories = vec![
            category(&first, true),
            category(&second, false),
        ];
        let rule_infos = vec![
            rule(&r_first, &first),
            rule(&r_second, &second),
        ];
        let dead_rules = HashSet::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        // first < second, so second is deprioritized
        let w_first = analysis.constructor_weights.get(&r_first)
            .copied()
            .expect("first category rule should have a weight");
        let w_second = analysis.constructor_weights.get(&r_second)
            .copied()
            .expect("second category rule should have a weight");

        prop_assert!(
            (w_first - base_weight).abs() < 1e-9,
            "lexicographically first category ({first}) should keep base weight {base_weight}, got {w_first}"
        );
        prop_assert!(
            (w_second - (base_weight + 0.5)).abs() < 1e-9,
            "lexicographically second category ({second}) should get +0.5 penalty: expected {}, got {w_second}",
            base_weight + 0.5
        );
    }

    // ── A3.2: Non-bisimilar pairs get no discount ────────────────────────

    /// Categories explicitly listed in `non_bisimilar_pairs` should not
    /// receive the +0.5 bisimilar discount.
    #[test]
    fn prop_non_bisimilar_no_discount(
        (first, second) in arb_category_pair(),
        w1 in 0.1_f64..100.0,
        w2 in 0.1_f64..100.0,
    ) {
        let alt = crate::alternating::AlternatingAnalysis {
            non_bisimilar_pairs: vec![(first.clone(), second.clone())],
            state_count: 2,
        };
        let mut bundle = empty_bundle();
        bundle.alternating = Some(&alt);

        let r_first = format!("r_{first}");
        let r_second = format!("r_{second}");

        let mut prediction_wfsts = HashMap::new();
        prediction_wfsts.insert(first.clone(), make_wfst(&first, &r_first, w1));
        prediction_wfsts.insert(second.clone(), make_wfst(&second, &r_second, w2));

        let categories = vec![
            category(&first, true),
            category(&second, false),
        ];
        let rule_infos = vec![
            rule(&r_first, &first),
            rule(&r_second, &second),
        ];
        let dead_rules = HashSet::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        let actual_w1 = analysis.constructor_weights.get(&r_first)
            .copied()
            .expect("first rule should have a weight");
        let actual_w2 = analysis.constructor_weights.get(&r_second)
            .copied()
            .expect("second rule should have a weight");

        prop_assert!(
            (actual_w1 - w1).abs() < 1e-9,
            "non-bisimilar {first}: weight should remain {w1}, got {actual_w1}"
        );
        prop_assert!(
            (actual_w2 - w2).abs() < 1e-9,
            "non-bisimilar {second}: weight should remain {w2}, got {actual_w2}"
        );
    }

    // ── A3.3: Bisimilar discount is exactly +0.5 ────────────────────────

    /// The discount applied to the lexicographically second category in a
    /// bisimilar pair is exactly +0.5 tropical weight.
    #[test]
    fn prop_bisimilar_discount_is_0_5(
        names in arb_category_names(2, 5),
        base_weight in 0.1_f64..100.0,
    ) {
        let alt = crate::alternating::AlternatingAnalysis {
            non_bisimilar_pairs: Vec::new(), // all pairs bisimilar
            state_count: names.len(),
        };
        let mut bundle = empty_bundle();
        bundle.alternating = Some(&alt);

        let mut prediction_wfsts = HashMap::new();
        let mut categories = Vec::new();
        let mut rule_infos = Vec::new();

        for (i, name) in names.iter().enumerate() {
            let rl = format!("r_{name}");
            prediction_wfsts.insert(name.clone(), make_wfst(name, &rl, base_weight));
            categories.push(category(name, i == 0));
            rule_infos.push(rule(&rl, name));
        }

        let dead_rules = HashSet::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        // The lexicographically smallest category keeps its base weight.
        // All others (deprioritized) get exactly +0.5.
        let smallest = &names[0]; // names is sorted
        for name in &names {
            let rl = format!("r_{name}");
            let w = analysis.constructor_weights.get(&rl)
                .copied()
                .unwrap_or(f64::NAN);

            if name == smallest {
                prop_assert!(
                    (w - base_weight).abs() < 1e-9,
                    "smallest category ({name}) should keep base weight {base_weight}, got {w}"
                );
            } else {
                let expected = base_weight + 0.5;
                prop_assert!(
                    (w - expected).abs() < 1e-9,
                    "deprioritized category ({name}) should have weight {expected}, got {w}"
                );
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint C1: Guard disambiguation (feature = "symbolic-automata")
// ══════════════════════════════════════════════════════════════════════════

/// Strategy: generate a list of subsumed guard pairs where labels follow
/// the "Category::Rule" format.
fn arb_subsumed_guards(max_pairs: usize) -> impl Strategy<Value = Vec<(String, String)>> {
    proptest::collection::vec(
        ("[A-Z][a-z]{0,4}::[A-Z][a-z]{0,4}", "[A-Z][a-z]{0,4}::[A-Z][a-z]{0,4}")
            .prop_filter("subsumed and subsumer must differ", |(a, b)| a != b),
        0..=max_pairs,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    // ── C1.1: Disambiguated tokens are a subset of subsumed labels ──────

    /// Every token in `guard_disambiguated_tokens` must come from the first
    /// element of some pair in `subsumed_guards`.
    #[test]
    fn prop_disambiguated_subset_subsumed_labels(
        subsumed_guards in arb_subsumed_guards(8),
    ) {
        let subsumed_labels: HashSet<String> = subsumed_guards
            .iter()
            .map(|(subsumed, _)| subsumed.clone())
            .collect();

        let sym = crate::symbolic::SymbolicAnalysis {
            num_states: 1,
            num_transitions: subsumed_guards.len(),
            guard_satisfiability: subsumed_guards.iter()
                .flat_map(|(a, b)| vec![(a.clone(), true), (b.clone(), true)])
                .collect(),
            overlapping_guards: Vec::new(),
            subsumed_guards,
            unsatisfiable_rule_labels: Vec::new(),
        };

        let mut bundle = empty_bundle();
        bundle.symbolic = Some(&sym);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        for token in &analysis.guard_disambiguated_tokens {
            prop_assert!(
                subsumed_labels.contains(token),
                "disambiguated token {:?} not found among subsumed labels {:?}",
                token, subsumed_labels,
            );
        }
    }

    // ── C1.2: Empty subsumed_guards ⟹ empty disambiguation ─────────────

    /// When there are no subsumed guard pairs, the disambiguation set must
    /// be empty.
    #[test]
    fn prop_no_subsumption_no_disambiguation(
        num_guards in 0_usize..5,
    ) {
        // Create guard_satisfiability entries but NO subsumed_guards.
        let guard_satisfiability: Vec<(String, bool)> = (0..num_guards)
            .map(|i| (format!("Cat::R{i}"), true))
            .collect();

        let sym = crate::symbolic::SymbolicAnalysis {
            num_states: 1,
            num_transitions: num_guards,
            guard_satisfiability,
            overlapping_guards: Vec::new(),
            subsumed_guards: Vec::new(),
            unsatisfiable_rule_labels: Vec::new(),
        };

        let mut bundle = empty_bundle();
        bundle.symbolic = Some(&sym);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        prop_assert!(
            analysis.guard_disambiguated_tokens.is_empty(),
            "empty subsumed_guards should produce empty guard_disambiguated_tokens, \
             got {:?}",
            analysis.guard_disambiguated_tokens,
        );
    }

    // ── C1.3: Every subsumed label appears in disambiguated set ─────────

    /// Every first element (the subsumed label) of each pair in
    /// `subsumed_guards` should appear in `guard_disambiguated_tokens`.
    #[test]
    fn prop_all_subsumed_all_disambiguated(
        subsumed_guards in arb_subsumed_guards(8),
    ) {
        let expected_labels: HashSet<String> = subsumed_guards
            .iter()
            .map(|(subsumed, _)| subsumed.clone())
            .collect();

        let sym = crate::symbolic::SymbolicAnalysis {
            num_states: 1,
            num_transitions: subsumed_guards.len(),
            guard_satisfiability: subsumed_guards.iter()
                .flat_map(|(a, b)| vec![(a.clone(), true), (b.clone(), true)])
                .collect(),
            overlapping_guards: Vec::new(),
            subsumed_guards,
            unsatisfiable_rule_labels: Vec::new(),
        };

        let mut bundle = empty_bundle();
        bundle.symbolic = Some(&sym);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        for label in &expected_labels {
            prop_assert!(
                analysis.guard_disambiguated_tokens.contains(label),
                "subsumed label {:?} should appear in guard_disambiguated_tokens, \
                 got {:?}",
                label, analysis.guard_disambiguated_tokens,
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint C3: Per-category entropy (feature = "probabilistic")
// ══════════════════════════════════════════════════════════════════════════

/// Strategy: generate a HashMap of `"Cat::RuleN" -> selectivity` entries
/// for a single category, with `n` rules and positive selectivities.
fn arb_single_cat_selectivities(
    cat: &str,
    n: usize,
) -> impl Strategy<Value = HashMap<String, f64>> {
    let cat = cat.to_string();
    proptest::collection::vec(0.01_f64..10.0, n).prop_map(move |weights| {
        weights
            .into_iter()
            .enumerate()
            .map(|(i, w)| (format!("{cat}::R{i}"), w))
            .collect()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    // ── C3.1: All entropy values are non-negative ───────────────────────

    /// Shannon entropy is always non-negative. This verifies that for any
    /// set of rule selectivities, every value in `per_category_entropy` is
    /// >= 0.0.
    #[test]
    fn prop_entropy_non_negative_all(
        selectivities in arb_single_cat_selectivities("Expr", 5),
    ) {
        let prob = crate::probabilistic::ProbabilisticAnalysis {
            num_states: 1,
            is_normalized: true,
            total_selectivity: selectivities.values().sum(),
            mean_entropy: 0.5,
            low_selectivity_rules: Vec::new(),
            rule_selectivities: selectivities,
        };
        let mut bundle = empty_bundle();
        bundle.probabilistic = Some(&prob);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        for (cat, &entropy) in &analysis.per_category_entropy {
            prop_assert!(
                entropy >= 0.0,
                "entropy for category {cat} should be >= 0.0, got {entropy}"
            );
        }
    }

    // ── C3.2: Single rule → zero entropy ───────────────────────────────

    /// A category with exactly one rule has a degenerate (single-outcome)
    /// distribution, so its Shannon entropy should be approximately zero.
    #[test]
    fn prop_single_rule_zero_entropy(
        selectivity in 0.01_f64..100.0,
    ) {
        let mut rule_selectivities = HashMap::new();
        rule_selectivities.insert("Expr::Only".to_string(), selectivity);

        let prob = crate::probabilistic::ProbabilisticAnalysis {
            num_states: 1,
            is_normalized: true,
            total_selectivity: selectivity,
            mean_entropy: 0.0,
            low_selectivity_rules: Vec::new(),
            rule_selectivities,
        };
        let mut bundle = empty_bundle();
        bundle.probabilistic = Some(&prob);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        if let Some(&e) = analysis.per_category_entropy.get("Expr") {
            prop_assert!(
                e.abs() < 1e-9,
                "single-rule category should have entropy ~0, got {e}"
            );
        }
        // If the category is absent from the map, that's also acceptable
        // (sum <= 0 guard or other pipeline path).
    }

    // ── C3.3: Uniform distribution → max entropy = ln(n) ────────────────

    /// For n rules with equal selectivity weights, the Shannon entropy
    /// should be ln(n) (the maximum entropy for n outcomes).
    #[test]
    fn prop_uniform_max_entropy(
        n in 2_usize..=8,
        uniform_weight in 0.1_f64..10.0,
    ) {
        let mut rule_selectivities = HashMap::new();
        for i in 0..n {
            rule_selectivities.insert(format!("Expr::R{i}"), uniform_weight);
        }

        let prob = crate::probabilistic::ProbabilisticAnalysis {
            num_states: 1,
            is_normalized: true,
            total_selectivity: uniform_weight * n as f64,
            mean_entropy: (n as f64).ln(),
            low_selectivity_rules: Vec::new(),
            rule_selectivities,
        };
        let mut bundle = empty_bundle();
        bundle.probabilistic = Some(&prob);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle,
        );

        let expected = (n as f64).ln();
        let actual = analysis.per_category_entropy.get("Expr")
            .copied()
            .expect("Expr should have an entropy entry for uniform distribution");

        prop_assert!(
            (actual - expected).abs() < 1e-9,
            "uniform {n}-rule entropy should be ln({n}) = {expected}, got {actual}"
        );
    }

    // ── C3.4: Adding a rule does not decrease entropy ───────────────────

    /// Shannon entropy is monotonically non-decreasing when adding an
    /// outcome (rule) to a uniform distribution. This tests that property
    /// by comparing entropy of n uniform rules vs. n+1 uniform rules.
    #[test]
    fn prop_more_rules_higher_entropy(
        n in 2_usize..=7,
        uniform_weight in 0.1_f64..10.0,
    ) {
        // Build "smaller" distribution: n uniform rules
        let mut sels_small = HashMap::new();
        for i in 0..n {
            sels_small.insert(format!("Expr::R{i}"), uniform_weight);
        }

        let prob_small = crate::probabilistic::ProbabilisticAnalysis {
            num_states: 1,
            is_normalized: true,
            total_selectivity: uniform_weight * n as f64,
            mean_entropy: (n as f64).ln(),
            low_selectivity_rules: Vec::new(),
            rule_selectivities: sels_small,
        };
        let mut bundle_small = empty_bundle();
        bundle_small.probabilistic = Some(&prob_small);

        let categories = vec![category("Expr", true)];
        let rule_infos: Vec<RuleInfo> = vec![];
        let dead_rules = HashSet::new();
        let prediction_wfsts = HashMap::new();

        let analysis_small = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle_small,
        );

        // Build "larger" distribution: n+1 uniform rules
        let mut sels_large = HashMap::new();
        for i in 0..=n {
            sels_large.insert(format!("Expr::R{i}"), uniform_weight);
        }

        let prob_large = crate::probabilistic::ProbabilisticAnalysis {
            num_states: 1,
            is_normalized: true,
            total_selectivity: uniform_weight * (n + 1) as f64,
            mean_entropy: ((n + 1) as f64).ln(),
            low_selectivity_rules: Vec::new(),
            rule_selectivities: sels_large,
        };
        let mut bundle_large = empty_bundle();
        bundle_large.probabilistic = Some(&prob_large);

        let analysis_large = run_build_pipeline(
            &dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle_large,
        );

        let e_small = analysis_small.per_category_entropy.get("Expr")
            .copied()
            .expect("Expr should have entropy for n-rule distribution");
        let e_large = analysis_large.per_category_entropy.get("Expr")
            .copied()
            .expect("Expr should have entropy for (n+1)-rule distribution");

        prop_assert!(
            e_large >= e_small - 1e-9,
            "adding a rule should not decrease entropy: \
             {n} rules = {e_small}, {} rules = {e_large}",
            n + 1,
        );
    }
}
