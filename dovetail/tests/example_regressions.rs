mod support;

use std::collections::HashSet;

use dovetail::egraph::{EGraph, EGraphConfig, ENode};
use dovetail::extract::{Derivation, ExtractionCompleteness, Extractor};
use dovetail::key::ContentKey;
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use rigail::TropicalWeight;

use support::{derivation_size, semantic_weight};

fn leaf(eg: &mut EGraph<String>, op: &str) -> dovetail::egraph::EClassId {
    eg.add(ENode::leaf(op.to_string()))
}

fn app(
    eg: &mut EGraph<String>,
    op: &str,
    children: Vec<dovetail::egraph::EClassId>,
) -> dovetail::egraph::EClassId {
    eg.add(ENode::new(op.to_string(), children))
}

fn mark_derivation_keys(d: &Derivation<String, TropicalWeight>, out: &mut HashSet<ContentKey>) {
    out.insert(d.key.clone());
    for child in &d.children {
        mark_derivation_keys(child, out);
    }
}

#[test]
fn saturation_then_extraction_keeps_expanded_forms_but_prefers_normal_form() {
    let mut eg = EGraph::<String>::new();
    let a = leaf(&mut eg, "value");
    let zero = leaf(&mut eg, "zero");
    let add_a_zero = app(&mut eg, "add", vec![a, zero]);
    let root = app(&mut eg, "add", vec![add_a_zero, zero]);

    let rules = vec![
        RewriteRule {
            lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::leaf("zero".into())]),
            rhs: Pattern::var("x"),
            label: Some("right_zero".into()),
        },
        RewriteRule {
            lhs: Pattern::app("add".into(), vec![Pattern::leaf("zero".into()), Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("left_zero".into()),
        },
        RewriteRule {
            lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
            rhs: Pattern::app("add".into(), vec![Pattern::var("y"), Pattern::var("x")]),
            label: Some("comm".into()),
        },
    ];

    let report = eg.saturate(&rules, 8);
    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, a), "normal form must be merged into the root class");

    let alternatives = eg.nodes(eg.find(root)).len();
    assert!(
        alternatives >= 3,
        "saturation should retain equivalent expanded forms, got {alternatives}"
    );

    let mut extractor = Extractor::new(&eg, semantic_weight);
    let best_result = extractor.kth(root, 0);
    assert_eq!(best_result.completeness, ExtractionCompleteness::BoundedByCycleCut);
    let best = best_result.value.expect("normal form derivation");
    assert_eq!(best.op, "value");
    assert_eq!(best.weight, TropicalWeight::new(0.0));
    assert!(
        derivation_size(&best) < 3,
        "best extraction should choose the compact normal form"
    );

    assert!(
        extractor.had_cycle_cut(),
        "root~value makes retained add forms cyclic, so extraction should report the cut"
    );

    let mut funded_extractor = Extractor::new(&eg, semantic_weight);
    let funded_best = funded_extractor.funded_best(root);
    assert_eq!(funded_best.completeness, ExtractionCompleteness::Complete);
    assert_eq!(
        funded_best.value.expect("funded normal form derivation").op,
        "value",
        "funded extraction certifies the compact normal form despite retained cyclic expansions"
    );
}

#[test]
fn growth_budget_is_reported_and_extraction_still_returns_seed_derivation() {
    let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 6 });
    let a = leaf(&mut eg, "value");
    let root = app(&mut eg, "f", vec![a]);
    let grow = RewriteRule {
        lhs: Pattern::app("f".into(), vec![Pattern::var("x")]),
        rhs: Pattern::app("f".into(), vec![Pattern::app("h".into(), vec![Pattern::var("x")])]),
        label: Some("grow".into()),
    };

    let report = eg.saturate(&[grow], 100);
    assert_eq!(report.outcome, SaturationOutcome::NodeLimit);
    assert!(eg.node_limit_reached());
    assert!(eg.node_count() <= 6);

    let mut extractor = Extractor::new(&eg, semantic_weight);
    let best_result = extractor.kth(root, 0);
    let best = best_result
        .value
        .expect("seed derivation remains extractable");
    assert_eq!(best.op, "f");
}

#[test]
fn exact_marking_distinguishes_same_operator_with_different_child_choices() {
    let mut eg = EGraph::<String>::new();
    let a = leaf(&mut eg, "a");
    let b = leaf(&mut eg, "b");
    eg.merge(a, b);
    eg.rebuild();
    let q = eg.find(a);
    let root = app(&mut eg, "pair", vec![q, q]);

    let mut extractor = Extractor::new(&eg, semantic_weight);
    let extracted = extractor.derivations(root).collect_checked();
    assert_eq!(extracted.completeness, ExtractionCompleteness::Complete);
    let derivations = extracted.value;
    assert_eq!(
        derivations.len(),
        4,
        "pair({{a,b}},{{a,b}}) must enumerate the full cartesian product"
    );

    let mut marked = HashSet::new();
    for derivation in &derivations {
        mark_derivation_keys(derivation, &mut marked);
    }
    assert!(
        marked.len() >= 5,
        "exact derivation keys should keep child-choice-distinct pair derivations visible"
    );
}
