//! AC (associative-commutative) ambiguity end-to-end: the `OpenRule` redex with
//! TWO valid pairings must produce BOTH as DISTINCT equal-weight alternatives.
//!
//! Governing mandate 1 (ambiguity preserved): every valid AC sub-multiset
//! matching is a distinct alternative; weight ORDERS, never PRUNES; all
//! equal-weight pairings survive extraction. Mirrors
//! `dovetail/src/extract.rs::tests::t2_ambiguous_hand_built_no_miss`.

use std::collections::HashSet;

use dovetail::egraph::{EClassId, EGraph, ENode};
use dovetail::extract::{ExtractionCompleteness, Extractor};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use rigail::TropicalWeight;

/// Sort children into the canonical bag order (by canonical class key) — the same
/// order the lowering and the AC matcher use, so a hand-built bag node hashconses
/// with the engine-built one.
fn canon_bag(eg: &EGraph<String>, children: Vec<EClassId>) -> Vec<EClassId> {
    let mut c: Vec<EClassId> = children.into_iter().map(|id| eg.find(id)).collect();
    c.sort_by_cached_key(|&a| eg.canonical_class_key(a));
    c
}

/// Flat weight: every node costs 1 (structural). With a flat cost, the two
/// distinct reductions have EQUAL weight — so the test exercises the
/// equal-weight-both-survive guarantee, not a weight tiebreak.
fn weigh_flat(_n: &ENode<String>) -> TropicalWeight {
    TropicalWeight(1.0)
}

/// The Ambient `OpenRule` as Dovetail data:
/// par { open(N,P), amb(N,Q), ...rest } ~> par { P, Q, ...rest }.
fn open_rule() -> RewriteRule<String> {
    RewriteRule {
        lhs: Pattern::ac(
            "par".into(),
            vec![
                Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
            ],
            Some("rest".into()),
        ),
        rhs: Pattern::ac(
            "par".into(),
            vec![Pattern::var("P"), Pattern::var("Q")],
            Some("rest".into()),
        ),
        label: Some("OpenRule".into()),
    }
}

#[test]
fn open_rule_two_pairings_both_survive_as_distinct_equal_weight_roots() {
    // Seed:  par { open(n, A), n[B], n[C] }.
    // OpenRule pairs open(n,·) with EITHER ambient (shared name n):
    //   pairing 1: (open n A, amb n B) leaves rest = { n[C] } ⇒ par { A, B, n[C] }
    //   pairing 2: (open n A, amb n C) leaves rest = { n[B] } ⇒ par { A, C, n[B] }
    // Both are valid, equal-weight, DISTINCT multisets — both must survive.
    let mut eg = EGraph::<String>::new();
    let n = eg.add(ENode::leaf("n".into()));
    let va = eg.add(ENode::leaf("A".into()));
    let vb = eg.add(ENode::leaf("B".into()));
    let vc = eg.add(ENode::leaf("C".into()));
    let open = eg.add(ENode::new("open".into(), vec![n, va]));
    let amb_b = eg.add(ENode::new("amb".into(), vec![n, vb]));
    let amb_c = eg.add(ENode::new("amb".into(), vec![n, vc]));

    let par_children = canon_bag(&eg, vec![open, amb_b, amb_c]);
    let par = eg.add(ENode::new("par".into(), par_children));
    eg.rebuild();

    let rep = eg.saturate(&[open_rule()], 30);
    assert_eq!(rep.outcome, SaturationOutcome::Converged, "AC saturation reaches a fixpoint");

    // Hand-build the two expected result bags (canonical). In an e-graph, all
    // EQUIVALENT terms collapse to ONE class, so the redex, res1, and res2 are
    // the SAME class (the redex reduces to each). The DISTINCTNESS that must be
    // preserved is at the E-NODE / derivation level — the shared class must
    // CONTAIN both distinct result-bag e-nodes (distinct exact ContentKeys), and
    // extraction must surface both as distinct alternatives.
    let amb_c_now = eg.find(amb_c);
    let amb_b_now = eg.find(amb_b);
    let res1_children = canon_bag(&eg, vec![va, vb, amb_c_now]); // { A, B, n[C] }
    let res2_children = canon_bag(&eg, vec![va, vc, amb_b_now]); // { A, C, n[B] }
    let res1_node = ENode::new("par".to_string(), res1_children);
    let res2_node = ENode::new("par".to_string(), res2_children);
    // The two result e-nodes are DISTINCT (distinct multisets ⇒ distinct keys).
    assert_ne!(
        res1_node.content_key(),
        res2_node.content_key(),
        "the two reductions are DISTINCT multisets (distinct exact keys)"
    );

    let res1 = eg.add(res1_node.clone());
    let res2 = eg.add(res2_node.clone());
    eg.rebuild();

    assert!(eg.equiv(par, res1), "pairing 1: par ~ {{A, B, n[C]}}");
    assert!(eg.equiv(par, res2), "pairing 2: par ~ {{A, C, n[B]}}");
    // They ARE the same class (all equivalent terms are one class) — that is
    // correct e-graph behavior; ambiguity lives in the node set, not the classes.
    assert_eq!(
        eg.find(res1),
        eg.find(res2),
        "equivalent reductions share a class (e-graph congruence)"
    );

    // The shared class must contain BOTH distinct reduced e-nodes (by exact key).
    let class_keys: HashSet<_> = eg
        .nodes(eg.find(par))
        .iter()
        .map(|n| n.content_key())
        .collect();
    assert!(
        class_keys.contains(&res1_node.content_key()),
        "redex class contains the {{A, B, n[C]}} reduction node"
    );
    assert!(
        class_keys.contains(&res2_node.content_key()),
        "redex class contains the {{A, C, n[B]}} reduction node"
    );

    // Extraction from the redex root must surface BOTH reductions as distinct
    // derivations, complete (no cycle cut on this acyclic system).
    let root = eg.find(par);
    let mut ex = Extractor::new(&eg, weigh_flat);
    let collected = ex.derivations(root).collect_checked();
    assert_eq!(
        collected.completeness,
        ExtractionCompleteness::Complete,
        "acyclic AC reduction extracts to completion"
    );
    let ds = collected.value;

    // Locate the two reduced derivations by their exact tree keys. Both must be
    // present (no-miss) and carry EQUAL weight (equal-weight-both-survive).
    let d1 = ds
        .iter()
        .find(|d| d.op == "par" && bag_child_ops(d) == sorted_ops(&["A", "B", "amb"]))
        .expect("the {A, B, n[C]} reduced derivation is present");
    let d2 = ds
        .iter()
        .find(|d| d.op == "par" && bag_child_ops(d) == sorted_ops(&["A", "C", "amb"]))
        .expect("the {A, C, n[B]} reduced derivation is present");
    assert_ne!(d1.key, d2.key, "the two reduced derivations are distinct (no merge)");
    assert_eq!(
        d1.weight, d2.weight,
        "equal-weight: both reductions survive, weight orders but does not prune"
    );

    // Best-first order is non-decreasing (sanity).
    let mut weights: Vec<f64> = ds.iter().map(|d| d.weight.0).collect();
    weights.sort_by(|a, b| a.partial_cmp(b).expect("finite weights"));
    for w in weights.windows(2) {
        assert!(w[0] <= w[1], "best-first non-decreasing weight order");
    }
}

/// The sorted multiset of immediate child operator labels of a derivation
/// (a coarse structural fingerprint of a bag derivation's elements).
fn bag_child_ops(d: &dovetail::extract::Derivation<String, TropicalWeight>) -> Vec<String> {
    let mut ops: Vec<String> = d.children.iter().map(|c| c.op.clone()).collect();
    ops.sort();
    ops
}

fn sorted_ops(ops: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = ops.iter().map(|s| s.to_string()).collect();
    v.sort();
    v
}

#[test]
fn open_rule_with_inert_extra_element_preserves_rest() {
    // par { open(n, A), n[B], q[D] }: only ONE valid pairing (the q-ambient has a
    // different name, so it cannot pair with open(n,·)); it must end up in `rest`.
    // Result: par { A, B, q[D] }. Exactly one reduction.
    let mut eg = EGraph::<String>::new();
    let n = eg.add(ENode::leaf("n".into()));
    let q = eg.add(ENode::leaf("q".into()));
    let va = eg.add(ENode::leaf("A".into()));
    let vb = eg.add(ENode::leaf("B".into()));
    let vd = eg.add(ENode::leaf("D".into()));
    let open = eg.add(ENode::new("open".into(), vec![n, va]));
    let amb_b = eg.add(ENode::new("amb".into(), vec![n, vb]));
    let amb_d = eg.add(ENode::new("amb".into(), vec![q, vd]));
    let par_children = canon_bag(&eg, vec![open, amb_b, amb_d]);
    let par = eg.add(ENode::new("par".into(), par_children));
    eg.rebuild();

    let rep = eg.saturate(&[open_rule()], 30);
    assert_eq!(rep.outcome, SaturationOutcome::Converged);

    let amb_d_now = eg.find(amb_d);
    let res_children = canon_bag(&eg, vec![va, vb, amb_d_now]); // { A, B, q[D] }
    let res = eg.add(ENode::new("par".into(), res_children));
    eg.rebuild();
    assert!(eg.equiv(par, res), "the single valid pairing reduces; q[D] stays in rest");
}
