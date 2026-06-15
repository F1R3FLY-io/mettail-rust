//! AC lowering shape: the `Pattern::ac` constructor produces the `AcApp` variant,
//! and a bag node's children — once canonicalized into the sorted-by-canonical-key
//! order the lowering and AC matcher use — hashcons regardless of input order.
//!
//! (The macro-side n-ary lowering of `PPar` lives in `mettail-languages`; dovetail
//! is substrate-agnostic and cannot depend on it. These tests pin the ENGINE
//! invariants the lowering relies on: the AC pattern shape and the
//! permutation-invariant canonical bag identity.)

use dovetail::egraph::{EClassId, EGraph, ENode};
use dovetail::rules::Pattern;

fn canon_bag(eg: &EGraph<String>, children: Vec<EClassId>) -> Vec<EClassId> {
    let mut c: Vec<EClassId> = children.into_iter().map(|id| eg.find(id)).collect();
    c.sort_by_cached_key(|&a| eg.canonical_class_key(a));
    c
}

#[test]
fn pattern_ac_builds_acapp_with_fixed_and_rest() {
    let pat = Pattern::ac(
        "par".to_string(),
        vec![
            Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
            Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
        ],
        Some("rest".to_string()),
    );
    match pat {
        Pattern::AcApp { op, fixed, rest } => {
            assert_eq!(op, "par", "AC op label preserved");
            assert_eq!(fixed.len(), 2, "two fixed sub-patterns");
            assert_eq!(rest.as_deref(), Some("rest"), "rest variable bound");
            // The fixed sub-patterns are positional Apps (open/amb).
            assert!(matches!(&fixed[0], Pattern::App { op, .. } if op == "open"));
            assert!(matches!(&fixed[1], Pattern::App { op, .. } if op == "amb"));
        },
        other => panic!("expected AcApp, got {other:?}"),
    }
}

#[test]
fn pattern_ac_without_rest() {
    let pat: Pattern<String> =
        Pattern::ac("par".into(), vec![Pattern::var("P"), Pattern::var("Q")], None);
    match pat {
        Pattern::AcApp { op, fixed, rest } => {
            assert_eq!(op, "par");
            assert_eq!(fixed.len(), 2);
            assert!(rest.is_none(), "no rest");
        },
        other => panic!("expected AcApp, got {other:?}"),
    }
}

#[test]
fn canonical_bag_children_are_sorted_and_permutation_invariant() {
    // Three distinct element classes; build a "par" bag node two ways (scrambled
    // input order vs reverse), each canonicalized to sorted order. Both must
    // hashcons to the SAME class, and the stored children must be sorted by
    // canonical class key (the n-ary lowering's invariant).
    let mut eg = EGraph::<String>::new();
    let p = eg.add(ENode::leaf("p".into()));
    let q = eg.add(ENode::leaf("q".into()));
    let r = eg.add(ENode::leaf("r".into()));

    let bag1 = eg.add(ENode::new("par".into(), canon_bag(&eg, vec![r, p, q])));
    let bag2 = eg.add(ENode::new("par".into(), canon_bag(&eg, vec![q, r, p])));
    eg.rebuild();

    assert_eq!(
        eg.find(bag1),
        eg.find(bag2),
        "bags with the same multiset hashcons regardless of input order"
    );

    // The stored children of the canonical bag are sorted by canonical class key.
    let nodes = eg.nodes(eg.find(bag1));
    let bag_node = nodes
        .iter()
        .find(|n| n.op == "par")
        .expect("par bag node present");
    let keys: Vec<_> = bag_node
        .children
        .iter()
        .map(|&c| eg.canonical_class_key(c))
        .collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted, "stored bag children are in canonical (sorted) key order");
    assert_eq!(bag_node.children.len(), 3, "n-ary node retains all three elements");
}

#[test]
fn distinct_multisets_are_distinct_bag_nodes() {
    // { p, q } vs { p, p } are distinct multisets ⇒ distinct bag classes (no
    // collision); { p, q } vs { q, p } are the same multiset ⇒ one class.
    let mut eg = EGraph::<String>::new();
    let p = eg.add(ENode::leaf("p".into()));
    let q = eg.add(ENode::leaf("q".into()));

    let pq = eg.add(ENode::new("par".into(), canon_bag(&eg, vec![p, q])));
    let qp = eg.add(ENode::new("par".into(), canon_bag(&eg, vec![q, p])));
    let pp = eg.add(ENode::new("par".into(), canon_bag(&eg, vec![p, p])));
    eg.rebuild();

    assert_eq!(eg.find(pq), eg.find(qp), "{{p,q}} == {{q,p}} (same multiset)");
    assert_ne!(eg.find(pq), eg.find(pp), "{{p,q}} != {{p,p}} (distinct multisets)");
}
