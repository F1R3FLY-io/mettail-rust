//! The e-graph viewed as a generic-`W` weighted tree automaton (DFTA): states =
//! e-classes, transitions = e-nodes. An e-node `f(c1..cn)` in class `q` is the
//! transition `f(q(c1)..q(cn)) → q`, weighted by a caller-supplied `weigh`.
//!
//! Computes per-class **inside weights** — `inside(q) = ⊕_{node ∈ q} weigh(node)
//! ⊗ ⊗_c inside(child)` — the `⊕`-aggregate over ALL derivations of `q`. With a
//! tropical (min,+) weight the inside is the 1-best derivation cost, which is the
//! **admissible heuristic** the best-first extractor uses.
//!
//! Weight ORDERS, never PRUNES: every e-node contributes via `⊕`; a derivation
//! drops out only if its weight is the semiring zero (`0̄`).
//!
//! This module provides both the acyclic fixpoint and the closed cyclic
//! inside-weight computation. Cyclic e-class weight closure uses rigail's
//! Newton-SCC solver after deterministic SCC decomposition.

use crate::hash::HashMap;
use std::marker::PhantomData;

use rigail::{solve_scc_weights_newton, PackingFactored, Semiring, StarSemiring};

use crate::egraph::{EClassId, EGraph, ENode};
use crate::scc;

mod sealed {
    pub trait Sealed {}

    impl Sealed for rigail::TropicalWeight {}
}

/// Marker for star semirings whose multiplication is commutative.
///
/// The SCC lowering groups out-of-SCC child weights into an `outside_product`.
/// That regrouping is value-preserving only when `times` commutes. Keep this
/// bound narrow: adding a new implementation is a proof/test obligation.
pub trait CommutativeStarSemiring: StarSemiring + sealed::Sealed {
    /// Whether an edge weight is in the domain where cyclic star closure is sound.
    fn valid_closed_weight(&self) -> bool;
}

impl CommutativeStarSemiring for rigail::TropicalWeight {
    #[inline]
    fn valid_closed_weight(&self) -> bool {
        self.is_zero() || (self.0.is_finite() && self.0 >= 0.0)
    }
}

/// A weighted-tree-automaton view of an e-graph, weighted by `weigh`.
pub struct EGraphDfta<'g, L, W, F> {
    egraph: &'g EGraph<L>,
    weigh: F,
    _w: PhantomData<W>,
}

impl<'g, L, W, F> EGraphDfta<'g, L, W, F>
where
    L: Clone + Eq + std::hash::Hash,
    W: Semiring,
    F: Fn(&ENode<L>) -> W,
{
    /// View `egraph` as a WTA weighted by `weigh`.
    pub fn new(egraph: &'g EGraph<L>, weigh: F) -> Self {
        EGraphDfta { egraph, weigh, _w: PhantomData }
    }

    /// The transitions into class `q` (its e-nodes).
    pub fn transitions_of(&self, q: EClassId) -> &[ENode<L>] {
        self.egraph.nodes(q)
    }

    /// The weight of a single transition (e-node).
    pub fn weight_of(&self, node: &ENode<L>) -> W {
        (self.weigh)(node)
    }

    /// Per-class inside weight, EXACT for acyclic e-graphs (a fixpoint that is
    /// only a partial estimate on cycles — use [`EGraphDfta::inside_weights_closed`]
    /// for exact cyclic results via Newton-SCC). Every derivation contributes via
    /// `⊕`; nothing is pruned.
    pub fn inside_weights(&self) -> HashMap<EClassId, W> {
        compute_inside_acyclic(self.egraph, &self.weigh)
    }
}

impl<'g, L, W, F> EGraphDfta<'g, L, W, F>
where
    L: Clone + Eq + std::hash::Hash,
    W: CommutativeStarSemiring,
    F: Fn(&ENode<L>) -> W,
{
    /// Per-class inside weight, EXACT INCLUDING cycles: trivial (acyclic) SCCs
    /// use the fixpoint; non-trivial (cyclic) SCCs are closed by rigail's
    /// Newton-SCC solver. This is the exact `⊕`-aggregate over all derivations,
    /// the admissible 1-best for the best-first extractor.
    pub fn inside_weights_closed(&self) -> HashMap<EClassId, W> {
        compute_inside_closed(self.egraph, &self.weigh)
    }
}

/// The acyclic inside-weight fixpoint (exact for acyclic e-graphs; a partial
/// estimate on cycles). A free function so [`EGraphDfta::inside_weights`], the
/// cyclic closure, and the extractor's heuristic share one implementation.
pub fn compute_inside_acyclic<L, W, F>(egraph: &EGraph<L>, weigh: &F) -> HashMap<EClassId, W>
where
    L: Clone + Eq + std::hash::Hash,
    W: Semiring,
    F: Fn(&ENode<L>) -> W,
{
    let classes: Vec<EClassId> = egraph.classes().collect();
    let mut inside: HashMap<EClassId, W> = classes.iter().map(|&q| (q, W::zero())).collect();
    // Acyclic: each class's inside stabilizes once its descendants have, so
    // `classes.len()` passes suffice. The cap also bounds cyclic inputs.
    let max_iters = classes.len().saturating_add(1);
    for _ in 0..max_iters {
        let mut changed = false;
        for &q in &classes {
            let mut acc = W::zero();
            for node in egraph.nodes(q) {
                let mut prod = weigh(node);
                for &child in &node.children {
                    let cw = inside
                        .get(&egraph.find(child))
                        .copied()
                        .unwrap_or_else(W::zero);
                    prod = prod.times(&cw);
                }
                acc = acc.plus(&prod);
            }
            if acc != inside[&q] {
                inside.insert(q, acc);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    inside
}

/// Per-class inside weight EXACT including cycles. Trivial SCCs keep the acyclic
/// fixpoint value; each non-trivial SCC is closed by `solve_scc_weights_newton`,
/// whose result is the COMPLETE closed inside weight and REPLACES the seed.
///
/// **NOTE (no double-star):** unlike prattail's SPPF realize — which multiplies
/// its acyclic-unrolled memo by `star_ref()` of the Newton aggregate — dovetail's
/// `inside` is a from-scratch fixpoint, so Newton's value is written DIRECTLY.
/// Multiplying by star here would double-close (a bug, caught by the 2-node SCC
/// test).
///
/// FV (PROVEN, zero-admission —
/// `dovetail/formal/rocq/theories/InsideWeights/InsideWeightSccClosure.v`):
/// the SCC→`PackingFactored` lowering is a syntactic re-indexing of the e-graph
/// inside recurrence (in-SCC unknowns by SCC-local index; out-of-SCC terms as
/// solved constants) — `lowering_factor_faithful` + `lowered_eq_recurrence` +
/// `lowering_preserves_fixpoints` prove that equality and that it preserves
/// fixpoints; `star_closure_is_lfp` proves the scalar/self-loop closure is the
/// exact LEAST fixpoint (= the ⊕-aggregate over all cycle-unfolded derivations,
/// missing none); `trivial_scc_constant` proves the trivial-SCC `continue` above
/// is sound. Given that lowering equality, Esparza–Kiefer–Luttenberger Newton
/// correctness (rigail) yields the exact least-fixpoint aggregate for the n-D
/// multi-call case. Commutativity of `⊗` is the precondition for the out-of-SCC
/// factoring and is enforced by [`CommutativeStarSemiring`].
pub fn compute_inside_closed<L, W, F>(egraph: &EGraph<L>, weigh: &F) -> HashMap<EClassId, W>
where
    L: Clone + Eq + std::hash::Hash,
    W: CommutativeStarSemiring,
    F: Fn(&ENode<L>) -> W,
{
    let mut inside = compute_inside_acyclic(egraph, weigh);
    for scc_classes in scc::tarjan_sccs(egraph) {
        if scc_classes.len() == 1 && !scc::has_self_loop(egraph, scc_classes[0]) {
            continue; // trivial SCC: the acyclic value is already exact
        }
        let solved = solve_scc(egraph, weigh, &scc_classes, &inside);
        for (i, &q) in scc_classes.iter().enumerate() {
            inside.insert(q, solved[i]);
        }
    }
    inside
}

/// Build the `PackingFactored` system for one SCC and solve it via Newton-SCC.
fn solve_scc<L, W, F>(
    egraph: &EGraph<L>,
    weigh: &F,
    scc_classes: &[EClassId],
    inside: &HashMap<EClassId, W>,
) -> Vec<W>
where
    L: Clone + Eq + std::hash::Hash,
    W: CommutativeStarSemiring,
    F: Fn(&ENode<L>) -> W,
{
    let idx: HashMap<EClassId, usize> = scc_classes
        .iter()
        .enumerate()
        .map(|(i, &q)| (q, i))
        .collect();
    let mut packings: Vec<PackingFactored<W>> = Vec::new();
    for (i, &q) in scc_classes.iter().enumerate() {
        for node in egraph.nodes(q) {
            // outside_product = weigh(node) ⊗ Π inside[out-of-SCC child].
            let mut outside_product = weigh(node);
            let mut in_scc_children = Vec::new();
            for &child in &node.children {
                let cc = egraph.find(child);
                if let Some(&j) = idx.get(&cc) {
                    in_scc_children.push(j); // in-SCC child (source order matters)
                } else {
                    let w_c = inside.get(&cc).copied().unwrap_or_else(W::one);
                    outside_product = outside_product.times(&w_c);
                }
            }
            if !in_scc_children.is_empty() {
                assert!(
                    outside_product.valid_closed_weight(),
                    "cyclic inside closure requires non-negative, non-NaN recursive transition weights or semiring zero"
                );
            }
            packings.push(PackingFactored {
                target_i: i,
                outside_product,
                in_scc_children,
            });
        }
    }
    solve_scc_weights_newton(scc_classes.len(), &packings, 64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rigail::TropicalWeight;

    fn weigh_calc(n: &ENode<String>) -> TropicalWeight {
        match n.op.as_str() {
            "2" => TropicalWeight(2.0),
            "3" => TropicalWeight(3.0),
            "add" => TropicalWeight(1.0),
            "a" => TropicalWeight(5.0),
            "b" => TropicalWeight(3.0),
            "f" => TropicalWeight(1.0),
            "g" => TropicalWeight(1.0),
            "c1" => TropicalWeight(10.0),
            "c2" => TropicalWeight(20.0),
            _ => TropicalWeight(0.0),
        }
    }

    #[test]
    fn inside_weight_accumulates_along_a_tree() {
        let mut eg = EGraph::<String>::new();
        let two = eg.add(ENode::leaf("2".into()));
        let three = eg.add(ENode::leaf("3".into()));
        let add = eg.add(ENode::new("add".into(), vec![two, three]));
        let dfta = EGraphDfta::new(&eg, weigh_calc);
        let inside = dfta.inside_weights();
        assert_eq!(inside[&eg.find(two)], TropicalWeight(2.0));
        assert_eq!(inside[&eg.find(three)], TropicalWeight(3.0));
        // tropical `times` = `+`: weigh(add)=1 ⊗ inside(2)=2 ⊗ inside(3)=3 = 6.
        assert_eq!(inside[&eg.find(add)], TropicalWeight(6.0));
        assert_eq!(dfta.transitions_of(eg.find(add)).len(), 1);
    }

    #[test]
    fn alternatives_combine_by_plus_min_without_dropping_either() {
        // One class with two derivations weighing 5 and 3. Tropical `plus` = min
        // = 3 ORDERS them, but BOTH e-nodes remain in the class (no prune).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into())); // 5
        let b = eg.add(ENode::leaf("b".into())); // 3
        eg.merge(a, b);
        eg.rebuild();
        let dfta = EGraphDfta::new(&eg, weigh_calc);
        let inside = dfta.inside_weights();
        assert_eq!(inside[&eg.find(a)], TropicalWeight(3.0), "⊕ = min orders");
        assert_eq!(
            dfta.transitions_of(eg.find(a)).len(),
            2,
            "both alternatives survive in the class — weight orders, never prunes"
        );
    }

    #[test]
    fn closed_inside_exact_on_self_cycle() {
        // P = { leaf a(5), f(P) } over tropical: inside(P) = min(5, 1+inside(P)) = 5
        // (a non-negative cycle only worsens the cost). Newton closes it; the
        // result must equal 5 and the computation must terminate.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let f = eg.add(ENode::new("f".into(), vec![a]));
        eg.merge(a, f);
        eg.rebuild();
        let p = eg.find(a);
        let dfta = EGraphDfta::new(&eg, weigh_calc);
        let inside = dfta.inside_weights_closed();
        assert_eq!(inside[&p], TropicalWeight(5.0), "cyclic inside closed to 5");
    }

    #[test]
    fn closed_inside_matches_fixpoint_on_acyclic() {
        let mut eg = EGraph::<String>::new();
        let two = eg.add(ENode::leaf("2".into()));
        let three = eg.add(ENode::leaf("3".into()));
        let add = eg.add(ENode::new("add".into(), vec![two, three]));
        let dfta = EGraphDfta::new(&eg, weigh_calc);
        let acyclic = dfta.inside_weights();
        let closed = dfta.inside_weights_closed();
        assert_eq!(closed[&eg.find(add)], acyclic[&eg.find(add)], "closed == fixpoint on acyclic");
        assert_eq!(closed[&eg.find(add)], TropicalWeight(6.0));
    }

    #[test]
    fn closed_inside_two_node_scc() {
        // u = c1(10) | f(v); v = c2(20) | g(u). Tropical:
        // inside(u) = min(10, 1+inside(v)); inside(v) = min(20, 1+inside(u))
        // ⟹ inside(u) = 10, inside(v) = 11. Exercises the multi-variable
        // (non-singleton) Newton path.
        let mut eg = EGraph::<String>::new();
        let c1 = eg.add(ENode::leaf("c1".into()));
        let c2 = eg.add(ENode::leaf("c2".into()));
        let fv = eg.add(ENode::new("f".into(), vec![c2]));
        let gu = eg.add(ENode::new("g".into(), vec![c1]));
        eg.merge(c1, fv); // u = { c1, f(v) }
        eg.merge(c2, gu); // v = { c2, g(u) }
        eg.rebuild();
        let u = eg.find(c1);
        let v = eg.find(c2);
        let dfta = EGraphDfta::new(&eg, weigh_calc);
        let inside = dfta.inside_weights_closed();
        assert_eq!(inside[&u], TropicalWeight(10.0));
        assert_eq!(inside[&v], TropicalWeight(11.0));
    }

    #[test]
    fn closed_inside_allows_negative_acyclic_exit_weights() {
        fn weigh_negative_exit(n: &ENode<String>) -> TropicalWeight {
            match n.op.as_str() {
                "bad" => TropicalWeight(-1.0),
                _ => TropicalWeight(0.0),
            }
        }

        let mut eg = EGraph::<String>::new();
        let bad = eg.add(ENode::leaf("bad".into()));
        let dfta = EGraphDfta::new(&eg, weigh_negative_exit);
        let inside = dfta.inside_weights_closed();
        assert_eq!(inside[&eg.find(bad)], TropicalWeight(-1.0));
    }

    #[test]
    #[should_panic(
        expected = "cyclic inside closure requires non-negative, non-NaN recursive transition weights"
    )]
    fn closed_inside_rejects_negative_recursive_tropical_weights() {
        fn weigh_negative_recursive(n: &ENode<String>) -> TropicalWeight {
            match n.op.as_str() {
                "f" => TropicalWeight(-1.0),
                "base" => TropicalWeight(5.0),
                _ => TropicalWeight(0.0),
            }
        }

        let mut eg = EGraph::<String>::new();
        let base = eg.add(ENode::leaf("base".into()));
        let f = eg.add(ENode::new("f".into(), vec![base]));
        eg.merge(base, f);
        eg.rebuild();
        let dfta = EGraphDfta::new(&eg, weigh_negative_recursive);
        let _ = dfta.inside_weights_closed();
    }

    #[test]
    #[should_panic(
        expected = "cyclic inside closure requires non-negative, non-NaN recursive transition weights"
    )]
    fn closed_inside_rejects_nan_recursive_tropical_weights() {
        fn weigh_nan_recursive(n: &ENode<String>) -> TropicalWeight {
            match n.op.as_str() {
                "f" => TropicalWeight(f64::NAN),
                "base" => TropicalWeight(5.0),
                _ => TropicalWeight(0.0),
            }
        }

        let mut eg = EGraph::<String>::new();
        let base = eg.add(ENode::leaf("base".into()));
        let f = eg.add(ENode::new("f".into(), vec![base]));
        eg.merge(base, f);
        eg.rebuild();
        let dfta = EGraphDfta::new(&eg, weigh_nan_recursive);
        let _ = dfta.inside_weights_closed();
    }
}
