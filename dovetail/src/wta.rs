//! The e-graph viewed as a generic-`W` weighted tree automaton (DFTA): states =
//! e-classes, transitions = e-nodes. An e-node `f(c1..cn)` in class `q` is the
//! transition `f(q(c1)..q(cn)) → q`, weighted by a caller-supplied `weigh`.
//!
//! Computes per-class **inside weights** — `inside(q) = ⊕_{node ∈ q} weigh(node)
//! ⊗ ⊗_c inside(child)` — the `⊕`-aggregate over ALL derivations of `q`. With a
//! tropical (min,+) weight the inside is the 1-best derivation cost, which is the
//! **admissible heuristic** the best-first extractor (next increment) uses.
//!
//! Weight ORDERS, never PRUNES: every e-node contributes via `⊕`; a derivation
//! drops out only if its weight is the semiring zero (`0̄`).
//!
//! This increment handles ACYCLIC e-graphs via fixpoint iteration. Cyclic
//! e-class weight closure (via rigail's Newton-SCC solver) is a later
//! increment; the iteration cap bounds cyclic inputs to a partial estimate
//! rather than looping.

use std::collections::HashMap;
use std::marker::PhantomData;

use rigail::Semiring;

use crate::egraph::{EClassId, EGraph, ENode};

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

    /// Per-class inside weight via fixpoint iteration (exact for acyclic
    /// e-graphs). Every derivation contributes via `⊕`; nothing is pruned.
    pub fn inside_weights(&self) -> HashMap<EClassId, W> {
        let classes: Vec<EClassId> = self.egraph.classes().collect();
        let mut inside: HashMap<EClassId, W> =
            classes.iter().map(|&q| (q, W::zero())).collect();
        // Acyclic: each class's inside stabilizes once its descendants have, so
        // `classes.len()` passes suffice. The cap also bounds cyclic inputs.
        let max_iters = classes.len().saturating_add(1);
        for _ in 0..max_iters {
            let mut changed = false;
            for &q in &classes {
                let mut acc = W::zero();
                for node in self.egraph.nodes(q) {
                    let mut prod = (self.weigh)(node);
                    for &child in &node.children {
                        let cw = inside
                            .get(&self.egraph.find(child))
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
}
