//! Iterative Tarjan SCC over the e-graph's class-dependency graph: class `q`
//! depends on class `c` iff some e-node of `q` has a child whose canonical class
//! is `c`. Used by the cyclic inside-weight closure (Newton-SCC) in `wta.rs`.
//!
//! Ported from prattail's proven iterative Tarjan (`sppf.rs`). **Deterministic:**
//! classes are indexed in sorted-id order so the SCC partition is reproducible
//! (HashMap key order is not stable, and the crate's determinism invariant must
//! hold). SCCs are returned in reverse-topological order (leaf SCCs first), so a
//! parent SCC's out-of-SCC children are already closed when it is solved.

use std::collections::HashMap;

use crate::egraph::{EClassId, EGraph};

/// Whether some e-node of class `q` has a child in the same class (a self-loop).
/// A singleton SCC is non-trivial (cyclic) iff this is true.
pub(crate) fn has_self_loop<L: Clone + Eq + std::hash::Hash>(eg: &EGraph<L>, q: EClassId) -> bool {
    let q = eg.find(q);
    eg.nodes(q).iter().any(|n| n.children.iter().any(|&c| eg.find(c) == q))
}

/// Strongly-connected components of the class-dependency graph, in
/// reverse-topological order (leaf SCCs first), deterministic.
pub(crate) fn tarjan_sccs<L: Clone + Eq + std::hash::Hash>(eg: &EGraph<L>) -> Vec<Vec<EClassId>> {
    let mut symbols: Vec<EClassId> = eg.classes().collect();
    symbols.sort();
    let n = symbols.len();
    if n == 0 {
        return Vec::new();
    }
    let idx_of: HashMap<EClassId, usize> =
        symbols.iter().enumerate().map(|(i, &q)| (q, i)).collect();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, &q) in symbols.iter().enumerate() {
        for node in eg.nodes(q) {
            for &child in &node.children {
                if let Some(&j) = idx_of.get(&eg.find(child)) {
                    adj[i].push(j);
                }
            }
        }
    }

    let mut index_of: Vec<Option<usize>> = vec![None; n];
    let mut lowlink: Vec<usize> = vec![0; n];
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut tarjan_stack: Vec<usize> = Vec::new();
    let mut sccs: Vec<Vec<EClassId>> = Vec::new();
    let mut idx_counter = 0usize;

    for v_start in 0..n {
        if index_of[v_start].is_some() {
            continue;
        }
        index_of[v_start] = Some(idx_counter);
        lowlink[v_start] = idx_counter;
        idx_counter += 1;
        tarjan_stack.push(v_start);
        on_stack[v_start] = true;
        let mut call_stack: Vec<(usize, usize)> = vec![(v_start, 0)];
        while let Some(&mut (node, ref mut ni)) = call_stack.last_mut() {
            if *ni < adj[node].len() {
                let w = adj[node][*ni];
                *ni += 1;
                if index_of[w].is_none() {
                    index_of[w] = Some(idx_counter);
                    lowlink[w] = idx_counter;
                    idx_counter += 1;
                    tarjan_stack.push(w);
                    on_stack[w] = true;
                    call_stack.push((w, 0));
                } else if on_stack[w] {
                    let w_index = index_of[w].expect("w should have an index");
                    if w_index < lowlink[node] {
                        lowlink[node] = w_index;
                    }
                }
            } else {
                let node_lowlink = lowlink[node];
                let node_index = index_of[node].expect("node should have an index");
                if node_lowlink == node_index {
                    let mut scc = Vec::new();
                    loop {
                        let w = tarjan_stack
                            .pop()
                            .expect("tarjan stack should not be empty mid-SCC");
                        on_stack[w] = false;
                        scc.push(symbols[w]);
                        if w == node {
                            break;
                        }
                    }
                    sccs.push(scc);
                }
                call_stack.pop();
                if let Some(&(parent, _)) = call_stack.last() {
                    if lowlink[node] < lowlink[parent] {
                        lowlink[parent] = lowlink[node];
                    }
                }
            }
        }
    }
    sccs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::ENode;

    #[test]
    fn acyclic_sccs_are_singletons() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _f = eg.add(ENode::new("f".into(), vec![a]));
        let sccs = tarjan_sccs(&eg);
        assert_eq!(sccs.len(), 2);
        assert!(sccs.iter().all(|s| s.len() == 1));
        assert!(!has_self_loop(&eg, a));
    }

    #[test]
    fn self_cycle_is_one_nontrivial_scc() {
        // P = { leaf a, f(P) } : a single self-looping SCC.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let f = eg.add(ENode::new("f".into(), vec![a]));
        eg.merge(a, f);
        eg.rebuild();
        let p = eg.find(a);
        assert!(has_self_loop(&eg, p), "f(P) makes P self-looping");
        let sccs = tarjan_sccs(&eg);
        assert!(sccs.iter().any(|s| s.contains(&p)));
    }

    #[test]
    fn tarjan_partition_is_deterministic() {
        let build = || {
            let mut eg = EGraph::<String>::new();
            let a = eg.add(ENode::leaf("a".into()));
            let f = eg.add(ENode::new("f".into(), vec![a]));
            eg.merge(a, f);
            eg.rebuild();
            eg
        };
        let s1 = tarjan_sccs(&build());
        let s2 = tarjan_sccs(&build());
        assert_eq!(s1, s2, "SCC partition reproducible (sorted indexing)");
    }
}
