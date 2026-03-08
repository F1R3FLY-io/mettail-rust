//! Forward-backward algorithm over generic semiring weights.
//!
//! Computes forward scores (total weight of all paths from start to each node)
//! and backward scores (total weight of all paths from each node to final) for
//! a DAG represented as an adjacency list.
//!
//! ## Semiring Genericity
//!
//! - With `TropicalWeight`: forward = Viterbi (min-cost path to each node).
//! - With `LogWeight`: forward = total probability to each node (log-sum-exp).
//!
//! ## Derived from lling-llang
//!
//! Source: `lling-llang/src/algorithms/forward_backward.rs`
//! License: MIT OR Apache-2.0

use crate::automata::semiring::Semiring;

/// Compute forward scores: total weight of all paths from node 0 to each node.
///
/// Requires a **topologically sorted** DAG (nodes numbered `0..num_nodes`).
/// Node 0 is the start (receives `one()`). Edges are traversed in order,
/// accumulating weights via `plus` (combine alternatives) and `times` (sequence).
///
/// # Arguments
///
/// * `edges` — Adjacency list: `edges[from]` = `[(to, weight), ...]`.
/// * `num_nodes` — Total number of nodes.
///
/// # Returns
///
/// `alpha[i]` = total weight of all paths from node 0 to node `i`.
pub fn forward_scores<W: Semiring>(edges: &[Vec<(usize, W)>], num_nodes: usize) -> Vec<W> {
    let mut alpha = vec![W::zero(); num_nodes];
    alpha[0] = W::one();

    for node in 0..num_nodes {
        if alpha[node].is_zero() {
            continue;
        }
        for &(target, ref w) in &edges[node] {
            let contribution = alpha[node].times(w);
            alpha[target] = alpha[target].plus(&contribution);
        }
    }

    alpha
}

/// Compute backward scores: total weight of all paths from each node to `final_node`.
///
/// Requires a **topologically sorted** DAG. The final node receives `one()`.
/// Edges are traversed in reverse order.
///
/// # Arguments
///
/// * `edges` — Adjacency list: `edges[from]` = `[(to, weight), ...]`.
/// * `num_nodes` — Total number of nodes.
/// * `final_node` — The target/sink node.
///
/// # Returns
///
/// `beta[i]` = total weight of all paths from node `i` to `final_node`.
pub fn backward_scores<W: Semiring>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
    final_node: usize,
) -> Vec<W> {
    let mut beta = vec![W::zero(); num_nodes];
    beta[final_node] = W::one();

    for node in (0..num_nodes).rev() {
        for &(target, ref w) in &edges[node] {
            let contribution = w.times(&beta[target]);
            beta[node] = beta[node].plus(&contribution);
        }
    }

    beta
}

/// Total path weight (partition function).
///
/// For a correctly constructed DAG: `forward[final_node] == backward[0]`.
#[inline]
pub fn total_weight<W: Semiring>(forward: &[W], final_node: usize) -> W {
    forward[final_node]
}

// =============================================================================
// Hot-path identification (Phase 5B.5)
// =============================================================================

/// A ranked edge with its contribution to total path weight.
#[derive(Debug, Clone)]
pub struct RankedEdge<W: Semiring> {
    /// Source node.
    pub from: usize,
    /// Target node.
    pub to: usize,
    /// The edge weight.
    pub weight: W,
    /// Expected count / occupancy: α(from) ⊗ w(e) ⊗ β(to).
    ///
    /// For `TropicalWeight`: cost of the best path through this edge.
    /// For `LogWeight`: total probability mass flowing through this edge.
    pub expected_weight: W,
}

/// Report identifying hot paths through the DAG.
#[derive(Debug, Clone)]
pub struct HotPathReport<W: Semiring> {
    /// Edges ranked by expected weight (hottest first for LogWeight;
    /// cheapest first for TropicalWeight).
    pub ranked_edges: Vec<RankedEdge<W>>,
    /// Total weight of the DAG (partition function).
    pub total: W,
    /// Number of nodes.
    pub num_nodes: usize,
    /// Number of edges.
    pub num_edges: usize,
}

/// Identify hot paths by computing expected weight for each edge.
///
/// For each edge `(u, v, w)`, the expected weight is `α(u) ⊗ w ⊗ β(v)`,
/// where `α` are forward scores and `β` are backward scores. This gives:
///
/// - **TropicalWeight**: cost of the best complete path through this edge.
///   Lower values are "hotter" (cheapest path uses this edge).
/// - **LogWeight**: total log-probability flowing through this edge.
///   Lower (more negative log) values carry more probability mass.
///
/// Edges are sorted so that the hottest edges come first.
pub fn hot_path_analysis<W: Semiring + PartialOrd>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
    final_node: usize,
) -> HotPathReport<W> {
    let alpha = forward_scores(edges, num_nodes);
    let beta = backward_scores(edges, num_nodes, final_node);
    let total = alpha[final_node];

    let mut ranked: Vec<RankedEdge<W>> = Vec::new();
    for (from, adj) in edges.iter().enumerate() {
        for &(to, ref w) in adj {
            let expected_weight = alpha[from].times(w).times(&beta[to]);
            ranked.push(RankedEdge {
                from,
                to,
                weight: *w,
                expected_weight,
            });
        }
    }

    // Sort by expected_weight ascending — for Tropical this puts cheapest
    // (hottest) paths first; for Log this puts highest-probability paths first
    // (most negative log = highest probability).
    ranked.sort_by(|a, b| {
        a.expected_weight
            .partial_cmp(&b.expected_weight)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let num_edges = ranked.len();
    HotPathReport {
        ranked_edges: ranked,
        total,
        num_nodes,
        num_edges,
    }
}

/// Identify the critical path (single best/cheapest path) through the DAG.
///
/// Returns the sequence of `(from, to)` edges on the best path from node 0
/// to `final_node`. For `TropicalWeight`, this is the minimum-cost path.
pub fn critical_path<W: Semiring>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
    final_node: usize,
) -> Vec<(usize, usize, W)> {
    let alpha = forward_scores(edges, num_nodes);
    let beta = backward_scores(edges, num_nodes, final_node);
    let total = alpha[final_node];

    let mut path = Vec::new();
    let mut current = 0;

    while current != final_node {
        let mut best_edge: Option<(usize, W, W)> = None;
        for &(to, ref w) in &edges[current] {
            let edge_total = alpha[current].times(w).times(&beta[to]);
            // Find the edge whose total path weight equals the DAG total.
            let is_on_best = edge_total.approx_eq(&total, 1e-10);
            if is_on_best {
                match &best_edge {
                    None => best_edge = Some((to, *w, edge_total)),
                    Some(_) => {
                        // Already found one — keep first
                    }
                }
            }
        }
        match best_edge {
            Some((to, w, _)) => {
                path.push((current, to, w));
                current = to;
            }
            None => break, // No path found (disconnected)
        }
    }

    path
}

/// Compute edge occupancy scores: fraction of total weight flowing through each edge.
///
/// Only meaningful for semirings where division is well-defined (e.g., LogWeight).
/// For TropicalWeight, this returns 1.0 for edges on the critical path and 0.0 otherwise.
pub fn edge_occupancy<W: Semiring>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
    final_node: usize,
) -> Vec<(usize, usize, f64)> {
    let alpha = forward_scores(edges, num_nodes);
    let beta = backward_scores(edges, num_nodes, final_node);
    let total = alpha[final_node];

    let mut occupancies = Vec::new();
    for (from, adj) in edges.iter().enumerate() {
        for &(to, ref w) in adj {
            let edge_total = alpha[from].times(w).times(&beta[to]);
            // Approximate occupancy: 1.0 if edge_total ≈ total, 0.0 otherwise.
            // For semirings without division, this is a binary indicator.
            let occ = if total.is_zero() {
                0.0
            } else if edge_total.approx_eq(&total, 1e-10) {
                1.0
            } else {
                // For non-tropical semirings, we can't compute exact fractions
                // without division. Report 0.0 for non-critical edges.
                0.0
            };
            occupancies.push((from, to, occ));
        }
    }

    occupancies
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;

    /// Build a simple chain: 0 →(2.0)→ 1 →(3.0)→ 2
    fn chain_edges() -> Vec<Vec<(usize, TropicalWeight)>> {
        vec![
            vec![(1, TropicalWeight::new(2.0))],
            vec![(2, TropicalWeight::new(3.0))],
            vec![], // node 2: no outgoing
        ]
    }

    #[test]
    fn test_forward_scores_chain() {
        let edges = chain_edges();
        let alpha = forward_scores(&edges, 3);

        // alpha[0] = one() = 0.0
        assert_eq!(alpha[0], TropicalWeight::one());
        // alpha[1] = 0.0 + 2.0 = 2.0 (tropical times = addition)
        assert_eq!(alpha[1], TropicalWeight::new(2.0));
        // alpha[2] = 2.0 + 3.0 = 5.0
        assert_eq!(alpha[2], TropicalWeight::new(5.0));
    }

    #[test]
    fn test_backward_scores_chain() {
        let edges = chain_edges();
        let beta = backward_scores(&edges, 3, 2);

        // beta[2] = one() = 0.0
        assert_eq!(beta[2], TropicalWeight::one());
        // beta[1] = 3.0 + 0.0 = 3.0
        assert_eq!(beta[1], TropicalWeight::new(3.0));
        // beta[0] = 2.0 + 3.0 = 5.0
        assert_eq!(beta[0], TropicalWeight::new(5.0));
    }

    /// Diamond DAG: 0 →(1.0)→ 1 →(2.0)→ 3
    ///              0 →(3.0)→ 2 →(1.0)→ 3
    fn diamond_edges() -> Vec<Vec<(usize, TropicalWeight)>> {
        vec![
            vec![(1, TropicalWeight::new(1.0)), (2, TropicalWeight::new(3.0))],
            vec![(3, TropicalWeight::new(2.0))],
            vec![(3, TropicalWeight::new(1.0))],
            vec![],
        ]
    }

    #[test]
    fn test_forward_scores_diamond() {
        let edges = diamond_edges();
        let alpha = forward_scores(&edges, 4);

        // Path 0→1→3: cost 1+2 = 3.0
        // Path 0→2→3: cost 3+1 = 4.0
        // Tropical forward[3] = min(3.0, 4.0) = 3.0
        assert_eq!(alpha[3], TropicalWeight::new(3.0));
    }

    #[test]
    fn test_forward_backward_consistency() {
        let edges = diamond_edges();
        let alpha = forward_scores(&edges, 4);
        let beta = backward_scores(&edges, 4, 3);

        // Total weight from forward and backward should agree
        let fwd_total = total_weight(&alpha, 3);
        let bwd_total = beta[0];
        assert_eq!(fwd_total, bwd_total);
    }

    #[test]
    fn test_forward_with_tropical() {
        // Tropical forward = Viterbi (min-cost path)
        // Triangle: 0 →(1.0)→ 1 →(1.0)→ 2, and 0 →(5.0)→ 2
        let edges = vec![
            vec![(1, TropicalWeight::new(1.0)), (2, TropicalWeight::new(5.0))],
            vec![(2, TropicalWeight::new(1.0))],
            vec![],
        ];
        let alpha = forward_scores(&edges, 3);
        // Path 0→1→2: 1+1 = 2.0
        // Path 0→2: 5.0
        // min(2.0, 5.0) = 2.0
        assert_eq!(alpha[2], TropicalWeight::new(2.0));
    }

    // =========================================================================
    // Hot-path analysis tests (Phase 5B.5)
    // =========================================================================

    #[test]
    fn test_hot_path_chain() {
        let edges = chain_edges();
        let report = hot_path_analysis(&edges, 3, 2);
        assert_eq!(report.num_edges, 2);
        assert_eq!(report.num_nodes, 3);
        // Total weight = 5.0 (tropical chain)
        assert_eq!(report.total, TropicalWeight::new(5.0));
        // Both edges should be on the critical path
        assert_eq!(report.ranked_edges.len(), 2);
    }

    #[test]
    fn test_hot_path_diamond_identifies_cheap_path() {
        let edges = diamond_edges();
        let report = hot_path_analysis(&edges, 4, 3);
        // 4 edges total
        assert_eq!(report.num_edges, 4);
        // The best path through 0→1→3 has total cost 3.0
        // The first ranked edge should be on the critical path (cost 3.0)
        let top = &report.ranked_edges[0];
        assert_eq!(top.expected_weight, TropicalWeight::new(3.0));
    }

    #[test]
    fn test_critical_path_chain() {
        let edges = chain_edges();
        let path = critical_path(&edges, 3, 2);
        assert_eq!(path.len(), 2);
        assert_eq!(path[0].0, 0); // from 0
        assert_eq!(path[0].1, 1); // to 1
        assert_eq!(path[1].0, 1); // from 1
        assert_eq!(path[1].1, 2); // to 2
    }

    #[test]
    fn test_critical_path_diamond() {
        let edges = diamond_edges();
        let path = critical_path(&edges, 4, 3);
        // Cheapest path: 0→1→3 (cost 3.0) vs 0→2→3 (cost 4.0)
        assert_eq!(path.len(), 2);
        assert_eq!(path[0].0, 0);
        assert_eq!(path[0].1, 1);
        assert_eq!(path[1].0, 1);
        assert_eq!(path[1].1, 3);
    }

    #[test]
    fn test_edge_occupancy_chain() {
        let edges = chain_edges();
        let occ = edge_occupancy(&edges, 3, 2);
        // Both edges on critical path: occupancy = 1.0
        assert_eq!(occ.len(), 2);
        assert_eq!(occ[0].2, 1.0);
        assert_eq!(occ[1].2, 1.0);
    }

    #[test]
    fn test_edge_occupancy_diamond() {
        let edges = diamond_edges();
        let occ = edge_occupancy(&edges, 4, 3);
        assert_eq!(occ.len(), 4);
        // Edges 0→1 and 1→3 are on the critical path (cost 3.0)
        // Edges 0→2 and 2→3 are not (cost 4.0)
        let on_path: Vec<_> = occ.iter().filter(|e| e.2 > 0.5).collect();
        assert_eq!(on_path.len(), 2);
    }

    #[test]
    fn test_hot_path_empty_dag() {
        let edges: Vec<Vec<(usize, TropicalWeight)>> = vec![vec![]];
        let report = hot_path_analysis(&edges, 1, 0);
        assert_eq!(report.num_edges, 0);
        assert!(report.ranked_edges.is_empty());
    }

    #[test]
    fn test_critical_path_single_node() {
        let edges: Vec<Vec<(usize, TropicalWeight)>> = vec![vec![]];
        let path = critical_path(&edges, 1, 0);
        assert!(path.is_empty()); // Already at final
    }

    #[cfg(feature = "wfst-log")]
    mod log_tests {
        use super::super::*;
        use crate::automata::semiring::LogWeight;

        #[test]
        fn test_forward_scores_diamond_log() {
            // Same diamond as tropical but with LogWeight
            let edges: Vec<Vec<(usize, LogWeight)>> = vec![
                vec![(1, LogWeight::new(1.0)), (2, LogWeight::new(3.0))],
                vec![(3, LogWeight::new(2.0))],
                vec![(3, LogWeight::new(1.0))],
                vec![],
            ];
            let alpha = forward_scores(&edges, 4);

            // Path 0→1→3: weight 1+2 = 3.0 (probability exp(-3))
            // Path 0→2→3: weight 3+1 = 4.0 (probability exp(-4))
            // Log total = -ln(exp(-3) + exp(-4))
            let expected = -((-3.0_f64).exp() + (-4.0_f64).exp()).ln();
            assert!(
                alpha[3].approx_eq(&LogWeight::new(expected), 1e-10),
                "expected {}, got {}",
                expected,
                alpha[3].value()
            );
        }

        #[test]
        fn test_forward_backward_consistency_log() {
            let edges: Vec<Vec<(usize, LogWeight)>> = vec![
                vec![(1, LogWeight::new(1.0)), (2, LogWeight::new(2.0))],
                vec![(3, LogWeight::new(1.0))],
                vec![(3, LogWeight::new(1.0))],
                vec![],
            ];
            let alpha = forward_scores(&edges, 4);
            let beta = backward_scores(&edges, 4, 3);

            let fwd_total = total_weight(&alpha, 3);
            // backward[0] should equal forward[final]
            assert!(
                fwd_total.approx_eq(&beta[0], 1e-10),
                "forward total {} != backward total {}",
                fwd_total.value(),
                beta[0].value()
            );
        }
    }
}
