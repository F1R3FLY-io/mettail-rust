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
