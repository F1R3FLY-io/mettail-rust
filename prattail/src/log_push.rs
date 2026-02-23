//! Log-pushing: normalize WFST weights for optimal beam pruning.
//!
//! After log-pushing, outgoing edge weights at each state sum to probability 1
//! (in the log semiring). This normalization makes beam pruning optimal
//! (Mohri et al., 2002) — the beam threshold has consistent meaning across
//! all states.
//!
//! ## Algorithm
//!
//! 1. Compute backward potentials `V[q]` using `backward_scores()` with `LogWeight`.
//! 2. For each edge `(p, q, w)`: `w' = w + V[q] - V[p]`.
//! 3. Result: at each state, `Σ exp(-outgoing_weights) ≈ 1`.
//!
//! ## Derived from lling-llang
//!
//! Source: `lling-llang/src/algorithms/push.rs`
//! License: MIT OR Apache-2.0

use crate::automata::semiring::{LogWeight, Semiring};
use crate::forward_backward::backward_scores;

/// Normalize edge weights in-place using log-pushing.
///
/// After pushing, outgoing edges at each node sum to probability ~1.0.
/// This requires that all edges use `LogWeight` (not `TropicalWeight`).
///
/// # Arguments
///
/// * `edges` — Mutable adjacency list: `edges[from]` = `[(to, weight), ...]`.
/// * `num_nodes` — Total number of nodes.
/// * `final_node` — The target/sink node.
pub fn log_push_weights(
    edges: &mut [Vec<(usize, LogWeight)>],
    num_nodes: usize,
    final_node: usize,
) {
    // Step 1: compute backward potentials
    let beta = backward_scores(edges, num_nodes, final_node);

    // Step 2: push weights — adjust each edge by backward potentials
    for p in 0..num_nodes {
        if beta[p].is_zero() {
            continue; // unreachable from final — skip
        }
        for edge in edges[p].iter_mut() {
            let q = edge.0;
            if beta[q].is_zero() {
                continue; // target unreachable
            }
            // w' = w + V[q] - V[p]
            // In log semiring, "add" = times, "subtract" = add inverse
            // So: w' = w.value() + beta[q].value() - beta[p].value()
            let new_weight = edge.1.value() + beta[q].value() - beta[p].value();
            edge.1 = LogWeight::new(new_weight);
        }
    }
}

/// Check that outgoing weights at each node approximately sum to 1.0
/// (in probability space).
///
/// Returns the maximum deviation from 1.0 across all reachable nodes.
/// After log-pushing, this should be very small (< 1e-6).
pub fn check_normalization(edges: &[Vec<(usize, LogWeight)>], num_nodes: usize) -> f64 {
    let mut max_deviation = 0.0_f64;

    for (_node, edge_list) in edges.iter().enumerate().take(num_nodes) {
        if edge_list.is_empty() {
            continue; // sink node, no outgoing
        }

        // Sum probabilities of outgoing edges
        let mut total = LogWeight::zero();
        for (_, w) in edge_list {
            total = total.plus(w);
        }

        if total.is_zero() {
            continue; // no outgoing probability
        }

        // Convert to probability and check distance from 1.0
        let prob_sum = total.to_probability();
        let deviation = (prob_sum - 1.0).abs();
        max_deviation = max_deviation.max(deviation);
    }

    max_deviation
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_push_normalizes() {
        // Diamond: 0 →(1.0)→ 1 →(2.0)→ 3
        //          0 →(3.0)→ 2 →(1.0)→ 3
        let mut edges: Vec<Vec<(usize, LogWeight)>> = vec![
            vec![(1, LogWeight::new(1.0)), (2, LogWeight::new(3.0))],
            vec![(3, LogWeight::new(2.0))],
            vec![(3, LogWeight::new(1.0))],
            vec![],
        ];

        // Before pushing: node 0 outgoing sum ≠ 1
        let deviation_before = check_normalization(&edges, 4);
        assert!(deviation_before > 0.01, "should not be normalized before pushing");

        log_push_weights(&mut edges, 4, 3);

        // After pushing: all nodes should be approximately normalized
        let deviation_after = check_normalization(&edges, 4);
        assert!(
            deviation_after < 1e-6,
            "after log-pushing, deviation should be < 1e-6, got {}",
            deviation_after
        );
    }

    #[test]
    fn test_log_push_preserves_best_path() {
        // Verify that the relative ordering of paths is preserved
        // Chain: 0 →(1.0)→ 1 →(2.0)→ 2
        //        0 →(5.0)→ 2
        let mut edges: Vec<Vec<(usize, LogWeight)>> = vec![
            vec![(1, LogWeight::new(1.0)), (2, LogWeight::new(5.0))],
            vec![(2, LogWeight::new(2.0))],
            vec![],
        ];

        // Record path weights before
        // Path 0→1→2: 1.0 + 2.0 = 3.0
        // Path 0→2: 5.0
        // Best path is 0→1→2 (lower weight)

        log_push_weights(&mut edges, 3, 2);

        // After pushing, compute new path weights
        let path_012 = edges[0]
            .iter()
            .find(|e| e.0 == 1)
            .expect("edge 0→1")
            .1
            .value()
            + edges[1]
                .iter()
                .find(|e| e.0 == 2)
                .expect("edge 1→2")
                .1
                .value();
        let path_02 = edges[0]
            .iter()
            .find(|e| e.0 == 2)
            .expect("edge 0→2")
            .1
            .value();

        // Best path should still be 0→1→2
        assert!(
            path_012 < path_02,
            "best path should be preserved: 0→1→2 ({}) < 0→2 ({})",
            path_012,
            path_02
        );
    }
}
