//! Bisimulation by partition refinement over a behavioral LTS — the compile-time
//! layer of the Heyting-SFA bisimulation (plan Pillar 2′ / heyting-algebra-
//! extensions.md §10.7).
//!
//! The proven Comm-reduction relation (`CommReductionCorrespondence.v`) is a
//! labeled transition system: states are processes, actions are the
//! **regularized (¬¬) minterm classes** of a `ProcessActionAlgebra` (the action
//! alphabet, decided exactly on the regular Boolean core `H_reg` of
//! [`crate::algebra_tower`]'s Heyting algebra). Two states are *bisimilar* when
//! each can match the other's labeled transitions and the targets stay related.
//!
//! This module computes the **coarsest bisimulation refining an initial coloring**
//! by signature refinement (Kanellakis–Smolka / Paige–Tarjan): repeatedly split
//! a block whenever two of its states reach *different* sets of blocks under some
//! action, until the partition is stable. The result is:
//!   - **sound** — [`Lts::is_bisimulation`] verifies the returned partition is a
//!     bisimulation (matching transitions both ways, same initial color);
//!   - **coarsest** — refinement only ever splits, so the fixpoint merges every
//!     pair of behaviorally indistinguishable states.
//!
//! This is the exact (clopen / regular) compile-time layer. Boundary gaps on the
//! semi-decidable behavioral leg (the `¬¬φ ∖ φ` region, where an action class is
//! `Sat3::DontKnow`) are closed at runtime by the Ascent `eqrel` congruence
//! fixpoint — the three-layer algorithm of §10.7. This module owns the first,
//! sound-at-compile-time layer; it never *merges* across a DontKnow boundary (it
//! only splits on confirmed action classes), so its partition is always a sound
//! under-approximation of full bisimilarity, refined (never coarsened) by the
//! runtime congruence closure.

use std::collections::BTreeMap;

/// An action label — a regularized minterm class of the process-action algebra.
pub type Action = u32;

/// A finite labeled transition system over states `0..num_states`.
#[derive(Clone, Debug, Default)]
pub struct Lts {
    /// Number of states (states are `0..num_states`).
    pub num_states: usize,
    /// Labeled transitions `(from, action, to)`.
    pub transitions: Vec<(usize, Action, usize)>,
}

impl Lts {
    /// Build an LTS over `num_states` with the given labeled transitions.
    pub fn new(num_states: usize, transitions: Vec<(usize, Action, usize)>) -> Self {
        Self { num_states, transitions }
    }

    /// Per-state outgoing adjacency `(action, target)`.
    fn adjacency(&self) -> Vec<Vec<(Action, usize)>> {
        let mut adj = vec![Vec::new(); self.num_states];
        for &(from, a, to) in &self.transitions {
            if from < self.num_states && to < self.num_states {
                adj[from].push((a, to));
            }
        }
        adj
    }

    /// One refinement step: a new block id per state, grouping states by their
    /// current block plus the *set* of `(action, target-block)` they reach.
    fn refine_once(block: &[usize], adj: &[Vec<(Action, usize)>]) -> Vec<usize> {
        let n = block.len();
        let mut signatures: Vec<(usize, Vec<(Action, usize)>)> = Vec::with_capacity(n);
        for s in 0..n {
            let mut sig: Vec<(Action, usize)> =
                adj[s].iter().map(|&(a, t)| (a, block[t])).collect();
            sig.sort_unstable();
            sig.dedup();
            signatures.push((block[s], sig));
        }
        let mut ids: BTreeMap<(usize, Vec<(Action, usize)>), usize> = BTreeMap::new();
        let mut next = vec![0usize; n];
        for (s, sig) in signatures.into_iter().enumerate() {
            let fresh = ids.len();
            next[s] = *ids.entry(sig).or_insert(fresh);
        }
        next
    }

    /// The number of distinct blocks in a partition.
    fn block_count(block: &[usize]) -> usize {
        let mut seen: BTreeMap<usize, ()> = BTreeMap::new();
        for &b in block {
            seen.insert(b, ());
        }
        seen.len()
    }

    /// The coarsest bisimulation refining `initial_colors` (one color per state):
    /// returns `block_of`, mapping each state to its bisimulation block id.
    ///
    /// Refinement only splits, so the block count is non-decreasing and bounded
    /// by `num_states`; the fixpoint is reached when a step adds no new block.
    pub fn bisimulation(&self, initial_colors: &[usize]) -> Vec<usize> {
        assert_eq!(
            initial_colors.len(),
            self.num_states,
            "initial coloring must assign one color per state"
        );
        let adj = self.adjacency();
        // Normalize the initial coloring to dense block ids.
        let mut block = Self::refine_once(initial_colors, &vec![Vec::new(); self.num_states]);
        // Re-seed with the colors actually folded in (refine_once above used empty
        // adjacency, so it grouped purely by color — exactly the normalized seed).
        loop {
            let refined = Self::refine_once(&block, &adj);
            if Self::block_count(&refined) == Self::block_count(&block) {
                return refined;
            }
            block = refined;
        }
    }

    /// Verify that `block_of` is a bisimulation w.r.t. `colors`: states in the
    /// same block share a color, and each matches the other's labeled
    /// transitions up to the partition (a sound checker, used to certify
    /// [`bisimulation`](Self::bisimulation)).
    pub fn is_bisimulation(&self, block_of: &[usize], colors: &[usize]) -> bool {
        let adj = self.adjacency();
        let n = self.num_states;
        // `s` can match every transition of `t` up to `block_of`.
        let matches = |s: usize, t: usize| -> bool {
            adj[t].iter().all(|&(a, t2)| {
                adj[s]
                    .iter()
                    .any(|&(a2, s2)| a2 == a && block_of[s2] == block_of[t2])
            })
        };
        for s in 0..n {
            for t in 0..n {
                if block_of[s] == block_of[t] {
                    if colors[s] != colors[t] {
                        return false;
                    }
                    if !matches(s, t) || !matches(t, s) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether two states are bisimilar under the coarsest bisimulation that
    /// refines `initial_colors`.
    pub fn bisimilar(&self, s: usize, t: usize, initial_colors: &[usize]) -> bool {
        let block = self.bisimulation(initial_colors);
        block[s] == block[t]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // actions
    const A: Action = 0;
    const B: Action = 1;
    const C: Action = 2;

    #[test]
    fn two_copies_of_a_b_are_bisimilar() {
        // r: 0 -a-> 1 -b-> 2(leaf);   q: 3 -a-> 4 -b-> 5(leaf)
        let lts = Lts::new(6, vec![(0, A, 1), (1, B, 2), (3, A, 4), (4, B, 5)]);
        let colors = vec![0; 6];
        let block = lts.bisimulation(&colors);
        // the two roots, the two a-successors, and the two leaves each merge.
        assert_eq!(block[0], block[3], "a.b roots should be bisimilar");
        assert_eq!(block[1], block[4]);
        assert_eq!(block[2], block[5]);
        assert!(lts.is_bisimulation(&block, &colors));
    }

    #[test]
    fn branching_distinguishes_choice_placement() {
        // s: 0 -a-> 1; 1 -b-> 2; 1 -c-> 3            (a.(b+c))
        // t: 4 -a-> 5; 4 -a-> 6; 5 -b-> 7; 6 -c-> 8  (a.b + a.c)
        let lts = Lts::new(
            9,
            vec![(0, A, 1), (1, B, 2), (1, C, 3), (4, A, 5), (4, A, 6), (5, B, 7), (6, C, 8)],
        );
        let colors = vec![0; 9];
        let block = lts.bisimulation(&colors);
        // a.(b+c) is NOT bisimilar to a.b + a.c (classic CCS example).
        assert_ne!(block[0], block[4], "a.(b+c) must differ from a.b+a.c");
        // but all four 0-leaves are bisimilar.
        assert_eq!(block[2], block[3]);
        assert_eq!(block[2], block[7]);
        assert_eq!(block[2], block[8]);
        assert!(lts.is_bisimulation(&block, &colors));
    }

    #[test]
    fn initial_colors_are_respected() {
        // Two leaves with DIFFERENT colors must stay separate (labeled bisim).
        let lts = Lts::new(2, vec![]);
        let colors = vec![0, 1];
        let block = lts.bisimulation(&colors);
        assert_ne!(block[0], block[1], "distinct colors must not merge");
        assert!(lts.is_bisimulation(&block, &colors));
        // Same color ⇒ merge.
        let same = vec![7, 7];
        let block2 = lts.bisimulation(&same);
        assert_eq!(block2[0], block2[1]);
        assert!(lts.is_bisimulation(&block2, &same));
    }

    #[test]
    fn self_loop_bisimilarity() {
        // 0 -a-> 0 and 1 -a-> 1 are bisimilar (both: forever-a).
        let lts = Lts::new(3, vec![(0, A, 0), (1, A, 1), (2, B, 2)]);
        let colors = vec![0; 3];
        let block = lts.bisimulation(&colors);
        assert_eq!(block[0], block[1], "two a-self-loops are bisimilar");
        assert_ne!(block[0], block[2], "a-loop vs b-loop differ");
        assert!(lts.is_bisimulation(&block, &colors));
    }
}
