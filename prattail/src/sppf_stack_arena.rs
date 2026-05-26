//! Phase F.13 chain_10000 Plan D E3 Substage 1 (2026-05-25): SPPF-stack
//! interning arena.
//!
//! # Refactor (2026-05-26)
//!
//! This module is now a thin specialization over the generic
//! [`crate::path_tree_arena::PathTreeArena<T>`] (introduced by
//! Plan D E6 — see `path_tree_arena.rs`). The original
//! `SppfStackArena` algorithm (15/15 unit + property tests, shipped
//! at commit `8056b9a`, wired into BranchCursor at commit `f18a847`)
//! generalizes element-wise to any `Copy + Eq + Hash` type. The
//! same path-tree shape now backs both
//! `SppfStackArena = PathTreeArena<SppfId>` and
//! `EdgeStackArena = PathTreeArena<GssEdgeId>` per the user mandate:
//! "Do not overfit for any particular use cases but ensure the
//! implementations fully generalize over their respective domains."
//!
//! Public API is unchanged from the pre-refactor module — `StackId`,
//! `STACK_ID_ROOT`, and `SppfStackArena`'s methods are re-exported
//! verbatim, so all walker + cohort_lazy call sites compile
//! unchanged. The 15 prior unit + property tests are preserved below.

// Re-export the generic arena's StackId + STACK_ID_ROOT so existing
// `use crate::sppf_stack_arena::{StackId, STACK_ID_ROOT, ...}` call
// sites keep working. The arena type is a type alias —
// monomorphization yields a concrete type byte-equivalent to the
// pre-refactor implementation.
pub use crate::path_tree_arena::{StackId, STACK_ID_ROOT};

/// SPPF-stack interning arena: walker-global path-tree of pushed
/// `SppfId`s. Type alias over the generic [`crate::path_tree_arena::PathTreeArena`].
pub type SppfStackArena = crate::path_tree_arena::PathTreeArena<crate::sppf::SppfId>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sppf::SppfId;

    #[test]
    fn root_is_empty() {
        let arena = SppfStackArena::new();
        assert_eq!(arena.len(STACK_ID_ROOT), 0);
        assert!(arena.is_empty(STACK_ID_ROOT));
        assert_eq!(arena.top(STACK_ID_ROOT), None);
        assert_eq!(arena.intern_pop(STACK_ID_ROOT), STACK_ID_ROOT);
    }

    #[test]
    fn single_push_makes_len_1() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 42);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.top(s1), Some(42));
        assert!(!arena.is_empty(s1));
    }

    #[test]
    fn push_then_pop_returns_to_root() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 7);
        let s0 = arena.intern_pop(s1);
        assert_eq!(s0, STACK_ID_ROOT);
        assert_eq!(arena.len(s0), 0);
    }

    #[test]
    fn dedup_shares_stackid_for_equal_chain() {
        let mut arena = SppfStackArena::new();
        let a = arena.intern_push(STACK_ID_ROOT, 1);
        let b = arena.intern_push(STACK_ID_ROOT, 1);
        assert_eq!(a, b, "Equal (parent, sid) must dedup to same StackId");
        assert_eq!(arena.node_count(), 1);
    }

    #[test]
    fn dedup_distinguishes_different_parents() {
        let mut arena = SppfStackArena::new();
        let a = arena.intern_push(STACK_ID_ROOT, 1);
        let b = arena.intern_push(STACK_ID_ROOT, 2);
        let ax = arena.intern_push(a, 5);
        let bx = arena.intern_push(b, 5);
        assert_ne!(ax, bx, "Same sid pushed onto distinct parents must yield distinct StackId");
    }

    #[test]
    fn slice_at_returns_chain_in_push_order() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 10);
        let s2 = arena.intern_push(s1, 20);
        let s3 = arena.intern_push(s2, 30);
        let mut scratch = Vec::new();
        let slice = arena.slice_at(s3, &mut scratch);
        assert_eq!(slice, &[10, 20, 30]);
    }

    #[test]
    fn slice_at_on_root_yields_empty() {
        let arena = SppfStackArena::new();
        let mut scratch = vec![999]; // ensure scratch is cleared
        let slice = arena.slice_at(STACK_ID_ROOT, &mut scratch);
        assert!(slice.is_empty());
    }

    #[test]
    fn to_vec_matches_slice_at() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let s3 = arena.intern_push(s2, 3);
        let owned = arena.to_vec(s3);
        let mut scratch = Vec::new();
        let borrowed = arena.slice_at(s3, &mut scratch);
        assert_eq!(owned.as_slice(), borrowed);
    }

    #[test]
    fn clear_empties_arena_but_preserves_root_semantics() {
        let mut arena = SppfStackArena::new();
        let _ = arena.intern_push(STACK_ID_ROOT, 1);
        let _ = arena.intern_push(STACK_ID_ROOT, 2);
        arena.clear();
        assert_eq!(arena.node_count(), 0);
        assert_eq!(arena.dedup_count(), 0);
        assert_eq!(arena.len(STACK_ID_ROOT), 0);
        assert_eq!(arena.intern_pop(STACK_ID_ROOT), STACK_ID_ROOT);
    }

    #[test]
    fn len_is_cached_and_correct() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let s3 = arena.intern_push(s2, 3);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.len(s2), 2);
        assert_eq!(arena.len(s3), 3);
    }

    #[test]
    fn pop_then_push_same_sid_returns_original_stackid() {
        let mut arena = SppfStackArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let popped = arena.intern_pop(s2);
        assert_eq!(popped, s1);
        let re_pushed = arena.intern_push(popped, 2);
        assert_eq!(re_pushed, s2, "Re-push of same sid onto popped parent must dedup");
    }

    /// Property: `slice_at(intern_push(s, x))` equals
    /// `slice_at(s) ++ [x]`. This is the structural correctness of
    /// the interning operation — every push appends exactly one
    /// element to the chain's slice view.
    #[test]
    fn property_push_appends_one_element() {
        let mut arena = SppfStackArena::new();
        let mut cur = STACK_ID_ROOT;
        let mut expected: Vec<SppfId> = Vec::new();
        for sid in [10u32, 20, 30, 40, 50, 60, 70, 80, 90, 100].iter().copied() {
            cur = arena.intern_push(cur, sid);
            expected.push(sid);
            let mut scratch = Vec::new();
            assert_eq!(
                arena.slice_at(cur, &mut scratch),
                expected.as_slice(),
                "After push of {} the slice must equal the expected prefix",
                sid
            );
            assert_eq!(arena.len(cur), expected.len());
            assert_eq!(arena.top(cur), Some(sid));
        }
    }

    /// Property: two cursors that follow identical push sequences
    /// from `STACK_ID_ROOT` end up with the same `StackId` (dedup
    /// is structural-equal, not address-equal).
    #[test]
    fn property_equal_push_sequences_dedup() {
        let mut arena = SppfStackArena::new();
        let seq = [3u32, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        let mut a = STACK_ID_ROOT;
        let mut b = STACK_ID_ROOT;
        for sid in seq.iter().copied() {
            a = arena.intern_push(a, sid);
            b = arena.intern_push(b, sid);
            assert_eq!(a, b, "Identical push sequences must dedup at every step");
        }
        // Node count equals the sequence length (no extras from b's pushes).
        assert_eq!(arena.node_count(), seq.len());
    }

    /// Property: pushing distinct sids in distinct orders yields
    /// distinct StackIds (no false-sharing across permutations).
    #[test]
    fn property_distinct_permutations_distinguish() {
        let mut arena = SppfStackArena::new();
        let a = arena.intern_push(STACK_ID_ROOT, 1);
        let a = arena.intern_push(a, 2);
        let a = arena.intern_push(a, 3);
        let b = arena.intern_push(STACK_ID_ROOT, 3);
        let b = arena.intern_push(b, 2);
        let b = arena.intern_push(b, 1);
        assert_ne!(a, b);
        let mut sa = Vec::new();
        let mut sb = Vec::new();
        assert_eq!(arena.slice_at(a, &mut sa), &[1, 2, 3]);
        assert_eq!(arena.slice_at(b, &mut sb), &[3, 2, 1]);
    }

    /// Property: dedup map and node-vec stay in lockstep — every
    /// dedup-map entry corresponds to a node, and vice versa.
    #[test]
    fn property_dedup_map_invariant() {
        let mut arena = SppfStackArena::new();
        for sid in 0u32..50 {
            let s = arena.intern_push(STACK_ID_ROOT, sid);
            // Repeated push of same (parent, sid) must not grow the arena.
            let s2 = arena.intern_push(STACK_ID_ROOT, sid);
            assert_eq!(s, s2);
        }
        assert_eq!(arena.node_count(), 50);
        assert_eq!(arena.dedup_count(), 50);
    }
}
