//! Phase F.13 chain_10000 Plan D E6 Substage 1 (2026-05-26): GSS
//! edge-stack interning arena.
//!
//! # Background
//!
//! Per Plan C Substage 0 histograms (ledger row Exp 0.5):
//! `BranchCursor::incoming_edge_stack` length scales LINEARLY with
//! chain depth — chain_50 max=56, chain_100 max=106, chain_200
//! max=206, chain_1000 max=1006. SmallVec inline was empirically
//! REJECTED (Exp 4: spill rate ≥ 94 % at chain_1000+).
//!
//! Plan D §E6 (extending the E3 path-tree shape to other per-cursor
//! Vec fields) recommends the same interning approach that succeeded
//! for `sppf_stack` (Exp 3 ACCEPT: WIN at chain_50/100/200,
//! NEUTRAL at chain_1000). Two cursors sharing a common path
//! prefix share the entire chain via dedup.
//!
//! # This module
//!
//! Thin specialization over [`crate::path_tree_arena::PathTreeArena<GssEdgeId>`].
//! `GssEdgeId = u64` per `crate::gss`. Public API mirrors
//! `SppfStackArena`: `intern_push`, `intern_pop`, `top`, `len`,
//! `is_empty`, `slice_at`, `to_vec`, `clear`, `node_count`,
//! `dedup_count`.
//!
//! ID-namespace discipline: `EdgeStackArena` and `SppfStackArena`
//! both expose `StackId(u32)` from the generic arena. Call sites
//! must NOT pass an SPPF-arena `StackId` to an edge-arena method
//! (and vice versa). Rust's type system does not enforce this; a
//! future hardening pass could phantom-parameterize the IDs.

// Re-export the generic arena's StackId + STACK_ID_ROOT so callers
// can `use crate::edge_stack_arena::{EdgeStackId, EDGE_STACK_ID_ROOT, ...}`
// (the aliases below) or use `StackId` directly.
pub use crate::path_tree_arena::{StackId, STACK_ID_ROOT};

/// Clarity alias: this arena's stack IDs distinct in usage intent
/// from `SppfStackArena`'s `StackId` (same underlying type).
pub type EdgeStackId = StackId;

/// Clarity alias for the empty-stack sentinel.
pub const EDGE_STACK_ID_ROOT: EdgeStackId = STACK_ID_ROOT;

/// GSS edge-stack interning arena.
pub type EdgeStackArena = crate::path_tree_arena::PathTreeArena<crate::gss::GssEdgeId>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gss::GssEdgeId;

    #[test]
    fn root_is_empty() {
        let arena = EdgeStackArena::new();
        assert_eq!(arena.len(EDGE_STACK_ID_ROOT), 0);
        assert!(arena.is_empty(EDGE_STACK_ID_ROOT));
        assert_eq!(arena.top(EDGE_STACK_ID_ROOT), None);
        assert_eq!(arena.intern_pop(EDGE_STACK_ID_ROOT), EDGE_STACK_ID_ROOT);
    }

    #[test]
    fn single_push_makes_len_1() {
        let mut arena = EdgeStackArena::new();
        let s1 = arena.intern_push(EDGE_STACK_ID_ROOT, 42u64);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.top(s1), Some(42u64));
        assert!(!arena.is_empty(s1));
    }

    #[test]
    fn handles_u64_max_edge_id() {
        let mut arena = EdgeStackArena::new();
        let s1 = arena.intern_push(EDGE_STACK_ID_ROOT, u64::MAX);
        assert_eq!(arena.top(s1), Some(u64::MAX));
    }

    #[test]
    fn dedup_shares_stackid() {
        let mut arena = EdgeStackArena::new();
        let a = arena.intern_push(EDGE_STACK_ID_ROOT, 1u64);
        let b = arena.intern_push(EDGE_STACK_ID_ROOT, 1u64);
        assert_eq!(a, b);
        assert_eq!(arena.node_count(), 1);
    }

    #[test]
    fn slice_at_returns_chain_in_push_order() {
        let mut arena = EdgeStackArena::new();
        let s1 = arena.intern_push(EDGE_STACK_ID_ROOT, 10u64);
        let s2 = arena.intern_push(s1, 20u64);
        let s3 = arena.intern_push(s2, 30u64);
        let mut scratch = Vec::new();
        let slice = arena.slice_at(s3, &mut scratch);
        assert_eq!(slice, &[10u64, 20, 30]);
    }

    #[test]
    fn property_push_appends_one_element() {
        let mut arena = EdgeStackArena::new();
        let mut cur = EDGE_STACK_ID_ROOT;
        let mut expected: Vec<GssEdgeId> = Vec::new();
        for eid in [u64::MAX, 0, 1, u32::MAX as u64, 1u64 << 40]
            .iter()
            .copied()
        {
            cur = arena.intern_push(cur, eid);
            expected.push(eid);
            let mut scratch = Vec::new();
            assert_eq!(arena.slice_at(cur, &mut scratch), expected.as_slice());
            assert_eq!(arena.len(cur), expected.len());
            assert_eq!(arena.top(cur), Some(eid));
        }
    }

    /// Property: clear() resets per-parse state. EdgeStackArena is
    /// owned by WpdaWalker and cleared from reset() to release the
    /// prior parse's chain nodes.
    #[test]
    fn clear_empties_arena() {
        let mut arena = EdgeStackArena::new();
        let _ = arena.intern_push(EDGE_STACK_ID_ROOT, 1u64);
        let _ = arena.intern_push(EDGE_STACK_ID_ROOT, 2u64);
        arena.clear();
        assert_eq!(arena.node_count(), 0);
        assert_eq!(arena.dedup_count(), 0);
    }
}
