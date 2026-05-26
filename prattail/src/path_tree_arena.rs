//! Phase F.13 chain_10000 Plan D E3/E6 (2026-05-26): generic
//! path-tree interning arena.
//!
//! # Background
//!
//! The chain_10000 architectural ceiling persists after the L1-L6
//! cohort lazy materialization stack + L4.2 Arc-wrapping. Per
//! heaptrack and Plan C Substage 0 histogram analysis (ledger
//! `prattail/docs/design/plans/chain-10000-experiments-ledger.md`
//! Exp 0.5):
//!
//! - `BranchCursor::sppf_stack` (`Arc<Vec<SppfId>>`) — addressed by
//!   E3 Substage 1 + 2 (commits `8056b9a` + `f18a847`, ACCEPT:
//!   chain_50 -5.02 %, chain_100 -3.95 %, chain_200 -1.22 %,
//!   chain_1000 NEUTRAL).
//!
//! - `BranchCursor::incoming_edge_stack` (`Arc<Vec<GssEdgeId>>`) —
//!   chain_1000 max=1006, p99 well above 64. SmallVec rejected
//!   empirically (Exp 4). The natural fix is the SAME path-tree
//!   interning shape as the SPPF stack (Plan D §E6).
//!
//! # This module
//!
//! `PathTreeArena<T>` is the generic implementation. Both
//! `crate::sppf_stack_arena::SppfStackArena = PathTreeArena<SppfId>`
//! and `crate::edge_stack_arena::EdgeStackArena = PathTreeArena<GssEdgeId>`
//! are type aliases. Rust monomorphizes each into a distinct concrete
//! type with byte-equivalent codegen to a hand-specialized version.
//!
//! # Design
//!
//! Path-tree mirrors `crate::gss::WpdaGss`. Each `ChainNode<T>` carries
//! `(parent: StackId, sid: T, len: u32)`. The arena interns chains via
//! `dedup: FxHashMap<(StackId, T), StackId>`: if a cursor pushes `sid`
//! onto `parent` and another cursor independently does the same, they
//! get the same `StackId` (the chain is shared structurally).
//!
//! `clear()` is the per-parse reset hook (cohort caches + walker state
//! reset together at `WpdaWalker::reset`).
//!
//! # Generalization (user mandate)
//!
//! Per user direction: "Do not overfit for any particular use cases
//! but ensure the implementations fully generalize over their
//! respective domains." This module is parameterized by `T: Copy +
//! Eq + Hash`. The 3 implemented arenas (sppf + edge + future) all
//! benefit from any algorithmic improvement landed here. No third
//! copy of the algorithm is created when the next path-stack pattern
//! appears.

use rustc_hash::FxHashMap;
use std::hash::Hash;

/// Index into a `PathTreeArena<T>`'s chain-node arena.
///
/// `STACK_ID_ROOT` denotes the empty stack (chain length 0). Each
/// `PathTreeArena<T>` instance has its own `StackId` namespace —
/// IDs from one arena must NOT be passed to another arena's API.
/// Rust's type system does not enforce this (the underlying type is
/// the same `StackId(u32)`); discipline at call sites is required.
/// Future hardening: parameterize `StackId<Kind>` with a phantom
/// type to make cross-arena IDs a compile error.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct StackId(pub u32);

/// Sentinel `StackId` for the empty stack. Matches the `gss.rs` /
/// `sppf.rs` convention of using `u32::MAX` as the "no node" sentinel.
pub const STACK_ID_ROOT: StackId = StackId(u32::MAX);

/// One node in the path-tree. `parent` is the predecessor `StackId`
/// (or `STACK_ID_ROOT` for a chain of length 1); `sid` is the element
/// this node pushed onto the chain; `len` is the cached chain length
/// (1 + parent's len).
#[derive(Copy, Clone, Debug)]
struct ChainNode<T: Copy> {
    parent: StackId,
    sid: T,
    len: u32,
}

/// Generic walker-global path-tree interning arena.
///
/// `T` is the element type (e.g., `SppfId = u32` or `GssEdgeId = u64`).
/// Two cursors that follow identical push sequences from `STACK_ID_ROOT`
/// arrive at the same `StackId` via dedup — the chain is shared
/// structurally.
pub struct PathTreeArena<T: Copy + Eq + Hash> {
    nodes: Vec<ChainNode<T>>,
    dedup: FxHashMap<(StackId, T), StackId>,
}

impl<T: Copy + Eq + Hash> Default for PathTreeArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + Eq + Hash> PathTreeArena<T> {
    /// Construct an empty arena.
    pub fn new() -> Self {
        PathTreeArena {
            nodes: Vec::new(),
            dedup: FxHashMap::default(),
        }
    }

    /// Reset the arena to empty. Called from `WpdaWalker::reset`
    /// per-parse to release the prior parse's chain nodes.
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.dedup.clear();
    }

    /// Intern `(parent, sid)` as a chain node and return its
    /// `StackId`. If `(parent, sid)` already exists, returns the
    /// existing `StackId` — this is the dedup-share point.
    ///
    /// Semantically equivalent to `vec.push(sid)` followed by
    /// returning a handle to the new stack.
    pub fn intern_push(&mut self, parent: StackId, sid: T) -> StackId {
        if let Some(&existing) = self.dedup.get(&(parent, sid)) {
            return existing;
        }
        let parent_len = self.node_len(parent);
        let id = StackId(
            u32::try_from(self.nodes.len())
                .expect("PathTreeArena: node count exceeds u32::MAX"),
        );
        self.nodes.push(ChainNode {
            parent,
            sid,
            len: parent_len + 1,
        });
        self.dedup.insert((parent, sid), id);
        id
    }

    /// Return the predecessor `StackId` (the chain with the top
    /// removed). For `STACK_ID_ROOT` returns `STACK_ID_ROOT`.
    pub fn intern_pop(&self, stack: StackId) -> StackId {
        if stack == STACK_ID_ROOT {
            STACK_ID_ROOT
        } else {
            self.nodes[stack.0 as usize].parent
        }
    }

    /// Peek the top element. Returns `None` for the empty stack.
    pub fn top(&self, stack: StackId) -> Option<T> {
        if stack == STACK_ID_ROOT {
            None
        } else {
            Some(self.nodes[stack.0 as usize].sid)
        }
    }

    /// Chain length. O(1) (cached on node).
    pub fn len(&self, stack: StackId) -> usize {
        self.node_len(stack) as usize
    }

    /// True iff stack is the root sentinel.
    pub fn is_empty(&self, stack: StackId) -> bool {
        stack == STACK_ID_ROOT
    }

    /// Materialize the chain as a contiguous slice via the caller's
    /// `scratch` buffer. The returned slice lives as long as the
    /// scratch borrow.
    ///
    /// O(chain_length). For hot read sites, prefer `top` / `len` /
    /// `intern_pop` over `slice_at` for single-element queries; a
    /// future LRU cache would amortize repeated `slice_at` calls.
    pub fn slice_at<'a>(
        &self,
        stack: StackId,
        scratch: &'a mut Vec<T>,
    ) -> &'a [T] {
        scratch.clear();
        let n = self.len(stack);
        scratch.reserve(n);
        // Walk parent chain from top → root, then reverse.
        let mut cur = stack;
        while cur != STACK_ID_ROOT {
            let node = self.nodes[cur.0 as usize];
            scratch.push(node.sid);
            cur = node.parent;
        }
        scratch.reverse();
        &scratch[..]
    }

    /// Materialize as an owned `Vec<T>` (allocation per call).
    /// Prefer `slice_at` when the slice borrow suffices.
    pub fn to_vec(&self, stack: StackId) -> Vec<T> {
        let mut v = Vec::new();
        self.slice_at(stack, &mut v);
        v
    }

    /// Diagnostic: number of chain nodes in the arena.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Diagnostic: number of distinct `(parent, sid)` keys in the
    /// dedup map. Always equal to `node_count()` post-insert.
    pub fn dedup_count(&self) -> usize {
        self.dedup.len()
    }

    fn node_len(&self, stack: StackId) -> u32 {
        if stack == STACK_ID_ROOT {
            0
        } else {
            self.nodes[stack.0 as usize].len
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U32Arena = PathTreeArena<u32>;
    type U64Arena = PathTreeArena<u64>;

    #[test]
    fn root_is_empty() {
        let arena: U32Arena = PathTreeArena::new();
        assert_eq!(arena.len(STACK_ID_ROOT), 0);
        assert!(arena.is_empty(STACK_ID_ROOT));
        assert_eq!(arena.top(STACK_ID_ROOT), None);
        assert_eq!(arena.intern_pop(STACK_ID_ROOT), STACK_ID_ROOT);
    }

    #[test]
    fn single_push_makes_len_1_u32() {
        let mut arena: U32Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 42);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.top(s1), Some(42));
    }

    #[test]
    fn single_push_makes_len_1_u64() {
        let mut arena: U64Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, u64::MAX);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.top(s1), Some(u64::MAX));
    }

    #[test]
    fn dedup_shares_stackid_for_equal_chain() {
        let mut arena: U32Arena = PathTreeArena::new();
        let a = arena.intern_push(STACK_ID_ROOT, 1);
        let b = arena.intern_push(STACK_ID_ROOT, 1);
        assert_eq!(a, b);
        assert_eq!(arena.node_count(), 1);
    }

    #[test]
    fn dedup_distinguishes_different_parents() {
        let mut arena: U32Arena = PathTreeArena::new();
        let a = arena.intern_push(STACK_ID_ROOT, 1);
        let b = arena.intern_push(STACK_ID_ROOT, 2);
        let ax = arena.intern_push(a, 5);
        let bx = arena.intern_push(b, 5);
        assert_ne!(ax, bx);
    }

    #[test]
    fn slice_at_returns_chain_in_push_order() {
        let mut arena: U32Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 10);
        let s2 = arena.intern_push(s1, 20);
        let s3 = arena.intern_push(s2, 30);
        let mut scratch = Vec::new();
        let slice = arena.slice_at(s3, &mut scratch);
        assert_eq!(slice, &[10, 20, 30]);
    }

    #[test]
    fn slice_at_on_root_yields_empty() {
        let arena: U32Arena = PathTreeArena::new();
        let mut scratch = vec![999];
        let slice = arena.slice_at(STACK_ID_ROOT, &mut scratch);
        assert!(slice.is_empty());
    }

    #[test]
    fn to_vec_matches_slice_at() {
        let mut arena: U32Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let s3 = arena.intern_push(s2, 3);
        let owned = arena.to_vec(s3);
        let mut scratch = Vec::new();
        let borrowed = arena.slice_at(s3, &mut scratch);
        assert_eq!(owned.as_slice(), borrowed);
    }

    #[test]
    fn clear_empties_arena() {
        let mut arena: U32Arena = PathTreeArena::new();
        let _ = arena.intern_push(STACK_ID_ROOT, 1);
        let _ = arena.intern_push(STACK_ID_ROOT, 2);
        arena.clear();
        assert_eq!(arena.node_count(), 0);
        assert_eq!(arena.dedup_count(), 0);
        assert_eq!(arena.len(STACK_ID_ROOT), 0);
    }

    #[test]
    fn len_is_cached_and_correct() {
        let mut arena: U32Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let s3 = arena.intern_push(s2, 3);
        assert_eq!(arena.len(s1), 1);
        assert_eq!(arena.len(s2), 2);
        assert_eq!(arena.len(s3), 3);
    }

    #[test]
    fn pop_then_push_same_sid_returns_original_stackid() {
        let mut arena: U32Arena = PathTreeArena::new();
        let s1 = arena.intern_push(STACK_ID_ROOT, 1);
        let s2 = arena.intern_push(s1, 2);
        let popped = arena.intern_pop(s2);
        assert_eq!(popped, s1);
        let re_pushed = arena.intern_push(popped, 2);
        assert_eq!(re_pushed, s2);
    }

    #[test]
    fn property_push_appends_one_element() {
        let mut arena: U32Arena = PathTreeArena::new();
        let mut cur = STACK_ID_ROOT;
        let mut expected: Vec<u32> = Vec::new();
        for sid in [10u32, 20, 30, 40, 50, 60, 70, 80, 90, 100].iter().copied() {
            cur = arena.intern_push(cur, sid);
            expected.push(sid);
            let mut scratch = Vec::new();
            assert_eq!(arena.slice_at(cur, &mut scratch), expected.as_slice());
            assert_eq!(arena.len(cur), expected.len());
            assert_eq!(arena.top(cur), Some(sid));
        }
    }

    #[test]
    fn property_equal_push_sequences_dedup() {
        let mut arena: U32Arena = PathTreeArena::new();
        let seq = [3u32, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        let mut a = STACK_ID_ROOT;
        let mut b = STACK_ID_ROOT;
        for sid in seq.iter().copied() {
            a = arena.intern_push(a, sid);
            b = arena.intern_push(b, sid);
            assert_eq!(a, b);
        }
        assert_eq!(arena.node_count(), seq.len());
    }

    #[test]
    fn property_dedup_map_invariant_u64() {
        let mut arena: U64Arena = PathTreeArena::new();
        for sid in 0u64..50 {
            let s = arena.intern_push(STACK_ID_ROOT, sid);
            let s2 = arena.intern_push(STACK_ID_ROOT, sid);
            assert_eq!(s, s2);
        }
        assert_eq!(arena.node_count(), 50);
        assert_eq!(arena.dedup_count(), 50);
    }
}
