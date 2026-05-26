//! Phase F.13 chain_10000 Plan D E3 Substage 1 (2026-05-25): SPPF-stack
//! interning arena.
//!
//! # Background
//!
//! The chain_10000 architectural ceiling persists after the L1-L6 cohort
//! lazy materialization stack + L4.2 Arc-wrapping of `recovery_deltas`
//! and `incoming_edge_stack`. Heaptrack on chain_1000 attributes 62.6 %
//! of peak heap to `BranchCursor::clone`. Plan D Explore agent
//! identified per-cursor `Arc<Vec<SppfId>> sppf_stack` (and its sibling
//! per-cursor history fields) as the residual consumer that Arc-CoW
//! does not amortize.
//!
//! When two cursors share `sppf_top` AND have just pushed the same
//! `SppfId` (Symbol-dedup at `sppf.rs:511` guarantees this), their
//! `sppf_stack` Vecs structurally coincide up to that point — yet each
//! cursor holds its OWN `Arc<Vec<SppfId>>` from a divergent Fork
//! ancestor.
//!
//! # The fix: GSS-style path-tree interning
//!
//! This file introduces `SppfStackArena`: a walker-global path-tree
//! that interns chains of pushed `SppfId`s. Each chain node has a
//! parent pointer + a pushed `SppfId`; the chain reconstructs the
//! cursor's `sppf_stack` via parent-walk. Two cursors that pushed
//! identical sequences from a common ancestor share the entire chain
//! prefix via dedup.
//!
//! The data structure mirrors `crate::gss::WpdaGss` — itself a Tomita
//! GSS (Scott & Johnstone 2010) implementing the same shape for the
//! parser's call stack. Extending the pattern to the SPPF stack is
//! the symmetric architectural move; the GSS proof of soundness
//! carries over.
//!
//! # API
//!
//! - `StackId(u32)` — index into the chain-node arena. `STACK_ID_ROOT`
//!   denotes an empty stack.
//! - `intern_push(parent, sid) -> StackId` — append `sid` to the
//!   chain rooted at `parent`. Interns via `(parent, sid) -> StackId`
//!   dedup map; equal-prefix cursors share the result.
//! - `intern_pop(parent) -> StackId` — drop the top of the chain.
//!   Returns `STACK_ID_ROOT` if `parent` was already at the root.
//! - `top(stack) -> Option<SppfId>` — peek the top `SppfId`. O(1).
//! - `len(stack) -> usize` — chain length (cached on the node).
//! - `slice_at(stack, scratch) -> &[SppfId]` — materialize the chain
//!   as a contiguous slice via a caller-provided `scratch: &mut Vec<SppfId>`.
//!   The slice lives as long as `scratch`. This is the bridge for
//!   call sites that need `&[SppfId]` semantics.
//!
//! # Substage scope
//!
//! THIS SUBSTAGE IS STANDALONE. No walker integration — no `BranchCursor`
//! field type change. The walker's `Arc<Vec<SppfId>>` representation is
//! UNCHANGED at this commit. E3 Substage 2 (separate commit) wires the
//! arena into `BranchCursor::sppf_stack_id` and migrates the ~14 walker
//! mutation sites. Unit + property tests in this file validate the
//! arena in isolation BEFORE any integration risk.
//!
//! # Why no walker integration here
//!
//! Per the chain_10000 Plan agent + the user's "don't wing complex
//! changes" mandate: validate the data structure first. If the slice
//! materialization cost (O(chain_length) per call) is unacceptable,
//! the design pivots to add an LRU cache (E3 Substage 3) BEFORE
//! integration — saving a wasted walker refactor.
//!
//! # Memory
//!
//! Each chain node is 12 bytes: `(parent: u32, sid: u32, len: u32)`.
//! Walker-global arena grows monotonically per parse; `WpdaWalker::reset`
//! clears it. At chain_10000 with peak ~225 cursors × avg chain
//! length ~50: <12 KB per cursor avg, 2.7 MB total — versus today's
//! per-cursor Arc<Vec<SppfId>> with the same average depth: 225 × 50 ×
//! 4 B + Arc overhead = 45+ KB per cursor at peak = 10 MB total. The
//! dedup factor depends on workload; for left-assoc chain we expect
//! >90 % sharing → ~1 MB total.

use rustc_hash::FxHashMap;

use crate::sppf::SppfId;

/// Index into the [`SppfStackArena`] chain-node arena.
///
/// `STACK_ID_ROOT` denotes the empty stack (chain length 0).
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct StackId(pub u32);

/// Sentinel `StackId` for the empty stack. Matches the `gss.rs` /
/// `sppf.rs` convention of using `u32::MAX` as the "no node" sentinel.
pub const STACK_ID_ROOT: StackId = StackId(u32::MAX);

/// One node in the path-tree. Mirrors `crate::gss::WpdaGssNode`:
/// `parent` is the predecessor `StackId` (or `STACK_ID_ROOT` for a
/// chain of length 1); `sid` is the `SppfId` this node pushed onto
/// the chain; `len` is the cached chain length (1 + parent's len).
#[derive(Copy, Clone, Debug)]
struct ChainNode {
    parent: StackId,
    sid: SppfId,
    len: u32,
}

/// Walker-global SPPF-stack interning arena.
///
/// `dedup` keys are `(parent: StackId, sid: SppfId)`; two cursors
/// reaching the same `(parent, sid)` push share the same `StackId`,
/// collapsing memory linearly with workload share-factor.
pub struct SppfStackArena {
    nodes: Vec<ChainNode>,
    dedup: FxHashMap<(StackId, SppfId), StackId>,
}

impl Default for SppfStackArena {
    fn default() -> Self {
        Self::new()
    }
}

impl SppfStackArena {
    /// Construct an empty arena.
    pub fn new() -> Self {
        SppfStackArena {
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
    pub fn intern_push(&mut self, parent: StackId, sid: SppfId) -> StackId {
        if let Some(&existing) = self.dedup.get(&(parent, sid)) {
            return existing;
        }
        let parent_len = self.node_len(parent);
        let id = StackId(
            u32::try_from(self.nodes.len())
                .expect("SppfStackArena: node count exceeds u32::MAX"),
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

    /// Peek the top `SppfId`. Returns `None` for the empty stack.
    pub fn top(&self, stack: StackId) -> Option<SppfId> {
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
    /// scratch borrow. Use this at sites that need `&[SppfId]`
    /// semantics during E3 Substage 2 wiring.
    ///
    /// O(chain_length). For hot read sites, E3 Substage 3 may add an
    /// LRU cache; until then, prefer `top` / `len` / `intern_pop`
    /// over `slice_at` for single-element queries.
    pub fn slice_at<'a>(
        &self,
        stack: StackId,
        scratch: &'a mut Vec<SppfId>,
    ) -> &'a [SppfId] {
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

    /// Materialize as an owned `Vec<SppfId>` (allocation per call).
    /// Used by call sites that need ownership rather than a borrow.
    /// Prefer `slice_at` when the slice borrow suffices.
    pub fn to_vec(&self, stack: StackId) -> Vec<SppfId> {
        let mut v = Vec::new();
        self.slice_at(stack, &mut v);
        v
    }

    /// Diagnostic: number of chain nodes in the arena. Used by
    /// walker-stats and E3 sizing analysis.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Diagnostic: number of distinct `(parent, sid)` keys in the
    /// dedup map. Always equal to `node_count()` post-insert; tracked
    /// separately to detect dedup-map drift bugs.
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
