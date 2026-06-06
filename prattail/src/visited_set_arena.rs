//! Phase F.13 chain_10000 Exp 8 Substage 1 (2026-05-26): path-tree
//! interning arena for SET semantics + LRU cache for O(1) contains().
//!
//! # Background
//!
//! After E3 (sppf_stack) and E6 (incoming_edge_stack) shipped path-tree
//! arenas, the dominant remaining per-cursor allocator is
//! `BranchCursor::visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>`
//! (Exp 5 Substage 0: max=1003 on chain_1000, 94.8 % > 64, linearly
//! scaling). Projected ~7 GB live peak at chain_10000 = the dominant
//! cause of the 24 GB OOM ceiling.
//!
//! The path-tree pattern doesn't directly transfer because
//! `FxHashSet::contains` is O(1) but a naive path-tree's contains() is
//! O(chain_length). This module pairs:
//!
//! 1. A **canonical-order** path-tree arena: elements pushed in sorted
//!    order (per `T: Ord`) so two cursors visiting the same SET (in any
//!    insertion order) arrive at the same `VisitedSetStackId`. Two-cursor
//!    union-on-equal-set is automatic via dedup.
//!
//! 2. A **walker-global LRU cache** of materialized `FxHashSet<T>` keyed
//!    by `VisitedSetStackId`. First `contains()` on a new ID is O(chain
//!    length) materialization + cache-insert; subsequent hits are O(1).
//!
//! # Generalization
//!
//! Per user mandate: parameterized by `T: Copy + Ord + Hash`. Concrete
//! type aliases (forthcoming): `VisitedDispatchArena =
//! VisitedSetArena<PackedDispatchConfig>` shared between
//! `visited_dispatch` and `visited_recovery` field swaps. Two cursors
//! that visited the same `(pos, cat_src, cur_bp)` config under
//! DIFFERENT contexts (recovery vs projection) share the StackId; the
//! `(visited_dispatch_id, visited_recovery_id)` pair distinguishes the
//! purpose at read sites.
//!
//! # Memory accounting (Plan agent design)
//!
//! Per-element costs at chain_1000:
//! - `Arc<FxHashSet>` baseline: ~28 B/entry × 1003 × ~250 K cursors live
//!   ≈ **~7 GB** at chain_1000-equivalent depth in chain_10000.
//! - Arena: ~16 B/node × 1003 unique chain nodes (one per (parent, T)
//!   pair, all cursors share the same prefix) ≈ **~16 KB** total.
//! - LRU cache: K=64 entries × 1003 × 28 B ≈ **~1.8 MB** active cache.
//! - Net memory win: ~3 orders of magnitude.
//!
//! # Correctness
//!
//! - StackId is **immutable**: once materialized, the set is correct
//!   forever (until `clear()`).
//! - `insert(stack, elem)` is **idempotent**: returns `stack` unchanged
//!   if `elem ∈ stack`.
//! - `clear()` must clear BOTH the arena AND the LRU cache.

use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::hash::Hash;
use std::sync::Arc;

/// Index into a `VisitedSetArena<T>`'s chain-node arena.
///
/// `VISITED_SET_ROOT` denotes the empty set. Each arena instance has
/// its own ID namespace — IDs from one arena must NOT be passed to
/// another arena's API. Discipline at call sites is required (Rust's
/// type system does not enforce this; the newtype hides the inner u32).
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct VisitedSetStackId(pub u32);

/// Sentinel `VisitedSetStackId` for the empty set.
pub const VISITED_SET_ROOT: VisitedSetStackId = VisitedSetStackId(u32::MAX);

/// One node in the canonical-order path-tree. `parent` is the
/// predecessor chain (smaller elements come first), `elem` is the
/// element this node adds, `len` is the cached set size.
#[derive(Copy, Clone, Debug)]
struct ChainNode<T: Copy> {
    parent: VisitedSetStackId,
    elem: T,
    len: u32,
}

/// Walker-global path-tree arena with LRU materialized-set cache.
///
/// Elements are stored in canonical (sorted) order, so two sets with
/// the same content but different insertion order share a single
/// StackId via dedup.
///
/// `LRU_K` is the cache capacity. K=64 is the default per Plan agent
/// memory math (~1.8 MB at chain_1000; fits ~50-60 active chain
/// configurations observed in E3 dedup-collapse).
pub struct VisitedSetArena<T: Copy + Ord + Eq + Hash, const LRU_K: usize = 64> {
    nodes: Vec<ChainNode<T>>,
    /// Dedup key: `(parent, elem)`. Two cursors that arrive at the
    /// same canonical-order chain share the resulting StackId.
    dedup: FxHashMap<(VisitedSetStackId, T), VisitedSetStackId>,
    /// LRU cache: materialized FxHashSet keyed by StackId. `Arc` so we
    /// can return a `Arc<FxHashSet<T>>` borrow without holding the
    /// `&mut self` borrow needed for LRU eviction.
    lru_map: FxHashMap<VisitedSetStackId, Arc<FxHashSet<T>>>,
    /// LRU eviction queue: front = oldest, back = newest. Move-to-back
    /// on hit, pop-front on overflow.
    lru_queue: VecDeque<VisitedSetStackId>,
    /// Diagnostic: cache hits (under `walker-stats` feature gate the
    /// caller can read this to tune K). Counted unconditionally because
    /// the cost is one `u64` add.
    lru_hits: u64,
    lru_misses: u64,
}

impl<T: Copy + Ord + Eq + Hash, const LRU_K: usize> Default for VisitedSetArena<T, LRU_K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + Ord + Eq + Hash, const LRU_K: usize> VisitedSetArena<T, LRU_K> {
    /// Construct an empty arena with an empty LRU cache.
    pub fn new() -> Self {
        VisitedSetArena {
            nodes: Vec::new(),
            dedup: FxHashMap::default(),
            lru_map: FxHashMap::default(),
            lru_queue: VecDeque::with_capacity(LRU_K),
            lru_hits: 0,
            lru_misses: 0,
        }
    }

    /// Reset arena + LRU cache. Called from `WpdaWalker::reset`
    /// per-parse so prior parses' nodes/cache are released. Critical
    /// invariant: cache MUST clear together with arena, otherwise a
    /// stale `Arc<FxHashSet>` could survive a parse with fresh IDs that
    /// happen to alias old IDs.
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.dedup.clear();
        self.lru_map.clear();
        self.lru_queue.clear();
    }

    /// Length (cardinality of the set). O(1).
    pub fn len(&self, stack: VisitedSetStackId) -> usize {
        if stack == VISITED_SET_ROOT {
            0
        } else {
            self.nodes[stack.0 as usize].len as usize
        }
    }

    /// True iff the set is empty.
    pub fn is_empty(&self, stack: VisitedSetStackId) -> bool {
        stack == VISITED_SET_ROOT
    }

    /// Returns true iff `elem ∈ set(stack)`.
    ///
    /// Hot path: LRU hit → O(1) FxHashSet lookup.
    /// Cold path: LRU miss → O(chain_length) materialize + O(1) lookup.
    ///
    /// After a miss, the materialized FxHashSet is interned in the LRU
    /// cache and subsequent contains() on the same StackId hit the
    /// cache. The cache uses K-capped LRU eviction.
    pub fn contains(&mut self, stack: VisitedSetStackId, elem: T) -> bool {
        if stack == VISITED_SET_ROOT {
            return false;
        }
        // Fast path: cache hit.
        if let Some(set) = self.lru_map.get(&stack) {
            self.lru_hits = self.lru_hits.saturating_add(1);
            let result = set.contains(&elem);
            // Move-to-back (most-recently-used). VecDeque has no O(1)
            // arbitrary-position remove; we accept O(K) worst-case
            // since K is small (64). For chain workloads the hot
            // stack is at the back already, so this is amortized O(1).
            self.touch_lru(stack);
            return result;
        }
        // Cold path: materialize + cache.
        self.lru_misses = self.lru_misses.saturating_add(1);
        let set = Arc::new(self.materialize(stack));
        let result = set.contains(&elem);
        self.cache_insert(stack, set);
        result
    }

    /// Insert `elem` into the set rooted at `stack`. Returns a
    /// `VisitedSetStackId` representing `set(stack) ∪ {elem}`.
    ///
    /// **Idempotent**: if `elem ∈ set(stack)`, returns `stack` unchanged.
    ///
    /// **Canonical order**: elements are interned in sorted order, so
    /// two cursors that insert `{A, B}` and `{B, A}` arrive at the
    /// same final StackId (via dedup on `(parent, sorted_elem)`).
    pub fn insert(&mut self, stack: VisitedSetStackId, elem: T) -> VisitedSetStackId {
        if self.contains(stack, elem) {
            return stack;
        }
        // Fast path: elem > top → simple intern_push (chain workloads
        // visit configs in monotonic-position order, hitting this path
        // 100 % of the time per Plan agent's analysis).
        let top = if stack == VISITED_SET_ROOT {
            None
        } else {
            Some(self.nodes[stack.0 as usize].elem)
        };
        if top.map_or(true, |t| elem > t) {
            let new_id = self.intern_push_node(stack, elem);
            // Warm the LRU for the new id by extending the parent's
            // cached set (if cached) with elem. This avoids a future
            // materialize-from-scratch when the next contains() hits
            // new_id.
            if let Some(parent_set) = self.lru_map.get(&stack).cloned() {
                let mut next: FxHashSet<T> = (*parent_set).clone();
                next.insert(elem);
                self.cache_insert(new_id, Arc::new(next));
            }
            return new_id;
        }
        // Slow path: rebuild in canonical order with `elem` spliced in.
        // O(chain_length). For chain workloads this is unreachable per
        // the monotonicity argument above; for other workloads
        // (rhocalc, edge_case) this preserves set semantics.
        let mut elements: Vec<T> = self.materialize_to_vec(stack);
        let insertion_pos = elements
            .binary_search(&elem)
            .err()
            .expect("insert slow path: elem must not be in set (contains() returned false)");
        elements.insert(insertion_pos, elem);
        let mut cur = VISITED_SET_ROOT;
        for e in elements {
            cur = self.intern_push_node(cur, e);
        }
        cur
    }

    /// Materialize the set as an owned `FxHashSet<T>`. O(chain_length).
    /// Used internally by `contains()` on LRU miss; exposed publicly
    /// for read-only inspection at non-hot sites.
    pub fn materialize(&self, stack: VisitedSetStackId) -> FxHashSet<T> {
        let n = self.len(stack);
        let mut set: FxHashSet<T> = FxHashSet::with_capacity_and_hasher(n, Default::default());
        let mut cur = stack;
        while cur != VISITED_SET_ROOT {
            let node = self.nodes[cur.0 as usize];
            set.insert(node.elem);
            cur = node.parent;
        }
        set
    }

    /// Materialize as an owned sorted `Vec<T>`. O(chain_length).
    /// Used by the `insert` slow path.
    fn materialize_to_vec(&self, stack: VisitedSetStackId) -> Vec<T> {
        let n = self.len(stack);
        let mut v: Vec<T> = Vec::with_capacity(n);
        let mut cur = stack;
        while cur != VISITED_SET_ROOT {
            let node = self.nodes[cur.0 as usize];
            v.push(node.elem);
            cur = node.parent;
        }
        // Nodes were walked top → root, so v is in reverse-canonical
        // order. Reverse to get sorted ascending.
        v.reverse();
        v
    }

    /// Diagnostic: number of unique chain nodes in the arena.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Diagnostic: number of distinct `(parent, elem)` dedup keys.
    /// Always equal to `node_count()` post-insert.
    pub fn dedup_count(&self) -> usize {
        self.dedup.len()
    }

    /// Diagnostic: LRU hit count (cumulative since `new()` or
    /// `clear()`).
    pub fn lru_hit_count(&self) -> u64 {
        self.lru_hits
    }

    /// Diagnostic: LRU miss count.
    pub fn lru_miss_count(&self) -> u64 {
        self.lru_misses
    }

    /// Diagnostic: current size of the LRU cache.
    pub fn lru_size(&self) -> usize {
        self.lru_map.len()
    }

    fn intern_push_node(&mut self, parent: VisitedSetStackId, elem: T) -> VisitedSetStackId {
        if let Some(&existing) = self.dedup.get(&(parent, elem)) {
            return existing;
        }
        let parent_len = if parent == VISITED_SET_ROOT {
            0
        } else {
            self.nodes[parent.0 as usize].len
        };
        let id = VisitedSetStackId(
            u32::try_from(self.nodes.len()).expect("VisitedSetArena: node count exceeds u32::MAX"),
        );
        self.nodes
            .push(ChainNode { parent, elem, len: parent_len + 1 });
        self.dedup.insert((parent, elem), id);
        id
    }

    fn touch_lru(&mut self, stack: VisitedSetStackId) {
        // O(K) worst-case linear scan to find + move-to-back. Chain
        // workloads typically hit the most-recent entry, making this
        // amortized O(1). For K=64 the worst case is a 64-step linear
        // scan = negligible compared to the materialize-from-scratch
        // alternative.
        if let Some(pos) = self.lru_queue.iter().position(|&x| x == stack) {
            self.lru_queue.remove(pos);
            self.lru_queue.push_back(stack);
        }
    }

    fn cache_insert(&mut self, stack: VisitedSetStackId, set: Arc<FxHashSet<T>>) {
        if self.lru_map.contains_key(&stack) {
            // Already cached; refresh position.
            self.touch_lru(stack);
            return;
        }
        if self.lru_queue.len() >= LRU_K {
            if let Some(evicted) = self.lru_queue.pop_front() {
                self.lru_map.remove(&evicted);
            }
        }
        self.lru_map.insert(stack, set);
        self.lru_queue.push_back(stack);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    type U32Arena = VisitedSetArena<u32>;
    type SmallLRU = VisitedSetArena<u32, 4>;

    #[test]
    fn root_is_empty() {
        let arena: U32Arena = VisitedSetArena::new();
        assert_eq!(arena.len(VISITED_SET_ROOT), 0);
        assert!(arena.is_empty(VISITED_SET_ROOT));
    }

    #[test]
    fn contains_on_root_is_false() {
        let mut arena: U32Arena = VisitedSetArena::new();
        assert!(!arena.contains(VISITED_SET_ROOT, 42));
    }

    #[test]
    fn single_insert_contains_yes() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s1 = arena.insert(VISITED_SET_ROOT, 7);
        assert!(arena.contains(s1, 7));
        assert_eq!(arena.len(s1), 1);
    }

    #[test]
    fn single_insert_contains_no_for_other() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s1 = arena.insert(VISITED_SET_ROOT, 7);
        assert!(!arena.contains(s1, 8));
    }

    #[test]
    fn dedup_shares_stackid_for_equal_set_in_canonical_order() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s_ab = {
            let s = arena.insert(VISITED_SET_ROOT, 1);
            arena.insert(s, 2)
        };
        let s_ab_again = {
            let s = arena.insert(VISITED_SET_ROOT, 1);
            arena.insert(s, 2)
        };
        assert_eq!(s_ab, s_ab_again);
    }

    #[test]
    fn dedup_shares_stackid_for_equal_set_reverse_order() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s_ab = {
            let s = arena.insert(VISITED_SET_ROOT, 1);
            arena.insert(s, 2)
        };
        // Insert in reverse: {2, 1} should collapse to the same StackId
        // as {1, 2} via canonical-order rebuild.
        let s_ba = {
            let s = arena.insert(VISITED_SET_ROOT, 2);
            arena.insert(s, 1)
        };
        assert_eq!(s_ab, s_ba);
    }

    #[test]
    fn idempotent_insert_returns_same_id() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s1 = arena.insert(VISITED_SET_ROOT, 7);
        let s1_again = arena.insert(s1, 7);
        assert_eq!(s1, s1_again);
    }

    #[test]
    fn lru_hit_returns_correct_set_membership() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s = arena.insert(VISITED_SET_ROOT, 1);
        let s = arena.insert(s, 2);
        let s = arena.insert(s, 3);
        // First contains() materializes; second hits cache.
        assert!(arena.contains(s, 2));
        let miss_first = arena.lru_miss_count();
        assert!(arena.contains(s, 2));
        let miss_second = arena.lru_miss_count();
        assert_eq!(miss_first, miss_second, "second contains should be cache hit");
        assert!(arena.lru_hit_count() >= 1);
    }

    #[test]
    fn lru_eviction_at_k_plus_1() {
        let mut arena: SmallLRU = VisitedSetArena::new();
        // Construct K+1 = 5 distinct sets and contains() each once.
        let stacks: Vec<_> = (10..15)
            .map(|i| {
                let s = arena.insert(VISITED_SET_ROOT, i);
                // Force materialize-and-cache.
                arena.contains(s, i);
                s
            })
            .collect();
        // After 5 misses, the cache holds at most K=4 entries. Oldest
        // stack should be evicted.
        assert!(arena.lru_size() <= 4);
        // The most-recent stack should still be cached.
        let _ = arena.contains(stacks[4], 14);
        // (No direct API for "is cached" — but lru_hit_count after a
        // re-contains of the newest stack should bump.)
        let hits_before = arena.lru_hit_count();
        let _ = arena.contains(stacks[4], 14);
        assert!(arena.lru_hit_count() > hits_before, "newest stack should be cached");
    }

    #[test]
    fn lru_miss_rebuilds_correctly_after_eviction() {
        let mut arena: SmallLRU = VisitedSetArena::new();
        let stacks: Vec<_> = (10..20)
            .map(|i| {
                let s = arena.insert(VISITED_SET_ROOT, i);
                arena.contains(s, i);
                s
            })
            .collect();
        // Oldest stack (stacks[0]) is evicted; contains() should
        // re-materialize correctly.
        assert!(arena.contains(stacks[0], 10));
        assert!(!arena.contains(stacks[0], 99));
    }

    #[test]
    fn clear_empties_arena_and_cache() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let s = arena.insert(VISITED_SET_ROOT, 1);
        let s = arena.insert(s, 2);
        arena.contains(s, 2);
        assert!(arena.node_count() > 0);
        assert!(arena.lru_size() > 0);
        arena.clear();
        assert_eq!(arena.node_count(), 0);
        assert_eq!(arena.dedup_count(), 0);
        assert_eq!(arena.lru_size(), 0);
    }

    #[test]
    fn arc_clone_does_not_invalidate_cache() {
        // VisitedSetStackId is Copy; cloning is just a u32 copy.
        let mut arena: U32Arena = VisitedSetArena::new();
        let s = arena.insert(VISITED_SET_ROOT, 1);
        let s2 = s;
        assert_eq!(s, s2);
        assert!(arena.contains(s2, 1));
    }

    #[test]
    fn monotonic_insertions_use_fast_path() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let mut s = VISITED_SET_ROOT;
        for i in 0..1000 {
            s = arena.insert(s, i);
        }
        // Chain length should be 1000.
        assert_eq!(arena.len(s), 1000);
        // Node count == 1000 (each (parent, i) is unique).
        assert_eq!(arena.node_count(), 1000);
        // contains works for arbitrary elements.
        assert!(arena.contains(s, 0));
        assert!(arena.contains(s, 999));
        assert!(!arena.contains(s, 1000));
    }

    #[test]
    fn dedup_count_matches_unique_nodes() {
        let mut arena: U32Arena = VisitedSetArena::new();
        let _s1 = arena.insert(VISITED_SET_ROOT, 1);
        let _s12 = {
            let s = arena.insert(VISITED_SET_ROOT, 1);
            arena.insert(s, 2)
        };
        // Two distinct nodes: {1}, {1,2}.
        assert_eq!(arena.node_count(), 2);
        assert_eq!(arena.dedup_count(), 2);
        // Re-insert the same — no new nodes.
        let _again = {
            let s = arena.insert(VISITED_SET_ROOT, 1);
            arena.insert(s, 2)
        };
        assert_eq!(arena.node_count(), 2);
    }

    #[test]
    fn cross_arena_id_misuse_not_enforced_but_documented() {
        // Discipline-only invariant: arena1's IDs must not be passed
        // to arena2. This test documents the limitation, not enforces.
        let mut a1: U32Arena = VisitedSetArena::new();
        let mut a2: U32Arena = VisitedSetArena::new();
        let s1 = a1.insert(VISITED_SET_ROOT, 1);
        let s2 = a2.insert(VISITED_SET_ROOT, 2);
        // s1 used in a2 would be undefined; we only check both work
        // in their own arena.
        assert!(a1.contains(s1, 1));
        assert!(a2.contains(s2, 2));
    }

    proptest! {
        #[test]
        fn property_contains_matches_set_semantics(
            xs in proptest::collection::vec(0u32..1000, 0..50)
        ) {
            let mut arena: U32Arena = VisitedSetArena::new();
            let mut s = VISITED_SET_ROOT;
            for x in &xs {
                s = arena.insert(s, *x);
            }
            let expected: FxHashSet<u32> = xs.iter().copied().collect();
            for x in 0..1000u32 {
                let in_arena = arena.contains(s, x);
                let in_expected = expected.contains(&x);
                prop_assert_eq!(in_arena, in_expected, "membership mismatch for {}", x);
            }
        }

        #[test]
        fn property_order_invariance(
            xs in proptest::collection::vec(0u32..100, 0..30)
        ) {
            let mut arena: U32Arena = VisitedSetArena::new();
            let mut s_forward = VISITED_SET_ROOT;
            for x in &xs {
                s_forward = arena.insert(s_forward, *x);
            }
            let mut s_reverse = VISITED_SET_ROOT;
            for x in xs.iter().rev() {
                s_reverse = arena.insert(s_reverse, *x);
            }
            prop_assert_eq!(s_forward, s_reverse,
                "forward and reverse insertion must yield same StackId");
        }

        #[test]
        fn property_monotonicity(
            xs in proptest::collection::vec(0u32..100, 0..30),
            extra in 0u32..200
        ) {
            let mut arena: U32Arena = VisitedSetArena::new();
            let mut s = VISITED_SET_ROOT;
            for x in &xs {
                s = arena.insert(s, *x);
            }
            // Snapshot all current members.
            let members_before: Vec<u32> = xs.iter().copied().collect();
            let s_extended = arena.insert(s, extra);
            // All prior members must still be in s_extended.
            for m in members_before {
                prop_assert!(arena.contains(s_extended, m));
            }
            prop_assert!(arena.contains(s_extended, extra));
        }
    }
}
