//! Phase F.13 chain_10000 Exp 15 Substage 1 (2026-05-27): walker-global
//! persistent state map for the planned CPS rewrite.
//!
//! Per `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` §3.2,
//! the CPS rewrite moves the per-cursor "heavy" fields off
//! `BranchCursor` (~512 B) and into a walker-global `CursorStore`
//! indexed by `CursorId`. The heavy fields become walker-global
//! HAMT-backed persistent maps (`im::OrdSet` for visited sets,
//! `im::HashMap` for sparse per-cursor Vecs). The "minimal" per-cursor
//! fields (pure Copy scalars + arena handles + the per-cursor weight)
//! live in a cache-friendly `Vec<MinimalCursorState>` indexed by
//! `CursorId.0`.
//!
//! Substage 1 ships ONLY the data structure module + constructors +
//! tests — dead code, no walker integration. Substage 2 introduces the
//! mirror-write feature gate that allocates a `CursorId` at each
//! `BranchCursor` allocation and mirrors mutations into the store.
//!
//! # Why HAMT structural sharing solves what Arc-CoW could not
//!
//! Today the walker's per-cursor `Arc<FxHashSet<PackedDispatchConfig>>`
//! visited_dispatch shares the Arc on Fork (O(1) bump), but the first
//! per-cursor `insert` post-Fork triggers `Arc::make_mut` which
//! deep-clones the FxHashSet. Exp 16 r3 attribution shows this is the
//! 23.3 % chain_500 walker dominator (1.14 GB across 49.6 M entries
//! with 712× content-level dedup; the entries arise from per-cursor
//! deep clones).
//!
//! `im::OrdSet<(CursorId, PackedDispatchConfig)>` keys by a `(cursor_id,
//! config)` tuple. Two cursors that share a prefix of visited-configs
//! share the underlying HAMT chain through the trie; per-cursor "cycle
//! defense" becomes a lookup of `(my_cursor_id, candidate_config)` in
//! the global set. On Fork, the child's `cursor_id` simply does not
//! have entries — the lineage-chain `contains` check (per plan §3.5)
//! walks parent ids in O(Fork-depth × log32 N) until a hit or root.
//! First per-child insert is `set.insert((child_id, config))` =
//! O(log32 N) with structural sharing.

use std::sync::Arc;

use crate::automata::semiring::SemiringRef;
use crate::cursor_id::{CursorId, CursorIdAllocator};
#[cfg(test)]
use crate::cursor_id::CURSOR_ID_NONE;
use crate::dispatch_cohort::DispatchKey;
use crate::edge_stack_arena::{EdgeStackId, EDGE_STACK_ID_ROOT};
use crate::gss::{GssNodeId, GSS_NODE_NONE};
use crate::sppf::SppfId;
use crate::sppf_stack_arena::{StackId, STACK_ID_ROOT};
use crate::wpda_runtime::WpdaState;
use crate::wpda_walker::{BuilderDelta, LexForkStamp, PackedDispatchConfig};

/// Minimal per-cursor fields: pure Copy + Arc handles. Stored in
/// `Vec<MinimalCursorState>` indexed by `CursorId.0`.
///
/// Size target per plan §3.3: ≤ 96 B (vs today's 512 B `BranchCursor`
/// — 5.3× per-cursor reduction). All "heavy" fields (the 6 listed in
/// `HeavyCursorFields` below) live on `CursorStore` walker-globally.
#[derive(Clone, Debug)]
pub struct MinimalCursorState<W: SemiringRef> {
    pub node: GssNodeId,
    pub pos: usize,
    pub weight: W,
    pub inner_state: WpdaState,
    pub source_priority: u32,
    pub incoming_edge_stack_id: EdgeStackId,
    pub recovery_depth: u8,
    pub sppf_stack_id: StackId,
    pub pending_packing_weight: W,
    pub collection_stack_depth: u8,
    pub last_action_output_cat: Option<u16>,
    pub cohort_origin: Option<DispatchKey>,
    pub cohort_revive_depth: u32,
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
}

impl<W: SemiringRef> MinimalCursorState<W> {
    /// Construct a seed minimal cursor state at the walker root.
    pub fn seed(initial_weight: W, initial_state: WpdaState) -> Self {
        Self {
            node: GSS_NODE_NONE,
            pos: 0,
            weight: initial_weight.clone(),
            inner_state: initial_state,
            source_priority: 0,
            incoming_edge_stack_id: EDGE_STACK_ID_ROOT,
            recovery_depth: 0,
            sppf_stack_id: STACK_ID_ROOT,
            pending_packing_weight: initial_weight,
            collection_stack_depth: 0,
            last_action_output_cat: None,
            cohort_origin: None,
            cohort_revive_depth: 0,
            sppf_collection_arena: Arc::new(Vec::new()),
        }
    }
}

/// Walker-global cursor store. All mutation goes through the typed
/// helpers (`visited_dispatch_insert`, `recovery_deltas_push`, etc.)
/// so the dual-write / lineage-chain logic is centralized.
///
/// # Lineage chain (per plan §3.5)
///
/// Each child `CursorId` allocated via `alloc_child(parent_id)` records
/// `parent_of_inheritance[child] = parent` so cycle defense looks up
/// `(child, config)` in the OrdSet AND recursively walks the chain to
/// the root. First per-child insert writes a single `(child, config)`
/// tuple; the chain walk handles the rest. Periodic chain flattening
/// (at merge boundaries) bounds the walk depth.
pub struct CursorStore<W: SemiringRef> {
    /// CursorId allocator (recycle pool).
    pub allocator: CursorIdAllocator,
    /// Per-cursor minimal state. Sparse Vec; entries at retired-id
    /// indices are stale but harmless (next alloc reissues the id and
    /// the caller overwrites via `set_minimal`).
    pub minimal: Vec<Option<MinimalCursorState<W>>>,

    // ── Heavy fields, walker-global, HAMT-backed ─────────────────────
    /// visited_dispatch: keyed by `(CursorId, PackedDispatchConfig)`.
    /// Per plan §3.5, the lineage chain handles parent-inheritance —
    /// this OrdSet stores ONLY entries directly inserted under each
    /// cursor_id; `contains` walks `parent_of_inheritance` to consult
    /// ancestor entries.
    pub visited_dispatch: im::OrdSet<(CursorId, PackedDispatchConfig)>,
    /// visited_recovery — same shape, distinct namespace.
    pub visited_recovery: im::OrdSet<(CursorId, PackedDispatchConfig)>,
    /// recovery_deltas: per-cursor `im::Vector<BuilderDelta>`; sparse
    /// (most cursors have no deltas). HAMT-backed; per-cursor push is
    /// O(log32 N) with prefix sharing across siblings.
    pub recovery_deltas: im::HashMap<CursorId, im::Vector<BuilderDelta>>,
    /// optional_scope_marks: per-cursor `im::Vector<usize>`; sparse.
    pub optional_scope_marks: im::HashMap<CursorId, im::Vector<usize>>,
    /// binder_scope_marks: per-cursor `im::Vector<(u16,
    /// im::Vector<String>)>`; sparse.
    pub binder_scope_marks:
        im::HashMap<CursorId, im::Vector<(u16, im::Vector<String>)>>,
    /// lex_fork_path: per-cursor `im::Vector<LexForkStamp>`; sparse.
    pub lex_fork_path: im::HashMap<CursorId, im::Vector<LexForkStamp>>,

    /// Lineage map: `parent_of_inheritance[child] = parent`. Used by
    /// `visited_dispatch_contains` / `visited_recovery_contains` to
    /// walk ancestor entries without sweep-on-Fork (per plan §3.5
    /// "key insight": chain walk replaces sweep). Stored as `im::HashMap`
    /// for the same Fork-time O(1) child-inserts.
    pub parent_of_inheritance: im::HashMap<CursorId, CursorId>,
}

impl<W: SemiringRef> Default for CursorStore<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: SemiringRef> CursorStore<W> {
    /// Construct an empty store.
    pub fn new() -> Self {
        Self {
            allocator: CursorIdAllocator::new(),
            minimal: Vec::new(),
            visited_dispatch: im::OrdSet::new(),
            visited_recovery: im::OrdSet::new(),
            recovery_deltas: im::HashMap::new(),
            optional_scope_marks: im::HashMap::new(),
            binder_scope_marks: im::HashMap::new(),
            lex_fork_path: im::HashMap::new(),
            parent_of_inheritance: im::HashMap::new(),
        }
    }

    /// Reset to empty (parse-boundary hook).
    pub fn clear(&mut self) {
        self.allocator.clear();
        self.minimal.clear();
        self.visited_dispatch = im::OrdSet::new();
        self.visited_recovery = im::OrdSet::new();
        self.recovery_deltas = im::HashMap::new();
        self.optional_scope_marks = im::HashMap::new();
        self.binder_scope_marks = im::HashMap::new();
        self.lex_fork_path = im::HashMap::new();
        self.parent_of_inheritance = im::HashMap::new();
    }

    /// Allocate a seed cursor (no parent — root of the parse).
    pub fn alloc_seed(&mut self, minimal: MinimalCursorState<W>) -> CursorId {
        let id = self.allocator.alloc();
        self.set_minimal(id, minimal);
        id
    }

    /// Allocate a child cursor inheriting from `parent` via the lineage
    /// chain. The caller is expected to follow up with `set_minimal`
    /// after applying any per-child branch-specific mutation.
    pub fn alloc_child(
        &mut self,
        parent: CursorId,
        minimal: MinimalCursorState<W>,
    ) -> CursorId {
        let id = self.allocator.alloc();
        self.set_minimal(id, minimal);
        if !parent.is_none() {
            self.parent_of_inheritance.insert(id, parent);
        }
        id
    }

    /// Retire a cursor: free its id, drop its persistent entries.
    /// HAMT structural sharing means the drop is cheap (the freed entries
    /// only disappear from the trie if no other handle owns the
    /// underlying node).
    pub fn retire(&mut self, id: CursorId) {
        if id.is_none() {
            return;
        }
        // Don't remove the minimal slot — sparse Vec keeps the slot as
        // None until the id is reallocated (idempotent reset).
        let idx = id.as_index();
        if idx < self.minimal.len() {
            self.minimal[idx] = None;
        }
        self.recovery_deltas.remove(&id);
        self.optional_scope_marks.remove(&id);
        self.binder_scope_marks.remove(&id);
        self.lex_fork_path.remove(&id);
        self.parent_of_inheritance.remove(&id);
        // visited_dispatch / visited_recovery: we don't sweep entries
        // here. Per plan §3.5, retired-id entries are harmless because
        // they cannot be reached by a future `contains` chain walk
        // (the lineage parent of any newly-allocated cursor is
        // recorded via alloc_child, not the retired id's children).
        // A periodic compaction pass (Substage 3+ enhancement) can
        // sweep `(retired_id, _)` entries at merge boundaries.
        self.allocator.retire(id);
    }

    /// Install / overwrite the minimal state for an id. Expands the
    /// sparse Vec as needed; existing slot is replaced.
    pub fn set_minimal(&mut self, id: CursorId, state: MinimalCursorState<W>) {
        if id.is_none() {
            return;
        }
        let idx = id.as_index();
        if idx >= self.minimal.len() {
            self.minimal.resize_with(idx + 1, || None);
        }
        self.minimal[idx] = Some(state);
    }

    /// Read the minimal state for an id. Returns `None` if the slot is
    /// empty (retired or never allocated).
    pub fn get_minimal(&self, id: CursorId) -> Option<&MinimalCursorState<W>> {
        if id.is_none() {
            return None;
        }
        self.minimal.get(id.as_index()).and_then(|opt| opt.as_ref())
    }

    /// Mutable companion of `get_minimal`.
    pub fn get_minimal_mut(
        &mut self,
        id: CursorId,
    ) -> Option<&mut MinimalCursorState<W>> {
        if id.is_none() {
            return None;
        }
        self.minimal
            .get_mut(id.as_index())
            .and_then(|opt| opt.as_mut())
    }

    // ── visited_dispatch operations (with lineage-chain semantics) ───

    /// Insert `(id, config)` into visited_dispatch.
    pub fn visited_dispatch_insert(
        &mut self,
        id: CursorId,
        config: PackedDispatchConfig,
    ) {
        if id.is_none() {
            return;
        }
        self.visited_dispatch.insert((id, config));
    }

    /// Test membership of `(id, config)`. Walks the lineage chain via
    /// `parent_of_inheritance` so an ancestor's prior insert is visible
    /// to the child. Per plan §3.5, the chain depth is bounded by
    /// nested Fork-depth.
    pub fn visited_dispatch_contains(
        &self,
        id: CursorId,
        config: PackedDispatchConfig,
    ) -> bool {
        let mut cur = id;
        while !cur.is_none() {
            if self.visited_dispatch.contains(&(cur, config)) {
                return true;
            }
            match self.parent_of_inheritance.get(&cur) {
                Some(&parent) => cur = parent,
                None => break,
            }
        }
        false
    }

    /// Insert `(id, config)` into visited_recovery.
    pub fn visited_recovery_insert(
        &mut self,
        id: CursorId,
        config: PackedDispatchConfig,
    ) {
        if id.is_none() {
            return;
        }
        self.visited_recovery.insert((id, config));
    }

    /// Test membership of `(id, config)` in visited_recovery with
    /// lineage-chain semantics.
    pub fn visited_recovery_contains(
        &self,
        id: CursorId,
        config: PackedDispatchConfig,
    ) -> bool {
        let mut cur = id;
        while !cur.is_none() {
            if self.visited_recovery.contains(&(cur, config)) {
                return true;
            }
            match self.parent_of_inheritance.get(&cur) {
                Some(&parent) => cur = parent,
                None => break,
            }
        }
        false
    }

    // ── recovery_deltas operations ───────────────────────────────────

    /// Push a builder delta onto cursor `id`'s recovery journal.
    pub fn recovery_deltas_push(&mut self, id: CursorId, delta: BuilderDelta) {
        if id.is_none() {
            return;
        }
        let mut v = self
            .recovery_deltas
            .get(&id)
            .cloned()
            .unwrap_or_else(im::Vector::new);
        v.push_back(delta);
        self.recovery_deltas.insert(id, v);
    }

    /// Read cursor `id`'s recovery_deltas (returns an empty iterator if
    /// absent).
    pub fn recovery_deltas_len(&self, id: CursorId) -> usize {
        self.recovery_deltas.get(&id).map_or(0, |v| v.len())
    }

    /// Materialize as a `Vec<BuilderDelta>` for replay at commit time.
    pub fn recovery_deltas_to_vec(&self, id: CursorId) -> Vec<BuilderDelta> {
        self.recovery_deltas
            .get(&id)
            .map(|v| v.iter().cloned().collect())
            .unwrap_or_default()
    }

    // ── Stats ────────────────────────────────────────────────────────

    /// Number of distinct cursor ids that have at least one
    /// visited_dispatch entry.
    pub fn visited_dispatch_distinct_cursors(&self) -> usize {
        let mut ids: std::collections::HashSet<CursorId> =
            std::collections::HashSet::new();
        for (id, _) in self.visited_dispatch.iter() {
            ids.insert(*id);
        }
        ids.len()
    }

    /// Total visited_dispatch entries (sum across cursors).
    pub fn visited_dispatch_total_entries(&self) -> usize {
        self.visited_dispatch.len()
    }

    /// Lineage-chain depth bound (max ancestor walk from any id).
    pub fn max_lineage_depth(&self) -> usize {
        let mut max_depth = 0;
        for (&id, _) in self.parent_of_inheritance.iter() {
            let mut depth = 0;
            let mut cur = id;
            while let Some(&parent) = self.parent_of_inheritance.get(&cur) {
                if parent.is_none() {
                    break;
                }
                depth += 1;
                cur = parent;
                if depth > 1_000_000 {
                    panic!(
                        "CursorStore::max_lineage_depth: chain depth >1M — \
                         likely a cycle bug"
                    );
                }
            }
            if depth > max_depth {
                max_depth = depth;
            }
        }
        max_depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;

    fn ready() -> WpdaState {
        WpdaState::Ready { min_bp: 0 }
    }

    fn seed_state() -> MinimalCursorState<LexicographicWeight> {
        MinimalCursorState::seed(LexicographicWeight::default(), ready())
    }

    #[test]
    fn store_starts_empty() {
        let s: CursorStore<LexicographicWeight> = CursorStore::new();
        assert_eq!(s.allocator.live_count(), 0);
        assert_eq!(s.visited_dispatch_total_entries(), 0);
        assert_eq!(s.visited_dispatch_distinct_cursors(), 0);
        assert_eq!(s.max_lineage_depth(), 0);
    }

    #[test]
    fn alloc_seed_returns_root_id() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let id = s.alloc_seed(seed_state());
        assert_eq!(id, CursorId(0));
        assert!(s.get_minimal(id).is_some());
        assert_eq!(s.allocator.live_count(), 1);
    }

    #[test]
    fn alloc_child_records_lineage() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let parent = s.alloc_seed(seed_state());
        let child = s.alloc_child(parent, seed_state());
        assert_ne!(parent, child);
        assert_eq!(s.parent_of_inheritance.get(&child), Some(&parent));
        assert_eq!(s.allocator.live_count(), 2);
    }

    #[test]
    fn retire_drops_minimal_and_lineage() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let parent = s.alloc_seed(seed_state());
        let child = s.alloc_child(parent, seed_state());
        s.retire(child);
        assert!(s.get_minimal(child).is_none());
        assert_eq!(s.parent_of_inheritance.get(&child), None);
        assert_eq!(s.allocator.live_count(), 1);
    }

    #[test]
    fn visited_dispatch_insert_then_contains() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let id = s.alloc_seed(seed_state());
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        assert!(!s.visited_dispatch_contains(id, cfg));
        s.visited_dispatch_insert(id, cfg);
        assert!(s.visited_dispatch_contains(id, cfg));
    }

    #[test]
    fn visited_dispatch_lineage_chain_resolves_parent_entry() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let parent = s.alloc_seed(seed_state());
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        s.visited_dispatch_insert(parent, cfg);
        let child = s.alloc_child(parent, seed_state());
        assert!(
            s.visited_dispatch_contains(child, cfg),
            "child should see parent's entry via lineage chain"
        );
    }

    #[test]
    fn visited_dispatch_lineage_chain_three_deep() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let a = s.alloc_seed(seed_state());
        let b = s.alloc_child(a, seed_state());
        let c = s.alloc_child(b, seed_state());
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        s.visited_dispatch_insert(a, cfg);
        assert!(s.visited_dispatch_contains(c, cfg));
        assert_eq!(s.max_lineage_depth(), 2);
    }

    #[test]
    fn visited_dispatch_chain_does_not_see_unrelated_cursor() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let a = s.alloc_seed(seed_state());
        let b = s.alloc_seed(seed_state());
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        s.visited_dispatch_insert(a, cfg);
        assert!(!s.visited_dispatch_contains(b, cfg));
    }

    #[test]
    fn visited_recovery_independent_of_visited_dispatch() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let id = s.alloc_seed(seed_state());
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        s.visited_dispatch_insert(id, cfg);
        assert!(!s.visited_recovery_contains(id, cfg));
        s.visited_recovery_insert(id, cfg);
        assert!(s.visited_recovery_contains(id, cfg));
    }

    #[test]
    fn recovery_deltas_push_then_read_len() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let id = s.alloc_seed(seed_state());
        assert_eq!(s.recovery_deltas_len(id), 0);
        s.recovery_deltas_push(id, BuilderDelta::EndBinderScope);
        s.recovery_deltas_push(id, BuilderDelta::EndBinderScope);
        assert_eq!(s.recovery_deltas_len(id), 2);
        let v = s.recovery_deltas_to_vec(id);
        assert_eq!(v.len(), 2);
    }

    #[test]
    fn retire_then_alloc_reuses_id() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let id = s.alloc_seed(seed_state());
        s.retire(id);
        let next = s.alloc_seed(seed_state());
        assert_eq!(id, next, "id should be recycled");
    }

    #[test]
    fn alloc_none_returns_none() {
        // CURSOR_ID_NONE handling is enforced at the caller layer; the
        // store treats it as a no-op for set_minimal / retire.
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        s.set_minimal(CURSOR_ID_NONE, seed_state());
        assert!(s.get_minimal(CURSOR_ID_NONE).is_none());
        s.retire(CURSOR_ID_NONE);
        assert_eq!(s.allocator.retire_count(), 0);
    }

    #[test]
    fn clear_resets_everything() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let a = s.alloc_seed(seed_state());
        let _b = s.alloc_child(a, seed_state());
        s.visited_dispatch_insert(a, PackedDispatchConfig::pack(0, 1, 0));
        s.recovery_deltas_push(a, BuilderDelta::EndBinderScope);
        s.clear();
        assert_eq!(s.allocator.live_count(), 0);
        assert_eq!(s.minimal.len(), 0);
        assert_eq!(s.visited_dispatch_total_entries(), 0);
        assert_eq!(s.recovery_deltas_len(a), 0);
        assert_eq!(s.parent_of_inheritance.get(&a), None);
    }

    #[test]
    fn distinct_cursors_counts_inserted_ids() {
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let a = s.alloc_seed(seed_state());
        let b = s.alloc_seed(seed_state());
        let cfg1 = PackedDispatchConfig::pack(0, 1, 0);
        let cfg2 = PackedDispatchConfig::pack(0, 2, 0);
        s.visited_dispatch_insert(a, cfg1);
        s.visited_dispatch_insert(a, cfg2);
        s.visited_dispatch_insert(b, cfg1);
        assert_eq!(s.visited_dispatch_distinct_cursors(), 2);
        assert_eq!(s.visited_dispatch_total_entries(), 3);
    }

    #[test]
    fn lineage_depth_bounded_at_chain_500() {
        // Stress test: alloc 500 cursors in a chain; verify lineage
        // depth equals 499 and chain walks complete.
        let mut s: CursorStore<LexicographicWeight> = CursorStore::new();
        let mut cur = s.alloc_seed(seed_state());
        for _ in 0..499 {
            cur = s.alloc_child(cur, seed_state());
        }
        assert_eq!(s.allocator.live_count(), 500);
        assert_eq!(s.max_lineage_depth(), 499);
        // Insert at root, query at leaf — chain walk completes.
        let root = CursorId(0);
        let cfg = PackedDispatchConfig::pack(0, 1, 0);
        s.visited_dispatch_insert(root, cfg);
        assert!(s.visited_dispatch_contains(cur, cfg));
    }
}
