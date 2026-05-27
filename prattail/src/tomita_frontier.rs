//! Phase F.13 chain_10000 Exp 14 Substage 1 (2026-05-27): Tomita-style
//! frontier merge map.
//!
//! # Background
//!
//! Per Tomita (1985) GLR and Scott-Johnstone (2010) GLL: when N parsers
//! reach the same descriptor (grammar slot + GSS-tip + input position
//! + SPPF tip), they are observationally equivalent and merge.
//!
//! Per Exp 14 plan (`prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`)
//! Substage 0 measurement (commit `9662b81`, 2026-05-27), the projected
//! per-step merge factor under a coarsened 5-tuple key
//! `TomitaKey = (state, node, pos, edge_top, collection_depth)` is
//! 2.85x-3.11x on LEFT-assoc chain_50/100/200 and 2.68x-2.71x on
//! RIGHT-assoc chain_50/100/200/1000. Below the plan's heuristic 5x
//! threshold but Welch-significant (p=9.2e-8). The 3x merge collapses
//! 28.9 M cohort cursor emissions at chain_500 LEFT-assoc to ~9.6 M —
//! a 67% reduction that is structurally meaningful.
//!
//! # This module
//!
//! Substage 1 ships ONLY the data structure module + types + tests —
//! dead code, no walker integration. Substage 3 wires the ingest path
//! at `step_fanout`'s drained-frame loop; subsequent substages graduate
//! actions to shell-broadcast paths.
//!
//! # Design (per plan §3.1)
//!
//! - [`TomitaKey`] is the coarse merge key.
//! - [`FrontierArc<W>`] carries the per-cursor-divergent state that a
//!   single `TomitaKey` cohort's arcs each track distinctly.
//! - [`FrontierNode<W>`] is one TomitaKey's shell + N arcs.
//! - [`TomitaFrontierMap<W>`] is the walker-global merge map.
//! - [`TomitaDivergence`] is the per-action classifier that the
//!   step_fanout's per-frontier dispatch consults; Substage 2 ships the
//!   classifier extensions in `cohort_lazy.rs`.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::automata::semiring::SemiringRef;
use crate::cohort_lazy::CohortShell;
use crate::dispatch_cohort::DispatchKey;
use crate::gss::{GssEdgeId, GssNodeId};
use crate::sppf_stack_arena::StackId;
use crate::wpda_runtime::WpdaState;
use crate::wpda_walker::LexForkStamp;

/// Tomita-merge key for the walker-global frontier merge map.
///
/// Coarsening of the current `ConfigKey` 11-tuple (see
/// `wpda_walker.rs:1827-1929`) that drops the four per-cursor lex
/// provenance axes (`lex_alt_idx`, `weight_src_idx`, `weight_rule_idx`,
/// `lex_fork_stamp`) plus `cohort_origin` plus `sppf_top`. Cursors with
/// the same TomitaKey but distinct ConfigKey arc-merge under this map.
///
/// Soundness: per the Exp 14 plan §2.4 (proof sketch), the engine's
/// `step` function is pure of cursor state at every dispatch site —
/// two cursors with the same TomitaKey receive the same
/// `WpdaStepAction`. Actions whose effect is invariant on the dropped
/// axes can apply to the shell once and broadcast per-arc weight
/// updates; divergent actions force per-arc materialization.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct TomitaKey {
    pub state: WpdaState,
    pub node: GssNodeId,
    pub pos: usize,
    pub incoming_edge_top: Option<GssEdgeId>,
    pub collection_depth: u8,
}

impl TomitaKey {
    /// Convenience constructor taking the 5 axes verbatim.
    pub fn new(
        state: WpdaState,
        node: GssNodeId,
        pos: usize,
        incoming_edge_top: Option<GssEdgeId>,
        collection_depth: u8,
    ) -> Self {
        Self {
            state,
            node,
            pos,
            incoming_edge_top,
            collection_depth,
        }
    }
}

/// Per-arc per-cursor-divergent state: the axes that today's
/// `BranchCursor` tracks distinctly but `TomitaKey` deliberately drops.
///
/// Size budget per plan §2.5: ~52 B for `LexicographicWeight` (12 B W),
/// vs today's ~512 B `BranchCursor`. Arc storage replaces full cursor
/// storage at every frontier collision.
#[derive(Clone, Debug)]
pub struct FrontierArc<W: SemiringRef> {
    /// Cumulative weight (matches `BranchCursor::weight`).
    pub weight: W,
    /// Pending Packing weight (matches `BranchCursor::pending_packing_weight`).
    pub pending_packing_weight: W,
    /// SPPF working-stack head (per-arc — distinct derivation histories
    /// produce different stack tops).
    pub sppf_stack_id: StackId,
    /// Stage 3.12 source-priority for Fork tiebreak.
    pub source_priority: u32,
    /// H12 cohort discriminator (matches `BranchCursor::cohort_origin`).
    pub cohort_origin: Option<DispatchKey>,
    /// Last action's output category (cross-cat dispatch propagation).
    pub last_action_output_cat: Option<u16>,
    /// Stage 3.20 / L12 bounded recovery counter.
    pub cohort_revive_depth: u32,
    /// Lex fork-path (Arc-shared; clone is O(1)).
    pub lex_fork_path: Arc<Vec<LexForkStamp>>,
    /// Lex provenance triple cached on the arc (for fast ConfigKey-
    /// equivalent dedup at arc-merge time without re-reading weight).
    pub lex_alt_idx: u16,
    pub weight_src_idx: u16,
    pub weight_rule_idx: u16,
}

impl<W: SemiringRef> FrontierArc<W> {
    /// Construct an arc with the given state. All fields explicit so
    /// callers cannot accidentally miss any.
    pub fn new(
        weight: W,
        pending_packing_weight: W,
        sppf_stack_id: StackId,
        source_priority: u32,
        cohort_origin: Option<DispatchKey>,
        last_action_output_cat: Option<u16>,
        cohort_revive_depth: u32,
        lex_fork_path: Arc<Vec<LexForkStamp>>,
        lex_alt_idx: u16,
        weight_src_idx: u16,
        weight_rule_idx: u16,
    ) -> Self {
        Self {
            weight,
            pending_packing_weight,
            sppf_stack_id,
            source_priority,
            cohort_origin,
            last_action_output_cat,
            cohort_revive_depth,
            lex_fork_path,
            lex_alt_idx,
            weight_src_idx,
            weight_rule_idx,
        }
    }

    /// Disambiguator for arc-level merge: arcs with equal disambiguator
    /// are mergeable at the same frontier under
    /// `LexicographicWeight`-style idempotent ⊕ aggregation.
    ///
    /// Per the Exp 14 plan §3.6 risk register R6/R8: divergent arc
    /// state (sppf_stack_id, lex provenance, cohort origin) MUST keep
    /// arcs distinct; only same-disambiguator arcs may collapse.
    pub fn merge_disambiguator(
        &self,
    ) -> (StackId, Option<DispatchKey>, u16, u16, u16) {
        (
            self.sppf_stack_id,
            self.cohort_origin.clone(),
            self.lex_alt_idx,
            self.weight_src_idx,
            self.weight_rule_idx,
        )
    }
}

/// Frontier node: one shell (cached TomitaKey axes + L1-L6 cohort shell
/// fields) + N arcs. Equivalent to a Tomita-GLR stack node with N
/// predecessor edges augmented with the WPDS-walker shell state.
#[derive(Clone)]
pub struct FrontierNode<W: SemiringRef> {
    /// Shared shell — reuses the existing L1-L6 `CohortShell` layout.
    /// Substage 3 wiring: at ingest, the walker constructs a new
    /// `CohortShell` per fresh TomitaKey, then shares the `Arc` across
    /// all arcs that land on this key. `Arc::make_mut` does one
    /// deep-clone per cohort first-mutation (vs one per cursor today).
    pub shell: Arc<CohortShell<W>>,
    /// The arcs. Vec because arc count is small (median ~10 at
    /// chain_500 LEFT-assoc per the Exp 16 r3 cohort-cursor-emission
    /// ratio).
    pub arcs: Vec<FrontierArc<W>>,
    /// Generation counter; incremented per `step_fanout` iteration.
    /// Frontier nodes whose generation lags the current map generation
    /// are evicted between steps (no live arcs).
    pub generation: u32,
}

impl<W: SemiringRef> FrontierNode<W> {
    /// Construct a fresh frontier node from a shell + initial single
    /// arc. The shell is wrapped in `Arc` here so all later
    /// arc-insertions share the same shell.
    pub fn new(shell: CohortShell<W>, initial_arc: FrontierArc<W>, generation: u32) -> Self {
        Self {
            shell: Arc::new(shell),
            arcs: vec![initial_arc],
            generation,
        }
    }

    /// Append an arc to this frontier node, marking it current-gen.
    pub fn push_arc(&mut self, arc: FrontierArc<W>, generation: u32) {
        self.arcs.push(arc);
        self.generation = generation;
    }

    /// Number of arcs at this frontier node.
    pub fn arc_count(&self) -> usize {
        self.arcs.len()
    }
}

/// Walker-global Tomita frontier merge map.
///
/// Lifecycle:
/// - Cleared at `WpdaWalker::reset()`.
/// - Grows during `step_fanout` via `register_arc` (Substage 3).
/// - Drained at end-of-step into the post-merge `branch_cursors:
///   Vec<Frame<W>>` (Substage 4+).
///
/// Per the plan §3.1, FxHashMap is chosen for hash speed (already the
/// walker's standard); the key is ~24 B (`WpdaState` + node u32 +
/// pos usize + Option<u64> + u8).
pub struct TomitaFrontierMap<W: SemiringRef> {
    /// Walker-global keyed map.
    map: FxHashMap<TomitaKey, FrontierNode<W>>,
    /// Per-step generation counter.
    current_generation: u32,
    /// Total `register_arc` calls (stats-only, walker-stats feature
    /// gated at use site). Not gated here so the field exists in both
    /// builds.
    total_registrations: u64,
    /// Total dedup hits (an arc landed on an existing TomitaKey).
    dedup_hits: u64,
}

impl<W: SemiringRef> Default for TomitaFrontierMap<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: SemiringRef> TomitaFrontierMap<W> {
    /// Construct an empty map.
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            current_generation: 0,
            total_registrations: 0,
            dedup_hits: 0,
        }
    }

    /// Reset to empty (parse-boundary hook).
    pub fn clear(&mut self) {
        self.map.clear();
        self.current_generation = 0;
        self.total_registrations = 0;
        self.dedup_hits = 0;
    }

    /// Begin the next step generation. Frontier nodes whose generation
    /// lags the new current generation become eligible for eviction
    /// via `evict_stale`.
    pub fn begin_generation(&mut self) {
        self.current_generation = self.current_generation.wrapping_add(1);
    }

    /// Read the current generation.
    pub fn current_generation(&self) -> u32 {
        self.current_generation
    }

    /// Register an arc at the given TomitaKey. If the key is new,
    /// allocate a fresh FrontierNode with the provided shell + arc as
    /// the only initial arc. If the key exists, push the arc onto
    /// the existing node (incrementing dedup_hits).
    ///
    /// The caller supplies the shell ONLY when a fresh node needs to
    /// be allocated; for an existing-key insert, the shell parameter
    /// is dropped (the existing node's shell is authoritative).
    ///
    /// Returns the post-insert arc-count of the frontier node at this
    /// key (= 1 for a fresh node; >1 for a dedup hit).
    pub fn register_arc(
        &mut self,
        key: TomitaKey,
        shell_if_new: CohortShell<W>,
        arc: FrontierArc<W>,
    ) -> usize {
        self.total_registrations = self.total_registrations.saturating_add(1);
        let gen = self.current_generation;
        match self.map.get_mut(&key) {
            Some(node) => {
                node.push_arc(arc, gen);
                self.dedup_hits = self.dedup_hits.saturating_add(1);
                node.arc_count()
            }
            None => {
                let node = FrontierNode::new(shell_if_new, arc, gen);
                self.map.insert(key, node);
                1
            }
        }
    }

    /// Number of distinct TomitaKeys currently in the map.
    pub fn distinct_keys(&self) -> usize {
        self.map.len()
    }

    /// Read access to a frontier node by key (for the per-frontier
    /// step dispatch in Substage 4+).
    pub fn get(&self, key: &TomitaKey) -> Option<&FrontierNode<W>> {
        self.map.get(key)
    }

    /// Mutable access to a frontier node by key.
    pub fn get_mut(&mut self, key: &TomitaKey) -> Option<&mut FrontierNode<W>> {
        self.map.get_mut(key)
    }

    /// Drain frontier nodes whose generation matches the current one;
    /// removes them from the map and yields ownership. Used by
    /// Substage 4+'s per-frontier step dispatch loop.
    pub fn drain_current_generation(
        &mut self,
    ) -> Vec<(TomitaKey, FrontierNode<W>)> {
        let cur = self.current_generation;
        let keys: Vec<TomitaKey> = self
            .map
            .iter()
            .filter_map(|(k, node)| if node.generation == cur { Some(k.clone()) } else { None })
            .collect();
        let mut out = Vec::with_capacity(keys.len());
        for k in keys {
            if let Some(node) = self.map.remove(&k) {
                out.push((k, node));
            }
        }
        out
    }

    /// Evict frontier nodes whose generation lags the current one.
    /// Used by Substage 4+ when arcs no longer flow through stale
    /// frontiers between steps (correctness defense — stale arcs are
    /// dangling references that risk reading freed SPPF/GSS state at
    /// reset boundaries; cleaner to drop them at step end).
    pub fn evict_stale(&mut self) -> usize {
        let cur = self.current_generation;
        let before = self.map.len();
        self.map.retain(|_, node| node.generation == cur);
        before.saturating_sub(self.map.len())
    }

    /// Total registrations (= sum of `register_arc` calls).
    pub fn total_registrations(&self) -> u64 {
        self.total_registrations
    }

    /// Total dedup hits.
    pub fn dedup_hits(&self) -> u64 {
        self.dedup_hits
    }

    /// Per-call merge hit ratio (0.0-1.0). Higher = more frontier-level
    /// sharing.
    pub fn hit_ratio(&self) -> f64 {
        if self.total_registrations == 0 {
            0.0
        } else {
            (self.dedup_hits as f64) / (self.total_registrations as f64)
        }
    }
}

/// Per-action divergence classifier for the planned Tomita per-arc
/// dispatch. Substage 2 extends `cohort_lazy::DivergenceClass` with a
/// new `classify_for_tomita` overload; this enum is the shape it
/// returns at action time. Walker uses the variant to decide:
///   - `ObsInvariantOverArcs`: apply once to shell + broadcast weight
///     multiplication to each arc.
///   - `ObsDivergentOverArcs`: materialize each arc to a Concrete
///     BranchCursor + per-cursor step (existing fall-through path).
///   - `DispatchResolved`: H12 cross-cat-projection result already
///     materialized in the dispatch_cohort_cache; re-register per
///     (arc, snapshot) pair.
///
/// Substage 4 ships the first ObsInvariantOverArcs handler for the
/// Advance/Accept/Error/Idle variants; Substage 5 graduates Push/Pop/
/// Replace/ConsumeAndPush when the popped/pushed EdgeKind is convergent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TomitaDivergence {
    /// Action effect is invariant on per-arc state — shell broadcast.
    ObsInvariantOverArcs,
    /// Action effect diverges per arc — materialize each arc.
    ObsDivergentOverArcs,
    /// H12 dispatch resolution; arcs become snapshot fan-out.
    DispatchResolved,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::edge_stack_arena::EDGE_STACK_ID_ROOT;
    use crate::sppf_stack_arena::STACK_ID_ROOT;
    use crate::wpda_runtime::WpdaState;

    fn fresh_key() -> TomitaKey {
        TomitaKey::new(
            WpdaState::Ready { min_bp: 0 },
            0,
            0,
            None,
            0,
        )
    }

    fn fresh_shell() -> CohortShell<LexicographicWeight> {
        CohortShell {
            node: 0,
            incoming_edge_stack_id: EDGE_STACK_ID_ROOT,
            collection_depth: 0,
            cohort_origin: None,
            lex_alt_idx: 0,
            weight_src_idx: 0,
            weight_rule_idx: 0,
            lex_fork_stamp: None,
            binder_scope_marks: Arc::new(Vec::new()),
            optional_scope_marks: Arc::new(Vec::new()),
            sppf_collection_arena: Arc::new(Vec::new()),
            visited_dispatch: Arc::new(rustc_hash::FxHashSet::default()),
            visited_recovery: Arc::new(rustc_hash::FxHashSet::default()),
            recovery_depth: 0,
            recovery_deltas: Arc::new(Vec::new()),
            inner_state: WpdaState::Ready { min_bp: 0 },
            pos: 0,
            dispatch_key: DispatchKey::new(0, 0, 0),
            sppf_stack_baseline_id: STACK_ID_ROOT,
            _phantom_weight: std::marker::PhantomData,
        }
    }

    fn fresh_arc() -> FrontierArc<LexicographicWeight> {
        FrontierArc::new(
            LexicographicWeight::default(),
            LexicographicWeight::default(),
            STACK_ID_ROOT,
            0,
            None,
            None,
            0,
            Arc::new(Vec::new()),
            0,
            0,
            0,
        )
    }

    #[test]
    fn map_starts_empty() {
        let map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        assert_eq!(map.distinct_keys(), 0);
        assert_eq!(map.total_registrations(), 0);
        assert_eq!(map.dedup_hits(), 0);
        assert_eq!(map.hit_ratio(), 0.0);
        assert_eq!(map.current_generation(), 0);
    }

    #[test]
    fn first_register_creates_node() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        let count = map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        assert_eq!(count, 1);
        assert_eq!(map.distinct_keys(), 1);
        assert_eq!(map.total_registrations(), 1);
        assert_eq!(map.dedup_hits(), 0);
    }

    #[test]
    fn second_register_same_key_dedups_arc() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        let count = map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        assert_eq!(count, 2);
        assert_eq!(map.distinct_keys(), 1);
        assert_eq!(map.total_registrations(), 2);
        assert_eq!(map.dedup_hits(), 1);
        assert!((map.hit_ratio() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn distinct_keys_for_distinct_pos() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        let mut k_a = fresh_key();
        k_a.pos = 1;
        let mut k_b = fresh_key();
        k_b.pos = 2;
        map.register_arc(k_a, fresh_shell(), fresh_arc());
        map.register_arc(k_b, fresh_shell(), fresh_arc());
        assert_eq!(map.distinct_keys(), 2);
    }

    #[test]
    fn distinct_keys_for_distinct_node() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        let mut k_a = fresh_key();
        k_a.node = 10;
        let mut k_b = fresh_key();
        k_b.node = 11;
        map.register_arc(k_a, fresh_shell(), fresh_arc());
        map.register_arc(k_b, fresh_shell(), fresh_arc());
        assert_eq!(map.distinct_keys(), 2);
    }

    #[test]
    fn distinct_keys_for_distinct_state() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        let mut k_a = fresh_key();
        k_a.state = WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 };
        let mut k_b = fresh_key();
        k_b.state = WpdaState::InfixLoop { cur_bp: 0 };
        map.register_arc(k_a, fresh_shell(), fresh_arc());
        map.register_arc(k_b, fresh_shell(), fresh_arc());
        assert_eq!(map.distinct_keys(), 2);
    }

    #[test]
    fn generation_increments() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        assert_eq!(map.current_generation(), 0);
        map.begin_generation();
        assert_eq!(map.current_generation(), 1);
        map.begin_generation();
        assert_eq!(map.current_generation(), 2);
    }

    #[test]
    fn evict_stale_drops_lagging_generation() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        // gen=0, register one arc.
        let mut k_old = fresh_key();
        k_old.pos = 1;
        map.register_arc(k_old, fresh_shell(), fresh_arc());
        assert_eq!(map.distinct_keys(), 1);
        // advance to gen=1, register a new arc.
        map.begin_generation();
        let mut k_new = fresh_key();
        k_new.pos = 2;
        map.register_arc(k_new, fresh_shell(), fresh_arc());
        assert_eq!(map.distinct_keys(), 2);
        // evict: the gen=0 node lags and goes away.
        let evicted = map.evict_stale();
        assert_eq!(evicted, 1);
        assert_eq!(map.distinct_keys(), 1);
    }

    #[test]
    fn drain_current_generation_removes_matching_nodes() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        let mut k_a = fresh_key();
        k_a.pos = 1;
        let mut k_b = fresh_key();
        k_b.pos = 2;
        map.register_arc(k_a, fresh_shell(), fresh_arc());
        map.register_arc(k_b, fresh_shell(), fresh_arc());
        let drained = map.drain_current_generation();
        assert_eq!(drained.len(), 2);
        assert_eq!(map.distinct_keys(), 0);
    }

    #[test]
    fn clear_resets_map() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        map.begin_generation();
        map.clear();
        assert_eq!(map.distinct_keys(), 0);
        assert_eq!(map.total_registrations(), 0);
        assert_eq!(map.dedup_hits(), 0);
        assert_eq!(map.current_generation(), 0);
    }

    #[test]
    fn arc_merge_disambiguator_distinguishes_lex_provenance() {
        let arc1 = fresh_arc();
        let mut arc2 = fresh_arc();
        arc2.lex_alt_idx = 5;
        assert_ne!(arc1.merge_disambiguator(), arc2.merge_disambiguator());
    }

    #[test]
    fn arc_merge_disambiguator_distinguishes_sppf_stack() {
        let arc1 = fresh_arc();
        let mut arc2 = fresh_arc();
        arc2.sppf_stack_id = StackId(1234);
        assert_ne!(arc1.merge_disambiguator(), arc2.merge_disambiguator());
    }

    #[test]
    fn frontier_node_push_arc_increments_count() {
        let mut node = FrontierNode::new(fresh_shell(), fresh_arc(), 0);
        assert_eq!(node.arc_count(), 1);
        node.push_arc(fresh_arc(), 0);
        assert_eq!(node.arc_count(), 2);
    }

    #[test]
    fn frontier_node_push_arc_updates_generation() {
        let mut node = FrontierNode::new(fresh_shell(), fresh_arc(), 0);
        assert_eq!(node.generation, 0);
        node.push_arc(fresh_arc(), 7);
        assert_eq!(node.generation, 7);
    }

    #[test]
    fn tomita_divergence_variants_are_distinct() {
        assert_ne!(
            TomitaDivergence::ObsInvariantOverArcs,
            TomitaDivergence::ObsDivergentOverArcs,
        );
        assert_ne!(
            TomitaDivergence::ObsInvariantOverArcs,
            TomitaDivergence::DispatchResolved,
        );
        assert_ne!(
            TomitaDivergence::ObsDivergentOverArcs,
            TomitaDivergence::DispatchResolved,
        );
    }

    #[test]
    fn shell_arc_share_via_arc_clone() {
        // Two registrations at the same TomitaKey share the shell Arc.
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        let node = map.get(&fresh_key()).expect("node present");
        assert_eq!(node.arcs.len(), 2);
        // The shell from the second register call is dropped — the
        // first registration's shell remains authoritative.
        assert_eq!(Arc::strong_count(&node.shell), 1);
    }

    #[test]
    fn high_arc_count_does_not_grow_map() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        for _ in 0..1000 {
            map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        }
        assert_eq!(map.distinct_keys(), 1);
        assert_eq!(map.total_registrations(), 1000);
        assert_eq!(map.dedup_hits(), 999);
        let node = map.get(&fresh_key()).expect("node present");
        assert_eq!(node.arcs.len(), 1000);
    }

    #[test]
    fn registration_across_generations_routes_to_existing_node() {
        let mut map: TomitaFrontierMap<LexicographicWeight> = TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        map.begin_generation();
        let count = map.register_arc(fresh_key(), fresh_shell(), fresh_arc());
        assert_eq!(count, 2);
        let node = map.get(&fresh_key()).expect("node present");
        assert_eq!(node.generation, 1, "registration in gen 1 marks the node current");
    }
}
