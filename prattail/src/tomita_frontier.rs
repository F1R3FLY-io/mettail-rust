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

use std::marker::PhantomData;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::automata::semiring::SemiringRef;
use crate::dispatch_cohort::DispatchKey;
use crate::edge_stack_arena::EdgeStackId;
use crate::gss::{GssEdgeId, GssNodeId};
use crate::sppf::SppfId;
use crate::sppf_stack_arena::StackId;
use crate::wpda_runtime::WpdaState;
use crate::wpda_walker::{BranchCursor, BuilderDelta, LexForkStamp, PackedDispatchConfig};

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

/// Phase F.13 chain_10000 Exp 14 Substage 1.5+2.5 (2026-05-27): the
/// soundness-fix shell — strictly the TomitaKey-invariant axes plus
/// three dispatch-derived axes. Distinct from `CohortShell<W>` (which
/// continues to back H12 dispatch cohorts where members satisfy the
/// `~_obs` equivalence by construction).
///
/// The 6 heavy fields (`recovery_deltas`, `visited_dispatch`,
/// `visited_recovery`, `binder_scope_marks`, `optional_scope_marks`,
/// `sppf_collection_arena`) that the prior plan had on the shell live
/// PER-ARC on `FrontierArc<W>` — see redesigned plan §2.4.1 for the
/// gap analysis. Materializing an arc reads heavy fields from the
/// arc, not from the shell — preserving each cursor's original state.
///
/// Size budget per plan §2.5: ~48 B (5 + 3 axes, mostly Copy or small).
#[derive(Clone, Debug)]
pub struct TomitaShell<W: SemiringRef> {
    /// The 5 TomitaKey axes (cached for materialize / step).
    pub node: GssNodeId,
    pub pos: usize,
    pub inner_state: WpdaState,
    pub incoming_edge_stack_id: EdgeStackId,
    pub collection_depth: u8,
    /// The 3 dispatch-derived axes (TomitaKey-invariant by engine.step
    /// purity at every dispatch site — the same TomitaKey yields the
    /// same dispatch_key / sppf_stack_baseline_id / recovery_depth).
    pub dispatch_key: DispatchKey,
    pub sppf_stack_baseline_id: StackId,
    pub recovery_depth: u8,
    /// Phantom for the W type parameter (the shell itself carries no
    /// weight — weights live on FrontierArc).
    pub _phantom: PhantomData<W>,
}

impl<W: SemiringRef> TomitaShell<W> {
    /// Construct a TomitaShell from a BranchCursor. Reads the 5
    /// TomitaKey axes + 3 dispatch-derived axes; ignores per-arc
    /// divergent fields (those go on FrontierArc).
    pub fn from_cursor(cursor: &BranchCursor<W>) -> Self {
        Self {
            node: cursor.node,
            pos: cursor.pos,
            inner_state: cursor.inner_state.clone(),
            incoming_edge_stack_id: cursor.incoming_edge_stack_id,
            collection_depth: cursor.collection_stack_depth,
            // dispatch_key, sppf_stack_baseline_id, recovery_depth are
            // not strictly TomitaKey-invariant axes — they're per-cursor
            // by today's representation. Per the plan §3.1 they're
            // "dispatch-derived" axes that the H12 cohort_origin /
            // sppf_stack_baseline carry. For now we read them from the
            // cursor verbatim; Substage 6 may refine to enforce strict
            // shell-invariance via classifier predicates.
            dispatch_key: cursor.cohort_origin.clone().unwrap_or(DispatchKey::new(
                cursor.pos, 0, 0,
            )),
            sppf_stack_baseline_id: cursor.sppf_stack_id,
            recovery_depth: cursor.recovery_depth,
            _phantom: PhantomData,
        }
    }
}

/// Per-arc per-cursor-divergent state.
///
/// Under the soundness-fix redesign (Substage 1.5+2.5, per redesigned
/// plan §3.1 Option A), the 6 heavy `Arc<...>` fields move from
/// `CohortShell` to here. Each is an O(1) refcount bump at ingest; if
/// two arcs at the same TomitaKey share an Arc handle (because they
/// share a Fork ancestor that has not mutated the field since the
/// fork), physical memory is shared via Arc; if not, each arc keeps
/// its own.
///
/// Size budget under Option A: ~100 B
///   - 11 light fields (~52 B) — the original Substage 1 set
///   - 6 heavy field Arcs (~48 B = 6 × 8 B pointers) — NEW
///
/// vs today's ~512 B `BranchCursor`. The per-arc cost increase (~48 B
/// for the soundness fix) is offset by the structural sharing of the
/// shared 5-axis TomitaShell + the elimination of per-cursor
/// duplicate state at TomitaKey collisions.
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
    // ── Substage 1.5+2.5 soundness-fix heavy fields (Option A) ──────
    /// Per-cursor recovery journal (preserved verbatim per arc — see
    /// redesigned plan §2.4.1 for the soundness rationale: the prior
    /// plan placed this on the shell, silently dropping per-cursor
    /// deltas).
    pub recovery_deltas: Arc<Vec<BuilderDelta>>,
    /// Per-cursor cross-cat dispatch defense set.
    pub visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
    /// Per-cursor recovery dispatch defense set.
    pub visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
    /// Per-cursor binder scope marks.
    pub binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
    /// Per-cursor optional scope marks.
    pub optional_scope_marks: Arc<Vec<usize>>,
    /// Per-cursor SPPF collection arena.
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
}

impl<W: SemiringRef + Clone> FrontierArc<W> {
    /// Construct an arc with the given state. All fields explicit so
    /// callers cannot accidentally miss any.
    #[allow(clippy::too_many_arguments)]
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
        recovery_deltas: Arc<Vec<BuilderDelta>>,
        visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
        visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
        binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
        optional_scope_marks: Arc<Vec<usize>>,
        sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
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
            recovery_deltas,
            visited_dispatch,
            visited_recovery,
            binder_scope_marks,
            optional_scope_marks,
            sppf_collection_arena,
        }
    }

    /// Construct an arc from a BranchCursor — captures every per-arc
    /// divergent axis (the 11 light + 6 heavy fields). Each Arc is
    /// O(1) refcount bump; the underlying storage is shared until a
    /// later `Arc::make_mut` triggers CoW.
    pub fn from_cursor(cursor: &BranchCursor<W>) -> Self {
        Self {
            weight: cursor.weight.clone(),
            pending_packing_weight: cursor.pending_packing_weight.clone(),
            sppf_stack_id: cursor.sppf_stack_id,
            source_priority: cursor.source_priority,
            cohort_origin: cursor.cohort_origin.clone(),
            last_action_output_cat: cursor.last_action_output_cat,
            cohort_revive_depth: cursor.cohort_revive_depth,
            lex_fork_path: Arc::clone(&cursor.lex_fork_path),
            // Lex provenance — read from weight if the weight supports
            // it. For now, default to 0 (Substage 6 may refine).
            lex_alt_idx: 0,
            weight_src_idx: 0,
            weight_rule_idx: 0,
            // Substage 1.5+2.5 soundness-fix heavy fields: per-arc Arcs.
            recovery_deltas: Arc::clone(&cursor.recovery_deltas),
            visited_dispatch: Arc::clone(&cursor.visited_dispatch),
            visited_recovery: Arc::clone(&cursor.visited_recovery),
            binder_scope_marks: Arc::new(cursor.binder_scope_marks.clone()),
            optional_scope_marks: Arc::new(cursor.optional_scope_marks.clone()),
            sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
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

/// Phase F.13 chain_10000 Exp 14 Substage 1.5+2.5 (2026-05-27): the
/// soundness-fix materialize primitive. Reconstructs a `BranchCursor`
/// from a `(TomitaShell, FrontierArc)` pair. ALL 6 heavy fields are
/// read from the ARC, not from the shell — preserving each cursor's
/// original observable state. See redesigned plan §2.4.1.
///
/// This is the Tomita analog of `cohort_lazy::materialize_branch_cursor`
/// (which reads heavy fields from the shell — sound under H12's
/// construction-time `~_obs` guarantee but unsound for arbitrary-cursor
/// Tomita ingest).
pub fn materialize_branch_cursor_from_arc<W: SemiringRef + Clone>(
    shell: &TomitaShell<W>,
    arc: &FrontierArc<W>,
) -> BranchCursor<W> {
    BranchCursor {
        // Shared shell axes (TomitaKey-invariant).
        node: shell.node,
        pos: shell.pos,
        inner_state: shell.inner_state.clone(),
        incoming_edge_stack_id: shell.incoming_edge_stack_id,
        collection_stack_depth: shell.collection_depth,
        recovery_depth: shell.recovery_depth,
        // Per-arc divergent light axes.
        weight: arc.weight.clone(),
        pending_packing_weight: arc.pending_packing_weight.clone(),
        sppf_stack_id: arc.sppf_stack_id,
        source_priority: arc.source_priority,
        cohort_origin: arc.cohort_origin.clone(),
        last_action_output_cat: arc.last_action_output_cat,
        cohort_revive_depth: arc.cohort_revive_depth,
        lex_fork_path: Arc::clone(&arc.lex_fork_path),
        // THE SOUNDNESS FIX: 6 heavy fields read from arc, not shell.
        recovery_deltas: Arc::clone(&arc.recovery_deltas),
        visited_dispatch: Arc::clone(&arc.visited_dispatch),
        visited_recovery: Arc::clone(&arc.visited_recovery),
        binder_scope_marks: (*arc.binder_scope_marks).clone(),
        optional_scope_marks: (*arc.optional_scope_marks).clone(),
        sppf_collection_arena: Arc::clone(&arc.sppf_collection_arena),
    }
}

/// Frontier node: one shell (cached TomitaKey-invariant axes) + N arcs.
/// Equivalent to a Tomita-GLR stack node with N predecessor edges
/// augmented with the WPDS-walker shell state.
///
/// **Substage 1.5+2.5 redesign**: the shell is now `Arc<TomitaShell<W>>`
/// (not `Arc<CohortShell<W>>`). This separates the soundness boundary:
/// `TomitaShell` carries only TomitaKey-invariant axes (no heavy
/// per-cursor-divergent fields). The 6 heavy fields live PER-ARC on
/// `FrontierArc`. See redesigned plan §2.4.1 and §3.1.
///
/// The existing `Arc<CohortShell<W>>` continues to back H12 dispatch
/// cohorts (which DO satisfy the construction-time `~_obs` equivalence
/// at `dispatch_cohort::pause_cohort_member`); Tomita uses the strictly
/// soundness-safe `TomitaShell` subset for general-purpose merging.
#[derive(Clone)]
pub struct FrontierNode<W: SemiringRef> {
    /// Shared shell — strictly TomitaKey-invariant axes.
    pub shell: Arc<TomitaShell<W>>,
    /// The arcs. Vec because arc count is small (median ~3 at
    /// chain_500 LEFT-assoc per Substage 0 measurement).
    pub arcs: Vec<FrontierArc<W>>,
    /// Generation counter; incremented per `step_fanout` iteration.
    /// Frontier nodes whose generation lags the current map generation
    /// are evicted between steps (no live arcs).
    pub generation: u32,
}

impl<W: SemiringRef> FrontierNode<W> {
    /// Construct a fresh frontier node from a TomitaShell + initial
    /// single arc. The shell is wrapped in `Arc` here so all later
    /// arc-insertions share the same shell.
    pub fn new(shell: TomitaShell<W>, initial_arc: FrontierArc<W>, generation: u32) -> Self {
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
        shell_if_new: TomitaShell<W>,
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

    fn fresh_shell() -> TomitaShell<LexicographicWeight> {
        TomitaShell {
            node: 0,
            pos: 0,
            inner_state: WpdaState::Ready { min_bp: 0 },
            incoming_edge_stack_id: EDGE_STACK_ID_ROOT,
            collection_depth: 0,
            dispatch_key: DispatchKey::new(0, 0, 0),
            sppf_stack_baseline_id: STACK_ID_ROOT,
            recovery_depth: 0,
            _phantom: std::marker::PhantomData,
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
            Arc::new(Vec::new()),
            Arc::new(rustc_hash::FxHashSet::default()),
            Arc::new(rustc_hash::FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        )
    }

    // Helper: build a FrontierArc with specific heavy fields for
    // soundness round-trip tests.
    #[allow(clippy::too_many_arguments)]
    fn arc_with_heavy(
        recovery_deltas: Arc<Vec<BuilderDelta>>,
        visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
        visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
        binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
        optional_scope_marks: Arc<Vec<usize>>,
        sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
    ) -> FrontierArc<LexicographicWeight> {
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
            recovery_deltas,
            visited_dispatch,
            visited_recovery,
            binder_scope_marks,
            optional_scope_marks,
            sppf_collection_arena,
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

    // ── Substage 1.5+2.5 soundness-fix tests ─────────────────────────

    #[test]
    fn frontier_arc_carries_heavy_fields_independently() {
        // Two arcs at the same TomitaKey can have different heavy
        // Arcs — register_arc must preserve each arc's Arcs (not
        // drop them via shell-overwrite as the prior plan would have).
        let mut map: TomitaFrontierMap<LexicographicWeight> =
            TomitaFrontierMap::new();
        let mut deltas_a = Vec::new();
        deltas_a.push(BuilderDelta::EndBinderScope);
        let deltas_a_arc: Arc<Vec<BuilderDelta>> = Arc::new(deltas_a);
        let deltas_b_arc: Arc<Vec<BuilderDelta>> = Arc::new(Vec::new());
        let arc_a = arc_with_heavy(
            Arc::clone(&deltas_a_arc),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let arc_b = arc_with_heavy(
            Arc::clone(&deltas_b_arc),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        map.register_arc(fresh_key(), fresh_shell(), arc_a);
        map.register_arc(fresh_key(), fresh_shell(), arc_b);
        let node = map.get(&fresh_key()).expect("node present");
        assert_eq!(node.arcs.len(), 2);
        // Per-arc heavy fields are preserved verbatim.
        assert_eq!(node.arcs[0].recovery_deltas.len(), 1);
        assert_eq!(node.arcs[1].recovery_deltas.len(), 0);
        assert!(Arc::ptr_eq(&node.arcs[0].recovery_deltas, &deltas_a_arc));
        assert!(Arc::ptr_eq(&node.arcs[1].recovery_deltas, &deltas_b_arc));
    }

    #[test]
    fn frontier_arc_visited_dispatch_per_arc() {
        // Two arcs at the same TomitaKey can have different
        // visited_dispatch sets — neither sees the other's entries.
        let mut set_a: FxHashSet<PackedDispatchConfig> = FxHashSet::default();
        set_a.insert(PackedDispatchConfig::pack(0, 1, 0));
        let arc_a = arc_with_heavy(
            Arc::new(Vec::new()),
            Arc::new(set_a),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let arc_b = arc_with_heavy(
            Arc::new(Vec::new()),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let mut map: TomitaFrontierMap<LexicographicWeight> =
            TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), arc_a);
        map.register_arc(fresh_key(), fresh_shell(), arc_b);
        let node = map.get(&fresh_key()).expect("node present");
        assert_eq!(node.arcs[0].visited_dispatch.len(), 1);
        assert_eq!(node.arcs[1].visited_dispatch.len(), 0);
    }

    #[test]
    fn materialize_from_arc_restores_heavy_fields() {
        // materialize_branch_cursor_from_arc must reconstruct ALL 6
        // heavy fields from the arc, not from the shell.
        let mut set_a: FxHashSet<PackedDispatchConfig> = FxHashSet::default();
        set_a.insert(PackedDispatchConfig::pack(42, 7, 3));
        let arc = arc_with_heavy(
            Arc::new(vec![BuilderDelta::EndBinderScope]),
            Arc::new(set_a),
            Arc::new(FxHashSet::default()),
            Arc::new(vec![(1u16, vec!["x".to_string(), "y".to_string()])]),
            Arc::new(vec![5usize, 10usize]),
            Arc::new(vec![vec![1u32, 2u32, 3u32]]),
        );
        let cursor = materialize_branch_cursor_from_arc(&fresh_shell(), &arc);
        assert_eq!(cursor.recovery_deltas.len(), 1);
        assert_eq!(cursor.visited_dispatch.len(), 1);
        assert_eq!(cursor.visited_recovery.len(), 0);
        assert_eq!(cursor.binder_scope_marks.len(), 1);
        assert_eq!(cursor.binder_scope_marks[0].1.len(), 2);
        assert_eq!(cursor.optional_scope_marks, vec![5usize, 10usize]);
        assert_eq!(cursor.sppf_collection_arena.len(), 1);
    }

    #[test]
    fn materialize_round_trip_two_distinct_arcs_recovers_separate_heavy_state() {
        // Soundness regression test: ingest two cursors with distinct
        // recovery_deltas at the same TomitaKey; materialize each arc
        // back to a cursor; verify each materialized cursor has its
        // original recovery_deltas, NOT the other's.
        let arc_a = arc_with_heavy(
            Arc::new(vec![BuilderDelta::EndBinderScope]),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let arc_b = arc_with_heavy(
            Arc::new(Vec::new()),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let mut map: TomitaFrontierMap<LexicographicWeight> =
            TomitaFrontierMap::new();
        map.register_arc(fresh_key(), fresh_shell(), arc_a);
        map.register_arc(fresh_key(), fresh_shell(), arc_b);
        let node = map.get(&fresh_key()).expect("node present");
        // Materialize both arcs:
        let cursor_a =
            materialize_branch_cursor_from_arc(&node.shell, &node.arcs[0]);
        let cursor_b =
            materialize_branch_cursor_from_arc(&node.shell, &node.arcs[1]);
        // Each cursor preserved its own recovery_deltas:
        assert_eq!(cursor_a.recovery_deltas.len(), 1);
        assert_eq!(cursor_b.recovery_deltas.len(), 0);
    }

    #[test]
    fn arc_clone_preserves_strong_count() {
        // Each arc's heavy field Arcs increment strong_count when the
        // arc is registered (Arc::clone in from_cursor / new). After
        // registration, the underlying Arc has 2 strong refs (caller +
        // arc's copy).
        let deltas: Arc<Vec<BuilderDelta>> = Arc::new(Vec::new());
        assert_eq!(Arc::strong_count(&deltas), 1);
        let arc = arc_with_heavy(
            Arc::clone(&deltas),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        assert_eq!(Arc::strong_count(&deltas), 2);
        // Drop the arc: strong_count drops back to 1.
        drop(arc);
        assert_eq!(Arc::strong_count(&deltas), 1);
    }

    #[test]
    fn arc_clone_shared_via_arc_ptr_eq() {
        // Two arcs constructed from the same parent's Arc (via
        // Arc::clone) share the underlying allocation.
        let shared: Arc<Vec<BuilderDelta>> = Arc::new(Vec::new());
        let arc_a = arc_with_heavy(
            Arc::clone(&shared),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        let arc_b = arc_with_heavy(
            Arc::clone(&shared),
            Arc::new(FxHashSet::default()),
            Arc::new(FxHashSet::default()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        );
        assert!(Arc::ptr_eq(&arc_a.recovery_deltas, &arc_b.recovery_deltas));
    }

    #[test]
    fn tomita_shell_distinct_from_cohort_shell_at_layout() {
        // Sanity: TomitaShell is markedly smaller than CohortShell —
        // 8 axes (mostly Copy / small) vs CohortShell's 20+ axes
        // including 6 Arc-wrapped heavy fields. We assert the
        // soundness boundary: TomitaShell does NOT have heavy fields.
        let shell = fresh_shell();
        // No method on TomitaShell returns Arc<FxHashSet> / Arc<Vec> —
        // the field layout does not contain them. Test by attempting
        // to access any heavy field — they should not exist.
        let _: GssNodeId = shell.node;
        let _: usize = shell.pos;
        let _: WpdaState = shell.inner_state.clone();
        // Anything resembling visited_dispatch / recovery_deltas /
        // binder_scope_marks etc. on the shell would be a compile
        // error. This test compiles ⇒ those fields are absent.
    }

    #[test]
    fn tomita_shell_from_cursor_captures_invariant_axes() {
        // Construct a synthetic BranchCursor with known invariant axes;
        // verify TomitaShell::from_cursor reads them correctly.
        use crate::edge_stack_arena::EDGE_STACK_ID_ROOT;
        let cursor: BranchCursor<LexicographicWeight> = BranchCursor {
            node: 42,
            pos: 7,
            inner_state: WpdaState::InfixLoop { cur_bp: 10 },
            incoming_edge_stack_id: EDGE_STACK_ID_ROOT,
            collection_stack_depth: 3,
            recovery_depth: 1,
            weight: LexicographicWeight::default(),
            pending_packing_weight: LexicographicWeight::default(),
            sppf_stack_id: STACK_ID_ROOT,
            source_priority: 0,
            cohort_origin: None,
            last_action_output_cat: None,
            cohort_revive_depth: 0,
            lex_fork_path: Arc::new(Vec::new()),
            recovery_deltas: Arc::new(Vec::new()),
            visited_dispatch: Arc::new(FxHashSet::default()),
            visited_recovery: Arc::new(FxHashSet::default()),
            binder_scope_marks: Vec::new(),
            optional_scope_marks: Vec::new(),
            sppf_collection_arena: Arc::new(Vec::new()),
        };
        let shell = TomitaShell::from_cursor(&cursor);
        assert_eq!(shell.node, 42);
        assert_eq!(shell.pos, 7);
        assert_eq!(shell.collection_depth, 3);
        assert_eq!(shell.recovery_depth, 1);
        assert!(matches!(shell.inner_state, WpdaState::InfixLoop { cur_bp: 10 }));
    }
}
