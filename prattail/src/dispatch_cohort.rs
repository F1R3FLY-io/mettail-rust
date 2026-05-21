//! Phase F.13 H12 — Tomita-GLR Dispatch-Cohort Sharing
//!
//! Stage 1.5 (2026-05-21): ambiguity fanout. Multi-packing Symbols
//! (sub-parses with > 1 alternative Packing) accumulate one
//! `WorkerSnapshot` per sibling worker pop. End-of-step revive emits
//! one cohort cursor per `(paused_member, snapshot)` pair so the
//! cohort frontier matches the per-cursor baseline's multi-derivation
//! shape. Downstream `merge_equivalent_cursors` collapses identical
//! ConfigKeys; ambiguity-distinguishing weights survive.
//!
//! Mathematical foundation
//! =======================
//!
//! For cohort member `M` and workers `W₁…Wₙ` at the same DispatchKey:
//!
//! - `engine.step(CrossCatDelegate{S, B}, pos=P)` is pure of cursor
//!   state (engine_impl.rs:1387-1394). All cohort members produce the
//!   SAME sub-parse outputs in terms of SppfId and hi_pos.
//! - SPPF Symbol-dedup at `(nt, lo, hi)` guarantees `Wᵢ_snap.symbol_id`
//!   is identical across all workers (intern_symbol at sppf.rs:511-525).
//! - SPPF Packing-dedup at `(rule_idx, children)` gives each `Wᵢ` a
//!   distinct Packing under the shared Symbol. `link_packing_to_symbol`
//!   ⊕-aggregates Packing weights into Symbol's `weight_sum`.
//! - For multi-packing Symbols, the per-cursor baseline produces N
//!   cursors at end-of-sub-parse, each with its OWN
//!   `pending_packing_weight` and cumulative `weight`. Stage 1.5
//!   captures one `WorkerSnapshot` per cohort revival; revive emits
//!   one revived cursor per snapshot.
//!
//! Per-stage lifecycle
//! ===================
//!
//! 1.5.0: schema only — `worker_snapshots: Vec<WorkerSnapshot>` per
//!        Resolved (length always 1). Behavior identical to Stage 1.3.1.
//! 1.5.1: end-of-step drain — replace inline revive in
//!        cursor_gss_pop_via_edge with a deferred drain at end of
//!        step_fanout (still single-snapshot per drain).
//! 1.5.2: multi-snapshot fanout — accumulate snapshots from sibling
//!        workers within the same step; drain emits paused × snapshots.
//! 1.5.3: InflightCollision pause enabled — full H12 active.

use crate::automata::semiring::SemiringRef;
use crate::sppf::SppfId;
use crate::wpda_runtime::WpdaState;

/// Cache key for cross-cat-projection dispatch sites. Mirrors the
/// payload of `WpdaState::CrossCatDelegate { source_src_idx,
/// inner_cur_bp }` together with the dispatch position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DispatchKey {
    pub pos: u32,
    pub source_src_idx: u16,
    pub inner_cur_bp: u8,
}

impl DispatchKey {
    #[inline(always)]
    pub fn new(pos: usize, source_src_idx: u16, inner_cur_bp: u8) -> Self {
        DispatchKey {
            pos: pos as u32,
            source_src_idx,
            inner_cur_bp,
        }
    }
}

/// Phase F.13 H12 Stage 1.5 (2026-05-21): per-packing worker snapshot.
/// Each sibling worker that pops a CrossCatProjection edge contributes
/// one snapshot. Multi-packing Symbols accumulate N snapshots before
/// end-of-step drain produces N revived cursors per paused cohort
/// member.
#[derive(Clone)]
pub struct WorkerSnapshot<W: SemiringRef> {
    /// Worker's `inner_state` at the moment it emitted the Pop action.
    /// Cohort revive sets `cursor.inner_state = worker_inner_state` so
    /// the next walker step re-emits the equivalent Pop.
    pub worker_inner_state: WpdaState,
    /// Worker's `last_action_output_cat` at pop. F.3b read at
    /// `apply_pop_body_to_cursor:9651` consumes this; cohort revive
    /// must inherit identically.
    pub worker_last_action_output_cat: Option<u16>,
    /// Worker's `pending_packing_weight` at pop. THIS IS THE
    /// PER-PACKING WEIGHT CONTRIBUTION — derived from the worker's
    /// path through the sub-parse and the per-Fork-arm branch weights.
    /// Stage 1.5 multiplies cohort member's `weight_at_dispatch` by
    /// THIS to compute revived cursor's weight (NOT the SPPF Symbol's
    /// aggregate weight_sum — that's the ⊕ over ALL packings, which
    /// would lose per-packing distinction).
    pub worker_pending_packing_weight: W,
    /// Worker's cumulative `weight` at pop. Diagnostic only; revive
    /// computes weight from `weight_at_dispatch × worker_pending_packing_weight`.
    pub worker_weight: W,
}

impl<W: SemiringRef> std::fmt::Debug for WorkerSnapshot<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorkerSnapshot")
            .field("inner_state", &self.worker_inner_state)
            .field("lao_cat", &self.worker_last_action_output_cat)
            .finish()
    }
}

/// State of a dispatch-cache entry.
pub enum DispatchCacheEntry<W: SemiringRef> {
    /// First cursor's sub-parse is in flight. Subsequent cohort members
    /// register here as paused; they revive at end-of-step drain.
    InFlight {
        cohort_size: u32,
        pending_cohort: Vec<CohortMember<W>>,
        /// Stage 1.5: worker snapshots accumulated by every sibling
        /// worker pop at this key during the SAME step_fanout
        /// iteration. The FIRST entry corresponds to the worker that
        /// triggered the InFlight→Resolved transition; later sibling
        /// workers append while we're still in the same step.
        worker_snapshots: Vec<WorkerSnapshot<W>>,
    },
    /// Sub-parse complete. Subsequent cursors that hit this key
    /// synthesize a resumed child per snapshot (multi-packing case
    /// produces N revived cursors).
    Resolved {
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        /// Stage 1.5: ALL worker snapshots, one per packing. For
        /// single-packing sub-parses this Vec has length 1 (collapses
        /// to Stage 1.3.1 behavior).
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        /// Stage 1.5: paused cohort members. PERSISTENT across drains
        /// — multi-packing requires re-reviving members against
        /// later-arriving snapshots from sibling workers that pop in
        /// LATER step_fanout iterations.
        pending_cohort: Vec<CohortMember<W>>,
        /// Stage 1.5: number of snapshots already used for revival
        /// (across past drains). At each end-of-step drain, snapshots
        /// `[snapshots_drained..]` are NEW since last drain — revive
        /// every paused member against each new snapshot.
        snapshots_drained: usize,
    },
    Failed,
}

impl<W: SemiringRef> std::fmt::Debug for DispatchCacheEntry<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DispatchCacheEntry::InFlight {
                cohort_size,
                pending_cohort,
                worker_snapshots,
            } => f
                .debug_struct("InFlight")
                .field("cohort_size", cohort_size)
                .field("pending_cohort_len", &pending_cohort.len())
                .field("worker_snapshots_len", &worker_snapshots.len())
                .finish(),
            DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                worker_snapshots,
                pending_cohort,
                snapshots_drained,
                ..
            } => f
                .debug_struct("Resolved")
                .field("symbol_id", symbol_id)
                .field("hi_pos", hi_pos)
                .field("worker_snapshots_len", &worker_snapshots.len())
                .field("pending_cohort_len", &pending_cohort.len())
                .field("snapshots_drained", snapshots_drained)
                .finish(),
            DispatchCacheEntry::Failed => f.write_str("Failed"),
        }
    }
}

/// A cohort member is a cursor that reached a `DispatchKey` while it
/// was `InFlight`.
pub struct CohortMember<W: SemiringRef> {
    pub return_frame: crate::wpda_walker::BranchCursor<W>,
    pub weight_at_dispatch: W,
}

impl<W: SemiringRef> Clone for CohortMember<W> {
    fn clone(&self) -> Self {
        CohortMember {
            return_frame: self.return_frame.clone(),
            weight_at_dispatch: self.weight_at_dispatch.clone(),
        }
    }
}

impl<W: SemiringRef> std::fmt::Debug for CohortMember<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CohortMember").finish()
    }
}

/// Walker-global cohort cache.
pub struct DispatchCohortCache<W: SemiringRef> {
    pub entries: rustc_hash::FxHashMap<DispatchKey, DispatchCacheEntry<W>>,
    pub registrations_total: u64,
    pub inflight_collisions_total: u64,
    pub resolved_hits_total: u64,
    pub failed_hits_total: u64,
    pub resolved_total: u64,
    pub failed_total: u64,
    pub snapshot_appends_total: u64,
}

impl<W: SemiringRef> DispatchCohortCache<W> {
    #[inline(always)]
    pub fn new() -> Self {
        DispatchCohortCache {
            entries: rustc_hash::FxHashMap::default(),
            registrations_total: 0,
            inflight_collisions_total: 0,
            resolved_hits_total: 0,
            failed_hits_total: 0,
            resolved_total: 0,
            failed_total: 0,
            snapshot_appends_total: 0,
        }
    }

    #[inline(always)]
    pub fn clear(&mut self) {
        self.entries.clear();
        self.registrations_total = 0;
        self.inflight_collisions_total = 0;
        self.resolved_hits_total = 0;
        self.failed_hits_total = 0;
        self.resolved_total = 0;
        self.failed_total = 0;
        self.snapshot_appends_total = 0;
    }

    /// Phase F.13 H12 Stage 1.5 — register a cross-cat-projection
    /// dispatch. Returns the outcome (ResolvedHit clones snapshots).
    pub fn register(&mut self, key: DispatchKey) -> RegisterOutcome<W> {
        self.registrations_total += 1;
        match self.entries.get_mut(&key) {
            None => {
                self.entries.insert(
                    key,
                    DispatchCacheEntry::InFlight {
                        cohort_size: 1,
                        pending_cohort: Vec::new(),
                        worker_snapshots: Vec::new(),
                    },
                );
                RegisterOutcome::WorkerInserted
            }
            Some(DispatchCacheEntry::InFlight { cohort_size, .. }) => {
                *cohort_size += 1;
                self.inflight_collisions_total += 1;
                RegisterOutcome::InflightCollision
            }
            Some(DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                ..
            }) => {
                self.resolved_hits_total += 1;
                RegisterOutcome::ResolvedHit {
                    symbol_id: *symbol_id,
                    hi_pos: *hi_pos,
                    pos_at_dispatch: *pos_at_dispatch,
                    worker_snapshots: worker_snapshots.clone(),
                }
            }
            Some(DispatchCacheEntry::Failed) => {
                self.failed_hits_total += 1;
                RegisterOutcome::FailedHit
            }
        }
    }

    /// Phase F.13 H12 Stage 1.5 — resolve. On the first sibling
    /// worker's pop: transition InFlight → Resolved with the worker's
    /// snapshot; paused cohort members move into Resolved's
    /// pending_cohort, awaiting end-of-step drain. On subsequent
    /// sibling worker pops: append snapshot to Resolved (so drain
    /// fans out the paused members per snapshot).
    pub fn resolve(
        &mut self,
        key: DispatchKey,
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        snap: WorkerSnapshot<W>,
    ) -> ResolveOutcome {
        let entry = match self.entries.get_mut(&key) {
            Some(e) => e,
            None => return ResolveOutcome::NoOp,
        };
        match entry {
            DispatchCacheEntry::InFlight {
                pending_cohort,
                worker_snapshots,
                ..
            } => {
                let drained_pending = std::mem::take(pending_cohort);
                let mut snapshots = std::mem::take(worker_snapshots);
                snapshots.push(snap);
                *entry = DispatchCacheEntry::Resolved {
                    symbol_id,
                    hi_pos,
                    pos_at_dispatch,
                    worker_snapshots: snapshots,
                    pending_cohort: drained_pending,
                    snapshots_drained: 0,
                };
                self.resolved_total += 1;
                ResolveOutcome::FirstResolve
            }
            DispatchCacheEntry::Resolved { worker_snapshots, .. } => {
                // Memory cap: refuse further snapshots beyond cap.
                // Pathological grammars with > 8 packings per Symbol
                // fall through to per-cursor for the overflow workers.
                const MAX_WORKER_SNAPSHOTS_PER_KEY: usize = 8;
                if worker_snapshots.len() < MAX_WORKER_SNAPSHOTS_PER_KEY {
                    worker_snapshots.push(snap);
                    self.snapshot_appends_total += 1;
                }
                ResolveOutcome::SnapshotAppended
            }
            DispatchCacheEntry::Failed => ResolveOutcome::NoOp,
        }
    }

    /// Phase F.13 H12 Stage 1.5 — end-of-step drain.
    ///
    /// Memory-bounded semantics: TAKES the pending_cohort members
    /// (via mem::take), NOT clone. This caps total memory at
    /// `pending_cohort.len() × snapshots.len()` per drain — strictly
    /// linear in the cap below. Cross-step snapshot arrivals are
    /// CAUGHT only at the next drain that has unconsumed members
    /// (typically none after the first), so multi-packing fanout
    /// across step boundaries is sacrificed for memory boundedness.
    ///
    /// The bounded-loss is acceptable because:
    /// - Single-step multi-packing (all sibling workers pop in the
    ///   same step) is FULLY captured by the first drain's
    ///   snapshots Vec, which the caller iterates over for fanout.
    /// - Cross-step multi-packing degrades to per-cursor semantics
    ///   for paused members (ResolvedHit register-time synthesis
    ///   still catches subsequent register hits with the full
    ///   snapshots Vec).
    #[allow(clippy::type_complexity)]
    pub fn take_pending_for_drain(
        &mut self,
        key: &DispatchKey,
    ) -> Option<(SppfId, u32, u32, Vec<WorkerSnapshot<W>>, Vec<CohortMember<W>>)> {
        let entry = self.entries.get_mut(key)?;
        match entry {
            DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                pending_cohort,
                snapshots_drained,
            } => {
                if pending_cohort.is_empty() {
                    return None;
                }
                let snaps: Vec<WorkerSnapshot<W>> =
                    worker_snapshots.clone();
                *snapshots_drained = worker_snapshots.len();
                let members = std::mem::take(pending_cohort);
                Some((
                    *symbol_id,
                    *hi_pos,
                    *pos_at_dispatch,
                    snaps,
                    members,
                ))
            }
            _ => None,
        }
    }

    /// Phase F.13 H12 Stage 1.5 — append a cohort member to the
    /// InFlight entry's pending list. Returns false if the entry has
    /// already transitioned past InFlight (race-safe; caller should
    /// fall through to worker allocation).
    ///
    /// Memory-bounded: refuses to add a member once
    /// `pending_cohort.len() >= MAX_PENDING_COHORT_PER_KEY`. The
    /// caller falls through to per-cursor sub-parse (no correctness
    /// loss; just no sharing for the overflow members).
    pub fn pause_cohort_member(
        &mut self,
        key: DispatchKey,
        member: CohortMember<W>,
    ) -> bool {
        const MAX_PENDING_COHORT_PER_KEY: usize = 16;
        match self.entries.get_mut(&key) {
            Some(DispatchCacheEntry::InFlight { pending_cohort, .. })
                if pending_cohort.len() < MAX_PENDING_COHORT_PER_KEY =>
            {
                pending_cohort.push(member);
                true
            }
            Some(DispatchCacheEntry::Resolved { pending_cohort, .. })
                if pending_cohort.len() < MAX_PENDING_COHORT_PER_KEY =>
            {
                pending_cohort.push(member);
                true
            }
            _ => false,
        }
    }

    /// Transition InFlight → Failed (sub-parse drop without a usable
    /// SPPF symbol). Reserved for Stage 1.5+.
    #[allow(dead_code)]
    pub fn fail(&mut self, key: DispatchKey) {
        if let Some(entry @ DispatchCacheEntry::InFlight { .. }) =
            self.entries.get_mut(&key)
        {
            *entry = DispatchCacheEntry::Failed;
            self.failed_total += 1;
        }
    }

    pub fn write_summary(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let collisions_ratio = if self.registrations_total > 0 {
            (self.inflight_collisions_total as f64) * 100.0
                / (self.registrations_total as f64)
        } else {
            0.0
        };
        writeln!(f, "═══ DISPATCH-COHORT CACHE STATS ═══")?;
        writeln!(
            f,
            "  registrations_total={}  inflight_collisions={} ({:.1}%)  \
             resolved_hits={}  failed_hits={}",
            self.registrations_total,
            self.inflight_collisions_total,
            collisions_ratio,
            self.resolved_hits_total,
            self.failed_hits_total,
        )?;
        writeln!(
            f,
            "  resolved_transitions={}  snapshot_appends={}  failed_transitions={}  cache_entries={}",
            self.resolved_total,
            self.snapshot_appends_total,
            self.failed_total,
            self.entries.len(),
        )?;
        Ok(())
    }
}

impl<W: SemiringRef> Default for DispatchCohortCache<W> {
    fn default() -> Self {
        Self::new()
    }
}

/// Outcome of a `register` call.
pub enum RegisterOutcome<W: SemiringRef> {
    WorkerInserted,
    InflightCollision,
    ResolvedHit {
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
    },
    FailedHit,
}

/// Outcome of a `resolve` call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolveOutcome {
    NoOp,
    FirstResolve,
    SnapshotAppended,
}
