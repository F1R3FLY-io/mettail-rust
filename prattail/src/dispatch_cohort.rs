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
///
/// `DispatchKey` is used as the FxHashMap key for the
/// `DispatchCohortCache::entries` lookup — it includes `pos` to
/// distinguish dispatch sites at different input positions (so the
/// cache correctly identifies in-flight dispatches per chain step).
///
/// **COQ-S1 (2026-05-27)**: `DispatchKey` is no longer used as a
/// `ConfigKey` equality discriminator — the proposed Cohort Origin
/// Quotient (`prattail/docs/design/plans/cohort-origin-quotient-coq.md`)
/// shows the `pos` axis prevents cursor merging across chain depths,
/// causing super-linear scaling. ConfigKey now uses
/// [`EquivKey`] instead, obtained via [`DispatchKey::equiv`]. The
/// cache itself still keys on full DispatchKey.
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

    /// **COQ-S1 (2026-05-27)**: project to the position-independent
    /// equivalence class for cohort-merge purposes. Two DispatchKeys
    /// produced at different chain depths but for the same
    /// `(source_src_idx, inner_cur_bp)` pair are observationally
    /// equivalent post-revive (engine.step is pure of cursor state at
    /// the dispatch site — same EquivKey ⇒ same action).
    ///
    /// Empirical chain_50 LEFT-assoc: 300 distinct DispatchKeys collapse
    /// to 6 distinct EquivKeys (50× collision rate). See COQ-S0
    /// instrumentation in walker_stats.rs.
    #[inline(always)]
    pub fn equiv(&self) -> EquivKey {
        EquivKey {
            source_src_idx: self.source_src_idx,
            inner_cur_bp: self.inner_cur_bp,
        }
    }
}

/// **COQ-S1 (2026-05-27)**: position-independent quotient of
/// [`DispatchKey`] for the cohort-merge equivalence relation. Drops
/// `pos`; retains the two grammar-determined axes.
///
/// Used as the `ConfigKey.cohort_origin` discriminator so cohort-revived
/// cursors at different chain depths can merge when they share the same
/// `(source_src_idx, inner_cur_bp)` dispatch site. This is the structural
/// fix for the chain workload's O(N²) apply_action scaling — the per-step
/// cohort discriminator was bounded by `|DispatchKey|` (= O(N) growth with
/// chain length), now bounded by `|EquivKey|` (= O(1), grammar-determined).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EquivKey {
    pub source_src_idx: u16,
    pub inner_cur_bp: u8,
}

impl EquivKey {
    #[inline(always)]
    pub fn new(source_src_idx: u16, inner_cur_bp: u8) -> Self {
        EquivKey {
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
    /// Worker's `pending_packing_weight` at pop. Cohort revive inherits
    /// this so downstream emit_fire_action behavior matches.
    pub worker_pending_packing_weight: W,
    /// Worker's cumulative `weight` at pop time. With
    /// `worker_pre_dispatch_weight`, revive computes per-packing weight
    /// delta = post - pre (tropical primary subtraction).
    pub worker_weight: W,
    /// Phase F.13 H12 Stage 1.5.3 (2026-05-21): worker's cumulative
    /// `weight` at register time (BEFORE the sub-parse started).
    /// Captured per snapshot so revive can compute per-packing weight
    /// delta = `tropical_primary_delta(worker_pre, worker_post)` —
    /// the additive primary cost of the sub-parse path through
    /// THIS packing. Replaces Stage 1.5.2's symbol_weight_sum
    /// aggregate (which lost per-packing distinction and broke
    /// `-3!`-style multi-packing tests).
    pub worker_pre_dispatch_weight: W,
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
        /// Stage 1.5: worker snapshots accumulated by every sibling
        /// worker pop at this key during the SAME step_fanout
        /// iteration. The FIRST entry corresponds to the worker that
        /// triggered the InFlight→Resolved transition; later sibling
        /// workers append while we're still in the same step.
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        /// Phase F.13 H12 Stage 1.5.3 (2026-05-21): the root worker's
        /// pre-dispatch weight (= parent.weight × branch.weight at
        /// register time). Internal Fork sub-cursors of this worker
        /// inherit this; ALL snapshots derived from this dispatch
        /// share the same worker_pre_dispatch_weight.
        worker_pre_dispatch_weight: W,
        /// Phase F.13 Stage L2c (2026-05-25): shared `~_obs`-invariant
        /// shell across all cohort members at this dispatch key.
        /// Constructed at first pause_cohort_member call from the
        /// pausing member's return_frame; subsequent pauses share via
        /// Arc::clone (O(1)). Sole representation since L2c removed
        /// the legacy `pending_cohort: Vec<CohortMember>` field that
        /// L2a/L2b had alongside (the mirror-write doubled memory and
        /// caused chain_1000 to explode to 9 GB in L2b).
        cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
        /// Phase F.13 Stage L2c (2026-05-25): per-member divergence
        /// state. Sole representation; `take_pending_for_drain`
        /// materializes a `CohortMember<W>` per state via
        /// `crate::cohort_lazy::materialize_branch_cursor` at drain
        /// time.
        pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
        /// Phase F.13 chain_10000 Exp 9 / Approach P Substage 1.a
        /// (2026-05-26): realize-time cohort fanout. Eligible cohort
        /// pauses push a `CohortContinuation` here AND (S1.b dual-write)
        /// also build a `CohortMemberState` above. S1.d makes this
        /// the sole representation for eligible sites — `pending_members`
        /// keeps the path for ineligible cohort sites. Drained at EOI
        /// by `install_cohort_continuations` (S1.c) and interned as
        /// outer-rule packings via `sppf.intern_packing`. Hard-capped
        /// at `MAX_DEFERRED_PER_KEY = 64` (S1.e raises to 256).
        deferred_continuations: Vec<crate::cohort_continuation::CohortContinuation<W>>,
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
        /// Stage 1.5: number of snapshots already used for revival
        /// (across past drains). At each end-of-step drain, snapshots
        /// `[snapshots_drained..]` are NEW since last drain — revive
        /// every paused member against each new snapshot.
        snapshots_drained: usize,
        /// Phase F.13 H12 Stage 1.5.3 (2026-05-21): the root worker's
        /// pre-dispatch weight, preserved through the InFlight→Resolved
        /// transition. Used by `read_worker_pre()` for cohort revive
        /// weight delta computation.
        worker_pre_dispatch_weight: W,
        /// Phase F.13 Stage L2c (2026-05-25): see InFlight variant.
        /// Transferred from InFlight when the entry transitions.
        cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
        /// Phase F.13 Stage L2c (2026-05-25): per-member divergence
        /// state. Sole representation. PERSISTENT across drains for
        /// multi-packing fanout.
        pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
        /// Phase F.13 chain_10000 Exp 9 / Approach P Substage 1.a
        /// (2026-05-26): deferred continuations transferred verbatim
        /// from `InFlight` at resolve time. PERSISTENT across drains
        /// for multi-packing fanout. Drained at EOI by
        /// `install_cohort_continuations` (S1.c).
        deferred_continuations: Vec<crate::cohort_continuation::CohortContinuation<W>>,
    },
    Failed,
}

impl<W: SemiringRef> std::fmt::Debug for DispatchCacheEntry<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DispatchCacheEntry::InFlight {
                cohort_size,
                worker_snapshots,
                worker_pre_dispatch_weight: _,
                cohort_shell: _,
                pending_members,
                deferred_continuations,
            } => f
                .debug_struct("InFlight")
                .field("cohort_size", cohort_size)
                .field("pending_members_len", &pending_members.len())
                .field("worker_snapshots_len", &worker_snapshots.len())
                .field(
                    "deferred_continuations_len",
                    &deferred_continuations.len(),
                )
                .finish(),
            DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                worker_snapshots,
                pending_members,
                snapshots_drained,
                ..
            } => f
                .debug_struct("Resolved")
                .field("symbol_id", symbol_id)
                .field("hi_pos", hi_pos)
                .field("worker_snapshots_len", &worker_snapshots.len())
                .field("pending_members_len", &pending_members.len())
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
    /// Phase F.13 H12 Stage 1.5.3R-d (2026-05-21): count of cohort
    /// cursors emitted via revive (from either pause→drain or
    /// register-time ResolvedHit). Tracks H12 reuse efficacy.
    pub cohort_cursors_emitted_total: u64,
    /// Phase F.13 H12 Stage 1.5.3R-d (2026-05-21): count of cohort
    /// cursors that graduated (cohort_origin cleared via G2 rule).
    /// Compared to emitted_total tells us how many cohorts survive
    /// past their dispatch's return frame.
    pub cohort_cursors_graduated_total: u64,
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
            cohort_cursors_emitted_total: 0,
            cohort_cursors_graduated_total: 0,
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
        self.cohort_cursors_emitted_total = 0;
        self.cohort_cursors_graduated_total = 0;
    }

    /// Phase F.13 H12 Stage 1.5 — register a cross-cat-projection
    /// dispatch. Returns the outcome (ResolvedHit clones snapshots).
    ///
    /// Stage 1.5.3: `worker_pre_weight` is the root worker's
    /// cumulative weight at the moment of register (= parent.weight ×
    /// branch.weight at the Fork-arm allocation site). Stashed on the
    /// InFlight entry for later cohort revive weight delta computation.
    pub fn register(
        &mut self,
        key: DispatchKey,
        worker_pre_weight: W,
    ) -> RegisterOutcome<W> {
        self.registrations_total += 1;
        match self.entries.get_mut(&key) {
            None => {
                self.entries.insert(
                    key,
                    DispatchCacheEntry::InFlight {
                        cohort_size: 1,
                        worker_snapshots: Vec::new(),
                        worker_pre_dispatch_weight: worker_pre_weight,
                        cohort_shell: None,
                        pending_members: Vec::new(),
                        // Phase F.13 chain_10000 Exp 9 S1.a (2026-05-26).
                        deferred_continuations: Vec::new(),
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
                worker_snapshots,
                worker_pre_dispatch_weight,
                cohort_shell,
                pending_members,
                deferred_continuations,
                ..
            } => {
                let mut snapshots = std::mem::take(worker_snapshots);
                snapshots.push(snap);
                let preserved_pre = worker_pre_dispatch_weight.clone();
                let preserved_shell = cohort_shell.take();
                let preserved_members = std::mem::take(pending_members);
                // Phase F.13 chain_10000 Exp 9 S1.a (2026-05-26):
                // transfer deferred continuations through the
                // InFlight → Resolved transition verbatim.
                let preserved_continuations =
                    std::mem::take(deferred_continuations);
                *entry = DispatchCacheEntry::Resolved {
                    symbol_id,
                    hi_pos,
                    pos_at_dispatch,
                    worker_snapshots: snapshots,
                    snapshots_drained: 0,
                    worker_pre_dispatch_weight: preserved_pre,
                    cohort_shell: preserved_shell,
                    pending_members: preserved_members,
                    deferred_continuations: preserved_continuations,
                };
                self.resolved_total += 1;
                ResolveOutcome::FirstResolve
            }
            DispatchCacheEntry::Resolved { worker_snapshots, .. } => {
                // Memory cap: refuse further snapshots beyond cap.
                // Pathological grammars with > 8 packings per Symbol
                // fall through to per-cursor for the overflow workers.
                //
                // 2026-05-25: experimental bump to 64 caused chain_1000
                // memory explosion to 4.5 GB RSS at 28 s wall-time
                // (vs ~5 MB baseline). The cap is a hard memory bound
                // that must be paired with the lazy CohortFrame
                // representation (Stage L6 of
                // `docs/design/plans/cohort-lazy-materialization.md`)
                // before it can be safely raised. Reverted to 4.
                //
                // Phase F.13 Stage L6 (2026-05-25): cap raised from 4
                // to 16 (4× of original). Empirically the cap=256
                // experiment caused chain_10000 to grow past 22 GB
                // RSS at 2:54 (close to baseline 24 GB OOM ceiling).
                // The L3+L4 per-cursor savings (~50× via lazy form +
                // Arc-shared cycle defense) don't fully amortize a
                // ~4096× cap-product increase (256²) — concrete
                // revives still happen for ObsDivergent steps and
                // pay the materialize cost. cap=16 (16²=256 cap
                // product, 16× original) should fit in ~6× pre-L3
                // baseline = ~150 MB at chain_1000.
                const MAX_WORKER_SNAPSHOTS_PER_KEY: usize = 16;
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
    /// Phase F.13 H12 Stage 1.5.1 — drain ONLY the NEW snapshots
    /// since the last drain, keeping pending_cohort PERSISTENT for
    /// cross-step multi-packing fanout. Members are cloned per drain
    /// (NOT taken), so subsequent worker snapshots in later steps
    /// can also revive against the same cohort.
    ///
    /// Memory bound: with `MAX_PENDING_COHORT_PER_KEY=4` and
    /// `MAX_WORKER_SNAPSHOTS_PER_KEY=4`, max total revivals per key
    /// per parse = 4 × 4 = 16. Across N keys, max revivals = 16N.
    /// Each clone is O(cursor-depth); total memory bounded.
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
                snapshots_drained,
                worker_pre_dispatch_weight: _,
                cohort_shell,
                pending_members,
                deferred_continuations: _,
            } => {
                // Phase F.13 Stage L2c (2026-05-25): drain reads from
                // the lazy form (`cohort_shell` + `pending_members`).
                // Materializes one `CohortMember` per state at drain
                // time. The legacy `pending_cohort: Vec<CohortMember>`
                // field has been removed; the lazy form is the sole
                // representation, so no mirror-write doubles memory
                // (L2b's failure mode).
                //
                // The drain output (`Vec<CohortMember>`) is identical
                // in shape to today's, so the walker code's revive
                // loop is unchanged. The materialization rebuilds full
                // BranchCursors; net memory is parity with today
                // (modulo the small Arc<CohortShell> overhead).
                // Memory benefit from full lazy stepping lands at L3
                // (the ObsInvariant fast path skips materialization
                // for shell-uniform steps).
                if pending_members.is_empty() {
                    return None;
                }
                if *snapshots_drained >= worker_snapshots.len() {
                    return None;
                }
                let new_snaps: Vec<WorkerSnapshot<W>> = worker_snapshots
                    [*snapshots_drained..]
                    .to_vec();
                *snapshots_drained = worker_snapshots.len();
                let shell = cohort_shell.as_ref().expect(
                    "L2c invariant: cohort_shell is Some whenever pending_members is non-empty",
                );
                let materialized: Vec<CohortMember<W>> = pending_members
                    .iter()
                    .map(|state| CohortMember {
                        return_frame: crate::cohort_lazy::materialize_branch_cursor(
                            shell, state,
                        ),
                        weight_at_dispatch: state.weight_at_dispatch.clone(),
                    })
                    .collect();
                Some((
                    *symbol_id,
                    *hi_pos,
                    *pos_at_dispatch,
                    new_snaps,
                    materialized,
                ))
            }
            _ => None,
        }
    }

    /// Phase F.13 H12 Stage 1.5.3 — read the cached worker
    /// pre-dispatch weight for a key. Returns None if the key has no
    /// entry. Used by the walker's resolve site to populate
    /// `WorkerSnapshot::worker_pre_dispatch_weight`.
    pub fn read_worker_pre(&self, key: &DispatchKey) -> Option<W> {
        match self.entries.get(key)? {
            DispatchCacheEntry::InFlight {
                worker_pre_dispatch_weight,
                ..
            } => Some(worker_pre_dispatch_weight.clone()),
            DispatchCacheEntry::Resolved {
                worker_pre_dispatch_weight,
                ..
            } => Some(worker_pre_dispatch_weight.clone()),
            DispatchCacheEntry::Failed => None,
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
        // Phase F.13 Stage L6 (2026-05-25): cap raised from 4 to 16
        // (matching MAX_WORKER_SNAPSHOTS_PER_KEY). cap=256 empirically
        // rejected — chain_10000 grew past 22 GB at 2:54 (near
        // baseline 24 GB OOM). The L3+L4 per-cursor savings amortize
        // partly but not enough to fully offset the cap-product blowup.
        const MAX_PENDING_COHORT_PER_KEY: usize = 16;
        match self.entries.get_mut(&key) {
            Some(DispatchCacheEntry::InFlight { cohort_shell, pending_members, .. })
                if pending_members.len() < MAX_PENDING_COHORT_PER_KEY =>
            {
                // Phase F.13 Stage L2c (2026-05-25): sole representation
                // is the lazy form (`cohort_shell` + `pending_members`).
                // The legacy `pending_cohort: Vec<CohortMember>` field
                // was removed in this commit. `pause_cohort_member`
                // still takes a `CohortMember<W>` for API compatibility
                // (the walker's three call sites at
                // wpda_walker.rs:9499/9540/9562 construct one), but
                // immediately extracts the shell + state and discards
                // the full BranchCursor clone. Net memory benefit:
                // members no longer hold full `return_frame` clones in
                // the cache (~3.2 KB per member → ~64 B per state).
                if cohort_shell.is_none() {
                    *cohort_shell = Some(std::sync::Arc::new(
                        crate::cohort_lazy::CohortShell::from_branch_cursor(
                            &member.return_frame,
                            key.clone(),
                        ),
                    ));
                }
                pending_members.push(
                    crate::cohort_lazy::CohortMemberState::from_branch_cursor(
                        &member.return_frame,
                        member.weight_at_dispatch.clone(),
                    ),
                );
                // The `member: CohortMember<W>` parameter is consumed
                // and dropped here — the full BranchCursor inside is
                // released (only the small shell + state captures
                // survive).
                drop(member);
                true
            }
            Some(DispatchCacheEntry::Resolved { cohort_shell, pending_members, .. })
                if pending_members.len() < MAX_PENDING_COHORT_PER_KEY =>
            {
                if cohort_shell.is_none() {
                    *cohort_shell = Some(std::sync::Arc::new(
                        crate::cohort_lazy::CohortShell::from_branch_cursor(
                            &member.return_frame,
                            key.clone(),
                        ),
                    ));
                }
                pending_members.push(
                    crate::cohort_lazy::CohortMemberState::from_branch_cursor(
                        &member.return_frame,
                        member.weight_at_dispatch.clone(),
                    ),
                );
                drop(member);
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
        writeln!(
            f,
            "  cohort_cursors_emitted={}  cohort_cursors_graduated={}",
            self.cohort_cursors_emitted_total,
            self.cohort_cursors_graduated_total,
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
