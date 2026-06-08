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

/// Sig-B Blocker-2 (2026-05-31): is the `SIGB_CROSSWRAP` trace gate on?
/// Read from the environment exactly once (first call) and memoized. Off
/// by default — when unset, the cross-wrap drain path emits NO trace and
/// the walker never calls the drain (M2.0 inert; gauntlet byte-identical).
#[inline]
fn sigb_crosswrap_trace() -> bool {
    static GATE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *GATE.get_or_init(|| std::env::var_os("SIGB_CROSSWRAP").is_some())
}

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
    pub pos: usize,
    pub source_src_idx: u16,
    pub inner_cur_bp: u8,
    /// M4 (2026-05-30, re-landed): the WRAPPING rule's category +
    /// rule-within-category index (`branch.symbol.{category_src_idx,
    /// rule_index_in_category}` at the dispatch site). Distinct cross-cat
    /// WRAP injections that share `(pos, source, bp)` but wrap via DIFFERENT
    /// rules (e.g. `int(int(5,32),32)` schedules 4 distinct wrap rules
    /// `(0,0)/(1,1)/(6,1)/(7,34)` at the same `(pos, source=Proc, bp=0)`)
    /// previously COLLAPSED to one DispatchKey → all but one were
    /// `pause_cohort_member`'d and lost (the cast-family root cause). Adding
    /// the wrap discriminator un-conflates them so each distinct injection
    /// gets its own cache entry and reaches EOI.
    ///
    /// NOTE: this widens ONLY the cohort-CACHE key (this struct), NOT the
    /// cohort-MERGE equivalence key [`EquivKey`] (see [`Self::equiv`]), which
    /// stays `(source_src_idx, inner_cur_bp)` so the chain workload's
    /// O(1)-bounded ConfigKey.cohort_origin merge (and its memory ceiling)
    /// is provably untouched.
    pub wrap_cat: u16,
    pub wrap_rule: u16,
}

impl DispatchKey {
    #[inline(always)]
    pub fn new(
        pos: usize,
        source_src_idx: u16,
        inner_cur_bp: u8,
        wrap_cat: u16,
        wrap_rule: u16,
    ) -> Self {
        DispatchKey {
            pos,
            source_src_idx,
            inner_cur_bp,
            wrap_cat,
            wrap_rule,
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
    ///
    /// M4 (2026-05-30): DELIBERATELY drops `wrap_cat`/`wrap_rule` too — the
    /// merge quotient stays narrow `(source_src_idx, inner_cur_bp)` so the
    /// cohort-MERGE (chain O(N²) defense) is unaffected by the cache-key
    /// widening. Only the cohort CACHE keys on the wrap discriminator.
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
        EquivKey { source_src_idx, inner_cur_bp }
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
        hi_pos: usize,
        pos_at_dispatch: usize,
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
                .field("deferred_continuations_len", &deferred_continuations.len())
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

/// Sig-B Blocker-2 (2026-05-31, pgmcp experiment #9): one own-wrap-gated
/// cross-wrap body-splice job. Produced by
/// [`DispatchCohortCache::take_pending_for_drain_crosswrap`] for each
/// `(paused cohort member M of a sibling key `K_sib`, worker snapshot of the
/// RESOLVED sibling `R`)` pair that passes the §2 eligibility predicate.
///
/// The walker revives each job via the EXISTING
/// `revive_cohort_member_with_snapshot` (the same entrypoint the normal
/// same-wrap drain uses), passing `member` + the resolved `R`'s
/// `(symbol_id, hi_pos, pos_at_dispatch)` and the RESOLVED wrap
/// `(wrap_cat, wrap_rule)`. The member is the LIVE cast cursor that paused
/// under `K_pause(W1)` awaiting its body; the resolution it needs is the
/// OUTERMOST-wrap `R(W2)`'s full-body SPPF symbol. Splicing it re-pushes
/// `CategoryEntry(source)` so the member's next walker step fires its cast
/// action → `is_accepting_config` true.
///
/// **Soundness (§3c):** this only ADDS sound cursors; the eligibility is the
/// purely-structural §2 predicate (no count/weight/cap/threshold). The
/// member's own-wrap `K_sib` entry is NOT removed — its own worker may still
/// resolve its own span; the cross-wrap splice only ADDS the body it needs.
pub struct CrossWrapSpliceJob<W: SemiringRef> {
    /// The paused cohort member of `K_sib` (materialized from its lazy
    /// `CohortShell` + `CohortMemberState`), to be revived/spliced.
    pub member: CohortMember<W>,
    /// `R.symbol_id` — the resolved sibling's full-body SPPF symbol.
    pub symbol_id: SppfId,
    /// `R.hi_pos` — the resolved sibling's body end position.
    pub hi_pos: usize,
    /// `R.pos_at_dispatch` — the shared dispatch-site position
    /// (== `K_sib.pos` by the eligibility predicate).
    pub pos_at_dispatch: usize,
    /// Shared dispatch source category (== `resolved_key.source_src_idx`
    /// == `K_sib.source_src_idx`, since `equiv()` matches).
    pub source_src_idx: u16,
    /// Shared dispatch inner binding-power (== `resolved_key.inner_cur_bp`).
    pub inner_cur_bp: u8,
    /// The RESOLVED wrap's category (`resolved_key.wrap_cat`). The revived
    /// member carries the RESOLVED wrap so its re-pushed CrossCatProjection
    /// edge + `cohort_origin` reflect the body that completed it (§3b).
    pub wrap_cat: u16,
    /// The RESOLVED wrap's rule index (`resolved_key.wrap_rule`).
    pub wrap_rule: u16,
    /// One `R` worker snapshot. `revive_cohort_member_with_snapshot` reads
    /// `worker_inner_state` / `worker_last_action_output_cat` /
    /// `worker_pending_packing_weight` from this. One job is produced per
    /// (member × snapshot), mirroring the same-wrap drain's fanout.
    pub snap: WorkerSnapshot<W>,
    /// Sig-B Blocker-3 §2.4c (2026-06-01, pgmcp experiment #9): the
    /// SINGLE-hop coercion to interpose over `R.symbol_id` before the
    /// member's cast fires, as `Some((coercion_cat, coercion_rule))`, or
    /// `None` when `body_cat == tgt_cat` (direct splice — byte-identical to
    /// the forward Blocker-2 job, which always sets `None`). Set ONLY by
    /// `take_span_anchored_outer_cast` (the EOI/pre-Error span drain); the
    /// forward `take_pending_for_drain_crosswrap` ALWAYS sets `None` so its
    /// jobs are byte-identical to pre-Blocker-3.
    pub coercion: Option<(u16, u16)>,
}

impl<W: SemiringRef> std::fmt::Debug for CrossWrapSpliceJob<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CrossWrapSpliceJob")
            .field("symbol_id", &self.symbol_id)
            .field("hi_pos", &self.hi_pos)
            .field("pos_at_dispatch", &self.pos_at_dispatch)
            .field("source_src_idx", &self.source_src_idx)
            .field("inner_cur_bp", &self.inner_cur_bp)
            .field("wrap_cat", &self.wrap_cat)
            .field("wrap_rule", &self.wrap_rule)
            .finish()
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
    /// Cohort-revive-rework M0 (2026-05-29): cumulative count of paused
    /// cohort members orphaned on `InFlight` entries (worker never
    /// reached `Resolved`, so the end-of-step drain never fired). These
    /// are the cross-cat cursors silently lost per the
    /// `drive-suite-green-ledger.md` "⚑ Cross-cat cluster ROOT CAUSE".
    /// Tallied at EOI by `orphaned_pending_members_count` and revived by
    /// M1's `drain_orphaned_inflight_members`.
    pub inflight_orphan_members_total: u64,
    /// Cohort-revive-rework M0 (2026-05-29): cumulative count of paused
    /// cohort members orphaned on `Failed` entries. (At this milestone
    /// the `Failed` variant is unit-shaped and carries NO pending_members,
    /// so this is structurally always 0 until M2 stashes them; counted
    /// separately so the census can confirm M0's prediction that the
    /// loss is entirely in the `InFlight` branch.)
    pub failed_orphan_members_total: u64,
    /// Sig-B Blocker-2 (2026-05-31, pgmcp experiment #9): take-once
    /// idempotence set for `take_pending_for_drain_crosswrap`. Keyed by
    /// `(K_sib, R.symbol_id)` — the sibling key whose member was
    /// cross-wrap-spliced, paired with the resolved symbol that supplied
    /// the body. A repeated drain pass over the SAME `(K_sib, symbol)` is
    /// suppressed so a member is cross-revived AT MOST once per
    /// resolved-body symbol (R3: prevents the re-injection loop). The
    /// member's own-wrap entry is left intact, so this set — not entry
    /// removal — is the sole idempotence guard for the cross-wrap path.
    /// Cleared at the parse boundary by `clear`.
    pub crosswrap_drained: rustc_hash::FxHashSet<(DispatchKey, SppfId)>,
    /// Sig-B Blocker-2 (2026-05-31): cumulative count of cross-wrap
    /// body-splice jobs emitted (one per member × snapshot). Observability
    /// for experiment #9 — a non-zero count on a failing cross-cat test is
    /// the empirical signature that the body-splice fired.
    pub crosswrap_splices_total: u64,
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
            inflight_orphan_members_total: 0,
            failed_orphan_members_total: 0,
            // Sig-B Blocker-2 (2026-05-31): fresh idempotence set + counter.
            crosswrap_drained: rustc_hash::FxHashSet::default(),
            crosswrap_splices_total: 0,
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
        self.inflight_orphan_members_total = 0;
        self.failed_orphan_members_total = 0;
        // Sig-B Blocker-2 (2026-05-31): clear the cross-wrap idempotence
        // set + counter at the parse boundary. SPPF SymbolIds are
        // per-parse; a stale `(DispatchKey, SppfId)` from a prior parse
        // would be unsound to honor against a fresh SPPF arena.
        self.crosswrap_drained.clear();
        self.crosswrap_splices_total = 0;
    }

    /// Clear token/SPPF-dependent entry state after a live token-source
    /// mutation while preserving cumulative diagnostics. Unlike `clear`,
    /// this is not a parse-boundary reset.
    #[inline(always)]
    pub fn clear_entries_preserving_diagnostics(&mut self) {
        self.entries.clear();
        self.crosswrap_drained.clear();
    }

    /// Phase F.13 H12 Stage 1.5 — register a cross-cat-projection
    /// dispatch. Returns the outcome (ResolvedHit clones snapshots).
    ///
    /// Stage 1.5.3: `worker_pre_weight` is the root worker's
    /// cumulative weight at the moment of register (= parent.weight ×
    /// branch.weight at the Fork-arm allocation site). Stashed on the
    /// InFlight entry for later cohort revive weight delta computation.
    pub fn register(&mut self, key: DispatchKey, worker_pre_weight: W) -> RegisterOutcome<W> {
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
            },
            Some(DispatchCacheEntry::InFlight { cohort_size, .. }) => {
                *cohort_size += 1;
                self.inflight_collisions_total += 1;
                RegisterOutcome::InflightCollision
            },
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
            },
            Some(DispatchCacheEntry::Failed) => {
                self.failed_hits_total += 1;
                RegisterOutcome::FailedHit
            },
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
        hi_pos: usize,
        pos_at_dispatch: usize,
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
                let preserved_continuations = std::mem::take(deferred_continuations);
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
            },
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
            },
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
    ) -> Option<(SppfId, usize, usize, Vec<WorkerSnapshot<W>>, Vec<CohortMember<W>>)> {
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
                let new_snaps: Vec<WorkerSnapshot<W>> =
                    worker_snapshots[*snapshots_drained..].to_vec();
                *snapshots_drained = worker_snapshots.len();
                let shell = cohort_shell.as_ref().expect(
                    "L2c invariant: cohort_shell is Some whenever pending_members is non-empty",
                );
                let materialized: Vec<CohortMember<W>> = pending_members
                    .iter()
                    .map(|state| CohortMember {
                        return_frame: crate::cohort_lazy::materialize_branch_cursor(shell, state),
                        weight_at_dispatch: state.weight_at_dispatch.clone(),
                    })
                    .collect();
                Some((*symbol_id, *hi_pos, *pos_at_dispatch, new_snaps, materialized))
            },
            _ => None,
        }
    }

    /// Sig-B Blocker-2 (2026-05-31, pgmcp experiment #9): own-wrap-gated
    /// CROSS-WRAP body-splice drain. Companion to
    /// [`Self::take_pending_for_drain`] (the SAME-wrap drain).
    ///
    /// **Root cause it closes (§1).** A cross-cat cast member paused under
    /// `K_pause(W1)` (its own wrap), but the body it awaits — the whole
    /// chain — resolves under the OUTERMOST wrap `K_resolve(W2)` at the
    /// SAME dispatch site. The same-wrap drain keys on the FULL widened
    /// `K_resolve`, so it never reaches the `K_pause(W1)` member → the cast
    /// `BinderRule` is never spliced → `is_accepting_config` stays false →
    /// "no accepting branch ... `(`". `K_resolve.equiv() == K_pause.equiv()`
    /// but `K_resolve != K_pause`.
    ///
    /// **THE structural eligibility predicate (§2) — NO count/weight/cap.**
    /// Cross-revive a paused member `M` of sibling key `K_sib` from the
    /// `Resolved` sibling `R = entries[resolved_key]` iff ALL hold:
    /// 1. `K_sib.equiv() == resolved_key.equiv()`  (narrow READ — same
    ///    `(source_src_idx, inner_cur_bp)` dispatch equivalence class);
    /// 2. `K_sib != resolved_key`  (DISTINCT wrap — same-wrap is the normal
    ///    drain's job);
    /// 3. `K_sib.pos == R.pos_at_dispatch`  (dispatch-site identity);
    /// 4. `K_sib` is `InFlight` (its own wrap has NOT resolved) **OR**
    ///    `K_sib` is `Resolved` with `hi_pos < R.hi_pos` (it resolved a
    ///    strictly SHORTER inner span) — THE load-bearing own-wrap-
    ///    non-resolution gate.
    ///
    /// Clause 4 is what excludes the PARENS-INNER steal (§2): the inner
    /// `(-0.5<0.5)` SELF-RESOLVES at its OWN required `hi_pos` (== `R.hi_pos`),
    /// so `hi_pos < R.hi_pos` is FALSE → not eligible → no steal →
    /// `cross_cat_with_parens` STAYS GREEN. The GENUINE floats/chain case has
    /// the cast member's own wrap `InFlight` (or a shorter span) → eligible.
    ///
    /// **Only ADDS sound cursors (§3c).** `K_sib` is NOT removed (its own
    /// worker may still resolve its own span); we only ADD the body it needs.
    /// `resolved_key`'s EquivKey is READ-only; the cache stays full
    /// `DispatchKey` (R5). One job per `(member × non-terminal R snapshot)`.
    ///
    /// **Take-once idempotence (§3a / R3).** `crosswrap_drained` records
    /// `(K_sib, R.symbol_id)`; a repeated drain pass over the same pair is
    /// suppressed so a member is cross-revived at most once per resolved
    /// body symbol — no entry removal, no re-injection loop.
    #[allow(clippy::type_complexity)]
    pub fn take_pending_for_drain_crosswrap(
        &mut self,
        resolved_key: &DispatchKey,
    ) -> Vec<CrossWrapSpliceJob<W>> {
        // ── Read `R` (the resolved sibling). Require Resolved; clone the
        //    fields the jobs need so the subsequent sibling scan can borrow
        //    `self.entries` immutably without aliasing.
        let (r_symbol_id, r_hi_pos, r_pos_at_dispatch, r_snaps): (
            SppfId,
            usize,
            usize,
            Vec<WorkerSnapshot<W>>,
        ) = match self.entries.get(resolved_key) {
            Some(DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                ..
            }) => {
                // Filter terminal snapshots: a worker that ended in
                // Error/Accept terminal would not produce a revivable
                // cursor (mirrors the same-wrap drain's terminal filter at
                // the walker site). Empty snapshot set ⇒ nothing to splice.
                let live: Vec<WorkerSnapshot<W>> = worker_snapshots
                    .iter()
                    .filter(|s| !s.worker_inner_state.is_terminal())
                    .cloned()
                    .collect();
                if live.is_empty() {
                    return Vec::new();
                }
                (*symbol_id, *hi_pos, *pos_at_dispatch, live)
            },
            _ => return Vec::new(),
        };
        let r_equiv = resolved_key.equiv();

        // ── Scan siblings (immutable borrow). Collect, per eligible
        //    `K_sib`, its materialized members. `crosswrap_drained` is
        //    consulted to skip already-spliced `(K_sib, R.symbol_id)` pairs
        //    so we do not materialize members we would only discard.
        let mut eligible: Vec<(DispatchKey, Vec<CohortMember<W>>)> = Vec::new();
        for (k_sib, entry) in self.entries.iter() {
            // Clause 1 + 2 + 3: equiv match, distinct wrap, dispatch-site
            // identity (`K_sib.pos == R.pos_at_dispatch`).
            if k_sib == resolved_key {
                continue;
            }
            if k_sib.equiv() != r_equiv {
                continue;
            }
            if k_sib.pos != r_pos_at_dispatch {
                continue;
            }
            // Take-once: skip if this `(K_sib, R.symbol_id)` already spliced.
            if self
                .crosswrap_drained
                .contains(&(k_sib.clone(), r_symbol_id))
            {
                continue;
            }
            // Clause 4 + member materialization. Eligible iff own wrap is
            // InFlight (with members) OR Resolved with a STRICTLY shorter
            // span (with members). `R.hi_pos` is the full-body span; an own
            // resolution at `>= R.hi_pos` means the member already has (or
            // can get) its own body — not a cross-wrap orphan.
            let (shell_opt, states): (
                &Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
                &Vec<crate::cohort_lazy::CohortMemberState<W>>,
            ) = match entry {
                DispatchCacheEntry::InFlight { cohort_shell, pending_members, .. }
                    if !pending_members.is_empty() =>
                {
                    (cohort_shell, pending_members)
                },
                DispatchCacheEntry::Resolved {
                    hi_pos: sib_hi,
                    cohort_shell,
                    pending_members,
                    ..
                } if *sib_hi < r_hi_pos && !pending_members.is_empty() => {
                    (cohort_shell, pending_members)
                },
                // Clause-4 FAIL (or empty members). This is the EXCLUDED
                // branch — most importantly the PARENS-INNER steal: a
                // sibling that passed clauses 1-3 but is self-`Resolved` at
                // `hi_pos >= R.hi_pos` (it already has its own body). M2.0
                // GATE evidence: trace it so we can confirm parens2's inner
                // member is self-Resolved at EQUAL hi_pos (the discriminator).
                other => {
                    if sigb_crosswrap_trace() {
                        let (st, sib_hi_dbg, mem_dbg) = match other {
                            DispatchCacheEntry::InFlight { pending_members, .. } => {
                                ("InFlight(empty)", usize::MAX, pending_members.len())
                            },
                            DispatchCacheEntry::Resolved {
                                hi_pos: sh, pending_members, ..
                            } => ("Resolved(>=hi)", *sh, pending_members.len()),
                            DispatchCacheEntry::Failed => ("Failed", usize::MAX, 0),
                        };
                        eprintln!(
                            "[SIGB_CROSSWRAP] EXCLUDED K_sib={{pos:{},src:{},bp:{},wrap:({},{})}} \
                             state={} sib_hi={} members={} | clause4-fail vs R.hi_pos={} \
                             (parens-inner-steal guard)",
                            k_sib.pos,
                            k_sib.source_src_idx,
                            k_sib.inner_cur_bp,
                            k_sib.wrap_cat,
                            k_sib.wrap_rule,
                            st,
                            sib_hi_dbg,
                            mem_dbg,
                            r_hi_pos,
                        );
                    }
                    continue;
                },
            };
            let shell = match shell_opt {
                Some(s) => s,
                // Invariant: a non-empty pending_members implies Some(shell)
                // (pause_cohort_member always sets the shell first). Skip
                // defensively if somehow absent.
                None => continue,
            };
            let members: Vec<CohortMember<W>> = states
                .iter()
                .map(|state| CohortMember {
                    return_frame: crate::cohort_lazy::materialize_branch_cursor(shell, state),
                    weight_at_dispatch: state.weight_at_dispatch.clone(),
                })
                .collect();
            // M2.0 trace-checkpoint (§4): log the eligible (K_sib, R) pair's
            // predicate fields under the SIGB_CROSSWRAP env gate. Confirms
            // the discriminator empirically (floats/chain: K_sib InFlight /
            // shorter; parens2 inner: excluded because self-Resolved at
            // EQUAL hi_pos).
            if sigb_crosswrap_trace() {
                let sib_state = match entry {
                    DispatchCacheEntry::InFlight { .. } => "InFlight",
                    DispatchCacheEntry::Resolved { hi_pos: sh, .. } => {
                        if *sh < r_hi_pos {
                            "Resolved(shorter)"
                        } else {
                            "Resolved(>=)"
                        }
                    },
                    DispatchCacheEntry::Failed => "Failed",
                };
                eprintln!(
                    "[SIGB_CROSSWRAP] ELIGIBLE K_sib={{pos:{},src:{},bp:{},wrap:({},{})}} \
                     state={} members={} | R=resolved_key{{wrap:({},{})}} \
                     R.symbol_id={} R.hi_pos={} R.pos_at_dispatch={} equiv=({},{})",
                    k_sib.pos,
                    k_sib.source_src_idx,
                    k_sib.inner_cur_bp,
                    k_sib.wrap_cat,
                    k_sib.wrap_rule,
                    sib_state,
                    members.len(),
                    resolved_key.wrap_cat,
                    resolved_key.wrap_rule,
                    r_symbol_id,
                    r_hi_pos,
                    r_pos_at_dispatch,
                    r_equiv.source_src_idx,
                    r_equiv.inner_cur_bp,
                );
            }
            eligible.push((k_sib.clone(), members));
        }
        if eligible.is_empty() {
            return Vec::new();
        }

        // ── Build jobs (immutable borrow dropped). One job per
        //    (eligible K_sib × member × non-terminal R snapshot). Mark each
        //    `(K_sib, R.symbol_id)` drained so repeat passes are idempotent.
        let mut jobs: Vec<CrossWrapSpliceJob<W>> = Vec::with_capacity(
            eligible.iter().map(|(_, m)| m.len()).sum::<usize>() * r_snaps.len(),
        );
        for (k_sib, members) in eligible {
            self.crosswrap_drained.insert((k_sib.clone(), r_symbol_id));
            for member in members {
                for snap in &r_snaps {
                    jobs.push(CrossWrapSpliceJob {
                        member: member.clone(),
                        symbol_id: r_symbol_id,
                        hi_pos: r_hi_pos,
                        pos_at_dispatch: r_pos_at_dispatch,
                        // equiv() match ⇒ source_src_idx + inner_cur_bp are
                        // identical between K_sib and resolved_key; read from
                        // resolved_key (the resolution's authoritative key).
                        source_src_idx: resolved_key.source_src_idx,
                        inner_cur_bp: resolved_key.inner_cur_bp,
                        // The RESOLVED wrap (§3b): the spliced member carries
                        // the wrap of the body that completed it.
                        wrap_cat: resolved_key.wrap_cat,
                        wrap_rule: resolved_key.wrap_rule,
                        snap: snap.clone(),
                        // Forward drain: NEVER interposes a coercion (the
                        // body category already matches at the same dispatch
                        // pos). Byte-identical to pre-Blocker-3.
                        coercion: None,
                    });
                }
            }
        }
        self.crosswrap_splices_total += jobs.len() as u64;
        jobs
    }

    /// Sig-B Blocker-3 §2.4a (2026-06-01, pgmcp experiment #9): the
    /// SPAN-ANCHORED outer-cast reconstruction drain — the EOI-time /
    /// pre-Error successor to M5.1's `take_outer_cast_revival`, distinct from
    /// the forward per-step [`take_pending_for_drain_crosswrap`] (which stays
    /// byte-identical). Where the forward drain pairs a paused member with a
    /// Resolved body by DISPATCH-POS EQUALITY (`K_sib.pos == R.pos_at_dispatch`),
    /// this drain pairs by SPAN ALIGNMENT (`R.span_lo == K_sib.pos`) — the
    /// evidence that the body `R` starts exactly where the member delegated,
    /// which the left-associative fold breaks for the genuine cross-cat cast
    /// (the §1.2 re-localization: the full-span body keys at an INNER dispatch
    /// pos, not the member's `(`-dispatch pos).
    ///
    /// Unlike the forward drain (one `resolved_key` argument), this scans ALL
    /// Resolved entries `R`, reads each `R.symbol_id`'s SPPF span `[lo, hi]`,
    /// and for each paused member `K_sib` (non-empty `pending_members`) tests
    /// the §2.4a eligibility:
    ///
    ///   1. `K_sib` has non-empty `pending_members`.
    ///   2. `K_sib.equiv() == R_key.equiv()` (narrow EquivKey read, R5).
    ///   3. `R.span_lo == K_sib.pos` (THE SPAN ANCHOR — replaces the forward
    ///      clause-3 pos-equality).
    ///   4. category compat: `body_cat == tgt_cat` (tgt_cat = K_sib.source_src_idx,
    ///      the cast arg cat the member dispatched its body as) OR
    ///      `single_hop_coercion(body_cat, tgt_cat)` non-empty. When matched
    ///      via a coercion, the job carries `coercion = Some((cat, rule))` so
    ///      the walker interposes it before the cast fires (§2.4c); when
    ///      `body_cat == tgt_cat`, `coercion = None` (direct splice).
    ///   5. take-once: `(K_sib, R.symbol_id) ∉ crosswrap_drained` (the SAME
    ///      monotone set the forward drain + §3d backstop share — §3 termination).
    ///
    /// Span anchor (3) + category compat (4) are FAR more selective than
    /// M5.1's equiv-only pairing — they cut the 16251-cursor over-fire while
    /// reaching the genuine span-aligned category-correct body. The member's
    /// own-wrap `K_sib` entry is NOT removed (`Ambiguous` first-class). The
    /// revival passes `pos_at_dispatch = K_sib.pos (= R.span_lo)` and
    /// `hi_pos = R.span_hi` (§2.4b) so the GSS re-push / SPPF push / cursor.pos
    /// are span-consistent.
    ///
    /// Returns an empty `Vec` when no span-aligned category-compatible
    /// undrained pair exists (the common case on cast-free workloads — the
    /// `entries` Resolved set is empty → O(1) return-0 → Welch-neutral).
    pub fn take_span_anchored_outer_cast<E: crate::wpda_walker::WpdaEngine<W>>(
        &mut self,
        sppf: &crate::sppf::Sppf<W>,
        engine: &E,
    ) -> Vec<CrossWrapSpliceJob<W>> {
        // ── Pass 1: snapshot every Resolved `R` with a live worker + its
        //    SPPF span [lo, hi] + body_cat + equiv. Clone the fields the jobs
        //    need so the sibling scan can borrow `self.entries` immutably.
        struct ResolvedBody<W: SemiringRef> {
            symbol_id: SppfId,
            span_lo: usize,
            span_hi: usize,
            body_cat: u16,
            equiv: EquivKey,
            snaps: Vec<WorkerSnapshot<W>>,
        }
        let mut bodies: Vec<ResolvedBody<W>> = Vec::new();
        for (r_key, r_entry) in self.entries.iter() {
            let (symbol_id, worker_snapshots) = match r_entry {
                DispatchCacheEntry::Resolved { symbol_id, worker_snapshots, .. } => {
                    (*symbol_id, worker_snapshots)
                },
                _ => continue,
            };
            // Live (non-terminal) snapshots only — a terminal worker yields no
            // revivable cursor (mirrors the forward drain's filter).
            let live: Vec<WorkerSnapshot<W>> = worker_snapshots
                .iter()
                .filter(|s| !s.worker_inner_state.is_terminal())
                .cloned()
                .collect();
            if live.is_empty() {
                continue;
            }
            // SPPF span [lo, hi] of R.symbol_id — THE span anchor read.
            let (span_lo, span_hi) = match (sppf.span_lo(symbol_id), sppf.span_hi(symbol_id)) {
                (Some(lo), Some(hi)) => (lo, hi),
                _ => continue,
            };
            // body_cat = R.symbol_id's category_src_idx (non_terminal_tag).
            let body_cat = match sppf.node(symbol_id) {
                Some(crate::sppf::SppfNode::Symbol { non_terminal_tag, .. }) => {
                    *non_terminal_tag as u16
                },
                _ => continue,
            };
            bodies.push(ResolvedBody {
                symbol_id,
                span_lo: span_lo as usize,
                span_hi: span_hi as usize,
                body_cat,
                equiv: r_key.equiv(),
                snaps: live,
            });
        }
        if bodies.is_empty() {
            return Vec::new();
        }

        // ── Pass 2: for each body × each paused member `K_sib`, test the
        //    §2.4a eligibility. Collect (K_sib, body_idx, coercion, members).
        struct Pairing<W: SemiringRef> {
            k_sib: DispatchKey,
            body_idx: usize,
            coercion: Option<(u16, u16)>,
            members: Vec<CohortMember<W>>,
        }
        let mut pairings: Vec<Pairing<W>> = Vec::new();
        for (k_sib, entry) in self.entries.iter() {
            // Clause 1 + member materialization: own wrap InFlight (with
            // members) OR Resolved with a STRICTLY shorter span (with members)
            // — a self-resolution at `>= some body's hi` is its own body, not
            // a cross-wrap orphan (the parens-inner-steal guard, mirrored from
            // the forward clause-4; here applied per-body below).
            let (shell_opt, states, sib_hi_opt): (
                &Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
                &Vec<crate::cohort_lazy::CohortMemberState<W>>,
                Option<usize>,
            ) = match entry {
                DispatchCacheEntry::InFlight { cohort_shell, pending_members, .. }
                    if !pending_members.is_empty() =>
                {
                    (cohort_shell, pending_members, None)
                },
                DispatchCacheEntry::Resolved {
                    hi_pos: sib_hi,
                    cohort_shell,
                    pending_members,
                    ..
                } if !pending_members.is_empty() => (cohort_shell, pending_members, Some(*sib_hi)),
                _ => continue,
            };
            let shell = match shell_opt {
                Some(s) => s,
                None => continue,
            };
            let k_equiv = k_sib.equiv();
            let tgt_cat = k_sib.source_src_idx;
            // Test each body against this member.
            for (body_idx, body) in bodies.iter().enumerate() {
                // Clause 3: span anchor — the body starts where K_sib delegated.
                if body.span_lo != k_sib.pos {
                    continue;
                }
                // Clause 2: narrow EquivKey match (R5).
                if k_equiv != body.equiv {
                    continue;
                }
                // Parens-inner-steal guard (forward clause-4 analogue): if
                // K_sib is self-Resolved at a span >= this body's hi, it
                // already has its own (equal/longer) body — exclude.
                if let Some(sib_hi) = sib_hi_opt {
                    if sib_hi >= body.span_hi {
                        continue;
                    }
                }
                // Clause 4: category compatibility. Direct iff body_cat ==
                // tgt_cat; else a single-hop coercion must bridge body_cat ->
                // tgt_cat.
                let coercion: Option<(u16, u16)> = if body.body_cat == tgt_cat {
                    None
                } else {
                    match engine.single_hop_coercion(body.body_cat, tgt_cat).first() {
                        Some(&(cc, cr)) => Some((cc, cr)),
                        None => continue, // cat-incompatible → reject
                    }
                };
                // Clause 5: take-once (shared monotone set).
                if self
                    .crosswrap_drained
                    .contains(&(k_sib.clone(), body.symbol_id))
                {
                    continue;
                }
                // Eligible. Materialize the member cursors (lazily from the
                // shell + states), one per pending member.
                let members: Vec<CohortMember<W>> = states
                    .iter()
                    .map(|state| CohortMember {
                        return_frame: crate::cohort_lazy::materialize_branch_cursor(shell, state),
                        weight_at_dispatch: state.weight_at_dispatch.clone(),
                    })
                    .collect();
                if sigb_crosswrap_trace() {
                    eprintln!(
                        "[SIGB_SPAN] PAIR R{{sym={},span=[{},{}],body_cat={}}} | \
                         K_sib{{pos:{},src:{},bp:{},wrap:({},{}),members={}}} tgt_cat={} \
                         coercion={:?}",
                        body.symbol_id,
                        body.span_lo,
                        body.span_hi,
                        body.body_cat,
                        k_sib.pos,
                        k_sib.source_src_idx,
                        k_sib.inner_cur_bp,
                        k_sib.wrap_cat,
                        k_sib.wrap_rule,
                        members.len(),
                        tgt_cat,
                        coercion,
                    );
                }
                pairings.push(Pairing {
                    k_sib: k_sib.clone(),
                    body_idx,
                    coercion,
                    members,
                });
            }
        }
        if pairings.is_empty() {
            return Vec::new();
        }

        // ── Pass 3: build jobs (one per pairing × member × R snapshot). Mark
        //    each `(K_sib, R.symbol_id)` drained (take-once, idempotent).
        let mut jobs: Vec<CrossWrapSpliceJob<W>> = Vec::new();
        for p in pairings {
            let body = &bodies[p.body_idx];
            self.crosswrap_drained
                .insert((p.k_sib.clone(), body.symbol_id));
            for member in &p.members {
                for snap in &body.snaps {
                    jobs.push(CrossWrapSpliceJob {
                        member: member.clone(),
                        symbol_id: body.symbol_id,
                        // §2.4b: the body's span IS the member's body extent.
                        // pos_at_dispatch = K_sib.pos = R.span_lo; hi_pos = R.span_hi.
                        hi_pos: body.span_hi,
                        pos_at_dispatch: p.k_sib.pos,
                        // equiv() match ⇒ source_src_idx + inner_cur_bp are
                        // identical between K_sib and the body's key; read from
                        // K_sib (the member whose continuation we revive).
                        source_src_idx: p.k_sib.source_src_idx,
                        inner_cur_bp: p.k_sib.inner_cur_bp,
                        // The MEMBER's own wrap (its cast rule) — this is the
                        // cast that fires on the member's continuation. (Unlike
                        // the forward drain which carries the RESOLVED body's
                        // wrap; here the member IS the outer cast, so its own
                        // wrap is authoritative.)
                        wrap_cat: p.k_sib.wrap_cat,
                        wrap_rule: p.k_sib.wrap_rule,
                        snap: snap.clone(),
                        // §2.4c: interpose the coercion (if any) before the
                        // member's cast fires.
                        coercion: p.coercion,
                    });
                }
            }
        }
        self.crosswrap_splices_total += jobs.len() as u64;
        jobs
    }

    /// Cohort-revive-rework M1 (2026-05-29): drain every paused cohort
    /// member still orphaned on an `InFlight` entry, returning one
    /// `(Arc<CohortShell>, CohortMemberState)` pair per member so the
    /// walker can re-materialize each as an independent worker via
    /// `cohort_lazy::materialize_branch_cursor`.
    ///
    /// **Take-semantics + entry removal (idempotent).** An `InFlight`
    /// entry whose owning worker reached `Resolved` would have been
    /// transitioned to `Resolved` and drained by `take_pending_for_drain`
    /// at end-of-step; an entry that is STILL `InFlight` at EOI fixpoint
    /// is one whose worker died (dropped / errored) without resolving —
    /// its paused members are the silently-lost cross-cat cursors. We
    /// **remove** the whole entry (not merely take its members): the
    /// re-injected orphan, when re-driven from `shell.inner_state` (its
    /// pre-Fork dispatch state), re-emits the same Fork and re-registers
    /// at this key. With the stale `InFlight` entry gone, that
    /// re-registration returns `WorkerInserted` (dispatch_cohort.rs:376)
    /// instead of `InflightCollision` — so the orphan becomes the WORKER
    /// for its own sub-parse and can run it to completion / EOI, rather
    /// than re-pausing behind the dead worker forever. Removing the entry
    /// is strictly idempotent: a second call finds no matching entry and
    /// returns empty.
    ///
    /// `Resolved` entries are left untouched (their members are not
    /// orphans). `Failed` is unit-shaped here (no members) — M2 will
    /// extend this to a `Failed` side-queue.
    ///
    /// Returns an empty `Vec` when there is nothing to revive (the
    /// common case — most parses leave no orphans).
    #[allow(clippy::type_complexity)]
    pub fn drain_orphaned_inflight_members(
        &mut self,
    ) -> Vec<(
        std::sync::Arc<crate::cohort_lazy::CohortShell<W>>,
        crate::cohort_lazy::CohortMemberState<W>,
    )> {
        // First pass: identify InFlight keys that carry revivable
        // orphans (Some(shell) + non-empty pending_members). We collect
        // keys then remove, because `FxHashMap` cannot be mutated while
        // its `values()` iterator is borrowed.
        let orphan_keys: Vec<DispatchKey> = self
            .entries
            .iter()
            .filter_map(|(k, entry)| match entry {
                DispatchCacheEntry::InFlight {
                    cohort_shell: Some(_), pending_members, ..
                } if !pending_members.is_empty() => Some(k.clone()),
                _ => None,
            })
            .collect();
        if orphan_keys.is_empty() {
            return Vec::new();
        }
        // Upper bound on output size: sum of pending_members lengths.
        // Re-read each entry to size the Vec exactly (members are capped
        // at MAX_PENDING_COHORT_PER_KEY = 16, keys are few at EOI).
        let total: usize = orphan_keys
            .iter()
            .filter_map(|k| match self.entries.get(k) {
                Some(DispatchCacheEntry::InFlight { pending_members, .. }) => {
                    Some(pending_members.len())
                },
                _ => None,
            })
            .sum();
        let mut out: Vec<(
            std::sync::Arc<crate::cohort_lazy::CohortShell<W>>,
            crate::cohort_lazy::CohortMemberState<W>,
        )> = Vec::with_capacity(total);
        for key in orphan_keys {
            // `remove` drops the stale InFlight entry so re-registration
            // of a re-injected orphan returns `WorkerInserted`.
            if let Some(DispatchCacheEntry::InFlight { cohort_shell, pending_members, .. }) =
                self.entries.remove(&key)
            {
                let shell = cohort_shell.expect(
                    "drain_orphaned_inflight_members: cohort_shell is Some by the \
                     orphan_keys filter (pause_cohort_member always sets it before \
                     pushing a member)",
                );
                for state in pending_members {
                    out.push((std::sync::Arc::clone(&shell), state));
                }
            }
        }
        out
    }

    /// Cohort-revive-rework M0 (2026-05-29): census of paused cohort
    /// members that are still orphaned at EOI — i.e. parked on
    /// `InFlight` entries whose owning worker never reached `Resolved`
    /// (so the end-of-step drain at `wpda_walker.rs:9068` never fired
    /// for them) or — once M2 lands — on `Failed` entries. Returns
    /// `(inflight_orphans, failed_orphans)`.
    ///
    /// `InFlight` orphans with a `cohort_shell` are the cross-cat
    /// cursors silently lost per the ledger's "⚑ Cross-cat cluster ROOT
    /// CAUSE": each is a valid alternate sub-parse (ProcStr / PVar /
    /// binder / nested-cast) that would have reached EOI but for the
    /// `(pos, source, bp)` cohort collision pausing it behind a worker
    /// that subsequently died. M1's `drain_orphaned_inflight_members`
    /// revives exactly this set.
    ///
    /// `Resolved` entries are EXCLUDED — their members were (or could
    /// still be) drained by the normal end-of-step path; they are not
    /// orphans. `Failed` is unit-shaped at this milestone (carries no
    /// `pending_members`) so its orphan count is structurally 0 until
    /// M2; counted separately so the census validates the prediction
    /// that the loss is entirely in the `InFlight` branch.
    pub fn orphaned_pending_members_count(&self) -> (u64, u64) {
        let mut inflight_orphans: u64 = 0;
        let failed_orphans: u64 = 0;
        for entry in self.entries.values() {
            if let DispatchCacheEntry::InFlight { cohort_shell, pending_members, .. } = entry {
                // Only members with a materializable shell are revivable.
                // (pause_cohort_member always sets the shell before
                // pushing a member, so a non-empty pending_members
                // implies Some(shell); the guard is belt-and-suspenders.)
                if cohort_shell.is_some() {
                    inflight_orphans += pending_members.len() as u64;
                }
            }
            // DispatchCacheEntry::Failed is a unit variant at M0/M1 —
            // it discards pending_members on the InFlight→Failed
            // transition (`fail`), so there is nothing to count here.
            // M2 will stash them into a side-queue and extend this.
        }
        (inflight_orphans, failed_orphans)
    }

    /// Phase F.13 H12 Stage 1.5.3 — read the cached worker
    /// pre-dispatch weight for a key. Returns None if the key has no
    /// entry. Used by the walker's resolve site to populate
    /// `WorkerSnapshot::worker_pre_dispatch_weight`.
    pub fn read_worker_pre(&self, key: &DispatchKey) -> Option<W> {
        match self.entries.get(key)? {
            DispatchCacheEntry::InFlight { worker_pre_dispatch_weight, .. } => {
                Some(worker_pre_dispatch_weight.clone())
            },
            DispatchCacheEntry::Resolved { worker_pre_dispatch_weight, .. } => {
                Some(worker_pre_dispatch_weight.clone())
            },
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
    pub fn pause_cohort_member(&mut self, key: DispatchKey, member: CohortMember<W>) -> bool
    where
        W: crate::automata::semiring::LexProvenance,
    {
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
                pending_members.push(crate::cohort_lazy::CohortMemberState::from_branch_cursor(
                    &member.return_frame,
                    member.weight_at_dispatch.clone(),
                ));
                // The `member: CohortMember<W>` parameter is consumed
                // and dropped here — the full BranchCursor inside is
                // released (only the small shell + state captures
                // survive).
                drop(member);
                true
            },
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
                pending_members.push(crate::cohort_lazy::CohortMemberState::from_branch_cursor(
                    &member.return_frame,
                    member.weight_at_dispatch.clone(),
                ));
                drop(member);
                true
            },
            _ => false,
        }
    }

    /// Sig-B Blocker-2 §3d (2026-05-31, pgmcp experiment #9): SYMMETRIC
    /// revive-on-pause backstop. The end-of-step drain
    /// ([`Self::take_pending_for_drain_crosswrap`]) handles the ordering
    /// "`R` resolves → find the paused members of a sibling `K_sib`". This
    /// method handles the OPPOSITE ordering: "member `M` pauses onto
    /// `K_pause` → a sibling `R'` has ALREADY resolved" — in which case the
    /// drain for `R'` already ran (before `M` existed) and would never
    /// revive `M`. The `boollit` case `int(y != true > x < "qua")` is
    /// exactly this: the cast member registers/pauses AFTER its body's
    /// outer-wrap sibling resolved.
    ///
    /// Call this at the walker's `InflightCollision` pause site, AFTER
    /// `pause_cohort_member`, passing the pausing member's `key`
    /// (`K_pause`) and the member. Returns one [`CrossWrapSpliceJob`] per
    /// `(already-Resolved distinct-wrap sibling R' × non-terminal R'
    /// snapshot)` that passes the SAME §2 eligibility predicate, with `M`
    /// (cloned) as the member to splice.
    ///
    /// **Predicate (identical to the drain, §2).** Splice `M` (under
    /// `K_pause`) from `Resolved` sibling `R'` iff:
    /// 1. `R'.equiv() == K_pause.equiv()`;
    /// 2. `R' != K_pause`;
    /// 3. `R'.pos_at_dispatch == K_pause.pos`;
    /// 4. `K_pause` is `InFlight` (it is — `M` just paused onto it) **OR**
    ///    `K_pause` is `Resolved` with `hi_pos < R'.hi_pos`. Since `M`
    ///    pauses onto an `InFlight` (or `Resolved`) entry, clause 4 holds
    ///    by construction for the `InFlight` case; for the `Resolved`-arm
    ///    pause we additionally require `K_pause.hi_pos < R'.hi_pos` so the
    ///    parens-inner self-resolution (equal hi) is still excluded.
    ///
    /// **Idempotence.** Shares `crosswrap_drained` keyed `(K_pause,
    /// R'.symbol_id)` with the drain, so a member is cross-revived at most
    /// once per resolved-body symbol regardless of which path fires first.
    /// `R'` is NOT removed (only ADDS the body `M` needs).
    #[allow(clippy::type_complexity)]
    pub fn crosswrap_backstop_for_pausing_member(
        &mut self,
        k_pause: &DispatchKey,
        member: &CohortMember<W>,
    ) -> Vec<CrossWrapSpliceJob<W>> {
        let pause_equiv = k_pause.equiv();
        // Read `K_pause`'s own state to evaluate clause 4 for the
        // `Resolved`-pause case (own span must be strictly shorter than R'
        // to be eligible; InFlight is always eligible).
        let pause_own_hi: Option<usize> = match self.entries.get(k_pause) {
            Some(DispatchCacheEntry::Resolved { hi_pos, .. }) => Some(*hi_pos),
            // InFlight / absent / Failed: treat as "own wrap not resolved"
            // (eligible by clause 4's InFlight disjunct). Failed members
            // would not have been paused here, so this is conservative.
            _ => None,
        };
        // Scan for already-Resolved distinct-wrap siblings R'. Capture R''s
        // OWN wrap (`wrap_cat`/`wrap_rule`) so the spliced member adopts the
        // RESOLVED body's wrap — symmetric with the drain (§3b: the revive
        // re-pushes `CategoryEntry(source)` with the RESOLVED wrap).
        let mut sources: Vec<(SppfId, usize, usize, u16, u16, Vec<WorkerSnapshot<W>>)> = Vec::new();
        for (k_sib, entry) in self.entries.iter() {
            if k_sib == k_pause {
                continue;
            }
            if k_sib.equiv() != pause_equiv {
                continue;
            }
            if let DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                ..
            } = entry
            {
                // Clause 3: dispatch-site identity.
                if *pos_at_dispatch != k_pause.pos {
                    continue;
                }
                // Clause 4 (Resolved-pause refinement): if K_pause itself
                // already resolved, require its own span strictly shorter
                // than R' (excludes equal-hi self-resolution = the parens
                // inner steal). InFlight K_pause: always eligible.
                if let Some(own_hi) = pause_own_hi {
                    if own_hi >= *hi_pos {
                        continue;
                    }
                }
                // Idempotence: skip if (K_pause, R'.symbol_id) already done.
                if self
                    .crosswrap_drained
                    .contains(&(k_pause.clone(), *symbol_id))
                {
                    continue;
                }
                let live: Vec<WorkerSnapshot<W>> = worker_snapshots
                    .iter()
                    .filter(|s| !s.worker_inner_state.is_terminal())
                    .cloned()
                    .collect();
                if live.is_empty() {
                    continue;
                }
                if sigb_crosswrap_trace() {
                    eprintln!(
                        "[SIGB_CROSSWRAP] BACKSTOP-PAUSE K_pause={{pos:{},src:{},bp:{},wrap:({},{})}} \
                         <= R'=K_sib{{wrap:({},{})}} R'.symbol_id={} R'.hi_pos={} \
                         R'.pos_at_dispatch={} equiv=({},{})",
                        k_pause.pos,
                        k_pause.source_src_idx,
                        k_pause.inner_cur_bp,
                        k_pause.wrap_cat,
                        k_pause.wrap_rule,
                        k_sib.wrap_cat,
                        k_sib.wrap_rule,
                        symbol_id,
                        hi_pos,
                        pos_at_dispatch,
                        pause_equiv.source_src_idx,
                        pause_equiv.inner_cur_bp,
                    );
                }
                sources.push((
                    *symbol_id,
                    *hi_pos,
                    *pos_at_dispatch,
                    k_sib.wrap_cat,
                    k_sib.wrap_rule,
                    live,
                ));
            }
        }
        if sources.is_empty() {
            return Vec::new();
        }
        let mut jobs: Vec<CrossWrapSpliceJob<W>> = Vec::with_capacity(
            sources
                .iter()
                .map(|(_, _, _, _, _, s)| s.len())
                .sum::<usize>(),
        );
        for (symbol_id, hi_pos, pos_at_dispatch, sib_wrap_cat, sib_wrap_rule, snaps) in sources {
            self.crosswrap_drained.insert((k_pause.clone(), symbol_id));
            for snap in snaps {
                jobs.push(CrossWrapSpliceJob {
                    member: member.clone(),
                    symbol_id,
                    hi_pos,
                    pos_at_dispatch,
                    source_src_idx: k_pause.source_src_idx,
                    inner_cur_bp: k_pause.inner_cur_bp,
                    // The RESOLVED sibling R''s wrap — the body `M` adopts.
                    wrap_cat: sib_wrap_cat,
                    wrap_rule: sib_wrap_rule,
                    snap,
                    // §3d backstop: never interposes a coercion (byte-identical
                    // to pre-Blocker-3).
                    coercion: None,
                });
            }
        }
        self.crosswrap_splices_total += jobs.len() as u64;
        jobs
    }

    /// Transition InFlight → Failed (sub-parse drop without a usable
    /// SPPF symbol). Reserved for Stage 1.5+.
    #[allow(dead_code)]
    pub fn fail(&mut self, key: DispatchKey) {
        if let Some(entry @ DispatchCacheEntry::InFlight { .. }) = self.entries.get_mut(&key) {
            *entry = DispatchCacheEntry::Failed;
            self.failed_total += 1;
        }
    }

    pub fn write_summary(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let collisions_ratio = if self.registrations_total > 0 {
            (self.inflight_collisions_total as f64) * 100.0 / (self.registrations_total as f64)
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
            self.cohort_cursors_emitted_total, self.cohort_cursors_graduated_total,
        )?;
        // Cohort-revive-rework M0/M1 (2026-05-29): orphan census +
        // revive accounting. `inflight_orphan_members` / `failed_orphan_members`
        // are the snapshots taken at EOI by `orphaned_pending_members_count`
        // (see `resolve_at_end_of_input`); a non-zero InFlight count on a
        // failing cross-cat test is the empirical signature of the root
        // cause this rework targets.
        writeln!(
            f,
            "  inflight_orphan_members={}  failed_orphan_members={}",
            self.inflight_orphan_members_total, self.failed_orphan_members_total,
        )?;
        // Sig-B Blocker-2 (2026-05-31): cross-wrap body-splice accounting.
        writeln!(
            f,
            "  crosswrap_splices={}  crosswrap_drained_pairs={}",
            self.crosswrap_splices_total,
            self.crosswrap_drained.len(),
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
        hi_pos: usize,
        pos_at_dispatch: usize,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;

    #[test]
    fn dispatch_key_preserves_positions_above_u32() {
        let low = DispatchKey::new(0, 7, 3, 11, 13);
        let after_u32 = (u32::MAX as usize) + 1;
        let high = DispatchKey::new(after_u32, 7, 3, 11, 13);

        assert_ne!(low, high);
        assert_eq!(high.pos, after_u32);

        let mut cache = DispatchCohortCache::<TropicalWeight>::new();
        assert!(matches!(
            cache.register(low.clone(), TropicalWeight(0.0)),
            RegisterOutcome::WorkerInserted
        ));
        assert!(matches!(
            cache.register(high.clone(), TropicalWeight(0.0)),
            RegisterOutcome::WorkerInserted
        ));
        assert_eq!(cache.entries.len(), 2);
        assert!(cache.entries.contains_key(&low));
        assert!(cache.entries.contains_key(&high));
    }
}
