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

pub(crate) const MAX_WORKER_SNAPSHOTS_PER_KEY: usize = 16;
const MAX_RESOLVED_BODIES_PER_KEY: usize = 16;

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
/// EP-P1 amended §P1 / red-team Round 6 R6-7 (2026-06-11): the cohort
/// cache is shared between the CrossCatProjection cohorts and the (v3)
/// CrossCatLhs program, and key-space disjointness must be STRUCTURAL,
/// not grammar-conditional (the R5-2 standard: relying on
/// `wrap_rule = u16::MAX` never colliding with a real
/// `rule_index_in_category` is the exact anti-pattern that rejected the
/// EdgeKind widening). A numeric collision would drain wrong-origin
/// members through the wrong revive — silent corruption. The route is a
/// CACHE-key axis only; [`DispatchKey::equiv`] drops it (with
/// `pos`/`wrap_*`) so the cohort-MERGE quotient and its M4 narrowing
/// are untouched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CohortRoute {
    /// The shipped CrossCatProjection/CrossCatDelegate cohorts.
    Projection,
    /// The EP-P1 CrossCatLhs program (measure mode @ this commit; the
    /// v3 enforcement reuses the same route).
    CrossCatLhs,
}

/// ROOT-P design-cycle-3 (2026-07-02): the projection-cohort CACHE key — the
/// full [`DispatchKey`], carrying the real `pos`. This is the key type the
/// cohort cache's `entries` map uses. It intentionally RETAINS
/// `wrap_cat`/`wrap_rule`/`route`/`source`/`bp` (unlike the merge-only
/// [`EquivKey`], which also drops those) so every grammar-determined
/// disambiguator survives. `cache_key()` copies the real `pos`, so the map
/// `DispatchKey ↦ entry` and the map `ProjCacheKey ↦ entry` are in bijection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProjCacheKey {
    /// The real dispatch `pos`.
    pub pos: usize,
    pub source_src_idx: u16,
    pub inner_cur_bp: u8,
    pub wrap_cat: u16,
    pub wrap_rule: u16,
    pub route: CohortRoute,
}

impl ProjCacheKey {
    /// Position-independent cohort-MERGE quotient (same as
    /// [`DispatchKey::equiv`]). The sibling scans over `entries` (now keyed on
    /// `ProjCacheKey`) call this to narrow to the `(source_src_idx,
    /// inner_cur_bp)` equivalence class — identical to the pre-quotient
    /// behavior since both axes are retained verbatim in the cache key.
    #[inline(always)]
    pub fn equiv(&self) -> EquivKey {
        EquivKey {
            source_src_idx: self.source_src_idx,
            inner_cur_bp: self.inner_cur_bp,
        }
    }
}

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
    /// R6-7 route discriminant (see [`CohortRoute`]). Cache-key axis
    /// only — dropped by [`Self::equiv`].
    pub route: CohortRoute,
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
            route: CohortRoute::Projection,
        }
    }

    /// EP-P1 (R6-7): the CrossCatLhs-route constructor — structurally
    /// disjoint from every projection key regardless of numeric field
    /// values.
    #[inline(always)]
    pub fn new_crosscat_lhs(
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
            route: CohortRoute::CrossCatLhs,
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

    /// ROOT-P design-cycle-3: project to the projection-cohort CACHE key — the
    /// full [`DispatchKey`] with the real `pos` preserved, so this is an injective
    /// image of the key and the cohort cache is byte-identical to the shipped
    /// (pos-bearing) behavior.
    ///
    /// RETAINS `wrap_cat`/`wrap_rule`/`route`/`source`/`bp` unconditionally so
    /// the M4 cast-family discriminator (wrap) and the R6-7 route discriminant
    /// survive.
    #[inline(always)]
    pub fn cache_key(&self) -> ProjCacheKey {
        ProjCacheKey {
            pos: self.pos,
            source_src_idx: self.source_src_idx,
            inner_cur_bp: self.inner_cur_bp,
            wrap_cat: self.wrap_cat,
            wrap_rule: self.wrap_rule,
            route: self.route,
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

#[derive(Clone)]
pub struct ResolvedHitBody<W: SemiringRef> {
    pub symbol_id: SppfId,
    pub hi_pos: usize,
    pub pos_at_dispatch: usize,
    pub worker_snapshots: Vec<WorkerSnapshot<W>>,
}

#[derive(Clone)]
pub struct CohortDrainJob<W: SemiringRef> {
    pub symbol_id: SppfId,
    pub hi_pos: usize,
    pub pos_at_dispatch: usize,
    pub snapshots: Vec<WorkerSnapshot<W>>,
    pub members: Vec<CohortMember<W>>,
}

#[derive(Clone)]
pub struct ResolvedBody<W: SemiringRef> {
    symbol_id: SppfId,
    hi_pos: usize,
    pos_at_dispatch: usize,
    worker_snapshots: Vec<WorkerSnapshot<W>>,
    snapshots_drained: usize,
}

/// State of a dispatch-cache entry.
pub enum DispatchCacheEntry<W: SemiringRef> {
    /// First cursor's sub-parse is in flight. Subsequent cohort members
    /// register here as paused; they revive at end-of-step drain.
    InFlight {
        cohort_size: u32,
        /// ROOT-P design-cycle-3: the REAL dispatch position(s) this InFlight
        /// entry represents. When the pos-quotient is OFF this is exactly the
        /// key's `pos` (a singleton — byte-identical). When ON, the entry is
        /// shared across `&`-segments, so this records every distinct dispatch
        /// `pos` that registered here (in registration order; deduplicated).
        /// The crosswrap sibling scan's `K_sib.pos == R.pos_at_dispatch`
        /// dispatch-site-identity clause reads THIS (any-match) instead of the
        /// quotiented key so it stays pos-correct under the quotient. `Vec` with
        /// capacity 1 (the OFF / non-quotiented singleton is the common case).
        pos_at_dispatch: Vec<usize>,
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
        /// shell for compact members at this dispatch key.
        /// Constructed at first pause_cohort_member call from the
        /// pausing member's return_frame; subsequent shell-compatible
        /// pauses share via Arc::clone (O(1)). Shell-incompatible
        /// pauses stay in `full_pending_members` instead of being
        /// forced through this representative shell.
        cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
        /// Phase F.13 Stage L2c (2026-05-25): per-member divergence
        /// state for members whose shell-owned evidence matches
        /// `cohort_shell`. `take_pending_for_drain` materializes a
        /// `CohortMember<W>` per state via
        /// `crate::cohort_lazy::materialize_branch_cursor` at drain
        /// time.
        pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
        /// Members that reached the same dispatch key but are not
        /// representable by `cohort_shell` plus `CohortMemberState`.
        /// They remain full cursors so ambiguity/evidence is preserved
        /// without sharing the first member's shell.
        full_pending_members: Vec<CohortMember<W>>,
        /// Phase F.13 chain_10000 Exp 9 / Approach P Substage 1.a
        /// (2026-05-26): realize-time cohort fanout. Eligible cohort
        /// pauses push a `CohortContinuation` here AND (S1.b dual-write)
        /// also build a `CohortMemberState` above. S1.d makes this
        /// the sole continuation representation for eligible sites —
        /// `pending_members` / `full_pending_members` keep the path for
        /// ineligible cohort sites. Drained at EOI by
        /// `install_cohort_continuations` (S1.c) and interned as
        /// outer-rule packings via `sppf.intern_packing`. Hard-capped at
        /// `MAX_DEFERRED_PER_KEY = 64` (S1.e raises to 256).
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
        /// Same dispatch key can legitimately produce multiple source
        /// bodies with distinct spans, e.g. `FVar("float")` at `[p,p+1]`
        /// and `FloatBin(...)` at `[p,q]`. Store those alternatives instead
        /// of appending their snapshots to the first body.
        alternate_bodies: Vec<ResolvedBody<W>>,
        /// A resolved cache hit may arrive before all longer source bodies
        /// for this dispatch key have been discovered. The first hit after
        /// each newly discovered body gets one uncached source worker so
        /// reuse does not make the cache extension-incomplete. Later hits
        /// only revive known bodies/park members until another body is added,
        /// keeping fallback exploration bounded by MAX_RESOLVED_BODIES_PER_KEY.
        resolved_hit_worker_spawned: bool,
        /// The bounded body/snapshot tables have refused at least one
        /// observable alternative for this key. From that point onward a
        /// cache hit must also run the uncached worker path; the cached bodies
        /// are useful reuse evidence, but no longer complete evidence.
        cache_saturated: bool,
        /// Phase F.13 H12 Stage 1.5.3 (2026-05-21): the root worker's
        /// pre-dispatch weight, preserved through the InFlight→Resolved
        /// transition. Used by `read_worker_pre()` for cohort revive
        /// weight delta computation.
        worker_pre_dispatch_weight: W,
        /// Phase F.13 Stage L2c (2026-05-25): see InFlight variant.
        /// Transferred from InFlight when the entry transitions.
        cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
        /// Phase F.13 Stage L2c (2026-05-25): per-member divergence
        /// state for shell-compatible members. PERSISTENT across drains
        /// for multi-packing fanout.
        pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
        /// Full cursor members whose shell-owned evidence differs from
        /// `cohort_shell`. PERSISTENT across drains for multi-packing
        /// fanout.
        full_pending_members: Vec<CohortMember<W>>,
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
                pos_at_dispatch,
                worker_snapshots,
                worker_pre_dispatch_weight: _,
                cohort_shell: _,
                pending_members,
                full_pending_members,
                deferred_continuations,
            } => f
                .debug_struct("InFlight")
                .field("cohort_size", cohort_size)
                .field("pos_at_dispatch", pos_at_dispatch)
                .field("pending_members_len", &pending_members.len())
                .field("full_pending_members_len", &full_pending_members.len())
                .field("worker_snapshots_len", &worker_snapshots.len())
                .field("deferred_continuations_len", &deferred_continuations.len())
                .finish(),
            DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                worker_snapshots,
                pending_members,
                full_pending_members,
                snapshots_drained,
                alternate_bodies,
                resolved_hit_worker_spawned,
                cache_saturated,
                ..
            } => f
                .debug_struct("Resolved")
                .field("symbol_id", symbol_id)
                .field("hi_pos", hi_pos)
                .field("worker_snapshots_len", &worker_snapshots.len())
                .field("alternate_bodies_len", &alternate_bodies.len())
                .field("resolved_hit_worker_spawned", resolved_hit_worker_spawned)
                .field("cache_saturated", cache_saturated)
                .field("pending_members_len", &pending_members.len())
                .field("full_pending_members_len", &full_pending_members.len())
                .field("snapshots_drained", snapshots_drained)
                .finish(),
            DispatchCacheEntry::Failed => f.write_str("Failed"),
        }
    }
}

/// A cohort member is a cursor that reached a `DispatchKey` while it
/// was `InFlight`.
pub struct CohortMember<W: SemiringRef> {
    pub member_id: u64,
    pub return_frame: crate::wpda_walker::BranchCursor<W>,
    pub weight_at_dispatch: W,
}

/// Parked members drained from one stale `InFlight` cohort entry.
///
/// This preserves the cache key and compact lazy member states so callers can
/// re-drive large orphan sets without first materializing every parked member
/// into a full [`BranchCursor`].
pub struct OrphanedInflightMembers<W: SemiringRef> {
    /// ROOT-P design-cycle-3: the cohort-cache key the orphan group lived under
    /// (a [`ProjCacheKey`]; identity/diagnostics only — downstream re-injection
    /// uses each member's own `return_frame`/shell, not this key).
    pub key: ProjCacheKey,
    pub cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
    pub pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
    pub full_pending_members: Vec<CohortMember<W>>,
}

impl<W: SemiringRef> OrphanedInflightMembers<W> {
    #[inline]
    pub fn member_count(&self) -> usize {
        pending_member_count(&self.pending_members, &self.full_pending_members)
    }
}

impl<W: SemiringRef> Clone for CohortMember<W> {
    fn clone(&self) -> Self {
        CohortMember {
            member_id: self.member_id,
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

#[inline]
fn pending_member_count<W: SemiringRef>(
    pending_members: &[crate::cohort_lazy::CohortMemberState<W>],
    full_pending_members: &[CohortMember<W>],
) -> usize {
    pending_members.len() + full_pending_members.len()
}

#[inline]
fn has_pending_members<W: SemiringRef>(
    pending_members: &[crate::cohort_lazy::CohortMemberState<W>],
    full_pending_members: &[CohortMember<W>],
) -> bool {
    !pending_members.is_empty() || !full_pending_members.is_empty()
}

fn materialize_pending_members<W: SemiringRef>(
    cohort_shell: &Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
    pending_members: &[crate::cohort_lazy::CohortMemberState<W>],
    full_pending_members: &[CohortMember<W>],
) -> Vec<CohortMember<W>> {
    let mut materialized =
        Vec::with_capacity(pending_member_count(pending_members, full_pending_members));
    if !pending_members.is_empty() {
        let shell = cohort_shell
            .as_ref()
            .expect("cohort invariant: compact pending_members require a cohort_shell");
        materialized.extend(pending_members.iter().map(|state| CohortMember {
            member_id: state.member_id,
            return_frame: crate::cohort_lazy::materialize_branch_cursor(shell, state),
            weight_at_dispatch: state.weight_at_dispatch.clone(),
        }));
    }
    materialized.extend(full_pending_members.iter().cloned());
    materialized
}

fn materialize_owned_pending_members<W: SemiringRef>(
    cohort_shell: Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
    pending_members: Vec<crate::cohort_lazy::CohortMemberState<W>>,
    mut full_pending_members: Vec<CohortMember<W>>,
) -> Vec<CohortMember<W>> {
    let mut materialized =
        Vec::with_capacity(pending_member_count(&pending_members, &full_pending_members));
    if !pending_members.is_empty() {
        let shell =
            cohort_shell.expect("cohort invariant: compact pending_members require a cohort_shell");
        materialized.extend(pending_members.into_iter().map(|state| CohortMember {
            member_id: state.member_id,
            return_frame: crate::cohort_lazy::materialize_branch_cursor(&shell, &state),
            weight_at_dispatch: state.weight_at_dispatch,
        }));
    }
    materialized.append(&mut full_pending_members);
    materialized
}

fn pause_pending_member<W>(
    key: &DispatchKey,
    cohort_shell: &mut Option<std::sync::Arc<crate::cohort_lazy::CohortShell<W>>>,
    pending_members: &mut Vec<crate::cohort_lazy::CohortMemberState<W>>,
    full_pending_members: &mut Vec<CohortMember<W>>,
    member: CohortMember<W>,
) where
    W: SemiringRef + crate::automata::semiring::LexProvenance,
{
    if cohort_shell.is_none() {
        *cohort_shell = Some(std::sync::Arc::new(
            crate::cohort_lazy::CohortShell::from_branch_cursor(&member.return_frame, key.clone()),
        ));
    }
    let shell = cohort_shell
        .as_ref()
        .expect("cohort_shell was initialized before pending member insertion");
    if shell.can_represent_branch_cursor(&member.return_frame, key) {
        pending_members.push(
            crate::cohort_lazy::CohortMemberState::from_branch_cursor_with_member_id(
                &member.return_frame,
                member.weight_at_dispatch.clone(),
                member.member_id,
            ),
        );
    } else {
        full_pending_members.push(member);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SnapshotInsertOutcome {
    Appended,
    Duplicate,
    Overflow { actual: usize },
}

fn worker_snapshot_observationally_eq<W: SemiringRef>(
    a: &WorkerSnapshot<W>,
    b: &WorkerSnapshot<W>,
) -> bool {
    // Phase 5A d1 (2026-06-10; FV: CohortSnapshotObservationalDedup
    // .{dedup_revival_no_loss, dedup_preserves_revived_set,
    // narrow_key_fits_where_full_key_overflows}, zero-admission): compare ONLY
    // the fields the revive consumer reads. `revive_cohort_member_with_snapshot`
    // (wpda_walker.rs) copies inner_state / last_action_output_cat /
    // pending_packing_weight to the revived cursor; `worker_pre_dispatch_weight`
    // is explicitly discarded there (`let _`, the falsified Stage-1.5.3
    // tropical-delta scheme) and `worker_weight` is never read (cursor.weight =
    // member.weight_at_dispatch ⊗ symbol_weight_sum). Snapshots differing only
    // in those dead fields revive BYTE-IDENTICALLY, so collapsing them is exact
    // observational-equivalence dedup (never weight-pruning) — and it stops the
    // d1 cross-cat-LHS delegates' re-resolution of shared cohort keys from
    // spuriously exhausting MAX_WORKER_SNAPSHOTS_PER_KEY (frontier-17-vs-16
    // AmbiguityBudget failures on nested/chained casts). The `-3!` per-packing
    // distinction is carried by `worker_pending_packing_weight`, which STAYS in
    // the key (the Stage-1.5.2 lesson). INVARIANT: this key must cover exactly
    // the consumer-read fields — if revive starts reading the weight fields
    // again, they must return to this comparison.
    a.worker_inner_state == b.worker_inner_state
        && a.worker_last_action_output_cat == b.worker_last_action_output_cat
        && a.worker_pending_packing_weight == b.worker_pending_packing_weight
}

fn append_snapshot_bounded<W: SemiringRef>(
    worker_snapshots: &mut Vec<WorkerSnapshot<W>>,
    snap: WorkerSnapshot<W>,
) -> SnapshotInsertOutcome {
    if worker_snapshots
        .iter()
        .any(|existing| worker_snapshot_observationally_eq(existing, &snap))
    {
        return SnapshotInsertOutcome::Duplicate;
    }
    if worker_snapshots.len() < MAX_WORKER_SNAPSHOTS_PER_KEY {
        worker_snapshots.push(snap);
        SnapshotInsertOutcome::Appended
    } else {
        SnapshotInsertOutcome::Overflow {
            actual: worker_snapshots.len().saturating_add(1),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CohortOverflowEvidence {
    pub budget: usize,
    pub actual: usize,
    pub position: usize,
}

fn resolved_body_matches(
    symbol_id: SppfId,
    hi_pos: usize,
    pos_at_dispatch: usize,
    body_symbol_id: SppfId,
    body_hi_pos: usize,
    body_pos_at_dispatch: usize,
) -> bool {
    symbol_id == body_symbol_id && hi_pos == body_hi_pos && pos_at_dispatch == body_pos_at_dispatch
}

fn resolved_hit_bodies<W: SemiringRef>(
    symbol_id: SppfId,
    hi_pos: usize,
    pos_at_dispatch: usize,
    worker_snapshots: &[WorkerSnapshot<W>],
    alternate_bodies: &[ResolvedBody<W>],
) -> Vec<ResolvedHitBody<W>> {
    let mut bodies = Vec::with_capacity(1 + alternate_bodies.len());
    bodies.push(ResolvedHitBody {
        symbol_id,
        hi_pos,
        pos_at_dispatch,
        worker_snapshots: worker_snapshots.to_vec(),
    });
    bodies.extend(alternate_bodies.iter().map(|body| ResolvedHitBody {
        symbol_id: body.symbol_id,
        hi_pos: body.hi_pos,
        pos_at_dispatch: body.pos_at_dispatch,
        worker_snapshots: body.worker_snapshots.clone(),
    }));
    bodies
}

fn live_resolved_bodies_from_entry<W: SemiringRef>(
    entry: &DispatchCacheEntry<W>,
) -> Vec<ResolvedHitBody<W>> {
    let DispatchCacheEntry::Resolved {
        symbol_id,
        hi_pos,
        pos_at_dispatch,
        worker_snapshots,
        alternate_bodies,
        ..
    } = entry
    else {
        return Vec::new();
    };
    let mut bodies = Vec::with_capacity(1 + alternate_bodies.len());
    let live: Vec<WorkerSnapshot<W>> = worker_snapshots
        .iter()
        .filter(|s| !s.worker_inner_state.is_terminal())
        .cloned()
        .collect();
    if !live.is_empty() {
        bodies.push(ResolvedHitBody {
            symbol_id: *symbol_id,
            hi_pos: *hi_pos,
            pos_at_dispatch: *pos_at_dispatch,
            worker_snapshots: live,
        });
    }
    for body in alternate_bodies {
        let live: Vec<WorkerSnapshot<W>> = body
            .worker_snapshots
            .iter()
            .filter(|s| !s.worker_inner_state.is_terminal())
            .cloned()
            .collect();
        if !live.is_empty() {
            bodies.push(ResolvedHitBody {
                symbol_id: body.symbol_id,
                hi_pos: body.hi_pos,
                pos_at_dispatch: body.pos_at_dispatch,
                worker_snapshots: live,
            });
        }
    }
    bodies
}

fn resolved_entry_max_hi_pos<W: SemiringRef>(entry: &DispatchCacheEntry<W>) -> Option<usize> {
    let DispatchCacheEntry::Resolved { hi_pos, alternate_bodies, .. } = entry else {
        return None;
    };
    Some(
        alternate_bodies
            .iter()
            .map(|body| body.hi_pos)
            .fold(*hi_pos, usize::max),
    )
}

/// ROOT-P design-cycle-3: does `entry` represent a dispatch at input position
/// `pos`? Reads the REAL dispatch position(s) from the ENTRY (never the map key,
/// which the pos-quotient may have collapsed to a sentinel), so the crosswrap /
/// backstop sibling scans' dispatch-site-identity clause stays pos-correct.
///
/// - `InFlight`: any of the recorded `pos_at_dispatch` positions matches (a
///   singleton == the key's real pos when the quotient is OFF ⇒ byte-identical).
/// - `Resolved`: the scalar `pos_at_dispatch` OR any per-body
///   `alternate_bodies[i].pos_at_dispatch` matches.
/// - `Failed`: never.
#[inline]
fn entry_has_dispatch_pos<W: SemiringRef>(entry: &DispatchCacheEntry<W>, pos: usize) -> bool {
    match entry {
        DispatchCacheEntry::InFlight { pos_at_dispatch, .. } => pos_at_dispatch.contains(&pos),
        DispatchCacheEntry::Resolved { pos_at_dispatch, alternate_bodies, .. } => {
            *pos_at_dispatch == pos || alternate_bodies.iter().any(|b| b.pos_at_dispatch == pos)
        },
        DispatchCacheEntry::Failed => false,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CrossWrapDrainKey {
    /// ROOT-P design-cycle-3: the sibling/pausing key as a [`ProjCacheKey`]
    /// (quotiented pos when ON; real pos when OFF ⇒ byte-identical idempotence).
    /// Combined with the per-parse-unique `member_id` + `symbol_id` + `coercion`
    /// this stays a unique take-once discriminator under the quotient.
    pub dispatch_key: ProjCacheKey,
    pub symbol_id: SppfId,
    pub member_id: u64,
    pub coercion: Option<(u16, u16)>,
}

impl CrossWrapDrainKey {
    #[inline]
    fn new(
        dispatch_key: &ProjCacheKey,
        symbol_id: SppfId,
        member_id: u64,
        coercion: Option<(u16, u16)>,
    ) -> Self {
        Self {
            dispatch_key: *dispatch_key,
            symbol_id,
            member_id,
            coercion,
        }
    }
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
    /// ROOT-P design-cycle-3: keyed on [`ProjCacheKey`] — the full `DispatchKey`
    /// with `pos` quotiented when the pos-quotient is ACTIVE, and `pos` preserved
    /// (byte-identical) when OFF. Every lookup converts a `DispatchKey` via
    /// [`DispatchKey::cache_key`]. The REAL dispatch position is preserved inside
    /// each entry (`pos_at_dispatch` on both InFlight and Resolved, plus per-body
    /// `ResolvedBody::pos_at_dispatch`) so the crosswrap / span-anchor sibling
    /// scans read positions from the ENTRY, never from the (possibly quotiented)
    /// key — keeping them byte-identical OFF and pos-correct ON.
    pub entries: rustc_hash::FxHashMap<ProjCacheKey, DispatchCacheEntry<W>>,
    next_member_id: u64,
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
    /// idempotence set for cross-wrap drains. Keyed by the sibling key
    /// whose member was spliced, the resolved body Symbol, the concrete
    /// paused continuation, and the optional coercion interposed by the
    /// span-anchored drain. The coercion axis is load-bearing: two grammar
    /// rules that both bridge `(body_cat -> target_cat)` are ambiguous
    /// alternatives, so idempotence must suppress repeats of the same
    /// coercion without draining its sibling coercion jobs.
    /// Cleared at the parse boundary by `clear`.
    pub crosswrap_drained: rustc_hash::FxHashSet<CrossWrapDrainKey>,
    /// Sig-B Blocker-2 (2026-05-31): cumulative count of cross-wrap
    /// body-splice jobs emitted (one per member × snapshot). Observability
    /// for experiment #9 — a non-zero count on a failing cross-cat test is
    /// the empirical signature that the body-splice fired.
    pub crosswrap_splices_total: u64,
    /// One-shot drain jobs for bodies/snapshots that exceeded the cache's
    /// persistent storage caps. These preserve the semantic fanout for members
    /// already waiting at the key while allowing the storage cap to remain a
    /// storage cap, not a parse-completeness failure.
    /// ROOT-P design-cycle-3: keyed on [`ProjCacheKey`] to match `entries`.
    uncached_body_drain_jobs: rustc_hash::FxHashMap<ProjCacheKey, Vec<CohortDrainJob<W>>>,
    /// Unresolved evidence produced by cache conditions that cannot be safely
    /// replayed. Plain body/snapshot storage saturation must not set this:
    /// those paths queue one-shot uncached drains and mark the entry saturated
    /// so future hits run uncached workers.
    unresolved_overflow_evidence: Option<CohortOverflowEvidence>,
    pub snapshot_overflows_total: u64,
    pub resolved_body_overflows_total: u64,
}

impl<W: SemiringRef> DispatchCohortCache<W> {
    #[inline(always)]
    pub fn new() -> Self {
        DispatchCohortCache {
            entries: rustc_hash::FxHashMap::default(),
            next_member_id: 0,
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
            uncached_body_drain_jobs: rustc_hash::FxHashMap::default(),
            unresolved_overflow_evidence: None,
            snapshot_overflows_total: 0,
            resolved_body_overflows_total: 0,
        }
    }

    #[inline(always)]
    pub fn clear(&mut self) {
        self.entries.clear();
        self.next_member_id = 0;
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
        self.uncached_body_drain_jobs.clear();
        self.unresolved_overflow_evidence = None;
        self.snapshot_overflows_total = 0;
        self.resolved_body_overflows_total = 0;
    }

    /// Clear token/SPPF-dependent entry state after a live token-source
    /// mutation while preserving cumulative diagnostics. Unlike `clear`,
    /// this is not a parse-boundary reset.
    #[inline(always)]
    pub fn clear_entries_preserving_diagnostics(&mut self) {
        self.entries.clear();
        self.next_member_id = 0;
        self.crosswrap_drained.clear();
        self.uncached_body_drain_jobs.clear();
        self.unresolved_overflow_evidence = None;
    }

    #[inline]
    pub fn unresolved_overflow_evidence(&self) -> Option<CohortOverflowEvidence> {
        self.unresolved_overflow_evidence
    }

    #[inline]
    pub fn allocate_member_id(&mut self) -> u64 {
        self.next_member_id = self
            .next_member_id
            .checked_add(1)
            .expect("cohort member id space exhausted within one parse");
        self.next_member_id
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
        // ROOT-P design-cycle-3: consult/insert under the pos-quotient CACHE key.
        // OFF ⇒ `ck` carries the real `pos` (byte-identical, singleton pos vec);
        // ON ⇒ `pos` is the quotient sentinel so cross-`&`-segment dispatches
        // share this entry (sharing the segment-1 branching decision). The REAL
        // dispatch position (`key.pos`, ALWAYS preserved on the DispatchKey) is
        // recorded IN the entry so the sibling scans stay pos-correct.
        let ck = key.cache_key();
        let real_pos = key.pos;
        match self.entries.get_mut(&ck) {
            None => {
                let mut pos_vec = Vec::with_capacity(1);
                pos_vec.push(real_pos);
                self.entries.insert(
                    ck,
                    DispatchCacheEntry::InFlight {
                        cohort_size: 1,
                        pos_at_dispatch: pos_vec,
                        worker_snapshots: Vec::new(),
                        worker_pre_dispatch_weight: worker_pre_weight,
                        cohort_shell: None,
                        pending_members: Vec::new(),
                        full_pending_members: Vec::new(),
                        // Phase F.13 chain_10000 Exp 9 S1.a (2026-05-26).
                        deferred_continuations: Vec::new(),
                    },
                );
                RegisterOutcome::WorkerInserted
            },
            Some(DispatchCacheEntry::InFlight { cohort_size, pos_at_dispatch, .. }) => {
                *cohort_size += 1;
                self.inflight_collisions_total += 1;
                // ROOT-P design-cycle-3: under the quotient this collision may be
                // a DIFFERENT dispatch position sharing the entry — record it so
                // the sibling scans see the full position set (dedup; OFF this is
                // always a same-pos collision so the vec stays a singleton).
                if !pos_at_dispatch.contains(&real_pos) {
                    pos_at_dispatch.push(real_pos);
                }
                RegisterOutcome::InflightCollision
            },
            Some(DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                alternate_bodies,
                resolved_hit_worker_spawned,
                cache_saturated,
                ..
            }) => {
                self.resolved_hits_total += 1;
                let spawn_worker = *cache_saturated || !*resolved_hit_worker_spawned;
                if !*cache_saturated {
                    *resolved_hit_worker_spawned = true;
                }
                RegisterOutcome::ResolvedHit {
                    bodies: resolved_hit_bodies(
                        *symbol_id,
                        *hi_pos,
                        *pos_at_dispatch,
                        worker_snapshots,
                        alternate_bodies,
                    ),
                    spawn_worker,
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
        let mut increment_resolved_total = false;
        let mut increment_snapshot_appends = false;
        let mut snapshot_overflow = None;
        let mut body_overflow = None;
        let mut uncached_body_drain_job = None;
        // ROOT-P design-cycle-3: resolve under the pos-quotient CACHE key.
        let ck = key.cache_key();
        let entry = match self.entries.get_mut(&ck) {
            Some(e) => e,
            None => return ResolveOutcome::NoOp,
        };
        let outcome = match entry {
            DispatchCacheEntry::InFlight {
                worker_snapshots,
                worker_pre_dispatch_weight,
                cohort_shell,
                pending_members,
                full_pending_members,
                deferred_continuations,
                ..
            } => {
                let mut snapshots = std::mem::take(worker_snapshots);
                snapshots.push(snap);
                let preserved_pre = worker_pre_dispatch_weight.clone();
                let preserved_shell = cohort_shell.take();
                let preserved_members = std::mem::take(pending_members);
                let preserved_full_members = std::mem::take(full_pending_members);
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
                    alternate_bodies: Vec::new(),
                    resolved_hit_worker_spawned: false,
                    cache_saturated: false,
                    worker_pre_dispatch_weight: preserved_pre,
                    cohort_shell: preserved_shell,
                    pending_members: preserved_members,
                    full_pending_members: preserved_full_members,
                    deferred_continuations: preserved_continuations,
                };
                increment_resolved_total = true;
                ResolveOutcome::FirstResolve
            },
            DispatchCacheEntry::Resolved {
                symbol_id: first_symbol_id,
                hi_pos: first_hi_pos,
                pos_at_dispatch: first_pos_at_dispatch,
                worker_snapshots,
                alternate_bodies,
                resolved_hit_worker_spawned,
                cache_saturated,
                cohort_shell,
                pending_members,
                full_pending_members,
                ..
            } => {
                if resolved_body_matches(
                    *first_symbol_id,
                    *first_hi_pos,
                    *first_pos_at_dispatch,
                    symbol_id,
                    hi_pos,
                    pos_at_dispatch,
                ) {
                    let overflow_snap = snap.clone();
                    match append_snapshot_bounded(worker_snapshots, snap) {
                        SnapshotInsertOutcome::Appended => {
                            increment_snapshot_appends = true;
                            ResolveOutcome::SnapshotAppended
                        },
                        SnapshotInsertOutcome::Duplicate => ResolveOutcome::SnapshotDuplicate,
                        SnapshotInsertOutcome::Overflow { actual } => {
                            *cache_saturated = true;
                            snapshot_overflow = Some(CohortOverflowEvidence {
                                budget: MAX_WORKER_SNAPSHOTS_PER_KEY,
                                actual,
                                position: key.pos,
                            });
                            if has_pending_members(pending_members, full_pending_members) {
                                uncached_body_drain_job = Some(CohortDrainJob {
                                    symbol_id,
                                    hi_pos,
                                    pos_at_dispatch,
                                    snapshots: vec![overflow_snap],
                                    members: materialize_pending_members(
                                        cohort_shell,
                                        pending_members,
                                        full_pending_members,
                                    ),
                                });
                            }
                            ResolveOutcome::SnapshotOverflow {
                                budget: MAX_WORKER_SNAPSHOTS_PER_KEY,
                                actual,
                            }
                        },
                    }
                } else if let Some(body) = alternate_bodies.iter_mut().find(|body| {
                    resolved_body_matches(
                        body.symbol_id,
                        body.hi_pos,
                        body.pos_at_dispatch,
                        symbol_id,
                        hi_pos,
                        pos_at_dispatch,
                    )
                }) {
                    let overflow_snap = snap.clone();
                    match append_snapshot_bounded(&mut body.worker_snapshots, snap) {
                        SnapshotInsertOutcome::Appended => {
                            increment_snapshot_appends = true;
                            ResolveOutcome::SnapshotAppended
                        },
                        SnapshotInsertOutcome::Duplicate => ResolveOutcome::SnapshotDuplicate,
                        SnapshotInsertOutcome::Overflow { actual } => {
                            *cache_saturated = true;
                            snapshot_overflow = Some(CohortOverflowEvidence {
                                budget: MAX_WORKER_SNAPSHOTS_PER_KEY,
                                actual,
                                position: key.pos,
                            });
                            if has_pending_members(pending_members, full_pending_members) {
                                uncached_body_drain_job = Some(CohortDrainJob {
                                    symbol_id,
                                    hi_pos,
                                    pos_at_dispatch,
                                    snapshots: vec![overflow_snap],
                                    members: materialize_pending_members(
                                        cohort_shell,
                                        pending_members,
                                        full_pending_members,
                                    ),
                                });
                            }
                            ResolveOutcome::SnapshotOverflow {
                                budget: MAX_WORKER_SNAPSHOTS_PER_KEY,
                                actual,
                            }
                        },
                    }
                } else {
                    // Memory cap: refuse to PERSIST further bodies beyond cap.
                    // This is a storage bound, not evidence that the parse path
                    // is invalid. The overflowing body is replayed once for the
                    // members already waiting at this key, and the entry is
                    // marked saturated so future cache hits run an uncached
                    // worker in parallel with cached reuse.
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
                    // to 16 (4x of original). Empirically the cap=256
                    // experiment caused chain_10000 to grow past 22 GB
                    // RSS at 2:54 (close to baseline 24 GB OOM ceiling).
                    // The L3+L4 per-cursor savings (~50x via lazy form +
                    // Arc-shared cycle defense) don't fully amortize a
                    // ~4096x cap-product increase (256^2) -- concrete
                    // revives still happen for ObsDivergent steps and
                    // pay the materialize cost. cap=16 (16^2=256 cap
                    // product, 16x original) should fit in ~6x pre-L3
                    // baseline = ~150 MB at chain_1000.
                    if alternate_bodies.len() < MAX_RESOLVED_BODIES_PER_KEY {
                        alternate_bodies.push(ResolvedBody {
                            symbol_id,
                            hi_pos,
                            pos_at_dispatch,
                            worker_snapshots: vec![snap],
                            snapshots_drained: 0,
                        });
                        *resolved_hit_worker_spawned = false;
                        increment_resolved_total = true;
                        ResolveOutcome::FirstResolve
                    } else {
                        let budget = 1usize.saturating_add(MAX_RESOLVED_BODIES_PER_KEY);
                        let actual = budget.saturating_add(1);
                        body_overflow =
                            Some(CohortOverflowEvidence { budget, actual, position: key.pos });
                        *cache_saturated = true;
                        if has_pending_members(pending_members, full_pending_members) {
                            uncached_body_drain_job = Some(CohortDrainJob {
                                symbol_id,
                                hi_pos,
                                pos_at_dispatch,
                                snapshots: vec![snap],
                                members: materialize_pending_members(
                                    cohort_shell,
                                    pending_members,
                                    full_pending_members,
                                ),
                            });
                        }
                        ResolveOutcome::ResolvedBodyOverflow { budget, actual }
                    }
                }
            },
            DispatchCacheEntry::Failed => ResolveOutcome::NoOp,
        };
        if increment_resolved_total {
            self.resolved_total += 1;
        }
        if increment_snapshot_appends {
            self.snapshot_appends_total += 1;
        }
        if let Some(_evidence) = snapshot_overflow {
            self.snapshot_overflows_total += 1;
        }
        if let Some(_evidence) = body_overflow {
            self.resolved_body_overflows_total += 1;
        }
        if let Some(job) = uncached_body_drain_job {
            self.uncached_body_drain_jobs
                .entry(ck)
                .or_default()
                .push(job);
        }
        outcome
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
        self.take_pending_for_drain_all(key)
            .into_iter()
            .next()
            .map(|job| (job.symbol_id, job.hi_pos, job.pos_at_dispatch, job.snapshots, job.members))
    }

    pub fn take_pending_for_drain_all(&mut self, key: &DispatchKey) -> Vec<CohortDrainJob<W>> {
        // ROOT-P design-cycle-3: drain under the pos-quotient CACHE key.
        let ck = key.cache_key();
        let mut jobs = self
            .uncached_body_drain_jobs
            .remove(&ck)
            .unwrap_or_default();
        let Some(entry) = self.entries.get_mut(&ck) else {
            return jobs;
        };
        let mut cached_jobs = match entry {
            DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                pos_at_dispatch,
                worker_snapshots,
                snapshots_drained,
                alternate_bodies,
                resolved_hit_worker_spawned: _,
                cache_saturated: _,
                worker_pre_dispatch_weight: _,
                cohort_shell,
                pending_members,
                full_pending_members,
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
                if !has_pending_members(pending_members, full_pending_members) {
                    return Vec::new();
                }
                let mut pending_jobs: Vec<(SppfId, usize, usize, Vec<WorkerSnapshot<W>>)> =
                    Vec::new();
                if *snapshots_drained < worker_snapshots.len() {
                    let new_snaps: Vec<WorkerSnapshot<W>> =
                        worker_snapshots[*snapshots_drained..].to_vec();
                    *snapshots_drained = worker_snapshots.len();
                    pending_jobs.push((*symbol_id, *hi_pos, *pos_at_dispatch, new_snaps));
                }
                for body in alternate_bodies.iter_mut() {
                    if body.snapshots_drained < body.worker_snapshots.len() {
                        let new_snaps: Vec<WorkerSnapshot<W>> =
                            body.worker_snapshots[body.snapshots_drained..].to_vec();
                        body.snapshots_drained = body.worker_snapshots.len();
                        pending_jobs.push((
                            body.symbol_id,
                            body.hi_pos,
                            body.pos_at_dispatch,
                            new_snaps,
                        ));
                    }
                }
                if pending_jobs.is_empty() {
                    return Vec::new();
                }
                let materialized = materialize_pending_members(
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                );
                pending_jobs
                    .into_iter()
                    .map(|(symbol_id, hi_pos, pos_at_dispatch, snapshots)| CohortDrainJob {
                        symbol_id,
                        hi_pos,
                        pos_at_dispatch,
                        snapshots,
                        members: materialized.clone(),
                    })
                    .collect()
            },
            _ => Vec::new(),
        };
        jobs.append(&mut cached_jobs);
        jobs
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
    /// **Take-once idempotence (§3a / R3).** `crosswrap_drained` records the
    /// concrete member/body pair plus the optional coercion. A repeated drain
    /// pass over the same concrete alternative is suppressed so a member is
    /// cross-revived at most once per resolved body/coercion alternative — no
    /// entry removal, no re-injection loop.
    #[allow(clippy::type_complexity)]
    pub fn take_pending_for_drain_crosswrap(
        &mut self,
        resolved_key: &DispatchKey,
    ) -> Vec<CrossWrapSpliceJob<W>> {
        // ── Read `R` (the resolved sibling). Require Resolved; clone every
        //    resolved body so the subsequent sibling scan can borrow
        //    `self.entries` immutably without aliasing. ROOT-P design-cycle-3:
        //    look up under the pos-quotient CACHE key.
        let Some(resolved_entry) = self.entries.get(&resolved_key.cache_key()) else {
            return Vec::new();
        };
        let resolved_bodies = live_resolved_bodies_from_entry(resolved_entry);
        if resolved_bodies.is_empty() {
            return Vec::new();
        }
        let r_equiv = resolved_key.equiv();
        let mut jobs: Vec<CrossWrapSpliceJob<W>> = Vec::new();

        for body in resolved_bodies {
            let r_symbol_id = body.symbol_id;
            let r_hi_pos = body.hi_pos;
            let r_pos_at_dispatch = body.pos_at_dispatch;
            let r_snaps = body.worker_snapshots;

            // ── Scan siblings (immutable borrow). Collect, per eligible
            //    `K_sib`, its materialized members. `crosswrap_drained` is
            //    consulted after materialization to skip already-spliced
            //    non-coercion body/member alternatives.
            let mut eligible: Vec<(ProjCacheKey, Vec<CohortMember<W>>)> = Vec::new();
            let resolved_ck = resolved_key.cache_key();
            for (k_sib, entry) in self.entries.iter() {
                // ROOT-P design-cycle-3 SCAN-PROBE (THROWAWAY, env-gated by
                // PRATTAIL_RP3_SCANPROBE): does the crosswrap sibling scan ever
                // iterate over route=Projection entries (the `@a<-@b` cohorts the
                // pos-quotient collapses)? If it only touches route entries that
                // are cast-family cross-WRAP, the quotient (which targets
                // Projection cohorts) is disjoint from this scan's pos-identity.
                if std::env::var_os("PRATTAIL_RP3_SCANPROBE").is_some() {
                    let _ = entry;
                    eprintln!(
                        "[RP3-SCAN crosswrap] k_sib{{route:{:?},pos:{},src:{},bp:{},wrap:({},{})}} R{{pos_disp:{}}}",
                        k_sib.route, k_sib.pos, k_sib.source_src_idx, k_sib.inner_cur_bp,
                        k_sib.wrap_cat, k_sib.wrap_rule, r_pos_at_dispatch,
                    );
                }
                // Clause 1 + 2 + 3: equiv match, distinct wrap, dispatch-site
                // identity (`K_sib.pos == R.pos_at_dispatch`). ROOT-P
                // design-cycle-3: clause-1 compares CACHE keys (the map's key
                // space); clause-3 reads the sibling's REAL dispatch pos from the
                // ENTRY (`entry_has_dispatch_pos`), not the possibly-quotiented
                // key, so it stays pos-correct under the quotient and
                // byte-identical when OFF (singleton entry pos == key pos).
                if *k_sib == resolved_ck {
                    continue;
                }
                if k_sib.equiv() != r_equiv {
                    continue;
                }
                if !entry_has_dispatch_pos(entry, r_pos_at_dispatch) {
                    continue;
                }
                // Clause 4 + member materialization. Eligible iff own wrap is
                // InFlight (with members) OR Resolved with a STRICTLY shorter
                // span (with members). `R.hi_pos` is the full-body span; an own
                // resolution at `>= R.hi_pos` means the member already has (or
                // can get) its own body — not a cross-wrap orphan.
                let members: Vec<CohortMember<W>> = match entry {
                    DispatchCacheEntry::InFlight {
                        cohort_shell,
                        pending_members,
                        full_pending_members,
                        ..
                    } if has_pending_members(pending_members, full_pending_members) => {
                        materialize_pending_members(
                            cohort_shell,
                            pending_members,
                            full_pending_members,
                        )
                    },
                    DispatchCacheEntry::Resolved {
                        cohort_shell,
                        pending_members,
                        full_pending_members,
                        ..
                    } if resolved_entry_max_hi_pos(entry).unwrap_or(usize::MAX) < r_hi_pos
                        && has_pending_members(pending_members, full_pending_members) =>
                    {
                        materialize_pending_members(
                            cohort_shell,
                            pending_members,
                            full_pending_members,
                        )
                    },
                    other => {
                        if sigb_crosswrap_trace() {
                            let (st, sib_hi_dbg, mem_dbg) = match other {
                                DispatchCacheEntry::InFlight {
                                    pending_members,
                                    full_pending_members,
                                    ..
                                } => (
                                    "InFlight(empty)",
                                    usize::MAX,
                                    pending_member_count(pending_members, full_pending_members),
                                ),
                                DispatchCacheEntry::Resolved {
                                    pending_members,
                                    full_pending_members,
                                    ..
                                } => (
                                    "Resolved(>=hi)",
                                    resolved_entry_max_hi_pos(other).unwrap_or(usize::MAX),
                                    pending_member_count(pending_members, full_pending_members),
                                ),
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
                let members: Vec<CohortMember<W>> = members
                    .into_iter()
                    .filter(|member| {
                        !self.crosswrap_drained.contains(&CrossWrapDrainKey::new(
                            k_sib,
                            r_symbol_id,
                            member.member_id,
                            None,
                        ))
                    })
                    .collect();
                if members.is_empty() {
                    continue;
                }
                if sigb_crosswrap_trace() {
                    let sib_state = match entry {
                        DispatchCacheEntry::InFlight { .. } => "InFlight",
                        DispatchCacheEntry::Resolved { .. } => {
                            if resolved_entry_max_hi_pos(entry).unwrap_or(usize::MAX) < r_hi_pos {
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

            // ── Build jobs (immutable borrow dropped). One job per
            //    (eligible K_sib × member × non-terminal R snapshot). Mark each
            //    non-coercion body/member alternative drained so repeat passes
            //    are idempotent without blocking later members under the same
            //    key.
            for (k_sib, members) in eligible {
                for member in members {
                    if !self.crosswrap_drained.insert(CrossWrapDrainKey::new(
                        &k_sib,
                        r_symbol_id,
                        member.member_id,
                        None,
                    )) {
                        continue;
                    }
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
    ///   5. take-once: the body/member/coercion alternative is not in
    ///      `crosswrap_drained` (the SAME monotone set the forward drain +
    ///      §3d backstop share — §3 termination).
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
            for body in live_resolved_bodies_from_entry(r_entry) {
                // SPPF span [lo, hi] of R.symbol_id — THE span anchor read.
                let (span_lo, span_hi) =
                    match (sppf.span_lo(body.symbol_id), sppf.span_hi(body.symbol_id)) {
                        (Some(lo), Some(hi)) => (lo, hi),
                        _ => continue,
                    };
                // body_cat = R.symbol_id's category_src_idx (non_terminal_tag).
                let body_cat = match sppf.node(body.symbol_id) {
                    Some(crate::sppf::SppfNode::Symbol { non_terminal_tag, .. }) => {
                        *non_terminal_tag as u16
                    },
                    _ => continue,
                };
                bodies.push(ResolvedBody {
                    symbol_id: body.symbol_id,
                    span_lo: span_lo as usize,
                    span_hi: span_hi as usize,
                    body_cat,
                    equiv: r_key.equiv(),
                    snaps: body.worker_snapshots,
                });
            }
        }
        if bodies.is_empty() {
            return Vec::new();
        }

        // ── Pass 2: for each body × each paused member `K_sib`, test the
        //    §2.4a eligibility. Collect (K_sib, body_idx, coercion, members).
        struct Pairing<W: SemiringRef> {
            // ROOT-P design-cycle-3: the sibling's CACHE key (ProjCacheKey).
            k_sib: ProjCacheKey,
            body_idx: usize,
            coercion: Option<(u16, u16)>,
            members: Vec<CohortMember<W>>,
        }
        let mut pairings: Vec<Pairing<W>> = Vec::new();
        for (k_sib, entry) in self.entries.iter() {
            // ROOT-P design-cycle-3 SCAN-PROBE (THROWAWAY, env-gated): route of
            // entries the span-anchored outer-cast scan iterates.
            if std::env::var_os("PRATTAIL_RP3_SCANPROBE").is_some() {
                eprintln!(
                    "[RP3-SCAN spananchor] k_sib{{route:{:?},pos:{},src:{},bp:{},wrap:({},{})}}",
                    k_sib.route, k_sib.pos, k_sib.source_src_idx, k_sib.inner_cur_bp,
                    k_sib.wrap_cat, k_sib.wrap_rule,
                );
            }
            // Clause 1 + member materialization: own wrap InFlight (with
            // members) OR Resolved with a STRICTLY shorter span (with members)
            // — a self-resolution at `>= some body's hi` is its own body, not
            // a cross-wrap orphan (the parens-inner-steal guard, mirrored from
            // the forward clause-4; here applied per-body below).
            let (members, sib_hi_opt): (Vec<CohortMember<W>>, Option<usize>) = match entry {
                DispatchCacheEntry::InFlight {
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                    ..
                } if has_pending_members(pending_members, full_pending_members) => (
                    materialize_pending_members(
                        cohort_shell,
                        pending_members,
                        full_pending_members,
                    ),
                    None,
                ),
                DispatchCacheEntry::Resolved {
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                    ..
                } if has_pending_members(pending_members, full_pending_members) => (
                    materialize_pending_members(
                        cohort_shell,
                        pending_members,
                        full_pending_members,
                    ),
                    resolved_entry_max_hi_pos(entry),
                ),
                _ => continue,
            };
            let k_equiv = k_sib.equiv();
            let tgt_cat = k_sib.source_src_idx;
            // Test each body against this member.
            for (body_idx, body) in bodies.iter().enumerate() {
                // Clause 3: span anchor — the body starts where K_sib delegated.
                // ROOT-P design-cycle-3: read the sibling's REAL delegation pos
                // from the ENTRY (`entry_has_dispatch_pos`), not the quotiented
                // key — byte-identical OFF (singleton entry pos == key pos).
                if !entry_has_dispatch_pos(entry, body.span_lo) {
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
                // tgt_cat; otherwise every single-hop coercion is a distinct
                // grammar alternative and must get its own splice job.
                let coercions: Vec<Option<(u16, u16)>> = if body.body_cat == tgt_cat {
                    vec![None]
                } else {
                    let coercions = engine.single_hop_coercion(body.body_cat, tgt_cat);
                    if coercions.is_empty() {
                        continue; // cat-incompatible -> reject
                    }
                    coercions.iter().copied().map(Some).collect()
                };
                for coercion in coercions {
                    // Clause 5: take-once (shared monotone set), per concrete
                    // member and per coercion. A previous span/forward drain
                    // for one continuation must not block later continuations
                    // parked under the same DispatchKey, and one coercion
                    // alternative must not drain its siblings.
                    let undrained_members: Vec<CohortMember<W>> = members
                        .iter()
                        .filter(|member| {
                            !self.crosswrap_drained.contains(&CrossWrapDrainKey::new(
                                k_sib,
                                body.symbol_id,
                                member.member_id,
                                coercion,
                            ))
                        })
                        .cloned()
                        .collect();
                    if undrained_members.is_empty() {
                        continue;
                    }
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
                            undrained_members.len(),
                            tgt_cat,
                            coercion,
                        );
                    }
                    pairings.push(Pairing {
                        k_sib: k_sib.clone(),
                        body_idx,
                        coercion,
                        members: undrained_members,
                    });
                }
            }
        }
        if pairings.is_empty() {
            return Vec::new();
        }

        // ── Pass 3: build jobs (one per pairing × member × R snapshot). Mark
        //    each body/member/coercion alternative drained (take-once,
        //    idempotent).
        let mut jobs: Vec<CrossWrapSpliceJob<W>> = Vec::new();
        for p in pairings {
            let body = &bodies[p.body_idx];
            for member in &p.members {
                if !self.crosswrap_drained.insert(CrossWrapDrainKey::new(
                    &p.k_sib,
                    body.symbol_id,
                    member.member_id,
                    p.coercion,
                )) {
                    continue;
                }
                for snap in &body.snaps {
                    jobs.push(CrossWrapSpliceJob {
                        member: member.clone(),
                        symbol_id: body.symbol_id,
                        // §2.4b: the body's span IS the member's body extent.
                        // pos_at_dispatch = K_sib.pos = R.span_lo; hi_pos = R.span_hi.
                        // ROOT-P design-cycle-3: clause 3 established the sibling
                        // delegated at `body.span_lo`, so use that directly (the
                        // real delegation pos) — quotient-safe and, when OFF,
                        // exactly `p.k_sib.pos` (byte-identical).
                        hi_pos: body.span_hi,
                        pos_at_dispatch: body.span_lo,
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
    /// full `CohortMember` per member so the walker can re-drive each
    /// as an independent worker.
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
    /// EP-P1 diagnostic (walker-stats consumers): count entries by state
    /// — (inflight_keys, inflight_keys_with_members, resolved_keys,
    /// resolved_keys_with_pending_members). Feeds the EOI census counter
    /// that distinguishes dead-worker stranding from normal resolution.
    pub fn dbg_entry_state_census(&self) -> (u64, u64, u64, u64) {
        let mut inflight = 0u64;
        let mut inflight_with = 0u64;
        let mut resolved = 0u64;
        let mut resolved_with = 0u64;
        for entry in self.entries.values() {
            match entry {
                DispatchCacheEntry::InFlight {
                    pending_members, full_pending_members, ..
                } => {
                    inflight += 1;
                    if has_pending_members(pending_members, full_pending_members) {
                        inflight_with += 1;
                    }
                },
                DispatchCacheEntry::Resolved {
                    pending_members, full_pending_members, ..
                } => {
                    resolved += 1;
                    if has_pending_members(pending_members, full_pending_members) {
                        resolved_with += 1;
                    }
                },
                DispatchCacheEntry::Failed => {},
            }
        }
        (inflight, inflight_with, resolved, resolved_with)
    }

    /// ROOT-P design-cycle-3 STAGE 0 GATE 0c (THROWAWAY DIAGNOSTIC, read-only).
    ///
    /// Groups the LIVE cache entry keys by the proposed `ProjCacheKey`-shape
    /// quotient — `(source_src_idx, inner_cur_bp, wrap_cat, wrap_rule, route)`,
    /// i.e. the full `DispatchKey` MINUS `pos` — and reports:
    ///   1. `distinct_dispatch_keys`: number of live entries (each a distinct
    ///      full `DispatchKey`).
    ///   2. `distinct_projcache_keys`: number of distinct quotient groups (the
    ///      count that would survive dropping `pos` from the cache key).
    ///   3. `pos_only_groups`: number of quotient groups whose members differ
    ///      ONLY in `pos` (all other axes identical — trivially true by
    ///      construction of the quotient, reported for confirmation).
    ///   4. `multi_pos_groups`: number of quotient groups with ≥2 distinct
    ///      `pos` values (these are the cross-`&`-segment re-forks the quotient
    ///      would collapse).
    ///   5. `max_pos_per_group`: the largest number of distinct positions
    ///      sharing one quotient (the per-key fork multiplier).
    ///
    /// GATE 0c PASSES iff `distinct_dispatch_keys` grows ~d^k while
    /// `distinct_projcache_keys` stays ~constant AND every multi-pos group
    /// differs ONLY in `pos` (the quotient is not inert / does not conflate
    /// distinct wrap/source axes).
    pub fn dbg_projcache_quotient_census(&self) -> (u64, u64, u64, u64, u64) {
        use rustc_hash::FxHashMap;
        // quotient axes (ProjCacheKey shape) -> set of distinct `pos` values.
        let mut groups: FxHashMap<(u16, u8, u16, u16, CohortRoute), Vec<usize>> =
            FxHashMap::default();
        for key in self.entries.keys() {
            let q = (
                key.source_src_idx,
                key.inner_cur_bp,
                key.wrap_cat,
                key.wrap_rule,
                key.route,
            );
            let positions = groups.entry(q).or_default();
            if !positions.contains(&key.pos) {
                positions.push(key.pos);
            }
        }
        let distinct_dispatch_keys = self.entries.len() as u64;
        let distinct_projcache_keys = groups.len() as u64;
        // By construction every group's members differ ONLY in `pos` (the five
        // quotient axes are held fixed within a group). We report the count of
        // groups (pos_only == distinct_projcache_keys) plus the multi-pos
        // subset that the quotient actually collapses.
        let pos_only_groups = distinct_projcache_keys;
        let mut multi_pos_groups = 0u64;
        let mut max_pos_per_group = 0u64;
        for positions in groups.values() {
            let n = positions.len() as u64;
            if n >= 2 {
                multi_pos_groups += 1;
            }
            if n > max_pos_per_group {
                max_pos_per_group = n;
            }
        }
        (
            distinct_dispatch_keys,
            distinct_projcache_keys,
            pos_only_groups,
            multi_pos_groups,
            max_pos_per_group,
        )
    }

    pub fn drain_orphaned_inflight_member_groups(&mut self) -> Vec<OrphanedInflightMembers<W>> {
        // First pass: identify InFlight keys that carry revivable
        // orphans. We collect keys then remove, because `FxHashMap`
        // cannot be mutated while its `values()` iterator is borrowed.
        let orphan_keys: Vec<ProjCacheKey> = self
            .entries
            .iter()
            .filter_map(|(k, entry)| match entry {
                DispatchCacheEntry::InFlight {
                    pending_members, full_pending_members, ..
                } if has_pending_members(pending_members, full_pending_members) => Some(*k),
                _ => None,
            })
            .collect();
        if orphan_keys.is_empty() {
            return Vec::new();
        }
        let mut out: Vec<OrphanedInflightMembers<W>> = Vec::with_capacity(orphan_keys.len());
        for key in orphan_keys {
            // `remove` drops the stale InFlight entry so re-registration
            // of a re-injected orphan returns `WorkerInserted`.
            if let Some(DispatchCacheEntry::InFlight {
                cohort_shell,
                pending_members,
                full_pending_members,
                ..
            }) = self.entries.remove(&key)
            {
                out.push(OrphanedInflightMembers {
                    key,
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                });
            }
        }
        out
    }

    pub fn drain_orphaned_inflight_members(&mut self) -> Vec<CohortMember<W>> {
        let groups = self.drain_orphaned_inflight_member_groups();
        let total: usize = groups
            .iter()
            .map(OrphanedInflightMembers::member_count)
            .sum();
        let mut out: Vec<CohortMember<W>> = Vec::with_capacity(total);
        for group in groups {
            out.extend(materialize_owned_pending_members(
                group.cohort_shell,
                group.pending_members,
                group.full_pending_members,
            ));
        }
        out
    }

    /// Non-mutating census of `InFlight` pending members that would be
    /// returned by [`Self::drain_orphaned_inflight_members`].
    ///
    /// The walker uses this to decide whether an orphan-revival round has
    /// work to do before removing evidence from the cache.
    pub fn revivable_inflight_member_count(&self) -> usize {
        self.entries
            .values()
            .map(|entry| match entry {
                DispatchCacheEntry::InFlight {
                    pending_members, full_pending_members, ..
                } => pending_member_count(pending_members, full_pending_members),
                _ => 0,
            })
            .sum()
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
            if let DispatchCacheEntry::InFlight {
                pending_members, full_pending_members, ..
            } = entry
            {
                inflight_orphans +=
                    pending_member_count(pending_members, full_pending_members) as u64;
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
        // ROOT-P design-cycle-3: read under the pos-quotient CACHE key.
        match self.entries.get(&key.cache_key())? {
            DispatchCacheEntry::InFlight { worker_pre_dispatch_weight, .. } => {
                Some(worker_pre_dispatch_weight.clone())
            },
            DispatchCacheEntry::Resolved { worker_pre_dispatch_weight, .. } => {
                Some(worker_pre_dispatch_weight.clone())
            },
            DispatchCacheEntry::Failed => None,
        }
    }

    /// EP-P1 v3.1 (led_chain root fix, 2026-06-12): take + REMOVE the parked
    /// members of a SPECIFIC `InFlight` key whose worker died (the walker's
    /// per-step dead-worker scan found no live body-producing lineage for
    /// it). Returns the materialized members so the walker can re-inject
    /// them as independent Proceed-lineages. Removing the entry means their
    /// re-emitted dispatch registers fresh (`WorkerInserted`) rather than
    /// colliding with the dead InFlight entry. A `Resolved` entry is NOT
    /// touched (its members are served by the normal drain). Returns empty
    /// when the key is absent / Resolved / has no parked members.
    pub fn take_inflight_members(&mut self, key: &DispatchKey) -> Vec<CohortMember<W>>
    where
        W: crate::automata::semiring::LexProvenance,
    {
        // ROOT-P design-cycle-3: consult/remove under the pos-quotient CACHE key.
        let ck = key.cache_key();
        match self.entries.get(&ck) {
            Some(DispatchCacheEntry::InFlight {
                pending_members, full_pending_members, ..
            }) if has_pending_members(pending_members, full_pending_members) => {},
            _ => return Vec::new(),
        }
        let Some(DispatchCacheEntry::InFlight {
            cohort_shell,
            pending_members,
            full_pending_members,
            ..
        }) = self.entries.remove(&ck)
        else {
            return Vec::new();
        };
        materialize_owned_pending_members(cohort_shell, pending_members, full_pending_members)
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
    pub fn pause_cohort_member(&mut self, key: DispatchKey, mut member: CohortMember<W>) -> bool
    where
        W: crate::automata::semiring::LexProvenance,
    {
        // Phase F.13 Stage L6 (2026-05-25): cap raised from 4 to 16
        // (matching MAX_WORKER_SNAPSHOTS_PER_KEY). cap=256 empirically
        // rejected — chain_10000 grew past 22 GB at 2:54 (near
        // baseline 24 GB OOM). The L3+L4 per-cursor savings amortize
        // partly but not enough to fully offset the cap-product blowup.
        const MAX_PENDING_COHORT_PER_KEY: usize = 16;
        if member.member_id == 0 {
            member.member_id = self.allocate_member_id();
        }
        // ROOT-P design-cycle-3: locate the entry under the pos-quotient CACHE
        // key; the FULL `key` is still passed to `pause_pending_member` below so
        // the cohort shell / member state keep their pos-bearing observational
        // identity (members from distinct `&`-segments stay distinguishable).
        match self.entries.get_mut(&key.cache_key()) {
            Some(DispatchCacheEntry::InFlight {
                cohort_shell,
                pending_members,
                full_pending_members,
                ..
            }) if pending_member_count(pending_members, full_pending_members)
                < MAX_PENDING_COHORT_PER_KEY =>
            {
                // Phase F.13 Stage L2c (2026-05-25): shell-compatible
                // members use the lazy form (`cohort_shell` +
                // `pending_members`). Shell-incompatible members keep the
                // full cursor in `full_pending_members` so evidence is not
                // overwritten by the representative shell.
                pause_pending_member(
                    &key,
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                    member,
                );
                true
            },
            Some(DispatchCacheEntry::Resolved {
                cohort_shell,
                pending_members,
                full_pending_members,
                ..
            }) if pending_member_count(pending_members, full_pending_members)
                < MAX_PENDING_COHORT_PER_KEY =>
            {
                pause_pending_member(
                    &key,
                    cohort_shell,
                    pending_members,
                    full_pending_members,
                    member,
                );
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
    /// **Idempotence.** Shares `crosswrap_drained` with the drain using the
    /// non-coercion key, so this concrete member is cross-revived at most once
    /// per resolved-body symbol regardless of which path fires first. `R'` is
    /// NOT removed (only ADDS the body `M` needs).
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
        // ROOT-P design-cycle-3: read K_pause's own entry under the CACHE key.
        let pause_own_hi: Option<usize> = match self.entries.get(&k_pause.cache_key()) {
            Some(entry @ DispatchCacheEntry::Resolved { .. }) => resolved_entry_max_hi_pos(entry),
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
            // ROOT-P design-cycle-3 SCAN-PROBE (THROWAWAY, env-gated): route of
            // entries the pausing-member crosswrap backstop scan iterates.
            if std::env::var_os("PRATTAIL_RP3_SCANPROBE").is_some() {
                let _ = entry;
                eprintln!(
                    "[RP3-SCAN backstop] k_sib{{route:{:?},pos:{},src:{},bp:{},wrap:({},{})}} pause{{pos:{}}}",
                    k_sib.route, k_sib.pos, k_sib.source_src_idx, k_sib.inner_cur_bp,
                    k_sib.wrap_cat, k_sib.wrap_rule, k_pause.pos,
                );
            }
            // ROOT-P design-cycle-3: compare CACHE keys (exclude K_pause's own
            // entry; distinct-wrap siblings have distinct quotient keys and
            // survive). Byte-identical OFF (cache key preserves pos).
            if *k_sib == k_pause.cache_key() {
                continue;
            }
            if k_sib.equiv() != pause_equiv {
                continue;
            }
            if matches!(entry, DispatchCacheEntry::Resolved { .. }) {
                for body in live_resolved_bodies_from_entry(entry) {
                    // Clause 3: dispatch-site identity.
                    if body.pos_at_dispatch != k_pause.pos {
                        continue;
                    }
                    // Clause 4 (Resolved-pause refinement): if K_pause itself
                    // already resolved, require its own span strictly shorter
                    // than R' (excludes equal-hi self-resolution = the parens
                    // inner steal). InFlight K_pause: always eligible.
                    if let Some(own_hi) = pause_own_hi {
                        if own_hi >= body.hi_pos {
                            continue;
                        }
                    }
                    // Idempotence: skip if this concrete member already saw
                    // R'.symbol_id. Other members under K_pause remain eligible.
                    if self.crosswrap_drained.contains(&CrossWrapDrainKey::new(
                        &k_pause.cache_key(),
                        body.symbol_id,
                        member.member_id,
                        None,
                    )) {
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
                        body.symbol_id,
                        body.hi_pos,
                        body.pos_at_dispatch,
                        pause_equiv.source_src_idx,
                        pause_equiv.inner_cur_bp,
                    );
                    }
                    sources.push((
                        body.symbol_id,
                        body.hi_pos,
                        body.pos_at_dispatch,
                        k_sib.wrap_cat,
                        k_sib.wrap_rule,
                        body.worker_snapshots,
                    ));
                }
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
            if !self.crosswrap_drained.insert(CrossWrapDrainKey::new(
                &k_pause.cache_key(),
                symbol_id,
                member.member_id,
                None,
            )) {
                continue;
            }
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
        // ROOT-P design-cycle-3: transition under the pos-quotient CACHE key.
        if let Some(entry @ DispatchCacheEntry::InFlight { .. }) =
            self.entries.get_mut(&key.cache_key())
        {
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
            "  crosswrap_splices={}  crosswrap_drain_keys={}",
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
        bodies: Vec<ResolvedHitBody<W>>,
        spawn_worker: bool,
    },
    FailedHit,
}

/// Outcome of a `resolve` call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolveOutcome {
    NoOp,
    FirstResolve,
    SnapshotAppended,
    SnapshotDuplicate,
    SnapshotOverflow { budget: usize, actual: usize },
    ResolvedBodyOverflow { budget: usize, actual: usize },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::semiring::Semiring;
    use crate::automata::semiring::TropicalWeight;
    use crate::wpda_runtime::WpdaState;

    fn lex_one() -> LexicographicWeight {
        <LexicographicWeight as Semiring>::one()
    }

    fn branch_cursor() -> crate::wpda_walker::BranchCursor<LexicographicWeight> {
        crate::wpda_walker::BranchCursor::seed_from_live(
            7,
            3,
            lex_one(),
            WpdaState::PrefixDispatch { pos: 3, cur_bp: 0 },
        )
    }

    fn cohort_member(
        return_frame: crate::wpda_walker::BranchCursor<LexicographicWeight>,
    ) -> CohortMember<LexicographicWeight> {
        CohortMember {
            member_id: 0,
            return_frame,
            weight_at_dispatch: lex_one(),
        }
    }

    fn worker_snapshot() -> WorkerSnapshot<LexicographicWeight> {
        worker_snapshot_with_rule(0)
    }

    fn worker_snapshot_with_rule(rule_idx: u16) -> WorkerSnapshot<LexicographicWeight> {
        WorkerSnapshot {
            worker_inner_state: WpdaState::Ready { min_bp: 0 },
            // Phase 5A d1 (2026-06-10): vary a CONSUMED field so each synthetic
            // snapshot is a genuinely distinct revival. Pre-d1 this helper
            // varied only `worker_weight` — a field the revive consumer never
            // reads — which the narrowed observational quotient now (correctly)
            // collapses, so weight-only variants no longer exercise the
            // snapshot cap (FV: CohortSnapshotObservationalDedup).
            worker_last_action_output_cat: Some(rule_idx),
            worker_pending_packing_weight: lex_one(),
            worker_weight: LexicographicWeight::from_cost(0.0, 0, rule_idx),
            worker_pre_dispatch_weight: lex_one(),
        }
    }

    struct TwoCoercionEngine;

    impl crate::wpda_walker::WpdaEngine<LexicographicWeight> for TwoCoercionEngine {
        fn step(
            &self,
            _state: &WpdaState,
            _gss: &crate::gss::WpdaGss<LexicographicWeight>,
            _frontier_top: Option<&crate::gss::WpdaGssNode>,
            _pos: usize,
            _tokens: &dyn crate::wpda_runtime::WpdaTokenSource,
            _frame_ctx: crate::wpda_runtime::FrameCtx,
        ) -> crate::wpda_walker::WpdaStepAction<LexicographicWeight> {
            crate::wpda_walker::WpdaStepAction::Idle
        }

        fn single_hop_coercion(&self, from_cat: u16, to_cat: u16) -> &[(u16, u16)] {
            static COERCIONS: [(u16, u16); 2] = [(7, 1), (7, 2)];
            if from_cat == 9 && to_cat == 7 {
                &COERCIONS
            } else {
                &[]
            }
        }
    }

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
        let high_outcome = cache.register(high.clone(), TropicalWeight(0.0));
        // `low` and `high` share (source,bp,wrap) but carry distinct positions,
        // and the CACHE key preserves the real `pos`, so they are two distinct
        // entries.
        assert!(matches!(high_outcome, RegisterOutcome::WorkerInserted));
        assert_eq!(cache.entries.len(), 2);
        assert!(cache.entries.contains_key(&low.cache_key()));
        assert!(cache.entries.contains_key(&high.cache_key()));
    }

    #[test]
    fn dispatch_cache_key_separates_all_obligation_axes() {
        // ROOT-P design-cycle-3: the NON-pos grammar axes (source, bp, wrap_cat,
        // wrap_rule) MUST each separate the cohort CACHE key in BOTH modes (the
        // M4 cast-family un-conflation). The POS axis separates only when the
        // pos-quotient is OFF; when ON, a pos-variant collapses onto `base`.
        let base = DispatchKey::new(3, 7, 0, 2, 16);
        let non_pos_variants = [
            DispatchKey::new(3, 8, 0, 2, 16), // source
            DispatchKey::new(3, 7, 1, 2, 16), // bp
            DispatchKey::new(3, 7, 0, 3, 16), // wrap_cat
            DispatchKey::new(3, 7, 0, 2, 17), // wrap_rule
        ];
        let pos_variant = DispatchKey::new(4, 7, 0, 2, 16); // pos only

        let mut cache = DispatchCohortCache::<TropicalWeight>::new();
        assert!(matches!(
            cache.register(base.clone(), TropicalWeight(0.0)),
            RegisterOutcome::WorkerInserted
        ));
        // Every non-pos variant is a fresh key in BOTH modes.
        for key in &non_pos_variants {
            assert_ne!(&base, key);
            assert_ne!(base.cache_key(), key.cache_key());
            assert!(matches!(
                cache.register(key.clone(), TropicalWeight(0.0)),
                RegisterOutcome::WorkerInserted
            ));
        }
        assert!(cache.entries.contains_key(&base.cache_key()));
        assert!(non_pos_variants
            .iter()
            .all(|key| cache.entries.contains_key(&key.cache_key())));

        // The pos-variant is a fresh key (WorkerInserted): the CACHE key
        // preserves the real `pos`, so a differing position separates entries.
        let pos_outcome = cache.register(pos_variant.clone(), TropicalWeight(0.0));
        assert_ne!(base.cache_key(), pos_variant.cache_key());
        assert!(matches!(pos_outcome, RegisterOutcome::WorkerInserted));
        // base + 4 non-pos + pos-variant = 6 distinct entries.
        assert_eq!(cache.entries.len(), 2 + non_pos_variants.len());
    }

    #[test]
    fn dispatch_equiv_key_only_quotients_position_and_wrap_axes() {
        let base = DispatchKey::new(3, 7, 0, 2, 16);

        assert_eq!(base.equiv(), DispatchKey::new(4, 7, 0, 2, 16).equiv());
        assert_eq!(base.equiv(), DispatchKey::new(3, 7, 0, 3, 16).equiv());
        assert_eq!(base.equiv(), DispatchKey::new(3, 7, 0, 2, 17).equiv());
        assert_ne!(base.equiv(), DispatchKey::new(3, 8, 0, 2, 16).equiv());
        assert_ne!(base.equiv(), DispatchKey::new(3, 7, 1, 2, 16).equiv());
    }

    #[test]
    fn resolved_drain_preserves_shell_incompatible_pending_member() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));

        let first = branch_cursor();
        let mut second = first.clone();
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(first)));

        second.binder_scope_marks.push((1, vec!["x".to_string()]));
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(second)));

        match cache.entries.get(&key.cache_key()) {
            Some(DispatchCacheEntry::InFlight {
                pending_members, full_pending_members, ..
            }) => {
                assert_eq!(pending_members.len(), 1);
                assert_eq!(full_pending_members.len(), 1);
            },
            other => panic!("expected InFlight cache entry, got {other:?}"),
        }

        assert_eq!(
            cache.resolve(key.clone(), 42, 9, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        let (_, _, _, _, drained) = cache
            .take_pending_for_drain(&key)
            .expect("resolved entry with a new snapshot should drain");

        assert_eq!(drained.len(), 2);
        assert!(drained
            .iter()
            .any(|member| member.return_frame.binder_scope_marks.is_empty()));
        assert!(drained
            .iter()
            .any(|member| !member.return_frame.binder_scope_marks.is_empty()));
    }

    #[test]
    fn resolved_drain_preserves_distinct_bodies_for_one_dispatch_key() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(branch_cursor())));

        assert_eq!(
            cache.resolve(key.clone(), 42, 4, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        assert_eq!(
            cache.resolve(key.clone(), 43, 8, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );

        let jobs = cache.take_pending_for_drain_all(&key);
        let mut bodies: Vec<(SppfId, usize)> =
            jobs.iter().map(|job| (job.symbol_id, job.hi_pos)).collect();
        bodies.sort_unstable();

        assert_eq!(bodies, vec![(42, 4), (43, 8)]);
        assert_eq!(jobs.len(), 2);
        assert!(jobs.iter().all(|job| job.members.len() == 1));
    }

    #[test]
    fn resolved_hit_returns_every_body_for_one_dispatch_key() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));

        assert_eq!(
            cache.resolve(key.clone(), 42, 4, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        assert_eq!(
            cache.resolve(key.clone(), 43, 8, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );

        match cache.register(key.clone(), lex_one()) {
            RegisterOutcome::ResolvedHit { bodies, spawn_worker } => {
                assert!(spawn_worker);
                let mut spans: Vec<(SppfId, usize)> = bodies
                    .iter()
                    .map(|body| (body.symbol_id, body.hi_pos))
                    .collect();
                spans.sort_unstable();
                assert_eq!(spans, vec![(42, 4), (43, 8)]);
            },
            _ => panic!("expected ResolvedHit with both bodies"),
        }
        match cache.register(key.clone(), lex_one()) {
            RegisterOutcome::ResolvedHit { spawn_worker, .. } => assert!(!spawn_worker),
            _ => panic!("expected second ResolvedHit"),
        }
        assert_eq!(
            cache.resolve(key.clone(), 44, 12, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        match cache.register(key, lex_one()) {
            RegisterOutcome::ResolvedHit { spawn_worker, .. } => assert!(spawn_worker),
            _ => panic!("expected ResolvedHit after new body"),
        }
    }

    #[test]
    fn snapshot_cap_queues_uncached_replay_without_unresolved_evidence() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));

        assert_eq!(
            cache.resolve(key.clone(), 42, 4, 3, worker_snapshot_with_rule(0)),
            ResolveOutcome::FirstResolve,
        );
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(branch_cursor())));
        for i in 1..MAX_WORKER_SNAPSHOTS_PER_KEY {
            assert_eq!(
                cache.resolve(key.clone(), 42, 4, 3, worker_snapshot_with_rule(i as u16)),
                ResolveOutcome::SnapshotAppended,
            );
        }

        let overflow = cache.resolve(
            key.clone(),
            42,
            4,
            3,
            worker_snapshot_with_rule(MAX_WORKER_SNAPSHOTS_PER_KEY as u16),
        );
        assert_eq!(
            overflow,
            ResolveOutcome::SnapshotOverflow {
                budget: MAX_WORKER_SNAPSHOTS_PER_KEY,
                actual: MAX_WORKER_SNAPSHOTS_PER_KEY + 1,
            },
        );
        assert_eq!(cache.snapshot_overflows_total, 1);
        assert_eq!(cache.unresolved_overflow_evidence(), None);

        match cache.register(key.clone(), lex_one()) {
            RegisterOutcome::ResolvedHit { spawn_worker, .. } => {
                assert!(spawn_worker, "saturated snapshot cache must spawn an uncached worker");
            },
            _ => panic!("expected ResolvedHit from saturated cache"),
        }

        let jobs = cache.take_pending_for_drain_all(&key);
        assert_eq!(jobs.len(), 2, "cached snapshots plus one uncached overflow replay");
        assert!(jobs.iter().any(|job| job.snapshots.len() == 1));
        assert!(jobs
            .iter()
            .any(|job| job.snapshots.len() == MAX_WORKER_SNAPSHOTS_PER_KEY));
    }

    #[test]
    fn snapshot_quotient_separates_each_observable_worker_field() {
        // Phase 5A d1 (2026-06-10): the quotient compares ONLY the fields the
        // revive consumer reads (inner_state / last_action_output_cat /
        // pending_packing_weight). The weight fields (`worker_weight`,
        // `worker_pre_dispatch_weight`) are DEAD at the consumer — revive
        // discards `worker_pre_dispatch_weight` (`let _`, the falsified
        // Stage-1.5.3 tropical-delta) and never reads `worker_weight` — so
        // snapshots differing only there revive byte-identically and MUST
        // collapse (FV: CohortSnapshotObservationalDedup.dedup_revival_no_loss
        // / narrow_key_fits_where_full_key_overflows). Pre-d1 this test
        // asserted all 5 fields separate; that over-fine key let the d1
        // cross-cat-LHS delegates spuriously exhaust
        // MAX_WORKER_SNAPSHOTS_PER_KEY (frontier-17-vs-16 budget failures).
        let base = worker_snapshot();
        let mut different_inner_state = base.clone();
        different_inner_state.worker_inner_state = WpdaState::PrefixDispatch { pos: 5, cur_bp: 1 };
        let mut different_output_cat = base.clone();
        different_output_cat.worker_last_action_output_cat = Some(9);
        let mut different_pending_weight = base.clone();
        different_pending_weight.worker_pending_packing_weight =
            LexicographicWeight::from_cost(1.0, 0, 0);
        let mut different_worker_weight = base.clone();
        different_worker_weight.worker_weight = LexicographicWeight::from_cost(2.0, 0, 0);
        let mut different_pre_weight = base.clone();
        different_pre_weight.worker_pre_dispatch_weight = LexicographicWeight::from_cost(3.0, 0, 0);

        // CONSUMED fields separate (each yields a distinct revived cursor).
        let consumed_variants =
            [different_inner_state, different_output_cat, different_pending_weight];
        for variant in &consumed_variants {
            assert!(
                !worker_snapshot_observationally_eq(&base, variant),
                "snapshot quotient must separate every field consumed by cohort revive",
            );
        }
        // DEAD fields collapse (identical revived cursor — exact
        // observational-equivalence dedup, never weight-pruning).
        let dead_variants = [different_worker_weight, different_pre_weight];
        for variant in &dead_variants {
            assert!(
                worker_snapshot_observationally_eq(&base, variant),
                "snapshots differing only in consumer-dead weight fields must collapse",
            );
        }

        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert_eq!(cache.resolve(key.clone(), 42, 4, 3, base), ResolveOutcome::FirstResolve,);
        for variant in consumed_variants {
            assert_eq!(
                cache.resolve(key.clone(), 42, 4, 3, variant),
                ResolveOutcome::SnapshotAppended,
            );
        }
        for variant in dead_variants {
            assert_eq!(
                cache.resolve(key.clone(), 42, 4, 3, variant),
                ResolveOutcome::SnapshotDuplicate,
            );
        }

        match cache.register(key, lex_one()) {
            RegisterOutcome::ResolvedHit { bodies, .. } => {
                assert_eq!(bodies.len(), 1);
                // base + 3 consumed-distinct variants; the 2 dead-field
                // variants collapsed as duplicates.
                assert_eq!(bodies[0].worker_snapshots.len(), 4);
            },
            _ => panic!("expected ResolvedHit"),
        }
    }

    #[test]
    fn duplicate_snapshot_does_not_consume_snapshot_cap() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));

        assert_eq!(
            cache.resolve(key.clone(), 42, 4, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        for _ in 0..(MAX_WORKER_SNAPSHOTS_PER_KEY * 2) {
            assert_eq!(
                cache.resolve(key.clone(), 42, 4, 3, worker_snapshot()),
                ResolveOutcome::SnapshotDuplicate,
            );
        }

        assert_eq!(cache.snapshot_overflows_total, 0);
        assert_eq!(cache.unresolved_overflow_evidence(), None);
        match cache.register(key, lex_one()) {
            RegisterOutcome::ResolvedHit { bodies, .. } => {
                assert_eq!(bodies.len(), 1);
                assert_eq!(bodies[0].worker_snapshots.len(), 1);
            },
            _ => panic!("expected ResolvedHit"),
        }
    }

    #[test]
    fn resolved_body_cap_queues_uncached_replay_without_unresolved_evidence() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));

        assert_eq!(
            cache.resolve(key.clone(), 42, 4, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(branch_cursor())));
        for i in 0..MAX_RESOLVED_BODIES_PER_KEY {
            assert_eq!(
                cache.resolve(key.clone(), 100 + i as SppfId, 5 + i, 3, worker_snapshot()),
                ResolveOutcome::FirstResolve,
            );
        }

        let budget = 1 + MAX_RESOLVED_BODIES_PER_KEY;
        let overflow = cache.resolve(key.clone(), 999, 99, 3, worker_snapshot());
        assert_eq!(overflow, ResolveOutcome::ResolvedBodyOverflow { budget, actual: budget + 1 },);
        assert_eq!(cache.resolved_body_overflows_total, 1);
        assert_eq!(cache.unresolved_overflow_evidence(), None);

        match cache.register(key.clone(), lex_one()) {
            RegisterOutcome::ResolvedHit { bodies, spawn_worker } => {
                assert_eq!(bodies.len(), budget);
                assert!(spawn_worker, "saturated body cache must spawn an uncached worker");
            },
            _ => panic!("expected ResolvedHit from saturated cache"),
        }

        let jobs = cache.take_pending_for_drain_all(&key);
        assert_eq!(jobs.len(), budget + 1);
        assert!(jobs
            .iter()
            .any(|job| job.symbol_id == 999 && job.hi_pos == 99 && job.snapshots.len() == 1));
    }

    #[test]
    fn crosswrap_drain_is_idempotent_per_member_not_per_dispatch_key() {
        let resolved_key = DispatchKey::new(3, 7, 0, 2, 16);
        let pause_key = DispatchKey::new(3, 7, 0, 3, 17);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(resolved_key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert!(matches!(
            cache.register(pause_key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert_eq!(
            cache.resolve(resolved_key.clone(), 42, 9, 3, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );

        assert!(cache.pause_cohort_member(pause_key.clone(), cohort_member(branch_cursor())));
        let first_jobs = cache.take_pending_for_drain_crosswrap(&resolved_key);
        assert_eq!(first_jobs.len(), 1);
        let first_member_id = first_jobs[0].member.member_id;
        assert_ne!(first_member_id, 0);

        assert!(cache.pause_cohort_member(pause_key, cohort_member(branch_cursor())));
        let second_jobs = cache.take_pending_for_drain_crosswrap(&resolved_key);
        assert_eq!(second_jobs.len(), 1);
        assert_ne!(second_jobs[0].member.member_id, 0);
        assert_ne!(second_jobs[0].member.member_id, first_member_id);
    }

    #[test]
    fn span_anchored_drain_preserves_every_coercion_alternative() {
        let mut sppf = crate::sppf::Sppf::<LexicographicWeight>::new();
        let body_symbol = sppf.intern_symbol(9, 3, 9);

        let resolved_key = DispatchKey::new(6, 7, 0, 2, 16);
        let pause_key = DispatchKey::new(3, 7, 0, 3, 17);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(resolved_key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert!(matches!(
            cache.register(pause_key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert_eq!(
            cache.resolve(resolved_key, body_symbol, 9, 6, worker_snapshot()),
            ResolveOutcome::FirstResolve,
        );
        assert!(cache.pause_cohort_member(pause_key, cohort_member(branch_cursor())));

        let jobs = cache.take_span_anchored_outer_cast(&sppf, &TwoCoercionEngine);
        let mut coercions: Vec<Option<(u16, u16)>> = jobs.iter().map(|job| job.coercion).collect();
        coercions.sort_unstable();

        assert_eq!(jobs.len(), 2);
        assert_eq!(coercions, vec![Some((7, 1)), Some((7, 2))]);
        assert_eq!(cache.crosswrap_drained.len(), 2);
        assert!(cache
            .take_span_anchored_outer_cast(&sppf, &TwoCoercionEngine)
            .is_empty());
    }

    #[test]
    fn revivable_inflight_member_count_is_non_mutating() {
        let key = DispatchKey::new(3, 7, 0, 2, 16);
        let mut cache = DispatchCohortCache::<LexicographicWeight>::new();
        assert!(matches!(
            cache.register(key.clone(), lex_one()),
            RegisterOutcome::WorkerInserted
        ));
        assert!(cache.pause_cohort_member(key.clone(), cohort_member(branch_cursor())));

        assert_eq!(cache.revivable_inflight_member_count(), 1);
        assert_eq!(cache.revivable_inflight_member_count(), 1);

        let drained = cache.drain_orphaned_inflight_members();
        assert_eq!(drained.len(), 1);
        assert_eq!(cache.revivable_inflight_member_count(), 0);
    }
}
