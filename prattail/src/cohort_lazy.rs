//! Phase F.13 Stage L1 (2026-05-25): cohort lazy materialization scaffolding.
//!
//! See `docs/design/plans/cohort-lazy-materialization.md` for the full
//! multi-week (L1-L6) plan.
//!
//! # Mandate
//!
//! At chain_10000 the walker OOMs at ~24 GB. Heaptrack on chain_1000
//! (`~/.claude/projects/.../memory/2026-05-24-chain_10000-heaptrack-architectural-ceiling.md`)
//! shows `BranchCursor::clone` at 49 % of peak heap. Per-cursor state
//! (six mutable fields cloned per Fork) is the dominant consumer.
//! Stage 3.1b (sppf_symbol_terms GC) and Stage 3.2 (im::Vector for
//! incoming_edge_stack) both failed empirically (5 MB vs 6-10 GB
//! predicted; 22 GB regression at chain_1000 respectively). The 24 GB
//! ceiling is fundamental to the current per-cursor-Vec representation.
//!
//! Lazy materialization introduces a `Frame<W>` enum with `Concrete`
//! (today's `BranchCursor`) and `Cohort` (a shared `~_obs`-invariant
//! shell plus a `Vec` of per-member divergence) variants. At a Tomita-GLR
//! cross-cat-projection dispatch site where 10-100s of cursors share the
//! same `(source_src_idx, pos, inner_cur_bp)`, they form one cohort
//! frame instead of N concrete cursors. The shell's mutable fields are
//! Arc-shared; only on per-member mutation does the cohort materialize.
//!
//! # Correctness gates
//!
//! 1. `~_dispatch` equivalence at H12 dispatch keys.
//! 2. `~_obs` divergence forces materialization BEFORE divergent step.
//! 3. EOI: all cohorts forcibly materialized.
//! 4. Cycle-defense (`visited_dispatch` / `visited_recovery`) honored
//!    per member via materialize-on-mutation.
//!
//! # Stage L1
//!
//! THIS FILE is L1: type definitions only. No constructor sites; no
//! reads from `Frame::Cohort`. Validated by L1 acceptance gate (gauntlet
//! 6169/0 + Welch's-t NEUTRAL chain_50/100/200/1000).
//!
//! Stage L2 wires the `InflightCollision` arm of
//! `allocate_fork_push_child` to build `CohortFrame` instead of
//! pushing onto the H12 `pending_cohort: Vec<CohortMember>`.
//!
//! Stage L3 implements `step_cohort_frame` with the action-divergence
//! classifier (per `cohort-lazy-materialization.md` Explore Agent 2's
//! concrete rule).

use crate::automata::semiring::SemiringRef;
use crate::dispatch_cohort::{DispatchKey, WorkerSnapshot};
use crate::sppf::SppfId;
use crate::wpda_walker::BranchCursor;
use std::sync::Arc;

/// Wrapper around what was historically `branch_cursors: Vec<BranchCursor>`.
///
/// `Frame::Concrete` is the current shape: one full `BranchCursor` per
/// parse-time configuration. `Frame::Cohort` represents N cursors that
/// share the same `~_obs` axes at a Tomita-GLR cross-cat-projection
/// dispatch site (they're about to launch the SAME sub-parse, with
/// per-member divergence only on weight / snapshot / source-priority).
///
/// L1: only `Concrete` is constructed anywhere. `Cohort` is reachable
/// from L2 onward.
pub enum Frame<W: SemiringRef> {
    Concrete(BranchCursor<W>),
    Cohort(Box<CohortFrame<W>>),
}

/// A cohort frame: many logical cursors represented as one shell + N
/// lazy member-states.
///
/// Construction (L2): at `allocate_fork_push_child`'s `InflightCollision`
/// arm, instead of building a fresh BranchCursor per paused worker, the
/// walker either creates a new `CohortFrame` (if none exists for this
/// dispatch key) or extends the existing one.
///
/// Step semantics (L3+): `step_cohort_frame` synthesizes one
/// representative inner_state from `shell`, dispatches `engine.step`,
/// then classifies the resulting `WpdaStepAction` as ObsInvariant
/// (apply to shell once, all members stay lazy), ObsDivergent
/// (materialize the cohort into N Concrete frames, then per-cursor
/// step), or DispatchResolved (broadcast the sub-parse result to all
/// members via `fan_out_cohort`).
pub struct CohortFrame<W: SemiringRef> {
    /// All `~_obs`-axis fields, shared by every member. Read-only after
    /// the cohort is constructed — any member whose step would mutate
    /// these triggers the materialize-on-mutation path.
    pub shell: Arc<CohortShell<W>>,
    /// Per-member divergence axes that are safe to keep lazy. At
    /// chain_10000 peak, expected ~22 members per frame across ~10
    /// active frames; size capped at `MAX_COHORT_FRAME_MEMBERS`
    /// (L6 introduces the cap to replace `MAX_PENDING_COHORT_PER_KEY=4`
    /// and `MAX_WORKER_SNAPSHOTS_PER_KEY=4`, the latter of which silently
    /// drops the 5th+ packing's revives today).
    pub members: Vec<CohortMemberState<W>>,
    /// Cached cohort dispatch result. `Some(_)` after the representative
    /// member's sub-parse completes via `resolve` on the H12 cache;
    /// `None` during in-flight.
    pub dispatch_result: Option<CohortDispatchResult<W>>,
}

/// All `~_obs` axes for a cohort, held by `Arc` so all members share
/// these reads in O(1).
///
/// Per the lazy-materialization correctness criterion (L2): if any
/// member's next step would mutate any of these fields per-member, the
/// cohort MUST materialize before the step fires.
pub struct CohortShell<W: SemiringRef> {
    /// GSS-tip shared by all members post-`CategoryEntry` push.
    pub node: crate::gss::GssNodeId,
    /// Top-of-stack of return frame edges. Shared Arc; `Arc::make_mut`
    /// on mutation triggers cohort materialization.
    pub incoming_edge_stack: Arc<Vec<crate::gss::GssEdgeId>>,
    /// Operational depth indicator (post Phase F.1).
    pub collection_depth: u8,
    /// Cohort-revival discriminator (Phase F.13 Stage 1.5.3R-b). All
    /// members of a cohort share this exactly; `ConfigKey` reads it to
    /// prevent merge with non-cohort cursors.
    pub cohort_origin: Option<DispatchKey>,
    /// Lex-axes (`LexProvenance` triple). All members share these by
    /// construction of `~_obs`: a member with a different lex_alt_idx
    /// would have bucketed separately upstream.
    pub lex_alt_idx: u16,
    pub weight_src_idx: u16,
    pub weight_rule_idx: u16,
    /// Top of `lex_fork_path`. `~_obs` axis (per Explore Agent 1: the
    /// walker treats different stamps as distinct parses at ConfigKey
    /// merge time, so cohort members must share this).
    pub lex_fork_stamp: Option<crate::wpda_walker::LexForkStamp>,
    /// Binder-scope marks shared by all members (Phase F.1+).
    pub binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
    /// Optional-scope marks shared by all members (Phase C.3).
    pub optional_scope_marks: Arc<Vec<usize>>,
    /// SPPF collection arena shared by all members (Phase F.4).
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
    /// Shared cycle-defense at the moment the cohort formed. Any
    /// member that would mutate this triggers materialization.
    pub visited_dispatch: Arc<rustc_hash::FxHashSet<crate::wpda_walker::PackedDispatchConfig>>,
    pub visited_recovery: Arc<rustc_hash::FxHashSet<crate::wpda_walker::PackedDispatchConfig>>,
    /// Recovery depth (Phase L12 / Stage 3.20).
    pub recovery_depth: u8,
    /// The dispatch key that defines this cohort's `~_dispatch`
    /// equivalence class.
    pub dispatch_key: DispatchKey,
    /// SPPF stack baseline before the cohort's dispatch fires. After
    /// resolution, each member pushes its `sub_symbol_id` onto a
    /// CoW-derived stack.
    pub sppf_stack_baseline: Arc<Vec<SppfId>>,
    /// Phantom for unused weight type parameter (the shell itself
    /// carries no weight — weights live in `CohortMemberState`).
    #[allow(dead_code)]
    pub _phantom_weight: std::marker::PhantomData<W>,
}

/// Per-member state that diverges across cohort members.
///
/// These are the axes that the per-cursor baseline tracks distinctly per
/// cursor. Storing only this minimum (instead of a full `BranchCursor`)
/// is the structural memory win of lazy materialization. At chain_1000
/// the per-cursor clone was ~3.2 KB (heaptrack); a `CohortMemberState`
/// is ~64 B (depending on `W` size).
pub struct CohortMemberState<W: SemiringRef> {
    /// Cumulative weight at the dispatch site (= `parent.weight ×
    /// branch.weight` at register time; matches today's
    /// `CohortMember.weight_at_dispatch`).
    pub weight_at_dispatch: W,
    /// Which `WorkerSnapshot` this member is associated with (multi-
    /// packing case). Index into `CohortDispatchResult::worker_snapshots`
    /// after resolution.
    pub snapshot_idx: u8,
    /// Member-local `pending_packing_weight` captured at cohort
    /// formation (consumed at the next `emit_fire_action`).
    pub pending_packing_weight: W,
    /// Member-local `last_action_output_cat` captured at formation.
    pub last_action_output_cat: Option<u16>,
    /// Member-local `source_priority` for the Fork tiebreak chain.
    pub source_priority: u32,
}

/// Cached cohort dispatch outcome: one `sub_symbol_id` shared by all
/// members, plus N snapshots (one per Packing under the shared Symbol)
/// for multi-packing fanout.
pub struct CohortDispatchResult<W: SemiringRef> {
    pub sub_symbol_id: SppfId,
    pub hi_pos: u32,
    pub pos_at_dispatch: u32,
    /// One snapshot per Packing under `sub_symbol_id`. For single-
    /// packing sub-parses this `Vec` has length 1. Members'
    /// `snapshot_idx` indexes into this vector.
    pub worker_snapshots: Vec<WorkerSnapshot<W>>,
}

/// Action divergence classification — the output of the L3
/// classifier that determines how `step_cohort_frame` handles each
/// cohort's next action.
///
/// See `docs/design/plans/cohort-lazy-materialization.md` §3.2 + the
/// concrete rule delivered by Explore Agent 2.
#[allow(dead_code)] // L1 scaffolding; consumed by L3
pub enum DivergenceClass {
    /// Apply to the shell once; all members stay lazy.
    ObsInvariant,
    /// Materialize the cohort into N `Frame::Concrete`s; per-cursor
    /// step thereafter.
    ObsDivergent,
    /// The cohort's queued sub-parse just completed. Cache the result
    /// in `CohortFrame::dispatch_result` and fan out to all members in
    /// one shot via `fan_out_cohort`.
    DispatchResolved,
}

impl<W: SemiringRef> Frame<W> {
    /// Get a shared reference to the underlying concrete cursor.
    ///
    /// **L1 invariant**: `Frame::Cohort` is never constructed; this
    /// always returns `Some(...)` and the `expect`-based unwrap form
    /// `as_concrete_expect` is the canonical L1 access pattern. From
    /// L2 onward callers must explicitly handle the `Cohort` arm.
    #[inline(always)]
    pub fn as_concrete(&self) -> Option<&BranchCursor<W>> {
        match self {
            Frame::Concrete(c) => Some(c),
            Frame::Cohort(_) => None,
        }
    }

    /// Get a mutable reference to the underlying concrete cursor.
    ///
    /// See `as_concrete` invariant.
    #[inline(always)]
    pub fn as_concrete_mut(&mut self) -> Option<&mut BranchCursor<W>> {
        match self {
            Frame::Concrete(c) => Some(c),
            Frame::Cohort(_) => None,
        }
    }

    /// Consume the frame and return the concrete cursor.
    ///
    /// Panics if the frame is `Cohort` (L1 invariant: unreachable).
    #[inline(always)]
    pub fn into_concrete(self) -> BranchCursor<W> {
        match self {
            Frame::Concrete(c) => c,
            Frame::Cohort(_) => {
                panic!("Frame::into_concrete called on Cohort variant — L1 invariant violated")
            }
        }
    }

    /// True iff the frame is the `Concrete` variant.
    #[inline(always)]
    pub fn is_concrete(&self) -> bool {
        matches!(self, Frame::Concrete(_))
    }
}

impl<W: SemiringRef> From<BranchCursor<W>> for Frame<W> {
    #[inline(always)]
    fn from(c: BranchCursor<W>) -> Self {
        Frame::Concrete(c)
    }
}

impl<W: SemiringRef> std::fmt::Debug for Frame<W>
where
    BranchCursor<W>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Frame::Concrete(c) => f.debug_tuple("Concrete").field(c).finish(),
            Frame::Cohort(_) => f.debug_struct("Cohort").finish(),
        }
    }
}
