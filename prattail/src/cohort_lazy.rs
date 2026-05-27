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
#[derive(Clone)]
pub struct CohortShell<W: SemiringRef> {
    /// GSS-tip shared by all members post-`CategoryEntry` push.
    pub node: crate::gss::GssNodeId,
    /// Top-of-stack of return frame edges. Phase F.13 chain_10000 Plan
    /// D E6 Substage 2 (2026-05-26): arena-interned `EdgeStackId` (Copy
    /// u32) replaces `Arc<Vec<GssEdgeId>>`. Walker mutation goes
    /// through `walker.incoming_edge_stack_arena.intern_push/pop`.
    pub incoming_edge_stack_id: crate::edge_stack_arena::EdgeStackId,
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
    pub visited_dispatch: im::OrdSet<crate::wpda_walker::PackedDispatchConfig>,
    pub visited_recovery: im::OrdSet<crate::wpda_walker::PackedDispatchConfig>,
    /// Recovery depth (Phase L12 / Stage 3.20). Mirrors
    /// `BranchCursor::recovery_depth` (u8); cohort formation captures
    /// the parent's depth verbatim (all members share by ~_obs def).
    pub recovery_depth: u8,
    /// Phase F.13 Stage L2a.1 (2026-05-25): recovery delta journal
    /// at cohort formation, shared by all members by ~_obs (the
    /// `~_obs` equivalence requires "same `recovery_deltas` journal
    /// up to the dispatch point"). Materialization deep-clones this
    /// Arc'd Vec into the revived cursor's owned `Vec<BuilderDelta>`.
    /// Closes the L2b BLOCKER on `take_pending_for_drain` migration.
    pub recovery_deltas: Arc<Vec<crate::wpda_walker::BuilderDelta>>,
    /// Phase F.13 Stage L2a.1 (2026-05-25): shared `inner_state` at
    /// dispatch site. All cohort members at the same dispatch key have
    /// the same `WpdaState` (specifically a `CrossCatDelegate` variant
    /// keyed on the dispatch's `(source_src_idx, inner_cur_bp)`).
    /// Captured at cohort formation; materialization clones it into
    /// each revived cursor's `inner_state` field.
    pub inner_state: crate::wpda_runtime::WpdaState,
    /// Phase F.13 Stage L2a.1 (2026-05-25): input position at the
    /// dispatch site. Shared by all members (this is `pos` in the
    /// `DispatchKey`). Materialization sets the revived cursor's
    /// `pos` from this initially; revive then advances to `hi_pos`
    /// after the sub-parse's symbol push.
    pub pos: usize,
    /// The dispatch key that defines this cohort's `~_dispatch`
    /// equivalence class.
    pub dispatch_key: DispatchKey,
    /// SPPF stack baseline before the cohort's dispatch fires. After
    /// resolution, each member pushes its `sub_symbol_id` onto the
    /// arena-extended chain.
    ///
    /// Phase F.13 chain_10000 Plan D E3 Substage 2 (2026-05-26):
    /// changed from `Arc<Vec<SppfId>>` to walker-global-arena-
    /// interned `StackId` (a `Copy u32`). Cohort formation captures
    /// `parent.sppf_stack_id` directly (no Arc bump); materialization
    /// initializes the revived cursor's `sppf_stack_id` to this
    /// baseline. Post-revive push of `sub_symbol_id` becomes
    /// `walker.sppf_stack_arena.intern_push(baseline_id, sid)`.
    pub sppf_stack_baseline_id: crate::sppf_stack_arena::StackId,
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
    /// Phase F.13 Stage L2a.2 (2026-05-25): per-member
    /// `cohort_revive_depth` captured at pause time. Members of a
    /// cohort can have distinct revive depths if they paused at
    /// different recursion levels within a nested cohort-revive
    /// chain. Materialization restores this value verbatim into the
    /// revived cursor.
    ///
    /// L2c reject root cause #1: previously hardcoded to 0 in
    /// `materialize_branch_cursor`, which caused revive to treat
    /// every member as a fresh sub-parse and explode downstream.
    pub cohort_revive_depth: u32,
    /// Phase F.13 Stage L2a.2 (2026-05-25): per-member full
    /// `lex_fork_path` captured at pause time. Cohort members that
    /// hit the same dispatch key via different lex-disambiguation
    /// paths have distinct paths; `ConfigKey` reads `.last()` but
    /// downstream lex tracking and merge identity may read more of
    /// the path. Stored as `Arc<Vec<LexForkStamp>>` (zero-cost
    /// clone) so per-member storage is one pointer; materialization
    /// is `Arc::clone`.
    ///
    /// L2c reject root cause #2: previously reconstructed from
    /// `shell.lex_fork_stamp` (the single top stamp only), losing
    /// path entries 0..n-1. Members whose original path had >1
    /// stamp were observationally distinct from the reconstructed
    /// form, causing identity-related cursor explosions.
    pub lex_fork_path: std::sync::Arc<Vec<crate::wpda_walker::LexForkStamp>>,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivergenceClass {
    /// Apply to the shell once; all members stay lazy.
    ObsInvariant,
    /// Materialize the cohort into N `Frame::Concrete`s; per-cursor
    /// step thereafter.
    ObsDivergent,
    /// The cohort's queued sub-parse just completed. Cache the result
    /// in `CohortFrame::dispatch_result` and fan out to all members in
    /// one shot via `fan_out_cohort`. Detected by the caller
    /// (`step_cohort_frame`) BEFORE classify runs — `classify` itself
    /// only returns `ObsInvariant` or `ObsDivergent`.
    DispatchResolved,
}

impl DivergenceClass {
    /// Phase F.13 Stage L3.3 (2026-05-25): classify a `WpdaStepAction`
    /// for cohort step routing. Returns either `ObsInvariant` (the
    /// action does not mutate any per-member-divergent BranchCursor
    /// field, so it can be applied in bulk to the shell) or
    /// `ObsDivergent` (the action mutates a per-member field, so the
    /// cohort must materialize before the action fires).
    ///
    /// **L3.3 conservative classification** (per plan doc §L3.3): we
    /// only treat actions that provably touch no per-member field as
    /// ObsInvariant; everything that touches `weight`, `recovery_deltas`,
    /// `last_action_output_cat`, or that forks into per-member-divergent
    /// children falls back to ObsDivergent (the L3.2 stub path —
    /// materialize → per-cursor step, identical to baseline).
    ///
    /// As confidence grows (L3.4b refinement, follow-on benchmarking),
    /// individual variants graduate from ObsDivergent to ObsInvariant.
    /// The graduation criterion is: "no per-member field in
    /// `CohortMemberState` is mutated by this action's apply path."
    ///
    /// Decisions:
    /// - **`Advance(_)`**: ObsInvariant — mutates only `cursor.inner_state`,
    ///   which is shell-invariant (all cohort members at the same
    ///   dispatch key share `inner_state` by ~_obs definition; the L4
    ///   Arc-shared cycle defense doesn't apply here because we only
    ///   write the field, not read its history).
    /// - **`Accept`, `Error`, `Idle`**: ObsInvariant — terminal /
    ///   no-op transitions that don't touch per-member fields.
    /// - **Everything carrying `weight: W`** (`Push`, `Pop`,
    ///   `Replace`, `Consume`, `ConsumeAndPush`, `ConsumeAndPop`,
    ///   `ConsumeAndReplace`, `ConsumeIdentAndReplace`,
    ///   `ReplaceAndPush`, `ParsePredicate`, `OptGroupAbsent`,
    ///   `OptGroupFinalize`): ObsDivergent — multiplies into each
    ///   member's weight, which is per-member by definition.
    /// - **`AdvanceWithEffect`**: ObsDivergent — appends to
    ///   `recovery_deltas`, which is per-member (L4 will Arc-share it
    ///   in the shell and CoW per-member).
    /// - **`Fork`**: ObsDivergent — Fork at a cohort site fans out
    ///   per-member (one cohort × N branches → potentially N cohorts;
    ///   L3.6 will route Fork through the materialize fallback so
    ///   the existing Fork handler runs per-cursor).
    pub fn classify<W: crate::automata::semiring::SemiringRef>(
        action: &crate::wpda_walker::WpdaStepAction<W>,
    ) -> DivergenceClass {
        use crate::wpda_walker::WpdaStepAction;
        match action {
            WpdaStepAction::Advance(_)
            | WpdaStepAction::Accept
            | WpdaStepAction::Error(_)
            | WpdaStepAction::Idle => DivergenceClass::ObsInvariant,
            WpdaStepAction::AdvanceWithEffect { .. }
            | WpdaStepAction::Push { .. }
            | WpdaStepAction::Pop { .. }
            | WpdaStepAction::Replace { .. }
            | WpdaStepAction::Fork { .. }
            | WpdaStepAction::ConsumeAndPush { .. }
            | WpdaStepAction::ConsumeAndPop { .. }
            | WpdaStepAction::Consume { .. }
            | WpdaStepAction::ConsumeIdentAndReplace { .. }
            | WpdaStepAction::ConsumeAndReplace { .. }
            | WpdaStepAction::ReplaceAndPush { .. }
            | WpdaStepAction::ParsePredicate { .. }
            | WpdaStepAction::OptGroupAbsent { .. }
            | WpdaStepAction::OptGroupFinalize { .. }
            // Phase F.13 chain_10000 Exp 6 Substage 6a (2026-05-26):
            // `IterativeChainAbsorb` mutates per-cursor `weight` +
            // `inner_state` + GSS top (idempotent push) — same per-
            // member divergence pattern as `ConsumeAndPush`, so
            // classified ObsDivergent. Unreachable at this commit
            // (engine codegen does not yet emit; Substage 6b).
            | WpdaStepAction::IterativeChainAbsorb { .. } => {
                DivergenceClass::ObsDivergent
            }
        }
    }

    /// Phase F.13 chain_10000 Exp 14 Substage 2 (2026-05-27): per-arc
    /// Tomita classifier. Returns the planned Tomita per-arc
    /// dispatch class for the given action.
    ///
    /// Plan ref: `prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`
    /// §3.6.
    ///
    /// Substage 2 ships the classifier with the SAME conservative
    /// graduation as `classify` (Advance + Accept/Error/Idle =
    /// `ObsInvariantOverArcs`; everything else = `ObsDivergentOverArcs`).
    /// Substage 5 will graduate Push/Pop/Replace/ConsumeAndPush to
    /// `ObsInvariantOverArcs` when the pushed/popped symbol's `EdgeKind`
    /// is convergent (per `gss::EdgeKind::is_convergent`) — that is the
    /// chain-interior payoff. Substage 5 will also expose a sibling
    /// `classify_for_tomita_with_edge_kind(action, edge_kind)` that
    /// takes the per-action EdgeKind hint to make the graduation
    /// decision at the call site.
    pub fn classify_for_tomita<W: crate::automata::semiring::SemiringRef>(
        action: &crate::wpda_walker::WpdaStepAction<W>,
    ) -> crate::tomita_frontier::TomitaDivergence {
        use crate::tomita_frontier::TomitaDivergence;
        use crate::wpda_walker::WpdaStepAction;
        match action {
            WpdaStepAction::Advance(_)
            | WpdaStepAction::Accept
            | WpdaStepAction::Error(_)
            | WpdaStepAction::Idle => TomitaDivergence::ObsInvariantOverArcs,
            WpdaStepAction::AdvanceWithEffect { .. }
            | WpdaStepAction::Push { .. }
            | WpdaStepAction::Pop { .. }
            | WpdaStepAction::Replace { .. }
            | WpdaStepAction::Fork { .. }
            | WpdaStepAction::ConsumeAndPush { .. }
            | WpdaStepAction::ConsumeAndPop { .. }
            | WpdaStepAction::Consume { .. }
            | WpdaStepAction::ConsumeIdentAndReplace { .. }
            | WpdaStepAction::ConsumeAndReplace { .. }
            | WpdaStepAction::ReplaceAndPush { .. }
            | WpdaStepAction::ParsePredicate { .. }
            | WpdaStepAction::OptGroupAbsent { .. }
            | WpdaStepAction::OptGroupFinalize { .. }
            | WpdaStepAction::IterativeChainAbsorb { .. } => {
                TomitaDivergence::ObsDivergentOverArcs
            }
        }
    }
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

    /// Phase F.13 Stage L3.1 (2026-05-25): the canonical access pattern
    /// for callers that statically know they are running before L3.4
    /// (cohort frames are never constructed before L3.4 enables them).
    /// Panics with a stage-tagged message if called on `Cohort`.
    #[inline(always)]
    pub fn as_concrete_expect(&self) -> &BranchCursor<W> {
        self.as_concrete().expect(
            "L3.1: branch_cursors entry must be Concrete (no cohort frames before L3.4)",
        )
    }

    /// Phase F.13 Stage L3.1 (2026-05-25): mutable companion of
    /// `as_concrete_expect`. Same L3.1 invariant: panics on `Cohort`.
    #[inline(always)]
    pub fn as_concrete_expect_mut(&mut self) -> &mut BranchCursor<W> {
        self.as_concrete_mut().expect(
            "L3.1: branch_cursors entry must be Concrete (no cohort frames before L3.4)",
        )
    }
}

/// Phase F.13 Stage L3.1 (2026-05-25): convenience iterator over a
/// frame slice that yields only `Concrete` cursors. Yields `expect`-
/// unwrapped concrete refs; panics on `Cohort` with the L3.1 message.
/// Used by stats/snapshot read loops in the walker.
#[inline]
pub fn concrete_iter<W: SemiringRef>(
    slice: &[Frame<W>],
) -> impl Iterator<Item = &BranchCursor<W>> {
    slice.iter().map(|f| f.as_concrete_expect())
}

impl<W: SemiringRef> From<BranchCursor<W>> for Frame<W> {
    #[inline(always)]
    fn from(c: BranchCursor<W>) -> Self {
        Frame::Concrete(c)
    }
}

impl<W: SemiringRef> CohortShell<W> {
    /// Phase F.13 Stage L2 (2026-05-25): construct a `CohortShell`
    /// snapshot from a `BranchCursor` at cohort formation time. All
    /// 15 `~_obs` axes are copied / Arc-bumped from `parent` into the
    /// shared shell. Subsequent cohort members at the same dispatch
    /// key reuse this shell verbatim via `Arc::clone`.
    ///
    /// `dispatch_key` is captured from the H12 cross-cat-projection
    /// dispatch site (`source_src_idx`, `inner_cur_bp`, `pos`) at the
    /// caller. `sppf_stack_baseline` is the parent's `sppf_stack`
    /// at the moment before the cohort's CategoryEntry push — used
    /// at fan_out time to derive each revived member's CoW post-
    /// dispatch SPPF stack.
    pub fn from_branch_cursor(
        parent: &BranchCursor<W>,
        dispatch_key: DispatchKey,
    ) -> Self {
        // Phase F.13 Stage L4.1 (2026-05-25): Arc::clone (O(1)) — was
        // `Arc::new(parent.visited_*.clone())` pre-L4.1 which deep-
        // cloned the HashSet. visited_* are now Arc-wrapped in
        // BranchCursor; this site bumps the refcount.
        let visited_dispatch_arc: im::OrdSet<crate::wpda_walker::PackedDispatchConfig> =
            parent.visited_dispatch.clone();
        let visited_recovery_arc: im::OrdSet<crate::wpda_walker::PackedDispatchConfig> =
            parent.visited_recovery.clone();
        let optional_scope_marks_arc: std::sync::Arc<Vec<usize>> =
            std::sync::Arc::new(parent.optional_scope_marks.clone());
        let binder_scope_marks_arc: std::sync::Arc<Vec<(u16, Vec<String>)>> =
            std::sync::Arc::new(parent.binder_scope_marks.clone());
        // Phase F.13 Stage L4.2 (2026-05-25): Arc::clone (O(1)) — was
        // `Arc::new(parent.field.clone())` deep-clone pre-L4.2. These
        // fields are now Arc-wrapped in BranchCursor.
        let recovery_deltas_arc: std::sync::Arc<Vec<crate::wpda_walker::BuilderDelta>> =
            std::sync::Arc::clone(&parent.recovery_deltas);
        Self {
            node: parent.node,
            // Phase F.13 chain_10000 Plan D E6 Substage 2 (2026-05-26):
            // arena-interned EdgeStackId (Copy u32) replaces Arc<Vec<GssEdgeId>>.
            incoming_edge_stack_id: parent.incoming_edge_stack_id,
            collection_depth: parent.collection_stack_depth,
            cohort_origin: parent.cohort_origin.clone(),
            lex_alt_idx: 0,    // populated from parent.weight via LexProvenance trait (Stage L3 wiring)
            weight_src_idx: 0, // ditto
            weight_rule_idx: 0, // ditto
            lex_fork_stamp: parent.lex_fork_path.last().copied(),
            binder_scope_marks: binder_scope_marks_arc,
            optional_scope_marks: optional_scope_marks_arc,
            sppf_collection_arena: std::sync::Arc::clone(&parent.sppf_collection_arena),
            visited_dispatch: visited_dispatch_arc,
            visited_recovery: visited_recovery_arc,
            recovery_depth: parent.recovery_depth,
            recovery_deltas: recovery_deltas_arc,
            inner_state: parent.inner_state.clone(),
            pos: parent.pos,
            dispatch_key,
            // Phase F.13 chain_10000 Plan D E3 Substage 2 (2026-05-26):
            // arena-interned StackId (Copy u32) replaces Arc<Vec<SppfId>>.
            sppf_stack_baseline_id: parent.sppf_stack_id,
            _phantom_weight: std::marker::PhantomData,
        }
    }
}

impl<W: SemiringRef + Clone> CohortMemberState<W> {
    /// Phase F.13 Stage L2 (2026-05-25): construct a per-member state
    /// from a `BranchCursor` at cohort formation time. Captures the
    /// per-member divergence axes (weight × snapshot index × packing
    /// weight × output cat × source priority) that the lazy
    /// representation tracks distinctly per member while the shell
    /// is Arc-shared.
    ///
    /// `weight_at_dispatch` is the cumulative weight at the H12
    /// register site (= `parent.weight × branch.weight` per the
    /// existing `CohortMember.weight_at_dispatch` convention).
    /// `snapshot_idx` is `0` at formation; the L3 fan_out path
    /// updates it per worker_snapshot during multi-packing fanout.
    pub fn from_branch_cursor(
        parent: &BranchCursor<W>,
        weight_at_dispatch: W,
    ) -> Self {
        Self {
            weight_at_dispatch,
            snapshot_idx: 0,
            pending_packing_weight: parent.pending_packing_weight.clone(),
            last_action_output_cat: parent.last_action_output_cat,
            source_priority: parent.source_priority,
            cohort_revive_depth: parent.cohort_revive_depth,
            lex_fork_path: std::sync::Arc::clone(&parent.lex_fork_path),
        }
    }
}

/// Phase F.13 Stage L2b (2026-05-25): reconstruct a `BranchCursor`
/// from a `CohortShell` + `CohortMemberState`. This is the
/// materialization primitive that bridges the lazy cohort
/// representation back to the existing per-cursor revive code path
/// (`revive_cohort_member_with_snapshot`). L2b uses this at
/// `take_pending_for_drain` to reconstruct legacy `CohortMember`s
/// from the new fields. L2c removes the legacy path entirely.
///
/// All shell `Arc` fields are deep-cloned into owned `Vec`/`HashSet`
/// since today's `BranchCursor` fields are not Arc-typed; this
/// mirrors the heaptrack-documented per-cursor clone cost. L4 (the
/// Arc-shared cycle defense stage) addresses this by Arc-typing
/// `BranchCursor`'s `visited_*` fields directly.
///
/// Phase F.13 Stage L2a.2 (2026-05-25): `cohort_revive_depth` and
/// `lex_fork_path` are now read verbatim from `state`. Pre-L2a.2 they
/// were hardcoded to 0 and reconstructed from `shell.lex_fork_stamp`
/// respectively; that caused L2c chain_1000 to explode to 10+ GB
/// because revive saw the wrong depth (treated members as fresh and
/// re-did the cohort sub-parse) and the wrong path (cursor identity
/// drift triggered redundant fork allocations).
pub fn materialize_branch_cursor<W: SemiringRef + Clone>(
    shell: &CohortShell<W>,
    state: &CohortMemberState<W>,
) -> BranchCursor<W> {
    BranchCursor {
        node: shell.node,
        pos: shell.pos,
        weight: state.weight_at_dispatch.clone(),
        inner_state: shell.inner_state.clone(),
        // Phase F.13 Stage L4.2 (2026-05-25): Arc::clone is O(1).
        recovery_deltas: std::sync::Arc::clone(&shell.recovery_deltas),
        source_priority: state.source_priority,
        // Phase F.13 chain_10000 Plan D E6 Substage 2 (2026-05-26):
        // arena-interned EdgeStackId (Copy u32) replaces Arc<Vec<GssEdgeId>>.
        incoming_edge_stack_id: shell.incoming_edge_stack_id,
        recovery_depth: shell.recovery_depth,
        // Phase F.13 Stage L4.1 (2026-05-25): Arc::clone (O(1)) — was
        // deep-clone pre-L4.1. The materialized cursor now shares the
        // shell's Arc'd cycle-defense sets; first per-cursor mutation
        // triggers Arc::make_mut copy-on-write.
        visited_recovery: shell.visited_recovery.clone(),
        visited_dispatch: shell.visited_dispatch.clone(),
        // Phase F.13 chain_10000 Plan D E3 Substage 2 (2026-05-26):
        // arena-interned StackId (Copy u32) replaces Arc<Vec<SppfId>>.
        sppf_stack_id: shell.sppf_stack_baseline_id,
        optional_scope_marks: (*shell.optional_scope_marks).clone(),
        binder_scope_marks: (*shell.binder_scope_marks).clone(),
        pending_packing_weight: state.pending_packing_weight.clone(),
        collection_stack_depth: shell.collection_depth,
        sppf_collection_arena: std::sync::Arc::clone(&shell.sppf_collection_arena),
        last_action_output_cat: state.last_action_output_cat,
        cohort_origin: shell.cohort_origin.clone(),
        cohort_revive_depth: state.cohort_revive_depth,
        lex_fork_path: std::sync::Arc::clone(&state.lex_fork_path),
    }
}

/// Phase F.13 Stage L3.2 (2026-05-25): hard cap on cohort frame member
/// count. L6 raises this from the H12 cap of 4. Defense-in-depth — the
/// lazy form should make 256 trivially affordable, but a runaway cohort
/// formation bug is preferable to OOM.
pub const MAX_COHORT_FRAME_MEMBERS: usize = 256;

/// Phase F.13 Stage L3.4 (2026-05-25): apply an `ObsInvariant`-class
/// action to a cohort frame's shell in-place. Returns `Ok(())` on
/// success (the cohort frame's shell mutated; all members observe the
/// change through the shared `Arc<CohortShell>`). Returns `Err(action)`
/// if the variant is not yet supported in this stage — caller falls
/// back to the L3.2 materialize-and-per-cursor-step path.
///
/// **L3.4 supported variants** (the conservative initial scope):
/// - `Advance(new_state)`: updates `shell.inner_state` via
///   `Arc::make_mut`. All members observe the new state without
///   per-member mutation.
///
/// All other variants — even those classified ObsInvariant by
/// `DivergenceClass::classify` (Accept/Error/Idle) — return `Err(action)`
/// at this stage. L3.4b will add terminal-state handling
/// (Accept/Error/Idle force materialization to surface cursor outcomes
/// in step_fanout's accounting) and L4 will add additional invariant
/// variants once Arc-shared cycle defense lets push/pop apply to shell
/// without per-member mutation.
pub fn apply_obs_invariant_to_shell<W: SemiringRef + Clone>(
    cf: &mut CohortFrame<W>,
    action: crate::wpda_walker::WpdaStepAction<W>,
) -> Result<(), crate::wpda_walker::WpdaStepAction<W>> {
    use crate::wpda_walker::WpdaStepAction;
    match action {
        WpdaStepAction::Advance(new_state) => {
            // Mutate the shell in-place. Arc::make_mut deep-clones the
            // shell if any other Arc holder exists; in the canonical
            // single-cohort-frame-per-key case, the shell is uniquely
            // referenced and Arc::make_mut is O(1).
            std::sync::Arc::make_mut(&mut cf.shell).inner_state = new_state;
            Ok(())
        }
        other => Err(other),
    }
}

/// Phase F.13 chain_10000 Exp 14 Substage 2 (2026-05-27): apply an
/// `ObsInvariantOverArcs` action to a Tomita frontier node's shell + all
/// arcs. Returns `Ok(())` on success; `Err(action)` on a variant not yet
/// supported in this stage (caller materializes each arc via
/// `materialize_branch_cursor` and falls through to per-cursor step).
///
/// Plan ref: `prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`
/// §3.2 (the per-frontier dispatch loop) and §3.4 (per-arc weight
/// aggregation).
///
/// **Substage 2 supported variants** (same conservative initial scope
/// as `apply_obs_invariant_to_shell`):
/// - `Advance(new_state)`: shell-mutate via `Arc::make_mut`; arcs
///   observe the new state without per-arc mutation.
///
/// Substage 4 will add Accept/Error/Idle terminal handling. Substage 5
/// will add Push/Pop/Replace/ConsumeAndPush (the chain-interior payoff)
/// with per-arc `weight ← weight ⊗ action.weight` broadcast inline.
pub fn apply_obs_invariant_to_frontier<W: SemiringRef + Clone>(
    node: &mut crate::tomita_frontier::FrontierNode<W>,
    action: crate::wpda_walker::WpdaStepAction<W>,
) -> Result<(), crate::wpda_walker::WpdaStepAction<W>> {
    use crate::wpda_walker::WpdaStepAction;
    match action {
        WpdaStepAction::Advance(new_state) => {
            // Single shell mutation. Per-arc state is unchanged.
            std::sync::Arc::make_mut(&mut node.shell).inner_state = new_state;
            Ok(())
        }
        other => Err(other),
    }
}

/// Phase F.13 Stage L3.2 (2026-05-25): consume a cohort frame and yield
/// one `Frame::Concrete(BranchCursor)` per member via
/// `materialize_branch_cursor`. This is the L3.2 step_cohort_frame
/// stub's primary primitive — and also the L3.6 forced-materialization
/// hook used at `merge_equivalent_cursors`, EOI, etc.
pub fn materialize_cohort_to_frames<W: SemiringRef + Clone>(
    cf: CohortFrame<W>,
) -> Vec<Frame<W>> {
    let shell = cf.shell;
    cf.members
        .into_iter()
        .map(|state| Frame::Concrete(materialize_branch_cursor(&shell, &state)))
        .collect()
}

impl<W: SemiringRef> CohortFrame<W> {
    /// Phase F.13 Stage L2 (2026-05-25): construct a fresh cohort
    /// frame at H12 first-member-register time. The shell is built
    /// from `parent` and shared across all subsequent members.
    pub fn new(shell: std::sync::Arc<CohortShell<W>>) -> Self {
        Self {
            shell,
            members: Vec::new(),
            dispatch_result: None,
        }
    }

    /// Append a member to the cohort. L2 invariant: all members must
    /// share the shell — caller is responsible for verifying
    /// `~_obs`-equivalence at the call site (via the H12 dispatch
    /// key equality).
    pub fn push_member(&mut self, member: CohortMemberState<W>) {
        self.members.push(member);
    }

    /// Member count.
    pub fn member_count(&self) -> usize {
        self.members.len()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::semiring::Semiring;
    use crate::wpda_runtime::{StackSymbolV2, WpdaState};
    use crate::wpda_walker::{TriggerMode, WpdaStepAction};

    fn ready() -> WpdaState {
        WpdaState::Ready { min_bp: 0 }
    }

    fn one() -> LexicographicWeight {
        <LexicographicWeight as Semiring>::one()
    }

    fn ret_sym() -> StackSymbolV2 {
        StackSymbolV2::return_symbol(0, 0)
    }

    #[test]
    fn classify_advance_is_invariant() {
        let action: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Advance(ready());
        assert_eq!(DivergenceClass::classify(&action), DivergenceClass::ObsInvariant);
    }

    #[test]
    fn classify_accept_error_idle_are_invariant() {
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Accept;
        let e: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Error("x".into());
        let i: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Idle;
        assert_eq!(DivergenceClass::classify(&a), DivergenceClass::ObsInvariant);
        assert_eq!(DivergenceClass::classify(&e), DivergenceClass::ObsInvariant);
        assert_eq!(DivergenceClass::classify(&i), DivergenceClass::ObsInvariant);
    }

    #[test]
    fn classify_push_is_divergent() {
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Push {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(DivergenceClass::classify(&a), DivergenceClass::ObsDivergent);
    }

    #[test]
    fn classify_pop_is_divergent() {
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Pop {
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(DivergenceClass::classify(&a), DivergenceClass::ObsDivergent);
    }

    #[test]
    fn classify_replace_is_divergent() {
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Replace {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(DivergenceClass::classify(&a), DivergenceClass::ObsDivergent);
    }

    #[test]
    fn classify_consume_family_is_divergent() {
        let c: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Consume {
            weight: one(),
            new_state: ready(),
        };
        let cp: WpdaStepAction<LexicographicWeight> = WpdaStepAction::ConsumeAndPush {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
            trigger_mode: TriggerMode::Discard,
        };
        let cpop: WpdaStepAction<LexicographicWeight> = WpdaStepAction::ConsumeAndPop {
            weight: one(),
            new_state: ready(),
        };
        let cr: WpdaStepAction<LexicographicWeight> = WpdaStepAction::ConsumeAndReplace {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        let cir: WpdaStepAction<LexicographicWeight> = WpdaStepAction::ConsumeIdentAndReplace {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
            start_scope: false,
        };
        for a in [&c, &cp, &cpop, &cr, &cir] {
            assert_eq!(DivergenceClass::classify(a), DivergenceClass::ObsDivergent);
        }
    }

    #[test]
    fn classify_fork_is_divergent() {
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Fork {
            branches: Vec::new(),
            consume_trigger: false,
        };
        assert_eq!(DivergenceClass::classify(&a), DivergenceClass::ObsDivergent);
    }

    #[test]
    fn classify_optgroup_family_is_divergent() {
        let abs: WpdaStepAction<LexicographicWeight> = WpdaStepAction::OptGroupAbsent {
            replace_symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        let fin: WpdaStepAction<LexicographicWeight> = WpdaStepAction::OptGroupFinalize {
            replace_symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(DivergenceClass::classify(&abs), DivergenceClass::ObsDivergent);
        assert_eq!(DivergenceClass::classify(&fin), DivergenceClass::ObsDivergent);
    }

    // ── Phase F.13 chain_10000 Exp 14 Substage 2 (2026-05-27): Tomita
    // per-arc classifier + apply tests. Substage 2 mirrors the conservative
    // initial-scope graduation of `classify` / `apply_obs_invariant_to_shell`.

    #[test]
    fn classify_for_tomita_advance_is_invariant_over_arcs() {
        use crate::tomita_frontier::TomitaDivergence;
        let action: WpdaStepAction<LexicographicWeight> =
            WpdaStepAction::Advance(ready());
        assert_eq!(
            DivergenceClass::classify_for_tomita(&action),
            TomitaDivergence::ObsInvariantOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_accept_error_idle_are_invariant() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Accept;
        let e: WpdaStepAction<LexicographicWeight> =
            WpdaStepAction::Error("x".into());
        let i: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Idle;
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsInvariantOverArcs,
        );
        assert_eq!(
            DivergenceClass::classify_for_tomita(&e),
            TomitaDivergence::ObsInvariantOverArcs,
        );
        assert_eq!(
            DivergenceClass::classify_for_tomita(&i),
            TomitaDivergence::ObsInvariantOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_push_is_divergent_over_arcs_at_substage_2() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Push {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsDivergentOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_pop_is_divergent_over_arcs_at_substage_2() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Pop {
            weight: one(),
            new_state: ready(),
        };
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsDivergentOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_fork_is_divergent_over_arcs() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::Fork {
            branches: Vec::new(),
            consume_trigger: false,
        };
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsDivergentOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_consume_and_push_is_divergent_over_arcs() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> = WpdaStepAction::ConsumeAndPush {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
            trigger_mode: TriggerMode::Discard,
        };
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsDivergentOverArcs,
        );
    }

    #[test]
    fn classify_for_tomita_iterative_chain_absorb_is_divergent_over_arcs() {
        use crate::tomita_frontier::TomitaDivergence;
        let a: WpdaStepAction<LexicographicWeight> =
            WpdaStepAction::IterativeChainAbsorb {
                symbol: ret_sym(),
                weight: one(),
                new_state: ready(),
            };
        assert_eq!(
            DivergenceClass::classify_for_tomita(&a),
            TomitaDivergence::ObsDivergentOverArcs,
        );
    }

    // Substage 1.5+2.5: tests updated to use TomitaShell (Option A
    // soundness fix) instead of CohortShell.

    fn fresh_tomita_shell() -> crate::tomita_frontier::TomitaShell<LexicographicWeight> {
        crate::tomita_frontier::TomitaShell {
            node: 0,
            pos: 0,
            inner_state: WpdaState::Ready { min_bp: 0 },
            incoming_edge_stack_id: crate::edge_stack_arena::EDGE_STACK_ID_ROOT,
            collection_depth: 0,
            dispatch_key: crate::dispatch_cohort::DispatchKey::new(0, 0, 0),
            sppf_stack_baseline_id: crate::sppf_stack_arena::STACK_ID_ROOT,
            recovery_depth: 0,
            _phantom: std::marker::PhantomData,
        }
    }

    fn fresh_frontier_arc() -> crate::tomita_frontier::FrontierArc<LexicographicWeight> {
        use std::sync::Arc;
        crate::tomita_frontier::FrontierArc::<LexicographicWeight>::new(
            one(),
            one(),
            crate::sppf_stack_arena::STACK_ID_ROOT,
            0,
            None,
            None,
            0,
            Arc::new(Vec::new()),
            0,
            0,
            0,
            Arc::new(Vec::new()),
            im::OrdSet::new(),
            im::OrdSet::new(),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
        )
    }

    #[test]
    fn apply_obs_invariant_to_frontier_advance_updates_shell() {
        use crate::tomita_frontier::FrontierNode;
        let shell = fresh_tomita_shell();
        let arc = fresh_frontier_arc();
        let mut node = FrontierNode::new(shell, arc, 0, 0);
        let new_state = WpdaState::PrefixDispatch { pos: 5, cur_bp: 3 };
        let result = apply_obs_invariant_to_frontier(
            &mut node,
            WpdaStepAction::<LexicographicWeight>::Advance(new_state.clone()),
        );
        assert!(result.is_ok());
        assert_eq!(node.shell.inner_state, new_state);
    }

    #[test]
    fn apply_obs_invariant_to_frontier_push_returns_err_at_substage_2() {
        use crate::tomita_frontier::FrontierNode;
        let shell = fresh_tomita_shell();
        let arc = fresh_frontier_arc();
        let mut node = FrontierNode::new(shell, arc, 0, 0);
        let action = WpdaStepAction::<LexicographicWeight>::Push {
            symbol: ret_sym(),
            weight: one(),
            new_state: ready(),
        };
        let result = apply_obs_invariant_to_frontier(&mut node, action.clone());
        assert!(result.is_err());
    }
}
