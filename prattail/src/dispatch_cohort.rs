//! Phase F.13 H12 — Tomita-GLR Dispatch-Cohort Sharing
//!
//! Mathematical foundation
//! =======================
//!
//! For two cursors `C₁, C₂` that both reach a `CrossCatDelegate
//! { source_src_idx = S, inner_cur_bp = B }` at the same `pos = P`:
//!
//! - The cursors carry distinct **return frames** (`incoming_edge_stack`,
//!   `binder_scope_marks`, pre-dispatch `sppf_stack`, `builder`, etc.).
//!   The H11a diagnostic measured 97.5% multi-discriminator divergence —
//!   the cursors really ARE in distinct parse states.
//! - BUT the work needed to compute `(SymbolId, hi_pos) = subparse(S, P, B)`
//!   is **identical** for both. Inspect
//!   `macros/src/gen/runtime/wpda_codegen/engine_impl.rs:1387-1394` —
//!   `engine.step(CrossCatDelegate { S, B }, …)` reads only `*S`,
//!   `*B`, and the inbound `_pos`. No cursor-local state is read.
//! - SPPF Symbol-dedup at `(nt, lo, hi)` (`prattail/src/sppf.rs:511-525`)
//!   is the formal output-identity witness: two cohort members that ran
//!   the sub-parse independently would produce the SAME `SppfId`.
//!
//! Therefore the sub-parse can be **shared**: run once, fan out the
//! result `(SppfId, hi_pos, sub_weight)` to ALL cohort members, each of
//! which then applies its distinct return frame `Rᵢ` independently.
//!
//! This is Tomita 1985 / Scott-Johnstone GLL 2010 in our notation. The
//! identical mathematical content already governs SPPF Symbol-dedup at
//! `(nt, lo, hi)` — but here we apply it to the **work** that *finds*
//! `(nt, lo, hi)`, not just the **output** that records it.
//!
//! Empirical motivation (chain_50, `walker-stats`)
//! ===============================================
//!
//! - `apply_action_calls = 2,036,307` (40,727× over ideal O(N) Pratt's 50).
//! - `cross_cat_branches = 1,543,396` — 88% of all forks; the dominant
//!   cost driver.
//! - Scaling exponent ≈ 2.62 (from chain_50/100/200 measurements).
//!
//! Predicted cohort entries ≈ `(num positions × num (S, B) pairs per pos)`
//! ≈ `50 × 3 = 150` (vs. 1,543,396 cross-cat branches) — a ~10⁴× collapse
//! of the dispatch frontier.
//!
//! Per-staging plan
//! ================
//!
//! See `prattail/docs/design/plans/phase-f13-algorithmic-cross-cat-cohort.md`.
//!
//! 1.1: scaffolding (this module) — types and field.
//! 1.2: write-only — populate cache; reads disabled.
//! 1.3: read path (4b: re-push CategoryEntry+Return on resume).
//! 1.4: read path optimization (4a: ghost-edge pop).
//! 1.5: ambiguity fanout (`Vec<(SppfId, hi_pos, W)>`).
//! 1.6: promote to default-on; delete the feature gate.

use crate::automata::semiring::SemiringRef;
use crate::sppf::SppfId;
use crate::wpda_runtime::WpdaState;

/// Cache key for cross-cat-projection dispatch sites. Mirrors the
/// payload of `WpdaState::CrossCatDelegate { source_src_idx,
/// inner_cur_bp }` together with the dispatch position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DispatchKey {
    /// The input position at which the cross-cat-projection dispatches.
    pub pos: u32,
    /// The category being projected into (target of the projection).
    pub source_src_idx: u16,
    /// The minimum binding power required of operators in the sub-parse.
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

/// State of a dispatch-cache entry. The first cohort member to reach a
/// `DispatchKey` becomes the **worker** and transitions the entry to
/// `InFlight`. Subsequent cohort members register as paused cohort
/// members. When the worker's sub-parse pops the `CategoryEntry(S)`
/// frame it pushed at dispatch, the entry transitions to `Resolved`
/// (or `Failed`) and paused members are revived.
pub enum DispatchCacheEntry<W: SemiringRef> {
    /// First cursor's sub-parse is in flight. Subsequent cohort members
    /// register here as paused; they are revived by `finalize_cohort`
    /// when the worker's sub-parse completes.
    InFlight {
        /// Number of cohort members registered so far (worker + paused).
        cohort_size: u32,
        /// Cohort members PAUSED at the dispatch site. The first cohort
        /// member (the worker) is NOT in this list — it is present in
        /// the walker's `branch_cursors`.
        pending_cohort: Vec<CohortMember<W>>,
    },
    /// Sub-parse complete. Subsequent cursors that hit this key
    /// synthesize a singleton resumed child from the cached result.
    Resolved {
        /// The SPPF symbol id the sub-parse produced. Identity-witnessed
        /// by `Sppf::intern_symbol((nt(source_src_idx), pos, hi_pos))`.
        symbol_id: SppfId,
        /// The input position after the sub-parse.
        hi_pos: u32,
        /// The weight delta from dispatch to pop. Combined with each
        /// cohort member's `weight_at_dispatch` at resume time so the
        /// final weight matches the per-cursor (pre-H12) bit-for-bit.
        sub_weight: W,
        /// The worker cursor's `inner_state` at the moment it emitted
        /// the Pop action (i.e., just before apply_pop_body_to_cursor
        /// transitioned it to the post-pop state). Cohort members at
        /// revive time inherit this state — the next walker step will
        /// re-emit the same Pop action, triggering the normal
        /// post-pop processing on the cohort member (action fire,
        /// splice into collection, etc.) — independent for each cohort
        /// member. SPPF Symbol-dedup makes the redundant intern calls
        /// idempotent under LexicographicWeight.
        worker_inner_state: WpdaState,
        /// Phase F.13 H12 Stage 1.3.1 (2026-05-21): the worker's
        /// `last_action_output_cat` at the moment of resolve. F.3b
        /// invariant (wpda_walker.rs:9651): this field is READ at
        /// `apply_pop_body_to_cursor`'s GroupingClosePreservingInner
        /// resolution as the inner_cat fallback. Cohort members
        /// MUST inherit the worker's post-sub-parse value — the
        /// cohort's pre-dispatch value differs (no fire fired) so
        /// post-pop state transitions would diverge. Identified by
        /// Plan agent analysis as the prime suspect for the float_cast_*
        /// failure family.
        worker_last_action_output_cat: Option<u16>,
        /// Phase F.13 H12 Stage 1.3.1 — worker's pending_packing_weight
        /// at pop time. Captures the residual weight after the
        /// sub-parse's emit_fire_action consumed pending_packing_weight
        /// (via mem::replace(_, W::one_ref())). Cohort member inherits.
        worker_pending_packing_weight: W,
        /// Phase F.13 H12 Stage 1.3.1 — worker's cumulative weight at
        /// pop time. Cohort member uses this directly (replacing its
        /// own weight_at_dispatch) because the sub-parse's weight
        /// contributions are encoded into the worker's cumulative
        /// weight.
        worker_weight: W,
    },
    /// Sub-parse failed (recovery dispatch exhausted, gauntlet-invalid
    /// input, etc.). All subsequent cohort members at this key drop
    /// without recurring the doomed sub-parse.
    Failed,
}

impl<W: SemiringRef> std::fmt::Debug for DispatchCacheEntry<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DispatchCacheEntry::InFlight {
                cohort_size,
                pending_cohort,
            } => f
                .debug_struct("InFlight")
                .field("cohort_size", cohort_size)
                .field("pending_cohort_len", &pending_cohort.len())
                .finish(),
            DispatchCacheEntry::Resolved {
                symbol_id, hi_pos, ..
            } => f
                .debug_struct("Resolved")
                .field("symbol_id", symbol_id)
                .field("hi_pos", hi_pos)
                .finish(),
            DispatchCacheEntry::Failed => f.write_str("Failed"),
        }
    }
}

/// A cohort member is a cursor that reached a `DispatchKey` while it
/// was `InFlight`. The cursor is removed from `walker.branch_cursors`
/// and stored here; on `Resolved`, the cursor is reconstituted with
/// the cached `(SppfId, hi_pos, sub_weight)` applied to its pre-dispatch
/// state.
pub struct CohortMember<W: SemiringRef> {
    /// The PAUSED cursor (snapshot taken at the dispatch site).
    /// Specifically, the cursor IS the return-frame: its sppf_stack,
    /// builder, incoming_edge_stack, binder_scope_marks, etc. are all
    /// the pre-sub-parse values — exactly the cursor that the
    /// per-cursor (pre-H12) path would have advanced through the
    /// sub-parse and then emerged from with the same `(SppfId, hi_pos)`.
    pub return_frame: crate::wpda_walker::BranchCursor<W>,
    /// The cursor's `weight` at dispatch time. The final weight after
    /// resume is `weight_at_dispatch.times_ref(&cached.sub_weight)`,
    /// matching the per-cursor path's left-fold order bit-for-bit.
    pub weight_at_dispatch: W,
}

impl<W: SemiringRef> std::fmt::Debug for CohortMember<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CohortMember").finish()
    }
}

/// Walker-global cohort cache. Lifecycle: created by `WpdaWalker::new`,
/// populated by the Fork-arm Push branch on `CrossCatDelegate`,
/// consumed at the matching pop in `apply_pop_body_to_cursor`, cleared
/// by `WpdaWalker::reset`.
///
/// Reset semantics: the cache is per-parse. SPPF SymbolIds are
/// per-parse too, so cross-parse reuse would be unsound.
pub struct DispatchCohortCache<W: SemiringRef> {
    /// Cache table. `FxHashMap` chosen for hash speed; the keys are
    /// dense integer tuples for which FxHash is the standard idiom in
    /// this codebase.
    pub entries: rustc_hash::FxHashMap<DispatchKey, DispatchCacheEntry<W>>,
    /// Total number of cross-cat-projection registrations seen.
    /// Increments on every Fork-arm Push of a CrossCatDelegate branch.
    pub registrations_total: u64,
    /// Registrations that found an existing `InFlight` entry — i.e.,
    /// COHORT collisions. Each such registration is a candidate for
    /// Tomita-GLR sharing (Stage 1.3 would PAUSE the cursor here).
    pub inflight_collisions_total: u64,
    /// Registrations that found an existing `Resolved` entry — Stage
    /// 1.3 would short-circuit the sub-parse (the result is already
    /// in the cache).
    pub resolved_hits_total: u64,
    /// Registrations that found an existing `Failed` entry — Stage 1.3
    /// would drop the cursor (the sub-parse is known to fail).
    pub failed_hits_total: u64,
    /// `InFlight` → `Resolved` transitions at the matching
    /// CategoryEntry pop.
    pub resolved_total: u64,
    /// `InFlight` → `Failed` transitions (sub-parse drop without a
    /// usable SPPF symbol).
    pub failed_total: u64,
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
    }

    /// Phase F.13 H12 Stage 1.2/1.3 (2026-05-21): Register a
    /// cross-cat-projection dispatch. The Fork-arm Push branch uses
    /// the returned `RegisterOutcome` to decide:
    ///   - WorkerInserted: allocate the worker child normally.
    ///   - InflightCollision: clone the parent, push into the entry's
    ///     pending_cohort via `pause_cohort_member`, DROP the would-be
    ///     child cursor (no append to the Fork's children Vec).
    ///   - ResolvedHit: short-circuit; synthesize a resumed child
    ///     immediately using the carried (symbol_id, hi_pos,
    ///     sub_weight, worker_inner_state).
    ///   - FailedHit: drop the cursor.
    pub fn register(&mut self, key: DispatchKey) -> RegisterOutcome<W> {
        self.registrations_total += 1;
        match self.entries.get_mut(&key) {
            None => {
                self.entries.insert(
                    key,
                    DispatchCacheEntry::InFlight {
                        cohort_size: 1,
                        pending_cohort: Vec::new(),
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
                sub_weight,
                worker_inner_state,
                worker_last_action_output_cat,
                worker_pending_packing_weight,
                worker_weight,
            }) => {
                self.resolved_hits_total += 1;
                RegisterOutcome::ResolvedHit {
                    symbol_id: *symbol_id,
                    hi_pos: *hi_pos,
                    sub_weight: sub_weight.clone(),
                    worker_inner_state: worker_inner_state.clone(),
                    worker_last_action_output_cat: *worker_last_action_output_cat,
                    worker_pending_packing_weight: worker_pending_packing_weight.clone(),
                    worker_weight: worker_weight.clone(),
                }
            }
            Some(DispatchCacheEntry::Failed) => {
                self.failed_hits_total += 1;
                RegisterOutcome::FailedHit
            }
        }
    }

    /// Phase F.13 H12 Stage 1.3 (2026-05-21): Transition an `InFlight`
    /// entry to `Resolved`, returning the paused cohort members for
    /// revive by the caller. Called from `cursor_gss_pop_via_edge`
    /// when a CategoryEntry pop matches a CrossCatProjection edge.
    ///
    /// Stage 1.3 caller responsibility: for each returned CohortMember,
    /// construct a revived BranchCursor (set pos=hi_pos, push symbol_id
    /// onto sppf_stack, re-push CategoryEntry(S) onto GSS so the next
    /// pop walks the normal post-pop path, restore inner_state to
    /// worker_inner_state) and add to walker.pending_cohort_revives.
    /// step_fanout drains pending_cohort_revives into new_cursors at
    /// end-of-step.
    pub fn resolve(
        &mut self,
        key: DispatchKey,
        symbol_id: SppfId,
        hi_pos: u32,
        sub_weight: W,
        worker_inner_state: WpdaState,
        worker_last_action_output_cat: Option<u16>,
        worker_pending_packing_weight: W,
        worker_weight: W,
    ) -> Vec<CohortMember<W>> {
        let entry = match self.entries.get_mut(&key) {
            Some(e) => e,
            None => return Vec::new(),
        };
        let pending = match entry {
            DispatchCacheEntry::InFlight { pending_cohort, .. } => {
                std::mem::take(pending_cohort)
            }
            _ => return Vec::new(),
        };
        *entry = DispatchCacheEntry::Resolved {
            symbol_id,
            hi_pos,
            sub_weight,
            worker_inner_state,
            worker_last_action_output_cat,
            worker_pending_packing_weight,
            worker_weight,
        };
        self.resolved_total += 1;
        pending
    }

    /// Phase F.13 H12 Stage 1.3 (2026-05-21): clone a cohort member
    /// onto the InFlight entry's `pending_cohort` for later revive at
    /// resolve(). No-op if the entry is not InFlight (returns false).
    pub fn pause_cohort_member(
        &mut self,
        key: DispatchKey,
        member: CohortMember<W>,
    ) -> bool {
        match self.entries.get_mut(&key) {
            Some(DispatchCacheEntry::InFlight { pending_cohort, .. }) => {
                pending_cohort.push(member);
                true
            }
            _ => false,
        }
    }

    /// Phase F.13 H12 Stage 1.3 (2026-05-21): read a Resolved entry's
    /// data for synthesizing a resumed child immediately (the
    /// ResolvedHit path — cursor arrives AFTER the worker has resolved).
    /// Returns None if the entry is not Resolved.
    pub fn get_resolved(
        &self,
        key: &DispatchKey,
    ) -> Option<(SppfId, u32, &W, &WpdaState, Option<u16>, &W, &W)> {
        match self.entries.get(key) {
            Some(DispatchCacheEntry::Resolved {
                symbol_id,
                hi_pos,
                sub_weight,
                worker_inner_state,
                worker_last_action_output_cat,
                worker_pending_packing_weight,
                worker_weight,
            }) => Some((
                *symbol_id,
                *hi_pos,
                sub_weight,
                worker_inner_state,
                *worker_last_action_output_cat,
                worker_pending_packing_weight,
                worker_weight,
            )),
            _ => None,
        }
    }

    /// Phase F.13 H12 Stage 1.2 (2026-05-21): Transition an `InFlight`
    /// entry to `Failed`. Reserved for sub-parse drop paths in Stage
    /// 1.3; unused in Stage 1.2.
    #[allow(dead_code)]
    pub fn fail(&mut self, key: DispatchKey) {
        if let Some(entry @ DispatchCacheEntry::InFlight { .. }) =
            self.entries.get_mut(&key)
        {
            *entry = DispatchCacheEntry::Failed;
            self.failed_total += 1;
        }
    }

    /// Phase F.13 H12 Stage 1.2 (2026-05-21): Diagnostic summary for
    /// the `PRATTAIL_WALKER_STATS=1` print path. Mirrors the
    /// `walker_stats::WalkerStats` Display impl style.
    pub fn write_summary(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let collisions_ratio = if self.registrations_total > 0 {
            (self.inflight_collisions_total as f64) * 100.0
                / (self.registrations_total as f64)
        } else {
            0.0
        };
        writeln!(
            f,
            "═══ DISPATCH-COHORT CACHE STATS ═══"
        )?;
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
            "  resolved_transitions={}  failed_transitions={}  cache_entries={}",
            self.resolved_total,
            self.failed_total,
            self.entries.len(),
        )?;
        Ok(())
    }
}

/// Phase F.13 H12 Stage 1.2/1.3 (2026-05-21): outcome of a `register`
/// call. The Fork-arm Push branch uses this to decide whether to
/// proceed normally, pause, synthesize a resumed child, or drop.
pub enum RegisterOutcome<W: SemiringRef> {
    /// First cursor at this key. Proceed normally to allocate the
    /// worker child.
    WorkerInserted,
    /// Existing InFlight entry. Pause this cursor: clone parent into
    /// the entry's pending_cohort, DROP the would-be child.
    InflightCollision,
    /// Existing Resolved entry. Synthesize a resumed child
    /// immediately using the carried sub-parse result data.
    ResolvedHit {
        symbol_id: SppfId,
        hi_pos: u32,
        sub_weight: W,
        worker_inner_state: WpdaState,
        worker_last_action_output_cat: Option<u16>,
        worker_pending_packing_weight: W,
        worker_weight: W,
    },
    /// Existing Failed entry. Drop the cursor — the sub-parse is
    /// known to fail.
    FailedHit,
}

impl<W: SemiringRef> Default for DispatchCohortCache<W> {
    fn default() -> Self {
        Self::new()
    }
}
