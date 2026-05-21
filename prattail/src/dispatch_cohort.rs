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

    /// Phase F.13 H12 Stage 1.2 (2026-05-21): Register a
    /// cross-cat-projection dispatch. Returns the outcome of the
    /// lookup so the caller (the Fork-arm Push branch) can record the
    /// appropriate counter increment.
    ///
    /// Stage 1.2 only WRITES — the outcome is not yet acted upon by
    /// the walker. Stage 1.3 will use the outcome to PAUSE cohort
    /// members and synthesize resumed singletons from Resolved
    /// entries.
    pub fn register(&mut self, key: DispatchKey) -> RegisterOutcome {
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
            Some(DispatchCacheEntry::Resolved { .. }) => {
                self.resolved_hits_total += 1;
                RegisterOutcome::ResolvedHit
            }
            Some(DispatchCacheEntry::Failed) => {
                self.failed_hits_total += 1;
                RegisterOutcome::FailedHit
            }
        }
    }

    /// Phase F.13 H12 Stage 1.2 (2026-05-21): Transition an `InFlight`
    /// entry to `Resolved`. Called from `apply_pop_body_to_cursor`
    /// when a CategoryEntry pop matches a CrossCatProjection edge.
    ///
    /// Returns the count of cohort members that were paused (Stage 1.3
    /// will revive them). Stage 1.2 ignores the return value; cohort
    /// members are not yet paused so the count is always 0.
    pub fn resolve(
        &mut self,
        key: DispatchKey,
        symbol_id: SppfId,
        hi_pos: u32,
        sub_weight: W,
    ) -> usize {
        match self.entries.get_mut(&key) {
            Some(entry @ DispatchCacheEntry::InFlight { .. }) => {
                let paused_count = match entry {
                    DispatchCacheEntry::InFlight {
                        pending_cohort, ..
                    } => pending_cohort.len(),
                    _ => 0,
                };
                *entry = DispatchCacheEntry::Resolved {
                    symbol_id,
                    hi_pos,
                    sub_weight,
                };
                self.resolved_total += 1;
                paused_count
            }
            _ => 0,
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

/// Phase F.13 H12 Stage 1.2 (2026-05-21): outcome of a `register`
/// call. The Fork-arm Push branch uses this to decide whether to:
///   - WorkerInserted: proceed normally (this cursor is the worker).
///   - InflightCollision: Stage 1.3 will PAUSE this cursor; Stage 1.2
///     ignores and lets the cursor proceed normally.
///   - ResolvedHit: Stage 1.3 will synthesize a resumed singleton
///     from the cached result; Stage 1.2 ignores and lets the cursor
///     proceed normally.
///   - FailedHit: Stage 1.3 will drop this cursor; Stage 1.2 ignores
///     and lets the cursor proceed normally (the sub-parse will fail
///     just as the original did).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegisterOutcome {
    WorkerInserted,
    InflightCollision,
    ResolvedHit,
    FailedHit,
}

impl<W: SemiringRef> Default for DispatchCohortCache<W> {
    fn default() -> Self {
        Self::new()
    }
}
