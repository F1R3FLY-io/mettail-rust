//! Phase F.13 (2026-05-20): walker statistics counters for algorithmic-
//! bottleneck attribution.
//!
//! Empirical context: AMD uProf call-graph analysis of
//! `test_right_assoc_chain_100` at tip `9108cfb` showed
//! `apply_action_to_cursor` consumed 71.7% of parse time across an
//! estimated ~10,000 invocations. The bottleneck is invocation COUNT,
//! not per-call cost. Chain scaling exponent ~2.62 — super-quadratic.
//!
//! These counters establish the exact numbers behind the estimate:
//! - How many `apply_action_to_cursor` calls actually fire per parse?
//! - How many cursors proliferate at peak?
//! - How effective is `merge_equivalent_cursors` (collapse ratio)?
//! - Where do cursors come from (seed/fork) and where do they die
//!   (resolution check / explicit drop / outcome drop / merge)?
//! - Which Fork dispatch kinds dominate the Fork count?
//!
//! With these numbers we can design the next algorithmic hypothesis
//! from empirical data instead of inference.
//!
//! ## Zero-cost when disabled
//!
//! Both this module's struct field on `WpdaWalker` AND the increment
//! macros are gated by `#[cfg(feature = "walker-stats")]`. When the
//! feature is off, macros expand to empty blocks and the field doesn't
//! exist. Verified with `cargo expand --release -p mettail-prattail`.
//!
//! ## Per-walker scoping
//!
//! Counters live on the `WpdaWalker` struct (not in a global / thread-
//! local). This eliminates parallel-test interference automatically:
//! each parse session owns its counters. No atomics, no mutexes — the
//! walker is single-threaded per session and `apply_action_to_cursor`
//! always borrows `&mut self`.
//!
//! ## Output
//!
//! Set environment variable `PRATTAIL_WALKER_STATS=1` before running.
//! At each `resolve_at_end_of_input` the walker prints a human-readable
//! summary to stderr via `Display` impl. Pattern matches the
//! `PRATTAIL_HANG_DUMP` env-var precedent in `hang_dump.rs`.

use std::fmt;

/// Walker statistics — 19 u64 counters tracking invocation count,
/// cursor proliferation, merge effectiveness, lifecycle, and Fork
/// composition.
///
/// All counters monotonically increment except `branch_cursors_peak_*`
/// which use max-update. `Default` produces all zeros.
#[derive(Default, Debug, Clone)]
pub struct WalkerStats {
    // ── Invocation / cost ─────────────────────────────────────────────
    /// Per-cursor `apply_action_to_cursor` calls. Confirms the ~10,000
    /// estimate for chain_100 and gives the exact scaling slope for
    /// chain_50/100/200.
    pub apply_action_calls: u64,
    /// `step_fanout` outer-loop iterations (one per parse step).
    /// Ratio `apply_action_calls / step_fanout_calls` = average
    /// cursors-per-step.
    pub step_fanout_calls: u64,
    /// Peak `branch_cursors.len()` BEFORE `merge_equivalent_cursors`
    /// runs. Captures the pre-merge cursor frontier size.
    pub branch_cursors_peak_pre_merge: u64,
    /// Peak `branch_cursors.len()` AFTER `merge_equivalent_cursors`
    /// runs. Difference vs pre-merge = number of cursors collapsed at
    /// peak.
    pub branch_cursors_peak_post_merge: u64,
    /// Running sum of `branch_cursors.len()` at each step entry.
    /// Average = `branch_cursors_sum / step_fanout_calls`.
    pub branch_cursors_sum: u64,

    // ── Merge effectiveness ───────────────────────────────────────────
    /// Total cursors considered for merge (running sum of input cursor
    /// count to each `merge_equivalent_cursors` invocation).
    pub merge_attempts_total: u64,
    /// Total cursors COLLAPSED by merge (one increment per Entry::Occupied
    /// hit). Ratio `merge_collapses_total / merge_attempts_total` =
    /// collapse rate. Low = ConfigKey too narrow.
    pub merge_collapses_total: u64,

    // ── Cursor lifecycle: sources ─────────────────────────────────────
    /// Cursors created by walker constructors + reset (always 1 per parse).
    pub cursors_created_via_seed: u64,
    /// Cursors created as Fork-arm children. Dominant source under
    /// chain-parsing.
    pub cursors_created_via_fork: u64,

    // ── Cursor lifecycle: sinks ───────────────────────────────────────
    /// Cursors dropped in `cursor_resolution_check` when transitioning
    /// to `WpdaState::Error`. NOT WIRED in first iteration —
    /// cursor_resolution_check has `&self` signature, would require
    /// breaking change to count here. The Drop is still captured in
    /// `cursors_dropped_via_outcome_drop` below (which counts ALL Drops
    /// reaching step_fanout's outcome handler).
    pub cursors_dropped_via_resolution_check: u64,
    /// Cursors dropped via `return CursorOutcome::Drop` inside
    /// `apply_action_to_cursor` (B12 / B14 / recovery cycle defenses).
    /// NOT WIRED in first iteration — 5 sites would require individual
    /// increments. Still captured in `cursors_dropped_via_outcome_drop`.
    pub cursors_dropped_via_explicit_drop: u64,
    /// Cursors dropped via the `CursorOutcome::Drop` arm at
    /// `step_fanout` (catches ALL Drops — from resolution_check + from
    /// explicit return in apply_action_to_cursor). This is the
    /// authoritative cursor-death counter in the first iteration.
    pub cursors_dropped_via_outcome_drop: u64,
    /// Cursors absorbed by `merge_equivalent_cursors`. Same source as
    /// `merge_collapses_total`; tracked separately for lifecycle
    /// conservation check (sum of sinks ≈ sum of sources).
    pub cursors_dropped_via_merge: u64,

    // ── Fork composition ──────────────────────────────────────────────
    /// Total `WpdaStepAction::Fork` firings.
    pub fork_total: u64,
    /// Branches with `ForkActionKind::Push` (cross-cat-projection
    /// dispatch family).
    pub fork_kind_push: u64,
    /// Branches with `ForkActionKind::OptGroupAbsent` (Optional Group
    /// SKIP arm).
    pub fork_kind_opt_group_absent: u64,
    /// Branches with any `LexAlt*` family (LexAlt, LexAltPrefixOp,
    /// LexAltPostfixOp, LexAltInfixOp, LexAltMixfixOp).
    pub fork_kind_lex_alt_family: u64,
    /// Branches with any `Consume*` / `ConsumeAndReplace*` family
    /// (terminal-consuming).
    pub fork_kind_consume_family: u64,
    /// Branches with other ForkActionKind variants (Pop /
    /// ReplaceAndPush / GuardedConsume* / etc.).
    pub fork_kind_other: u64,
    /// Recovery-typed Fork dispatches (where `is_recovery == true`).
    /// Distinguishes recovery Forks from grammar Forks in the total.
    pub fork_recovery_dispatches: u64,
    /// Branches whose `new_state` is `WpdaState::CrossCatDelegate { .. }`.
    /// Confirms cross-cat projection as the dominant Fork-branch source.
    pub fork_cross_cat_projection_branches: u64,

    // ── Phase F.13 chain_10000 Exp 10 Substage 0-bis (2026-05-26):
    //     sole-diff outlier downstream-context classification ─────
    /// Per-context breakdown of `node_only` sole-diff cases (cursor A
    /// and B differ ONLY in `node`, edge same, etc.). Indices:
    /// 0=cohort_origin.is_some(), 1=InfixLoop state, 2=recovery_depth>0,
    /// 3=other. Sum across indices ≤ `merge_miss_node_diff_total`
    /// (multi-context overlap is double-counted under first-match
    /// rule: classify cohort first, then InfixLoop, then recovery,
    /// else other). Per Exp 10 S0-bis: if a single context dominates
    /// (≥ 80 % of node_only outliers), Exp 10 S1-bis could drop the
    /// edge axis ONLY for that context (per-state ConfigKey).
    pub merge_miss_node_only_by_context: [u64; 4],
    /// Same shape as `merge_miss_node_only_by_context`, for the
    /// symmetric `edge_only` sole-diff case (edge differs but node
    /// matches — the inverse outlier).
    pub merge_miss_edge_only_by_context: [u64; 4],

    // ── Phase F.13 chain_10000 Plan D E4 Substage 1.a (2026-05-26):
    //     Streaming SPPF reclamation-window measurement ──────────────
    /// Number of step_fanout iterations at which the reclamation
    /// window was sampled. Denominator for the histograms below.
    pub sppf_reclaim_window_samples: u64,
    /// Number of step_fanout iterations at which the cohort cache
    /// pinned the SPPF lower-bound position (cache_min < frontier_min).
    /// Per Plan agent: this is the load-bearing diagnostic — if the
    /// cohort cache pins low positions, the SPPF reclamation window
    /// is bounded above by `min over cache_entry of symbol_id.lo_pos`,
    /// not by the cursor frontier.
    pub sppf_reclaim_cache_pinned_samples: u64,
    /// Maximum observed `(frontier_min - cache_min)` gap. When the
    /// cohort cache pins, this is the size of the lost reclamation
    /// opportunity (positions that COULD have been released if the
    /// cache hadn't held them).
    pub sppf_reclaim_cache_pin_gap_max: u64,
    /// Bucketed histogram of the reclamation window size relative to
    /// the chain length. Buckets index by
    /// `(min_referenced_pos / max(chain_len, 1)) * 16`, clamped to
    /// `[0, 15]`. Bucket 0 = window 0-6.25 % (effectively no reclaim);
    /// bucket 15 = 93.75-100 % (entire input reclaimable).
    pub sppf_reclaim_window_histogram: [u64; 16],
    /// Bucketed histogram of fraction of Symbol nodes whose
    /// `hi_pos < min_referenced_pos` (reclaim candidates). 10 buckets
    /// of 10 % each. Per Plan agent gate: PROCEED to S1.b iff
    /// reclaim-candidate fraction ≥ 50 % on chain_1000 (buckets 5-9).
    pub sppf_reclaimable_nodes_pct_histogram: [u64; 10],
    /// Maximum observed Symbol node count at any step_fanout sample
    /// (denominator context for the candidate fraction).
    pub sppf_reclaim_symbol_count_max: u64,

    // ── Phase F.13 chain_10000 Exp 13 Substage 0 (2026-05-26):
    //     iterative chain-region length tracker ─────────────────────
    /// Total iterations of the `IterativeChainAbsorb` arm where
    /// `already_chained == true`. Per Plan agent: gate fires iff
    /// `chain_region_iterations` is large enough on chain_1000 that
    /// the iterative path covers > 100 elements (≥ 100 iterations).
    /// Used by Exp 13 S0 to decide whether Earley + Leo outboard
    /// chain-region delegation would add value vs the existing
    /// iterative path that already captures the per-iteration win.
    pub chain_region_iterations: u64,

    // ── Phase F.13 chain_10000 Exp 11 Substage 0 (2026-05-26):
    //     per-class Fork breakdown gate ──────────────────────────────
    /// Per-class Fork firing count. Indices: 0=lex_fork (any LexAlt*
    /// family branch present), 1=implicit_cast (CrossCatDelegate with
    /// `BP_TIER_PASS2C_SYNTHESIZED` weight), 2=h12_cross_cat
    /// (CrossCatDelegate non-pass-2c), 3=other. A Fork firing
    /// increments the class of its dominant branch (first-encountered
    /// class wins). Used by the Exp 11 Substage 0 gate:
    /// proceed iff `(lex_fork + implicit_cast) / fork_total > 0.30`
    /// AND `avg_fanout(lex) + avg_fanout(cast) > 2.0`.
    pub fork_total_by_class: [u64; 4],
    /// Sum of branches.len() across Fork firings classified into each
    /// class. Average fanout-cardinality per class = entry /
    /// `fork_total_by_class[c]`.
    pub fork_branches_by_class: [u64; 4],

    // ── F.13 H11a diagnostic: merge-miss pair sampling ─────────────────
    /// Total intra-`pos` pairs sampled by the diagnostic pass (denominator
    /// for the merge-miss breakdown ratios).
    pub merge_miss_pairs_considered_total: u64,
    /// Pairs that differ on ONLY `state` (other 3 discriminators match).
    pub merge_miss_state_diff_total: u64,
    /// Pairs that differ on ONLY `node` (other 3 discriminators match).
    pub merge_miss_node_diff_total: u64,
    /// Pairs that differ on ONLY `incoming_edge` (other 3 discriminators match).
    pub merge_miss_edge_diff_total: u64,
    /// Pairs that differ on ONLY `collection_depth` (other 3 discriminators match).
    pub merge_miss_depth_diff_total: u64,
    /// Pairs that differ on ≥ 2 discriminators (multi-axis divergence).
    pub merge_miss_multi_diff_total: u64,

    // ── F.13 H11b diagnostic: cross-cat census ─────────────────────────
    /// Number of cross-cat Fork branches that would be filtered by H11b's
    /// dispatch_branch_seen mechanism (i.e., branches whose target
    /// `(source_cat, pos, inner_bp)` was already emitted by an earlier
    /// cursor at this dispatch site).
    pub fork_branches_dropped_pre_emit: u64,
    /// Number of cross-cat Fork branches whose target `(cat, pos)` already
    /// has at least one SPPF Symbol interned. Coarser signal than
    /// `dropped_pre_emit` — confirms structural redundancy.
    pub fork_target_symbol_already_in_sppf: u64,

    // ── F.13 H13 Step 0 diagnostic: edge-kind-relaxed merge would-merge ──
    /// Number of merge-miss pairs (intra-`pos`, multi-discriminator) whose
    /// `incoming_edge_stack.last()` differs by `GssEdgeId` but would
    /// match under the H13 EdgeKind-relaxed equivalence. If this count
    /// is ≥ 60% of `merge_miss_pairs_considered_total`, H13 Step 2
    /// (actual merge relaxation) is justified. Otherwise H13 is REJECTED.
    pub merge_miss_pairs_edge_kind_equivalent: u64,

    // ── F.13 Stage 3.A (2026-05-23): 7-axis sole-cause attribution ──
    // The legacy `merge_miss_*_diff_total` counters above cover only the
    // original 4 ConfigKey axes (state, node, edge, depth). ConfigKey
    // has grown to 11 fields; the 7 newer ones (cohort_origin, sppf_top,
    // lex_alt_idx, weight_src_idx, weight_rule_idx, lex_fork_stamp) all
    // landed in `merge_miss_multi_diff_total` regardless of which truly
    // differs. These 7 sole-cause counters partition the previous
    // catch-all and let us rank the actual dominant under-merging axis.
    /// Pairs that differ on ONLY `cohort_origin`.
    pub merge_miss_cohort_origin_diff_total: u64,
    /// Pairs that differ on ONLY `sppf_top` (= `sppf_stack.last()`).
    pub merge_miss_sppf_top_diff_total: u64,
    /// Pairs that differ on ONLY `weight.lex_alt_idx`.
    pub merge_miss_lex_alt_idx_diff_total: u64,
    /// Pairs that differ on ONLY `weight.lex_src_idx`.
    pub merge_miss_weight_src_idx_diff_total: u64,
    /// Pairs that differ on ONLY `weight.lex_rule_idx`.
    pub merge_miss_weight_rule_idx_diff_total: u64,
    /// Pairs that differ on ONLY `lex_fork_path.last()` (= LexForkStamp).
    pub merge_miss_lex_fork_stamp_diff_total: u64,

    // ── F.13 Stage 3.A: Lead #1 `(pred, EdgeKind)`-equivalence ─────────
    /// Pairs whose `incoming_edge_stack.last()` differs by `GssEdgeId`
    /// AND on no other axis, but whose underlying
    /// `(predecessor_node, EdgeKind)` projection MATCHES. This is the
    /// would-merge count for Lead #1 (EdgeKind-class incoming_edge).
    /// Strictly finer than `merge_miss_pairs_edge_kind_equivalent`
    /// (H13's kind-only) because it preserves predecessor-frame
    /// identity. If this ratio over `merge_miss_pairs_considered_total`
    /// is ≥ 40 %, Lead #1 is justified.
    pub merge_miss_pairs_pred_edge_class_equivalent: u64,

    // ── F.13 Stage 3.A: per-axis multi-diff participation ──────────────
    /// Of the pairs in `merge_miss_multi_diff_total`, how many had each
    /// axis as ONE OF the differing fields. Indexed as: 0=state,
    /// 1=node, 2=edge, 3=collection_depth, 4=cohort_origin, 5=sppf_top,
    /// 6=lex_alt_idx, 7=weight_src_idx, 8=weight_rule_idx,
    /// 9=lex_fork_stamp. Sums over the 10 indices may exceed
    /// `merge_miss_multi_diff_total` (each multi-diff pair contributes
    /// to multiple indices).
    pub merge_miss_multi_participation: [u64; 10],

    // ── Phase F.13 chain_10000 Plan C Substage 0 (2026-05-26) ─────────
    // Read-only length-histogram instrumentation for the two
    // BranchCursor fields targeted by Plan C's SmallVec experiment
    // (Substage 1). Sampled in `step_fanout` per-cursor; informs the
    // inline `N` sizing for `SmallVec<[T; N]>` so the spill threshold
    // covers ≥ 99 % of cursors. Buckets: indices 0..=7 correspond to
    // length ranges {0, 1, 2, 4, 8, 16, 32, 64+} via
    // `histogram_bucket_index`.
    /// Per-cursor `incoming_edge_stack.len()` distribution across all
    /// step_fanout sampling points. The chain-10000 ceiling-lift plan
    /// needs the p99 of this distribution to choose SmallVec N.
    pub incoming_edge_stack_len_histogram: [u64; 8],
    /// Maximum observed `incoming_edge_stack.len()` across all sample
    /// points. Caps the histogram's right tail interpretation.
    pub incoming_edge_stack_len_max: u64,
    /// Sample count for `incoming_edge_stack` histogram (the divisor
    /// to compute per-bucket fractions).
    pub incoming_edge_stack_len_samples: u64,
    /// Same as above for `recovery_deltas.len()`.
    pub recovery_deltas_len_histogram: [u64; 8],
    pub recovery_deltas_len_max: u64,
    pub recovery_deltas_len_samples: u64,
    /// Phase F.13 chain_10000 Exp 5 Substage 0 (2026-05-26):
    /// histogram gate for the Plan B CursorId-keyed pilot on
    /// `visited_dispatch`. Plan B agent recommended this gate
    /// (mirroring Plan C Substage 0) to empirically confirm whether
    /// the field's typical size justifies the walker-global HashMap
    /// refactor cost. If chain max ≤ 4, pilot SKIPPED — no
    /// allocation to save. If max > 16, pilot proceeds.
    pub visited_dispatch_len_histogram: [u64; 8],
    pub visited_dispatch_len_max: u64,
    pub visited_dispatch_len_samples: u64,
    pub visited_recovery_len_histogram: [u64; 8],
    pub visited_recovery_len_max: u64,
    pub visited_recovery_len_samples: u64,
    /// Phase F.13 chain_10000 Exp 10 Substage 0 (2026-05-26):
    /// ConfigKey discriminator pairwise correlation matrix. The
    /// 10-axis ConfigKey (state, node, edge, depth, cohort_origin,
    /// sppf_top, lex_alt_idx, weight_src_idx, weight_rule_idx,
    /// lex_fork_stamp) was accreted across regressions; some axes
    /// likely correlate (e.g., lex_fork_stamp ↔ lex_alt_idx). For a
    /// merge-miss pair that diverges on multiple axes, record which
    /// PAIRS of axes both contribute. Stored as a flat
    /// lower-triangular array indexed as `lower_triangle_index(i, j)`
    /// where i < j ∈ 0..10. Per the Plan agent (Exp 10 design): a
    /// pair (i, j) with co-occurrence rate > 0.95 on chain_1000 AND
    /// axis-i sole-diff < 1% indicates axis i is dominated by axis j
    /// and is a drop-candidate from ConfigKey.
    pub merge_miss_pair_participation: PairCounts,
    /// Phase F.13 chain_10000 Exp 12 Substage 0 (2026-05-26):
    /// length histograms for `binder_scope_marks` and
    /// `optional_scope_marks` — gate the path-tree-arena migration
    /// per Plan agent Exp 12 design. If chain_1000 max ≤ 8 or
    /// mean ≤ 2 (histogram mostly empty/single-element), SKIP the
    /// arena migration; if max > 8 AND mean > 2, proceed to S1.
    pub binder_scope_marks_len_histogram: [u64; 8],
    pub binder_scope_marks_len_max: u64,
    pub binder_scope_marks_len_samples: u64,
    pub optional_scope_marks_len_histogram: [u64; 8],
    pub optional_scope_marks_len_max: u64,
    pub optional_scope_marks_len_samples: u64,
    /// Phase F.13 chain_10000 Exp 12 Substage 0 (2026-05-26):
    /// per-binder-scope inner `Vec<String>` (`names`) size histogram.
    /// Path-tree-arena dedups the OUTER Vec<(u16, Vec<String>)>;
    /// the inner Vec<String> per frame is still per-cursor allocated.
    /// If median inner-Vec size > 4, the arena win is diminished —
    /// inner Vec dominates per-frame cost.
    pub binder_scope_names_len_histogram: [u64; 8],
    pub binder_scope_names_len_max: u64,
    pub binder_scope_names_len_samples: u64,
}

/// Phase F.13 chain_10000 Exp 10 Substage 0 (2026-05-26): wrapper
/// over `[u64; 45]` for the ConfigKey pairwise correlation matrix.
/// Newtype required because `[T; N]` only implements `Default` for
/// N ≤ 32 in stable Rust; 45 = C(10, 2) for the 10 ConfigKey axes.
#[derive(Debug, Clone)]
pub struct PairCounts(pub [u64; 45]);

impl Default for PairCounts {
    fn default() -> Self {
        PairCounts([0; 45])
    }
}

impl std::ops::Index<usize> for PairCounts {
    type Output = u64;
    fn index(&self, i: usize) -> &u64 {
        &self.0[i]
    }
}

impl std::ops::IndexMut<usize> for PairCounts {
    fn index_mut(&mut self, i: usize) -> &mut u64 {
        &mut self.0[i]
    }
}

/// Phase F.13 chain_10000 Exp 10 Substage 0 (2026-05-26): map
/// `(i, j)` with `i < j ∈ 0..10` to a flat index in `0..45`. The
/// inverse `merge_miss_pair_participation[lower_triangle_index(i, j)]`
/// is the co-divergence count for axis pair (i, j).
pub fn lower_triangle_index(i: usize, j: usize) -> usize {
    debug_assert!(i < j && j < 10, "expected i<j<10, got ({}, {})", i, j);
    // Number of pairs with smaller first index, plus offset within row.
    // Row i has (9 - i) entries: (i, i+1), (i, i+2), ..., (i, 9).
    // Cumulative before row i: sum_{k=0}^{i-1} (9 - k) = 9i - i(i-1)/2.
    let row_start = 9 * i - i * (i.saturating_sub(1)) / 2;
    row_start + (j - i - 1)
}

/// Phase F.13 chain_10000 Plan C Substage 0 (2026-05-26): histogram
/// bucket index for a non-negative length value. Power-of-two ish
/// bucketing: {0, 1, 2, 4, 8, 16, 32, 64+}.
///
/// Returns an index in 0..8.
pub fn histogram_bucket_index(len: usize) -> usize {
    match len {
        0 => 0,
        1 => 1,
        2..=3 => 2,
        4..=7 => 3,
        8..=15 => 4,
        16..=31 => 5,
        32..=63 => 6,
        _ => 7, // 64+
    }
}

impl WalkerStats {
    /// Effective number of average cursors per step.
    pub fn avg_cursors_per_step(&self) -> f64 {
        if self.step_fanout_calls == 0 {
            0.0
        } else {
            self.branch_cursors_sum as f64 / self.step_fanout_calls as f64
        }
    }

    /// Merge collapse ratio (0.0–1.0). 1.0 = every considered cursor
    /// gets merged (rare). 0.0 = merge collapses nothing (ConfigKey
    /// too narrow).
    pub fn merge_collapse_ratio(&self) -> f64 {
        if self.merge_attempts_total == 0 {
            0.0
        } else {
            self.merge_collapses_total as f64 / self.merge_attempts_total as f64
        }
    }
}

impl fmt::Display for WalkerStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "═══ PRATTAIL WALKER STATS ═══")?;
        writeln!(
            f,
            "  apply_action_calls={}  step_fanout_calls={}  avg_cursors_per_step={:.2}",
            self.apply_action_calls,
            self.step_fanout_calls,
            self.avg_cursors_per_step(),
        )?;
        writeln!(
            f,
            "  branch_cursors_peak_pre_merge={}  post_merge={}  sum={}",
            self.branch_cursors_peak_pre_merge,
            self.branch_cursors_peak_post_merge,
            self.branch_cursors_sum,
        )?;
        writeln!(
            f,
            "  merge_attempts={}  merge_collapses={}  collapse_ratio={:.3}",
            self.merge_attempts_total,
            self.merge_collapses_total,
            self.merge_collapse_ratio(),
        )?;
        writeln!(
            f,
            "  cursors_created: seed={} fork={} → total={}",
            self.cursors_created_via_seed,
            self.cursors_created_via_fork,
            self.cursors_created_via_seed + self.cursors_created_via_fork,
        )?;
        writeln!(
            f,
            "  cursors_dropped: resolution={} explicit={} outcome={} merge={}",
            self.cursors_dropped_via_resolution_check,
            self.cursors_dropped_via_explicit_drop,
            self.cursors_dropped_via_outcome_drop,
            self.cursors_dropped_via_merge,
        )?;
        writeln!(
            f,
            "  fork_total={}  recovery_dispatches={}  cross_cat_branches={}",
            self.fork_total,
            self.fork_recovery_dispatches,
            self.fork_cross_cat_projection_branches,
        )?;
        writeln!(
            f,
            "  fork_kinds: push={} opt_group_absent={} lex_alt={} consume={} other={}",
            self.fork_kind_push,
            self.fork_kind_opt_group_absent,
            self.fork_kind_lex_alt_family,
            self.fork_kind_consume_family,
            self.fork_kind_other,
        )?;
        // Phase F.13 chain_10000 Exp 10 S0-bis (2026-05-26).
        let node_only_total: u64 =
            self.merge_miss_node_only_by_context.iter().sum();
        if node_only_total > 0 {
            let d = node_only_total as f64;
            writeln!(
                f,
                "  merge_miss_node_only_by_context: cohort_revive={} ({:.1}%) infix_loop={} ({:.1}%) recovery={} ({:.1}%) other={} ({:.1}%)",
                self.merge_miss_node_only_by_context[0],
                100.0 * self.merge_miss_node_only_by_context[0] as f64 / d,
                self.merge_miss_node_only_by_context[1],
                100.0 * self.merge_miss_node_only_by_context[1] as f64 / d,
                self.merge_miss_node_only_by_context[2],
                100.0 * self.merge_miss_node_only_by_context[2] as f64 / d,
                self.merge_miss_node_only_by_context[3],
                100.0 * self.merge_miss_node_only_by_context[3] as f64 / d,
            )?;
        }
        let edge_only_total: u64 =
            self.merge_miss_edge_only_by_context.iter().sum();
        if edge_only_total > 0 {
            let d = edge_only_total as f64;
            writeln!(
                f,
                "  merge_miss_edge_only_by_context: cohort_revive={} ({:.1}%) infix_loop={} ({:.1}%) recovery={} ({:.1}%) other={} ({:.1}%)",
                self.merge_miss_edge_only_by_context[0],
                100.0 * self.merge_miss_edge_only_by_context[0] as f64 / d,
                self.merge_miss_edge_only_by_context[1],
                100.0 * self.merge_miss_edge_only_by_context[1] as f64 / d,
                self.merge_miss_edge_only_by_context[2],
                100.0 * self.merge_miss_edge_only_by_context[2] as f64 / d,
                self.merge_miss_edge_only_by_context[3],
                100.0 * self.merge_miss_edge_only_by_context[3] as f64 / d,
            )?;
        }
        // Phase F.13 chain_10000 Plan D E4 Substage 1.a (2026-05-26).
        if self.sppf_reclaim_window_samples > 0 {
            let total = self.sppf_reclaim_window_samples as f64;
            writeln!(
                f,
                "  sppf_reclaim_window: samples={} cache_pinned={} ({:.1}%) pin_gap_max={} symbol_count_max={}",
                self.sppf_reclaim_window_samples,
                self.sppf_reclaim_cache_pinned_samples,
                100.0 * self.sppf_reclaim_cache_pinned_samples as f64 / total,
                self.sppf_reclaim_cache_pin_gap_max,
                self.sppf_reclaim_symbol_count_max,
            )?;
            // Window histogram: 16 buckets of 6.25 % each.
            write!(f, "  sppf_reclaim_window_histogram (% of chain reclaimable):")?;
            for (i, &count) in self.sppf_reclaim_window_histogram.iter().enumerate() {
                if count > 0 {
                    let pct = 100.0 * count as f64 / total;
                    write!(
                        f,
                        " [{}-{}%]={}({:.1}%)",
                        i * 100 / 16,
                        (i + 1) * 100 / 16,
                        count,
                        pct,
                    )?;
                }
            }
            writeln!(f)?;
            // Candidate-fraction histogram: 10 buckets of 10 % each.
            write!(f, "  sppf_reclaimable_nodes_pct_histogram (% of Symbol nodes droppable):")?;
            for (i, &count) in self.sppf_reclaimable_nodes_pct_histogram.iter().enumerate() {
                if count > 0 {
                    let pct = 100.0 * count as f64 / total;
                    write!(
                        f,
                        " [{}-{}%]={}({:.1}%)",
                        i * 10,
                        (i + 1) * 10,
                        count,
                        pct,
                    )?;
                }
            }
            writeln!(f)?;
            // Gate: per Plan agent, PROCEED to S1.b iff bucket 5-9 sum
            // (≥ 50 % candidates) ≥ 50 % of samples AND window-histogram
            // bucket 2+ (≥ 12.5 % window) ≥ 10 % of samples.
            let cand_50plus: u64 =
                self.sppf_reclaimable_nodes_pct_histogram[5..].iter().sum();
            let window_12plus: u64 =
                self.sppf_reclaim_window_histogram[2..].iter().sum();
            let cand_pct = 100.0 * cand_50plus as f64 / total;
            let window_pct = 100.0 * window_12plus as f64 / total;
            writeln!(
                f,
                "  sppf_reclaim_gate: candidate≥50%={:.1}% (need ≥50%) AND window≥12.5%={:.1}% (need ≥10%): {}",
                cand_pct,
                window_pct,
                if cand_pct >= 50.0 && window_pct >= 10.0 { "FIRES" } else { "DOES NOT FIRE → Streaming SPPF futile, close E4 as DATA-CONCLUDED" },
            )?;
        }
        // Phase F.13 chain_10000 Exp 13 Substage 0 (2026-05-26).
        if self.chain_region_iterations > 0 {
            writeln!(
                f,
                "  chain_region_iterations={} (Exp 13 S0 gate: ≥ 100 \
                 = chain-region of size ≥ 100 elements; Earley+Leo \
                 outboard candidate when ≥ 9000)",
                self.chain_region_iterations,
            )?;
        }
        // Phase F.13 chain_10000 Exp 11 Substage 0 (2026-05-26).
        if self.fork_total > 0 {
            let denom = self.fork_total as f64;
            writeln!(
                f,
                "  fork_class: lex_fork={} ({:.1}%) cross_cat_total={} ({:.1}%) other={} ({:.1}%)",
                self.fork_total_by_class[0],
                100.0 * self.fork_total_by_class[0] as f64 / denom,
                self.fork_total_by_class[1],
                100.0 * self.fork_total_by_class[1] as f64 / denom,
                self.fork_total_by_class[2],
                100.0 * self.fork_total_by_class[2] as f64 / denom,
            )?;
            writeln!(
                f,
                "  fork_avg_fanout_by_class: lex={:.2} cross_cat={:.2} other={:.2}",
                self.fork_branches_by_class[0] as f64
                    / self.fork_total_by_class[0].max(1) as f64,
                self.fork_branches_by_class[1] as f64
                    / self.fork_total_by_class[1].max(1) as f64,
                self.fork_branches_by_class[2] as f64
                    / self.fork_total_by_class[2].max(1) as f64,
            )?;
        }
        // F.13 H11a diagnostic
        if self.merge_miss_pairs_considered_total > 0 {
            let denom = self.merge_miss_pairs_considered_total as f64;
            writeln!(
                f,
                "  merge_miss: pairs={} state_only={} ({:.1}%) node_only={} ({:.1}%) edge_only={} ({:.1}%) depth_only={} ({:.1}%) multi={} ({:.1}%)",
                self.merge_miss_pairs_considered_total,
                self.merge_miss_state_diff_total,
                100.0 * self.merge_miss_state_diff_total as f64 / denom,
                self.merge_miss_node_diff_total,
                100.0 * self.merge_miss_node_diff_total as f64 / denom,
                self.merge_miss_edge_diff_total,
                100.0 * self.merge_miss_edge_diff_total as f64 / denom,
                self.merge_miss_depth_diff_total,
                100.0 * self.merge_miss_depth_diff_total as f64 / denom,
                self.merge_miss_multi_diff_total,
                100.0 * self.merge_miss_multi_diff_total as f64 / denom,
            )?;
        }
        // F.13 H11b diagnostic
        if self.fork_cross_cat_projection_branches > 0 || self.fork_branches_dropped_pre_emit > 0 {
            writeln!(
                f,
                "  cross_cat: total_branches={} would_drop={} target_in_sppf={}",
                self.fork_cross_cat_projection_branches,
                self.fork_branches_dropped_pre_emit,
                self.fork_target_symbol_already_in_sppf,
            )?;
        }
        // F.13 H13 Step 0 diagnostic
        if self.merge_miss_pairs_considered_total > 0
            && self.merge_miss_pairs_edge_kind_equivalent > 0
        {
            let denom = self.merge_miss_pairs_considered_total as f64;
            writeln!(
                f,
                "  H13_diagnostic: would_merge_under_edge_kind={} ({:.1}%) — gate ≥ 60% to proceed to Step 2",
                self.merge_miss_pairs_edge_kind_equivalent,
                100.0 * self.merge_miss_pairs_edge_kind_equivalent as f64 / denom,
            )?;
        }
        // F.13 Stage 3.A diagnostic: 7-axis sole-cause + Lead #1 gate
        if self.merge_miss_pairs_considered_total > 0 {
            let denom = self.merge_miss_pairs_considered_total as f64;
            writeln!(
                f,
                "  merge_miss_extended_sole: cohort_origin={} ({:.1}%) sppf_top={} ({:.1}%) lex_alt_idx={} ({:.1}%) weight_src_idx={} ({:.1}%) weight_rule_idx={} ({:.1}%) lex_fork_stamp={} ({:.1}%)",
                self.merge_miss_cohort_origin_diff_total,
                100.0 * self.merge_miss_cohort_origin_diff_total as f64 / denom,
                self.merge_miss_sppf_top_diff_total,
                100.0 * self.merge_miss_sppf_top_diff_total as f64 / denom,
                self.merge_miss_lex_alt_idx_diff_total,
                100.0 * self.merge_miss_lex_alt_idx_diff_total as f64 / denom,
                self.merge_miss_weight_src_idx_diff_total,
                100.0 * self.merge_miss_weight_src_idx_diff_total as f64 / denom,
                self.merge_miss_weight_rule_idx_diff_total,
                100.0 * self.merge_miss_weight_rule_idx_diff_total as f64 / denom,
                self.merge_miss_lex_fork_stamp_diff_total,
                100.0 * self.merge_miss_lex_fork_stamp_diff_total as f64 / denom,
            )?;
            if self.merge_miss_multi_diff_total > 0 {
                let names = [
                    "state", "node", "edge", "depth", "cohort_origin",
                    "sppf_top", "lex_alt_idx", "weight_src_idx",
                    "weight_rule_idx", "lex_fork_stamp",
                ];
                write!(f, "  merge_miss_multi_participation:")?;
                for (i, n) in names.iter().enumerate() {
                    let c = self.merge_miss_multi_participation[i];
                    let multi_denom = self.merge_miss_multi_diff_total as f64;
                    write!(
                        f,
                        " {}={} ({:.1}%)",
                        n,
                        c,
                        100.0 * c as f64 / multi_denom,
                    )?;
                }
                writeln!(f)?;
            }
            writeln!(
                f,
                "  Lead1_gate: pred_edge_class_equivalent={} ({:.1}%) — Stage A gate ≥ 40% to ship Lead #1 (incoming_edge → (pred, EdgeKind))",
                self.merge_miss_pairs_pred_edge_class_equivalent,
                100.0 * self.merge_miss_pairs_pred_edge_class_equivalent as f64 / denom,
            )?;
        }
        // Phase F.13 chain_10000 Plan C Substage 0 (2026-05-26):
        // length histograms for incoming_edge_stack + recovery_deltas.
        // Used to size SmallVec inline N in Plan C Substage 1.
        if self.incoming_edge_stack_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.incoming_edge_stack_len_samples as f64;
            write!(
                f,
                "  incoming_edge_stack_len_histogram (n={}, max={}):",
                self.incoming_edge_stack_len_samples,
                self.incoming_edge_stack_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.incoming_edge_stack_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        if self.recovery_deltas_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.recovery_deltas_len_samples as f64;
            write!(
                f,
                "  recovery_deltas_len_histogram (n={}, max={}):",
                self.recovery_deltas_len_samples,
                self.recovery_deltas_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.recovery_deltas_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        // Phase F.13 chain_10000 Exp 5 Substage 0 (2026-05-26).
        if self.visited_dispatch_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.visited_dispatch_len_samples as f64;
            write!(
                f,
                "  visited_dispatch_len_histogram (n={}, max={}):",
                self.visited_dispatch_len_samples,
                self.visited_dispatch_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.visited_dispatch_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        if self.visited_recovery_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.visited_recovery_len_samples as f64;
            write!(
                f,
                "  visited_recovery_len_histogram (n={}, max={}):",
                self.visited_recovery_len_samples,
                self.visited_recovery_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.visited_recovery_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        // Phase F.13 chain_10000 Exp 12 Substage 0 (2026-05-26).
        if self.binder_scope_marks_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.binder_scope_marks_len_samples as f64;
            write!(
                f,
                "  binder_scope_marks_len_histogram (n={}, max={}):",
                self.binder_scope_marks_len_samples,
                self.binder_scope_marks_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.binder_scope_marks_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        if self.optional_scope_marks_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.optional_scope_marks_len_samples as f64;
            write!(
                f,
                "  optional_scope_marks_len_histogram (n={}, max={}):",
                self.optional_scope_marks_len_samples,
                self.optional_scope_marks_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.optional_scope_marks_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        if self.binder_scope_names_len_samples > 0 {
            let labels = ["0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64+"];
            let total = self.binder_scope_names_len_samples as f64;
            write!(
                f,
                "  binder_scope_names_len_histogram (n={}, max={}):",
                self.binder_scope_names_len_samples,
                self.binder_scope_names_len_max,
            )?;
            for (i, lbl) in labels.iter().enumerate() {
                let c = self.binder_scope_names_len_histogram[i];
                write!(f, " {}={} ({:.1}%)", lbl, c, 100.0 * c as f64 / total)?;
            }
            writeln!(f)?;
        }
        // Phase F.13 chain_10000 Exp 10 Substage 0 (2026-05-26):
        // ConfigKey pairwise correlation. Print as lower-triangular
        // matrix (10x10 → 45 entries) for axis pairs (i, j) with i<j.
        // Axis names match merge_miss_multi_participation (line ~393).
        let axis_names = [
            "state", "node", "edge", "depth", "cohort_origin", "sppf_top",
            "lex_alt_idx", "weight_src_idx", "weight_rule_idx", "lex_fork_stamp",
        ];
        let mut has_any = false;
        for &c in self.merge_miss_pair_participation.0.iter() {
            if c > 0 {
                has_any = true;
                break;
            }
        }
        if has_any && self.merge_miss_multi_diff_total > 0 {
            let denom = self.merge_miss_multi_diff_total as f64;
            writeln!(
                f,
                "  merge_miss_pair_participation (axis i ∧ j both differ; denom = multi_diff_total = {}):",
                self.merge_miss_multi_diff_total,
            )?;
            for i in 0..10 {
                for j in (i + 1)..10 {
                    let idx = lower_triangle_index(i, j);
                    let c = self.merge_miss_pair_participation[idx];
                    if c > 0 {
                        let pct = 100.0 * c as f64 / denom;
                        writeln!(
                            f,
                            "    ({}, {}) = {} ({:.1}%)",
                            axis_names[i], axis_names[j], c, pct,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// Increment a `u64` counter on `self.stats` (zero-cost when feature off).
///
/// Usage: `stats_inc!(self, apply_action_calls);`
#[macro_export]
macro_rules! stats_inc {
    ($walker:expr, $field:ident) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker.stats.$field = $walker.stats.$field.saturating_add(1);
        }
    };
}

/// Add an arbitrary value to a `u64` counter on `self.stats` (zero-cost
/// when feature off).
///
/// Usage: `stats_add!(self, branch_cursors_sum, self.branch_cursors.len() as u64);`
#[macro_export]
macro_rules! stats_add {
    ($walker:expr, $field:ident, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let v: u64 = ($value) as u64;
            $walker.stats.$field = $walker.stats.$field.saturating_add(v);
        }
    };
}

/// Max-update a `u64` counter on `self.stats` (zero-cost when feature
/// off). Used for peak counters.
///
/// Usage: `stats_max!(self, branch_cursors_peak_pre_merge,
///                    self.branch_cursors.len() as u64);`
#[macro_export]
macro_rules! stats_max {
    ($walker:expr, $field:ident, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let v: u64 = ($value) as u64;
            if v > $walker.stats.$field {
                $walker.stats.$field = v;
            }
        }
    };
}

/// Phase F.13 chain_10000 Plan C Substage 0 (2026-05-26): sample a
/// length value into a `[u64; 8]` histogram + max + samples counter
/// (zero-cost when feature off). Triple of fields:
///   - `$hist_field` is the `[u64; 8]` histogram.
///   - `$max_field` is the `u64` max.
///   - `$samples_field` is the `u64` total sample count.
///
/// Usage:
///   `stats_histogram_sample!(self, incoming_edge_stack_len_histogram,
///                            incoming_edge_stack_len_max,
///                            incoming_edge_stack_len_samples,
///                            cursor.incoming_edge_stack.len());`
#[macro_export]
macro_rules! stats_histogram_sample {
    ($walker:expr, $hist_field:ident, $max_field:ident, $samples_field:ident, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let v: usize = $value;
            let idx = $crate::walker_stats::histogram_bucket_index(v);
            $walker.stats.$hist_field[idx] =
                $walker.stats.$hist_field[idx].saturating_add(1);
            let vu64 = v as u64;
            if vu64 > $walker.stats.$max_field {
                $walker.stats.$max_field = vu64;
            }
            $walker.stats.$samples_field =
                $walker.stats.$samples_field.saturating_add(1);
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_all_zeros() {
        let s = WalkerStats::default();
        assert_eq!(s.apply_action_calls, 0);
        assert_eq!(s.step_fanout_calls, 0);
        assert_eq!(s.avg_cursors_per_step(), 0.0);
        assert_eq!(s.merge_collapse_ratio(), 0.0);
    }

    #[test]
    fn display_renders_without_panic() {
        let s = WalkerStats {
            apply_action_calls: 9_847,
            step_fanout_calls: 412,
            branch_cursors_peak_pre_merge: 47,
            branch_cursors_peak_post_merge: 23,
            branch_cursors_sum: 9_847,
            merge_attempts_total: 2_184,
            merge_collapses_total: 1_772,
            cursors_created_via_seed: 1,
            cursors_created_via_fork: 9_846,
            cursors_dropped_via_resolution_check: 12,
            cursors_dropped_via_explicit_drop: 4,
            cursors_dropped_via_outcome_drop: 58,
            cursors_dropped_via_merge: 1_772,
            fork_total: 1_968,
            fork_kind_push: 5_904,
            fork_kind_opt_group_absent: 0,
            fork_kind_lex_alt_family: 0,
            fork_kind_consume_family: 3_936,
            fork_kind_other: 12,
            fork_recovery_dispatches: 0,
            fork_cross_cat_projection_branches: 5_904,
            // Phase F.13 chain_10000 Exp 10 S0-bis (2026-05-26).
            merge_miss_node_only_by_context: [0; 4],
            merge_miss_edge_only_by_context: [0; 4],
            // Phase F.13 chain_10000 Plan D E4 Substage 1.a (2026-05-26).
            sppf_reclaim_window_samples: 0,
            sppf_reclaim_cache_pinned_samples: 0,
            sppf_reclaim_cache_pin_gap_max: 0,
            sppf_reclaim_window_histogram: [0; 16],
            sppf_reclaimable_nodes_pct_histogram: [0; 10],
            sppf_reclaim_symbol_count_max: 0,
            // Phase F.13 chain_10000 Exp 13 Substage 0 (2026-05-26).
            chain_region_iterations: 0,
            // Phase F.13 chain_10000 Exp 11 Substage 0 (2026-05-26).
            fork_total_by_class: [0; 4],
            fork_branches_by_class: [0; 4],
            merge_miss_pairs_considered_total: 0,
            merge_miss_state_diff_total: 0,
            merge_miss_node_diff_total: 0,
            merge_miss_edge_diff_total: 0,
            merge_miss_depth_diff_total: 0,
            merge_miss_multi_diff_total: 0,
            fork_branches_dropped_pre_emit: 0,
            fork_target_symbol_already_in_sppf: 0,
            merge_miss_pairs_edge_kind_equivalent: 0,
            merge_miss_cohort_origin_diff_total: 0,
            merge_miss_sppf_top_diff_total: 0,
            merge_miss_lex_alt_idx_diff_total: 0,
            merge_miss_weight_src_idx_diff_total: 0,
            merge_miss_weight_rule_idx_diff_total: 0,
            merge_miss_lex_fork_stamp_diff_total: 0,
            merge_miss_pairs_pred_edge_class_equivalent: 0,
            merge_miss_multi_participation: [0; 10],
            // Phase F.13 chain_10000 Plan C Substage 0 (2026-05-26).
            incoming_edge_stack_len_histogram: [0; 8],
            incoming_edge_stack_len_max: 0,
            incoming_edge_stack_len_samples: 0,
            recovery_deltas_len_histogram: [0; 8],
            recovery_deltas_len_max: 0,
            recovery_deltas_len_samples: 0,
            // Phase F.13 chain_10000 Exp 5 Substage 0 (2026-05-26).
            visited_dispatch_len_histogram: [0; 8],
            visited_dispatch_len_max: 0,
            visited_dispatch_len_samples: 0,
            visited_recovery_len_histogram: [0; 8],
            visited_recovery_len_max: 0,
            visited_recovery_len_samples: 0,
            // Phase F.13 chain_10000 Exp 10 + Exp 12 Substage 0 (2026-05-26).
            merge_miss_pair_participation: PairCounts([0; 45]),
            binder_scope_marks_len_histogram: [0; 8],
            binder_scope_marks_len_max: 0,
            binder_scope_marks_len_samples: 0,
            optional_scope_marks_len_histogram: [0; 8],
            optional_scope_marks_len_max: 0,
            optional_scope_marks_len_samples: 0,
            binder_scope_names_len_histogram: [0; 8],
            binder_scope_names_len_max: 0,
            binder_scope_names_len_samples: 0,
        };
        let rendered = format!("{}", s);
        assert!(rendered.contains("apply_action_calls=9847"));
        assert!(rendered.contains("collapse_ratio=0.811"));
    }

    #[test]
    fn merge_collapse_ratio_zero_attempts() {
        let s = WalkerStats {
            merge_attempts_total: 0,
            merge_collapses_total: 0,
            ..Default::default()
        };
        assert_eq!(s.merge_collapse_ratio(), 0.0);
    }

    #[test]
    fn avg_cursors_zero_steps() {
        let s = WalkerStats::default();
        assert_eq!(s.avg_cursors_per_step(), 0.0);
    }
}
