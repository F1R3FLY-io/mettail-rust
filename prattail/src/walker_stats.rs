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

use rustc_hash::FxHashMap;

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
    /// Calculator-map cross-cat fan-out fix
    /// (`docs/design/calculator-map-crosscat-fanout.md` §4): cursors dropped
    /// by `subsume_weight_dominated_when_single_result` — the single-result
    /// demand-mode weight-dominance subsumption. NON-zero ONLY on the
    /// `Cat::parse` (single-result) path; always 0 on `_all`/`_prefix`/
    /// bounding-mode and when `PRATTAIL_SR_SUBSUME=0`. The subsumption is
    /// INVISIBLE under `PRATTAIL_TRACE` (tracing routes the single-result
    /// facade to the exhaustive driver, so the demand flag stays false) — so
    /// this counter (not a trace) is the way to observe the pass firing.
    pub cursors_dropped_via_sr_subsume: u64,

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

    // ── Phase F.13 chain_10000 Exp 16 (2026-05-26): walker memory
    //     attribution profiling. Per E4 S1.a data the SPPF arena is
    //     NOT the chain_10000 bottleneck; per Exp 9 the cohort cache
    //     pause-side state is bigger than the revive-side; per Exp 8
    //     the visited_dispatch Arc<FxHashSet> is the wrong target.
    //     This counter set captures the MAX size of every walker-
    //     owned structure across the parse so the post-parse byte
    //     attribution identifies the actual dominant consumer.
    pub mem_attr_branch_cursors_max: u64,
    pub mem_attr_cache_entries_max: u64,
    pub mem_attr_cache_pending_members_sum_max: u64,
    pub mem_attr_cache_worker_snapshots_sum_max: u64,
    pub mem_attr_cache_deferred_continuations_sum_max: u64,
    pub mem_attr_sppf_stack_arena_nodes_max: u64,
    pub mem_attr_incoming_edge_stack_arena_nodes_max: u64,
    pub mem_attr_sppf_nodes_max: u64,
    pub mem_attr_sppf_symbol_packings_max: u64,
    pub mem_attr_gss_nodes_max: u64,
    pub mem_attr_gss_edges_max: u64,
    pub mem_attr_visited_dispatch_unique_arcs_max: u64,
    pub mem_attr_visited_dispatch_total_entries_max: u64,
    pub mem_attr_recovery_deltas_unique_arcs_max: u64,
    pub mem_attr_sppf_symbol_terms_max: u64,
    // Exp 16 round 3: SPPF auxiliary storage + per-cursor splice
    // arenas + cohort-revive WorkerSnapshot Arc heap accounting.
    pub mem_attr_sppf_text_arena_bytes_max: u64,
    pub mem_attr_sppf_text_index_count_max: u64,
    pub mem_attr_sppf_dedup_packing_children_bytes_max: u64,
    pub mem_attr_sppf_dedup_symbol_count_max: u64,
    pub mem_attr_sppf_dedup_terminal_count_max: u64,
    pub mem_attr_sppf_collection_arena_total_entries_max: u64,
    pub mem_attr_sppf_collection_arena_unique_arcs_max: u64,
    pub mem_attr_lex_fork_path_total_entries_max: u64,
    pub mem_attr_lex_fork_path_unique_arcs_max: u64,
    pub mem_attr_binder_scope_marks_unique_arcs_max: u64,

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

    // ── F.13 H13 Step 0 diagnostic: edge-kind-relaxed merge would-merge ──
    /// Number of merge-miss pairs (intra-`pos`, multi-discriminator) whose
    /// `incoming_edge_stack.last()` differs by `GssEdgeId` but would
    /// match under the H13 EdgeKind-relaxed equivalence. Cross-cat
    /// projections compare the full `EdgeKind`, including `wrap_cat` and
    /// `wrap_rule`; the formal wrap-sensitive counterexample shows that
    /// `(source,bp)` alone is not a sound observable edge equivalence.
    /// If this count is ≥ 60% of `merge_miss_pairs_considered_total`,
    /// H13 Step 2 (actual merge relaxation) is justified. Otherwise H13
    /// is REJECTED.
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

    /// Phase F.13 chain_10000 plan-amend Substage 0 (2026-05-26):
    /// EdgeKind coarse-dedup projection. Counterfactual measurement of
    /// what `EdgeStackArena` would look like under Intervention A's
    /// keying scheme (`(parent, EdgeKind)` for convergent kinds;
    /// `(parent, EdgeKind, GssEdgeId)` for divergent kinds). The gate
    /// to ship Intervention A is `projected_dedup_rate() >= 100x` on
    /// left_assoc_chain_500. Populated by walker push sites under the
    /// `walker-stats` feature; zero-cost when disabled.
    pub edge_kind_projection: EdgeKindProjection,

    /// Phase F.13 chain_10000 Exp 14 Substage 0 (2026-05-27): TomitaKey
    /// coarse-merge projection. Counterfactual measurement of what the
    /// planned `TomitaFrontierMap` (Tomita 1985 / Scott-Johnstone 2010)
    /// would dedup if the walker keyed cursors on
    /// `(state, node, pos, edge_top, collection_depth)` per
    /// `prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`
    /// §2.3. The gate to proceed past Substage 0 is `projected_dedup_rate()
    /// >= 5.0` on left_assoc_chain_500.
    pub tomita_key_projection: TomitaKeyProjection,

    /// Phase F.13 chain_10000 Exp 15 Substage 0 (2026-05-27): CPS
    /// continuation size projection. Counterfactual measurement of the
    /// `Continuation::ApplyAction` record size distribution under the
    /// planned CPS rewrite (see
    /// `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` §3.1).
    /// Gate: P50 ≤ 32 B AND P99 ≤ 64 B on left_assoc_chain_500.
    pub continuation_size_projection: ContinuationSizeProjection,

    /// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): force-ratio
    /// projection. Counterfactual measurement of how many Fork-arm
    /// children would be created as compact deferred branch records vs
    /// how many would actually be forced (materialized into
    /// `BranchCursor`) under the planned weight-keyed lazy traversal
    /// (see `prattail/docs/design/plans/lazy-weight-guided-walker.md`
    /// §3 L0). The L0 gate FAILED at chain_50 (ratio 0.799 vs threshold
    /// 0.5; projected savings 1.24x). Plan v1 superseded by Plan v2 at
    /// `lazy-arc-native-walker.md`; this projection is now a residual-
    /// divergence diagnostic (L5 gate: `apply_action_calls / arc_count
    /// ≤ 0.10`).
    pub thunk_force_projection: ThunkForceRatioProjection,

    /// Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27): Pop
    /// EdgeKind histogram. Bucket index matches `pop_kind_bucket_index`
    /// helper below, one bucket per `EdgeKind` variant. Sampled
    /// at every `WpdaStepAction::Pop` entry by deriving the EdgeKind
    /// from the popped GSS node's symbol via `EdgeKind::from_symbol`.
    ///
    /// L2 instrumentation gate: confirms which EdgeKind dominates the
    /// chain-interior Pop volume before paying L2's ~400 LOC budget on
    /// the broadcast helper. The Plan v2's L2 substage targets the
    /// single-predecessor convergent EdgeKinds (CategoryEntryRoot,
    /// CrossCatProjection, PrefixRuleEntry, InfixContinuation,
    /// LexAltLiteral, OptionalGroupAt, BinderListLoopAt). If the dominant bucket falls
    /// outside that set (e.g., Generic, ReturnFrame, CollectionElement),
    /// L2 is misdesigned and needs re-architecture.
    pub pop_kind_histogram: [u64; 16],

    /// Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27):
    /// `apply_action_to_cursor` variant histogram. 19 buckets for the
    /// 19 `WpdaStepAction` variants. Sampled at each
    /// apply_action_to_cursor entry — exposes which arm dominates the
    /// action volume so L2-L3 can target the right variant for
    /// graduation.
    ///
    /// Empirical baseline (chain_50, walker-stats): Fork = 42.1%,
    /// Push = 36.6%, Pop = 14.4%. The combined Fork + Push (78.7%) is
    /// the dominant lever; Pop alone is structurally insufficient for
    /// the L4 (chain_10000 < 500 MB) target.
    pub apply_action_variant_histogram: [u64; 21],

    /// Phase F.13 chain_10000 Lazy redesign L2a prep (2026-05-27): Push
    /// EdgeKind histogram, sampled at the apply_action_to_cursor Push
    /// arm. These are the RESIDUAL Push calls — those NOT covered by
    /// Substage 5's broadcast (which already handles InfixContinuation,
    /// PrefixRuleEntry, LexAltLiteral at `wpda_walker.rs:7949-8071`).
    /// Bucket index matches `pop_kind_bucket_index` (same EdgeKind
    /// taxonomy).
    ///
    /// L2a gate: confirms CategoryEntryRoot + CrossCatProjection +
    /// OptionalGroupAt sum ≥ 80% of residual Push volume. If below
    /// threshold, the L2a broadcast targets are wrong and re-targeting
    /// is required.
    pub push_kind_histogram: [u64; 16],

    /// Phase F.13 chain_10000 COQ-S0 (2026-05-27): cumulative count of
    /// distinct `DispatchKey` values observed across all
    /// `DispatchCohortCache::register` calls during the parse. The
    /// DispatchKey includes `pos: u32` as a discriminator.
    ///
    /// Sampled via FxHashSet at every register call site in
    /// `wpda_walker.rs::allocate_fork_push_child`. The set's memory
    /// cost is bounded by the distinct count (e.g., ~500 entries at
    /// chain_500) so this is cheap.
    pub cohort_origin_dispatch_keys_seen:
        rustc_hash::FxHashSet<crate::dispatch_cohort::DispatchKey>,

    /// Phase F.13 chain_10000 COQ-S0 (2026-05-27): cumulative count of
    /// distinct `EquivKey` values observed (= DispatchKey minus pos).
    /// The proposed COQ quotient drops `pos` from ConfigKey equality;
    /// this set measures the empirical collision rate.
    ///
    /// Gate: `len(dispatch_keys_seen) / len(equiv_keys_seen) ≥ 20` at
    /// chain_500 confirms the pos axis is the dominant discriminator
    /// and COQ would collapse the cohort merge factor by ≥ 20×.
    pub cohort_origin_equiv_keys_seen: rustc_hash::FxHashSet<(u16, u8)>,

    /// Phase F.13 chain_10000 COQ-S0 (2026-05-27): peak per-step
    /// distinct DispatchKey count across branch_cursors' cohort_origin.
    /// Sampled at the start of each step_fanout call by counting unique
    /// cohort_origins in the current branch_cursors set.
    ///
    /// If median per-step distinct count ≥ 5, the cohort merge fails
    /// to coalesce across chain depths (COQ target confirmed).
    pub cohort_origin_distinct_per_step_max: u64,
    /// Phase F.13 chain_10000 COQ-S0 (2026-05-27): running sum of
    /// per-step distinct DispatchKey counts (for computing average).
    pub cohort_origin_distinct_per_step_sum: u64,
    /// Phase F.13 chain_10000 COQ-S0 (2026-05-27): per-step samples
    /// counter.
    pub cohort_origin_per_step_samples: u64,

    /// Phase F.13 chain_10000 Plan v6 H2 (2026-05-27): chain-region
    /// Earley absorption trigger fired this parse (one per
    /// `(category_src_idx, rule_index_in_category)` pair where the
    /// IterativeChainAbsorb arm detected a chain region of ≥ 4 atoms).
    /// Region-amortized: should be == 1 per chain region (vs Exp 13
    /// S1.c which invoked per-iteration).
    pub chain_earley_trigger_count: u64,
    /// Phase F.13 chain_10000 Plan v6 H2 (2026-05-27): Earley invocation
    /// succeeded (returned Some root_sppf_id).
    pub chain_earley_succeeded_count: u64,
    /// Phase F.13 chain_10000 Plan v6 H2 (2026-05-27): Earley invocation
    /// returned None (chain region too short or chart construction
    /// declined).
    pub chain_earley_returned_none_count: u64,
    /// Phase F.13 chain_10000 Plan v6 H2 (2026-05-27): sum of atom
    /// counts that Earley absorbed (used to compute chain_end_pos
    /// projection). Divide by `chain_earley_succeeded_count` for the
    /// average chain length absorbed per Earley call.
    pub chain_earley_atoms_absorbed_sum: u64,

    // ── Evidence-pruning P1 Step-0 diagnostics (plan §P1 commit 2;
    //    ledger 02-program-ledger.md) — walker-side counters. The three
    //    fall-through GATE counters live in `ep_p1` (process-wide
    //    atomics) because the gate runs in GENERATED code with no
    //    walker access. ──────────────────────────────────────────────
    /// EP-P1: `EdgeKind::CrossCatLhs` delegate pushes applied (the
    /// Pass-0 dispatch-time d-worker spawns). Denominator for the
    /// cohort-share gate (share iff dup ≥ 10%).
    pub crosscat_lhs_delegates_spawned: u64,
    /// EP-P1: spawns BEYOND THE FIRST at the same `(pos,
    /// source_src_idx)` — the would-share measure (an `EquivKey`-style
    /// merge would coalesce exactly these at registration; spawn
    /// multiplicity, not instantaneous liveness, is what sharing
    /// removes). Numerator for the cohort-share gate.
    pub crosscat_lhs_delegate_dup_at_pos_source: u64,
    /// EP-P1: spawn counts per `(pos, source_src_idx)` backing the dup
    /// counter (diagnostic detail; non-zero entries with count > 1 are
    /// the share candidates).
    pub crosscat_lhs_spawns_at_pos_source: FxHashMap<(usize, u16), u64>,
    /// EP-P1: `apply_action_to_cursor` calls attributed to cursors
    /// UNDER a `CrossCatLhs` frame (any such edge in the cursor's
    /// `incoming_edge_stack`). The waste-gate metric: must drop ≥ 60%
    /// on `int(float(int(3.14))) == 3` when P1 enforcement lands, else
    /// the residue passes to P2/P3.
    pub cast_then_infix_steps: u64,
    /// EP-P1: memo `incoming_edge_stack_id → contains-CrossCatLhs?`.
    /// Exact forever (arena stacks are interned and immutable per id);
    /// collapses the attribution scan to one edge-stack walk per
    /// distinct stack.
    pub crosscat_lhs_stack_memo: FxHashMap<crate::edge_stack_arena::EdgeStackId, bool>,
    /// EP-P1 amended §P1 SHADOW (2026-06-11, Round 5): would-share
    /// decisions a v2 parking enforcement would have coalesced — a 2nd+
    /// CrossCatLhs dispatch push at the same full key. Partitioned
    /// `[state_class * 2 + recovery_enabled]` per the I4 convention.
    pub ep_p1_shadow_would_share_total: [u64; WPDA_STATE_CLASS_COUNT * 2],
    /// EP-P1 amended §P1 SHADOW: observation-only spawn counts keyed
    /// `(push pos, source_src_idx, host_cat)` — the full DispatchKey
    /// modulo the per-arm-constant wrap_rule. Reset with the rest of
    /// the stats at the per-parse boundary; NEVER feeds the dispatch-
    /// cohort cache.
    pub ep_p1_shadow_seen: FxHashMap<(usize, u16, u16), u32>,
    /// EP-P1 MEASURE (Round 6, the v3 deciding measurement): first
    /// arrivals at a CrossCatLhs DispatchKey (the would-be workers).
    pub ep_p1_measure_workers: u64,
    /// EP-P1 MEASURE: arrivals during the in-flight window (these are
    /// the only ones a v3 would PARK — must stay small for the
    /// synchronous-consumption mechanism; the parking cap is 16).
    pub ep_p1_measure_inflight_hits: u64,
    /// EP-P1 MEASURE: arrivals AFTER resolution (a v3 consumes these
    /// synchronously in place — zero materialization). The deciding
    /// ratio: resolved_hits ≫ inflight_hits ⇒ synchronous consumption
    /// collapses the class.
    pub ep_p1_measure_resolved_hits: u64,
    /// EP-P1 MEASURE: arrivals at a key whose worker FAILED.
    pub ep_p1_measure_failed_hits: u64,
    /// EP-P1 MEASURE (R6-6/B1): first-resolver member tail per key
    /// `(dispatch_pos, source, host_cat)` → (state class, reentry
    /// would fire). Same-key resolvers compare their OWN tails.
    pub ep_p1_measure_first_tail: FxHashMap<(usize, u16, u16), (u8, bool)>,
    /// EP-P1 MEASURE (R6-6/B1): same-key resolvers whose member tail
    /// DIVERGED from the first resolver's — the empirical T3 witness
    /// (a worker-broadcast revive would have corrupted these members;
    /// the v3 member-tail revive is REQUIRED, not optional).
    pub ep_p1_measure_tail_divergent: u64,
    /// EP-P1 v3.1 ON: arrivals that consumed a resolved body
    /// synchronously in place (the flip experiment's effectiveness
    /// counter — expected ≈ the Measure resolved_hits population).
    pub ep_p1_consumed_in_place: u64,
    /// EP-P1 v3.1 ON: park attempts refused by the 16/key cap that
    /// fell back to Proceed (sound — less sharing only; expected ~0 on
    /// the corpus: in-flight population 24 across ~4 keys).
    pub ep_p1_park_overflow_fallbacks: u64,
    // ── led_chain ROOT-CAUSE DIAGNOSTIC (TEMPORARY; walker-stats only) ──
    /// Consume-decision register() outcome histogram at the On arm
    /// (7146): [WorkerInserted, InflightCollision, ResolvedHit, FailedHit].
    pub dbg_ccl_reg_outcome: [u64; 4],
    /// ResolvedHit at the consume arm but NOT quiescent (so it PARKED
    /// instead of consuming) — the "resolved-but-not-quiescent" stall.
    pub dbg_ccl_resolved_not_quiescent: u64,
    /// pause_cohort_member returned true (parked) at the consume arm.
    pub dbg_ccl_parked_ok: u64,
    /// Per-key consume-decision register count: how concentrated the
    /// registrations are. Key = (pos, source, host, route-implicit).
    pub dbg_ccl_reg_by_key: FxHashMap<(usize, u16, u16), u64>,
    /// Per-key park-overflow count.
    pub dbg_ccl_overflow_by_key: FxHashMap<(usize, u16, u16), u64>,
    /// Number of distinct cache keys still InFlight at EOI (orphan keys).
    pub dbg_ccl_inflight_keys_at_eoi: u64,
    /// In-step drain: jobs produced + members revived.
    pub dbg_ccl_drain_jobs: u64,
    pub dbg_ccl_drain_members: u64,
    /// EOI backstop: jobs + members revived.
    pub dbg_ccl_eoi_jobs: u64,
    pub dbg_ccl_eoi_members: u64,
    /// Quiescence decrements that reached zero (scheduled a drain).
    pub dbg_ccl_quiesce_to_zero: u64,
    /// Live-lineage increments (per-edge).
    pub dbg_ccl_lineage_inc: u64,
    /// Live-lineage decrements (per-edge).
    pub dbg_ccl_lineage_dec: u64,
    /// EOI: times revive_orphaned reached the M1 InFlight drain.
    pub dbg_ccl_m1_reached: u64,
    /// EOI: orphan_count observed at the M1 drain.
    pub dbg_ccl_m1_orphan_count: u64,
    /// EOI: members re-injected by M1 InFlight drain.
    pub dbg_ccl_m1_injected: u64,
    /// EOI: times the revival-rounds cap short-circuited before M1.
    pub dbg_ccl_rounds_capped: u64,
    /// EOI: times eoi_release was engaged.
    pub dbg_ccl_eoi_release_set: u64,
    /// §2 age-timeout: InFlightCollision arrivals that PROCEEDED because
    /// their worker was stale (> K steps without resolving).
    pub dbg_ccl_stale_proceed: u64,
    /// Mid-parse dead-worker release: members re-injected because their
    /// CrossCatLhs worker died (no live body-producing lineage).
    pub dbg_ccl_dead_worker_released: u64,
    /// EOI: times the InFlight-orphan re-injection was SKIPPED because the
    /// live frontier already held an accepting configuration (the
    /// budget-divergence fix; recovery is unnecessary when an accept exists).
    pub dbg_ccl_accept_present_skip: u64,

    // ── Evidence-pruning P2 Step-0 diagnostics (plan §P2 commit 2;
    //    ledger 02-program-ledger.md) — the Parikh/suffix obligation gate
    //    in SHADOW. All four are PARTITIONED `[state_class * 2 +
    //    recovery_enabled]` per the I4 convention (a single hit in a rare
    //    state must never be statistically buried). Display prints only
    //    non-zero slots (round-3 m-3). ───────────────────────────────────
    /// EP-P2: cursors the shadow obligation gate WOULD-REFUTE — the
    /// top-`RuleAt` frame's `must` demands a class the suffix mask cannot
    /// supply (`must != 0 ∧ (must & S[pos]) != must`), AND (I8) `must`
    /// is disjoint from the recovery-synthesizable classes. NOTHING is
    /// dropped (shadow). The gate consults the RECOVERY-OFF partition for
    /// its accept/STOP verdict (I8: under recovery-ON, sync tokens
    /// supply almost any obligation, so refutation is suppressed there).
    pub parikh_shadow_would_refute_total: [u64; WPDA_STATE_CLASS_COUNT * 2],
    /// EP-P2: the HARD-STOP TRIPWIRE — a would-refuted cursor (its sticky
    /// `ep_shadow_refuted` bit set) that STILL participates in an accepted
    /// parse at the EOI accept-snapshot. MUST stay all-zero everywhere
    /// (I4); any non-zero slot = the model or the transcription is wrong
    /// (deep-dive the mechanism; do NOT tune it away).
    pub parikh_shadow_refuted_then_accepted: [u64; WPDA_STATE_CLASS_COUNT * 2],
    /// EP-P2: `apply_action` calls spent on cursors AFTER the shadow gate
    /// would-refuted them (the flag is set) — the direct waste
    /// quantification. The accept gate: `≥ 20%` of `apply_action_calls`
    /// (recovery-off world) ⇒ recommend enforcement; `< 5%` ⇒ STOP.
    pub parikh_shadow_steps_after_would_refute: [u64; WPDA_STATE_CLASS_COUNT * 2],
    /// EP-P2: cursors dying at the EOI premature-Accepted / non-accepting
    /// filter that were SHADOW-REFUTABLE earlier — how many late deaths
    /// the gate could have caught at the obligation-creating transition.
    pub eoi_dead_cursors_parikh_refutable: [u64; WPDA_STATE_CLASS_COUNT * 2],

    // ── Evidence-pruning P4 (Stages C+E: ORDER-ONLY) diagnostics (plan
    //    §P4; ledger 02-program-ledger.md). The demotion is a PERMUTATION
    //    of the within-`step_fanout` iteration order (ForwardOrderOnly.v
    //    T5 `demotion_preserves_accepted_set`): it kills NOTHING. These
    //    counters are NOT partitioned (the demotion is frontier-global, not
    //    per-WpdaState); plain scalars. Display prints only when non-zero. ──
    /// EP-P4: the count of zero-innovation members that were stable-
    /// partitioned BEHIND ≥1 innovating member within a `step_fanout`
    /// pass (`PRATTAIL_EP_P4_DEMOTE=on`). A member is "zero-innovation"
    /// when its `consumed_since_last_check` flag is false (it advanced in
    /// the producing step only via ε / structural / recovery edges — its
    /// `pos` did not strictly advance). Effectiveness signal only; the
    /// surviving-cursor SET is invariant under the reorder (T3/T5).
    pub zero_innovation_demotions: u64,
    /// EP-P4: THE MODEL TRIPWIRE — a demoted (zero-innovation) member that
    /// was enqueued into the within-step continuation drain but NOT stepped
    /// before the pass exited. MUST stay 0 everywhere: ForwardOrderOnly.v
    /// T4 `every_member_stepped` + the InnovationDemotion invariant
    /// (`demoted_member_unstepped_at_exit == 0`) require demotion to
    /// permute WITHIN one pass and never defer a live member to a later
    /// pass (a deferred member is invisible to `run_to_end_of_input`'s
    /// whole-frontier progress fingerprint and `!progress_made` could exit
    /// early). Wired so any residual demoted-but-unstepped member at the
    /// end of the `step_fanout` drain increments it; non-zero = the
    /// transcription violated the within-step invariant (deep-dive; do NOT
    /// tune away).
    pub demoted_member_unstepped_at_exit: u64,
    /// EP-P4 (Stage E): the last computed frontier effective-sample-size
    /// ×1000 (Kish ESS over the live frontier's primary likelihood mass —
    /// see `frontier_ess_x1000` in wpda_walker.rs). Recorded at every
    /// `AmbiguityBudget` sentinel emission and at EOI; surfaced in the
    /// budget error report's hint so "1 winner + noise" (ESS≈1000) is
    /// distinguishable from genuine k-way ambiguity (ESS≈k·1000). 0 until
    /// the first budget/EOI event (the hot path computes it lazily at the
    /// event — it pays NOTHING when no budget event fires).
    pub frontier_ess_x1000_last: u32,

    // ── Evidence-pruning P5 (Stage D: regular residual over-approximation
    //    gate) ENTRY-GATE measurement (plan §P5; ledger 02-program-ledger.md).
    //    `residual_dead_steps` reduces (P2-real, P2-shadow, P3-shadow all = 0)
    //    to: apply_action steps on cursors that DIE at the EOI
    //    `!is_accepting_config` filter (never reach an accepting config), as a
    //    % of `apply_action_calls`. GATE: ≥ 15% ⇒ implement Stage D; < 15% ⇒
    //    STOP. Two numerators BRACKET the true share (a single counter cannot
    //    be both a global partition AND fork-correct — see the field docs on
    //    `BranchCursor::p5_steps_own/lineage`): `own` (lower) ≤ true ≤
    //    `lineage` (upper). Plain scalars; Display prints only when non-zero. ─
    /// EP-P5: Σ over EOI-dead cursors of `p5_steps_own` (own-since-fork) — the
    /// LOWER-BOUND `residual_dead_steps` numerator. `dead_own /
    /// apply_action_calls` under-counts the true dead share (fork ancestry +
    /// parked segments excluded). Default 0.
    pub p5_residual_dead_steps_own: u64,
    /// EP-P5: Σ over EOI-dead cursors of `p5_steps_lineage` (ancestry path
    /// length) — the UPPER-BOUND numerator. `dead_lineage / apply_action_calls`
    /// over-counts (shared prefixes double-counted across dead branches; can
    /// exceed 100%). Default 0.
    pub p5_residual_dead_steps_lineage: u64,
    /// EP-P5: Σ over EOI-ACCEPTING cursors of `p5_steps_own` — the denominator
    /// cross-check. `dead_own + accepted_own ≤ apply_action_calls`; the gap is
    /// the derived pre-EOI-lost residual (fork ancestry + mid-parse Drops +
    /// parked segments). Default 0.
    pub p5_accepted_steps_own: u64,
    /// EP-P5: Σ over EOI-accepting cursors of `p5_steps_lineage` (the lineage
    /// counterpart of the cross-check). Default 0.
    pub p5_accepted_steps_lineage: u64,
    /// EP-P5: raw cursor counts at the EOI frontier accounting pass
    /// (`p5_account_eoi_frontier`), independent of step counts —
    /// `examined` = all live EOI-frontier cursors; `dead` = those failing
    /// `is_accepting_config`. The LOAD-BEARING interp-A evidence: a non-zero
    /// `dead` with `p5_residual_dead_steps_* == 0` means the EOI-death
    /// population EXISTS but is step-free (re-seeded terminal singletons /
    /// freshly-materialized cohort members that reached EOI without
    /// re-entering `apply_action_to_cursor`), so Stage D would prune zero
    /// apply_action work. Default 0.
    pub p5_eoi_cursors_examined: u64,
    pub p5_eoi_dead_cursors: u64,

    // ─── BCC shadow (Batched Cross-cat delegate + Continuation-descriptor ───
    //     sharing, Plan afde9c48, Stage 0). Gated PRATTAIL_BCC_SHADOW=1.
    //     Distinct from the node-coarsening COARSEN-SHADOW above: BCC models the
    //     M4 SEAL — both `@a` cross-cat readings sealed to ONE canonical element
    //     Symbol so their sppf_stack TOP + the `@a`-reading EDGE label + the
    //     per-reading weight-rule all CANONICALIZE (one packing under one
    //     continuation), which the COARSEN-SHADOW keys did NOT do (they kept the
    //     two readings' distinct sppf tags / edge kinds / weight-rules apart).
    /// ★ S0-G-LINEAR (DECISIVE). Peak distinct BCC-coarsened buckets at the
    /// merge tier: node→N_cont-class, sppf_stack WHOLE chain projected to tags
    /// with the cross-cat element TOP sealed to ONE canonical sentinel, edge
    /// stack projected with BOTH `@a`-reading edge kinds (CrossCatProjection /
    /// CrossCatLhs*) folded to ONE canonical label, and the lex/weight
    /// provenance canonicalized. If this goes LINEAR in `k` while
    /// `branch_cursors_peak_pre_merge` is exponential ⇒ BCC's shared
    /// continuation linearizes the frontier (S0-G-LINEAR PASS). If it stays
    /// super-linear ⇒ a deeper multiplier below the `@a` fork ⇒ HALT.
    pub bcc_shadow_peak_pre_merge: u64,
    /// BCC control: the SAME BCC key but WITHOUT sealing the sppf-top / edge
    /// label (i.e. deep-edge-sppf with only the node→N_cont demotion + lex
    /// canonicalization). Isolates the seal's contribution: if
    /// `bcc_shadow_peak_pre_merge` ≪ this, the SEAL is what folds; if they are
    /// equal, the seal contributes nothing (the divergence is below it).
    pub bcc_shadow_peak_noseal: u64,
    /// BCC MAXIMAL-seal control (obstruction-naming): the STRONGEST possible
    /// coarsening — WHOLE sppf-stack chain collapsed + cohort dropped + edges
    /// folded, retaining only (state_class, node_class, pos, collection_depth,
    /// edge-fold). If this stays exponential in k, NO element seal can linearize
    /// the frontier — the residual is the (pos / collection_depth / edge-length)
    /// derivation multiplicity BCC's single continuation cursor cannot fold.
    pub bcc_shadow_peak_maximal: u64,
    /// BCC GLL-INVARIANT FLOOR: the absolute Tomita/GLL continuation key
    /// `(state/slot, pos)` = (state_class, node_class, pos, collection_depth),
    /// EVERYTHING else (incl. edge-stack) dropped. If linear ⇒ the edge-stack is
    /// the sole residual carrier; if ALSO exponential ⇒ `pos`-multiplicity
    /// itself (many partial derivations at the same position) is irreducible.
    pub bcc_shadow_peak_gll_floor: u64,
    /// BCC S0-G-Cont audit: count of merge-tier cursor pairs whose BCC key
    /// COLLAPSES (would share N_cont) but whose SEALED element Symbol tag
    /// DIFFERS (e.g. an `InputBind` vs `InputBindQuoted` element = different
    /// COMM arity). MUST be 0 for a sound two-category seal — any non-zero is
    /// the cycle-2 unsoundness wall (two different-typed readings forced to one
    /// continuation). Reported for the gravest gate.
    pub bcc_shadow_seal_type_conflicts: u64,
    /// BCC S0-G-Cont audit denominator: count of merge-tier cursor pairs whose
    /// BCC key collapses AND whose sealed element tag AGREES (a sound share).
    pub bcc_shadow_seal_agreements: u64,
    /// BCC number of shadow evaluations (denominator).
    pub bcc_shadow_calls: u64,

    // ─── DW shadow (DEEP SPPF-continuation-sharing / descriptor-worklist, ───
    //     Plan aaf070b3 / DESCRIPTOR_WORKLIST_DESIGN.md, Stage 0). Gated
    //     PRATTAIL_DW_SHADOW=1. Distinct from BCC-SHADOW above: BCC sealed only
    //     the cross-cat element TOP; DW installs the `.*sep`-return-reconvergence
    //     projection `R` which folds each MAXIMAL RUN of CrossCatLhs-family edges
    //     at-or-below a repetition-return (CollectionElement/CollectionMarker)
    //     frame to ONE canonical `(edge_target, EdgeKind-tag)` label — collapsing
    //     the per-`&`-segment distinct left-contexts (chain LENGTH) to the shared
    //     return slot. BCC's `bcc_edge_stack_proj` folded each cross-cat edge
    //     INDIVIDUALLY but retained chain length → stayed exponential; `R`
    //     collapses the RUN → O(1) chain per element. This is the mechanical
    //     discriminator that separates DW from the 3 prior HALTs.
    /// ★ S0-DW-LINEAR (DECISIVE). Peak distinct DW-reconverged buckets at the
    /// merge tier: the full ConfigKey axes (state_class, node_class, pos,
    /// collection_depth) with `incoming_edge_stack` replaced by `R(edge_stack)`
    /// and the sppf_stack projected to tags. PASS iff LINEAR in `k` (tracks
    /// GLL_FLOOR) while `branch_cursors_peak_pre_merge` is exponential; HALT if it
    /// stays super-linear (a multiplier survives below the CrossCatLhs run).
    pub dw_shadow_peak: u64,
    /// DW MAXIMAL-R control: `R(edge_stack)` alone (whole sppf-stack dropped +
    /// cohort dropped), retaining only (state_class, node_class, pos,
    /// collection_depth, R). The floor of what the `R` edge-stack fold achieves.
    pub dw_shadow_peak_maximal_r: u64,
    /// ★ S0-DW-SOUND pop-target conflicts (MUST be 0). For each pair of cursors
    /// the DW key now co-locates, count those whose concrete `incoming_edge_stack`
    /// TOPS route to INCOMPATIBLE pop targets (differing `(edge_target,
    /// EdgeKind.source_src_idx)`). A nonzero is the cycle-3 wrong-body-revive
    /// condition — HALT. Expected 0: co-located cursors share the `.*sep`-return
    /// slot; per-reading tails stay on distinct concrete top edges.
    pub dw_pop_target_conflicts: u64,
    /// ★ S0-DW-SOUND seal-type conflicts POST-gate (MUST be 0). Within each DW
    /// bucket folding ≥2 cursors, count pairs whose sealed element top tag DIFFERS
    /// (two different-typed `@a` readings forced to one continuation). The
    /// make-or-break gate: BCC measured 13,918 PRE-gate; the design's whole
    /// feasibility rests on this being 0 now that every `<-` target is alts=Ok(1).
    pub dw_seal_type_conflicts: u64,
    /// DW S0-DW-SOUND denominator: DW-bucket pairs whose sealed top tag AGREES.
    pub dw_seal_agreements: u64,
    /// ★ RT-7 anti-M0 tripwire: total count of repetition-return
    /// (CollectionElement/CollectionMarker) frames observed across the drained
    /// cursors' edge-stacks — the sites `R` folds at. MUST be ≥ k for the
    /// `@a<-c & …` k-segment `&`-list, else the reconvergence site is WRONG (the
    /// M0 failure fired 0×) → HALT + re-locate before any further work.
    pub dw_return_fires: u64,
    /// DW number of shadow evaluations (denominator).
    pub dw_shadow_calls: u64,

    // ─── DW LINEARITY BISECTION (Stage-0 diagnostic). Each replaces the ───
    //     edge-stack axis in an otherwise-GLL_FLOOR key (state_class, node_class,
    //     pos, coll_depth, [proj]) with a progressively COARSER edge-stack
    //     projection, to bracket EXACTLY where linearity emerges (mirrors the
    //     BCC SEALED/MAXIMAL/GLL_FLOOR ladder). Interpretation: the coarsest
    //     projection that is BOTH linear-in-k AND sound is the fix target; if
    //     none is, the `<-` residual is a genuine derivation-multiplicity floor.
    /// Peak buckets keying edge-stack as the variant-only SEQUENCE + seg-block RLE.
    pub dw_bisect_variant_seq: u64,
    /// Peak buckets keying edge-stack as the variant-only MULTISET (order-indep).
    pub dw_bisect_variant_multiset: u64,
    /// Peak buckets keying edge-stack as the variant-only SET (distinct present).
    pub dw_bisect_variant_set: u64,
    /// Peak buckets keying edge-stack as the COUNT of cross-cat-family edges only.
    pub dw_bisect_crosscat_count: u64,
    /// Peak buckets keying edge-stack as its LENGTH only.
    pub dw_bisect_len: u64,
    /// ★ SOUNDNESS of the LINEAR (crosscat_count) projection: co-located pairs
    /// under the count-key whose CONCRETE pop-targets are INCOMPATIBLE. Nonzero ⇒
    /// the ONLY edge-stack projection that linearizes is UNSOUND (over-merges
    /// distinct continuations that the lossy merge would drop) ⇒ S0-DW-SOUND HALT.
    pub dw_count_pop_conflicts: u64,
    /// crosscat_count-key soundness denominator: co-located pairs whose concrete
    /// pop-targets AGREE (a sound share).
    pub dw_count_agreements: u64,

    /// ROOT-P EXACT-FAN A1 measurement (`PRATTAIL_CGLL_FAN_MEASURE`, 2026-07-09):
    /// number of `Pop` reduce sites at which the READ-ONLY exact-fan counting
    /// pass ran in `step_canonical`'s reduce-reconnection block. The coarse fan
    /// (`cgll_slot_fan_pop`) still runs UNCHANGED at each such site — this pass
    /// only OBSERVES (`C_coarse` vs `C_exact = gll_edges_by_slot(cat,lo)`), so a
    /// measurement build reverts byte-identical. Non-zero only under the const +
    /// `PRATTAIL_CGLL_FAN_MEASURE` (and only in a `walker-stats` build — the whole
    /// `stats` field is feature-gated, so adding this is byte-identical for the
    /// default build). The DECISIVE readings are the `CGLL-FANMEASURE` stderr
    /// report lines (driven by `step_canonical` locals), not this counter.
    ///
    /// RETIRED (2026-07-13; the hosting hybrid arm was physically removed
    /// 2026-07-15 with the classic engine, task #19b S1), so this counter can no
    /// longer fire.
    pub cgll_fanmeasure_sites_total: u64,
}

/// Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27): bucket
/// index for `apply_action_variant_histogram`. Matches the variant order
/// of `crate::wpda_walker::WpdaStepAction`.
pub fn apply_action_variant_index<W: crate::automata::semiring::SemiringRef>(
    action: &crate::wpda_walker::WpdaStepAction<W>,
) -> usize {
    use crate::wpda_walker::WpdaStepAction;
    match action {
        WpdaStepAction::Advance(_) => 0,
        WpdaStepAction::AdvanceWithEffect { .. } => 1,
        WpdaStepAction::Push { .. } | WpdaStepAction::PushWithEdgeKind { .. } => 2,
        WpdaStepAction::Pop { .. } => 3,
        WpdaStepAction::Replace { .. } => 4,
        WpdaStepAction::Fork { .. } => 5,
        WpdaStepAction::ConsumeAndPush { .. } => 6,
        WpdaStepAction::IterativeChainAbsorb { .. } => 7,
        WpdaStepAction::ConsumeAndPop { .. } => 8,
        WpdaStepAction::Consume { .. } => 9,
        WpdaStepAction::ConsumeIdentAndReplace { .. } => 10,
        WpdaStepAction::ConsumeAndReplace { .. } => 11,
        // #307 ROOT-A red-team fix (2026-06-11): own bucket 19 — sharing
        // bucket 11 with ConsumeAndReplace conflated the two actions in
        // exactly the per-action-kind attribution the evidence-pruning
        // P-series diagnostics depend on.
        WpdaStepAction::ConsumeAtAndReplace { .. } => 19,
        // #307 ROOT-F (2026-06-11): membership-checked collection close —
        // own bucket 20 (never shared with ConsumeAndPop: per-action
        // attribution feeds the evidence-pruning P-series diagnostics).
        WpdaStepAction::ConsumeAtAndPop { .. } => 20,
        WpdaStepAction::ReplaceAndPush { .. } => 12,
        WpdaStepAction::ParsePredicate { .. } => 13,
        WpdaStepAction::OptGroupAbsent { .. } => 14,
        WpdaStepAction::OptGroupFinalize { .. } => 15,
        WpdaStepAction::Accept => 16,
        WpdaStepAction::Error(_) => 17,
        WpdaStepAction::Idle => 18,
    }
}

/// Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27): label
/// for each `apply_action_variant_histogram` bucket index.
pub fn apply_action_variant_label(idx: usize) -> &'static str {
    [
        "Advance",
        "AdvanceWithEffect",
        "Push",
        "Pop",
        "Replace",
        "Fork",
        "ConsumeAndPush",
        "IterativeChainAbsorb",
        "ConsumeAndPop",
        "Consume",
        "ConsumeIdentAndReplace",
        "ConsumeAndReplace",
        "ReplaceAndPush",
        "ParsePredicate",
        "OptGroupAbsent",
        "OptGroupFinalize",
        "Accept",
        "Error",
        "Idle",
        "ConsumeAtAndReplace",
        "ConsumeAtAndPop",
    ][idx.min(20)]
}

/// Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27): bucket
/// index for `pop_kind_histogram`. Matches the variant order of
/// `crate::gss::EdgeKind`.
pub fn pop_kind_bucket_index(kind: &crate::gss::EdgeKind) -> usize {
    use crate::gss::EdgeKind;
    match kind {
        EdgeKind::Generic => 0,
        EdgeKind::CategoryEntryRoot => 1,
        EdgeKind::CategoryEntryContinuation { .. } => 2,
        EdgeKind::CrossCatProjection { .. } => 3,
        EdgeKind::CrossCatLhs { .. } | EdgeKind::CrossCatLhsScoped { .. } => 4,
        EdgeKind::CrossCatLhsReentry { .. } => 5,
        EdgeKind::TransparentSourceReentry { .. } => 6,
        EdgeKind::PrefixRuleEntry { .. } => 7,
        EdgeKind::InfixContinuation { .. } => 8,
        EdgeKind::LexAltLiteral { .. } => 9,
        EdgeKind::OptionalGroupAt { .. } => 10,
        EdgeKind::BinderListLoopAt { .. } => 11,
        EdgeKind::CollectionElement { .. } => 12,
        EdgeKind::GroupingMarker { .. } => 13,
        EdgeKind::MixfixMarker { .. } => 14,
        EdgeKind::ReturnFrame { .. } => 15,
    }
}

/// Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27): human-
/// readable label for each `pop_kind_histogram` bucket index.
pub fn pop_kind_label(idx: usize) -> &'static str {
    [
        "Generic",
        "CategoryEntryRoot",
        "CategoryEntryContinuation",
        "CrossCatProjection",
        "CrossCatLhs",
        "CrossCatLhsReentry",
        "TransparentSourceReentry",
        "PrefixRuleEntry",
        "InfixContinuation",
        "LexAltLiteral",
        "OptionalGroupAt",
        "BinderListLoopAt",
        "CollectionElement",
        "GroupingMarker",
        "MixfixMarker",
        "ReturnFrame",
    ][idx.min(15)]
}

/// Phase F.13 chain_10000 plan-amend Substage 0 (2026-05-26):
/// counterfactual projection of the `EdgeStackArena` under Intervention A's
/// coarse `(parent, EdgeKind)` keying.
///
/// Used only with `--features walker-stats` + `PRATTAIL_WALKER_STATS=1`.
/// When the feature is off, every field stays at `Default` (empty
/// `Vec`/`FxHashMap`, zero counters) and `observe_push` is never called.
/// Memory cost when idle: ~48 bytes (empty Vec + empty FxHashMap).
///
/// Projection algorithm: each call to `observe_push` mirrors the actual
/// arena's `intern_push` against a shadow arena keyed by
/// `(projected_parent, EdgeKind, divergent_disambiguator)`. The
/// `projected_id_by_actual` sidecar maps each actual `StackId` to its
/// counterpart in the shadow arena, so the next push from the same
/// actual parent resolves the same projected parent. Divergent kinds
/// (per `EdgeKind::is_convergent`) keep the `GssEdgeId` in the key to
/// preserve Stage 3.12.6's wrong-pop defense; convergent kinds drop it
/// (this is where the coarse-dedup wins materialize).
#[derive(Default, Debug, Clone)]
pub struct EdgeKindProjection {
    /// Sidecar `projected_id_by_actual[actual_stack_id.0 as usize] =
    /// projected_stack_id`. `STACK_ID_ROOT` (== `u32::MAX`) is treated
    /// out-of-band — both projection root and actual root are the
    /// shared sentinel.
    pub projected_id_by_actual: Vec<crate::path_tree_arena::StackId>,
    /// Shadow arena dedup map. Key = `(projected_parent, EdgeKind,
    /// optional GssEdgeId)`. The third component is `Some(edge_id)` for
    /// divergent kinds, `None` for convergent — matching what
    /// Intervention A would key on.
    pub projection_dedup: FxHashMap<
        (
            crate::path_tree_arena::StackId,
            crate::gss::EdgeKind,
            Option<crate::gss::GssEdgeId>,
        ),
        crate::path_tree_arena::StackId,
    >,
    /// Distinct projected nodes seen (== shadow arena node count).
    pub projected_node_count: u32,
    /// Max `actual_new_id.0 + 1` observed — proxies the actual arena's
    /// node count so `projected_dedup_rate` is self-contained.
    pub actual_node_count_seen: u32,
    /// Total `observe_push` invocations (== total intern_push call
    /// attempts on the actual edge arena while instrumentation was on).
    pub observe_push_calls: u64,
    /// `observe_push` outcomes where the projection dedup hit an
    /// existing shadow entry. `projected_dedup_hit_ratio = hits /
    /// observe_push_calls` is the per-call hit rate (independent of
    /// the per-arena node ratio).
    pub projection_dedup_hits: u64,
}

impl EdgeKindProjection {
    /// Reset to empty (called from walker reset).
    pub fn clear(&mut self) {
        self.projected_id_by_actual.clear();
        self.projection_dedup.clear();
        self.projected_node_count = 0;
        self.actual_node_count_seen = 0;
        self.observe_push_calls = 0;
        self.projection_dedup_hits = 0;
    }

    /// Record an actual `intern_push(actual_parent, edge_id) ->
    /// actual_new_id` and mirror it through the shadow arena keyed by
    /// `(projected_parent, kind, divergent_disambiguator)`. Returns
    /// the projected `StackId` assigned (or hit) for this push.
    pub fn observe_push(
        &mut self,
        actual_parent: crate::path_tree_arena::StackId,
        actual_new_id: crate::path_tree_arena::StackId,
        kind: crate::gss::EdgeKind,
        edge_id: crate::gss::GssEdgeId,
    ) -> crate::path_tree_arena::StackId {
        use crate::path_tree_arena::{StackId, STACK_ID_ROOT};
        self.observe_push_calls = self.observe_push_calls.saturating_add(1);
        let projected_parent = if actual_parent == STACK_ID_ROOT {
            STACK_ID_ROOT
        } else {
            let idx = actual_parent.0 as usize;
            if idx < self.projected_id_by_actual.len() {
                self.projected_id_by_actual[idx]
            } else {
                // Parent was never observed — instrumentation gap.
                // Conservative fallback: treat as a fresh root chain.
                STACK_ID_ROOT
            }
        };
        let divergent_disambiguator = if kind.is_convergent() {
            None
        } else {
            Some(edge_id)
        };
        let key = (projected_parent, kind, divergent_disambiguator);
        let projected_new = if let Some(&existing) = self.projection_dedup.get(&key) {
            self.projection_dedup_hits = self.projection_dedup_hits.saturating_add(1);
            existing
        } else {
            let id = StackId(self.projected_node_count);
            self.projection_dedup.insert(key, id);
            self.projected_node_count = self.projected_node_count.saturating_add(1);
            id
        };
        let new_id_u = actual_new_id.0;
        if new_id_u != u32::MAX {
            let need = (new_id_u as usize).saturating_add(1);
            if self.projected_id_by_actual.len() < need {
                self.projected_id_by_actual.resize(need, STACK_ID_ROOT);
            }
            self.projected_id_by_actual[new_id_u as usize] = projected_new;
            if new_id_u.saturating_add(1) > self.actual_node_count_seen {
                self.actual_node_count_seen = new_id_u.saturating_add(1);
            }
        }
        projected_new
    }

    /// Compute the projected dedup ratio:
    /// `actual_node_count_seen / projected_node_count`. Returns 0.0
    /// when the projection has no nodes yet.
    pub fn projected_dedup_rate(&self) -> f64 {
        if self.projected_node_count == 0 {
            0.0
        } else {
            (self.actual_node_count_seen as f64) / (self.projected_node_count as f64)
        }
    }

    /// Per-call dedup hit ratio: fraction of `observe_push` calls that
    /// hit an existing projected entry. 0.0 when no calls yet.
    pub fn projected_dedup_hit_ratio(&self) -> f64 {
        if self.observe_push_calls == 0 {
            0.0
        } else {
            (self.projection_dedup_hits as f64) / (self.observe_push_calls as f64)
        }
    }
}

/// Phase F.13 chain_10000 Exp 14 Substage 0 (2026-05-27): TomitaKey
/// coarse-merge projection counters. Mirrors what `TomitaFrontierMap`
/// would dedup if the walker keyed cursors on the 5-tuple
/// `(state, node, pos, edge_top, collection_depth)` (per Tomita 1985 /
/// Scott-Johnstone 2010 GLL-descriptor coarsening of the current 11-axis
/// ConfigKey).
///
/// Plan ref: `prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`
/// §5 Substage 0. The gate is "projected dedup ratio ≥ 5×" on
/// left_assoc_chain_500. If FAILS, downstream Exp 14 substages SKIP.
///
/// Per-step semantics: each `step_fanout` iteration observes the cursor
/// population pre-step. For Concrete frames, observe once per cursor.
/// For Cohort frames, observe N times (once per member) — all members
/// share the same TomitaKey by construction of the cohort. Distinct
/// TomitaKeys are counted PER STEP (different step generations should
/// not merge because Tomita-merge is bounded by step boundaries via the
/// generation counter in the planned TomitaFrontierMap).
///
/// Aggregate metric:
/// `cumulative_cursors_ingested / cumulative_per_step_distinct_keys`
/// = average per-step merge factor over the parse.
#[derive(Default, Debug, Clone)]
pub struct TomitaKeyProjection {
    /// Per-step working set of distinct TomitaKey values; cleared at
    /// each `step_fanout` entry via `begin_step`.
    pub per_step_distinct_keys: FxHashMap<TomitaKey, u64>,
    /// Total cursor observations across all steps (sum of per-step
    /// frontier sizes; counts cohort members individually).
    pub cumulative_cursors_ingested: u64,
    /// Total distinct TomitaKeys summed across all steps (= sum of
    /// per_step_distinct_keys.len() at each `end_step`).
    pub cumulative_per_step_distinct_keys: u64,
    /// Per-step max ingest count (peak frontier observed at any single
    /// step, in cursor units).
    pub max_cursors_per_step: u64,
    /// Per-step max distinct-key count.
    pub max_distinct_keys_per_step: u64,
    /// Step count actually observed.
    pub observed_steps: u64,
}

/// Phase F.13 chain_10000 Exp 14 Substage 0 (2026-05-27): the coarse
/// merge key that the planned `TomitaFrontierMap` would use. Drops the
/// four lex provenance axes plus `cohort_origin` plus `sppf_top` from
/// the current `ConfigKey` 11-tuple. Cursors with the same TomitaKey
/// but distinct ConfigKey would arc-merge under Intervention A of
/// `exp14-tomita-per-arc-gss-merge.md` §2.3.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct TomitaKey {
    pub state: crate::wpda_runtime::WpdaState,
    pub node: crate::gss::GssNodeId,
    pub pos: usize,
    pub incoming_edge_top: Option<crate::gss::GssEdgeId>,
    pub collection_depth: u8,
}

impl TomitaKeyProjection {
    /// Reset to empty (called from walker reset).
    pub fn clear(&mut self) {
        self.per_step_distinct_keys.clear();
        self.cumulative_cursors_ingested = 0;
        self.cumulative_per_step_distinct_keys = 0;
        self.max_cursors_per_step = 0;
        self.max_distinct_keys_per_step = 0;
        self.observed_steps = 0;
    }

    /// Begin a new step: clear the per-step distinct-key working set.
    /// Call at the top of `step_fanout`.
    pub fn begin_step(&mut self) {
        self.per_step_distinct_keys.clear();
    }

    /// Observe one cursor with its TomitaKey + member-multiplicity
    /// (1 for Concrete, N for a Cohort frame member-count). The
    /// caller is expected to increment by the per-frame contribution.
    pub fn observe(&mut self, key: TomitaKey, count: u64) {
        if count == 0 {
            return;
        }
        let entry = self.per_step_distinct_keys.entry(key).or_insert(0);
        *entry = entry.saturating_add(count);
        self.cumulative_cursors_ingested = self.cumulative_cursors_ingested.saturating_add(count);
    }

    /// End the current step: roll per-step distinct count into cumulative.
    /// Call after every frame in `step_fanout` is processed.
    pub fn end_step(&mut self) {
        let distinct = self.per_step_distinct_keys.len() as u64;
        if distinct == 0 {
            return;
        }
        let cursors_this_step: u64 = self.per_step_distinct_keys.values().copied().sum();
        self.cumulative_per_step_distinct_keys = self
            .cumulative_per_step_distinct_keys
            .saturating_add(distinct);
        if cursors_this_step > self.max_cursors_per_step {
            self.max_cursors_per_step = cursors_this_step;
        }
        if distinct > self.max_distinct_keys_per_step {
            self.max_distinct_keys_per_step = distinct;
        }
        self.observed_steps = self.observed_steps.saturating_add(1);
        self.per_step_distinct_keys.clear();
    }

    /// Average per-step merge factor = average bucket size under TomitaKey
    /// keying. Higher = more reduction. Gate: ≥ 5.0 per the plan.
    pub fn projected_dedup_rate(&self) -> f64 {
        if self.cumulative_per_step_distinct_keys == 0 {
            0.0
        } else {
            (self.cumulative_cursors_ingested as f64)
                / (self.cumulative_per_step_distinct_keys as f64)
        }
    }
}

/// Phase F.13 chain_10000 Exp 15 Substage 0 (2026-05-27): CPS
/// continuation record size projection. Counterfactual measurement of
/// the size distribution `Continuation::ApplyAction { cursor_id, action }`
/// records would have under the planned CPS rewrite (see
/// `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` §3.1).
///
/// Plan gate: P50 record size ≤ 32 B AND P99 ≤ 64 B on
/// left_assoc_chain_500. If FAILS, the per-record cost will not deliver
/// the projected 5.3× per-cursor reduction; downstream substages SKIP.
///
/// Histogram buckets (8 bands): 0-7, 8-15, 16-31, 32-63, 64-127, 128-255,
/// 256-511, 512+. P50 ≤ 32 ⇔ cumulative count through band 3 ≥ 50 %;
/// P99 ≤ 64 ⇔ cumulative through band 4 ≥ 99 %.
///
/// Separately tracks `step_continuations_emitted` (the count of small
/// 8-byte `Continuation::Step { cursor_id }` records that the Fork-arm
/// broadcast would enqueue) — these are NOT included in the ApplyAction
/// size histogram because their size is uniformly 8 B by construction.
#[derive(Default, Debug, Clone)]
pub struct ContinuationSizeProjection {
    /// Size histogram for `Continuation::ApplyAction` records (bytes).
    pub apply_action_size_histogram: [u64; 8],
    /// Sum of observed sizes (for mean).
    pub apply_action_size_sum_bytes: u64,
    /// Count of `ApplyAction` continuations observed.
    pub apply_action_observations: u64,
    /// Maximum observed `ApplyAction` size.
    pub apply_action_size_max_bytes: u64,
    /// Count of `Continuation::Step` records the Fork-arm broadcast
    /// would enqueue (= sum of branches.len() over Fork actions).
    pub step_continuations_emitted: u64,
    /// Per-action-variant counts (17 variants in `WpdaStepAction` +
    /// Other catch-all). Index matches `continuation_size_variant_index`
    /// helper below.
    pub action_variant_counts: [u64; 19],
}

/// Power-of-two-ish bucket for continuation size (matches the histogram
/// bands documented on `ContinuationSizeProjection`).
pub fn continuation_size_bucket(size_bytes: usize) -> usize {
    match size_bytes {
        0..=7 => 0,
        8..=15 => 1,
        16..=31 => 2,
        32..=63 => 3,
        64..=127 => 4,
        128..=255 => 5,
        256..=511 => 6,
        _ => 7, // 512+
    }
}

impl ContinuationSizeProjection {
    /// Reset to empty (called from walker reset).
    pub fn clear(&mut self) {
        self.apply_action_size_histogram = [0; 8];
        self.apply_action_size_sum_bytes = 0;
        self.apply_action_observations = 0;
        self.apply_action_size_max_bytes = 0;
        self.step_continuations_emitted = 0;
        self.action_variant_counts = [0; 19];
    }

    /// Record an ApplyAction observation: size in bytes + variant index
    /// + number of Fork children (0 for non-Fork variants).
    pub fn observe_apply_action(
        &mut self,
        size_bytes: usize,
        variant_index: usize,
        fork_children: usize,
    ) {
        let bucket = continuation_size_bucket(size_bytes);
        self.apply_action_size_histogram[bucket] =
            self.apply_action_size_histogram[bucket].saturating_add(1);
        self.apply_action_size_sum_bytes = self
            .apply_action_size_sum_bytes
            .saturating_add(size_bytes as u64);
        self.apply_action_observations = self.apply_action_observations.saturating_add(1);
        let size_u64 = size_bytes as u64;
        if size_u64 > self.apply_action_size_max_bytes {
            self.apply_action_size_max_bytes = size_u64;
        }
        if variant_index < self.action_variant_counts.len() {
            self.action_variant_counts[variant_index] =
                self.action_variant_counts[variant_index].saturating_add(1);
        }
        if fork_children > 0 {
            self.step_continuations_emitted = self
                .step_continuations_emitted
                .saturating_add(fork_children as u64);
        }
    }

    /// Mean ApplyAction continuation size in bytes (0 if no observations).
    pub fn mean_apply_action_size(&self) -> f64 {
        if self.apply_action_observations == 0 {
            0.0
        } else {
            (self.apply_action_size_sum_bytes as f64) / (self.apply_action_observations as f64)
        }
    }

    /// Returns true iff the histogram indicates P50 ≤ p50_max AND P99 ≤
    /// p99_max under the plan's bucketing. Each bound is mapped to a
    /// bucket index via `continuation_size_bucket`.
    pub fn passes_size_gate(&self, p50_max: usize, p99_max: usize) -> bool {
        if self.apply_action_observations == 0 {
            return false;
        }
        let total = self.apply_action_observations;
        let p50_bucket = continuation_size_bucket(p50_max);
        let p99_bucket = continuation_size_bucket(p99_max);
        // Cumulative through p50_bucket.
        let cum_p50: u64 = self.apply_action_size_histogram[..=p50_bucket].iter().sum();
        let cum_p99: u64 = self.apply_action_size_histogram[..=p99_bucket].iter().sum();
        let p50_ok = (cum_p50 as f64) / (total as f64) >= 0.50;
        let p99_ok = (cum_p99 as f64) / (total as f64) >= 0.99;
        p50_ok && p99_ok
    }
}

/// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): instrumentation
/// gate for weight-keyed lazy Fork-arm traversal.
///
/// Counts:
/// - `created`: per Fork-arm child that would be enqueued as a
///   compact deferred branch record in the planned lazy walker. Incremented at
///   every `children.push(child)` site in `wpda_walker.rs` Fork arm
///   (lines 5855-7323; 23 sites total).
/// - `forced`: per cursor that actually enters `apply_action_to_cursor`.
///   In the lazy redesign these correspond to thunks popped from the
///   weight-keyed min-heap and materialized.
/// - `seed_cursors`: per cursor created via seed / commit-winner
///   write-back (NOT Fork-arm fan-out — lines 5027, 5100). Tracked
///   separately so the ratio reflects fan-out laziness, not the
///   constant seed-cost.
///
/// Decision rule (chain_500 LEFT-assoc): if
/// `forced / created >= 0.5`, abort the lazy plan — the min-heap will
/// bottom out at the same materialization count as the eager Vec. If
/// `forced / created < 0.5`, proceed to L1.
///
/// Per-Fork-kind histogram: `by_action_kind` tracks how many created
/// thunks fall into each `ForkActionKind` bucket. Index correspondence:
///   0 = Push                (chain-interior dominant)
///   1 = OptGroupAbsent      (optional-group absent arm)
///   2 = ConsumeAndReplace   (lex shift + state replace)
///   3 = ConsumeAndPop       (lex shift + GSS pop)
///   4 = ConsumeAndCaptureAndPush (binder capture)
///   5 = ConsumeIdentAndReplace
///   6 = ConsumeIdentAndPop
///   7 = ConsumeAndReplaceWithEffect
///   8 = Consume             (plain lex shift)
///   9 = LexAlt              (lex-alt fork)
///  10 = LexAltPrefixOp
///  11 = LexAltPostfixOp
///  12 = LexAltInfixOp
///  13 = LexAltMixfixOp
///  14 = Other catch-all
#[derive(Default, Debug, Clone)]
pub struct ThunkForceRatioProjection {
    /// Total Fork-arm children that would be enqueued as thunks
    /// (current eager walker materializes them all immediately).
    pub created: u64,
    /// Total cursors that actually entered `apply_action_to_cursor`.
    /// In the lazy walker these correspond to thunks force-popped from
    /// the priority queue.
    pub forced: u64,
    /// Seed / commit-winner write-back cursors (NOT Fork-arm). Tracked
    /// separately so the force-ratio reflects fan-out laziness.
    pub seed_cursors: u64,
    /// Per-kind histogram (15 buckets per documentation above).
    pub by_action_kind: [u64; 15],
}

impl ThunkForceRatioProjection {
    pub fn clear(&mut self) {
        self.created = 0;
        self.forced = 0;
        self.seed_cursors = 0;
        self.by_action_kind = [0; 15];
    }

    /// Record one Fork-arm child that would be enqueued lazily.
    pub fn observe_created(&mut self, kind_index: usize) {
        self.created = self.created.saturating_add(1);
        let idx = if kind_index < 15 { kind_index } else { 14 };
        self.by_action_kind[idx] = self.by_action_kind[idx].saturating_add(1);
    }

    /// Record one cursor entering `apply_action_to_cursor` (= thunk
    /// force in the lazy redesign).
    pub fn observe_forced(&mut self) {
        self.forced = self.forced.saturating_add(1);
    }

    /// Record one seed / commit-winner write-back cursor.
    pub fn observe_seed(&mut self) {
        self.seed_cursors = self.seed_cursors.saturating_add(1);
    }

    /// force / created ratio. 0.0 if no created thunks. The L0 gate
    /// passes iff this is `< 0.5` on left_assoc_chain_500.
    pub fn force_ratio(&self) -> f64 {
        if self.created == 0 {
            0.0
        } else {
            (self.forced as f64) / (self.created as f64)
        }
    }

    /// Projected memory savings as a multiplier (eager_bytes /
    /// lazy_bytes) under the substitution `BranchCursor (~3 KB) →
    /// compact deferred branch record (~64 B avg)`. Conservative — assumes deferred
    /// thunks stay in the heap for the parse duration (worst case).
    pub fn projected_memory_savings_multiplier(&self) -> f64 {
        const BYTES_PER_BRANCH_CURSOR: f64 = 3072.0;
        const BYTES_PER_THUNK: f64 = 64.0;
        if self.created == 0 {
            return 0.0;
        }
        let eager_bytes = (self.created as f64) * BYTES_PER_BRANCH_CURSOR;
        let forced_materialized_bytes = (self.forced as f64) * BYTES_PER_BRANCH_CURSOR;
        let deferred_thunk_bytes =
            ((self.created - self.forced.min(self.created)) as f64) * BYTES_PER_THUNK;
        let lazy_bytes = forced_materialized_bytes + deferred_thunk_bytes;
        if lazy_bytes <= 0.0 {
            0.0
        } else {
            eager_bytes / lazy_bytes
        }
    }
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
        // BCC SHADOW (Plan afde9c48, Stage 0 — the DECISIVE S0-G-LINEAR + the
        // gravest S0-G-Cont). Prints only when PRATTAIL_BCC_SHADOW populated it.
        if self.bcc_shadow_calls > 0 {
            writeln!(
                f,
                "  BCC-SHADOW: peak_pre_merge_real={} bcc_peak_SEALED={} bcc_peak_noseal={} bcc_peak_MAXIMAL={} bcc_peak_GLL_FLOOR={}  (S0-G-LINEAR: SEALED linear-in-k ⇒ PASS; MAXIMAL/GLL_FLOOR exponential ⇒ derivation-multiplicity floor, no seal linearizes)",
                self.branch_cursors_peak_pre_merge,
                self.bcc_shadow_peak_pre_merge,
                self.bcc_shadow_peak_noseal,
                self.bcc_shadow_peak_maximal,
                self.bcc_shadow_peak_gll_floor,
            )?;
            writeln!(
                f,
                "  BCC-SHADOW S0-G-Cont: seal_type_CONFLICTS={} seal_agreements={}  (CONFLICTS MUST be 0 — nonzero = two different-typed @a readings forced to one continuation = cycle-2 wall)",
                self.bcc_shadow_seal_type_conflicts,
                self.bcc_shadow_seal_agreements,
            )?;
        }
        // DW SHADOW (Plan aaf070b3 / DESCRIPTOR_WORKLIST_DESIGN.md, Stage 0 — the
        // 3-way gate S0-DW-LINEAR / S0-DW-SOUND / RT-7). Prints only when
        // PRATTAIL_DW_SHADOW populated it.
        if self.dw_shadow_calls > 0 {
            writeln!(
                f,
                "  DW-SHADOW S0-DW-LINEAR: peak_pre_merge_real={} dw_shadow_peak(R)={} dw_peak_MAXIMAL_R={} bcc_GLL_FLOOR={}  (PASS iff dw_shadow_peak LINEAR-in-k tracking GLL_FLOOR while real is exponential; HALT if super-linear)",
                self.branch_cursors_peak_pre_merge,
                self.dw_shadow_peak,
                self.dw_shadow_peak_maximal_r,
                self.bcc_shadow_peak_gll_floor,
            )?;
            writeln!(
                f,
                "  DW-SHADOW S0-DW-SOUND: pop_target_CONFLICTS={} seal_type_CONFLICTS={} seal_agreements={}  (BOTH conflicts MUST be 0 — pop_target>0 = cycle-3 wrong-body revive; seal_type>0 = different-typed @a readings on one continuation. THE make-or-break.)",
                self.dw_pop_target_conflicts,
                self.dw_seal_type_conflicts,
                self.dw_seal_agreements,
            )?;
            writeln!(
                f,
                "  DW-SHADOW RT-7 tripwire: dw_return_fires={}  (MUST be >= k for @a<-c & … k-segment list, else the .*sep-return reconvergence site is WRONG = the M0 fires-0x failure → HALT+relocate)",
                self.dw_return_fires,
            )?;
            writeln!(
                f,
                "  DW-SHADOW LINEARITY-BISECT (edge-stack axis, coarsest→finest): variant_seq={} variant_multiset={} variant_set={} crosscat_count={} len={} | GLL_FLOOR(drop)={}  (find the coarsest that is LINEAR-in-k)",
                self.dw_bisect_variant_seq,
                self.dw_bisect_variant_multiset,
                self.dw_bisect_variant_set,
                self.dw_bisect_crosscat_count,
                self.dw_bisect_len,
                self.bcc_shadow_peak_gll_floor,
            )?;
            writeln!(
                f,
                "  DW-SHADOW LINEAR-KEY SOUNDNESS (crosscat_count): pop_target_CONFLICTS={} agreements={}  (the ONLY linear edge-stack key's soundness — nonzero ⇒ the linear projection over-merges incompatible pops ⇒ S0-DW-SOUND HALT)",
                self.dw_count_pop_conflicts,
                self.dw_count_agreements,
            )?;
        }
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
            "  cursors_dropped: resolution={} explicit={} outcome={} merge={} sr_subsume={}",
            self.cursors_dropped_via_resolution_check,
            self.cursors_dropped_via_explicit_drop,
            self.cursors_dropped_via_outcome_drop,
            self.cursors_dropped_via_merge,
            self.cursors_dropped_via_sr_subsume,
        )?;
        writeln!(
            f,
            "  fork_total={}  recovery_dispatches={}  cross_cat_branches={}",
            self.fork_total, self.fork_recovery_dispatches, self.fork_cross_cat_projection_branches,
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
        let node_only_total: u64 = self.merge_miss_node_only_by_context.iter().sum();
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
        let edge_only_total: u64 = self.merge_miss_edge_only_by_context.iter().sum();
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
        // Phase F.13 chain_10000 Exp 16 (2026-05-26): walker memory
        // attribution with byte-estimated breakdown.
        if self.mem_attr_branch_cursors_max
            + self.mem_attr_cache_entries_max
            + self.mem_attr_sppf_nodes_max
            > 0
        {
            // Per-element size estimates (bytes). Conservative — actual
            // sizes include Arc'd heap allocations not counted here.
            const SZ_BRANCH_CURSOR: u64 = 512; // BranchCursor (post path-tree arenas)
            const SZ_CACHE_ENTRY_BASE: u64 = 256;
            const SZ_COHORT_MEMBER_STATE: u64 = 96; // CohortMemberState
            const SZ_WORKER_SNAPSHOT: u64 = 96; // WorkerSnapshot
            const SZ_COHORT_CONTINUATION: u64 = 64; // CohortContinuation (Exp 9 S1.a)
            const SZ_PATH_TREE_NODE: u64 = 16;
            const SZ_SPPF_NODE: u64 = 56; // largest variant ~48-56 B
            const SZ_SPPF_LINK: u64 = 8;
            let mb = |b: u64| b as f64 / (1024.0 * 1024.0);
            let branch_b = self.mem_attr_branch_cursors_max * SZ_BRANCH_CURSOR;
            let cache_base_b = self.mem_attr_cache_entries_max * SZ_CACHE_ENTRY_BASE;
            let pending_b = self.mem_attr_cache_pending_members_sum_max * SZ_COHORT_MEMBER_STATE;
            let snap_b = self.mem_attr_cache_worker_snapshots_sum_max * SZ_WORKER_SNAPSHOT;
            let cont_b =
                self.mem_attr_cache_deferred_continuations_sum_max * SZ_COHORT_CONTINUATION;
            let sppf_stack_b = self.mem_attr_sppf_stack_arena_nodes_max * SZ_PATH_TREE_NODE;
            let edge_stack_b =
                self.mem_attr_incoming_edge_stack_arena_nodes_max * SZ_PATH_TREE_NODE;
            let sppf_nodes_b = self.mem_attr_sppf_nodes_max * SZ_SPPF_NODE;
            let sppf_links_b = self.mem_attr_sppf_symbol_packings_max * SZ_SPPF_LINK;
            const SZ_GSS_NODE: u64 = 64; // WpdaGssNode {pos, symbol, ...}
            const SZ_GSS_EDGE: u64 = 64; // WpdaGssEdge {from, to, weight, ...}
            const SZ_FXHASHSET_ENTRY: u64 = 24;
            const SZ_RECOVERY_DELTA: u64 = 64;
            const SZ_SPPF_TERM_ENTRY: u64 = 32;
            let gss_nodes_b = self.mem_attr_gss_nodes_max * SZ_GSS_NODE;
            let gss_edges_b = self.mem_attr_gss_edges_max * SZ_GSS_EDGE;
            let vd_entries_b =
                self.mem_attr_visited_dispatch_total_entries_max * SZ_FXHASHSET_ENTRY;
            let rd_arcs_b = self.mem_attr_recovery_deltas_unique_arcs_max * SZ_RECOVERY_DELTA;
            let sppf_terms_b = self.mem_attr_sppf_symbol_terms_max * SZ_SPPF_TERM_ENTRY;
            let total_b = branch_b
                + cache_base_b
                + pending_b
                + snap_b
                + cont_b
                + sppf_stack_b
                + edge_stack_b
                + sppf_nodes_b
                + sppf_links_b
                + gss_nodes_b
                + gss_edges_b
                + vd_entries_b
                + rd_arcs_b
                + sppf_terms_b;
            writeln!(
                f,
                "  mem_attr (peak; conservative — Arc'd heap not counted): total={:.2} MB",
                mb(total_b),
            )?;
            let pct = |b: u64| {
                if total_b == 0 {
                    0.0
                } else {
                    100.0 * b as f64 / total_b as f64
                }
            };
            writeln!(
                f,
                "    branch_cursors      = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_branch_cursors_max,
                SZ_BRANCH_CURSOR,
                mb(branch_b),
                pct(branch_b),
            )?;
            writeln!(
                f,
                "    cohort cache base   = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_cache_entries_max,
                SZ_CACHE_ENTRY_BASE,
                mb(cache_base_b),
                pct(cache_base_b),
            )?;
            writeln!(
                f,
                "    pending_members     = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_cache_pending_members_sum_max,
                SZ_COHORT_MEMBER_STATE,
                mb(pending_b),
                pct(pending_b),
            )?;
            writeln!(
                f,
                "    worker_snapshots    = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_cache_worker_snapshots_sum_max,
                SZ_WORKER_SNAPSHOT,
                mb(snap_b),
                pct(snap_b),
            )?;
            writeln!(
                f,
                "    deferred_continuations = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_cache_deferred_continuations_sum_max,
                SZ_COHORT_CONTINUATION,
                mb(cont_b),
                pct(cont_b),
            )?;
            writeln!(
                f,
                "    sppf_stack_arena    = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_sppf_stack_arena_nodes_max,
                SZ_PATH_TREE_NODE,
                mb(sppf_stack_b),
                pct(sppf_stack_b),
            )?;
            writeln!(
                f,
                "    edge_stack_arena    = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_incoming_edge_stack_arena_nodes_max,
                SZ_PATH_TREE_NODE,
                mb(edge_stack_b),
                pct(edge_stack_b),
            )?;
            writeln!(
                f,
                "    sppf_nodes          = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_sppf_nodes_max,
                SZ_SPPF_NODE,
                mb(sppf_nodes_b),
                pct(sppf_nodes_b),
            )?;
            writeln!(
                f,
                "    sppf_symbol_packings = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_sppf_symbol_packings_max,
                SZ_SPPF_LINK,
                mb(sppf_links_b),
                pct(sppf_links_b),
            )?;
            writeln!(
                f,
                "    gss_nodes           = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_gss_nodes_max,
                SZ_GSS_NODE,
                mb(gss_nodes_b),
                pct(gss_nodes_b),
            )?;
            writeln!(
                f,
                "    gss_edges           = {} × {:>4} B = {:>8.2} MB ({:>5.1}%)",
                self.mem_attr_gss_edges_max,
                SZ_GSS_EDGE,
                mb(gss_edges_b),
                pct(gss_edges_b),
            )?;
            writeln!(
                f,
                "    visited_dispatch (unique Arcs / total entries) = {} / {} ({} dedup ratio); entries × {} B = {:.2} MB ({:.1}%)",
                self.mem_attr_visited_dispatch_unique_arcs_max,
                self.mem_attr_visited_dispatch_total_entries_max,
                if self.mem_attr_visited_dispatch_unique_arcs_max > 0 {
                    self.mem_attr_visited_dispatch_total_entries_max as f64
                        / self.mem_attr_visited_dispatch_unique_arcs_max as f64
                } else {
                    0.0
                },
                SZ_FXHASHSET_ENTRY,
                mb(vd_entries_b),
                pct(vd_entries_b),
            )?;
            writeln!(
                f,
                "    recovery_deltas (unique Arcs) = {} × {} B = {:.2} MB ({:.1}%)",
                self.mem_attr_recovery_deltas_unique_arcs_max,
                SZ_RECOVERY_DELTA,
                mb(rd_arcs_b),
                pct(rd_arcs_b),
            )?;
            writeln!(
                f,
                "    sppf_symbol_terms (walker memo) = {} × {} B = {:.2} MB ({:.1}%)",
                self.mem_attr_sppf_symbol_terms_max,
                SZ_SPPF_TERM_ENTRY,
                mb(sppf_terms_b),
                pct(sppf_terms_b),
            )?;
            // Exp 16 round 3: extra structures previously uncounted.
            let text_arena_b = self.mem_attr_sppf_text_arena_bytes_max;
            let dedup_packing_keys_b = self.mem_attr_sppf_dedup_packing_children_bytes_max;
            const SZ_SPLICE_SLOT_BASE: u64 = 24;
            const SZ_LEX_FORK_STAMP: u64 = 16;
            let splice_b = self.mem_attr_sppf_collection_arena_total_entries_max * 4
                + self.mem_attr_sppf_collection_arena_unique_arcs_max * SZ_SPLICE_SLOT_BASE;
            let lex_fork_b = self.mem_attr_lex_fork_path_total_entries_max * SZ_LEX_FORK_STAMP;
            writeln!(f, "  Exp 16 round 3 — additional structures (NOT in 'total' above):",)?;
            writeln!(
                f,
                "    sppf.text_arena                = {} B = {:.2} MB",
                text_arena_b,
                mb(text_arena_b),
            )?;
            writeln!(
                f,
                "    sppf.text_index                = {} entries × 8 B = {:.2} MB",
                self.mem_attr_sppf_text_index_count_max,
                mb(self.mem_attr_sppf_text_index_count_max * 8),
            )?;
            writeln!(
                f,
                "    sppf.dedup_packing keys (sum Vec<SppfId> child bytes) = {} B = {:.2} MB",
                dedup_packing_keys_b,
                mb(dedup_packing_keys_b),
            )?;
            writeln!(
                f,
                "    sppf.dedup_symbol entries      = {} × ~16 B = {:.2} MB",
                self.mem_attr_sppf_dedup_symbol_count_max,
                mb(self.mem_attr_sppf_dedup_symbol_count_max * 16),
            )?;
            writeln!(
                f,
                "    sppf.dedup_terminal entries    = {} × ~32 B = {:.2} MB",
                self.mem_attr_sppf_dedup_terminal_count_max,
                mb(self.mem_attr_sppf_dedup_terminal_count_max * 32),
            )?;
            writeln!(
                f,
                "    sppf_collection_arena (unique Arcs / total entries) = {} / {}; entries × 4 B + arcs × {} B = {:.2} MB",
                self.mem_attr_sppf_collection_arena_unique_arcs_max,
                self.mem_attr_sppf_collection_arena_total_entries_max,
                SZ_SPLICE_SLOT_BASE,
                mb(splice_b),
            )?;
            writeln!(
                f,
                "    lex_fork_path (unique Arcs / total entries) = {} / {}; entries × {} B = {:.2} MB",
                self.mem_attr_lex_fork_path_unique_arcs_max,
                self.mem_attr_lex_fork_path_total_entries_max,
                SZ_LEX_FORK_STAMP,
                mb(lex_fork_b),
            )?;
            writeln!(
                f,
                "    binder_scope_marks (unique Arcs) = {}",
                self.mem_attr_binder_scope_marks_unique_arcs_max,
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
                    write!(f, " [{}-{}%]={}({:.1}%)", i * 10, (i + 1) * 10, count, pct,)?;
                }
            }
            writeln!(f)?;
            // Gate: per Plan agent, PROCEED to S1.b iff bucket 5-9 sum
            // (≥ 50 % candidates) ≥ 50 % of samples AND window-histogram
            // bucket 2+ (≥ 12.5 % window) ≥ 10 % of samples.
            let cand_50plus: u64 = self.sppf_reclaimable_nodes_pct_histogram[5..].iter().sum();
            let window_12plus: u64 = self.sppf_reclaim_window_histogram[2..].iter().sum();
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
                self.fork_branches_by_class[0] as f64 / self.fork_total_by_class[0].max(1) as f64,
                self.fork_branches_by_class[1] as f64 / self.fork_total_by_class[1].max(1) as f64,
                self.fork_branches_by_class[2] as f64 / self.fork_total_by_class[2].max(1) as f64,
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
        if self.fork_cross_cat_projection_branches > 0 {
            writeln!(f, "  cross_cat: total_branches={}", self.fork_cross_cat_projection_branches,)?;
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
                    "state",
                    "node",
                    "edge",
                    "depth",
                    "cohort_origin",
                    "sppf_top",
                    "lex_alt_idx",
                    "weight_src_idx",
                    "weight_rule_idx",
                    "lex_fork_stamp",
                ];
                write!(f, "  merge_miss_multi_participation:")?;
                for (i, n) in names.iter().enumerate() {
                    let c = self.merge_miss_multi_participation[i];
                    let multi_denom = self.merge_miss_multi_diff_total as f64;
                    write!(f, " {}={} ({:.1}%)", n, c, 100.0 * c as f64 / multi_denom,)?;
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
                self.incoming_edge_stack_len_samples, self.incoming_edge_stack_len_max,
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
                self.recovery_deltas_len_samples, self.recovery_deltas_len_max,
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
                self.visited_dispatch_len_samples, self.visited_dispatch_len_max,
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
                self.visited_recovery_len_samples, self.visited_recovery_len_max,
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
                self.binder_scope_marks_len_samples, self.binder_scope_marks_len_max,
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
                self.optional_scope_marks_len_samples, self.optional_scope_marks_len_max,
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
                self.binder_scope_names_len_samples, self.binder_scope_names_len_max,
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
            "state",
            "node",
            "edge",
            "depth",
            "cohort_origin",
            "sppf_top",
            "lex_alt_idx",
            "weight_src_idx",
            "weight_rule_idx",
            "lex_fork_stamp",
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
        // Phase F.13 chain_10000 plan-amend Substage 0 (2026-05-26):
        // EdgeKind projected dedup gate. Shows the counterfactual arena
        // node count + ratio under Intervention A's keying scheme.
        if self.edge_kind_projection.observe_push_calls > 0 {
            writeln!(f, "  edge_kind_projection (Intervention A counterfactual):")?;
            writeln!(
                f,
                "    observe_push_calls={} projected_nodes={} actual_nodes_seen={} dedup_ratio={:.2}x hit_ratio={:.4}",
                self.edge_kind_projection.observe_push_calls,
                self.edge_kind_projection.projected_node_count,
                self.edge_kind_projection.actual_node_count_seen,
                self.edge_kind_projection.projected_dedup_rate(),
                self.edge_kind_projection.projected_dedup_hit_ratio(),
            )?;
        }
        // Phase F.13 chain_10000 Exp 14 Substage 0 (2026-05-27):
        // TomitaKey projected merge gate. Shows the counterfactual
        // per-step distinct-key count + merge factor under the planned
        // TomitaFrontierMap keying.
        if self.tomita_key_projection.observed_steps > 0 {
            writeln!(f, "  tomita_key_projection (Exp 14 counterfactual):")?;
            writeln!(
                f,
                "    observed_steps={} cumulative_cursors={} cumulative_distinct_keys={} avg_merge_factor={:.2}x max_cursors_per_step={} max_distinct_per_step={}",
                self.tomita_key_projection.observed_steps,
                self.tomita_key_projection.cumulative_cursors_ingested,
                self.tomita_key_projection.cumulative_per_step_distinct_keys,
                self.tomita_key_projection.projected_dedup_rate(),
                self.tomita_key_projection.max_cursors_per_step,
                self.tomita_key_projection.max_distinct_keys_per_step,
            )?;
        }
        // Phase F.13 chain_10000 Exp 15 Substage 0 (2026-05-27):
        // CPS continuation size projection. Shows the counterfactual
        // record size distribution + gate status.
        if self.continuation_size_projection.apply_action_observations > 0 {
            writeln!(f, "  continuation_size_projection (Exp 15 counterfactual):")?;
            let hist = self
                .continuation_size_projection
                .apply_action_size_histogram;
            writeln!(
                f,
                "    apply_action observations={} mean={:.1}B max={}B step_continuations_emitted={}",
                self.continuation_size_projection.apply_action_observations,
                self.continuation_size_projection.mean_apply_action_size(),
                self.continuation_size_projection.apply_action_size_max_bytes,
                self.continuation_size_projection.step_continuations_emitted,
            )?;
            writeln!(
                f,
                "    apply_action size histogram [0-7,8-15,16-31,32-63,64-127,128-255,256-511,512+]: {:?}",
                hist,
            )?;
            let p50_pass = self.continuation_size_projection.passes_size_gate(32, 64);
            writeln!(
                f,
                "    gate (P50<=32 AND P99<=64): {}",
                if p50_pass { "PASS" } else { "FAIL" },
            )?;
        }
        // Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27):
        // apply_action_to_cursor variant histogram — identifies the
        // dominant arm so L2-L3 can target it for graduation.
        let action_total: u64 = self.apply_action_variant_histogram.iter().sum();
        if action_total > 0 {
            writeln!(f, "  apply_action_variant_histogram (Lazy redesign L2 prep-2):")?;
            writeln!(f, "    total apply_action calls: {}", action_total)?;
            // Sort buckets descending by count for the top-5 view.
            let mut indexed: Vec<(usize, u64)> = self
                .apply_action_variant_histogram
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, c)| *c > 0)
                .collect();
            indexed.sort_by(|a, b| b.1.cmp(&a.1));
            for (i, count) in &indexed {
                let pct = 100.0 * (*count as f64) / (action_total as f64);
                writeln!(
                    f,
                    "    [{:>2}] {:<22} = {:>10} ({:>5.1}%)",
                    i,
                    crate::walker_stats::apply_action_variant_label(*i),
                    count,
                    pct,
                )?;
            }
        }
        // Phase F.13 chain_10000 Plan v6 H2 (2026-05-27): chain-region
        // Earley absorption trigger stats.
        if self.chain_earley_trigger_count > 0 {
            let avg_atoms = if self.chain_earley_succeeded_count > 0 {
                (self.chain_earley_atoms_absorbed_sum as f64)
                    / (self.chain_earley_succeeded_count as f64)
            } else {
                0.0
            };
            writeln!(f, "  chain_earley_absorption (Plan v6 H2):",)?;
            writeln!(
                f,
                "    trigger_count={} succeeded={} returned_none={} avg_atoms_absorbed={:.1}",
                self.chain_earley_trigger_count,
                self.chain_earley_succeeded_count,
                self.chain_earley_returned_none_count,
                avg_atoms,
            )?;
        }
        // Phase F.13 chain_10000 COQ-S0 (2026-05-27): cohort_origin
        // distinct count vs EquivKey collision rate.
        if !self.cohort_origin_dispatch_keys_seen.is_empty() {
            let dispatch_distinct = self.cohort_origin_dispatch_keys_seen.len() as u64;
            let equiv_distinct = self.cohort_origin_equiv_keys_seen.len() as u64;
            let collision_ratio = if equiv_distinct == 0 {
                0.0
            } else {
                (dispatch_distinct as f64) / (equiv_distinct as f64)
            };
            let avg_per_step = if self.cohort_origin_per_step_samples == 0 {
                0.0
            } else {
                (self.cohort_origin_distinct_per_step_sum as f64)
                    / (self.cohort_origin_per_step_samples as f64)
            };
            writeln!(f, "  cohort_origin_equivkey (COQ-S0 prep):",)?;
            writeln!(
                f,
                "    distinct_dispatch_keys={}  distinct_equiv_keys={}  collision_ratio={:.1}x",
                dispatch_distinct, equiv_distinct, collision_ratio,
            )?;
            writeln!(
                f,
                "    per_step_distinct: max={} avg={:.1} samples={}",
                self.cohort_origin_distinct_per_step_max,
                avg_per_step,
                self.cohort_origin_per_step_samples,
            )?;
            writeln!(
                f,
                "    gate (collision_ratio ≥ 20x AND per_step_avg ≥ 5): {}",
                if collision_ratio >= 20.0 && avg_per_step >= 5.0 {
                    "PASS — COQ justified"
                } else {
                    "FAIL — re-target"
                },
            )?;
        }
        // Phase F.13 chain_10000 Lazy redesign L2a prep (2026-05-27):
        // Push EdgeKind histogram — residual Push apply_action_to_cursor
        // calls (those NOT covered by Substage 5's broadcast).
        let push_total: u64 = self.push_kind_histogram.iter().sum();
        if push_total > 0 {
            writeln!(
                f,
                "  push_kind_histogram (Lazy redesign L2a prep — RESIDUAL after Substage 5):"
            )?;
            writeln!(f, "    total residual Push arm entries: {}", push_total)?;
            for (i, count) in self.push_kind_histogram.iter().enumerate() {
                if *count == 0 {
                    continue;
                }
                let pct = 100.0 * (*count as f64) / (push_total as f64);
                writeln!(
                    f,
                    "    [{:>2}] {:<22} = {:>10} ({:>5.1}%)",
                    i,
                    crate::walker_stats::pop_kind_label(i),
                    count,
                    pct,
                )?;
            }
            // L2a gate: CategoryEntryRoot + CrossCatProjection +
            // optional/binder-loop inner markers are the L2a targets.
            // CrossCatLhs and CrossCatLhsReentry are identity-strict and
            // intentionally excluded.
            let l2a_target: u64 = self.push_kind_histogram[1]
                + self.push_kind_histogram[3]
                + self.push_kind_histogram[10]
                + self.push_kind_histogram[11];
            let l2a_pct = 100.0 * (l2a_target as f64) / (push_total as f64);
            writeln!(
                f,
                "    L2a_target_share (CategoryEntryRoot+CrossCatProj+Opt/BinderLoop): {} / {} ({:.1}%) — gate (≥ 80%): {}",
                l2a_target,
                push_total,
                l2a_pct,
                if l2a_pct >= 80.0 { "PASS" } else { "FAIL" },
            )?;
        }
        // Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27):
        // Pop EdgeKind histogram — dominant convergent kind gates L2.
        let pop_total: u64 = self.pop_kind_histogram.iter().sum();
        if pop_total > 0 {
            writeln!(f, "  pop_kind_histogram (Lazy redesign L2 prep):")?;
            writeln!(f, "    total Pop arm entries: {}", pop_total)?;
            for (i, count) in self.pop_kind_histogram.iter().enumerate() {
                if *count == 0 {
                    continue;
                }
                let pct = 100.0 * (*count as f64) / (pop_total as f64);
                writeln!(
                    f,
                    "    [{:>2}] {:<22} = {:>10} ({:>5.1}%)",
                    i,
                    crate::walker_stats::pop_kind_label(i),
                    count,
                    pct,
                )?;
            }
            // L2 gate: convergent buckets are broadcastable. CrossCatLhs and
            // CrossCatLhsReentry are identity-strict and intentionally excluded.
            let convergent: u64 = self.pop_kind_histogram[1]
                + self.pop_kind_histogram[2]
                + self.pop_kind_histogram[3]
                + self.pop_kind_histogram[7]
                + self.pop_kind_histogram[8]
                + self.pop_kind_histogram[9]
                + self.pop_kind_histogram[10]
                + self.pop_kind_histogram[11];
            let convergent_pct = 100.0 * (convergent as f64) / (pop_total as f64);
            writeln!(
                f,
                "    convergent_pop_share: {} / {} ({:.1}%) — L2 gate (≥ 50%): {}",
                convergent,
                pop_total,
                convergent_pct,
                if convergent_pct >= 50.0 {
                    "PASS"
                } else {
                    "FAIL"
                },
            )?;
        }
        // Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27):
        // force-ratio projection. Decision rule: forced/created < 0.5
        // on left_assoc_chain_500 to ship L1-L5.
        if self.thunk_force_projection.created > 0 || self.thunk_force_projection.forced > 0 {
            writeln!(f, "  thunk_force_projection (Lazy redesign L0):")?;
            writeln!(
                f,
                "    created={}  forced={}  seed_cursors={}  ratio={:.3}",
                self.thunk_force_projection.created,
                self.thunk_force_projection.forced,
                self.thunk_force_projection.seed_cursors,
                self.thunk_force_projection.force_ratio(),
            )?;
            writeln!(
                f,
                "    by_action_kind [Push,OptGroupAbsent,ConsumeAndReplace,ConsumeAndPop,ConsumeAndCaptureAndPush,ConsumeIdentAndReplace,ConsumeIdentAndPop,ConsumeAndReplaceWithEffect,Consume,LexAlt,LexAltPrefixOp,LexAltPostfixOp,LexAltInfixOp,LexAltMixfixOp,Other]:",
            )?;
            writeln!(f, "      {:?}", self.thunk_force_projection.by_action_kind,)?;
            let gate_pass = self.thunk_force_projection.force_ratio() < 0.5;
            writeln!(
                f,
                "    gate (force_ratio < 0.5): {}  projected_memory_savings_multiplier={:.2}x",
                if gate_pass { "PASS" } else { "FAIL" },
                self.thunk_force_projection
                    .projected_memory_savings_multiplier(),
            )?;
        }
        // Evidence-pruning P1 Step-0 (plan §P1 commit 2): non-zero-slot
        // printing only (P-series round-3 m-3). Gate counters are
        // process-cumulative atomics (ep_p1 module docs); walker-side
        // counters are per-walker.
        {
            let (ep_considered, ep_gated_off, ep_d2_only) = ep_p1::snapshot();
            if ep_considered > 0
                || self.crosscat_lhs_delegates_spawned > 0
                || self.cast_then_infix_steps > 0
            {
                writeln!(f, "  ep_p1_crosscat_lhs (EP plan §P1 Step-0):")?;
                writeln!(
                    f,
                    "    fallthrough_considered={}  fallthrough_gated_off={}  d2_only_hits={} [process-cumulative]",
                    ep_considered, ep_gated_off, ep_d2_only,
                )?;
                writeln!(
                    f,
                    "    delegates_spawned={}  dup_at_pos_source={}  cast_then_infix_steps={}",
                    self.crosscat_lhs_delegates_spawned,
                    self.crosscat_lhs_delegate_dup_at_pos_source,
                    self.cast_then_infix_steps,
                )?;
                let mut dup_keys: Vec<(&(usize, u16), &u64)> = self
                    .crosscat_lhs_spawns_at_pos_source
                    .iter()
                    .filter(|(_, count)| **count > 1)
                    .collect();
                if !dup_keys.is_empty() {
                    dup_keys.sort();
                    writeln!(
                        f,
                        "    dup (pos, source_src_idx) → spawns: {:?}",
                        dup_keys
                            .iter()
                            .map(|((pos, src), count)| ((*pos, *src), **count))
                            .collect::<Vec<_>>(),
                    )?;
                }
            }
        }
        // EP-P1 amended §P1 SHADOW (2026-06-11): non-zero-slot printing.
        {
            let shadow_total: u64 = self.ep_p1_shadow_would_share_total.iter().sum();
            if shadow_total > 0 {
                writeln!(f, "  ep_p1_shadow (amended §P1, PRATTAIL_EP_P1=shadow):")?;
                let slots: Vec<(usize, u64)> = self
                    .ep_p1_shadow_would_share_total
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(_, v)| *v > 0)
                    .collect();
                writeln!(
                    f,
                    "    would_share_total={} non-zero slots [class*2+rec → n]: {:?}",
                    shadow_total, slots,
                )?;
                let mut shadow_dups: Vec<((usize, u16, u16), u32)> = self
                    .ep_p1_shadow_seen
                    .iter()
                    .filter(|(_, count)| **count > 1)
                    .map(|(key, count)| (*key, *count))
                    .collect();
                if !shadow_dups.is_empty() {
                    shadow_dups.sort();
                    writeln!(
                        f,
                        "    full-key dups (pos, source, host_cat) → spawns: {:?}",
                        shadow_dups,
                    )?;
                }
            }
        }
        // EP-P1 MEASURE (Round 6): the arrival-phase split + the B1
        // tail-divergence witness. Non-zero printing only.
        {
            let measure_total = self.ep_p1_measure_workers
                + self.ep_p1_measure_inflight_hits
                + self.ep_p1_measure_resolved_hits
                + self.ep_p1_measure_failed_hits;
            if measure_total > 0 {
                writeln!(f, "  ep_p1_measure (PRATTAIL_EP_P1=measure, v3 deciding split):")?;
                writeln!(
                    f,
                    "    workers={}  inflight_hits={}  resolved_hits={}  failed_hits={}  tail_divergent={}",
                    self.ep_p1_measure_workers,
                    self.ep_p1_measure_inflight_hits,
                    self.ep_p1_measure_resolved_hits,
                    self.ep_p1_measure_failed_hits,
                    self.ep_p1_measure_tail_divergent,
                )?;
            }
        }
        // EP-P1 v3.1 ON counters (non-zero only under enforcement).
        {
            if self.ep_p1_consumed_in_place > 0 || self.ep_p1_park_overflow_fallbacks > 0 {
                writeln!(
                    f,
                    "  ep_p1_on (v3.1): consumed_in_place={}  park_overflow_fallbacks={}",
                    self.ep_p1_consumed_in_place, self.ep_p1_park_overflow_fallbacks,
                )?;
            }
        }
        // EP-P2 Step-0 SHADOW (plan §P2 commit 2): the Parikh/suffix
        // obligation gate. Non-zero-slot printing (round-3 m-3); each slot
        // is `class*2 + recovery_enabled`. The accept/STOP gate reads the
        // RECOVERY-OFF partition (even slots) against apply_action_calls.
        {
            let would_refute: u64 = self.parikh_shadow_would_refute_total.iter().sum();
            let refuted_accepted: u64 = self.parikh_shadow_refuted_then_accepted.iter().sum();
            let steps_after: u64 = self.parikh_shadow_steps_after_would_refute.iter().sum();
            let eoi_refutable: u64 = self.eoi_dead_cursors_parikh_refutable.iter().sum();
            if would_refute > 0 || refuted_accepted > 0 || steps_after > 0 || eoi_refutable > 0 {
                let nz = |arr: &[u64; WPDA_STATE_CLASS_COUNT * 2]| -> Vec<(usize, u64)> {
                    arr.iter()
                        .copied()
                        .enumerate()
                        .filter(|(_, v)| *v > 0)
                        .collect()
                };
                // Recovery-OFF partition = even slots (rec=0); the gate's
                // accept/STOP basis.
                let rec_off_steps: u64 = self
                    .parikh_shadow_steps_after_would_refute
                    .iter()
                    .step_by(2)
                    .sum();
                writeln!(f, "  ep_p2_parikh_shadow (EP plan §P2 Step-0, PRATTAIL_EP_P2=shadow):")?;
                writeln!(
                    f,
                    "    would_refute_total={}  refuted_then_accepted={} (MUST be 0)  steps_after_would_refute={}  eoi_dead_refutable={}",
                    would_refute, refuted_accepted, steps_after, eoi_refutable,
                )?;
                writeln!(
                    f,
                    "    [class*2+rec → n] would_refute={:?}  steps_after={:?}  eoi_refutable={:?}",
                    nz(&self.parikh_shadow_would_refute_total),
                    nz(&self.parikh_shadow_steps_after_would_refute),
                    nz(&self.eoi_dead_cursors_parikh_refutable),
                )?;
                if refuted_accepted > 0 {
                    writeln!(
                        f,
                        "    ⚠ HARD-STOP TRIPWIRE: refuted_then_accepted slots {:?} — model/transcription is WRONG",
                        nz(&self.parikh_shadow_refuted_then_accepted),
                    )?;
                }
                if self.apply_action_calls > 0 {
                    let pct = (steps_after as f64) * 100.0 / (self.apply_action_calls as f64);
                    let pct_off = (rec_off_steps as f64) * 100.0 / (self.apply_action_calls as f64);
                    writeln!(
                        f,
                        "    steps_after_would_refute = {:.2}% of apply_action_calls ({:.2}% recovery-off) — gate ≥ 20% to proceed, < 5% STOP",
                        pct, pct_off,
                    )?;
                }
            }
        }
        // EP-P4 (Stages C+E: ORDER-ONLY) — innovation demotion + ESS report
        // (plan §P4; ForwardOrderOnly.v T3/T4/T5/T6). Non-zero / nontrivial
        // printing only. The tripwire line is ALWAYS shown once any demotion
        // fired, so a regression is loud.
        {
            if self.zero_innovation_demotions > 0
                || self.demoted_member_unstepped_at_exit > 0
                || self.frontier_ess_x1000_last > 0
            {
                writeln!(
                    f,
                    "  ep_p4_order_only (PRATTAIL_EP_P4_DEMOTE=on): zero_innovation_demotions={}  demoted_member_unstepped_at_exit={} (MUST be 0)  frontier_ess_x1000_last={}",
                    self.zero_innovation_demotions,
                    self.demoted_member_unstepped_at_exit,
                    self.frontier_ess_x1000_last,
                )?;
                if self.demoted_member_unstepped_at_exit > 0 {
                    writeln!(
                        f,
                        "    ⚠ TRIPWIRE: demoted_member_unstepped_at_exit > 0 — demotion deferred a live member out of its step_fanout pass (ForwardOrderOnly.v T4/T5 violated); deep-dive the within-step invariant",
                    )?;
                }
            }
        }
        // EP-P5 (Stage D) ENTRY-GATE measurement (plan §P5). `residual_dead_steps`
        // = apply_action steps on cursors that DIE at the EOI accepting filter,
        // as % of apply_action_calls. Two numerators bracket the true share:
        // own (lower) ≤ true ≤ lineage (upper). GATE: ≥ 15% ⇒ implement Stage D;
        // < 15% ⇒ STOP. Printed whenever any parse work happened
        // (`apply_action_calls > 0`) so the gate evidence — including the
        // informative all-zero-dead case — is always visible in a measurement
        // build.
        {
            if self.p5_residual_dead_steps_own > 0
                || self.p5_residual_dead_steps_lineage > 0
                || self.p5_accepted_steps_own > 0
                || self.p5_accepted_steps_lineage > 0
                || self.apply_action_calls > 0
            {
                writeln!(
                    f,
                    "  ep_p5_residual_gate (EP plan §P5 ENTRY-GATE, default ep_p1=On world):",
                )?;
                writeln!(
                    f,
                    "    dead_steps[own={} lineage={}]  accepted_steps[own={} lineage={}]  apply_action_calls={}",
                    self.p5_residual_dead_steps_own,
                    self.p5_residual_dead_steps_lineage,
                    self.p5_accepted_steps_own,
                    self.p5_accepted_steps_lineage,
                    self.apply_action_calls,
                )?;
                if self.apply_action_calls > 0 {
                    let denom = self.apply_action_calls as f64;
                    let lower = (self.p5_residual_dead_steps_own as f64) * 100.0 / denom;
                    let upper = (self.p5_residual_dead_steps_lineage as f64) * 100.0 / denom;
                    // Derived pre-EOI-lost residual on the OWN (partition)
                    // counter: apply_action_calls − dead_own − accepted_own
                    // (fork ancestry + mid-parse Drops + parked segments).
                    let accounted = self
                        .p5_residual_dead_steps_own
                        .saturating_add(self.p5_accepted_steps_own);
                    let pre_eoi_lost = self.apply_action_calls.saturating_sub(accounted);
                    let lost_pct = (pre_eoi_lost as f64) * 100.0 / denom;
                    writeln!(
                        f,
                        "    residual_dead_steps = [{:.2}% .. {:.2}%] of apply_action_calls (own..lineage bracket) — GATE ≥ 15% ⇒ implement Stage D, < 15% ⇒ STOP",
                        lower, upper,
                    )?;
                    writeln!(
                        f,
                        "    own-partition cross-check: dead_own + accepted_own = {} ; pre_eoi_lost (fork ancestry + drops + parks) = {} ({:.2}%)",
                        accounted, pre_eoi_lost, lost_pct,
                    )?;
                    writeln!(
                        f,
                        "    EOI frontier cursors examined={} (of which DIED, !is_accepting_config={}) — the raw EOI-death population (step-free if dead_steps=0 ⇒ Stage D has no late-death work to prune)",
                        self.p5_eoi_cursors_examined, self.p5_eoi_dead_cursors,
                    )?;
                }
            }
        }
        // led_chain ROOT-CAUSE DIAGNOSTIC (TEMPORARY).
        {
            let dbg_total: u64 = self.dbg_ccl_reg_outcome.iter().sum::<u64>()
                + self.dbg_ccl_drain_jobs
                + self.dbg_ccl_eoi_jobs;
            if dbg_total > 0 {
                writeln!(
                    f,
                    "  DBG-CCL reg_outcome[Worker,Inflight,Resolved,Failed]={:?} resolved_not_quiescent={} parked_ok={}",
                    self.dbg_ccl_reg_outcome,
                    self.dbg_ccl_resolved_not_quiescent,
                    self.dbg_ccl_parked_ok,
                )?;
                writeln!(
                    f,
                    "  DBG-CCL lineage inc={} dec={} quiesce_to_zero={} inflight_keys_at_eoi={}",
                    self.dbg_ccl_lineage_inc,
                    self.dbg_ccl_lineage_dec,
                    self.dbg_ccl_quiesce_to_zero,
                    self.dbg_ccl_inflight_keys_at_eoi,
                )?;
                writeln!(
                    f,
                    "  DBG-CCL drain jobs={} members={}  eoi jobs={} members={}",
                    self.dbg_ccl_drain_jobs,
                    self.dbg_ccl_drain_members,
                    self.dbg_ccl_eoi_jobs,
                    self.dbg_ccl_eoi_members,
                )?;
                writeln!(
                    f,
                    "  DBG-CCL M1 reached={} orphan_count={} injected={} rounds_capped={} eoi_release_set={} stale_proceed={} dead_released={} accept_present_skip={}",
                    self.dbg_ccl_m1_reached,
                    self.dbg_ccl_m1_orphan_count,
                    self.dbg_ccl_m1_injected,
                    self.dbg_ccl_rounds_capped,
                    self.dbg_ccl_eoi_release_set,
                    self.dbg_ccl_stale_proceed,
                    self.dbg_ccl_dead_worker_released,
                    self.dbg_ccl_accept_present_skip,
                )?;
                let mut keys: Vec<_> = self.dbg_ccl_reg_by_key.iter().collect();
                keys.sort_by_key(|(k, _)| **k);
                for (k, n) in keys {
                    let ovf = self.dbg_ccl_overflow_by_key.get(k).copied().unwrap_or(0);
                    writeln!(
                        f,
                        "    DBG-CCL key(pos={},src={},host={}) regs={} overflow={}",
                        k.0, k.1, k.2, n, ovf,
                    )?;
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

// ── Evidence-pruning program (P-series) ────────────────────────────────
//
// Conventions (plan: docs/design/evidence-pruning/02-staged-implementation-
// plan.md v3, USER-APPROVED 2026-06-11; ledger: 02-program-ledger.md):
//
// - Kill switches: `PRATTAIL_EP_<STAGE>=off|shadow|on`, read ONCE per
//   walker construction (never per step).
// - Shadow counters per definite gate, PARTITIONED by WpdaState-class ×
//   recovery_enabled (I4; a single hit in a rare state must never be
//   statistically buried):
//     `<stage>_shadow_would_refute_total: [u64; WPDA_STATE_CLASS_COUNT * 2]`
//     `<stage>_shadow_refuted_then_accepted: [u64; ..]`  (MUST stay all-0)
//     `<stage>_shadow_steps_after_would_refute: [u64; ..]`
//   Index = `state_class * 2 + (recovery_enabled as usize)`.
// - Display prints ONLY non-zero slots (round-3 m-3: full 2×N dumps per
//   stage are unreadable next to the ~86 existing report lines).
// - Increment via `stats_inc_idx!` below (`stats_inc!` takes a bare
//   ident and cannot index — round-2 m-1).

/// Coarse `WpdaState` partition for P-series shadow counters. Buckets,
/// not variants: the soundness partition needs "which intrinsic
/// subsystem", not the full enum.
pub const WPDA_STATE_CLASS_COUNT: usize = 8;

/// Map a `WpdaState` to its P-series partition class.
/// 0 dispatch (PrefixDispatch/AmbiguityFanout) · 1 infix (InfixLoop/
/// InfixChainIterative) · 2 mixfix (MixfixContinuation/MixfixLiteralRun)
/// · 3 collection (CollectionLoop/CollectionOpenParen) · 4 binder
/// (BinderRule/BinderListLoop/OptionalGroup) · 5 cross-cat
/// (CrossCatDelegate) · 6 unwind/saturate (Unwinding/Saturating/
/// GroupingClosePreservingInner) · 7 other/terminal.
pub fn wpda_state_class(state: &crate::wpda_runtime::WpdaState) -> usize {
    use crate::wpda_runtime::WpdaState as S;
    match state {
        S::PrefixDispatch { .. } | S::AmbiguityFanout { .. } => 0,
        S::InfixLoop { .. } | S::InfixChainIterative { .. } => 1,
        S::MixfixContinuation { .. } | S::MixfixLiteralRun { .. } => 2,
        S::CollectionLoop { .. } | S::CollectionOpenParen { .. } => 3,
        S::BinderRule { .. } | S::BinderListLoop { .. } | S::OptionalGroup { .. } => 4,
        S::CrossCatDelegate { .. } => 5,
        S::Unwinding | S::Saturating { .. } | S::GroupingClosePreservingInner { .. } => 6,
        _ => 7,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ★ GLL-FLOOR SHADOW RECOGNIZER — control + measurement thread-local
//   (investigation a166789b, Stage-0 gate validation BEFORE any wiring).
//
//   This module is the ACTIVE recognizer control. When `Mode != Off`, the
//   walker's `merge_equivalent_cursors` swaps the derivation-provenance-bearing
//   `ConfigKey` for a COARSE GLL-floor merge key (SLOT or LITERAL), turning the
//   SAME automaton (transition fn, GSS, lexer) into a coarse-keyed RECOGNIZER:
//   distinct fine derivations that share a coarse key COLLAPSE to one bucket
//   (keep-one representative). The parse is then run exactly as normal (via the
//   ordinary facade `Cat::parse`), and its Ok/Err is read as the recognizer
//   verdict Reachable/Unreachable.
//
//   SOUNDNESS-BY-CONSTRUCTION of the validation (the reachability-⊆ lemma):
//   the ONLY change vs the real parser is the merge KEY. The real parser is
//   itself a keep-one merge on the FINE key with edge-guided pop. This coarse
//   recognizer is keep-one on a COARSE key with the SAME edge-guided pop. A
//   keep-one-coarse recognizer explores a SUBSET of the reachability of the
//   task's true UNION / pop_all_predecessors-fan-out recognizer (fan-out only
//   ADDS pop targets, never removes). Hence:  keep-one-coarse Reachable  ⟹
//   fan-out Reachable.  So if this (harsher) keep-one recognizer is Reachable
//   on every parseable span (G0-SOUND), the true fan-out recognizer is too —
//   a CONSERVATIVE, sound validation of G0-SOUND. (Conversely a keep-one
//   Unreachable is inconclusive for fan-out — reported as such.)
//
//   ZERO effect on the real parse: `Mode::Off` (the default, and the only
//   value without a harness explicitly opting in) leaves the merge key at the
//   exact `ConfigKey` path. Feature-gated `walker-stats`.
#[cfg(feature = "walker-stats")]
pub mod recog {
    use std::cell::Cell;

    /// Which coarse merge key the recognizer uses (or `Off` = real parser).
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub enum Mode {
        /// Real parser — full `ConfigKey` (derivation-provenance retained).
        Off,
        /// SLOT key: `(WpdaState, gss-node, pos, collection_depth, cohort.equiv())`
        /// — the fine ConfigKey MINUS the derivation-provenance block
        /// (incoming-edge / edge-stack, sppf_top / sppf_stack, lex_* stamps).
        Slot,
        /// LITERAL key AS SPECIFIED by the design under test:
        /// `(state_class, node_class, pos, collection_depth, bp_floor)`.
        Literal,
        /// DIAGNOSTIC: SLOT + the edge-stack (incoming_edge + incoming_edge_stack)
        /// — i.e. drops ONLY the sppf_* + lex_* axes, RETAINING the pop-routing
        /// edge-stack. Used to localize keep-one SLOT false-rejects: if `SlotEdge`
        /// is sound where `Slot` false-rejects, the lost config was a POP TARGET
        /// (which the task's `pop_all_predecessors` fan-out recovers without the
        /// edge-stack), and `SlotEdge`'s frontier reveals the edge-stack blow-up
        /// that fan-out is needed to avoid.
        SlotEdge,
        /// DIAGNOSTIC: SLOT + the SINGLE `incoming_edge` (one `GssEdgeId`) but
        /// NOT the `incoming_edge_stack`. Isolates whether the cheap,
        /// grammar-bounded single pop-routing edge suffices for SOUNDNESS
        /// without the exponential cross-product edge-STACK. If `SlotEdge1` is
        /// sound (0 false-rejects) AND poly (flat frontier) it is the wireable
        /// non-parseability oracle; if it is unsound where `SlotEdge` is sound,
        /// the edge-STACK (not just the single edge) is load-bearing and the
        /// `pop_all_predecessors` fan-out is required instead.
        SlotEdge1,
        /// THE WIREABLE ORACLE: SLOT merge key (identical to `Slot`) PLUS pop
        /// FAN-OUT over `pop_all_predecessors` (Tomita fork-on-pop) at every
        /// pop. Recovers the pop-target reachability that keep-one `Slot` loses
        /// (the 3 trailing-comma false-rejects) while keeping the Slot-column
        /// polynomial frontier — the edge-stack cross-product is never
        /// materialized. Drives the same fan-out path the production
        /// `recognizer_mode` oracle uses; this harness variant validates it
        /// (G0-SOUND 0-false-reject + G0-POLY tracks Slot not SlotEdge).
        SlotFanout,
    }

    thread_local! {
        static MODE: Cell<Mode> = const { Cell::new(Mode::Off) };
        static PEAK: Cell<u64> = const { Cell::new(0) };
        static STEPS: Cell<u64> = const { Cell::new(0) };
    }

    /// Activate/deactivate the recognizer for the current thread. The harness
    /// calls `set(Mode::Slot|Literal)` before `Cat::parse`, then `set(Mode::Off)`.
    #[inline]
    pub fn set(m: Mode) {
        MODE.with(|c| c.set(m));
    }
    #[inline]
    pub fn get() -> Mode {
        MODE.with(|c| c.get())
    }
    #[inline]
    pub fn is_active() -> bool {
        get() != Mode::Off
    }

    /// Reset the per-parse frontier peak + merge-tier step count.
    #[inline]
    pub fn reset_peak() {
        PEAK.with(|c| c.set(0));
        STEPS.with(|c| c.set(0));
    }
    /// Record one merge tier's POST-merge frontier size (the recognizer's
    /// coarse-keyed frontier — the G0-POLY metric).
    #[inline]
    pub fn record_frontier(n: u64) {
        PEAK.with(|c| c.set(c.get().max(n)));
        STEPS.with(|c| c.set(c.get().saturating_add(1)));
    }
    /// Peak post-merge coarse frontier size observed this parse.
    #[inline]
    pub fn peak() -> u64 {
        PEAK.with(|c| c.get())
    }
    /// Number of merge tiers observed this parse (a proxy for total steps).
    #[inline]
    pub fn steps() -> u64 {
        STEPS.with(|c| c.get())
    }
}

/// Increment slot `$idx` of a dimensioned `[u64; N]` counter on
/// `self.stats` (zero-cost when feature off). The P-series partitioned-
/// counter primitive (round-2 m-1: `stats_inc!` cannot index).
///
/// Usage:
///   `stats_inc_idx!(self, parikh_shadow_would_refute_total,
///        crate::walker_stats::wpda_state_class(&cursor.inner_state) * 2
///            + recovery_enabled as usize);`
#[macro_export]
macro_rules! stats_inc_idx {
    ($walker:expr, $field:ident, $idx:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            let __i: usize = $idx;
            if __i < $walker.stats.$field.len() {
                $walker.stats.$field[__i] = $walker.stats.$field[__i].saturating_add(1);
            }
        }
    };
}

/// Evidence-pruning P1 Step-0 (plan §P1 commit 2): the lex-fork
/// fall-through GATE counters. The gate executes in GENERATED parser
/// code (`emit_lex_fork_at_prefix_dispatch`'s fragment, forks.rs) which
/// has no `&mut WalkerStats` in scope, so these are process-wide
/// atomics behind an always-defined hook fn (no-op body without the
/// `walker-stats` feature). Counters are MONOTONE process-cumulative
/// (never drained): with `PRATTAIL_WALKER_STATS=1` every report prints
/// the running totals, so the LAST report of a run carries the corpus
/// totals.
pub mod ep_p1 {
    #[cfg(feature = "walker-stats")]
    use std::sync::atomic::{AtomicU64, Ordering};

    #[cfg(feature = "walker-stats")]
    pub static CROSSCAT_LHS_FALLTHROUGH_CONSIDERED: AtomicU64 = AtomicU64::new(0);
    #[cfg(feature = "walker-stats")]
    pub static CROSSCAT_LHS_FALLTHROUGH_GATED_OFF: AtomicU64 = AtomicU64::new(0);
    #[cfg(feature = "walker-stats")]
    pub static CROSSCAT_LHS_D2_ONLY_HITS: AtomicU64 = AtomicU64::new(0);

    /// Gate-consultation hook called from the generated fall-through
    /// fragment (one call per ambiguous-token PrefixDispatch gate
    /// evaluation).
    ///
    /// - `kind_hit`: `prefix_crosscat_lhs_has_dispatch_rule` matched
    ///   the current token (the d1 kind predicate, BEFORE the trigger
    ///   gate) → `crosscat_lhs_fallthrough_considered` counts every
    ///   call; `kind_hit && !gate_open` counts
    ///   `crosscat_lhs_fallthrough_gated_off` (the trigger-presence
    ///   gate suppressed an otherwise-eligible crosscat fall-through).
    /// - `gate_open`: `kind_hit` AND `prefix_crosscat_lhs_trigger_ahead`
    ///   (the full d1g disjunct as shipped).
    /// - `crosscat_load_bearing`: the fall-through decided TRUE, would
    ///   have been FALSE without the crosscat disjunct, AND ≥ 1 lex-alt
    ///   branch was bypassed — the runtime witness of the FV
    ///   `d1_d2_delta` (CastLexForkCrossCatLhsGap: the d1-vs-d2 delta
    ///   is EXACTLY the bypassed secondary interpretation at SourceCtx;
    ///   d2 = the fork-keeping `LexAltRuleKind::CrossCatLhs` variant).
    ///   Counted as `crosscat_lhs_d2_only_hits`: if 0 across
    ///   battery + corpus, d1 suffices and the d2 extension records a
    ///   STOP (plan §P1 accept/STOP gates).
    #[inline]
    #[allow(unused_variables)]
    pub fn note_crosscat_lhs_fallthrough(
        kind_hit: bool,
        gate_open: bool,
        crosscat_load_bearing: bool,
    ) {
        #[cfg(feature = "walker-stats")]
        {
            CROSSCAT_LHS_FALLTHROUGH_CONSIDERED.fetch_add(1, Ordering::Relaxed);
            if kind_hit && !gate_open {
                CROSSCAT_LHS_FALLTHROUGH_GATED_OFF.fetch_add(1, Ordering::Relaxed);
            }
            if crosscat_load_bearing {
                CROSSCAT_LHS_D2_ONLY_HITS.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    /// Snapshot (load) the three gate counters:
    /// `(considered, gated_off, d2_only)`. All zero without the
    /// `walker-stats` feature.
    pub fn snapshot() -> (u64, u64, u64) {
        #[cfg(feature = "walker-stats")]
        {
            (
                CROSSCAT_LHS_FALLTHROUGH_CONSIDERED.load(Ordering::Relaxed),
                CROSSCAT_LHS_FALLTHROUGH_GATED_OFF.load(Ordering::Relaxed),
                CROSSCAT_LHS_D2_ONLY_HITS.load(Ordering::Relaxed),
            )
        }
        #[cfg(not(feature = "walker-stats"))]
        (0, 0, 0)
    }
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

/// EP-P4 (Stage E): record the LAST-computed frontier ESS ×1000 (an
/// ASSIGNMENT, not an accumulation — `frontier_ess_x1000_last` reflects the
/// most recent budget/EOI event). Zero-cost when the feature is off. The
/// value is also carried in the budget sentinel / surfaced in the error
/// report independently of this counter — this is the stats-side mirror so
/// `PRATTAIL_WALKER_STATS=1` runs see the ESS even when no error propagates.
#[macro_export]
macro_rules! record_frontier_ess {
    ($walker:expr, $value:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker.stats.frontier_ess_x1000_last = ($value) as u32;
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
            $walker.stats.$hist_field[idx] = $walker.stats.$hist_field[idx].saturating_add(1);
            let vu64 = v as u64;
            if vu64 > $walker.stats.$max_field {
                $walker.stats.$max_field = vu64;
            }
            $walker.stats.$samples_field = $walker.stats.$samples_field.saturating_add(1);
        }
    };
}

/// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): record one
/// Fork-arm child as a lazily-enqueued thunk (zero-cost when feature
/// off). Pass the `ForkActionKind` bucket index (0..=14) per the
/// histogram documented on `ThunkForceRatioProjection`.
///
/// Usage at every `children.push(child)` site in wpda_walker.rs:
///   `stats_thunk_created!(self, FORK_KIND_INDEX_PUSH);`
#[macro_export]
macro_rules! stats_thunk_created {
    ($walker:expr, $kind_index:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker
                .stats
                .thunk_force_projection
                .observe_created($kind_index);
        }
    };
}

/// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): record one
/// cursor entering `apply_action_to_cursor` (= thunk force in the
/// lazy redesign). Wired once at the entry of `apply_action_to_cursor`.
#[macro_export]
macro_rules! stats_thunk_forced {
    ($walker:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker.stats.thunk_force_projection.observe_forced();
        }
    };
}

/// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): record one
/// seed / commit-winner write-back cursor (NOT Fork-arm fan-out).
/// Wired at `wpda_walker.rs:5027, 5100` per Explore agent catalogue.
#[macro_export]
macro_rules! stats_thunk_seed {
    ($walker:expr) => {
        #[cfg(feature = "walker-stats")]
        {
            $walker.stats.thunk_force_projection.observe_seed();
        }
    };
}

/// Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27): ForkActionKind
/// bucket indices for `stats_thunk_created!` calls. Matches the
/// histogram documented on `ThunkForceRatioProjection`.
pub mod fork_kind_index {
    pub const PUSH: usize = 0;
    pub const OPT_GROUP_ABSENT: usize = 1;
    pub const CONSUME_AND_REPLACE: usize = 2;
    pub const CONSUME_AND_POP: usize = 3;
    pub const CONSUME_AND_CAPTURE_AND_PUSH: usize = 4;
    pub const CONSUME_IDENT_AND_REPLACE: usize = 5;
    pub const CONSUME_IDENT_AND_POP: usize = 6;
    pub const CONSUME_AND_REPLACE_WITH_EFFECT: usize = 7;
    pub const CONSUME: usize = 8;
    pub const LEX_ALT: usize = 9;
    pub const LEX_ALT_PREFIX_OP: usize = 10;
    pub const LEX_ALT_POSTFIX_OP: usize = 11;
    pub const LEX_ALT_INFIX_OP: usize = 12;
    pub const LEX_ALT_MIXFIX_OP: usize = 13;
    pub const OTHER: usize = 14;
}

// ─────────────────────────────────────────────────────────────────────────────
// ★ GLL-FLOOR SHADOW RECOGNIZER (investigation a166789b, Stage 0 — VALIDATION
//   BEFORE WIRING). Gated `walker-stats` + activated per-parse via `reset(true)`.
//
//   PURPOSE. Validate the architecture-native NON-PARSEABILITY ORACLE hypothesis:
//   RECOGNITION (∃ a parse?) is strictly weaker than PARSING, so the SAME
//   automaton run as a coarse-keyed RECOGNIZER can reject genuinely-unparseable
//   spans in polynomial time (a one-sided oracle: Unreachable ⇒ non-parseable;
//   Reachable ⇒ run the full parser). This module is a MEASURE-ONLY shadow: it
//   reads the walker's merge-tier frontier + EOI-accept configs and computes, in
//   parallel to the real parse, the coarse-frontier reachability signals. It
//   writes ONLY into this module's thread-local store — ZERO effect on the real
//   parse (byte-identical). It is a piggyback traversal over the REAL walker's
//   projected frontier, NOT an independent re-implementation of the transition
//   relation.
//
//   THREE KEYS are projected from each live cursor and measured side-by-side:
//     • GLL_FLOOR  `(state_class, node_class, pos, coll_depth)` — the EXISTING
//       `bcc_shadow_peak_gll_floor` key (no binding-power axis).
//     • LITERAL    GLL_FLOOR + `bp_floor` — the coarse key AS LITERALLY
//       SPECIFIED `(state-class, node-class, pos, collection-depth, bp-floor)`.
//     • SLOT       `(WpdaState, node StackSymbolV2, pos, coll_depth,
//       cohort_origin.equiv())` — the fine `ConfigKey` MINUS the
//       derivation-provenance block. This is the GLL GRAMMAR SLOT: the minimal
//       key the G0-MONOTONE audit predicts is required for a SOUND recognizer.
//       Grammar-bounded ⇒ polynomial.
//
//   OVER-MERGE = the number of LITERAL buckets that collapse ≥2 DISTINCT SLOT
//   keys — a config where the literal coarse key CANNOT distinguish two
//   genuinely-distinct grammar slots. A keep-one recognizer on the LITERAL key
//   would retain one representative and LOSE the others' transitions → potential
//   FALSE-REJECT. On a PARSEABLE corpus, OVER-MERGE is the empirical failable
//   soundness signal: 0 ⇒ literal ≡ slot ⇒ empirically sound; >0 ⇒ the literal
//   key conflates distinct slots (necessary condition for a false-reject; the
//   static G0-MONOTONE audit confirms these fields gate transitions). SLOT never
//   over-merges (it IS the slot) ⇒ the sound key by construction.
#[cfg(feature = "walker-stats")]
pub mod gll_recog {
    use crate::dispatch_cohort::EquivKey;
    use crate::gss::NodeClass;
    use crate::wpda_runtime::{StackSymbolV2, WpdaState};
    use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};

    /// The EXISTING GLL invariant floor `(state_class, node_class, pos,
    /// collection_depth)` — no binding-power axis (== `bcc_shadow_peak_gll_floor`).
    pub type GllFloorKey = (usize, NodeClass, usize, usize);

    /// The coarse key AS LITERALLY SPECIFIED: GLL_FLOOR + `bp_floor`
    /// (`state_binding_power_floor`).
    pub type LiteralKey = (usize, NodeClass, usize, usize, Option<u8>);

    /// The fine `ConfigKey` with the DERIVATION-PROVENANCE block dropped: the
    /// GLL grammar slot. Retains the full state + node grammar identity + cohort
    /// (all grammar-bounded); drops incoming-edge-stack, sppf_top/sppf_stack,
    /// and the lex_* disambiguation stamps.
    #[derive(Clone, PartialEq, Eq, Hash)]
    pub struct SlotKey {
        pub state: WpdaState,
        pub node_symbol: Option<StackSymbolV2>,
        pub pos: usize,
        pub coll_depth: usize,
        pub cohort: Option<EquivKey>,
    }

    /// One projected cursor: its three keys, computed walker-side.
    pub type Item = (GllFloorKey, LiteralKey, SlotKey);

    #[derive(Default)]
    struct State {
        active: bool,
        merge_calls: u64,
        peak_fine: u64,       // peak pre-merge frontier size (drained.len())
        peak_gll_floor: u64,  // peak distinct GLL_FLOOR keys at a merge
        peak_literal: u64,    // peak distinct LITERAL keys at a merge
        peak_slot: u64,       // peak distinct SLOT keys at a merge  (POLY metric)
        overmerge_pairs: u64, // Σ over LITERAL buckets of (distinct SLOTs − 1)
        overmerge_buckets: u64,
        bp_recovered_pairs: u64, // Σ over GLL_FLOOR buckets of (distinct LITERALs − 1)
        reach_literal: HashSet<LiteralKey>,
        reach_slot: HashSet<SlotKey>,
        accept_slot_reached: bool,
        accept_literal_reached: bool,
        first_overmerge: Option<String>,
    }

    thread_local! {
        static STATE: RefCell<State> = RefCell::new(State::default());
    }

    /// Begin observing a fresh parse. `active=false` fully disables observation.
    /// Resets ALL per-parse state.
    #[inline]
    pub fn reset(active: bool) {
        STATE.with(|s| {
            *s.borrow_mut() = State {
                active,
                ..State::default()
            };
        });
    }

    /// True iff a parse is currently being observed (the walker checks this
    /// before doing any projection work).
    #[inline]
    pub fn is_active() -> bool {
        STATE.with(|s| s.borrow().active)
    }

    /// Observe one merge-tier frontier: the walker passes the three projected
    /// keys per live (drained) cursor. Updates peaks, over-merge counts, and the
    /// accumulated reachability sets.
    pub fn observe_frontier(items: &[Item]) {
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            if !st.active {
                return;
            }
            st.merge_calls = st.merge_calls.saturating_add(1);
            st.peak_fine = st.peak_fine.max(items.len() as u64);

            let gll: HashSet<&GllFloorKey> = items.iter().map(|(g, _, _)| g).collect();
            let lit: HashSet<&LiteralKey> = items.iter().map(|(_, l, _)| l).collect();
            let slot: HashSet<&SlotKey> = items.iter().map(|(_, _, sl)| sl).collect();
            st.peak_gll_floor = st.peak_gll_floor.max(gll.len() as u64);
            st.peak_literal = st.peak_literal.max(lit.len() as u64);
            st.peak_slot = st.peak_slot.max(slot.len() as u64);

            // OVER-MERGE: group SLOTs by LITERAL. A LITERAL bucket with ≥2
            // distinct SLOTs conflates distinct grammar slots.
            let mut by_lit: HashMap<&LiteralKey, HashSet<&SlotKey>> =
                HashMap::with_capacity(lit.len());
            for (_g, l, sl) in items {
                by_lit.entry(l).or_default().insert(sl);
            }
            for (l, slots) in &by_lit {
                if slots.len() >= 2 {
                    st.overmerge_buckets = st.overmerge_buckets.saturating_add(1);
                    st.overmerge_pairs =
                        st.overmerge_pairs.saturating_add((slots.len() - 1) as u64);
                    if st.first_overmerge.is_none() {
                        let detail = slots
                            .iter()
                            .map(|sk| {
                                format!(
                                    "{{state={:?}, node={:?}, cohort={:?}}}",
                                    sk.state, sk.node_symbol, sk.cohort
                                )
                            })
                            .collect::<Vec<_>>()
                            .join("  ||  ");
                        st.first_overmerge = Some(format!(
                            "LITERAL {:?} conflates {} distinct SLOTs: {}",
                            l,
                            slots.len(),
                            detail
                        ));
                    }
                }
            }

            // bp-recovery: how much the bp_floor axis alone refines GLL_FLOOR.
            let mut by_gll: HashMap<&GllFloorKey, HashSet<&LiteralKey>> =
                HashMap::with_capacity(gll.len());
            for (g, l, _sl) in items {
                by_gll.entry(g).or_default().insert(l);
            }
            for (_g, lits) in &by_gll {
                if lits.len() >= 2 {
                    st.bp_recovered_pairs =
                        st.bp_recovered_pairs.saturating_add((lits.len() - 1) as u64);
                }
            }

            for (_g, l, sl) in items {
                st.reach_literal.insert(*l);
                st.reach_slot.insert(sl.clone());
            }
        });
    }

    /// Observe an EOI-accepting configuration (recognizer verdict = Reachable).
    pub fn observe_accept(lit: LiteralKey, slot: SlotKey) {
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            if !st.active {
                return;
            }
            st.accept_literal_reached = true;
            st.accept_slot_reached = true;
            st.reach_literal.insert(lit);
            st.reach_slot.insert(slot);
        });
    }

    /// Per-parse readout.
    #[derive(Debug, Clone, Default)]
    pub struct Snapshot {
        pub merge_calls: u64,
        pub peak_fine: u64,
        pub peak_gll_floor: u64,
        pub peak_literal: u64,
        pub peak_slot: u64,
        pub overmerge_pairs: u64,
        pub overmerge_buckets: u64,
        pub bp_recovered_pairs: u64,
        pub reach_literal_size: u64,
        pub reach_slot_size: u64,
        /// Recognizer verdict (piggyback): an EOI-accepting config was observed.
        pub accept_slot_reached: bool,
        pub accept_literal_reached: bool,
        pub first_overmerge: Option<String>,
    }

    /// Read the current parse's signals.
    pub fn snapshot() -> Snapshot {
        STATE.with(|s| {
            let st = s.borrow();
            Snapshot {
                merge_calls: st.merge_calls,
                peak_fine: st.peak_fine,
                peak_gll_floor: st.peak_gll_floor,
                peak_literal: st.peak_literal,
                peak_slot: st.peak_slot,
                overmerge_pairs: st.overmerge_pairs,
                overmerge_buckets: st.overmerge_buckets,
                bp_recovered_pairs: st.bp_recovered_pairs,
                reach_literal_size: st.reach_literal.len() as u64,
                reach_slot_size: st.reach_slot.len() as u64,
                accept_slot_reached: st.accept_slot_reached,
                accept_literal_reached: st.accept_literal_reached,
                first_overmerge: st.first_overmerge.clone(),
            }
        })
    }
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
            cursors_dropped_via_sr_subsume: 0,
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
            // Phase F.13 chain_10000 Exp 16 (2026-05-26).
            mem_attr_branch_cursors_max: 0,
            mem_attr_cache_entries_max: 0,
            mem_attr_cache_pending_members_sum_max: 0,
            mem_attr_cache_worker_snapshots_sum_max: 0,
            mem_attr_cache_deferred_continuations_sum_max: 0,
            mem_attr_sppf_stack_arena_nodes_max: 0,
            mem_attr_incoming_edge_stack_arena_nodes_max: 0,
            mem_attr_sppf_nodes_max: 0,
            mem_attr_sppf_symbol_packings_max: 0,
            mem_attr_gss_nodes_max: 0,
            mem_attr_gss_edges_max: 0,
            mem_attr_visited_dispatch_unique_arcs_max: 0,
            mem_attr_visited_dispatch_total_entries_max: 0,
            mem_attr_recovery_deltas_unique_arcs_max: 0,
            mem_attr_sppf_symbol_terms_max: 0,
            // Exp 16 round 3 (2026-05-26).
            mem_attr_sppf_text_arena_bytes_max: 0,
            mem_attr_sppf_text_index_count_max: 0,
            mem_attr_sppf_dedup_packing_children_bytes_max: 0,
            mem_attr_sppf_dedup_symbol_count_max: 0,
            mem_attr_sppf_dedup_terminal_count_max: 0,
            mem_attr_sppf_collection_arena_total_entries_max: 0,
            mem_attr_sppf_collection_arena_unique_arcs_max: 0,
            mem_attr_lex_fork_path_total_entries_max: 0,
            mem_attr_lex_fork_path_unique_arcs_max: 0,
            mem_attr_binder_scope_marks_unique_arcs_max: 0,
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
            // Phase F.13 chain_10000 plan-amend Substage 0 (2026-05-26).
            edge_kind_projection: EdgeKindProjection::default(),
            // Phase F.13 chain_10000 Exp 14 Substage 0 (2026-05-27).
            tomita_key_projection: TomitaKeyProjection::default(),
            // Phase F.13 chain_10000 Exp 15 Substage 0 (2026-05-27).
            continuation_size_projection: ContinuationSizeProjection::default(),
            // Phase F.13 chain_10000 Lazy redesign L0 (2026-05-27).
            thunk_force_projection: ThunkForceRatioProjection::default(),
            // Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27).
            pop_kind_histogram: [0; 16],
            // Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27).
            apply_action_variant_histogram: [0; 21],
            // Phase F.13 chain_10000 Lazy redesign L2a prep (2026-05-27).
            push_kind_histogram: [0; 16],
            // Phase F.13 chain_10000 COQ-S0 (2026-05-27).
            cohort_origin_dispatch_keys_seen: rustc_hash::FxHashSet::default(),
            cohort_origin_equiv_keys_seen: rustc_hash::FxHashSet::default(),
            cohort_origin_distinct_per_step_max: 0,
            cohort_origin_distinct_per_step_sum: 0,
            cohort_origin_per_step_samples: 0,
            // Phase F.13 chain_10000 Plan v6 H2 (2026-05-27).
            chain_earley_trigger_count: 0,
            chain_earley_succeeded_count: 0,
            chain_earley_returned_none_count: 0,
            chain_earley_atoms_absorbed_sum: 0,
            // Evidence-pruning P1 Step-0 (2026-06-11).
            crosscat_lhs_delegates_spawned: 0,
            crosscat_lhs_delegate_dup_at_pos_source: 0,
            crosscat_lhs_spawns_at_pos_source: FxHashMap::default(),
            cast_then_infix_steps: 0,
            crosscat_lhs_stack_memo: FxHashMap::default(),
            // EP-P1 amended §P1 shadow (2026-06-11).
            ep_p1_shadow_would_share_total: [0; WPDA_STATE_CLASS_COUNT * 2],
            ep_p1_shadow_seen: FxHashMap::default(),
            // EP-P1 measure (Round 6).
            ep_p1_measure_workers: 0,
            ep_p1_measure_inflight_hits: 0,
            ep_p1_measure_resolved_hits: 0,
            ep_p1_measure_failed_hits: 0,
            ep_p1_measure_first_tail: FxHashMap::default(),
            ep_p1_measure_tail_divergent: 0,
            ep_p1_consumed_in_place: 0,
            ep_p1_park_overflow_fallbacks: 0,
            // led_chain diagnostic (TEMPORARY).
            dbg_ccl_reg_outcome: [0; 4],
            dbg_ccl_resolved_not_quiescent: 0,
            dbg_ccl_parked_ok: 0,
            dbg_ccl_reg_by_key: FxHashMap::default(),
            dbg_ccl_overflow_by_key: FxHashMap::default(),
            dbg_ccl_inflight_keys_at_eoi: 0,
            dbg_ccl_drain_jobs: 0,
            dbg_ccl_drain_members: 0,
            dbg_ccl_eoi_jobs: 0,
            dbg_ccl_eoi_members: 0,
            dbg_ccl_quiesce_to_zero: 0,
            dbg_ccl_lineage_inc: 0,
            dbg_ccl_lineage_dec: 0,
            dbg_ccl_m1_reached: 0,
            dbg_ccl_m1_orphan_count: 0,
            dbg_ccl_m1_injected: 0,
            dbg_ccl_rounds_capped: 0,
            dbg_ccl_eoi_release_set: 0,
            dbg_ccl_stale_proceed: 0,
            dbg_ccl_dead_worker_released: 0,
            dbg_ccl_accept_present_skip: 0,
            // EP-P2 Step-0 shadow counters.
            parikh_shadow_would_refute_total: [0; WPDA_STATE_CLASS_COUNT * 2],
            parikh_shadow_refuted_then_accepted: [0; WPDA_STATE_CLASS_COUNT * 2],
            parikh_shadow_steps_after_would_refute: [0; WPDA_STATE_CLASS_COUNT * 2],
            eoi_dead_cursors_parikh_refutable: [0; WPDA_STATE_CLASS_COUNT * 2],
            // EP-P4 Step-0 order-only counters.
            zero_innovation_demotions: 0,
            demoted_member_unstepped_at_exit: 0,
            frontier_ess_x1000_last: 0,
            // EP-P5 entry-gate measurement counters.
            p5_residual_dead_steps_own: 0,
            p5_residual_dead_steps_lineage: 0,
            p5_accepted_steps_own: 0,
            p5_accepted_steps_lineage: 0,
            p5_eoi_cursors_examined: 0,
            p5_eoi_dead_cursors: 0,
            // GSS node-coarsening shadow fields (Plan a0ddad66) — all zero
            // here; this display test predates them.
            ..Default::default()
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
