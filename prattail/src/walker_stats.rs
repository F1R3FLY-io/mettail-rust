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
    /// helper below — 13 buckets, one per `EdgeKind` variant. Sampled
    /// at every `WpdaStepAction::Pop` entry by deriving the EdgeKind
    /// from the popped GSS node's symbol via `EdgeKind::from_symbol`.
    ///
    /// L2 instrumentation gate: confirms which EdgeKind dominates the
    /// chain-interior Pop volume before paying L2's ~400 LOC budget on
    /// the broadcast helper. The Plan v2's L2 substage targets the
    /// single-predecessor convergent EdgeKinds (CategoryEntryRoot,
    /// CrossCatProjection, PrefixRuleEntry, InfixContinuation,
    /// LexAltLiteral, OptionalGroupAt). If the dominant bucket falls
    /// outside that set (e.g., Generic, ReturnFrame, CollectionElement),
    /// L2 is misdesigned and needs re-architecture.
    pub pop_kind_histogram: [u64; 13],

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
    pub push_kind_histogram: [u64; 13],

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
        EdgeKind::CrossCatProjection { .. } => 2,
        EdgeKind::CrossCatLhs { .. } => 3,
        EdgeKind::CrossCatLhsReentry { .. } => 4,
        EdgeKind::PrefixRuleEntry { .. } => 5,
        EdgeKind::InfixContinuation { .. } => 6,
        EdgeKind::LexAltLiteral { .. } => 7,
        EdgeKind::OptionalGroupAt { .. } => 8,
        EdgeKind::CollectionElement { .. } => 9,
        EdgeKind::GroupingMarker { .. } => 10,
        EdgeKind::MixfixMarker { .. } => 11,
        EdgeKind::ReturnFrame { .. } => 12,
    }
}

/// Phase F.13 chain_10000 Lazy redesign L2 prep (2026-05-27): human-
/// readable label for each `pop_kind_histogram` bucket index.
pub fn pop_kind_label(idx: usize) -> &'static str {
    [
        "Generic",
        "CategoryEntryRoot",
        "CrossCatProjection",
        "CrossCatLhs",
        "CrossCatLhsReentry",
        "PrefixRuleEntry",
        "InfixContinuation",
        "LexAltLiteral",
        "OptionalGroupAt",
        "CollectionElement",
        "GroupingMarker",
        "MixfixMarker",
        "ReturnFrame",
    ][idx.min(12)]
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
            // L2a gate: buckets [1] CategoryEntryRoot + [2] CrossCatProjection
            // + [8] OptionalGroupAt are the L2a targets. CrossCatLhs and
            // CrossCatLhsReentry are identity-strict and intentionally excluded.
            let l2a_target: u64 = self.push_kind_histogram[1]
                + self.push_kind_histogram[2]
                + self.push_kind_histogram[8];
            let l2a_pct = 100.0 * (l2a_target as f64) / (push_total as f64);
            writeln!(
                f,
                "    L2a_target_share (CategoryEntryRoot+CrossCatProj+OptGroupAt): {} / {} ({:.1}%) — gate (≥ 80%): {}",
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
                + self.pop_kind_histogram[5]
                + self.pop_kind_histogram[6]
                + self.pop_kind_histogram[7]
                + self.pop_kind_histogram[8];
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
            pop_kind_histogram: [0; 13],
            // Phase F.13 chain_10000 Lazy redesign L2 prep-2 (2026-05-27).
            apply_action_variant_histogram: [0; 21],
            // Phase F.13 chain_10000 Lazy redesign L2a prep (2026-05-27).
            push_kind_histogram: [0; 13],
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
