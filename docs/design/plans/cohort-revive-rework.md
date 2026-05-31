# Dispatch-Cohort Revive-Loss Fix — Plan + Scientific Evaluation (2026-05-29)

Fixes the ~30 cross-cat/cast/bare-var/binder failures (the Phase-8 research-grade remainder).
Ledger anchor: `drive-suite-green-ledger.md` "⚑ Cross-cat cluster ROOT CAUSE".

## Root cause (trace-proven; empirically: `test_nested_int_int`=`int(int(5,32),32)`, 90.9% inflight_collisions, 11/24 keys stuck InFlight → orphaned members → "no accepting branch")
`allocate_fork_push_child` (`wpda_walker.rs:12831-12893`) registers each `CrossCatDelegate` under
`DispatchKey::new(pos_after, source_src_idx, inner_cur_bp)`. A colliding second register →
`InflightCollision` → `pause_cohort_member` (`dispatch_cohort.rs:628`, stores full `CohortShell`
pre-dispatch state) → `return Vec::new()` (removed from stepping). Paused members revive ONLY when a
sibling worker reaches `Resolved` (drain at `wpda_walker.rs:9068-9156`, `take_pending_for_drain`
matches ONLY `Resolved`). **Loss branches:** (1) key stays `InFlight` forever (worker dies first) →
never drained; (2) `fail()` (`dispatch_cohort.rs:702`) overwrites with `Failed`, DISCARDING
`pending_members`. `force_materialize_cohort_frames` (`:8408`) flushes `Frame::Cohort` in
branch_cursors, NOT the cache → EOI `accepting_indices==0` → "no accepting branch" (`:4191-4214`).
Compounded by `extract_dispatch_config` (`:2654`) keying on `(pos,cat_src,cur_bp)` only (no rule/source).
Bucketed PRE-EXISTING (fails identically at a23ef69). Point-fix FALSIFIED (cohort no-pause "shuffled" failures).

## Chosen approach: TARGETED revive-on-loss (a)+(b), NOT full Exp-15
Members carry enough to revive: `CohortShell` (`cohort_lazy.rs:108-185`) captures the full pre-dispatch
cursor; `materialize_branch_cursor(shell,member)` (`cohort_lazy.rs:593-628`) reconstructs a steppable
`BranchCursor` in the `CrossCatDelegate` state. Re-inject orphaned members → they run the cross-cat
sub-parse themselves → reach EOI. (`revive_cohort_member_with_snapshot` can't be reused — needs a
resolved worker snapshot.) Exp-15/14 are memory-ceiling programs orthogonal to this correctness bug.

## Milestones (each independently buildable + gated)
- **M0 — census (measure-only):** `dispatch_cohort.rs` add `orphaned_pending_members_count()` +
  `inflight_orphan_members_total`/`failed_orphan_members_total` counters + `write_summary`; log in
  `resolve_at_end_of_input` under `PRATTAIL_WALKER_STATS`. Predict ≥1 orphan/failing-test, 0 for passing.
- **M1 — revive-on-loss (InFlight; the core):** `dispatch_cohort.rs` add
  `drain_orphaned_inflight_members()` (TAKE pending_members from non-Resolved entries w/ a shell →
  idempotent). `wpda_walker.rs` `run_to_end_of_input` `!progress_made` block (~`:3844-3849`): before
  `return Ok(())`, call `revive_orphaned_cohort_members_once()` → if it injected cursors, `continue`.
  New method materializes each orphan via `materialize_branch_cursor` → push `Frame::Concrete` into
  `branch_cursors`. Guard: take-semantics + `revival_rounds < 4` cap.
- **M2 — Failed-discard:** `fail()` stashes `pending_members` into an `orphaned_failed` side-queue;
  drain extends to it. (Defer if M0 shows 0 failed-orphans, but implement for soundness.)
- **M3 — bare-var/binder facet:** after M1/M2, re-run bare-var/comm/binder subset. If `bare_variable_infers_as_proc`
  still `Ambiguous`, reconcile in inference/realize (preserve `Ambiguous` first-class; evidence-driven).
- **M4 — (OPTIONAL, gated) widen `DispatchKey`/`extract_dispatch_config` keying** for cross-cat-vs-cross-cat
  lex-split collisions. Keep `EquivKey` (`dispatch_cohort.rs:90`) UNWIDENED (chain dedup/memory ceiling).
  Apply ONLY if M3 leaves residual; gate behind Welch + memory re-measurement; Approach-P fallback.

## Disambiguation (preserved)
Revived members are alternates kept by EVIDENCE (paused = would-have-been-live workers). Re-injected
cursors flow through `merge_equivalent_cursors` (`:9190`) + SPPF dedup → observational collapse only.
`Ambiguous` stays first-class. Falsifier: `-3!` ladder + `h3_chain_correctness` + `wpda_parity_*` stay green.

## Scientific evaluation (Welch's t-test, p<0.05) — the "Welch-gated" requirement
- **H_correctness:** M1 flips the cast/nested cross-cat tests green (orphan-starved family).
- **H_perf (Welch):** M1 is NEUTRAL on chain perf — chains early-return before cohort registration
  (`pos_in_absorbed_chain_interval` `:12848`) so orphan-drain adds ~0 hot-path work.
  Panel: `trampoline_tests::{test_left_assoc_chain_50/100/200, test_right_assoc_chain_50/100/200/1000}`,
  release, QUIET, N≥15 (hyperfine `-N --warmup 3 --runs 15`), Welch two-sample t per arm; ACCEPT iff
  NO arm shows LOSS at p<0.05 (treatment_mean ≤ baseline_mean + 1 SE). Baseline = pre-M1 (recovery patch
  state); treatment = post-M1.
- **H_memory:** chain_1000/chain_2000 peak RSS within +5% of baseline (chain_10000 O(N) ~112MB ceiling intact).
- pgmcp: `experiment_open`/`record_measurement`/`decide` continuing the exp #8 lineage.

## Verification (per-milestone + end-to-end)
gauntlet `cargo test --release -p mettail-prattail --lib` 4220/0; op-suites gen_calculator_op ≥1331/0,
gen_rhocalc_op 532/0; the ~30 cross-cat targets; disambiguation gate; Welch+memory (M1/M2/M4).

## Effort: ~3-5 sessions. Resume via the ledger "⚑" section after each milestone.

## Critical anchors
- Pause: `wpda_walker.rs:12876-12893`; storage `dispatch_cohort.rs:628-697`.
- Revive-only-on-resolve: `wpda_walker.rs:13608-13624` + `dispatch_cohort.rs:534-599`.
- Failed discard: `dispatch_cohort.rs:702-709`. EOI miss: `wpda_walker.rs:8408-8424`.
- M1 hook: `wpda_walker.rs:3844-3849`. Reconstruct: `cohort_lazy.rs:593-628`.
- Keys: `dispatch_cohort.rs:63-95` (keep `equiv()`/`EquivKey` unwidened). Cycle-defense: `wpda_walker.rs:2654-2667`.
- Welch panel: `languages/tests/trampoline_tests.rs:279-367`; bench `languages/benches/bench_scaling.rs`.
