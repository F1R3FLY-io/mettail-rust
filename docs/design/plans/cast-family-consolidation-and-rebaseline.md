# Cast-family consolidation onto feature/wfst-architecture + full-suite re-baseline (2026-06-03)

## What happened (the correction)
An entire session of Float cast-family work was conducted on `d2d9a3b` (tag `sigb-b3-span-FINAL`) — a HELD, UNMERGED line that is **not** an ancestor of the shipping branch `feature/wfst-architecture` (merge-base `6507b9c`). The "definitively proven" Float root did not reproduce on the shipping branch; ~8 fix attempts were moot. The empirical red-team caught the branch mislocation. The cast-family work itself (Bool closure + cohort machinery, +4165 lines) was real, needed, and never merged. See `memory/feedback_verify_base_branch_before_work.md`.

## Consolidation (LANDED, verified, reversible)
Merged `sigb-b3-span-FINAL`/`d2d9a3b` onto `feature/wfst-architecture` HEAD `d14fc4c` → **`315cfc3`** (staged in a detached worktree, 5 conflicts resolved by taking the fuller `d2d9a3b` side while **preserving feature/wfst's unique `realize-DFS shared-node fix` byte-for-byte**, calc tests unioned; then fast-forwarded). Reversible: `git reset --hard d14fc4c`. `dispatch_cohort.rs` 943→1765 lines.

## Full-suite regression diff (the careful verification)
`cargo nextest run --workspace` on both branches (bounded ci profile, 32G-capped):
- **PRE `d14fc4c`: 9731 run, 68 failed, 2 timed out, 20 skipped.**
- **POST `315cfc3`: 9734 run, 56 failed, 20 skipped.** Net **−12**.
- **FIXED by consolidation (18):** `calculator::{test_nested_int_int, test_nested_int_float, test_nested_float_int_arithmetic, test_cast_float_overflow_to_inf, test_cast_int_float_floor, test_cast_int_nonfinite_float_is_error, test_casts_from_numeric_strings, test_int_from_float_still_works, test_binary_int_requires_width, test_ambiguous_dispatch_gt_env, test_ambiguous_dispatch_gteq_env, simulator_regression_cross_cat_with_parens}` + `rhocalc_tests::comm::{comm_with_remaining_parallel, multi_input_two_channels, multi_input_uses_both_vars, single_channel}` + `rhocalc_tests::parsing::bare_variable_infers_as_proc` + `gen_calculator_prop::map_display_parse_roundtrip`.
- **REGRESSIONS introduced (6):** seed-flaky proptests `gen_calculator_prop::list_display_parse_roundtrip`, `gen_mixedmath_prop::int_display_parse_roundtrip`, `gen_rhocalc_prop::bigint_display_parse_roundtrip`, `gen_ambient_prop::proc_display_parse_roundtrip` (the latter is the known >900s HANG) — re-run to confirm flaky; **deterministic+real: `recovery_integration_tests::test_calc_recovery_deeply_nested_with_error`, `rhocalc_tests::new_and_extrusion::new_multi_binder_parses`**.
- **VERDICT: consolidation STANDS** (18 fixes incl. the whole int/float cast family, vs ~2 real deterministic regressions). The regressions join the green backlog.

## Remaining 56 failures on feature/wfst-architecture @ 315cfc3 (the green backlog)
- **~30 `*_display_parse_roundtrip`/`*_strong_roundtrip` proptests** across nearly every grammar (calculator, rhocalc, ledtest, guardedrho, class2/3, mixedmath, ambient) — the plan's **Cluster J** (mostly pre-existing); likely systemic display↔parse. The plan's notes: "downstream of Cluster B parser".
- **~15 `rhocalc_tests`** (parsing::receive/new_single, new_and_extrusion::*, comm::*, congruence::{add,comparison}_cong, beta::*, native_ops fraction, exec) — rhocalc parse/eval. Sample mode: `parsing::receive` on `(x?y).{y!(0)}` → "no accepting branch reached end of input".
- **3 cast residual:** `test_nested_float_float_int`, `test_triple_nested_float` (the genuine Float STOP — now on the right branch, the prior cohort-detachment root-cause applies HERE), `test_bool_from_list_elem`.
- **~6 scattered:** `roundtrip_tests::{roundtrip_int_parse_display, idempotent_int_display}`, `led_delegation_tests::test_p1_10_parenthesized_sub_expressions`, `casting_example_files_calculator`, `class2_opt_collection_smoke::choosemaybe_parse_none_via_wpda`, `gen_class3multi_prop::proc_parse_determinism`, + the 2 deterministic consolidation regressions.
- **1 HANG:** `gen_ambient_prop::proc_display_parse_roundtrip` (>900s) — pre-existing; needs input-bounding / the parse pathology root.

Artifacts: `/var/tmp/suite-green/{wfst-PRE-consolidation-fullsuite,wfst-consolidated-fullsuite}.log` + `{PRE,POST}-clean.txt`. Reversibility anchor: `d14fc4c`.

## Next (on the shipping branch, carefully)
Drive the 56 to green. Start with the dominant, likely-systemic **roundtrip cluster (Cluster J ~30)** — root-cause one representative failure to find the common root (vs heterogeneous), then prove-root → design → red-team → implement per the standing discipline. Then rhocalc (~15), the 2 deterministic regressions, the scattered, the Float residual, and the hang.

---

## ★ NEXT-SESSION HANDOFF (2026-06-03; paused to reserve tokens — RESUME FROM HERE) ★

### Branch reality (verify FIRST, every session)
- **Work ON `feature/wfst-architecture`** (the shipping branch; HEAD `ba5790c` at handoff). The cast-family consolidation is **LANDED** as `315cfc3` (parents `d14fc4c` + `d2d9a3b`). **Reversibility anchor: `d14fc4c`** (`git reset --hard d14fc4c` undoes the consolidation). `d2d9a3b` (tag `sigb-b3-span-FINAL`) is NOW in `feature/wfst` history — do NOT work on it directly.
- Before ANY work: `git merge-base --is-ancestor <base> feature/wfst-architecture` + reproduce the target failure ON `feature/wfst-architecture`. (The whole prior detour was an unmerged `d2d9a3b` worktree — see `memory/feedback_verify_base_branch_before_work.md`.) NOTE: `Agent isolation:worktree` may base from `main`, NOT the current branch — the `a9d79f3b` agent landed on `7eb035c`(main) and had to detach-checkout `ba5790c`. Always confirm the worktree HEAD/branch.

### Full-suite baseline on `feature/wfst-architecture @ 315cfc3`: 9678 passed / **56 failed** / 20 skipped (was 68 pre-consolidation; net −12). Backlog by cluster + PROVEN roots:

**Cluster J — display↔parse roundtrip (~30) — HETEROGENEOUS, 3 roots (root-cause agent `a9d79f3b`, `/var/tmp/suite-green/clusterj-VERDICT.txt`):**
- **ROOT A (DOMINANT ~65-70%, cross-grammar):** implicit cross-cat coercion/injection (`BoolToInt`/`IntToBigRat`/`UInt32ToBigInt`/`BoolToFloat`/`CastNum`/`CastPred`…) OR operand-level category-mix whose Display emits no wrapper → on re-parse, `arg.into_term::<TargetCat>()` returns **None** for NON-LEAF inners → "all fork branches dropped" at WFST fork/realize. **Code fix-point: the `into_term::<T>()→None` site in the SPPF cross-cat realize path** (`prattail/src/wpda_walker.rs:10471` + resolve/realize). Build self-diagnoses it: `pipeline.rs:235-280` `DeadRuleWarning::WfstUnreachable`; `lint.rs:2175-2218` K01 KAT (Calc 65 / RhoCalc 38 / LedTest 8 / GuardedRho 5 failing A→B pairs). **NEGATIVE flip: `B2/B3/B3_SPAN_DISABLE` + caps (`MAX_COHORT_FRAME_MEMBERS`/`MAX_REVIVAL_ROUNDS`/`SPURIOUS_ORPHAN_THRESHOLD`) have ZERO effect → the `315cfc3` cohort cache is NOT the root; it's upstream at WFST fork/realize.** Sub-roots: **A′** operand-category-mix (FLIP-2: toggling one operand's cat flips FAIL↔PASS); **A″** same-keyword cast overload 1-arg vs 2-arg (`wpda_walker.rs:9075` "Exp-15 doubly-nested casts"; **FLIP-1 DECISIVE**: `int`→`intw` keyword rename fixes `int(str(5),3)`). FLIP-3: mixedmath `BoolToInt`, inner Bool complexity flips it.
- **ROOT B (~10%, calculator-only):** ternary `?:`(`Tern`, `calculator.rs:142`) adjacent to a comparison — `e` arm greedily extends across the Bool op (`1 ? 2 : 3 > 4 ~ 5`). FLIP-4 control-confirmed (not code-flipped).
- **ROOT C (~25-30%, process-calculus grammars):** Name/binder-led production (`POutput` `rhocalc.rs:74`, `NQuote` `@(…)`, `for`/`where`, multi-`Binder` `Scope`) NOT admitted in nested-delimited operand position. `a!(error)` parses standalone; `len(a!(error))`/`@(a!(b))` fail at the leading identifier (NOT the `error` term). Min-pair isolated (not code-flipped).

**rhocalc_tests (~15):** parse "no accepting branch" (e.g. `parsing::receive` `(x?y).{y!(0)}`) — **overlaps ROOT C** (nested Name/binder in operand) + ROOT A (cross-cat). Likely cleared substantially by the Root C and Root A fixes.

**Cast residual (2):** `test_nested_float_float_int`, `test_triple_nested_float` = **ROOT A″** (the same-keyword `float(`-overload doubly-nested cast). The prior `d2d9a3b` cohort-detachment investigation (now superseded — it was the WRONG layer per the NEGATIVE flip) is moot; the REAL fix is A″ (per-keyword cast disambiguation / the `into_term` realize site). FLIP-1's `intw` rename is the proof-of-mechanism.

**2 deterministic consolidation regressions:** `recovery_integration_tests::test_calc_recovery_deeply_nested_with_error`, `rhocalc_tests::new_and_extrusion::new_multi_binder_parses` (introduced by `315cfc3`; fix or accept).

**Scattered (~6):** `roundtrip_tests::{roundtrip_int_parse_display, idempotent_int_display}`, `led_delegation_tests::test_p1_10_parenthesized_sub_expressions`, `casting_example_files_calculator`, `class2_opt_collection_smoke::choosemaybe_parse_none_via_wpda`, `gen_class3multi_prop::proc_parse_determinism`, `calculator::test_bool_from_list_elem`. **1 HANG:** `gen_ambient_prop::proc_display_parse_roundtrip` (>900s) — needs input-bounding / the parse pathology.

### THE UNIFYING INSIGHT
ROOT A (+ A″) is the single highest-yield target: it spans the bulk of Cluster J across grammars, the 2 Float targets, and (via ROOT C-adjacency) much of rhocalc. **The fix lives at the SPPF cross-cat realize path (`into_term::<T>()→None` for non-leaf inners) + the same-keyword cast overload disambiguation — NOT the cohort cache** (flip-proven NEGATIVE). Tackle ROOT A first (design → red-team-to-convergence → implement), then ROOT C (process-calculus nested operand), then ROOT B, the 2 regressions, scattered, the hang.

### RESUME STEPS (next session)
1. Confirm `feature/wfst-architecture @ ≥315cfc3`; re-confirm the 56-baseline (`/var/tmp/suite-green/POST-clean.txt`).
2. **ROOT A**: prove the code fix-point (toggle/trace the `into_term::<T>()→None` realize site + the A″ keyword-overload) → design → **red-team to convergence** (per `memory/feedback_red_team_design_until_convergence.md`) → implement → verify (full-suite diff vs the 56) → commit. Highest yield (Cluster J bulk + Float residual + rhocalc-adjacent).
3. Then ROOT C, ROOT B, the 2 regressions, the scattered, the hang. Each: prove-root → design → red-team → implement → verify → commit.
4. Disciplines: prove-root-before-claiming; verify-base-branch; red-team-to-convergence; one 32G build at a time; Welch for any perf-path change; commit at stable points.

### Pending cleanup (needs user approval — `git worktree remove --force` was DENIED as destructive)
Stray worktrees (all commits recoverable via branches/tags/feature-wfst-history): `/var/tmp/wt-realize`, `/var/tmp/wt-genfactor`, `/var/tmp/wt-consolidate`, `/var/tmp/wt-wfst`, `.claude/worktrees/agent-a19f5e8f55e0db73f`, `.claude/worktrees/agent-a9d79f3b45f2dd40d`. Ask before removing.

### Artifacts
`/var/tmp/suite-green/`: `wfst-{PRE-consolidation,consolidated}-fullsuite.log`, `{PRE,POST}-clean.txt`, `clusterj-VERDICT.txt` + `clusterj-step*.log`, `consolidate-VERDICT.txt`. pgmcp experiment #9.
