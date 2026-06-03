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
