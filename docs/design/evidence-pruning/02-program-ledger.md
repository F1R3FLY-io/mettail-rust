# Evidence-Pruning Program — Running Ledger

> The P-series execution ledger (plan: `02-staged-implementation-plan.md` v3, USER-APPROVED
> 2026-06-11; red-team record: `03-red-team-ledger.md`, CONVERGED after 4 rounds).
> Every stage records its M/D/I/L commits, measured numbers (per-corpus), accept/STOP verdicts,
> and pgmcp experiment ids here. STOPs are first-class outcomes (H13/CD06 precedent).
>
> **Strategic frame (user directive, 2026-06-11):** the P-series executes FIRST; the
> Dovetail/Rho-machine flip (M-RHO.1→.4) follows immediately after — and no further correctness
> investment goes into Ascent-side problem classes the flip dissolves by construction.

## Baseline (pinned 2026-06-11 @ `f1ea267c`)

The post-ROOT-A/ROOT-F/eval-closure baseline — all waste numbers and battery gates compare
against THIS commit (the unsourced pre-ROOT-A "342,699" figure is retired; see red-team F1):

| Suite | Result | Notes |
|---|---|---|
| `gen_ledtest_op` | **220/0** | SENTINEL — any failure aborts the active stage |
| `gen_calculator_op` | 1330/0 | |
| `gen_rhocalc_op` | 530/1 | pre-existing `castbigrat` (tracked separately) |
| `edge_case_tests` | 229/0 | the historical ambient pair fixed @ 38dcd485 |
| `rhocalc_tests` | **126/0** | first-ever full green @ f1ea267c |
| `gen_ambient_analytical` | 52/0 (1 ignored) | |
| `gen_ambient_rewrite` | 13/0 | |
| `gen_ambient_prop` | 17/0 | |
| `mettail-prattail --lib` | 3980/0 | includes egraph:: |
| `--features walker-stats` build | green | I6 gate (round-2 B-1) |
| `rocq-prattail-wpda` | green | zero-Admitted corpus |

Model commits already landed (M-commits, zero-admission, `Print Assumptions` clean):
- `ParikhObligationGate.v` (P2 spec, 9 thms) @ 288bcb42
- `EvidenceGatedDelegates.v` (P1 spec, 6 thms) @ 6829a5e5
- `ForwardOrderOnly.v` (P4 spec, 6 thms incl. the consolidated InnovationDemotion obligations) @ 8106ec26
- `CollectionForkEvidence.v` (16 thms; the ROOT-F production validation of the program's
  philosophy) @ 288bcb42 + 38dcd485 + ac88faeb

## P0 — Scaffold (this stage)

| Deliverable | Status |
|---|---|
| This ledger file (pinned baselines) | ✅ this commit |
| `stats_inc_idx!` + `WPDA_STATE_CLASS_COUNT` (partitioned-counter mechanics, round-2 m-1) | ✅ this commit |
| P-series conventions section in walker_stats.rs (`PRATTAIL_EP_<STAGE>=off\|shadow\|on`; `<stage>_shadow_{would_refute_total, refuted_then_accepted, steps_after_would_refute}` partitioned by WpdaState-class × recovery_enabled; non-zero-slot printing) | ✅ this commit |
| `languages/examples/cast_tower_bench.rs` (the P1/P2 Welch panel; kill-switch arms; **tiered** — see smoke findings) | ✅ this commit |
| `recovery_cohort_bench` zero-innovation extension + `PRATTAIL_EP_P4_DEMOTE` arm | ✅ this commit |
| Battery identical (P0 is behavior-neutral) | ✅ **PASSED** — ledtest 220/0 SENTINEL, calc 1330/0, rhocalc_op 530/1 (pre-existing castbigrat), edge 229/0, **rhocalc_tests 126/0**, ambient 52/0+13/0+17/0, prattail-lib 3980/0, BOTH cfg builds green (default + `--features walker-stats`), bench smoke exit-0 with well-formed CSV |

### P0 smoke findings (2026-06-11 @ f1ea267c, debug profile)

The bench smoke was NOT a formality — the panel as first written (uniform 20 reps × 30
samples) could never complete its base arm. Per-input bisect (single parse, debug):

| idx | input | shape | time |
|---|---|---|---|
| 0 | `int(3) == 3` | d1 + cmp | 7.5 ms |
| 1 | `int(3) + 3` | d1 + arith | 7.0 ms |
| 2 | `int(3)` | d1 | 6.8 ms |
| 3 | `int(float(int(3.14)))` | d3 tower | 29.6 ms |
| 4 | `int(float(int(3.14))) == 3` | d3 tower + cmp | **1.17 s** (40× its bare tower) |
| 5 | `int(float(int(float(int(3.14)))))` | d5 tower | 121 ms |
| 6 | `int(float(int(float(int(3.14))))) == 3` | d5 tower + cmp | **> 580 s** (> 4800× its bare tower) |
| 7 | `int(1) == 1 and int(2) == 2` | 2× d1 + cmp | 11.7 ms |
| 8 | `float(3) >= 3.0` | d1 float cmp | 7.2 ms |

**The law:** bare towers scale gently (~4× per +2 depth); a compare continuation BEHIND the
tower explodes the frontier ~K^depth (d3+cmp 40×, d5+cmp >4800× — consistent with K≈5-7 per
level once the cross-cat-LHS delegate fan engages). This is the P1 pathology measured live on
the shipping tip — the panel's base arm IS the "before" evidence, and the depth-independence
claim (`CastLookaheadGateBound`: gated frontier ~ trigger count, NOT depth) is directly
testable input-by-input.

**Protocol consequence (bench redesign, this commit):** per-input CSV rows
(`config,input_idx,reps,sample,nanos`); heavy tier (idx 4, 6) runs reps=1/sample; env knobs
`CAST_TOWER_SAMPLES` / `CAST_TOWER_HEAVY=off` (debug smokes) /
`CAST_TOWER_PATHOLOGICAL=on` (idx 6 — EXCLUDED by default so the bench completes out of the
box; even release-profile idx 6 projects to tens of seconds per parse × 30 samples on the
base arm). Panels run RELEASE. Base-arm evidence for idx 6 is a right-censored wall-clock
bound (> 580 s debug single-parse at this baseline), not a t-test sample; treatment arms
(P1 gate on) opt in and SHOULD complete it — that asymmetry is itself the
depth-independence acceptance evidence.

**Harness traps recorded (cost a prior session ~3 silent smokes):** (1) `cargo run --example`
re-fingerprints against a DIFFERENT feature unification than `cargo build --examples` → full
languages-lib rebuild (~minutes) silently eating the timeout — build first, then execute the
binary from `target/debug/examples/` directly; (2) Rust stdout is BLOCK-buffered to
files/pipes — a timeout-killed run loses ALL buffered CSV, indistinguishable from "no
output" (`exit: 0` from `head`/`tail` in a pipeline masks the kill); progress/diagnostic
lines belong on stderr (unbuffered).

## P1 — Delegate fan (next)

M `EvidenceGatedDelegates.v` ✅ (landed early) → D counters/probes → gates (d2 iff
`crosscat_lhs_d2_only_hits > 0`; share iff dup ≥ 10%, EquivKey ONLY) → I → L.

## Stage log

- 2026-06-11 P0 opened.
- 2026-06-11 P0 smoke caught the heavy-tier blowup (idx 6 > 580 s debug) → bench redesigned
  (tiers + per-input rows + env knobs); battery gate PASSED (all 9 suites + both cfg builds
  identical to the pinned baseline); P0 committed.
