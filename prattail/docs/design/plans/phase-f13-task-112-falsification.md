# Phase F.13 Task #112 — Calculator AST Box→Arc: Hypothesis Falsified at Stage 1 Gate

**Status:** FALSIFIED — experiment did not proceed to Stage 2.
**Date:** 2026-05-23.
**Tip at falsification:** `605c716` on `feature/wfst-architecture`.

## Hypothesis under test

**H4-prime (Plan agent reformulation, since the original H4 was obsoleted
by Phase F.3c.4's deletion of `cursor.builder`):**

> Replacing `Box<#cat>` with `Arc<#cat>` in the generated AST enum will
> reduce wall-clock time of `Language::run_ascent_typed` on rewrite-
> heavy inputs (e.g., `rholang_bench::replication/basic`) by ≥ 5 %.
> Mechanism: every cloned subtree in a rule body becomes a refcount bump
> (8-byte atomic increment) instead of a full recursive deep clone via
> the trampolined `iterative_clone` engine. The `DualIndexedRel`
> buckets become parallel `Arc` handles, not duplicated subtrees.

## Method

Per the Plan agent's recommended 2-stage gate (`memory/f13-stage-2-3-
semantic-hash.md` and feedback-optimization-t-test discipline):

1. **Stage 1 (~1 hour, cheap):** profile `rholang_bench::replication/basic`
   at HEAD with `perf record --call-graph fp -F 999`. Decision rule:
   - AST clone consumes **≥ 20 %** of total time → motivated; proceed to
     Stage 2 (15-18 hour Box→Arc edit + Welch's t-test).
   - AST clone consumes **10–20 %** → marginal; proceed only if
     Scope-body-only narrow scope (≤ 2 hours) is acceptable.
   - AST clone consumes **< 10 %** → falsified; do not proceed.

2. **Stage 2 (15-18 hours, contingent on Stage 1):** full Box→Arc swap
   per `phase-f13-task-112-plan-agent-design`. Welch's t-test on
   `rholang_bench::replication/basic` N=15 baseline vs N=15 treatment;
   ACCEPT iff p < 0.05 AND treatment_mean < baseline_mean.

## Stage 1 measurement

Workload: `rholang_bench --bench replication/basic --measurement-time 5
--warm-up-time 1 --sample-size 10` (criterion's internal sampling) under
`taskset -c 4` on AMD Ryzen Threadripper PRO 5975WX. `perf record` with
frame-pointer call-graph (DWARF rejected by kernel for BRS on this CPU,
per `[[f13-baseline-2026-05-20]]`). Total samples: 13 932.

**AST-clone-attributable cycles:**

| Function | % of total |
|----------|-----------:|
| `rholang::clone_iterative` (trampolined AST clone engine) | 0.29 % |
| `rholang::clone_handle_proc` | 0.19 % |
| `core::ptr::drop_in_place::<rholang::Proc>` | 0.12 % |
| `rholang::clone_handle_name` | 0.09 % |
| `rholang::Proc::clone` (entry-point dispatch) | 0.09 % |
| **Total AST clone + drop** | **≈ 0.78 %** |

**For comparison, the actual hot functions:**

| Function | % of total |
|----------|-----------:|
| `libm::exp` (criterion's Gaussian-KDE statistical analysis, OUT of bench scope) | 13.38 % |
| `core::hash::sip::Sip13Rounds::write` (HashMap operations) | 8.09 % |
| `WpdaWalker::apply_action_to_cursor` | 2.29 % |
| `WpdaWalker::step_fanout` | 2.11 % |
| `WpdaWalker::BranchCursor::clone` (NOT user AST — walker cursor state) | 0.90 % |
| `Arc<Vec<u32>>::clone_from_ref_in` (token kinds vector — independent of #112) | 0.41 % |

## Verdict

**FALSIFIED.** AST clone consumes 0.78 % of total runtime in the
rewrite-heaviest benchmark in the workspace. That is **~13× below** the
Plan agent's 10 % gate, and **~25× below** the 20 % gate for the full
Stage 2 effort.

Even under the optimistic upper bound — that converting Box to Arc
eliminates **100 %** of those 0.78 % cycles — the maximum achievable
speedup is < 0.78 % wall-clock. With a measurement floor of ~1 % per
Criterion's intra-sample variance, a < 0.78 % effect is statistically
indistinguishable from noise. Welch's t-test on N=15+15 would not be
able to detect it.

The hypothesis is therefore not just unmotivated; it is **not testable**
on the rholang workload. Running Stage 2 would consume 15-18 hours of
implementation work and produce a null t-test result — wasting both the
implementation budget and the gauntlet's signal-to-noise capacity.

## What IS the bottleneck?

The two largest non-statistical-overhead consumers are:

1. **Hash operations (8.09 %).** SipHash-13 is the standard but
   relatively slow HashMap hasher. The Stage 2.3.7 FxHash swap addressed
   this at the parser dedup sites; downstream HashMap operations in the
   Ascent rewrite engine (`DualIndexedRel`, the cohort caches) still use
   default hashers. If a future hotspot demands attention, switching
   ascent-side HashMaps to FxHash is a more promising hypothesis than
   #112 — but should itself be motivated by a more targeted profile.

2. **WpdaWalker::apply_action_to_cursor + step_fanout (4.40 % combined).**
   These are the walker's hot loop. The cohort-cache work (H12 Stage 1.6,
   Task #117) has already addressed the dispatch and recovery axes. The
   remaining cost is structural (cursor state mutation + GSS traversal).
   Further reductions are research-grade, not refactor-grade.

## Recommendation

Close Task #112. Re-open only if a future profiling run on a different
workload (one where AST clone genuinely dominates — e.g., a workload that
forces many distinct rule firings on small terms with high arity) shows
AST clone ≥ 10 % of total runtime. The H4-prime hypothesis is sound in
the abstract; it just doesn't apply to the workloads we have today.

## Outcome (the experimental ledger)

| Stage | Status | Duration |
|-------|--------|---------:|
| Plan agent design | done | 1 h |
| Stage 1 gate (this document) | FALSIFIED | 1 h |
| Stage 2 (Box→Arc + Welch's t-test) | **NOT EXECUTED** (gate failed) | 0 h |
| **Total effort** | **2 h** | (vs 17-20 h if Stage 2 had proceeded) |

This is a successful application of the user's "approach scientifically
with Welch's t-test" mandate: the cheap gate caught an unmotivated
hypothesis before the expensive implementation began. The Welch's t-test
was never required because the hypothesis failed the more fundamental
falsifiability gate (is the targeted quantity even significant?).
