# E-3 construction-cost session — T-INCR W-B extension ladder (H3v2) + H1 W-A rules ladder

Session 2026-07-21 (the CLEAN run; supersedes `voided-run-1/` — see below), pgmcp
experiment 146 (`e-3-lazy-incremental-set-automaton-construction`).

* Binary: `bench_e3_construction` (release/LLVM, feature `bench-e3-construction`),
  sha256 `b1c143c13398e09939c19a6e9c74eea94426aa5f4387adf78bb631b8df71f14f`, built at git
  `5382bd7a`; window ran at git `445a9cce` (data-only commit on top — code tree identical).
* Protocol: one systemd-supervised uninterrupted window; `taskset -c 0-7`; `performance`
  governor on all 32 CPUs (verified at window open, recorded in every JSONL header);
  300 s settle; run once; `n = 30` recorded reps + 3 warmup per cell;
  `RUST_MIN_STACK=8388608`. The H3v2 equivalence gate ran BEFORE every W-B cell.
* **Window: start `2026-07-21T06:45:22Z` — end `2026-07-21T08:32:14Z`** (settle from
  `06:40:22Z`; bounds corroborated by the per-file JSONL headers' `unix_time_secs`).
* Descriptive statistics only — the pgmcp experiment ledger owns verdicts.

## Frozen-vs-default discrepancy note (REQUIRED record)

The harness's `DEFAULT_LADDER_R` is `{8, 16, 32, 64, 125, 250, 500, 750, 1000}`; the FROZEN
H1 registration names **128**, not 125. This session passed the frozen values explicitly via
`--r` (`8 16 32 64 128 250 500 750 1000`); no cell used the 125 default. The harness default
was left unchanged (a code-side default swap would have re-touched a landed surface
mid-experiment).

## Voided first attempt

`voided-run-1/` preserves the first 2026-07-21 window, ruled VOID (fragmented: the runner
was externally killed mid `e3_wb_r1000_incremental`; a detached resume completed the
remainder in a second segment). Its per-cell bytes — including its own 16/16-PASS gate
records — are kept unmodified for provenance and are NOT part of this record's numbers.

## Files

* `e3_wb_gate_r{100,250,500,1000}.jsonl` — the pre-registered H3v2 equivalence gate,
  **16/16 PASS** (per r: `base-shape`; `auto-inject-nonempty` — the EM-2 anti-vacuity case
  with `auto_injected_rewrites = 1` and `auto_entry_violations = 0`; `non-base-fallback` —
  the coordinator-pinned fail-closed congruence append, path
  `fallback:the appended rewrite carries premises`, artifacts ≡ batch; `chained-k3`).
  Components per gate line: fingerprint, state_count, deferred multiset, byte-equal
  installed Par (prost encoding), fired-set count-multisets on the shared corpus.
* `e3_wb_r{100,250,500,1000}_{incremental,full}.jsonl` — the W-B extension ladders
  (K = 50 single-rewrite appends over the `multi1`/`distinct` base; one line per append;
  30 reps + 3 warmup). Zero DNFs, zero `fell_back`, every append installed Ok.
* `e3_wb_spans_r{100,250,500,1000}.jsonl` — companion Stage-0 SELF-time span cells on the
  same base sources (the floor/ceiling share instrument).
* `e3_h1_{spans,direct}_{multi1,multi3,mixed}_r{8,16,32,64,128,250,500,750,1000}.jsonl` —
  the H1 W-A ladder, both entry modes; plus
  `e3_h1_{spans,direct}_{multi1,multi3}_r750_shared16.jsonl` (the thesis-'maa' 708-symbol
  alphabet-axis analogue).
* `e3_incr_summary.json` — descriptive medians, SELF-time shares, EM-7b top-end local
  log-log slopes (regressor `log(total pattern nodes)`, points 500→750→1000, per
  shape/mode; global fits deliberately not reported).
* `session.log` — the run's cell log, recovered from the systemd journal (the tee'd
  scratchpad copy was swept by an external cleanup; journald's burst rate-limit dropped
  ~20 of the 79 lines — the JSONL headers are the authoritative per-cell timestamps).

## Headline descriptives (medians)

W-B per-append wall (H3v2; savings = `1 − inc/full`):

| r | incremental p50 | full p50 | savings | reused-phase SELF share (floor comparand) | Par-emission SELF share |
|---|---|---|---|---|---|
| 100 | 18.99 ms | 28.67 ms | 33.8 % | 9.1 % | 88.4 % |
| 250 | 86.74 ms | 114.50 ms | 24.2 % | 4.6 % | 94.1 % |
| 500 | 320.94 ms | 373.74 ms | 14.1 % | 2.5 % | 96.8 % |
| 1000 | 1232.64 ms | 1374.89 ms | 10.3 % | 1.3 % | 98.3 % |

* The FLOOR ("incremental ≥ the reused-phase SELF-time share") holds at every r, with a
  large margin: the savings exceed the bypassed phases' SELF shares because the batch arm's
  `compile_in_rho_matching_ruleset` internally RE-RUNS the lowering pipeline for its
  injection-site/family derivations (EM-4) — the incremental bypass eliminates those
  duplicated activations too, whose time the SELF-attribution assigns to the lowering
  phases, not to the ruleset compile.
* For the same reason the naive single-pass ceiling formula `1 − Par-emission SELF share`
  (1.7 % at r = 1000) is NOT an upper bound on the measured savings in a re-entrant
  pipeline; the emission chain is paid ONCE by the incremental arm (its wall is ~98 %
  emission at r = 1000) while the batch arm pays parts of the lowering repeatedly. The
  exact ceiling composition under re-entrancy is the ledger's call (EM-4c: the
  ruleset-compile-re-lowers-everything redundancy is itself the bigger first-compile
  lever — now directly quantified: ≈ savings − reused-share ≈ 9 % of the batch wall at
  r = 1000).

H1 (per shape/mode; local log-log slope over 500→750→1000 in `log(pattern nodes)`; p50 at
r = 1000):

| mode/shape | slope (local) | p50 @ r=1000 |
|---|---|---|
| direct/multi1 | 1.232 | 0.500 ms |
| direct/multi3 | 0.898 | 0.563 ms |
| direct/mixed | 1.113 | 0.474 ms |
| spans (full pipeline)/multi1 | 1.918 | 1317.4 ms |
| spans/multi3 | 1.921 | 1325.9 ms |
| spans/mixed | 1.872 | 1298.1 ms |

* Direct `compile_structural` at r = 1000 is SUB-MILLISECOND in every shape (the F1
  "single-digit ms" prediction beaten by ~10×); the multi1 local slope point estimate
  (1.232) sits above the pre-registered 1.15 on sub-ms cells — CI treatment is the
  ledger's.
* The FULL pipeline at r = 1000 is p50 ≈ 1.30–1.33 s — between the < 1 s accept bound and
  the ≥ 10 s refute bound (the registration's split-verdict region). Phase-ranked, the
  superlinearity lives in `installed_program_par` (83.7 % SELF at r = 1000, vs 57.8 % at
  r = 100) — the Par-emission fold, not the automaton.
* r = 750 alphabet axis: `shared16` carries 8.6× the pattern nodes (19 454 vs 2 250,
  multi1) yet the full pipeline is slightly FASTER (726 vs 751 ms — 16 root ops ⇒ fewer
  constructor terms/channels) and direct construction stays sub-2 ms (1.65 vs 0.29 ms) —
  the thesis-'maa' symbol-count blowup is structurally absent in this representation.

## Anomalies (recorded)

1. The first window attempt was fragmented and voided (see `voided-run-1/VOIDED.md`); this
   clean run replaces it. Its gate also passed 16/16 — no equivalence anomaly in either run.
2. Concurrent read-only planning agents (coordinator-sanctioned) kept machine load ≈ 5–6
   during parts of both windows; cells were pinned to CPUs 0–7 and medians over 30 reps ×
   50 appends absorb scheduling noise. Not a protocol violation (recorded).
3. The scratchpad copy of the session log was swept externally after the window closed;
   `session.log` is the journal-recovered copy (partial — see Files).
