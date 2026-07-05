# Rho-Native Baseline Benchmarks (Epic 9 #2053)

> Baseline established 2026-07-05. Scientific ledger for the pre-optimization state
> of the rho-native surface — the reference every Epic 9 optimization (#2054–2061)
> and the #2005–2007 in-Rho matching optimization must be measured against, per the
> benchmark-before-optimize discipline.

## Methodology

| Axis | Value |
|---|---|
| CPU | AMD Ryzen Threadripper PRO 5975WX, 32 cores / 4 CCDs (8 cores/CCD), base ~3.6 GHz |
| Governor | `performance` (all cores at max frequency) |
| Affinity | pinned to CCD0 (`taskset -c 0-7` + `AllowedCPUs=0-7`) to avoid cross-CCD latency |
| Harness | criterion 0.5, 100 samples, 3 s warm-up |
| Build | release, sibling target dir, `systemd-run` memory-capped |
| Bench | `languages/benches/rho_native_bench.rs` (`cargo bench -p languages --bench rho_native_bench`) |

The pre-existing `languages/benches/*` and `prattail/benches/*` cover **parser
generation + parsing**; this bench adds the previously-uncovered **Dovetail
saturation** (D-stage) and **RhoNet lowering** (F-stage artifact) — the campaign's
core surface.

## Baselines

### Dovetail saturation — `<Lang>::dovetail_report_for` (Calculator, max_iters=64, max_nodes=100k)

| Input | Median | 95% CI |
|---|---|---|
| `add` = `1 + 2` | **2.40 ms** | [2.389, 2.406] ms |
| `nested` = `(2 + 3) * (4 - 1)` | **119.07 µs** | [118.58, 119.55] µs |
| `deep` = `((1+2)*(3+4)) - ((5-1)*(2+2))` | **535.05 µs** | [531.29, 539.90] µs |

### RhoNet lowering — `RhoNetProgram::from_language_def(...).lower_to_par(...)`

| Language | Median | 95% CI |
|---|---|---|
| `swapdemo` (4 ctors + 1 base rewrite) | **16.07 µs** | [16.009, 16.130] µs |
| `calculator` (large: numeric folds + casts + collections) | **4.99 ms** | [4.977, 5.000] ms |

## Observations (hypotheses for Epic 9)

1. **Trivial-term saturation anomaly (⚠).** `1 + 2` saturates in **2.40 ms** — ~20× SLOWER
   than the structurally larger `nested` (119 µs) and ~4.5× slower than `deep` (535 µs).
   A trivial term should be the *cheapest*, so this inverts expectation. Hypothesis:
   `1 + 2` triggers a numeric-fold path (integer coercion / BigInt) whose per-call
   fixed cost dominates, or a one-time e-graph/lazy-init cost the first-run bench
   absorbs. **This is the highest-value Epic 9 #2054/#2056 investigation target** —
   profile with `perf record --call-graph lbr` before optimizing.
2. **RhoNet lowering scales with language size.** SwapDemo (16 µs) vs Calculator
   (5 ms) is ~310×; Calculator lowering re-derives the full rule set, channels, RHS
   templates, and casts each call. #2056 ("avoid repeated pattern cloning and rule
   compilation") targets exactly this — the `CompiledRuleSet` reuse (proven in
   `PositionalSetAutomatonSound.v` `reuse_is_per_node_deterministic`) should be
   verified to apply on the RhoNet lowering path too.

## Coverage vs #2053 scope

| Area | Baseline |
|---|---|
| parser generation, parsing | `languages/benches/*`, `prattail/benches/*` (pre-existing) |
| Dovetail saturation | **this ledger** (`dovetail_saturation/*`) |
| RhoNet planning / Rho `Par` generation | **this ledger** (`rho_net_lowering/*`) |
| Dovetail extraction | folded into `dovetail_report_for` (saturation + extraction) |
| Rho runtime execution, REPL exec / step | gap — needs a runtime bench driving `PlannedRhoBackend` (a Rho machine spin-up per iter; deferred to a runtime-bench slice, tracked under Epic 9) |
