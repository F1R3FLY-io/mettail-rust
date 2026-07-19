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

## Profile — `dovetail_saturation/add` (perf, dwarf call-graph, 1999 Hz, CCD0)

Self-time (`perf report --sort=overhead,symbol`), captured 2026-07-05:

| Symbol | Self % |
|---|---|
| `dovetail::wta::compute_inside_closed` (WTA inside weights) | 12.1 |
| `RandomState::hash_one::<EClassId>` + `Sip13 Hasher::write` | **~16.2** (9.8 + 6.4) |
| `EGraph::nodes` | 6.1 |
| `Extractor::compose` + `Extractor::kth_raw` | 8.2 |
| `dovetail::scc::tarjan_sccs` | 3.6 |
| `malloc` + `cfree` | 6.3 |
| `SetAutomaton::search_egraph` | 3.0 |
| `hashbrown … reserve_rehash` (EClassId set) | 1.9 |
| `CalculatorDovetailOp::clone` | 1.6 |

**Bottleneck #1 (actionable, safe): `EClassId` hashing uses the default `RandomState`
(SipHash-1-3) — ~16% of saturation.** `EClassId` is a small-integer newtype used as an
internal e-graph key; it needs no DoS resistance. Switching the e-graph's
`EClassId`-keyed maps/sets to a fast integer hasher (FxHash / `BuildHasherDefault`) is
the classic Rust win. **Hypothesis: FxHash cuts ≥10% off saturation wall-time with zero
behavior change; gate with a t-test (criterion `--baseline`).**

**Bottleneck #2 (deeper): WTA inside-weight (12%) + extraction (8%) + node iteration
(6%) dominate the rest** — consistent with the `1+2` result value being re-cast into
many numeric e-classes (Int/UInt/Float/BigInt/BigRat/Fixed) that the weighting +
extractor then traverse. This is the demand-gated-saturation / cast-explosion axis
(#2054/#2055) — larger, separate change.

## Optimization O1 — FxHash for e-graph keys (APPLIED, 2026-07-05)

**Hypothesis (from Bottleneck #1):** replacing the default `RandomState` (SipHash-1-3)
with FxHash on the e-graph's `EClassId`/`ENode` keys cuts ≥10 % off saturation
wall-time with zero behavior change.

**Change:** added an inline FxHasher (`dovetail/src/hash.rs`, no new dependency —
dovetail keeps `rigail` as its only external dep) and pointed the e-graph, extractor,
WTA, SCC, set-automaton, and rules maps/sets at it (`crate::hash::{HashMap, HashSet}`).

**Result (criterion `--baseline`, same rig, t-test):**

| Benchmark | SipHash | FxHash | Δ | p |
|---|---|---|---|---|
| `dovetail_saturation/add` | 2.40 ms | **1.456 ms** | **−40.0 %** | 0.00 |
| `dovetail_saturation/nested` | 119.1 µs | **83.2 µs** | **−30.0 %** | 0.00 |
| `dovetail_saturation/deep` | 535.1 µs | **401.1 µs** | **−24.7 %** | 0.00 |
| `rho_net_lowering/swapdemo` | 16.07 µs | 16.30 µs | +0.1 % | 0.80 (no change) |
| `rho_net_lowering/calculator` | 4.99 ms | 4.98 ms | −0.1 % | 0.49 (no change) |

**Verdict: CONFIRMED and exceeds hypothesis** — 24–40 % faster saturation, all p < 0.05;
the two lowering benches (which never touch e-graph hashing) are statistically
unchanged, confirming the win is targeted and side-effect-free. Correctness: all 113
`dovetail` tests pass (including the positional-oracle property test), so hash-order
independence holds — the swap changes only speed, not results.

## Post-merge profile shift (2026-07-07)

A branch merge (primary WPDA-parser tree → this tree) integrated new Calculator
cross-category numeric-cast rules, INVERTING the profile: `add` 1.46 ms→297 µs
(faster), `nested` 83 µs→**2.53 ms** (+2925 % regression), `deep` ~unchanged.
Evidence-based root cause: the new rules make each literal parse in all 6 numeric
categories, so an expression lowers to a **combinatorial forest of equivalent
typed-parse roots** (nested = 65 classes/25 roots; `(2+3)+(4+1)` = 130/80; the *larger*
`deep` collapses to Int-only 15/6 because its top `-` prunes the cross-category chain).
Two factors: **(A)** the ambiguity forest = parser domain (fix #1, requested —
demand-gate cross-category injection, preserving the display→parse roundtrip); **(B)**
per-root extraction recompute = engine domain (O2/O3).

## Optimization O2 — reuse the extractor across roots (APPLIED, commit `bbc05217`)

The report path (`macros/.../typed_report.rs`) built a **fresh `Extractor` per root**,
so `funded_best` re-ran `compute_inside_closed` (O(classes) fixpoint + SCC + Newton)
once per root, discarding the memo — an O(roots) multiplier. Fix: hoist the extractor
out of all three per-root `funded_best` loops (main report / reconstruct / alternatives).
**Result (t-test p<0.05):** add −16.7 %, nested −27.9 %, deep −23.6 %. 3563 tests pass.

## Optimization O3 — reuse the composed derivation at pop (APPLIED)

Post-O2 perf: `Extractor::compose` = **23.4 %** self-time. `make_candidate` computed the
full `(op, w, key, children)` for heap ordering but **discarded op+children**;
`build_derivation` recomposed the whole thing at pop — every popped candidate composed
**twice** (redundant fraction → ½). The self-time is the `ContentKey` build (key-byte Vec
alloc + order-preserving byte-doubling + `from_bytes` box). Fix (Plan-agent designed):
build the full `Rc<Derivation>` in `make_candidate` (compose-free — it already computes
op+children) and reuse it at pop via `Rc::clone`, deleting `OrdKey` + `build_derivation`
— **zero extra w/key memory** (they move into the derivation). O3b: FxHash for the
report-projection root-dedup set (residual SipHash). **Result (t-test p<0.05):** add
−12.4 %, nested −16.3 %, deep −10.3 %. Extraction **byte-identical**: 125 dovetail tests
pass incl. `prop_extractor_matches_bruteforce_acyclic_oracle` (full ordered
`(weight, key, op)` sequence vs a brute-force oracle over 256 random e-graphs).

## Cumulative on the post-merge `nested` regression

O2 (−28 %) then O3 (−16 %) = **−39 % engine-side** (2.53 ms → 1.55 ms), extraction
oracle-verified. The residual (still ~18× the pre-merge 83 µs) is the ambiguity **forest
itself** — the parser-side fix #1 (demand-gate cross-category injection), not an engine
cost. Engine-side generic wins to date: **O1** (FxHash keys), **O2** (extractor reuse),
**O3** (composed-derivation reuse) — all benefit every language, zero parser code.

## Coverage vs #2053 scope

| Area | Baseline |
|---|---|
| parser generation, parsing | `languages/benches/*`, `prattail/benches/*` (pre-existing) |
| Dovetail saturation | **this ledger** (`dovetail_saturation/*`) |
| RhoNet planning / Rho `Par` generation | **this ledger** (`rho_net_lowering/*`) |
| Dovetail extraction | folded into `dovetail_report_for` (saturation + extraction) |
| Rho runtime execution, REPL exec / step | Rho runtime execution: **covered** by the Track B matcher head-to-head — 86 driver cells × 33 reps + criterion warm/cold matrices on the live counting `RhoRuntime` ([set-automaton-vs-naive.md](set-automaton-vs-naive.md), pgmcp experiment 144); REPL exec / step remains open (Epic 9) |
