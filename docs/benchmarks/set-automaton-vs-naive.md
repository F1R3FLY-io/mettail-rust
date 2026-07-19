# Set Automaton vs Naive KT Appendix-A — Track B Verdict Report

> Protocol executed 2026-07-19 (pgmcp experiment 144,
> `set-automaton-vs-naive-kt-appendix-a-in-rho-matching-efficiency`).
> Scientific ledger for the pre-registered efficiency gate on the in-Rho
> matcher: the optimized set-automaton receiver network vs the Knotted-Topoi
> Appendix-A naive per-location scheme, measured on the live counting
> f1r3node `RhoRuntime`. Companion narrative: [29 §5 — the efficiency
> gate](../architecture/rho-native-integration/29-knotted-topoi-satisfaction-crosswalk.md);
> theory: [21 — set-automata optimization
> theory](../architecture/rho-native-integration/21-set-automata-optimization-theory.md)
> (§7.3 the interner as the Erkens–Groote specialization, §8 the AC boundary,
> §10 where the WHY-tier sits).

## 1. Verdict summary

The question is the USER's efficiency gate (recorded verbatim in experiment
144 before any measurement): "The purpose of targetting the set automata for
pattern matching is to make it more efficient than the pure Rholang proposal
in the Knotted Topoi paper. If it is not more efficient then we should not
target it."

The answer, in three sentences. **First**, on matcher-attributable work the
two schemes are not merely close — the runtime counters (`matching_tau`,
`attempts`, `successes`, `firing_visible`, `subst_tau`,
`consumed_cost_units`) are **exactly equal, with zero rep-to-rep variance, at
every cell of every workload both matchers can run**, because the naive
emitter's soundness envelope (`OverlappingTagDemand`: pairwise-distinct rule
roots, no root op below the root) admits exactly the rulesets in which every
once-published spread message has at most one candidate reader — the admitted
naive scheme is *itself symbol-once* under the once-published spread.
**Second**, on wall-clock the automaton is statistically indistinguishable
from naive everywhere within the pre-registered 5% practical-equivalence
margin — per-cell ratios 0.951–1.026 on the $`\lambda`$/swap/contextual
ladders, log-log exponents CI-overlapping — *except* on the multi-rule
`multi_rule_shared` family, where the automaton column is 7.6%–31.4% slower
(mean ratio 1.076 at $`r=2,s=1`$ growing monotonically with $`r`$ to 1.314 at
$`r=8,s=3`$; every cell beyond the margin at BH
$`q \le 1.5\times 10^{-14}`$), the price of the per-site drive statically
replicating the full $`r`$-case network at each of the $`r`$ sites.
**Third**, the pre-approved exploratory persistent-fire probe (R3, the
self-driving naive column) wins every matching-work counter — sessions
$`n \to 1`$, `matching_tau` from $`\tfrac{3n^2+11n}{2}`$ down to exactly
$`7n`$, injected bytes 26× smaller, interpreter-charged cost ~20% lower — and
still **loses wall-clock ~1.7× at scale** (52.36 s vs 30.87 s at $`n=64`$),
because its $`2n^2-1`$ re-spread volume serializes through persistent-contract
dispatches on the single session's critical path.

Mechanical outcome under the pre-registered rule, and the decision record:
§9. In one line: W1 (the counter-exponent leg) is unsatisfiable given exact
counter equality, W2 (the wall-clock leg) holds on its swap/contextual family
but the multi-rule family is sa-worse beyond the margin, so the frozen
"naive wins or ties everywhere" clause fires and the rule outputs **retarget
the in-Rho matcher to the naive per-location scheme within its sound
envelope** — with the engineering decision resting with the protocol owner,
and a keep-list that survives either way.

## 2. Pre-registration and amendments

The provenance chain, in order:

1. **Registration before code.** pgmcp experiment 144
   (`set-automaton-vs-naive-kt-appendix-a-in-rho-matching-efficiency`,
   project `mettail-rust`) was opened and its criterion **locked at
   2026-07-18T20:09:57Z** — 48 minutes *before* the first Track B emitter
   commit (`73f07cb0`, the B0 admission-matrix audit + B1 naive Appendix-A
   emitter, 2026-07-18T20:57:47Z). Primary metric:
   `matcher_attributable_inspections_per_normalization` (loc:/cap: COMM count
   + RSpace match attempts + installed-receiver count); predicted direction:
   decrease (automaton below naive); registered test: Welch t,
   $`\alpha = 0.05`$, one-tailed, minimum effect Cohen's $`d = 0.5`$,
   Benjamini–Hochberg correction across cells; planned $`n = 30`$ replicates.
2. **The frozen verdict rule** (quoted from the registration): "the automaton
   WINS iff (W1) the fitted log-log exponent on matcher-attributable
   inspections is strictly better (CI-separated) on the λ-chain workload (i)
   and the nested multi-candidate workload (vi, naive-vs-host-replay), AND
   (W2) warm-mode wall-clock is not worse beyond a 5% margin (one-sided Welch
   t-test, α=0.05) at practical sizes n≤8 on workloads (ii) wide locate-all,
   (iv) small SwapDemo, (v) contextual. Report crossover n\* per workload. If
   naive wins or ties everywhere: retarget to the pure scheme (remove locator
   network; KEEP admission gating, σ-receiver channels, subst TRS,
   AC/contextual paths, interner as compile-time tc(K)/O3 analysis). Split
   verdict: automaton stays with regimes documented." The registration also
   pre-declared the honest-measurement framing (§8, threat 1), the two guard
   encodings (PatternGuard headline, ConsumeTest paper-literal secondary),
   R3 as a *labeled exploratory*, the AC scope-out, and DNFs-as-data.
3. **Smoke refutation 1** (commit `ad1c0bc5`, B6 smoke, 2026-07-19T00:07Z):
   on every single-rule root drive the two columns are COMM-count-identical
   — the registered $`\tau`$-divergence hypothesis is refuted in that
   workload shape ("corpus amendment pending user call" recorded in the
   commit).
4. **USER-approved amendment (a) — workload (vii).** The corpus amendment
   adds `multi_rule_shared`, the multi-rule pattern-set family the automaton
   was designed for, held inside *both* admission gates, and retargets the W1
   exponent leg at it (the "amended-W1" prediction: naive counter cost grows
   with $`r`$; sa stays $`O(\text{subject})`$). Implemented exactly as
   registered in commit `e56bb208` — which then **refuted the amended leg
   too, with a mechanism** (§6).
5. **USER-approved amendment (b) — the split_byte unlock.** A pre-existing
   f1r3node panic (`Blake2b512Random::split_byte(i8)` overflow for parallel
   eval widths in [129, 256]) had fail-closed 9 ladder cells. Fixed upstream
   on the f1r3node-rust-mettail branch `fix/split-byte-width-range` (commit
   `31b354e6`: widths 129..=256 route to `split_short`; widths ≤ 128
   byte-identical; the commit carries the Scala-divergence review and
   consensus note — the split id feeds unforgeable-name derivation, so the
   fix lives only on that branch pending review). Commit `94e05252` then
   flipped the harness hazard machinery to regression assertions
   (`in_split_regression_zone` provenance flag, `catch_unwind` kept), so the
   full $`\lambda`$-chain ladder $`n \in \{4,\dots,64\}`$ became measurable.
6. **No-weakening disposition.** Both refuted signal checks were kept, as
   pre-registered, and disposed as *measured verdicts + equality regression
   pins*: smoke assertion 6 prints the measured REFUTED verdict with its
   numbers, and the driver-bin test was renamed
   `multi_rule_shared_counters_are_equal_the_amended_w1_refutation` — a
   counter divergence in *either* direction now fails the build, citing
   experiment 144.
7. **R3** (commit `64e6783c`) ran as the pre-approved exploratory column
   after the primary dataset was frozen (`1ed4feec`), on its own dated
   directory with its own binary anchor.

## 3. Environment and protocol

Sources: `data/sa-vs-naive/2026-07-19/{header.json,env.txt,WARNINGS.md,sanity.txt}`
and `data/sa-vs-naive/2026-07-19-r3/{header.json,sanity.txt}`. Hardware
baseline: `/home/dylon/.claude/hardware-specifications.md`.

| Axis | Value |
|---|---|
| CPU | AMD Ryzen Threadripper PRO 5975WX (Zen 3, 32c/4 CCDs), governor `performance` on all pinned cores, `amd-pstate-epp` active, boost on |
| Affinity | `taskset -c 0-7` (CCD0) on every measured invocation |
| Memory bound | `systemd-run --user --scope -q -p MemoryMax=28G`, `RUST_MIN_STACK=8388608` |
| OS / toolchain | Linux 7.1.3-arch2-2, rustc 1.99.0-nightly (eff8269f7 2026-07-18), release build |
| Tree | branch `feature/rho-native-set-automata`; primary data at `5c985622`; R3 base `1ed4feec` (R3 code uncommitted at run time by instruction; landed as `64e6783c`) |
| Binary anchors | driver sha256 `cc3cf970…251293de`; pinned criterion bench binary sha256 `e519ebc2…4ef3db697`; R3 driver sha256 `50d46278…c9c038be` |
| Counter protocol | 86 cells × 33 reps (3 warm-up + 30 measured; post-hoc `"warmup":true` marking), fresh counting runtime per rep, 60 s per-rep timeout + 8 MiB emitted-program guard as structured DNF lines |
| Wall protocol | criterion, 30 samples / 5 s warm-up per cell (CLI override), warm (emission+build+inj+readback) and cold (adds compile+bring-up) matrices; pattern-guard pass + consume-test pass |
| Statistics (B7) | Welch t per cell on the driver's 30 measured `inj_ns` samples; one-sided 5%-margin test; BH within family; log-log exponent fits (`csv/b7_*.csv`) |
| Acceptance | **0 DNF lines** (`csv/dnf_audit.csv` empty); observed ≡ expected multiset on every rep; **zero rep-to-rep counter variance in every cell** (deterministic seed confirmed; `sanity.txt`) |

Cell accounting (`csv/cell_accounting.csv`): 70 pattern-guard + 16
consume-test = 86 cells, each 3/30 warm-up/measured, zero DNF anywhere —
the README's 83-cell accounting plus the registry-admitted `lambda_chain`
$`n=2`$ smoke-size extension (sa, naive/pattern-guard, naive/consume-test).
R3 adds 6 exploratory cells (§5.6) at the same 33-rep discipline.

Two provenance notes are on record in `WARNINGS.md`, neither affecting
measurement validity:

- **HEAD spread under a concurrent agent.** Branch HEAD moved during the run
  window (Track C documentation commits, e.g. `b87a9779`); every moved commit
  is docs-only —
  `git diff --name-only e56bb208..5c985622 -- rholang-runtime/` is empty — so
  the harness compiled into the measurement binaries is byte-identical to the
  task-pinned `e56bb208`. The stable anchors are the binary sha256 values
  above (the driver embeds `git_sha` per invocation at cell start, so
  per-cell jsonl headers record whichever docs-only HEAD was current).
- **Criterion rc=101 rebuild incident.** The first `cold/lambda_chain`
  criterion invocation died *inside cargo's freshness rebuild* (a concurrent
  agent's uncommitted, non-compiling edits to shared upstream crates); zero
  measurements were taken by the failed invocation. The chunk was re-run, and
  every remaining criterion chunk invoked the already-built bench binary
  directly (`SA_VS_NAIVE_BENCH_BIN` mode), pinned by sha256 — every criterion
  sample in the run comes from that one binary.

Data locations follow the size-class split in
`data/sa-vs-naive/2026-07-19/ARCHIVED.md`: lean record in git (headers, env,
warnings, sanity, per-cell medians, B7 analysis CSVs, cell accounting); full
per-replicate samples in pgmcp experiment 144 (arms `sa` / `naive` /
`replay` / `naive-r3`, samples unit-keyed by (n, encoding, rep)); bulk
per-cell jsonl, flat per-rep CSVs, zstd-archived criterion trees, and run
logs on disk untracked (pgmcp-indexed).

## 4. Corpus — the workload families

Seven families were registered, (i)–(vii); six generate cells. Full
definitions: `data/sa-vs-naive/README.md` §1 and the module rustdoc of
`rholang-runtime/benches/support/workloads.rs`. Every subject is
deterministic by construction with a directly-computed expected-firings
ground truth verified on every rep.

| # | Workload | Sizes | Columns | What it exercises |
|---|---|---|---|---|
| (i) | `lambda_chain` | 2\*, 4, 8, 16, 32, 64 | sa + naive | per-step ROOT $`\beta`$ redex on both matchers, $`n`$ steps to NF, each step on a fresh counting runtime fed by the previous step's observed reduct |
| (ii) | `swap_comb` | 1–64 | sa + naive | ONE locate-all call vs ONE naive comprehension call over $`m`$ pairwise-distinct `Swap` redexes under an inert comb |
| (iii) | AC characterization | — | — | **scoped out**: the naive Appendix-A scheme is positional-only (no bag clause), so an AC workload has no naive column; AC-carrier COMM traffic stays classified (`ac_carrier` counter) so an accidental AC excursion would be visible |
| (iv) | `swap_small` | 1–8 | sa + naive | a single `Swap` under $`k-1`$ inert wrappers — the crossover floor |
| (v) | `wrap_swap_ctx` | 1 | sa + naive | both contextual drivers; depth 2 fails closed on *both* emitters (pinned), so the ladder is exactly {1} |
| (vi) | `nested_spine` | 2–16 | naive + replay | naive in-Rho comprehension vs the production host-$`\sigma`$ replay — the honest head-to-head in the automaton's fail-closed regime |
| (vii) | `multi_rule_shared` | $`n = 100r+s`$, $`r \in \{2,4,8\} \times s \in \{1,2,3\}`$ | sa + naive | the amended-W1 pattern-set regime: $`r`$ rules $`R_i(S^s(x)) \Rightarrow x`$ with pairwise-distinct roots and ONE shared non-root chain |

\* the $`n = 2`$ cells are the registry-admitted smoke-size extension.

Admission constraints (all pinned by unit tests):

- `lambda_chain` $`n \ge 2`$ and `nested_spine` $`k \ge 2`$ fail closed on
  the one-call locate-all (`AutomatonUnsupported::NestedEntryMultiSite`) —
  hence the per-step root drive for (i) and the replay column for (vi).
- `multi_rule_shared` $`r \ge 2`$ likewise fails closed on the ONE-call
  locate-all because the `NestedEntryMultiSite` gate counts candidate sites
  **across entries** (`sites.len() > 1 && !ruleset_all_entries_flat`), not
  per entry. The sa column keeps the automaton via the per-rule drive at
  admitted sites: the full $`r`$-entry interned network installed at each of
  the $`r`$ comb-leaf sites over ONE spread (contention-free for this family:
  sites pairwise non-ancestral, no rule root op at any non-root position —
  both pinned).
- Naive admission (`NaiveKtUnsupported::OverlappingTagDemand`): pairwise
  distinct roots, shared op $`S`$ no rule's root — (vii) is deliberately the
  closest both-columns-admitted approach to the sharing regime.
- `consume-test` (the paper-literal guard encoding) is admitted only on
  single-candidate subjects: `swap_small` (all $`k`$), `lambda_chain`,
  `wrap_swap_ctx`, `swap_comb` $`m=1`$, `multi_rule_shared` $`r=1`$.
- R3's scope is a single column: `lambda_chain` / `naive-r3` /
  pattern-guard-only, $`n \in \{2,\dots,64\}`$ (typed CLI rejection
  elsewhere).

## 5. Results per workload

### 5.1 Counter equality — stated once, with the mechanism

Across **every** cell of every family both matchers can run — (i), (ii),
(iv), (v), (vii); all sizes; both naive encodings — the six runtime counters
`matching_tau`, `firing_visible`, `subst_tau`, `attempts`, `successes`, and
`consumed_cost_units` are **exactly equal between sa and naive**, with zero
rep-to-rep variance (B7 `counter_inequality_cells = []`; `sanity.txt`). This
is not a tie within noise; it is a deterministic identity, measured with
certainty. Mechanism (§6): the sound-naive envelope is symbol-once under the
once-published spread. The only per-cell divergences anywhere are *static*:
`program_encoded_len` and `program_receiver_count` (§5.4). Consequently the
per-workload tables below carry wall-clock and static columns; the counters
appear only where a capability split makes them differ ((vi), R3).

### 5.2 `lambda_chain` — the per-step β ladder

Median injection wall (30 measured reps; `summary_medians.csv`), Welch on
per-rep means (`csv/b7_welch_cells.csv`, sa vs naive/pattern-guard):

| $`n`$ | sa (ms) | naive-pg (ms) | naive-ct (ms) | mean ratio sa/naive | two-sided $`p`$ | one-sided $`p`$(sa >5% worse) |
|---|---|---|---|---|---|---|
| 2 | 8.13 | 8.10 | 8.33 | 0.9974 | 0.42 | ≈ 1.0 |
| 4 | 21.83 | 21.63 | 22.29 | 1.0111 | 1.3e-11 | 1.0 |
| 8 | 74.06 | 74.37 | 75.70 | 0.9968 | 3.8e-3 | 1.0 |
| 16 | 360.57 | 365.65 | 372.43 | 0.9899 | 9.0e-6 | 1.0 |
| 32 | 2679.75 | 2773.75 | 2789.66 | 0.9719 | 1.1e-10 | 1.0 |
| 64 | 30869.71 | 30978.29 | 30603.69 | 0.9910 | 0.23 | ≈ 1.0 |

Individual cells reach two-sided significance in *both* directions with
small effects (−2.8% to +1.1%); nothing approaches the 5% margin, and no
crossover $`n^\*`$ exists. The fitted log-log wall exponents (slope ± 95% CI,
$`R^2`$; `b7_analysis` on the median ladder) are CI-overlapping:

| Ladder | sa | naive | $`R^2`$ (sa / naive) |
|---|---|---|---|
| `lambda_chain` | 2.359 ± 0.385 | 2.366 ± 0.381 | 0.973 / 0.974 |
| `swap_comb` | 1.789 ± 0.267 | 1.787 ± 0.277 | 0.972 / 0.970 |
| `swap_small` | 0.917 ± 0.128 | 0.909 ± 0.135 | 0.971 / 0.967 |

The ≈ 2.36 exponent on the chain is the pre-registered per-invocation
framing showing up as predicted: both schemes pay $`\Theta(n^2)`$ total
spread sends when an $`n`$-step chain is driven per-step, so the wall
exponent carries the spread volume, not a matcher difference (§8, threat 1).

### 5.3 The W2 family — `swap_comb`, `swap_small`, `wrap_swap_ctx`

The pre-registered W2 family is the 13 cells at practical sizes
$`n \le 8`$ on (ii)/(iv)/(v). One-sided 5%-margin Welch with BH across the
family (`csv/b7_w2_family.csv`): **zero cells sa-worse beyond margin** —
every $`\text{BH } q = 1.0`$ (every raw one-sided $`p \ge 0.999998`$). Mean
ratios sa/naive span 0.951–1.013 inside the family; sa is nominally *faster*
in 12 of 13 cells. Median walls (ms) at the family edges: `swap_small`
$`k=1`$ 0.769 vs 0.792, $`k=8`$ 5.089 vs 5.207; `swap_comb` $`m=8`$ 11.55
vs 11.70; `wrap_swap_ctx` 1.329 vs 1.337. **W2 HOLDS.**

The `swap_comb` ladder continues beyond the registered family without a
crossover: $`m=16`$ ratio 1.026 (two-sided $`p = 4.3\times 10^{-3}`$, within
margin), $`m=32`$ 0.986, $`m=64`$ 0.969 — sa slightly faster again at the
top. Consume-test, the paper-literal secondary encoding, tracked
pattern-guard closely everywhere it is admitted (e.g. `swap_small` $`k=8`$
median 5.215 ms vs 5.207 ms) and had no registered statistics of its own.

### 5.4 `multi_rule_shared` — the one wall-clock separation

All nine cells (`csv/b7_mrs_family.csv`; means over 30 reps; static columns
are deterministic, so median = value):

| $`n`$ ($`r,s`$) | sa (ms) | naive (ms) | ratio | BH $`q`$ (sa worse >5%) | encoded len sa/naive (B) | receivers sa/naive |
|---|---|---|---|---|---|---|
| 201 (2,1) | 2.098 | 1.951 | 1.076 | 4.3e-27 | 3 115 / 2 455 | 17 / 13 |
| 202 (2,2) | 2.925 | 2.679 | 1.092 | 1.0e-34 | 4 209 / 3 225 | 23 / 17 |
| 203 (2,3) | 3.928 | 3.483 | 1.128 | 2.3e-35 | 5 351 / 4 035 | 29 / 21 |
| 401 (4,1) | 5.387 | 4.737 | 1.137 | 1.1e-17 | 9 282 / 5 832 | 51 / 27 |
| 402 (4,2) | 7.444 | 6.313 | 1.179 | 1.3e-17 | 12 678 / 7 547 | 71 / 35 |
| 403 (4,3) | 9.883 | 8.619 | 1.147 | 1.5e-14 | 16 202 / 9 342 | 91 / 43 |
| 801 (8,1) | 15.289 | 12.891 | 1.186 | 1.1e-17 | 31 040 / 14 192 | 167 / 55 |
| 802 (8,2) | 22.474 | 17.590 | 1.278 | 2.7e-25 | 43 272 / 18 223 | 239 / 71 |
| 803 (8,3) | 29.106 | 22.148 | 1.314 | 2.1e-33 | 55 880 / 22 413 | 311 / 87 |

**All nine cells are sa-worse beyond the 5% margin**
($`q \le 1.5\times 10^{-14}`$, Cohen's $`d`$ 4.2–17.6), the ratio growing
with $`r`$ (1.08 → 1.31) — while the *runtime counters remain exactly equal*
(§5.1). The wall gap follows the static gap: under the
`NestedEntryMultiSite`-forced per-site drive, the sa column installs the full
$`r`$-case network at each of the $`r`$ sites, so its emitted program grows
from 1.27× naive's at $`r=2`$ to 2.49× at $`r=8`$ (receivers 311 vs 87 at
$`r=8,s=3`$), and the interpreter pays for evaluating and installing that
static replication. Compile-time interning is real in the same cells —
$`r+s+1 = 12`$ automaton states vs the per-rule sum $`r(s+2) = 40`$ at
$`r=8,s=3`$, asserted by `multi_rule_shared_state_sharing_is_real` — but the
current runtime encoding does not transport it to the wire (§6). No
crossover: sa-worse-beyond-margin already at the smallest cell.

### 5.5 `nested_spine` — naive in-Rho vs production host-σ replay

The automaton fails closed here (multi-candidate $`\lambda`$-spine), so this
is the capability column: what in-Rho *matching itself* costs relative to the
production fallback that fires host-computed $`\sigma`$ as ground
accept-send COMMs. Medians:

| $`k`$ | naive $`\tau`$/attempts/cost | replay $`\tau`$/attempts/cost | naive (ms) | replay (ms) | ratio |
|---|---|---|---|---|---|
| 2 | 11 / 15 / 38 | 0 / 2 / 6 | 1.98 | 0.25 | 8.0 |
| 4 | 23 / 33 / 80 | 0 / 4 / 12 | 4.78 | 0.48 | 10.0 |
| 8 | 47 / 69 / 164 | 0 / 8 / 24 | 13.22 | 1.10 | 12.0 |
| 16 | 95 / 141 / 332 | 0 / 16 / 48 | 48.53 | 3.30 | 14.7 |

The registered W1 leg on this workload is degenerate in replay's favor by
construction — replay does *zero* in-Rho matching ($`\tau = 0`$ identically)
— so it cannot show the automaton counter-better either.

### 5.6 R3 — the persistent-fire probe (pre-approved exploratory)

R3 deviates from the same-firing contract **by design**: a fired naive
receiver routes its reduct (computed by the real in-Rho subst TRS) to a
`^respread` reserved-receiver family that re-walks and re-emits the spread
*in-session*, so a chain normalizes in ONE injection (sessions $`n \to 1`$;
the reduct is delivered to the in-session walker family, not OUT). Every rep
verifies the observed OUT value in-drive against the same terminal-NF ground
truth the per-step column uses; 6 cells × 33 reps, 0 DNF, one counter
profile per cell (`2026-07-19-r3/sanity.txt`). Closed forms, exact at every
ladder point (per-step form fitted exactly over all six sizes; R3 forms
verified per rep in sanity):

```math
\tau_{\text{match}}^{\text{per-step}}(n) = \tfrac{3n^2 + 11n}{2},
\qquad
\tau_{\text{match}}^{\text{R3}}(n) = 7n,
\qquad
\tau_{\text{respread}}^{\text{R3}}(n) = 2n^2 - 1,
\qquad
\tau_{\text{subst}}(n) = 3n \ \text{(both regimes)}.
```

From `2026-07-19-r3/comparison.md` (medians; wall ratio vs the sa column):

| $`n`$ | $`\tau_{\text{match}}`$ per-step / R3 | respread per-step / R3 | consumed | attempts | encoded (B) | receivers | wall sa / naive-pg / R3 (ms) | R3/sa |
|---|---|---|---|---|---|---|---|---|
| 2 | 17 / 14 | 0 / 7 | 85 / 78 | 33 / 35 | 23 347 / 15 440 | 49 / 28 | 8.13 / 8.10 / 8.19 | 1.01 |
| 4 | 46 / 28 | 0 / 31 | 230 / 194 | 86 / 87 | 53 752 / 19 066 | 110 / 34 | 21.83 / 21.63 / 23.95 | 1.10 |
| 8 | 140 / 56 | 0 / 127 | 700 / 570 | 252 / 239 | 138 846 / 27 486 | 268 / 46 | 74.06 / 74.37 / 105.66 | 1.43 |
| 16 | 472 / 112 | 0 / 511 | 2 360 / 1 898 | 824 / 735 | 427 839 / 48 959 | 728 / 70 | 360.57 / 365.65 / 608.62 | 1.69 |
| 32 | 1 712 / 224 | 0 / 2 047 | 8 560 / 6 858 | 2 928 / 2 495 | 1 658 915 / 111 063 | 2 224 / 118 | 2 679.75 / 2 773.75 / 4 646.87 | 1.73 |
| 64 | 6 496 / 448 | 0 / 8 191 | 32 480 / 25 994 | 10 976 / 9 087 | 8 126 035 / 309 175 | 7 520 / 214 | 30 869.71 / 30 978.29 / 52 361.30 | 1.70 |

The inversion: R3 wins **every matching-work counter** — 14.5× fewer
matching COMMs at $`n=64`$, ~20% lower interpreter-charged cost, 26× smaller
injected program, 35× fewer receivers — and the per-step columns even pay
$`n`$ runtime bring-ups per rep *outside* these timers where R3 pays one.
Yet R3 **loses wall-clock**: parity at $`n \le 4`$, 1.43× at $`n=8`$, ~1.7×
at $`n \ge 16`$ (52.36 s vs 30.87 s at $`n=64`$). The measured account is
that the $`2n^2-1`$ re-spread volume runs on the single session's critical
path as persistent-contract dispatches, where the per-step columns evaluate
their (equally quadratic) spread volume as bulk sends per injection; the
finer attribution is hypothesis-grade (§8, threat 5).

## 6. The two refutations, with the mechanism

This section is load-bearing: both pre-registered divergence predictions were
measured, refuted, and *explained*, and the explanations were pinned as
regression tests.

**Refutation 1 — single-rule equality** (commit `ad1c0bc5`, B6 smoke). On
every root-restricted single-rule drive — `lambda_chain`
$`n \in \{2,4,8\}`$, `swap_comb`, `swap_small`, `wrap_swap_ctx` — the
optimized and naive columns agree exactly on every runtime counter (e.g.
$`n = 2`$: $`\tau`$ 17 = 17, attempts 33 = 33); only `program_encoded_len`
differs slightly. With one rule, the per-site naive receiver and the
automaton network do the same work; the same-CLTS theorem
(`same_clts_weak_bisim`, presupposed and enforced empirically by the 42/42
fired-multiset equivalence gate run before any measurement) promises a
difference only in erased $`\tau`$ *structure*, never $`\tau`$ *count* — and
the counters confirmed it.

**Refutation 2 — multi-rule distinct-root equality** (commit `e56bb208`,
workload (vii)). The amended-W1 prediction expected the naive counter cost to
grow like $`O(r \cdot \text{subject-overlap})`$ against the automaton's
$`O(\text{subject})`$. Measured: **exact counter equality at every
$`(r,s)`$ cell** — ratio 1.000, flat in both knobs. The mechanism is an
envelope theorem, not a measurement accident:

> Any ruleset the naive `OverlappingTagDemand` gate *admits* has
> pairwise-distinct roots with no root op at any non-root position. Under the
> once-published linear spread ABI, that means every spread message has **at
> most one candidate reader** on the naive side — the admitted naive scheme
> is *itself symbol-once*, per-site COMM-identical to the automaton network
> (both collect their schedule through the same
> `collect_nested_schedule`). The regime where set-automaton sharing would
> pay at runtime — several rules inspecting one subject position, i.e.
> shared roots / overlapping demands — is exactly the regime where the naive
> baseline is **unsound and fails closed**: duplicated inspection under one
> linear spread mis-consumes rather than merely slowing down.

Where sharing *pays*, naive cannot run; where naive *runs*, its envelope
already forces symbol-once work. That conjunction is why the counter legs
could never separate, in either the original or the amended form.

**The compile-time reality, and why it does not reach the wire.** The
interner's sharing is real: the combined automaton for (vii) interns
$`r+s+1`$ states against the per-rule sum $`r(s+2)`$ — 12 vs 40 at
$`r=8,s=3`$ (doc 21 §7.1–§7.3: the interned DAG is the Erkens–Groote
match-goal automaton partially evaluated to the sub-pattern quotient, size
independent of inspection order). But the current *per-site drive* re-emits
the full network at every admitted site, so the runtime encoding runs in the
automaton's disfavor — static size 1.27×→2.49× naive's as $`r`$ grows, and
the multi-rule wall gap of §5.4 follows it. The sharing exists at compile
time and is destroyed by per-site replication on the way to the wire.

## 7. Capability splits

The landscape splits by capability, and each regime got its honest
comparison:

- **Nested multi-candidate subjects** (a $`\lambda`$-spine with
  $`k \ge 2`$ head-matching sites): the optimized locate-all fails closed
  (`AutomatonUnsupported::NestedEntryMultiSite`), so the in-Rho matcher there
  is naive-only and the production behavior is host-$`\sigma`$ replay.
  §5.5 measures the in-Rho-matching price itself: $`\tau`$ 11 vs 0, attempts
  15 vs 2, cost 38 vs 6 at $`k=2`$; wall 8×→14.7× replay's.
- **Shared-root pattern sets**: automaton-only in principle — the naive gate
  fails closed (unsound there, §6) while the automaton's O3 accept fan-out
  handles overlapping demands. No runtime head-to-head *can* exist, and the
  regime is **empty in the current corpus**: no bundled language's positional
  ruleset has shared roots today (the B6 finding's "needs multi-RULE root
  sharing, which no bundled demo language exercises").
- **AC patterns** bypass the positional machinery entirely on both sides
  (doc 21 §8: `compile_structural` rejects `AcApp`; the AC fragment fires as
  one atomic multiset consume on its own budget-accounted path, shared by
  both schemes) — scoped out of the head-to-head by registration.

## 8. Threats to validity

1. **Per-invocation architecture scope (pre-registered).** Both schemes pay
   $`\Theta(n^2)`$ total spread sends over an $`n`$-step chain driven
   per-step, so wall exponents (~2.36 on the chain) carry spread volume, not
   matcher structure; the registration therefore carried the asymptotic claim
   on matcher-attributable inspections, and those turned out exactly equal.
   A persistent/amortized architecture is a different regime — R3 probed it
   and §9 schedules the rest.
2. **Corpus scale and shape.** The workloads are demo-scale languages built
   for attribution, not production programs. Production languages are larger,
   but their positional (non-AC) rulesets are distinct-rooted today, so the
   measured envelope — where naive is admitted at all — is the envelope that
   exists in the shipped corpus; a future shared-root positional ruleset
   would land in the automaton-only regime with no naive comparator.
3. **Single hardware/OS/interpreter.** One machine (Threadripper PRO 5975WX,
   CCD0-pinned), one kernel, one rustc nightly, one f1r3node build (with the
   `fix/split-byte-width-range` routing; the zone cells are flagged
   `in_split_regression_zone` for provenance). No cross-machine replication.
4. **HEAD spread during the run.** Concurrent docs-only commits moved HEAD
   under the executor; validity rests on the recorded binary sha256 anchors
   and the empty harness diff (`WARNINGS.md`), not on a frozen branch.
5. **R3's wall-gap attribution is hypothesis-grade.** The measured facts are
   the counter inversion and the 1.7× wall loss; the *account* — critical-path
   serialization of the $`2n^2-1`$ re-spread through persistent-contract
   dispatches vs bulk-evaluated per-injection spreads, with possible
   contributions from RSpace contention on the walker family and lost
   per-step bulk-evaluation parallelism — was not perf-profiled and remains
   a set of hypotheses for the E-1/A-S5 follow-ups.
6. **Consume-test is secondary.** The paper-literal encoding ran only on its
   admitted single-candidate cells and carried no registered statistics; its
   medians tracked pattern-guard closely, so the headline conclusions do not
   depend on the guard-encoding choice.

## 9. Verdict under the pre-registered rule, and the decision record

**Mechanical evaluation of the frozen rule.**

- **W1 (counter-exponent leg): unsatisfiable.** On the original leg
  ((i) + (vi)) and on the USER-amended leg ((vii)), the matcher-attributable
  inspection counters are *exactly equal* wherever both matchers run (and
  (vi)'s replay side does no in-Rho matching at all), with zero variance —
  there is no exponent separation to fit and no CI to separate. The effect is
  exactly zero, measured with certainty.
- **W2 (wall-clock leg): holds on its family; fails outside it.** Zero of
  the 13 registered swap/contextual cells at $`n \le 8`$ are sa-worse beyond
  the 5% margin (all BH $`q = 1.0`$). The same one-sided test on the
  multi-rule family finds sa worse beyond the margin at **all nine cells**
  ($`q \le 1.5\times 10^{-14}`$, ratio 1.076→1.314 growing with $`r`$).
- **Crossover $`n^\*`$:** none on any sa-vs-naive ladder (no cell beyond the
  margin outside (vii); (vii) is beyond the margin from its smallest cell).

The automaton therefore does not WIN (W1 ∧ W2 is unsatisfiable), and the
data select the frozen "**naive wins or ties everywhere**" branch: counters
tie exactly everywhere, wall ties within margin on every swap/λ ladder, and
naive wins beyond margin on the whole multi-rule family. That clause's
pre-registered output is:

> **Retarget the in-Rho matcher to the naive per-location scheme within its
> sound (`OverlappingTagDemand`) envelope** — removing the serialized locator
> network (the loc:/cap: locator plumbing) and its per-site static
> replication, which are exactly what the multi-rule family showed being
> paid for without a counter return.

**Decision record.** Experiment 144's formal decision (result 194, decided
2026-07-19T06:16:41Z) records the primary hypothesis **inconclusive** in the
engine's typing (test\_type `none`: a Welch t cannot run on a deterministic
zero-variance effect) with the operator note recording what that means
scientifically: the predicted decrease is *refuted with a mechanism*, the
secondary axes are as above, and **the engineering retarget decision under
the USER's efficiency gate is escalated to the protocol owner with the
complete evidence pack**. This report is that pack's verdict document: it
states the rule's mechanical output; the decision rests with the user.

> **Decision (2026-07-19, protocol owner).** Keep **both** strategies. The set-automaton
> network remains the production in-Rho matcher (the campaign proceeds on it), and the naive
> per-location emitter remains maintained under the `bench-naive-baseline` feature as the
> measured, sound-envelope alternative. The pre-registered rule's mechanical output (retarget)
> is explicitly **not adopted at this time**; the retention is **experiment-contingent** — the
> scheduled E-6a PathMap subject indexing (which targets the exact per-site static-replication
> penalty behind the automaton's only measured loss), E-1 scion grafting on the persistent
> regime, and the post-A-S5 in-Rho-driver rematch are the paths expected to supply the
> automaton's edge. If they do not, this decision is revisited against this same evidence pack.

**The keep-list — regardless of the decision** (pre-registered in the same
clause, restated by the decision record):

- the **compile-time interner** as the $`tc(K)`$/O3 channel-naming and
  admission *analysis* (the zero-admission O1/O2/O3 theory of doc 21 is
  about the naming quotient, not about any runtime network);
- the **admission gating** on both sides (`NestedEntryMultiSite`,
  `OverlappingTagDemand`) — the soundness fences the refutation mechanism
  runs through;
- the **σ-receiver / firing contracts** and the **de-Bruijn subst TRS**
  (matcher-indifferent by the same-CLTS theorem);
- the **AC and contextual paths** (their own optimality regimes, untouched
  by this comparison);
- the **automaton as the only in-Rho option for any shared-root positional
  ruleset** — the O3 accept fan-out capability naive cannot host (§7);
  retargeting the *default* matcher does not delete the capability.

What retargeting would remove: the serialized locator network and the
per-site replication of the installed automaton — the two artifacts the data
showed costing wall time (§5.4) while buying no counter (§5.1).

**Three scheduled forward paths could re-open the question**, and are
recorded as such rather than folded into the verdict:

1. **E-6a — PathMap subject indexing**: spread a subject as one `EPathMap`
   value with site enumeration by prefix-restricted zipper queries on the
   machine — this would carry the compile-time sharing into the runtime
   encoding and could dissolve the `NestedEntryMultiSite` fail-close that
   forced the per-site drive (doc 29 §5's path-machine reading; scheduled
   first after this verdict).
2. **E-1 — scion grafting** (Erkens thesis, ch. 6): per-state canned send
   bundles target exactly the re-spread cost that made R3 lose wall-clock in
   the persistent regime.
3. **The post-A-S5 rematch**: re-run the R3-style persistent comparison
   against the in-Rho automaton driver once enforcement stage A-S5 lands the
   in-Rho quiescence driver (the pre-registration marks R3 exploratory for
   precisely this reason).

## 10. Reproduction

- **Protocol (verbatim executor):** `data/sa-vs-naive/full.sh` — phases
  `driver` (86 cells × 33 reps, one jsonl per cell), `criterion`
  (pattern-guard, 30 samples / 5 s warm-up), `criterion-ct` (consume-test
  pass), `post` (jq → CSV), `sanity`. Plumbing/signal validation:
  `data/sa-vs-naive/smoke.sh`. Both require the quarantined feature set
  `bench-naive-baseline swap-demo-runtime lambda-demo-runtime
  ctx-demo-runtime` (absent from every default build) and run under
  `systemd-run --user --scope -q -p MemoryMax=28G env
  RUST_MIN_STACK=8388608 taskset -c 0-7`.
- **Targets:** driver bin `bench_sa_vs_naive_driver`
  (`--workload W --matcher {sa,naive,replay,naive-r3} --encoding
  {pattern-guard,consume-test} --n N --reps 33 --format json-lines`);
  criterion bench `bench_sa_vs_naive` (`--sample-size 30 --warm-up-time 5`;
  `SA_VS_NAIVE_BENCH_BIN` to pin a prebuilt binary). Shared generators:
  `rholang-runtime/benches/support/workloads.rs`. R3 column: the same driver
  with `--matcher naive-r3` (`lambda_chain`/pattern-guard only), landed in
  commit `64e6783c`.
- **Analysis:** the B7 statistics of §5 are the committed
  `data/sa-vs-naive/2026-07-19/csv/b7_{welch_cells,w2_family,mrs_family}.csv`
  (Welch per cell on the 30 measured `inj_ns` samples, one-sided 5%-margin
  tests, BH per family, log-log fits).
- **Data locations** (per `data/sa-vs-naive/2026-07-19/ARCHIVED.md`): lean
  record in git; full per-replicate samples in pgmcp experiment 144
  (`set-automaton-vs-naive-kt-appendix-a-in-rho-matching-efficiency`; arms
  `sa` / `naive` / `replay` / `naive-r3`); bulk jsonl/CSV/criterion-tarballs
  on disk untracked, pgmcp-indexed.
- **Upstream dependency:** f1r3node-rust-mettail branch
  `fix/split-byte-width-range` (commit `31b354e6`) — required for the cells
  whose parallel eval width falls in [129, 256]; the run headers flag those
  cells via `in_split_regression_zone`.
