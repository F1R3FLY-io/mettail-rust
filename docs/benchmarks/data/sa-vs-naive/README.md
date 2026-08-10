# sa-vs-naive — the Track-B naive-baseline head-to-head: run protocol and data layout

This directory holds the measurement DATA and the exact, executable RUN
PROTOCOL for the Track-B benchmark comparing the OPTIMIZED set-automaton
in-Rho matcher against the NAIVE Knotted-Topoi Appendix-A baseline (and, in
the fail-closed regime, the production host-σ REPLAY fallback) on the live
in-memory counting f1r3node `RhoRuntime`.

Everything below is meant to be executed VERBATIM by the run orchestrator.
The harness itself lives in `rholang-runtime`:

| artifact | path | registration |
|---|---|---|
| workload generators + per-rep drive (shared module) | `rholang-runtime/benches/support/workloads.rs` | compiled into both targets below |
| criterion wall-clock bench | `rholang-runtime/benches/bench_sa_vs_naive.rs` | `[[bench]] name = "bench_sa_vs_naive"`, `harness = false` |
| JSON-lines counter driver | `rholang-runtime/src/bin/bench_sa_vs_naive_driver.rs` | `[[bin]] name = "bench_sa_vs_naive_driver"` |
| smoke validation | `docs/benchmarks/data/sa-vs-naive/smoke.sh` | this directory |

Both targets require the quarantined feature set

```
--features "bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime"
```

and are ABSENT from every default build (`required-features` gating; the
`bench-naive-baseline` feature carries no production metering/budget surface —
the bench-local secondary cost read inside `bench_support` is the only cost
touch).

## Run-record index — the committed measurements in this directory

| directory | what | pgmcp experiment | mettail commit | one-line verdict |
|---|---|---|---|---|
| `2026-07-19/` | the Track-B protocol execution of this README (full 83-cell counter + criterion matrix; data placement per its `ARCHIVED.md`) | 144 | `1ed4feec` | sa-vs-naive runtime counters EQUAL on every admitted cell (the §8 findings, incl. the amended-W1 refutation-with-mechanism); the static installed network + wall are the discriminators |
| `2026-07-19-r3/` | R3 follow-up — the self-driving (persistent-fire) naive single-session column vs the frozen per-step columns on `lambda_chain` | 144 | `64e6783c` | counters won (fewer matching COMMs per chain), wall-clock lost (n = 8: 105.66 vs 74.06 ms) |
| `2026-07-19-e6a/` | **E-6a** — PathMap-backed subject indexing for in-Rho matching, vs the spread+drive control | 145 | `87faea85` | primary CONFIRMED (6.8–18.6× fewer spread+matching COMMs; `NestedEntryMultiSite` DISSOLVED) but treatment inj wall 2.54×–39.70× SLOWER — the f1r3node per-call trie-rebuild artifact |
| `2026-07-19-e6a-postfix/` | E-6a re-measure after the f1r3node trie-cache fix (`84a0fbe4`) | 145 | `06e1d9f0` | counters byte-identical; wall does NOT flip (band → 2.44×–37.33×); residual root-caused to by-value EPathMap transport → spawned the EPathMap value-handling fix |
| `2026-07-20-e6d1/` | **E-6d #1** — E-6a re-measure after EPM P0–P2 (intern store + chain fusion, `351e494d`) | 148 | `c631c051` | counters byte-identical; swap16 **4.31×** / nested16 **3.97×** vs postfix (all completed cells 1.90×–4.31×); band → 1.30×–8.34×; new #1 cost = the P1 digest pipeline |
| `2026-07-20-e6d2/` | **E-6d #2** — final re-measure after the FULL stack (P3 wrapper + P4 transport, `ead2f152`) | 149 | `7b4d5663` | counters byte-identical to ALL THREE baselines; further **1.43×/1.34×**, cumulative **6.15×/5.34×**; band → 1.19×–6.35×; residual = the ≈45 ms/inj ps-deep-copy floor (the L2 junction, user decision) |
| `2026-07-20-e6d3/` | **E-6d #3** — the L2 falsification re-measure (shared-`ps` `SharedPars`, `131aecee`) | 150 | `e8bc939c` | counters byte-identical to ALL FOUR baselines; **attribution CONFIRMED** — boxed `to_vec` 44.83 → 5.38 ms/inj (−88.0%); further **4.73×/4.89×**, cumulative **29.10×/26.12×**; band → **0.79×–1.37×** (treatment FASTER than control on 4/9); residual = digest ≈15.0 > clone ≈10.4 > drop ≈5.2 ms/inj → the USER-owned byte-array protobuf effort |

The five E-6a/E-6d records (rows 3–7) form the EPathMap-fix measurement arc —
CLOSED 2026-07-20 by the E-6d #3 confirmed verdict — against the
f1r3node-rust-mettail stack `31b354e6` (split-byte routing) →
`84a0fbe4` (trie-cache) → `602144bd` (P0 parity harness) → `c3d5b3f2` (P1
intern store) → `351e494d` (P2 chain fusion) → `4e422b6b` (P3 wrapper) →
`60aaa02e`/`6c0a90cb`/`ead2f152` (P4.1–P4.3 transport/matcher/hashing) →
`131aecee` (L2 shared-`ps` SharedPars), on
branch `fix/epathmap-value-handling` == `feature/mettail` (fast-forward
merge-back 2026-07-20, re-applied after L2). The per-commit consensus
analysis, Scala-divergence flags, gate inventory, and the upstream review
checklist live in the f1r3node review packet:
`f1r3node docs/epathmap-value-handling-review.md` (§12 carries the L2 entry
and the E-6d #3 verdict).

## 1. The workload matrix

| workload | sizes (full) | columns | expected firings | drive |
|---|---|---|---|---|
| `lambda_chain` | 4, 8, 16, 32, 64 | `sa` + `naive` | n | per-step ROOT β redex on BOTH matchers, n steps to NF, each step on a fresh counting runtime fed by the previous step's OBSERVED reduct (the B2 discipline; locate-all fails closed on n ≥ 2 — B0) |
| `swap_comb` | 1, 2, 4, 8, 16, 32, 64 | `sa` + `naive` | m | ONE locate-all call vs ONE naive comprehension call; m pairwise-distinct `Swap` redexes under an inert right comb |
| `swap_small` | 1 … 8 | `sa` + `naive` | 1 | both drivers on a single `Swap` under k − 1 inert wrappers — the crossover floor |
| `wrap_swap_ctx` | 1 | `sa` + `naive` | 1 | both CONTEXTUAL drivers on `Wrap(Swap(A, B))`; depth 2 FAILS CLOSED on both emitters (pinned by unit test), so the ladder is exactly {1} |
| `nested_spine` | 2, 4, 8, 16 | `naive` + `replay` | k | naive in-Rho comprehension vs the production host-σ REPLAY fallback (host-computed σ fired as ground accept-send COMMs) — the honest comparison in the fail-closed regime |
| `multi_rule_shared` | 201, 202, 203, 401, 402, 403, 801, 802, 803 (`n = 100·r + s`) | `sa` + `naive` | r | the AMENDED-W1 multi-rule pattern-set regime (workload (vii)): r rules `Rᵢ(Sˢ(x))` with pairwise-DISTINCT roots and ONE SHARED non-root sub-pattern chain, over an r-redex inert comb `Rᵢ(Sˢ(Kᵢ))`; sa = the per-rule drive at admitted sites (the production per-site network — ALL r entries' interned automaton — at each of the r sites over ONE spread; the ONE-call locate-all fails closed for r ≥ 2, its `NestedEntryMultiSite` gate counts candidate sites ACROSS entries) vs ONE naive Appendix-A comprehension call |

### The `multi_rule_shared` amendment (pgmcp experiment 144, amended: workload (vii))

The size parameter encodes BOTH knobs: `n = 100·r + s` with r = `n / 100`
rules and s = `n % 100` shared-`S`-chain depth (both ≥ 1); the full ladder is
the cross product r ∈ {2, 4, 8} × s ∈ {1, 2, 3} and the smoke cell is n = 402
(r = 4, s = 2). The family is the pattern-SET sharing regime the set automaton
was designed for, held inside BOTH admission gates: the roots are pairwise
distinct and the shared op `S` is no rule's root (so the naive
`OverlappingTagDemand` gate admits), and the sa column drives per-rule at
admitted sites (each site is exactly the admitted nested-ruleset ≤ 1-site
install; the r comb-leaf sites are pairwise non-ancestral and no root op
occurs non-root, so the co-install is contention-free — both facts pinned by
driver-bin unit tests). Compile-time sharing is REAL and asserted:
`state_count = r + s + 1` for the combined automaton vs the per-rule sum
`r·(s + 2)`.

**Pre-registered amended-W1 prediction:** per-cell `matching_tau` and
`attempts` scale ~O(subject) on the sa column but ~O(r · subject-overlap) on
the naive column, so the naive/sa ratio grows with r (and with s at fixed r).
The smoke HARD-asserts the signal exists at r = 4, s = 2 (assertion 6); per
the amendment protocol a failure is a REFUTATION that must surface with its
numbers, never a reason to weaken the assertion. See the dated FINDING
addendum in §8 for the measured outcome.

AC characterization is SCOPED OUT of the head-to-head (the naive Appendix-A
scheme is positional-only; see the module rustdoc in
`benches/support/workloads.rs`).

Naive guard encodings: `pattern-guard` (default, safe everywhere) and
`consume-test` (single-candidate subjects only: `swap_small`, `lambda_chain`,
`wrap_swap_ctx`, `swap_comb` m = 1, `multi_rule_shared` r = 1; the driver and
bench refuse the rest).

### FIXED — the formerly-panicking f1r3node `split_byte(i8)` zone [129, 256]

`DebruijnInterpreter::eval` splits its per-term random by the 0-based term
index; the OLD branch sent every Par whose top-level term list had 2 ..= 256
entries to `split_byte(id.try_into().unwrap())`
(`f1r3node rholang/src/rust/interpreter/reduce.rs`), but
`Blake2b512Random::split_byte` takes an `i8`
(`crypto/src/rust/hash/blake2b512_random.rs:97`) — so a term index ≥ 128
panicked with `TryFromIntError(PosOverflow)`: every parallel eval width in
**[129, 256]** crashed, per eval level, per injection. FIXED on the
f1r3node-rust-mettail branch `fix/split-byte-width-range` (commit `31b354e6`,
the working tree this repository path-depends on): the branch boundary moved
from `> 256` to `> 128`, so widths in [129, 256] join the `split_short(i16)`
path used by every larger width, while widths ≤ 128 keep byte-identical
`split_byte` randomness (the consensus-relevant defined range is untouched; a
`split_short` child appends two domain-separation path bytes where a
`split_byte` child appends one, so the rerouted range cannot collide with any
defined `split_byte` output — see the fix commit message for the full
argument and the Scala-divergence review note).

The harness no longer gates on the zone: the fail-closed
`interpreter-split-hazard` DNF and the criterion skip are RETIRED, and every
formerly-gated cell now RUNS. The offline width probe remains as PROVENANCE —
the driver's run header records `max_eval_width` plus
`in_split_regression_zone` (replacing the retired `interpreter_split_hazard`
flag) so analysis can tell which results depend on the fixed routing — and
the per-rep `catch_unwind` panic guard remains as belt-and-suspenders. The
in-zone pattern-guard cells are EXACTLY (pinned by the
`interpreter_split_regression_zone_cells_are_pinned_and_smoke_cells_are_clear`
unit test, with the `interpreter_split_regression_width_129_evaluates`
actual-eval spot check proving the zone evaluates; per-step chain width is
`10 + 9·links`, so every chain n ≥ 14 passes through the zone at its
14-to-27-links-remaining steps, widths 136–253):

| regression-zone cell | in-zone injection width |
|---|---|
| `lambda_chain/{sa,naive}/16` | 136–154 (steps with 14–16 links left) |
| `lambda_chain/{sa,naive}/32` | 136–253 (steps with 14–27 links left) |
| `lambda_chain/{sa,naive}/64` | 136–253 (steps with 14–27 links left) |
| `swap_comb/{sa,naive}/16` | 175 |
| `nested_spine/naive/16` | 174 |

All other cells stay clear of the zone. In particular, the current R3
pattern-route PDA has maximum evaluator width 10 at every $`n \in
\{4,8,16,32,64\}`$ ladder point: it captures the chain argument directly
instead of constructing a full-subject spread. The historical R3 emitter's
n = 16 full-chain injection was in the zone, while its n = 32/64 injections
were above it; those widths are retained only in the archived run record.
Every smoke cell also remains clear. Measurable `lambda_chain` coverage is
therefore the FULL ladder
n ∈ {4, 8, 16, 32, 64} (plus the smoke n = 2). The upstream fix is
consensus-relevant (the split id feeds unforgeable-name derivation) and lives
only on that f1r3node branch — review before upstreaming further.

Every rep VERIFIES the observed OUT multiset against the workload's
directly-computed ground truth (per step for `lambda_chain`); a mismatch is a
`"dnf":true` line (driver) or a panic (criterion), never a silently-timed
wrong run.

## 2. Environment pinning (CHECK AND RECORD — do not attempt to change)

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
unset RUST_MIN_STACK                   # ordinary stacks; the workspace does not inject it

# Record (the driver also embeds all of this in its run-header line):
git rev-parse HEAD
hostname
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor   # RECORD the governor;
                                                            # do NOT change it.
grep Cpus_allowed_list /proc/self/status
```

Hardware baseline: `/home/dylon/.claude/hardware-specifications.md`.

* CPU affinity: run every measurement under `taskset -c 0-7` (8 pinned cores).
* Memory bound: run builds under
  `systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0` and measured
  binaries under the corresponding 4 GiB bound (NEVER `TasksMax`).
* If the recorded governor is not `performance`, RECORD that fact in the run
  notes and proceed — the protocol never modifies machine state.

## 3. Build (once, before measuring)

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  env -u RUST_MIN_STACK \
  cargo build --release -p rholang-runtime \
    --features "bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime" \
    --bin bench_sa_vs_naive_driver

systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  env -u RUST_MIN_STACK \
  cargo bench -p rholang-runtime \
    --features "bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime" \
    --bench bench_sa_vs_naive -- --test        # compile + list only, no measurement
```

## 4. Output layout

One dated directory per protocol execution:

```
docs/benchmarks/data/sa-vs-naive/<YYYY-MM-DD>/
├── env.txt                     # §2 records (SHA, hostname, governor, affinity)
├── driver/                     # §5 JSON-lines, one file per cell
│   └── <workload>_<matcher>[_<encoding>]_n<N>.jsonl
├── criterion/                  # §6 criterion output (copy of target/criterion)
└── csv/                        # §7 post-processed tables
    ├── driver_cells.csv
    └── driver_summary.csv
```

## 5. Counter protocol — the driver (reps ≥ 30 per the pre-registered 144-cell experiment)

One driver invocation per cell; each rep runs on a FRESH counting runtime
(fresh COMM/match counters), with the 60 s per-rep timeout and the 8 MiB
emitted-program guard producing `"dnf":true` lines instead of hangs. The first
line of every file is the self-describing run header.

Invoke the §3-built BINARY directly (a per-cell `cargo run` would re-run the
whole-workspace freshness check — minutes per invocation on this workspace).
Every invocation explicitly removes `RUST_MIN_STACK`; stack-safety gates, not
an environment-sized stack, establish the supported depth:

The frozen post-D-E5 production-SA versus persistent-R3 rematch is captured by
`post-d-e5-r3.sh`. It records three warmups and 51 measured repetitions per arm
at each of `n = 2, 4, 8, 16, 32, 64`, refuses to overwrite an existing run,
and invokes `analyze-post-d-e5-r3.py` to apply the predeclared deterministic
counter, resource, and wall-time decision gates.

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
DATE=$(date +%F)
OUT=docs/benchmarks/data/sa-vs-naive/$DATE/driver
mkdir -p "$OUT"
REPS=30
DRIVER=target/release/bench_sa_vs_naive_driver
unset RUST_MIN_STACK

run() { # workload matcher n [encoding]
  local w=$1 m=$2 n=$3 enc=${4:-pattern-guard} suffix=""
  [ "$m" = naive ] && [ "$enc" != pattern-guard ] && suffix="_${enc}"
  systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 \
    env -u RUST_MIN_STACK \
    taskset -c 0-7 \
    "$DRIVER" \
      --workload "$w" --matcher "$m" --encoding "$enc" \
      --n "$n" --reps "$REPS" --format json-lines \
      --out "$OUT/${w}_${m}${suffix}_n${n}.jsonl"
}

# The full matrix, pattern-guard:
for n in 4 8 16 32 64;      do run lambda_chain sa    "$n"; run lambda_chain naive "$n"; done
for n in 1 2 4 8 16 32 64;  do run swap_comb    sa    "$n"; run swap_comb    naive "$n"; done
for n in 1 2 3 4 5 6 7 8;   do run swap_small   sa    "$n"; run swap_small   naive "$n"; done
run wrap_swap_ctx sa 1; run wrap_swap_ctx naive 1
for n in 2 4 8 16;          do run nested_spine naive "$n"; run nested_spine replay "$n"; done
# multi_rule_shared: n = 100·r + s, r ∈ {2,4,8} × s ∈ {1,2,3} (amended W1).
for n in 201 202 203 401 402 403 801 802 803; do
  run multi_rule_shared sa "$n"; run multi_rule_shared naive "$n"
done

# The consume-test encoding on its admitted single-candidate cells:
for n in 4 8 16 32 64;      do run lambda_chain naive "$n" consume-test; done
for n in 1 2 3 4 5 6 7 8;   do run swap_small   naive "$n" consume-test; done
run wrap_swap_ctx naive 1 consume-test
run swap_comb     naive 1 consume-test
```

Cell accounting: 10 + 14 + 16 + 2 + 8 + 18 pattern-guard + 15 consume-test =
83 driver invocations; at `REPS=30` that is 2 490 measured reps (the
pre-registered 144-cell protocol — amended by workload (vii)
`multi_rule_shared`, +18 counter cells and +36 criterion warm/cold cells —
adds the criterion warm/cold wall matrix of §6 on top of these counter
cells).

## 6. Wall-clock protocol — criterion

Group naming: `warm/<workload>/<matcher>/<n>` and `cold/<workload>/<matcher>/<n>`.

* **warm** measures per iteration: per-call emission + `build` + `inj` +
  `readback` (compilation and counting-runtime bring-up are OUTSIDE the
  measured region — the B3 hoist).
* **cold** measures per iteration: `compile_workload` + runtime bring-up +
  emission + `build` + `inj` + `readback`.
* Verification/decode is never measured. Bench-top defaults are 10 samples /
  3 s warm-up; the full protocol pins 30 samples:

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
DATE=$(date +%F)
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  env -u RUST_MIN_STACK \
  taskset -c 0-7 \
  cargo bench -p rholang-runtime \
    --features "bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime" \
    --bench bench_sa_vs_naive -- --sample-size 30 --warm-up-time 5 \
  2>&1 | tee docs/benchmarks/data/sa-vs-naive/$DATE/criterion-run.log

cp -r target/criterion docs/benchmarks/data/sa-vs-naive/$DATE/criterion
```

To bench the consume-test encoding's wall times on its admitted cells, re-run
with `BENCH_SA_VS_NAIVE_ENCODING=consume-test` in the environment (non-admitted
cells are skipped with a note on stderr).

## 7. Post-processing — JSON lines → CSV (jq)

```bash
cd docs/benchmarks/data/sa-vs-naive/$DATE

# Per-rep long table.
{
  echo 'workload,matcher,encoding,n,rep,build_ns,inj_ns,readback_ns,program_encoded_len,program_receiver_count,observed_count,consumed_cost_units,matching_tau,firing_visible,subst_tau,ac_carrier,contextual_plumbing,observation,other,join_arity_gt1,attempts,successes'
  jq -r 'select(.workload and (.dnf != true)) |
    [.workload.name, .workload.matcher, .workload.encoding, .workload.n, .workload.rep,
     .build_ns, .inj_ns, .readback_ns, .program_encoded_len, .program_receiver_count,
     .observed_count, .consumed_cost_units,
     .comm.matching_tau, .comm.firing_visible, .comm.subst_tau, .comm.ac_carrier,
     .comm.contextual_plumbing, .comm.observation, .comm.other, .comm.join_arity_gt1,
     .matches.attempts, .matches.successes] | @csv' driver/*.jsonl
} > csv/driver_cells.csv

# Per-cell medians (inj wall + the discriminating counters).
{
  echo 'workload,matcher,encoding,n,reps,median_inj_ns,median_matching_tau,median_attempts,median_consumed'
  jq -rs '
    def median: sort | if length == 0 then null
      elif length % 2 == 1 then .[length/2 | floor]
      else (.[length/2 - 1] + .[length/2]) / 2 end;
    [.[] | select(.workload and (.dnf != true))]
    | group_by(.workload.name, .workload.matcher, .workload.encoding, .workload.n)[]
    | [.[0].workload.name, .[0].workload.matcher, .[0].workload.encoding, .[0].workload.n,
       length,
       ([.[].inj_ns] | median),
       ([.[].comm.matching_tau] | median),
       ([.[].matches.attempts] | median),
       ([.[].consumed_cost_units] | median)] | @csv' driver/*.jsonl
} > csv/driver_summary.csv

# DNF audit (must be empty for an accepted run).
jq -r 'select(.dnf == true) | [.workload.name, .workload.matcher, .workload.n, .reason] | @csv' \
  driver/*.jsonl > csv/dnf_audit.csv
[ -s csv/dnf_audit.csv ] && echo 'WARNING: dnf lines present — investigate before accepting the run'
```

## 8. Smoke validation (plumbing + signal, NOT measurement)

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
docs/benchmarks/data/sa-vs-naive/smoke.sh /tmp/sa-vs-naive-smoke release
```

Asserts: every line parses, zero dnf, observed counts equal ground truth on
every cell (both columns agree), and the STRUCTURAL discriminating signal —
`matching_tau`/`attempts` divergence between the `naive` (in-Rho matching)
and `replay` (host-computed σ) columns on `nested_spine`. The pre-registered
`lambda_chain` sa-vs-naive `matching_tau` hypothesis is MEASURED and reported
as a CONFIRMED/REFUTED verdict — see the finding below. Assertion 6
HARD-asserts the amended-W1 `multi_rule_shared` signal (naive `matching_tau`
> sa at r = 4, s = 2) per the amendment protocol — see the dated addendum
below for the measured outcome.

### FINDING (B6 smoke, 2026-07-18) — sa-vs-naive counter EQUALITY on single-rule root drives

On the root-restricted per-step drives with the single-rule demo languages,
the optimized and naive columns are COMM-COUNT-IDENTICAL: at `lambda_chain`
n ∈ {2, 4, 8}, `matching_tau`, `firing_visible`, `subst_tau`, `attempts`,
`successes`, `consumed_cost_units`, and the receiver counts all agree exactly
(e.g. n = 2: τ 17 = 17, attempts 33 = 33; only `program_encoded_len` differs
slightly — naive 53 392 vs sa 53 752 bytes at n = 4). The same holds for
`swap_comb`/`swap_small`/`wrap_swap_ctx` (one rule ⇒ per-site the naive
receiver and the automaton network do the same work; the same-CLTS theorem
promises a difference only in erased τ STRUCTURE, not τ count — the naive
scheme's cost blow-up needs multi-RULE root sharing, which no bundled demo
language exercises). The counter columns that DO discriminate are
`nested_spine`'s `naive` (in-Rho matching: τ 11, attempts 15, cost 38 at
k = 2) vs `replay` (host σ: τ 0, attempts 2, cost 6) — the in-Rho-matching
price itself. For the sa-vs-naive cells, the wall-clock criterion matrix and
`program_encoded_len` are therefore the primary comparators, with the
counters serving as the equality VALIDATION instrument.

### FINDING ADDENDUM (amended W1 smoke, 2026-07-18) — the `multi_rule_shared` signal assertion REFUTES across the whole ladder

The workload (vii) amendment was implemented exactly as pre-registered and
the HARD signal assertion (smoke assertion 6; the
`multi_rule_shared_signal_exists_at_smoke_cell` driver-bin unit test) was run
against the full r × s ladder (release driver, 3 reps/cell, rep 0 shown; all
reps identical — the counters are deterministic under the fixed seed):

| cell (n = 100·r + s) | `matching_tau` sa = naive | `attempts` sa = naive | `consumed` sa = naive | `program_encoded_len` sa vs naive | `program_receiver_count` sa vs naive |
|---|---|---|---|---|---|
| r=2, s=1 (201) | 11 = 11 | 15 = 15 | 38 = 38 | 3 115 vs 2 455 | 17 vs 13 |
| r=2, s=2 (202) | 15 = 15 | 19 = 19 | 48 = 48 | 4 209 vs 3 225 | 23 vs 17 |
| r=2, s=3 (203) | 19 = 19 | 23 = 23 | 58 = 58 | 5 351 vs 4 035 | 29 vs 21 |
| r=4, s=1 (401) | 23 = 23 | 33 = 33 | 80 = 80 | 9 282 vs 5 832 | 51 vs 27 |
| r=4, s=2 (402) | 31 = 31 | 41 = 41 | 100 = 100 | 12 678 vs 7 547 | 71 vs 35 |
| r=4, s=3 (403) | 39 = 39 | 49 = 49 | 120 = 120 | 16 202 vs 9 342 | 91 vs 43 |
| r=8, s=1 (801) | 47 = 47 | 69 = 69 | 164 = 164 | 31 040 vs 14 192 | 167 vs 55 |
| r=8, s=2 (802) | 63 = 63 | 85 = 85 | 204 = 204 | 43 272 vs 18 223 | 239 vs 71 |
| r=8, s=3 (803) | 79 = 79 | 101 = 101 | 244 = 244 | 55 880 vs 22 413 | 311 vs 87 |

The naive/sa runtime-counter ratio is exactly 1.000 at EVERY (r, s) — it does
not grow with r or with s. The amended-W1 prediction is REFUTED, and the
refutation has a MECHANISM, not a measurement accident: under the
once-published linear spread ABI, any ruleset the naive `OverlappingTagDemand`
gate admits has pairwise-distinct roots with no root op at any non-root
position, so every spread message has AT MOST ONE candidate reader on the
naive side — i.e. the ADMITTED naive scheme is already symbol-once, per-site
COMM-identical to the automaton network (both collect their schedule through
the SAME `collect_nested_schedule`). The regime where set-automaton sharing
would pay at runtime (several rules inspecting ONE subject position — shared
roots / overlapping demands) is exactly the regime the naive baseline cannot
host: it fails CLOSED there instead of running slowly. Duplicated inspection
under one linear spread is unsound, not slow. This extends the B6 finding
above (single-rule counter equality) to the multi-rule distinct-root regime.

What DOES discriminate on this workload, growing with r: the STATIC installed
network — the sa per-rule drive installs the full r-case per-site network at
each of the r sites (`program_encoded_len` sa/naive ≈ 1.27× at r = 2 →
2.49× at r = 8; `program_receiver_count` 311 vs 87 at r = 8, s = 3), and the
warm `inj` wall time follows it (rep 0: 37 ms sa vs 27 ms naive at n = 803).
The smoke assertion 6 and the driver-bin signal unit test are left IN PLACE
as pre-registered (they fail, loudly, with these numbers): per the amendment
protocol the refutation must keep surfacing until the protocol owner
dispositions it — do NOT weaken either assertion.

## 9. Acceptance gates for a protocol execution

1. `env.txt` recorded; governor state noted (recorded, not changed).
2. Zero `"dnf":true` lines (`csv/dnf_audit.csv` empty).
3. Every cell has ≥ 30 accepted reps (driver) / 30 samples (criterion).
4. The per-rep verification (observed ≡ expected multiset) held everywhere —
   guaranteed by gate 2, since a mismatch emits a dnf line.
5. Comparisons follow the repo's optimization discipline (paired t-test on
   matched cells before any claim).
