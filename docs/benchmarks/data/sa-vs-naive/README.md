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

## 1. The workload matrix

| workload | sizes (full) | columns | expected firings | drive |
|---|---|---|---|---|
| `lambda_chain` | 4, 8, 16, 32, 64 | `sa` + `naive` | n | per-step ROOT β redex on BOTH matchers, n steps to NF, each step on a fresh counting runtime fed by the previous step's OBSERVED reduct (the B2 discipline; locate-all fails closed on n ≥ 2 — B0) |
| `swap_comb` | 1, 2, 4, 8, 16, 32, 64 | `sa` + `naive` | m | ONE locate-all call vs ONE naive comprehension call; m pairwise-distinct `Swap` redexes under an inert right comb |
| `swap_small` | 1 … 8 | `sa` + `naive` | 1 | both drivers on a single `Swap` under k − 1 inert wrappers — the crossover floor |
| `wrap_swap_ctx` | 1 | `sa` + `naive` | 1 | both CONTEXTUAL drivers on `Wrap(Swap(A, B))`; depth 2 FAILS CLOSED on both emitters (pinned by unit test), so the ladder is exactly {1} |
| `nested_spine` | 2, 4, 8, 16 | `naive` + `replay` | k | naive in-Rho comprehension vs the production host-σ REPLAY fallback (host-computed σ fired as ground accept-send COMMs) — the honest comparison in the fail-closed regime |

AC characterization is SCOPED OUT of the head-to-head (the naive Appendix-A
scheme is positional-only; see the module rustdoc in
`benches/support/workloads.rs`).

Naive guard encodings: `pattern-guard` (default, safe everywhere) and
`consume-test` (single-candidate subjects only: `swap_small`, `lambda_chain`,
`wrap_swap_ctx`, `swap_comb` m = 1; the driver and bench refuse the rest).

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

All other cells — including every smoke cell and the n = 32/64 single-
injection cells (width > 256, always the `split_short` branch) — stay clear
of the zone. Measurable `lambda_chain` coverage is therefore the FULL ladder
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
export RUST_MIN_STACK=8388608          # also set by .cargo/config.toml [env]

# Record (the driver also embeds all of this in its run-header line):
git rev-parse HEAD
hostname
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor   # RECORD the governor;
                                                            # do NOT change it.
grep Cpus_allowed_list /proc/self/status
```

Hardware baseline: `/home/dylon/.claude/hardware-specifications.md`.

* CPU affinity: run every measurement under `taskset -c 0-7` (8 pinned cores).
* Memory bound: run every cargo invocation under
  `systemd-run --user --scope -q -p MemoryMax=28G` (NEVER `TasksMax`).
* If the recorded governor is not `performance`, RECORD that fact in the run
  notes and proceed — the protocol never modifies machine state.

## 3. Build (once, before measuring)

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
systemd-run --user --scope -q -p MemoryMax=28G \
  env RUST_MIN_STACK=8388608 \
  cargo build --release -p rholang-runtime \
    --features "bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime" \
    --bin bench_sa_vs_naive_driver

systemd-run --user --scope -q -p MemoryMax=28G \
  env RUST_MIN_STACK=8388608 \
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
whole-workspace freshness check — minutes per invocation on this workspace;
`RUST_MIN_STACK` must be exported because `.cargo/config.toml [env]` does not
apply off-cargo):

```bash
cd /home/dylon/Workspace/f1r3fly.io/mettail-rust
DATE=$(date +%F)
OUT=docs/benchmarks/data/sa-vs-naive/$DATE/driver
mkdir -p "$OUT"
REPS=30
DRIVER=target/release/bench_sa_vs_naive_driver
export RUST_MIN_STACK=8388608

run() { # workload matcher n [encoding]
  local w=$1 m=$2 n=$3 enc=${4:-pattern-guard} suffix=""
  [ "$m" = naive ] && [ "$enc" != pattern-guard ] && suffix="_${enc}"
  systemd-run --user --scope -q -p MemoryMax=28G \
    env RUST_MIN_STACK=8388608 \
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

# The consume-test encoding on its admitted single-candidate cells:
for n in 4 8 16 32 64;      do run lambda_chain naive "$n" consume-test; done
for n in 1 2 3 4 5 6 7 8;   do run swap_small   naive "$n" consume-test; done
run wrap_swap_ctx naive 1 consume-test
run swap_comb     naive 1 consume-test
```

Cell accounting: 10 + 14 + 16 + 2 + 8 pattern-guard + 15 consume-test = 65
driver invocations; at `REPS=30` that is 1 950 measured reps (the 144-cell
pre-registered protocol adds the criterion warm/cold wall matrix of §6 —
2 matchers × warm/cold over the size ladders — on top of these counter cells).

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
systemd-run --user --scope -q -p MemoryMax=28G \
  env RUST_MIN_STACK=8388608 \
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
as a CONFIRMED/REFUTED verdict — see the finding below.

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

## 9. Acceptance gates for a protocol execution

1. `env.txt` recorded; governor state noted (recorded, not changed).
2. Zero `"dnf":true` lines (`csv/dnf_audit.csv` empty).
3. Every cell has ≥ 30 accepted reps (driver) / 30 samples (criterion).
4. The per-rep verification (observed ≡ expected multiset) held everywhere —
   guaranteed by gate 2, since a mismatch emits a dnf line.
5. Comparisons follow the repo's optimization discipline (paired t-test on
   matched cells before any claim).
