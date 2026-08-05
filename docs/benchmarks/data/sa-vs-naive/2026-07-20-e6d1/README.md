# 2026-07-20-e6d1 — E-6d #1: E-6a corpus re-measure after the EPathMap P1+P2 fix

> **Historical measurement record.** This report describes the exact 2026-07-20 implementation,
> including its set-encoded values, intern-store experiment, and retired codec cap. The current
> E-6a revalidation uses native homogeneous `PathMap<Par>` storage and the capless canonical codec.

Pre-registered pgmcp **experiment 148** (criteria FROZEN before the run). Re-run of the full
E-6a measured corpus (same workloads, seeds, 33-rep/3-warmup protocol, `taskset -c 0-7` as
`../2026-07-19-e6a/` and `../2026-07-19-e6a-postfix/`) against f1r3node-rust-mettail branch
`fix/epathmap-value-handling` @ `351e494d`:

- **P0** `602144bd` — parity harness (prost/serde/event-hash/Ord goldens + charge-KIND traces).
- **P1** `c3d5b3f2` — content-addressed EPathMap intern store (K2 digest+verify keying,
  streaming encode, eval_stable classifier).
- **P2** `351e494d` — method-chain view fusion (`try_eval_fused_method_chain` name-gated
  recognizer called first in both EMethodBody dispatch arms; charge-order replay).

Stacked on the postfix baseline's `84a0fbe4` (trie-cache) + `31b354e6`. mettail driver tree
`4608ef3a` (protocol build: `cargo build --release -p rholang-runtime --bin
bench_e6a_pathmap_driver --features bench-naive-baseline,swap-demo-runtime,lambda-demo-runtime,ctx-demo-runtime`).
Hardware: AMD Ryzen Threadripper PRO 5975WX (ASUS Workstation, Zen 3); governor
`performance` on CPUs 0-7, `scaling_driver=amd-pstate-epp`, `boost=1`, max 4561.8 MHz.

## Verdict against the frozen gates

- **(a) Counter identity: PASS.** All 15 deterministic counter columns
  ({primary, matching_comms, consumed_cost_units, program_encoded_len, attempts} ×
  {median,min,max}) byte-identical to BOTH baselines on every cell/arm; extended counters
  (spread_sends/successes/observed_count/receiver_count + all 10 `comm.*` classes) also
  identical; swap_comb 64 treatment still DNFs by the machine trie-key cap (untouched). The
  fix changed no observable semantics; the E-6a primary verdict stands unchanged.
- **(c) Primary ≥2× treatment inj: PASS.** swap_comb 16 **4.31×** (1541.572→357.969 ms) and
  nested_spine 16 **3.97×** (1315.088→331.159 ms), Welch one-sided q_BH ≈ 1e-79/3e-62; every
  completed treatment cell improved 1.90×–4.31× (all significant). The treatment/control inj
  ratio band compressed **2.44×–37.33× → 1.30×–8.34×**.
- **(b) Control neutrality: 9/10 cells within ±3.94%; ONE frozen-threshold violation as-run**
  — swap_comb 64 control +10.36% vs postfix (BH-sig). Root-caused as a machine-state
  transient, not a P1+P2 control-path regression: the run began 47 s after a 6m38s all-core
  release build; the cell ran 15–69 s into the run with a decaying within-cell trend
  (first-10 median 1606.9 → last-10 1536.7 ms; warmups 1651–1665); a labeled settled-machine
  DIAGNOSTIC re-probe of the same binary/cell (NOT part of this record) gave median
  **1417.9 ms = postfix +0.4%** (postfix 1411.8). The same cell also moved −7.2% pre-fix→
  postfix with zero control-path code changes (it was excluded from the postfix ±2.6%
  control set because its treatment DNFs). Coordinator owns the gate call.

| workload | n | postfix control→e6d1 | postfix treatment→e6d1 | improvement |
|---|---|---|---|---|
| swap_comb | 4 | 4.182→4.173 (−0.2%) | 38.333→13.298 | 2.88× |
| swap_comb | 16 | 41.294→42.923 (+3.9%) | 1541.572→357.969 | **4.31×** |
| swap_comb | 64 | 1411.759→1558.001 (+10.4%; diag 1417.9) | DNF→DNF (machine cap) | — |
| multi_rule_shared | 402 | 7.165→7.181 (+0.2%) | 65.246→21.944 | 2.97× |
| multi_rule_shared | 803 | 26.858→26.722 (−0.5%) | 567.204→150.638 | 3.77× |
| nested_spine | 2 | 1.987→1.972 (−0.7%) | 7.832→3.737 | 2.10× |
| nested_spine | 8 | 13.246→13.173 (−0.6%) | 195.893→57.373 | 3.41× |
| nested_spine | 16 | 46.445→47.360 (+2.0%) | 1315.088→331.159 | **3.97×** |
| lambda_chain | 4 | 21.847→21.586 (−1.2%) | 53.389→28.057 | 1.90× |
| lambda_chain | 8 | 74.211→74.019 (−0.3%) | 217.392→97.665 | 2.23× |

## Profile finding (perf cpu-clock, swap_comb n=16 treatment, mirrored capture)

Same flat self-time classifier as the postfix baseline (calibrated: reproduces the postfix
README's 32.4%/14.0% as 32.61%/12.75% on the saved postfix capture):

- clone-class (models `Clone::clone` + prost boxed `to_vec`): **32.61% → 24.47%** of wall;
  absolute ≈502.7 → ≈87.6 ms/inj (**5.7× less**).
- drop/free: **12.75% → 11.50%**; absolute ≈196.6 → ≈41.2 ms/inj (**4.8× less**).
- The frozen "chain-eval clone+drop < 10% of wall" check is **NOT met as a wall-share**
  (24.47+11.50 = 35.97%) because the wall itself shrank 4.31× AND a new dominant cost
  appeared: prost `encoded_len`/encode **3.34% → 20.12%** (absolute ≈51.5 → ≈72.0 ms, the
  only absolute riser) — the **P1 K2 digest pipeline itself** (`Par::encoded_len` is now the
  #1 resolved frame at 10.11%, + `ExprInstance::encoded_len` 4.97%, GUnforgeable encode fold
  3.39%, `Blake2bVarCore::compress` 1.01%). True call-path attribution is unavailable in
  BOTH captures (release binary without frame pointers: 97% of clone-class samples have zero
  resolvable ancestry; dwarf re-capture unwinds nothing) — the baseline 32.4/14.0 were the
  same global flat numbers, so the comparison above is like-for-like.

## Files

- `run.sh` / `analyze.py` — the exact protocol + analysis scripts (mirror the postfix dir).
- `comparison.md` — this run's within-run primary/secondary table; `cells.csv` — test table.
- `summary.csv`, `driver/*.jsonl`, `csv/driver_cells.csv`, `e6d1-run.log` — bulk raw data,
  gitignored per the data policy (pgmcp experiment 148; `csv/driver_cells.csv` uses the
  `arm_e6d1` column with values `control-e6d1`/`treatment-e6d1`, postfix-precedent shape).

Cross-references: baselines `../2026-07-19-e6a/` (pre-fix) and `../2026-07-19-e6a-postfix/`
(post trie-cache); pgmcp experiments 145/148; f1r3node commits `602144bd`/`c3d5b3f2`/
`351e494d` (consensus-relevance: review before upstreaming, same standing as `31b354e6`).
