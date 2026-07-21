# 2026-07-20-e6d3 — E-6d #3: the L2 shared-ps FALSIFICATION re-measure

Pre-registered pgmcp **experiment 150** (criteria FROZEN before the run). Re-run of the full
E-6a measured corpus (same workloads, seeds, 33-rep/3-warmup protocol, `taskset -c 0-7` as
`../2026-07-19-e6a/`, `../2026-07-19-e6a-postfix/`, `../2026-07-20-e6d1/`,
`../2026-07-20-e6d2/`) against f1r3node-rust-mettail branch `fix/epathmap-value-handling` @
`131aecee` (== `feature/mettail`) — the complete E-6d #2 stack plus L2:

- **P0** `602144bd` — parity harness (prost/serde/event-hash/Ord goldens + charge-KIND traces).
- **P1** `c3d5b3f2` — content-addressed EPathMap intern store (K2 digest+verify keying).
- **P2** `351e494d` — method-chain view fusion (name-gated recognizer, charge-order replay).
- **P3** `4e422b6b` — hand-maintained EPathMap wrapper via `extern_path` (cached-bytes
  Message impl, shadow-cell handle, construction-site migration).
- **P4.1** `60aaa02e` / **P4.2** `6c0a90cb` / **P4.3** `ead2f152` — Arc-shaped hot-store
  payloads, borrowed Matcher signature, spliced event hashing (StableHashSerialize).
- **L2** `131aecee` — **shared ps** (Arc-backed SharedPars; O(1) ps clone at the node; CoW
  mutation census). THE COMMIT UNDER TEST.

Stacked on the postfix baseline's `84a0fbe4` (trie-cache) + `31b354e6`. mettail driver tree
`504e3d0b` (contains the P4 adaptation `ae30b69c`; protocol build: `cargo build --release
-p rholang-runtime --bin bench_e6a_pathmap_driver --features
bench-naive-baseline,swap-demo-runtime,lambda-demo-runtime,ctx-demo-runtime`). Hardware: AMD
Ryzen Threadripper PRO 5975WX (ASUS Workstation, Zen 3); governor `performance` on CPUs 0-7,
`scaling_driver=amd-pstate-epp`, `boost=1`, max 4561.8 MHz.

**Settle (frozen since exp 149):** build finished 20:11:48 exit 0 (5m46s); a session outage
kept the machine measurement-idle post-build; first measured cell 21:20:41 — recorded settle
wait 4134 s >= the frozen 300 s. Within-cell first-10 vs last-10 control trends: every cell
flat (−1.65%…+2.32%) — **no transient** (swap64-control's first10 median 1418.5 ms matches
e6d1's settled diagnostic 1417.9 ms).

## THE ATTRIBUTION VERDICT (gate c, the question this run decided): CONFIRMED

E-6d #2 found the flat ≈44.8 ms/inj boxed prost `Expr::to_vec` deep-copy class as the #1
residual and hypothesized it is dominated by EPathMap ps copies; L2 makes ps clones O(1).
The frozen instrument — the post-run profile's boxed-to_vec absolute ms/inj on swap_comb
n=16 treatment (classifier share × the official run median):

- **boxed `Expr::to_vec`: 44.83 → 5.38 ms/inj — an 88.0% fall** (frozen: >=50% fall =>
  CONFIRMED; within ±20% => REFUTED). **The attribution hypothesis is CONFIRMED**: the
  flat to_vec class WAS the EPathMap ps deep-copy; sharing the ps at the node collapsed it.
- The confirmed-branch wall prediction (gate d) was also met, 4.3× beyond its threshold.

## Verdict against the frozen gates

- **(a) Counter identity: PASS.** All 15 deterministic counter columns
  ({primary, matching_comms, consumed_cost_units, program_encoded_len, attempts} ×
  {median,min,max}) byte-identical to ALL FOUR baselines on every cell/arm; extended
  counters (spread_sends/successes/observed_count/receiver_count + all 10 `comm.*` classes)
  also identical; swap_comb 64 treatment still DNFs by the machine trie-key cap (untouched).
  L2 changed no observable semantics; the E-6a primary verdict stands unchanged.
- **(c) THE ATTRIBUTION VERDICT: CONFIRMED** (above; the profile section has the packet).
- **(d) Walls >=1.1x further vs e6d2 on the heavy cells: MET — by 4.3x.** swap_comb 16
  **4.73×** (250.735→52.980 ms, q_BH ≈ 4e-115) and nested_spine 16 **4.89×**
  (246.227→50.342 ms, q_BH ≈ 8e-78); every completed treatment cell improved further
  1.33×–4.89× (all significant). The treatment/control ratio band compressed
  **1.19×–6.35× → 0.79×–1.37×** (pre-fix: 2.54×–39.70×) — the treatment is now FASTER
  than control on 4 of 9 completed cells (lambda_chain 4/8, multi_rule_shared 402/803).
  Cumulative postfix→e6d3: swap16 **29.10×**, nested16 **26.12×**, all nine completed
  cells 2.89×–29.10×.
- **(b) Control neutrality vs e6d2: FAIL as-run on 1/10 — the historically noisy
  swap64-control, −5.15%** (1472.725→1396.932 ms, BH-significant; barely past the frozen
  5% line). The other nine cells sit within ±2.13% and the direction pattern is MIXED —
  4 faster / 6 slower, sign-test p≈0.75 — so unlike e6d2's uniform all-faster shift there
  is NO machine-state offset signature this run. The violating cell's five-run arc is
  1521.8 → 1411.8 → 1558.0 → 1472.7 → 1396.9 ms (inter-run spread ≈11%; e6d3 is a new low
  but only 1.1% below postfix); its within-cell trend is flat (−1.55%). Disclosure: two
  light status probes (cat/ls/pgrep, un-pinned) overlapped this cell's window ~21:20:45–
  21:21:34 — reported as a possible minor perturbation source. Under the most conservative
  reading (attribute the whole −5.15% to machine state), the treatment ratios elsewhere
  move by ≤2.13% and both gate-(d) cells stay above 4.6×. Coordinator owns the gate call.

## The five-run arc (inj wall medians, ms)

| workload | n | control inj ms (pre→post→e6d1→e6d2→e6d3) | treatment inj ms (pre→post→e6d1→e6d2→e6d3) | further (e6d2→e6d3) | cumul. (post→e6d3) |
|---|---|---|---|---|---|
| swap_comb | 4 | 4.165→4.182→4.173→3.935→3.969 | 41.999→38.333→13.298→10.319→5.445 | 1.90× | 7.04× |
| swap_comb | 16 | 41.826→41.294→42.923→39.481→39.551 | 1660.510→1541.572→357.969→250.735→**52.980** | **4.73×** | **29.10×** |
| swap_comb | 64 | 1521.846→1411.759→1558.001→1472.725→1396.932 | DNF×5 (machine cap) | — | — |
| multi_rule_shared | 402 | 7.537→7.165→7.181→6.920→6.868 | 75.254→65.246→21.944→16.295→6.454 | 2.52× | 10.11× |
| multi_rule_shared | 803 | 28.088→26.858→26.722→26.467→25.903 | 623.416→567.204→150.638→109.207→24.889 | 4.39× | 22.79× |
| nested_spine | 2 | 1.992→1.987→1.972→1.902→1.897 | 8.543→7.832→3.737→3.190→2.032 | 1.57× | 3.86× |
| nested_spine | 8 | 13.508→13.246→13.173→12.448→12.530 | 211.945→195.893→57.373→44.674→13.345 | 3.35× | 14.68× |
| nested_spine | 16 | 47.929→46.445→47.360→44.257→44.416 | 1382.703→1315.088→331.159→246.227→**50.342** | **4.89×** | **26.12×** |
| lambda_chain | 4 | 22.396→21.847→21.586→20.473→20.535 | 56.797→53.389→28.057→24.614→18.503 | 1.33× | 2.89× |
| lambda_chain | 8 | 75.200→74.211→74.019→69.985→70.031 | 232.249→217.392→97.665→83.289→55.403 | 1.50× | 3.92× |

## Profile finding (perf cpu-clock, swap_comb n=16 treatment, mirrored capture — the verdict packet)

Same calibrated flat self-time classifier as e6d1/e6d2 (1281 samples — proportionally fewer
because the wall is 4.73× smaller at the same 4 kHz; probe median 55.6 ms vs official
52.980 ms). Shares of wall, absolutes against each run's official median:

- **clone-class (the L2 target): COLLAPSED.** 29.76% → 19.61% of a 4.73×-smaller wall;
  absolute ≈74.6 → **≈10.4 ms/inj (−86%)**. Within it, the boxed `Expr::to_vec`
  deep-copies — absolutely FLAT across the three prior captures (≈44.6→44.8) — fell
  **44.83 → 5.38 ms/inj (−88.0%, THE VERDICT NUMBER)**; models `Clone::clone` fell
  ≈29.8 → ≈5.0 ms (−83%). `Expr::to_vec` fell from the #1 resolved frame (7.80%) to
  ≈4.30% (split 2.19%+2.11% across two symbol instances); `drop_glue::<Par>` 7.35%→2.58%.
- **drop/free:** 13.22% → 9.85%; absolute ≈33.1 → ≈5.2 ms/inj (−84%). libc-unresolved
  allocator internals ≈108.5 → ≈15.4 ms (−86%) — the allocator traffic followed the copies.
- **digest pipeline (the frozen "expect ≈7-8% share unchanged" check): the SHARE did NOT
  stay at 7-8% — it is now the #1 class at 28.27%** (encoded_len 24.05% + encode-write
  3.05% + Blake2b 1.17%); but that share is taken of the 4.73×-smaller wall — the ABSOLUTE
  fell ≈19.6 → ≈15.0 ms/inj (−23.5%). The share expectation implicitly assumed a modest
  wall change; with the wall collapse every non-collapsed class's share expanded ~4.7×.
  Reported honestly: the digest absolute also improved (consistent with cached-bytes
  hits on now-shared nodes), and it is the dominant residual.
- **Top-5 self-time frames:** `Par::encoded_len` 10.23%; `ExprInstance::encoded_len`
  (call_once) 6.64%; GUnforgeable `encoded_len` map-fold 4.53%; `cfree` 3.51%;
  libc-unresolved 2.81% (next resolved: `drop_glue::<Par>` 2.58%, `Expr::to_vec`
  2.19%+2.11%, `Par::clone` 2.11%).
- Attribution caveat (unchanged, like-for-like across all four captures): release binary
  without frame pointers — ~98% of clone-class samples have zero resolvable ancestry
  (3 of 250 resolvable; 2 under the `ParToSExpr` readback, 1 under `Expr::to_vec`).
- Residual picture at 52.980 ms/inj: digest-pipeline ≈15.0 (28.3%) > clone-class ≈10.4
  (19.6%) > drop/free ≈5.2 (9.9%) — the remaining prost encode/copy tail is the province
  of the byte-array protobuf effort.

## Files

- `run.sh` / `analyze.py` — the exact protocol + analysis scripts (mirror the e6d2 dir; only
  OUT and the header comment differ, including the frozen settle-wait step).
- `comparison.md` — this run's within-run primary/secondary table; `cells.csv` — test table.
- `summary.csv`, `driver/*.jsonl`, `csv/driver_cells.csv` (`arm_e6d3` column,
  `control-e6d3`/`treatment-e6d3`), `e6d3-run.log` — bulk raw data, gitignored per the data
  policy (pgmcp experiment 150).

Cross-references: baselines `../2026-07-19-e6a/` (pre-fix), `../2026-07-19-e6a-postfix/`
(post trie-cache), `../2026-07-20-e6d1/` (P0–P2), `../2026-07-20-e6d2/` (full P0–P4);
pgmcp experiments 145/148/149/150; f1r3node commits `602144bd`/`c3d5b3f2`/`351e494d`/
`4e422b6b`/`60aaa02e`/`6c0a90cb`/`ead2f152`/`131aecee` (consensus-relevance: review before
upstreaming, same standing as `31b354e6`); the upstream review packet is
`f1r3node docs/epathmap-value-handling-review.md` (extend with L2 + this verdict).
