# 2026-07-20-e6d2 — E-6d #2: final E-6a re-measure after the FULL EPathMap fix stack

Pre-registered pgmcp **experiment 149** (criteria FROZEN before the run). Final re-run of the
full E-6a measured corpus (same workloads, seeds, 33-rep/3-warmup protocol, `taskset -c 0-7`
as `../2026-07-19-e6a/`, `../2026-07-19-e6a-postfix/`, `../2026-07-20-e6d1/`) against
f1r3node-rust-mettail branch `fix/epathmap-value-handling` @ `ead2f152` — the complete stack:

- **P0** `602144bd` — parity harness (prost/serde/event-hash/Ord goldens + charge-KIND traces).
- **P1** `c3d5b3f2` — content-addressed EPathMap intern store (K2 digest+verify keying,
  streaming encode, eval_stable classifier).
- **P2** `351e494d` — method-chain view fusion (name-gated recognizer, charge-order replay).
- **P3** `4e422b6b` — hand-maintained EPathMap wrapper via `extern_path` (cached-bytes
  Message impl, shadow-cell handle, construction-site migration).
- **P4.1** `60aaa02e` — Arc-shaped hot-store payloads (reference-shaped transport).
- **P4.2** `6c0a90cb` — borrowed Matcher signature (zero-copy match attempts).
- **P4.3** `ead2f152` — spliced event hashing via StableHashSerialize (PM-1 emitter).

Stacked on the postfix baseline's `84a0fbe4` (trie-cache) + `31b354e6`. mettail driver tree
`ae30b69c` (the P4 borrowed-Match/Arc-Datum adaptation commit; protocol build: `cargo build
--release -p rholang-runtime --bin bench_e6a_pathmap_driver --features
bench-naive-baseline,swap-demo-runtime,lambda-demo-runtime,ctx-demo-runtime`). Hardware: AMD
Ryzen Threadripper PRO 5975WX (ASUS Workstation, Zen 3); governor `performance` on CPUs 0-7,
`scaling_driver=amd-pstate-epp`, `boost=1`, max 4561.8 MHz.

**E-6d #1 settle lesson applied (frozen into exp 149):** build finished 18:48:01, recorded
300 s settle 18:48:35→18:53:35, first measured cell at 5m34s post-build (e6d1 had begun 47 s
post-build and took a +10.4% swap64-control transient). Within-cell first-10 vs last-10
trends this run: every control cell flat (−0.3%…+0.4%, one +4.6%) — **no transient**.

## Verdict against the frozen gates

- **(a) Counter identity: PASS.** All 15 deterministic counter columns
  ({primary, matching_comms, consumed_cost_units, program_encoded_len, attempts} ×
  {median,min,max}) byte-identical to ALL THREE baselines on every cell/arm; extended
  counters (spread_sends/successes/observed_count/receiver_count + all 10 `comm.*` classes)
  also identical; swap_comb 64 treatment still DNFs by the machine trie-key cap (untouched).
  P3+P4 changed no observable semantics; the E-6a primary verdict stands unchanged.
- **(c) Primary ≥1.2× FURTHER treatment inj vs e6d1: PASS.** swap_comb 16 **1.43×**
  (357.969→250.735 ms) and nested_spine 16 **1.34×** (331.159→246.227 ms), Welch one-sided
  q_BH ≈ 4e-37/1e-56; every completed treatment cell improved further 1.14×–1.43× (all
  significant). Ratio band compressed again **1.30×–8.34× → 1.19×–6.35×** (pre-fix band was
  2.54×–39.70×). Cumulative postfix→e6d2: swap16 **6.15×**, nested16 **5.34×**, all nine
  completed cells 2.17×–6.15×. FALSIFIER not triggered (≥1.1× everywhere primary AND the
  digest frames collapsed — see the profile).
- **(b) Control neutrality vs e6d1: FAIL as-run on 7/10 cells — uniformly FASTER.** Shifts
  −0.96%…−8.02%, ALL negative (10/10 faster than e6d1, sign-test p≈0.002 under a
  machine-neutral null; 9/10 also faster than postfix, 10/10 faster than pre-fix; the one
  exception, swap64-control vs postfix +4.3%, is the historically noisy cell whose e6d1
  settled diagnostic was 1417.9 ms — e6d2: 1472.7 ms). Within-cell trends are flat, so this
  is NOT a settling transient; the two candidate mechanisms are (i) a REAL shared-transport
  win — P4.1 Arc-shaped hot-store payloads + P4.2 borrowed Matcher sit on the produce/consume
  path BOTH arms exercise — or (ii) a global machine-state offset between sessions. The
  binaries cannot be A/B'd retroactively (the e6d1 binary was overwritten by the protocol
  rebuild). Under the MOST CONSERVATIVE reading (attribute the entire control shift to
  machine state), the ratio-of-ratios still passes the primary: swap16 **1.31×**, nested16
  **1.26×** (all nine cells 1.08×–1.37×). Coordinator owns the gate call.

| workload | n | control inj ms (pre→post→e6d1→e6d2) | treatment inj ms (pre→post→e6d1→e6d2) | further (e6d1→e6d2) | cumul. (post→e6d2) |
|---|---|---|---|---|---|
| swap_comb | 4 | 4.165→4.182→4.173→3.935 | 41.999→38.333→13.298→10.319 | 1.29× | 3.71× |
| swap_comb | 16 | 41.826→41.294→42.923→39.481 | 1660.510→1541.572→357.969→250.735 | **1.43×** | **6.15×** |
| swap_comb | 64 | 1521.846→1411.759→1558.001→1472.725 | DNF→DNF→DNF→DNF (machine cap) | — | — |
| multi_rule_shared | 402 | 7.537→7.165→7.181→6.920 | 75.254→65.246→21.944→16.295 | 1.35× | 4.00× |
| multi_rule_shared | 803 | 28.088→26.858→26.722→26.467 | 623.416→567.204→150.638→109.207 | 1.38× | 5.19× |
| nested_spine | 2 | 1.992→1.987→1.972→1.902 | 8.543→7.832→3.737→3.190 | 1.17× | 2.46× |
| nested_spine | 8 | 13.508→13.246→13.173→12.448 | 211.945→195.893→57.373→44.674 | 1.28× | 4.38× |
| nested_spine | 16 | 47.929→46.445→47.360→44.257 | 1382.703→1315.088→331.159→246.227 | **1.34×** | **5.34×** |
| lambda_chain | 4 | 22.396→21.847→21.586→20.473 | 56.797→53.389→28.057→24.614 | 1.14× | 2.17× |
| lambda_chain | 8 | 75.200→74.211→74.019→69.985 | 232.249→217.392→97.665→83.289 | 1.17× | 2.61× |

## Profile finding (perf cpu-clock, swap_comb n=16 treatment, mirrored capture — the L2/D2 packet)

Same calibrated flat self-time classifier as e6d1 (5374 samples; probe median 258.6 ms vs
official 250.735 ms). Shares of wall, with absolutes against each run's official median:

- **prost encode-class (the P1 digest tax): COLLAPSED.** `encoded_len` **20.12% → 6.53%**
  (+ encode-write frames: 22.28% → 7.40%; + Blake2b: digest pipeline 23.33% → 7.81%).
  Absolute ≈72.0 → ≈16.4 ms/inj (**4.4× less**). `Par::encoded_len` fell from the #1
  resolved frame (10.11%) to #6 (3.35%). The frozen "<5% of wall" check is NOT met by
  +1.53 pp as a share — but the share is taken of a 1.43×-smaller wall; P3's cached-bytes
  wrapper eliminated ~78% of the absolute digest cost.
- **clone-class (the L2 evidence): the ps-deep-copy residue REMAINS DOMINANT — now the #1
  cost class.** 24.47% → **29.76%** of wall; absolute ≈87.6 → ≈74.6 ms/inj (only −15%).
  Within it, prost boxed `to_vec` deep-copies are absolutely FLAT (≈44.6 → ≈44.8 ms;
  12.46% → 17.88% share) while models `Clone::clone` fell −31% (≈43.0 → ≈29.8 ms). The
  handle economy (P3 shadow-cell + P4 Arc transport) removed the digest tax, NOT the
  boxed-oneof deep-copy floor.
- **drop/free:** 11.50% → **13.22%**; absolute ≈41.2 → ≈33.1 ms/inj (−20%).
- **Top-5 self-time frames:** libc-unresolved allocator internal 10.12%; `Expr::to_vec`
  (prost boxed deep-copy) 7.80%; `drop_glue::<Par>` 7.35%; `Par::clone` 5.73%; `cfree`
  3.59% (next resolved: `Vec<GUnforgeable>::clone` 3.42%, `Par::encoded_len` 3.35%).
- Attribution caveat (unchanged from both prior captures): release binary without frame
  pointers — ~95% of clone-class samples have zero resolvable ancestry; of the 29 resolvable
  clone leaves, 28 sit under `Expr::to_vec` and 1 under the `ParToSExpr` readback. The flat
  comparison is like-for-like across all three captures.

## Files

- `run.sh` / `analyze.py` — the exact protocol + analysis scripts (mirror the e6d1 dir; only
  OUT and the header comment differ, including the frozen settle-wait step).
- `comparison.md` — this run's within-run primary/secondary table; `cells.csv` — test table.
- `summary.csv`, `driver/*.jsonl`, `csv/driver_cells.csv` (`arm_e6d2` column,
  `control-e6d2`/`treatment-e6d2`), `e6d2-run.log` — bulk raw data, gitignored per the data
  policy (pgmcp experiment 149).

Cross-references: baselines `../2026-07-19-e6a/` (pre-fix), `../2026-07-19-e6a-postfix/`
(post trie-cache), `../2026-07-20-e6d1/` (P0–P2); pgmcp experiments 145/148/149; f1r3node
commits `602144bd`/`c3d5b3f2`/`351e494d`/`4e422b6b`/`60aaa02e`/`6c0a90cb`/`ead2f152`
(consensus-relevance: review before upstreaming, same standing as `31b354e6`).
Merge-back 2026-07-20: `fix/epathmap-value-handling` was fast-forwarded into `feature/mettail`
(both refs carry the measured `ead2f152` stack); the upstream review packet is
`f1r3node docs/epathmap-value-handling-review.md`.
