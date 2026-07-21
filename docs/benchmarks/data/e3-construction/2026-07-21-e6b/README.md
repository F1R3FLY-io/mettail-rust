# E-3 T-E6B / H4v2 — PathMap-backed construction-side fragment store

Window `2026-07-21T09:44:07Z..11:18:50Z` UTC, bin `bench_e3_construction`
(sha256 `6e80d242…`) @ mettail `c4d3be6c`; store impl `5f442ff7`, harness
`c4d3be6c`. `taskset -c 0-7`, performance governor, 300 s settle, run once;
K=50 extension-ladder appends × 30 measured reps (+3 warmup) per cell;
r ∈ {100,250,500,1000}, two store arms (pathmap / hashmap twin). Equivalence
gate (`--mode wb-gate`) ran green before the cells at every r.

## Deterministic verdict (pgmcp experiment 146, H4v2)

- **(ii) invalidation exactness — CONFIRMED.** `actual_invalidated ==
  expected_invalidated` on all 12,000 measured rows, every cell, both arms.
- **(iii) wall guard — CONFIRMED.** The PathMap store is wall-neutral vs the
  HashMap twin: pm/hm = 1.000 / 1.000 / 1.005 / 0.993 at r = 100 / 250 / 500 /
  1000 — within the ±5% two-sided guard everywhere. Zero fallbacks; all
  installs Ok.
- **(i) retained-bytes benefit — NOT RENDERED (harness gap).** The bench
  emitted `store_entries` (a COUNT — identical 1.00× between arms at every r)
  but not the retained-*bytes* field the frozen (i) requires ("retained
  serialized-fragment bytes deduped by Arc identity < per-variant
  whole-artifact maps"). Equal entry counts do not settle the byte comparison
  (deduped fragments vs. whole artifacts can differ in bytes at equal counts).
  A byte-emitting deterministic re-run renders (i); tracked as the follow-up.

Per-cell medians and the full row data are in `e6b_summary.json` and the
`e6b_r{r}_{store}.jsonl` files. This record is complete and authoritative for
(ii) and (iii); (i) is appended by the byte-emit re-run.
