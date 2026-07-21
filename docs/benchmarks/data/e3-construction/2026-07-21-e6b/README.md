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
- **(i) retained-bytes benefit — HOLDS at every r (CORRECTED 2026-07-21).**
  The retained-bytes ARE emitted — on the terminal `e6b_rep` summary line of
  each JSONL (`retained_fragment_bytes` / `whole_artifact_bytes` /
  `retained_lt_whole`); an earlier analysis parsed only the per-append `e6b`
  lines (which carry `store_entries`, a count) and wrongly reported a "harness
  gap." Rendered: retained vs whole = 25,692 / 682,812 (r100, 26.6×) →
  123,143 / 5,646,438 (r1000, **45.9×**); 96–98% fewer bytes, margin GROWING
  with r; `retained_lt_whole = true` at every r. Mechanism: NOT cross-key
  content dedup (`content_dedup_hits = 0`; `store_entries` 1.00× both arms) but
  ACROSS-SNAPSHOT Arc-identity CoW dedup (`dedup_hits` 6,175 → 51,175) — each
  unchanged fragment's `Arc` persists across all 51 snapshots counted ONCE,
  while the whole-artifact baseline re-counts per snapshot; the per-rule
  fragment granularity enables it. Full rendering + provenance:
  `../2026-07-21-e6b-bytes/` (@ commit `cbac25af`).

Per-cell medians and the full row data are in `e6b_summary.json` and the
`e6b_r{r}_{store}.jsonl` files. This record is authoritative for (ii)/(iii)
and carries the (i) bytes on its `e6b_rep` lines; `../2026-07-21-e6b-bytes/`
renders (i) explicitly. H4v2 CONFIRMED on all three sub-metrics.
