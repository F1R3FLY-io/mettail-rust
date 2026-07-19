# 2026-07-19-e6a — E-6a: PathMap-backed subject indexing for in-Rho matching

Pre-registered pgmcp **experiment 145**
(`e-6a-pathmap-backed-subject-indexing-for-in-rho-matching`). Criterion
LOCKED at registration: Welch `α = 0.05`, Benjamini–Hochberg across cells,
≥ 30 measured reps/arm after 3 warmups, primary metric
`spread_plus_matching_comms_per_normalization`, lower better.

Measured at mettail-rust `c979fb63` + the uncommitted E-6a working tree
(`rholang-runtime/src/e6a_support.rs`, `src/bin/bench_e6a_pathmap_driver.rs`,
`tests/e6a_pathmap_spike.rs`, `tests/rho_net_e6a_equivalence.rs`, plus the
`pathmap_index` COMM-class extension of `bench_support.rs`/`workloads.rs`),
all quarantined behind `bench-naive-baseline` — no production surface.

## Arms

* **control** — the CURRENT spread+drive path: per-node `spread_term_par`
  (`loc:` head-tag send per node + `col:`/`cap:` collapse fold) + the cell's
  current matcher column (`sa` for swap_comb locate-all / multi_rule_shared
  per-rule / lambda_chain per-step root; `naive` for nested_spine, whose sa
  locate-all fails closed with `NestedEntryMultiSite`), sites located by the
  HOST-side `collect_redex_sites` walk.
* **treatment** — the PathMap subject index: ONE persistent `EPathMap`
  produce (paths mirror `spread_child_location`'s site scheme, segmented per
  component; «s» op-first site/tag entries + «v» tuple-wrapped σ-carrier
  entries), MACHINE-side per-op site enumeration
  (`readZipperAt([tag]).getSubtrie()` published on `e6a:sites:…`), harness
  readback (the pre-registered REDUCED form), then per-(entry, site)
  QUERY-MATCH processes (`pathExists` guard chains + `descendFirst().getLeaf()`
  σ extraction + `build_accept_send`-ABI accepts) against the persistent
  index. Zero `loc:`/`col:`/`cap:` traffic; `collect_redex_sites` never runs.

## Layout

| file | content | git |
|---|---|---|
| `run.sh` | the VERBATIM run protocol (33 reps, 3 warmups, `taskset -c 0-7`) | tracked |
| `analyze.py` | per-cell Welch+BH analysis → `summary.csv` / `cells.csv` / `comparison.md` | tracked |
| `comparison.md` | the per-cell primary/secondary table | tracked |
| `driver/*.jsonl` | raw per-rep JSON lines (one file per cell × arm) | ignored (bulk) |
| `driver/e6a_samples.csv` | flat per-rep samples (pgmcp ingestion shape) | ignored (bulk) |
| `summary.csv`, `cells.csv` | aggregates + test table | ignored (bulk) |
| `e6a-run.log` | the run transcript | ignored (bulk) |

## Headline (see `comparison.md` for the full table)

* The treatment is LOWER on the primary in ALL 9 completed cells (deterministic
  counters — within-arm variance 0 — so Welch degenerates to the exact
  comparison; every completed cell significant at q = 0): effects range from
  −27 (nested_spine 2) to −564 (lambda_chain 8), i.e. 6.8–18.6× fewer
  spread-sends+matching-COMMs per normalization.
* `NestedEntryMultiSite` is DISSOLVED on the measured corpus: nested_spine
  k ∈ {2, 8, 16} and multi_rule_shared r ∈ {4, 8} run IN-RHO under the
  treatment (machine-enumerated sites, no descent races — queries are
  non-destructive reads of the persistent index), with fired sets equal to the
  control and to the directly-computed expected multisets
  (`tests/rho_net_e6a_equivalence.rs`, 5/5).
* HONEST COSTS: (i) the exploratory inj-wall secondary is SLOWER under the
  treatment in every cell (2.5–40×) — the reducer's `EPathMap` methods rebuild
  the whole trie from `ps` on EVERY call (`e_pathmap_to_rholang_pathmap`) and
  the prefix-scanning methods iterate the whole map, so a query is O(index);
  (ii) swap_comb m = 64 treatment DNFs by the machine trie-key caps (S-expr
  symbol ≤ 63 bytes with `Symbol(63)` = 0xFF colliding with the segment
  separator ⇒ safe cap 62; list arity ≤ 63 ⇒ site depth ≤ 61) — recorded as
  33/33 `dnf` lines, never forced; (iii) what remains host-side in the reduced
  form: index construction (a subject walk, same class as the control's
  host-side spread emission), the discovery readback + per-site query `Par`
  codegen + second injection, and the non-ancestry verification.
