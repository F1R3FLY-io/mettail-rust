# E-6a post-fix re-measurement — after the f1r3node EPathMap trie-cache fix

> **Historical measurement record.** This report describes the exact 2026-07-19 implementation,
> including its set-encoded values and retired codec cap. The current E-6a revalidation uses native
> homogeneous `PathMap<Par>` storage, exact-key lookup, and the capless canonical codec.

Re-run of the full E-6a measured corpus (same workloads, seeds, and 33-rep protocol as
`../2026-07-19-e6a/`; `taskset -c 0-7`, performance governor) against the f1r3node-rust-mettail
branch `fix/epathmap-trie-cache` @ `84a0fbe4` (stacked on `fix/split-byte-width-range` @
`31b354e6`). The fix: (a) a bounded process-wide memo around `e_pathmap_to_rholang_pathmap`
(keyed by the full prost encoding — full-bytes equality on hit, no truncated digest trusted;
O(1) refcounted clone on hit; copy-on-write isolates callers), eliminating the per-query
whole-trie rebuild; (b) native terminator-first zipper descent for the previously
whole-map-scanning query methods (`pathExists`, `getSubtrie`, `childCount`, `descendFirst`,
`descendIndexedBranch`, `toNextSibling`, `toPrevSibling`), order-pinned against the retired
scans. Cost `reserve_*` lines untouched — the fix removes uncharged host work only.

## Verdict against the pre-registered contingency

- **Counters: byte-identical** to the pre-fix run on every cell/arm (all 15 deterministic
  columns) — the fix changed no observable semantics; the E-6a primary verdict (treatment
  6.4×–18.6× fewer spread+matching COMMs; `NestedEntryMultiSite` dissolved) stands unchanged.
- **Wall: does NOT flip.** Treatment improved 4.9%–13.3%; control within ±2.6% noise; the
  treatment/control inj ratio moved 2.54×–39.70× → 2.44×–37.33×. Per the user-approved
  contingency, A-S5b proceeds on the value-carrier branch (per-candidate private data), with
  the PathMap index carrier preserved as a swap seam.
- **New profile-backed root cause of the residual** (perf cpu-clock, swap_comb n=16 treatment):
  the trie rebuild is gone (`par_to_sexpr` 0.02%); the wall is now dominated by **by-value
  EPathMap transport** through eval/dispatch/COMM — `Par`/`ExprInstance` clone 16.5%, drop/free
  14.0%, prost `to_vec` deep-copy 15.9%, `encoded_len` 3.4%, malloc 3.2%. The interpreter
  deep-clones the map-carrying Par per method dispatch; fixing that means reference-shaped
  zipper receivers or interned map payloads — an interpreter value-handling change outside this
  fix's scope, recorded for the conditional deep-dive.

## Files

- `run.sh` / `analyze.py` — the exact re-run + analysis scripts (mirrors `../2026-07-19-e6a/`).
- `comparison.md` — primary/secondary comparison table (this run).
- `cells.csv` — the per-cell test table.
- `summary.csv`, `driver/*.jsonl`, `e6a-run.log` — bulk raw data, gitignored per the data
  policy (stored in pgmcp, experiment 145 `e-6a-pathmap-subject-indexing`).

Cross-references: pre-fix run `../2026-07-19-e6a/`; pgmcp experiment 145; f1r3node commit
`84a0fbe4` (consensus-relevance: none intended — pure-function memoization + algorithmically
equivalent descent; review before upstreaming, same standing as `31b354e6`).
