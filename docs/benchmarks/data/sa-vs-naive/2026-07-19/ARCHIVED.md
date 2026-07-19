# Data locations

The raw record of each protocol run is split by size class (user directive 2026-07-19):

- **In git (this directory)**: `header.json`, `env.txt`, `WARNINGS.md`, `sanity.txt`,
  `summary_medians.csv` (per-cell medians), and the analysis outputs under `csv/`
  (`b7_*`, `driver_summary`, `cell_accounting`, `dnf_audit`).
- **In pgmcp (experiment 144, `set-automaton-vs-naive-kt-appendix-a-in-rho-matching-efficiency`)**:
  the full per-replicate samples, ingested per workload with arms split by matcher and each
  sample unit-keyed by `(n, encoding, rep)` — query them through the experiment ledger.
- **On disk, untracked (pgmcp-indexed)**: the per-cell `driver/*.jsonl`, the flat per-rep
  `summary.csv` and `csv/driver_cells.csv`, the zstd-archived criterion estimate trees
  (`criterion.tar.zst`, `criterion-consume-test.tar.zst` — extract with `tar --zstd -xf`),
  and the `*-run.log` execution logs.
