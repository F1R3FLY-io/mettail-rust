# Post-D-E5 persistent-R3 production rematch

This immutable run is pgmcp experiment 174, the rematch scheduled by the
2026-07-19 keep-both decision. It compares the production set-automaton (SA)
driver with the D-E5 finite-route persistent R3 driver on identity-beta chains
of depths 2, 4, 8, 16, 32, and 64.

## Result

The corrected frozen decision is **`retarget-generated-driver-to-r3`**. Every
cell passes all five gates: expected output, exact firing count, lower committed
matching-COMM count, lower evaluated communication-prefix cost, and wall-time
non-inferiority. R3 is also strictly smaller in encoded program bytes at every
size. The complete table is in [comparison.md](comparison.md), with
machine-readable statistics in `analysis.json`.

## Protocol and resources

- Source commit: `1ae848b44dcff6da186cdb3b5c7e45e439edda59`.
- Driver SHA-256: `d958c94562376e56df5034adb53b95c886eae6d86f958555d017f38f7b748675`.
- Three warmups followed by 51 measured repetitions per arm and size.
- CPU affinity: cores 0–7.
- Build RSS cap: 12 GiB; run RSS cap: 4 GiB; swap disabled.
- Ordinary Rust stacks; no `RUST_MIN_STACK`, `stacker`, or traversal-depth cap.
- Zero DNF cells and deterministic semantic/counter vectors within each cell.

The raw JSON-lines samples and `samples.tsv` are immutable. `sha256sums.txt`
authenticates the run inputs and projections.

## Analysis correction

The first analyzer incorrectly required both arms to emit one observation per
firing. SA intentionally emits `n` per-step observations, whereas persistent
R3 emits one combined normal-form observation while recording the same `n`
visible firings. [ANALYSIS-CORRECTION.md](ANALYSIS-CORRECTION.md) records the
defect and correction. The raw measurements were not repeated or altered; only
derived analysis was recomputed from the authenticated samples.
