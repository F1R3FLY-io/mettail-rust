# Mettail WPDA Lean Checks

This optional Lean project mirrors small Prattail WPDA runtime invariants that
are also proved in Rocq. Rocq remains the authoritative proof target; Lean is
kept here only when it gives a useful independent check.

Current checked obligation:

- `EquivKey` intentionally drops dispatch position and wrap identity.
- `EdgeKind.crossCatProjection` equality preserves wrap identity, matching the
  Rust `EdgeKind::CrossCatProjection` payload and the TLA+ wrap-sensitive model.
- `ConfigKey` carries the runtime merge discriminators that must prevent
  unsound cursor collapse: cohort origin, SPPF top, and lex-fork stamp.
- EOI semantic-root acceptance rejects non-structural skipped prefixes while
  allowing delimiter-only wrappers around a same-span semantic root.
- Recovery infra signatures include the active recovery config, token map,
  sync set, and WFST observation needed to safely reuse recovery-dispatch
  cohort cache entries.

Run through the capped formal harness from the repository root:

```sh
make -C formal check-capped FORMAL_CAPPED_TARGET=lean-prattail-wpda
```
