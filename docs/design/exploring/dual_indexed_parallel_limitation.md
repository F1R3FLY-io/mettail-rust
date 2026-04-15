# DualIndexed BYODS Provider: Parallel Mode Limitation

**Date**: 2026-03-21
**Status**: Serial-only — `ascent-parallel` feature is a no-op

---

## Summary

The `dual_indexed` BYODS provider (`languages/src/dual_indexed.rs`) provides O(1)
lookup on both columns of binary relations via dual `HashMap` indexing. It is used
by **all** generated languages for `rw_*`, `fold_*`, and collection projection
relations (see `macros/src/logic/relations.rs`).

This provider **only implements serial Ascent traits** and cannot be used with
`ascent_par!` (parallel fixpoint evaluation). The `ascent-parallel` feature flag
is retained in `Cargo.toml` for forward compatibility but is currently a no-op:
`generate_ascent_struct()` in `macros/src/gen/runtime/language.rs` always emits
`ascent!` (serial).

---

## Root Cause

`ascent_par!` passes the `par` token to BYODS provider macros and requires:

| Trait | Purpose |
|-------|---------|
| `CRelIndexWrite` | Concurrent relation index writes during parallel fixpoint |
| `CRelFullIndexWrite` | Full-index (both columns bound) concurrent writes |
| `CFreezable` | `freeze()`/`unfreeze()` for parallel snapshot isolation |
| `CRelIndexRead` | `c_index_get()`, `c_iter_all()` returning Rayon iterators |

`DualIndexedRel<T>` and the `ToByodsBinRel*` adaptor types only implement:

| Trait | Status |
|-------|--------|
| `RelIndexMerge` | Implemented (serial merge) |
| `Freezable` | Empty implementation (no-op) |
| `ByodsBinRel` | Implemented (serial `ind0_index_get`, `ind1_index_get`) |

The `compile_error!` guard arms in the provider macros produce a clear diagnostic
if someone re-enables `ascent_par!` without implementing parallel support.

---

## Options for Future Parallel Support

### Option A: Parallel-Safe DualIndexed (highest effort, best performance)

Implement `CRelIndexWrite`, `CFreezable`, and `CRelIndexRead` for
`DualIndexedRel<T>` and all adaptor types. Requires:
- Thread-safe data structures (e.g., `DashMap`) or lock-free concurrent `HashMap`
- `freeze()` creating immutable snapshots, `unfreeze()` reconstructing mutable state
- Rayon-compatible parallel iterators for `c_index_get` and `c_iter_all`

### Option B: Non-BYODS Fallback (medium effort, reduced performance)

Have `par` macro arms return Ascent's default parallel relation types instead of
`DualIndexedRel`. Loses O(1) dual-column lookup but gains parallel execution.

### Option C: Per-Language Opt-In (medium effort, flexible)

Allow each `language!` invocation to declare whether it uses BYODS relations.
Languages without BYODS can use `ascent_par!`; those with BYODS stay serial.

---

## Related

- `docs/design/exploring/ascent_parallel_issue.md` — original investigation (Nov 2025)
- `languages/src/dual_indexed.rs` — BYODS provider implementation
- `macros/src/gen/runtime/language.rs` — `generate_ascent_struct()` function
- `macros/src/logic/relations.rs` — relation generation using `#[ds(crate::dual_indexed)]`
