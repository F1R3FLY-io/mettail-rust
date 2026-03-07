---
Date: 2026-03-06
Updated: 2026-03-06
---

# Decision Tree Design Documents

PathMap Decision Tree — Unified Parse Dispatch for PraTTaIL.

## Reading Order

1. **[overview.md](overview.md)** — Design rationale, approach comparison, trade-offs
2. **[bytecode-specification.md](bytecode-specification.md)** — Complete byte encoding spec
3. **[trie-construction.md](trie-construction.md)** — Insertion algorithm, worked examples *(planned)*
4. **[nonterminal-resolution.md](nonterminal-resolution.md)** — FIRST set expansion at NT boundaries *(planned)*
5. **[code-emission.md](code-emission.md)** — Match-arm and flat-table emission *(planned)*
6. **[grammar-algebra.md](grammar-algebra.md)** — PathMap meet/subtract/join for composition *(planned)*

## Related Documents

- **Theory**: [`docs/theory/decision-tree/foundations.md`](../../theory/decision-tree/foundations.md) — Determinism theorems, subsumption proofs
- **Architecture**: [`docs/architecture/decision-tree/module-map.md`](../../architecture/decision-tree/module-map.md) — Module structure, data flow
- **Diagnostics**: [`docs/diagnostics/decision-tree/README.md`](../../diagnostics/decision-tree/README.md) — D01-D09 lint catalog

## Source Files

| File                            | Role                                                                                                                     |
|---------------------------------|--------------------------------------------------------------------------------------------------------------------------|
| `prattail/src/decision_tree.rs` | Core module (~3400 lines): trie, analysis, `dispatch_strategy()`, `build_decision_trees_from_spec()`, `IncrementalState` |
| `prattail/src/pipeline.rs`      | Tree construction, diagnostic emission, D07 coverage module, Layer 10 cache load/save                                    |
| `prattail/src/trampoline.rs`    | Consumes `dispatch_strategy()` for DisjointSuffix + NfaTryAll codegen, coverage instrumentation                          |
| `prattail/src/compose.rs`       | X06/X07 composition analysis via `build_decision_trees_from_spec()`                                                      |
| `prattail/src/cost_benefit.rs`  | Optimization gates (legacy fallback control)                                                                             |
| `prattail/src/lib.rs`           | `pub mod decision_tree`, `PipelineAnalysis.decision_trees`                                                               |

## Implementation Status

| Phase    | Status   | Description                                                                                                      |
|----------|----------|------------------------------------------------------------------------------------------------------------------|
| 1        | COMPLETE | Infrastructure + Trie Construction                                                                               |
| 2        | COMPLETE | Decision Tree Analysis (10 analysis layers)                                                                      |
| 3-4      | COMPLETE | Diagnostic utilities (`emit_match_arms`, `emit_flat_table`). Actual codegen via trampoline `dispatch_strategy()` |
| 5        | COMPLETE | Integration — DisjointSuffix + NfaTryAll + Singleton consumed by trampoline                                      |
| 6        | COMPLETE | Documentation (20+ docs created/updated)                                                                         |
| 7        | COMPLETE | Languages regenerated, all workspace tests pass                                                                  |
| X06/X07  | COMPLETE | `build_decision_trees_from_spec()` + compose pipeline integration                                                |
| D07      | COMPLETE | Runtime coverage instrumentation (`parser-coverage` feature gate)                                                |
| Layer 10 | COMPLETE | `.prattail-cache` with version-tagged `IncrementalState`                                                         |
