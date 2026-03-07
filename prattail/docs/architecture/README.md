# PraTTaIL WFST Architecture — Quick Reference

**Date:** 2026-03-04

---

## 1  Overview

PraTTaIL's WFST subsystem is **always-on** — every grammar build produces
prediction and recovery WFSTs with no feature gate required.  The only gated
surface is `wfst-log`, which adds log-semiring training, forward-backward
posteriors, and weight pushing.  At compile time the pipeline constructs WFSTs,
runs a four-pass optimization cascade, detects dead rules, and emits
weight-ordered dispatch and recovery code.  At runtime, thread-local state
carries NFA spillover buffers, bracket balance, and running weights for
context-sensitive recovery.

---

## 2  Layer Inventory

### Always-On (Tier 0)

| #  | Module                  | Source File             | Purpose                                                                      |
|----|-------------------------|-------------------------|------------------------------------------------------------------------------|
| 1  | Semiring algebra        | `automata/semiring.rs`  | `Semiring` trait + 8 concrete always-on types                                |
| 2  | FIRST/FOLLOW analysis   | `prediction.rs`         | `build_dispatch_action_tables()`, `resolve_dispatch_winners()`               |
| 3  | Cross-category dispatch | `dispatch.rs`           | `write_category_dispatch_weighted()`                                         |
| 4  | Pipeline orchestrator   | `pipeline.rs`           | Coordinates WFST construction, optimization, codegen                         |
| 5  | Prediction engine       | `wfst.rs`               | `PredictionWfst`, `build_prediction_wfsts()`, `nfa_alternative_order()`      |
| 6  | Token label encoding    | `token_id.rs`           | `TokenId = u16`, `TokenIdMap`, `EPSILON_TOKEN`                               |
| 7  | Weighted parse chart    | `lattice.rs`            | `TokenLattice<T,S,W>`, `viterbi_best_path()`, `viterbi_generic()`            |
| 8  | Error repair engine     | `recovery.rs`           | `RecoveryWfst`, `viterbi_recovery()`, 3-tier context multipliers             |
| 9  | Grammar composition     | `compose.rs`            | `compose_languages()`, `compose_with_wfst()`, `compose_many()`               |
| 10 | Optimization passes     | `transducer.rs`         | `TransducerCascade`, `OptimizationPass` trait                                |
| 11 | Dead-rule detection     | `pipeline.rs`           | Four-tier analysis (§5) with `BooleanWeight` reachability                    |
| 12 | Lint layer              | `lint.rs`               | 23 diagnostics across 5 categories (§6)                                      |
| 13 | NFA disambiguation      | `trampoline.rs`         | Forced-prefix replay, weight-ordered spillover buffers                       |
| 14 | NFA spillover TLS       | `trampoline.rs`         | `NFA_PREFIX_SPILL_Cat`, `NFA_FORCED_PREFIX_Cat`, `NFA_PRIMARY_WEIGHT_Cat`    |
| 15 | Recovery state TLS      | `language.rs` / codegen | `BRACKET_STATE_Cat`, `LAST_ERROR_POS_Cat`, `RUNNING_WEIGHT_Cat`              |
| 16 | Prediction statics      | `pipeline.rs` (codegen) | `WFST_TRANSITIONS_Cat`, `WFST_STATE_OFFSETS_Cat`, `PREDICTION_Cat: LazyLock` |
| 17 | Recovery statics        | `pipeline.rs` (codegen) | `RECOVERY_SYNC_TOKENS_Cat`, `RECOVERY_SYNC_SOURCES_Cat`                      |
| 18 | Decision tree           | `decision_tree.rs`      | `PathMap`, `DecisionTreeBuilder`, D01-D09 analysis layers                    |

### `wfst-log`-Gated (Tier 1)

| #  | Module                | Source File           | Purpose                                                   |
|----|-----------------------|-----------------------|-----------------------------------------------------------|
| 19 | Baum-Welch posteriors | `forward_backward.rs` | `forward_scores()`, `backward_scores()`, `total_weight()` |
| 20 | Mohri weight pushing  | `log_push.rs`         | `log_push_weights()`, `check_normalization()`             |
| 21 | Weight training       | `training.rs`         | `TrainedModel`, `RuleWeights::train()`, SGD               |

---

## 3  Semiring Catalog

| Semiring               | ⊕            | ⊗         | 0̄       | 1̄       | Gate       | Application                                 |
|------------------------|--------------|-----------|---------|---------|------------|---------------------------------------------|
| `TropicalWeight`       | min          | +         | +∞      | 0       | —          | Dispatch ordering, beam pruning             |
| `CountingWeight`       | +            | ×         | 0       | 1       | —          | Ambiguity detection (W02/W03)               |
| `BooleanWeight`        | ∨            | ∧         | 0       | 1       | —          | Dead-rule detection, reachability           |
| `EditWeight`           | min          | +         | +∞      | 0       | —          | Repair cost via `RepairAction::edit_cost()` |
| `ContextWeight`        | ∪            | ∩         | ∅       | {all}   | —          | Rule-set reachability per WFST state        |
| `ComplexityWeight`     | min          | max       | +∞      | 0       | —          | Bottleneck lookahead depth                  |
| `NbestWeight<N>`       | N-best merge | concat    | ∅       | {ε}     | —          | Top-N path extraction                       |
| `ProductWeight<S₁,S₂>` | comp.        | comp.     | (0₁,0₂) | (1₁,1₂) | —          | Multi-objective; lexicographic Ord          |
| `LogWeight`            | log-sum-exp  | +         | +∞      | 0       | `wfst-log` | Probabilistic parsing, forward-backward     |
| `EntropyWeight`        | ⊕_entropy    | ⊗_entropy | (∞,∞)   | (0,0)   | `wfst-log` | Shannon entropy of parse distributions      |

---

## 4  Pipeline Execution Order

Steps inside `generate_parser_code()`:

```
 1. compute_first_sets()
 2. Augment FIRST with native literal tokens (Integer/Float/Boolean/StringLit)
 3. analyze_cross_category_overlaps()
 4. compute_follow_sets_from_inputs()
 5. WFST construction block:
    5a. build_dispatch_action_tables()              [prediction.rs]
    5b. build_prediction_wfsts()                    [wfst.rs]
    5c. TransducerCascade optimization              [transducer.rs]
          WeightNorm → DeadStateElim → StateMin (→ BeamPruning)
    5d. TokenIdMap::from_names()                    [token_id.rs]
    5e. build_recovery_wfsts()                      [recovery.rs]
    5f. detect_dead_rules() (four-tier)             [pipeline.rs]
    5g. NFA spillover detection                     [trampoline.rs]
 6. resolve_dispatch_winners()
 7. write_rd_handler() × N
 8. write_trampolined_parser() per category
 9. write_category_dispatch_weighted()              [dispatch.rs]
10. write_recovery_helpers()
11. Per category: generate_sync_predicate()
                  generate_wfst_recovery_fn()
                  write_trampolined_parser_recovering_wfst()
```

---

## 5  Dead-Rule Detection Tiers

| Tier | Mechanism                                                                 | Semiring        | Result                                    |
|------|---------------------------------------------------------------------------|-----------------|-------------------------------------------|
| 1    | Literal rule without native type match                                    | —               | `LiteralNoNativeType` warning             |
| 2    | Fixed-point category reachability over FIRST/cast/cross-cat edges         | `BooleanWeight` | `UnreachableCategory` warning             |
| 3    | WFST query: no FIRST token dispatches to rule via `predict()`             | `BooleanWeight` | `WfstUnreachable` warning                 |
| 4    | Transitive semantic liveness via equation/rewrite/logic dependency groups | —               | **Resurrects** rules flagged by Tiers 1–3 |

---

## 6  Lint Categories

| Prefix | Category          | Count | Key Source Data                                    |
|--------|-------------------|------:|----------------------------------------------------|
| **G**  | Grammar structure |    10 | Rule specs, FIRST/FOLLOW, operator tables          |
| **W**  | WFST-specific     |     5 | Prediction WFSTs, dispatch weights                 |
| **R**  | Recovery          |     5 | Sync sets, repair costs, bracket patterns          |
| **C**  | Cross-category    |     3 | Cast graphs, FIRST-set overlaps                    |
| **D**  | Decision tree     |     9 | PathMap trie structure, ambiguity, lookahead depth |
| **P**  | Performance       |     3 | Spillover counts, cast depth, alternative fan-out  |

32 total lints emitted by `run_lints()` in `lint.rs` — see [lint-layer.md](../design/lint-layer.md) for the full catalog (includes 9 D-category decision tree lints).

---

## 7  Dependency Topology

```
  lib.rs [core]
  ├── pipeline.rs [core] ────────────────┐
  │     │                                │
  │     ▼                                ▼
  │   prediction.rs [core] ─────────► dispatch.rs [core]
  │     │                                │
  │     │                                ▼
  │     │                          write_category_
  │     │                          dispatch_weighted()
  │     │                                │
  │     │                                │
  │     └────────────────────────────────┊──► wfst.rs [core] ──► token_id.rs [core]
  │                                      │         │
  │                                      │         ▼
  │                                      │    PredictionWfst
  │                                      │         │
  │                                      │         ▼
  │                                      │    generate_weighted_dispatch()
  │                                      │
  │                                      ├──► transducer.rs [core]
  │                                      │         │
  │                                      │         ├──► wfst.rs (PredictionWfst)
  │                                      │         └──► semiring.rs (TropicalWeight)
  │                                      │
  │                                      ├──► recovery.rs [core] ──► token_id.rs [core]
  │                                      │         │
  │                                      │         ├──► lattice.rs [core]
  │                                      │         │         │
  │                                      │         │         ▼
  │                                      │         │    semiring.rs [core/log]
  │                                      │         │         ┊
  │                                      │         │         ┊ #[cfg(wfst-log)]
  │                                      │         │         ▼
  │                                      │         │    LogWeight
  │                                      │         │
  │                                      │         └──► compose.rs [core] ──► lib.rs [core]
  │                                      │
  └──────────────────────────────────────┴──► forward_backward.rs [log]
                                                    │
                                                    ├──► semiring.rs (LogWeight)
                                                    │
                                                    ▼
                                               log_push.rs [log] ──► forward_backward.rs [log]
                                                    │
                                                    └──► semiring.rs

                                               training.rs [log] ──► forward_backward.rs [log]
                                                    ├──► semiring.rs (LogWeight, TropicalWeight)
                                                    └──► serde_json (model I/O)
```

Reading the graph: a module on the left of `──►` imports from the module on the right.

---

## 8  Feature Gates

| Gate               | Modules Enabled | Semirings Added                    | Use Case                                                 |
|--------------------|-----------------|------------------------------------|----------------------------------------------------------|
| *(none — default)* | Layers 1–18     | 8 (Tropical through ProductWeight) | All compile-time analysis and runtime parsing            |
| `wfst-log`         | + Layers 19–21  | + LogWeight, EntropyWeight         | Probabilistic training, weight pushing, entropy analysis |

All dispatch, prediction, recovery, dead-rule detection, and lint analysis run **unconditionally**.  The `wfst-log` gate adds only statistical training and log-domain operations.

---

## 9  Deep-Dive Documents

### Architecture

| Topic                               | Document                                                                                          |
|-------------------------------------|---------------------------------------------------------------------------------------------------|
| Decision tree module map            | [decision-tree/module-map.md](../../architecture/decision-tree/module-map.md)                     |
| Decision tree pipeline integration  | [decision-tree/pipeline-integration.md](../../architecture/decision-tree/pipeline-integration.md) |
| Module inventory + dependency graph | [wfst/module-map.md](wfst/module-map.md)                                                          |
| Pipeline execution + data flow      | [wfst/pipeline-integration.md](wfst/pipeline-integration.md)                                      |
| Optimization pass inventory         | [wfst/optimization-pipeline.md](wfst/optimization-pipeline.md)                                    |
| NFA spillover thread-locals         | [wfst/nfa-spillover-architecture.md](wfst/nfa-spillover-architecture.md)                          |
| Recovery state propagation          | [wfst/recovery-state-propagation.md](wfst/recovery-state-propagation.md)                          |
| Token lattice integration           | [wfst/token-lattices.md](wfst/token-lattices.md)                                                  |
| Crate module graph                  | [crate-structure.md](crate-structure.md)                                                          |
| Full data-flow trace                | [data-flow.md](data-flow.md)                                                                      |

### Design

| Topic                         | Document                                                                                                      |
|-------------------------------|---------------------------------------------------------------------------------------------------------------|
| Four-tier dead-rule detection | [design/wfst/dead-rule-detection.md](../design/wfst/dead-rule-detection.md)                                   |
| Lint layer (23 lints)         | [design/lint-layer.md](../design/lint-layer.md)                                                               |
| Composed dispatch             | [design/composed-dispatch.md](../design/composed-dispatch.md)                                                 |
| Error recovery strategies     | [design/wfst/error-recovery.md](../design/wfst/error-recovery.md)                                             |
| NFA disambiguation            | [design/disambiguation/08-nfa-wfst-disambiguation.md](../design/disambiguation/08-nfa-wfst-disambiguation.md) |
| Grammar composition           | [design/wfst/grammar-composition.md](../design/wfst/grammar-composition.md)                                   |
| Cost-benefit framework        | [design/wfst/cost-benefit-framework.md](../design/wfst/cost-benefit-framework.md)                             |
| Recovery config DSL           | [design/wfst/recovery-config.md](../design/wfst/recovery-config.md)                                           |

### Theory

| Topic                         | Document                                                                                      |
|-------------------------------|-----------------------------------------------------------------------------------------------|
| Semiring axioms + instances   | [theory/wfst/semirings.md](../theory/wfst/semirings.md)                                       |
| Weighted automata foundations | [theory/wfst/weighted-automata.md](../theory/wfst/weighted-automata.md)                       |
| Viterbi + forward-backward    | [theory/wfst/viterbi-and-forward-backward.md](../theory/wfst/viterbi-and-forward-backward.md) |
| Composition correctness       | [theory/wfst/composition-correctness.md](../theory/wfst/composition-correctness.md)           |
| Cascade suppression           | [theory/wfst/cascade-suppression.md](../theory/wfst/cascade-suppression.md)                   |

### Per-Semiring Design + Theory

| Semiring         | Design                                                                                      | Theory                                                                                      |
|------------------|---------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------|
| TropicalWeight   | [design/wfst/semirings/tropical-weight.md](../design/wfst/semirings/tropical-weight.md)     | [theory/wfst/semirings/tropical-weight.md](../theory/wfst/semirings/tropical-weight.md)     |
| CountingWeight   | [design/wfst/semirings/counting-weight.md](../design/wfst/semirings/counting-weight.md)     | [theory/wfst/semirings/counting-weight.md](../theory/wfst/semirings/counting-weight.md)     |
| BooleanWeight    | [design/wfst/semirings/boolean-weight.md](../design/wfst/semirings/boolean-weight.md)       | [theory/wfst/semirings/boolean-weight.md](../theory/wfst/semirings/boolean-weight.md)       |
| EditWeight       | [design/wfst/semirings/edit-weight.md](../design/wfst/semirings/edit-weight.md)             | [theory/wfst/semirings/edit-weight.md](../theory/wfst/semirings/edit-weight.md)             |
| ContextWeight    | [design/wfst/semirings/context-weight.md](../design/wfst/semirings/context-weight.md)       | [theory/wfst/semirings/context-weight.md](../theory/wfst/semirings/context-weight.md)       |
| ComplexityWeight | [design/wfst/semirings/complexity-weight.md](../design/wfst/semirings/complexity-weight.md) | [theory/wfst/semirings/complexity-weight.md](../theory/wfst/semirings/complexity-weight.md) |
| NbestWeight      | [design/wfst/semirings/nbest-weight.md](../design/wfst/semirings/nbest-weight.md)           | [theory/wfst/semirings/nbest-weight.md](../theory/wfst/semirings/nbest-weight.md)           |
| ProductWeight    | [design/wfst/semirings/product-weight.md](../design/wfst/semirings/product-weight.md)       | [theory/wfst/semirings/product-weight.md](../theory/wfst/semirings/product-weight.md)       |
| LogWeight        | [design/wfst/semirings/log-weight.md](../design/wfst/semirings/log-weight.md)               | [theory/wfst/semirings/log-weight.md](../theory/wfst/semirings/log-weight.md)               |
| EntropyWeight    | [design/wfst/semirings/entropy-weight.md](../design/wfst/semirings/entropy-weight.md)       | [theory/wfst/semirings/entropy-weight.md](../theory/wfst/semirings/entropy-weight.md)       |

---

## 10  Debug Environment Variables

| Variable               | Values         | Effect                                       |
|------------------------|----------------|----------------------------------------------|
| `PRATTAIL_DUMP_EBNF`   | `1` or `/path` | Writes EBNF grammar before WFST construction |
| `PRATTAIL_DUMP_PARSER` | `1` or `/path` | Writes full generated parser source          |
