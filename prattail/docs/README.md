# PraTTaIL Documentation

**PraTTaIL** (Pratt + Tail = Pratt-based parser generator with tail-call
optimization) is a compile-time parser generator that combines Pratt parsing,
recursive descent, and prediction-driven dispatch to produce fast, stack-safe
parsers from HOL-style language definitions.

---

## Reading Order

### New to PraTTaIL?

1. [Quick Start Guide](usage/quick-start.md) — Define a language, parse input, inspect results
2. [Grammar Features Reference](usage/grammar-features.md) — Complete DSL syntax reference
3. [Troubleshooting](usage/troubleshooting.md) — Common issues and solutions

### Understanding the Theory

1. [Finite Automata](theory/finite-automata.md) — NFA/DFA construction, Hopcroft minimization, maximal munch
2. [Prediction and Lookahead](theory/prediction-and-lookahead.md) — FIRST/FOLLOW sets, dispatch tables, comparison with LL/LR
3. [Pratt Parsing](theory/pratt-parsing.md) — Binding power pairs, precedence, associativity
4. [Disambiguation (overview)](design/disambiguation/README.md) — Six-layer model for resolving parse ambiguity

### Deep-Dive Design

1. [Architecture Overview](design/architecture-overview.md) — Pipeline phases, module structure, data flow
2. [Automata Pipeline](design/automata-pipeline.md) — Lexer generation: Thompson, subset construction, compression
3. [Prediction Engine](design/prediction-engine.md) — FIRST/FOLLOW computation, dispatch tables, sync predicates
4. [Pratt Generator](design/pratt-generator.md) — Rule classification, BP assignment, Pratt codegen
5. [Recursive Descent Generator](design/recursive-descent-generator.md) — Structural rules, binders, collections, lambda/dollar
6. [Cross-Category Dispatch](design/cross-category-dispatch.md) — Cast rules, FIRST set overlap, backtracking

### Weighted Parsing (WFST)

All grammars benefit from WFST-weighted dispatch — prediction WFSTs, weighted
recovery, and dead-rule detection are always active. The `wfst-log` feature
adds probabilistic training via the log semiring.

**Theory — Foundations:**

1. [Semirings Overview](theory/wfst/semirings.md) — Axioms, instances, numerical stability
2. [Weighted Automata](theory/wfst/weighted-automata.md) — WFST structure, TokenId, PredictionWfst
3. [Viterbi and Forward-Backward](theory/wfst/viterbi-and-forward-backward.md) — Shortest-path, beam pruning, N-best

**Theory — Per-Semiring:**

| Semiring | Feature | Document |
|----------|---------|----------|
| TropicalWeight | always | [theory/wfst/semirings/tropical-weight.md](theory/wfst/semirings/tropical-weight.md) |
| CountingWeight | always | [theory/wfst/semirings/counting-weight.md](theory/wfst/semirings/counting-weight.md) |
| BooleanWeight | always | [theory/wfst/semirings/boolean-weight.md](theory/wfst/semirings/boolean-weight.md) |
| EditWeight | always | [theory/wfst/semirings/edit-weight.md](theory/wfst/semirings/edit-weight.md) |
| ProductWeight | always | [theory/wfst/semirings/product-weight.md](theory/wfst/semirings/product-weight.md) |
| LogWeight | wfst-log | [theory/wfst/semirings/log-weight.md](theory/wfst/semirings/log-weight.md) |

**Architecture:**

- [Module Map](architecture/wfst/module-map.md) — Module inventory, dependency graph, feature-gate matrix
- [Pipeline Integration](architecture/wfst/pipeline-integration.md) — WFST insertion point, data flow, codegen outputs

**Design:**

- [Prediction WFSTs](design/wfst/prediction.md) — Weight assignment, 2-state architecture, beam pruning
- [Error Recovery](design/wfst/error-recovery.md) — Edit-cost repair, 3-tier context, Viterbi recovery
- [Grammar Composition](design/wfst/grammar-composition.md) — Language union, WFST-aware merging
- [Weight Training](design/wfst/weight-training.md) — LogWeight SGD, forward-backward, trained models (`wfst-log`)

**Design — Per-Semiring:**

| Semiring | Document |
|----------|----------|
| TropicalWeight | [design/wfst/semirings/tropical-weight.md](design/wfst/semirings/tropical-weight.md) |
| CountingWeight | [design/wfst/semirings/counting-weight.md](design/wfst/semirings/counting-weight.md) |
| BooleanWeight | [design/wfst/semirings/boolean-weight.md](design/wfst/semirings/boolean-weight.md) |
| EditWeight | [design/wfst/semirings/edit-weight.md](design/wfst/semirings/edit-weight.md) |
| ProductWeight | [design/wfst/semirings/product-weight.md](design/wfst/semirings/product-weight.md) |
| LogWeight | [design/wfst/semirings/log-weight.md](design/wfst/semirings/log-weight.md) |

**Usage:**

- [Feature Gates](usage/wfst/feature-gates.md) — Two-tier model (default + wfst-log), test counts
- [DSL Configuration](usage/wfst/dsl-configuration.md) — `beam_width`, `log_semiring_model_path`
- [Training Guide](usage/wfst/training-guide.md) — Corpus preparation, SGD training, model serialization (`wfst-log`)

---

## Documentation by Category

| Directory                      | Contents                                                    |
|--------------------------------|-------------------------------------------------------------|
| [architecture/](architecture/) | Crate structure, data flow, generated code anatomy, WFST module map |
| [benchmarks/](benchmarks/)     | Parse performance comparison, optimization ledger           |
| [design/](design/)             | Pipeline, engines, generators, disambiguation, WFST design  |
| [theory/](theory/)             | Formal foundations: automata, prediction, Pratt, semirings   |
| [usage/](usage/)               | Quick start, grammar features, EBNF dump, troubleshooting, WFST config |

---

## Quick Links

- [EBNF Dump](usage/ebnf-dump.md) — Debug grammar definitions with EBNF output
- [Troubleshooting](usage/troubleshooting.md) — Solve common problems
- [Generated Code Anatomy](architecture/generated-code-anatomy.md) — Annotated walkthrough of generated parser code
- [Parse Performance](benchmarks/parse-performance.md) — PraTTaIL vs LALRPOP benchmarks
- [Optimization Ledger](benchmarks/optimization-ledger.md) — Scientific record of all optimization experiments
- [WFST Pipeline Benchmarks](benchmarks/wfst-pipeline-integration.md) — Always-on WFST performance impact
- [Semiring Overview](theory/wfst/semirings.md) — Six semirings for weighted parsing
- [Feature Gates](usage/wfst/feature-gates.md) — Two-tier feature model
