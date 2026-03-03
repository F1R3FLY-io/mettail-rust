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
4. [Token Lattices](theory/wfst/token-lattices.md) — Weighted DAG for lexical ambiguity, Viterbi, beam pruning, N-best
5. [Multi-Step Viterbi Recovery](theory/wfst/multi-step-viterbi-recovery.md) — Repair lattice, transposition edit, correctness
6. [Cascade Suppression](theory/wfst/cascade-suppression.md) — Absorbing-state model for error cascade prevention

**Theory — Per-Semiring:**

| Semiring | Feature | Document |
|----------|---------|----------|
| TropicalWeight | always | [theory/wfst/semirings/tropical-weight.md](theory/wfst/semirings/tropical-weight.md) |
| CountingWeight | always | [theory/wfst/semirings/counting-weight.md](theory/wfst/semirings/counting-weight.md) |
| BooleanWeight | always | [theory/wfst/semirings/boolean-weight.md](theory/wfst/semirings/boolean-weight.md) |
| EditWeight | always | [theory/wfst/semirings/edit-weight.md](theory/wfst/semirings/edit-weight.md) |
| ProductWeight | always | [theory/wfst/semirings/product-weight.md](theory/wfst/semirings/product-weight.md) |
| LogWeight | wfst-log | [theory/wfst/semirings/log-weight.md](theory/wfst/semirings/log-weight.md) |
| EntropyWeight | wfst-log | [theory/wfst/semirings/entropy-weight.md](theory/wfst/semirings/entropy-weight.md) |
| NbestWeight | always | [theory/wfst/semirings/nbest-weight.md](theory/wfst/semirings/nbest-weight.md) |

**Theory — Optimization:**

- [Optimization Transducer Cascade](theory/wfst/optimization-transducer-cascade.md) — E1 transducer cascade theory: OptimizationPass trait, composition, convergence

**Architecture:**

- [Module Map](architecture/wfst/module-map.md) — Module inventory, dependency graph, feature-gate matrix
- [Pipeline Integration](architecture/wfst/pipeline-integration.md) — WFST insertion point, data flow, codegen outputs
- [Token Lattice Integration](architecture/wfst/token-lattices.md) — Module dependencies, compile-time vs runtime, recovery/dispatch integration
- [Recovery State Propagation](architecture/wfst/recovery-state-propagation.md) — Thread-local state, pipeline integration, zero-overhead design

**Design:**

- [Prediction WFSTs](design/wfst/prediction.md) — Weight assignment, 2-state architecture, beam pruning
- [Error Recovery](design/wfst/error-recovery.md) — Edit-cost repair, 3-tier context, Viterbi recovery
- [Extended Recovery Strategies](design/wfst/extended-recovery-strategies.md) — New repair actions, multi-step Viterbi, cross-category recovery
- [RecoveryConfig](design/wfst/recovery-config.md) — Tunable recovery parameters and trained weights
- [Grammar Composition](design/wfst/grammar-composition.md) — Language union, WFST-aware merging
- [Dead-Rule Detection](design/wfst/dead-rule-detection.md) — Three-tier analysis: literal, category-reachability, WFST dispatch
- [Weight Training](design/wfst/weight-training.md) — LogWeight SGD, forward-backward, trained models (`wfst-log`)
- [Token Lattices](design/wfst/token-lattices.md) — Two-path abstraction, generic semiring parametrization, algorithm trade-offs

**Design — Per-Semiring:**

| Semiring | Document |
|----------|----------|
| TropicalWeight | [design/wfst/semirings/tropical-weight.md](design/wfst/semirings/tropical-weight.md) |
| CountingWeight | [design/wfst/semirings/counting-weight.md](design/wfst/semirings/counting-weight.md) |
| BooleanWeight | [design/wfst/semirings/boolean-weight.md](design/wfst/semirings/boolean-weight.md) |
| EditWeight | [design/wfst/semirings/edit-weight.md](design/wfst/semirings/edit-weight.md) |
| ProductWeight | [design/wfst/semirings/product-weight.md](design/wfst/semirings/product-weight.md) |
| LogWeight | [design/wfst/semirings/log-weight.md](design/wfst/semirings/log-weight.md) |
| EntropyWeight | [design/wfst/semirings/entropy-weight.md](design/wfst/semirings/entropy-weight.md) |
| NbestWeight | [design/wfst/semirings/nbest-weight.md](design/wfst/semirings/nbest-weight.md) |

**Usage:**

- [Feature Gates](usage/wfst/feature-gates.md) — Two-tier model (default + wfst-log), test counts
- [DSL Configuration](usage/wfst/dsl-configuration.md) — `beam_width`, `log_semiring_model_path`
- [Training Guide](usage/wfst/training-guide.md) — Corpus preparation, SGD training, model serialization (`wfst-log`)
- [Recovery Tuning Guide](usage/wfst/recovery-tuning.md) — Parameter tuning, diagnostics interpretation, trained weights

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
- [Semiring Overview](theory/wfst/semirings.md) — Eight semirings for weighted parsing
- [Feature Gates](usage/wfst/feature-gates.md) — Two-tier feature model
