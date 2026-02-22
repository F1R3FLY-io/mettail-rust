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

---

## Documentation by Category

| Directory | Contents |
|---|---|
| [architecture/](architecture/) | Crate structure, data flow, generated code anatomy |
| [benchmarks/](benchmarks/) | Parse performance comparison, optimization ledger |
| [design/](design/) | Pipeline, engines, generators, disambiguation |
| [theory/](theory/) | Formal foundations: automata, prediction, Pratt parsing |
| [usage/](usage/) | Quick start, grammar features, EBNF dump, troubleshooting |

---

## Quick Links

- [EBNF Dump](usage/ebnf-dump.md) — Debug grammar definitions with EBNF output
- [Troubleshooting](usage/troubleshooting.md) — Solve common problems
- [Generated Code Anatomy](architecture/generated-code-anatomy.md) — Annotated walkthrough of generated parser code
- [Parse Performance](benchmarks/parse-performance.md) — PraTTaIL vs LALRPOP benchmarks
- [Optimization Ledger](benchmarks/optimization-ledger.md) — Scientific record of all optimization experiments
