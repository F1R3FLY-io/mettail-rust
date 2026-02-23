# Weighted Finite-State Transducers in PraTTaIL

**Date:** 2026-02-22

This document is the entry point for the WFST documentation suite. It
explains why weighted parsing matters, describes how PraTTaIL layers WFST
support onto its core automata, and provides a navigation map to every
sub-document in the suite.

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [Feature Tiers](#2-feature-tiers)
3. [Architecture Overview](#3-architecture-overview)
4. [Document Navigation](#4-document-navigation)
5. [Prerequisites](#5-prerequisites)

---

## 1. Motivation

A conventional finite-state parser answers a binary question: does this
input belong to the language? That is sufficient for correct programs, but
real-world parsing must handle three harder problems.

### 1.1 Disambiguation

Many grammars admit more than one parse for a given input. Operator
precedence and associativity resolve some ambiguities structurally, but
others require external knowledge — for example, preferring the
shift over the reduce in a context where user intent is unclear, or ranking
one interpretation over another based on learned frequency. Assigning a
weight (probability, cost, or log-likelihood) to each path through the
automaton turns disambiguation into a shortest-path problem over a
semiring-weighted graph.

### 1.2 Error Recovery

When the lexer or parser encounters unexpected input it must recover
gracefully rather than abort. Unweighted recovery relies on hand-coded sync
predicates and heuristic skip rules. Weighted recovery treats deletions,
insertions, and substitutions as edit operations with associated costs,
computing the minimum-cost repair path through a failure lattice. This
yields more principled recovery with tunable error budgets.

### 1.3 Training and Adaptation

Weights can be estimated from a corpus of source files using the
forward-backward (Baum-Welch) algorithm or direct frequency counting. A
trained model captures project-specific idioms — for example, that a
particular DSL almost always uses keyword `let` rather than `var` in a
certain position — and uses that signal to improve both parse ranking and
error messages. Serialized `TrainedModel` instances can be loaded at
compile time to influence generated dispatch tables, or embedded as static
data for runtime weight override via `PredictionWfst::with_trained_weights()`.

### 1.4 Design Philosophy

WFST support is strictly opt-in. The zero-feature build compiles 150 tests
and adds no WFST code to generated parsers. Each feature tier is additive:
enabling `wfst` brings in the structural machinery; enabling `wfst-log`
adds the numerically stable log-semiring needed for probabilistic
training. Parsers that do not need weighted parsing pay no compile-time or
run-time cost.

---

## 2. Feature Tiers

| Tier      | Feature Flag          | Modules Added                                        | Test Count |
|-----------|-----------------------|------------------------------------------------------|------------|
| None      | (default)             | Core automata + Pratt/RD parser                      | 150        |
| WFST      | `--features wfst`     | `wfst`, `token_id`, `lattice`, `recovery`, `compose` | 254        |
| WFST-Log  | `--features wfst-log` | `forward_backward`, `log_push`, `training`           | 288        |

`wfst-log` implies `wfst`; enabling only `wfst-log` in `Cargo.toml`
automatically activates the full WFST tier as well.

Activating `wfst` at the workspace level propagates through the `macros`
and `languages` crates so that the proc-macro pipeline can emit
WFST-augmented dispatch tables and recovery functions automatically.

---

## 3. Architecture Overview

The WFST subsystem sits across four layers. Vertical arrows show data
flow; horizontal connections show module dependencies. Dotted characters
mark the points where a vertical flow crosses a horizontal boundary.

```
  ┌───────────────────────────────────────────────────────────────────┐
  │  Layer 4 — DSL                                                    │
  │                                                                   │
  │   language! { options { beam_width: 1.5,                         │
  │                          log_semiring_model_path: "model.json" } }│
  │                    │                   │                          │
  └────────────────────┼───────────────────┼──────────────────────────┘
                       │                   │
  ┌────────────────────┼───────────────────┼──────────────────────────┐
  │  Layer 3 — Pipeline│                   │                          │
  │                    ▼                   ▼                          │
  │   FIRST/FOLLOW ──► Dispatch Tables ──► WFST Build ──► Codegen    │
  │        │               │    │               │    │        │      │
  │        └───────────────┘    │               └────┊────────┘      │
  │                             │                    │               │
  └─────────────────────────────┊────────────────────┊───────────────┘
                                │                    │
  ┌─────────────────────────────┊────────────────────┊───────────────┐
  │  Layer 2 — Core             │                    │               │
  │                             ▼                    ▼               │
  │   PredictionWfst ◄──── TokenLattice ◄──── RecoveryWfst           │
  │         │                   ┊                    │               │
  │         └──────► Composition┊◄───────────────────┘               │
  │                             ┊                                    │
  └─────────────────────────────┊────────────────────────────────────┘
                                ┊
  ┌─────────────────────────────╂────────────────────────────────────┐
  │  Layer 1 — Theory           ▼                                    │
  │                                                                   │
  │   Semirings ──► Weighted Automata ──► Viterbi / Forward-Backward │
  │                                                                   │
  └───────────────────────────────────────────────────────────────────┘
```

**Layer 1 — Theory** provides the algebraic foundations. A semiring
`(K, ⊕, ⊗, 0̄, 1̄)` supplies the tropical or log-probability weight
domain. Weighted automata assign semiring elements to transitions.
Viterbi finds the minimum-cost path; forward-backward accumulates
posterior counts for training.

**Layer 2 — Core** implements the runtime structures. `PredictionWfst`
represents the prediction lattice constructed from FIRST sets and
dispatch tables; `from_flat()` reconstructs it from CSR static arrays
embedded in generated code. `TokenLattice` holds the weighted chart of
token hypotheses. `RecoveryWfst` encodes edit-cost transitions for error
repair; `from_flat()` reconstructs it from embedded sync token arrays.
`compose` implements the WFST composition algorithm used to combine
prediction and recovery automata.

**Layer 3 — Pipeline** wires the core modules into the PraTTaIL
compile-time pipeline. After FIRST/FOLLOW sets are computed, the
pipeline builds dispatch action tables, constructs the prediction and
recovery WFSTs, serializes them as CSR static arrays
(`emit_prediction_wfst_static()`, `emit_recovery_wfst_static()`), and
emits feature-gated codegen for weighted dispatch arms, recovery
functions with full 4-strategy context-aware repair, and
`LazyLock<PredictionWfst>` / `LazyLock<RecoveryWfst>` constructors
for runtime access.

**Layer 4 — DSL** exposes user-facing knobs. `beam_width` controls how
many hypotheses the beam-pruning step retains; `log_semiring_model_path`
points to a serialized `TrainedModel` JSON file; both fields are parsed
by the `options { }` block in the `language!` macro.

---

## 4. Document Navigation

### 4.1 Theory

| Document                                                   | Description                                                                  |
|------------------------------------------------------------|------------------------------------------------------------------------------|
| [theory/semirings.md](theory/semirings.md)                                               | Semiring axioms, tropical and log-probability instances, numerical stability |
| [theory/weighted-automata.md](theory/weighted-automata.md)                               | Weighted NFA/DFA, transition weight assignment, path weight multiplication   |
| [theory/viterbi-and-forward-backward.md](theory/viterbi-and-forward-backward.md)         | Viterbi shortest-path and forward-backward (Baum-Welch) algorithms, posterior computation, convergence |

### 4.2 Architecture

| Document                                                                             | Description                                                           |
|--------------------------------------------------------------------------------------|-----------------------------------------------------------------------|
| [architecture/module-map.md](architecture/module-map.md)                             | Module inventory, dependency graph, and feature-gate matrix           |
| [architecture/pipeline-integration.md](architecture/pipeline-integration.md)         | WFST insertion point in the pipeline, data flow, codegen outputs      |
| [design/prediction.md](design/prediction.md)                                         | Construction of `PredictionWfst` from FIRST sets and dispatch tables  |
| [theory/viterbi-and-forward-backward.md](theory/viterbi-and-forward-backward.md)     | `TokenLattice` chart representation, beam-pruning mechanics           |
| [design/error-recovery.md](design/error-recovery.md)                                 | Edit-cost encoding in `RecoveryWfst`, tier-3 context recovery         |
| [design/grammar-composition.md](design/grammar-composition.md)                       | WFST composition algorithm, on-the-fly construction, epsilon handling |

### 4.3 Design

| Document                                                                             | Description                                                                              |
|--------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| [architecture/pipeline-integration.md](architecture/pipeline-integration.md)         | How WFST modules hook into `generate_parser_code()` in `pipeline.rs`                     |
| [architecture/pipeline-integration.md](architecture/pipeline-integration.md)         | Weighted dispatch codegen: `write_prefix_match_arms`, `write_category_dispatch_weighted` |
| [usage/dsl-configuration.md](usage/dsl-configuration.md)                             | `BeamWidthConfig` enum (`Disabled`, `Explicit`, `Auto`), DSL parsing, auto mode          |

### 4.4 Usage

| Document                                                         | Description                                                                    |
|------------------------------------------------------------------|--------------------------------------------------------------------------------|
| [usage/feature-gates.md](usage/feature-gates.md)                 | Enabling WFST features, minimal example with beam pruning, expected output     |
| [usage/training-guide.md](usage/training-guide.md)               | Collecting a corpus, running forward-backward, serializing `TrainedModel` JSON |
| usage/troubleshooting.md                                          | Common WFST errors, feature-flag pitfalls, weight underflow diagnosis          |

---

## 5. Prerequisites

The WFST documentation assumes familiarity with the following concepts.
Each is either covered in the linked document or explained in the theory
tier of this suite.

**From core PraTTaIL** (covered in `prattail/docs/`):

- Pratt parsing: binding-power pairs, prefix/infix/postfix handler
  dispatch. See [theory/pratt-parsing.md](../../theory/pratt-parsing.md).
- PraTTaIL pipeline basics: `LanguageSpec` → pipeline stages →
  `TokenStream`. See
  [design/architecture-overview.md](../../design/architecture-overview.md).
- Prediction engine: FIRST/FOLLOW sets, dispatch tables, sync predicates.
  See [design/prediction-engine.md](../../design/prediction-engine.md).

**From algebra** (covered in [theory/semirings.md](theory/semirings.md)):

- Semiring axioms: two binary operations `⊕` (addition) and `⊗`
  (multiplication) over a set K with identities `0̄` and `1̄`.
- Tropical semiring: `(ℝ ∪ {+∞}, min, +, +∞, 0)` — weights are costs,
  best path minimizes total cost.
- Log-probability semiring: `(ℝ ∪ {-∞}, log-sum-exp, +, -∞, 0)` —
  weights are log-probabilities, best path maximizes total probability.

Readers comfortable with finite automata and graph shortest-path algorithms
will find the WFST material accessible without prior exposure to formal
language theory. The theory documents are self-contained and build from
first principles.
