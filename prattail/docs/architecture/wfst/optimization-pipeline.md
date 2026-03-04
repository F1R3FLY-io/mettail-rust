# WFST Optimization Pipeline Architecture

**Date:** 2026-03-01

---

## Table of Contents

1. [Overview](#1-overview)
2. [Pipeline Integration Points](#2-pipeline-integration-points)
3. [Optimization Inventory](#3-optimization-inventory)
4. [Compile-Time vs Runtime Classification](#4-compile-time-vs-runtime-classification)
5. [Semiring Usage Map](#5-semiring-usage-map)
6. [Data Flow Diagram](#6-data-flow-diagram)
7. [Dependency Graph](#7-dependency-graph)
8. [Module Map](#8-module-map)
9. [Cost-Benefit Meta-Optimization](#9-cost-benefit-meta-optimization)
10. [Source References](#10-source-references)

---

## 1. Overview

PraTTaIL's WFST infrastructure enables 17 optimizations across 6 categories,
powered by 8 semirings (4 existing + 4 planned) and a meta-optimization
framework. This document describes how these optimizations fit into the
existing pipeline state machine:

```
LanguageSpec ──→ [Extract] ──→ Ready ──→ [Generate] ──→ Generated ──→ [Finalize] ──→ Complete
                 separate       LexerBundle ──→ lexer_code    concatenate + parse
                 bundles       ParserBundle ──→ parser_code   into TokenStream
```

Optimizations insert at three points:
- **Post-WFST construction** (compile-time analysis): D1, A4, A5
- **Codegen** (compile-time code transformation): F1, F2, A1, A2, B1
- **Runtime** (generated code behavior): B2, F3, B3

---

## 2. Pipeline Integration Points

The pipeline (`pipeline.rs`) executes these phases in order. Optimization
insertion points are marked with `◆`:

```
Extract LanguageSpec
    │
    ▼
Compute FIRST sets ──→ Compute FOLLOW sets
    │                        │
    ▼                        ▼
Build dispatch action tables
    │
    ▼
Build prediction WFSTs ──→ Apply beam width
    │
    ▼
Build recovery WFSTs
    │
    ▼
◆ Lint layer (run_lints)                    ← W01 dead-rule, W02 NFA ambiguity
    │
    ▼
◆ D1: Cost-benefit analysis                ← evaluates grammar profile
    │                                          recommends applicable optimizations
    ▼
◆ A2: Hot/cold arm partitioning            ← dispatch.rs codegen
    │
    ▼
◆ F1: Spillover pruning                    ← trampoline.rs NFA codegen
◆ F2: Early termination                    ← trampoline.rs NFA codegen
◆ B2: Running weight accumulation          ← trampoline.rs thread-locals + codegen
    │
    ▼
Write trampolined parsers per category
    │
    ▼
Write recovering parsers
    │
    ▼
Finalize (concatenate + parse TokenStream)
```

---

## 3. Optimization Inventory

| ID | Name                  | Category      | Complexity | Sprint |
|----|-----------------------|---------------|------------|--------|
| F1 | Spillover Pruning     | NFA Spillover | Trivial    | 1 ✓    |
| F2 | Early Termination     | NFA Spillover | Trivial    | 1 ✓    |
| A2 | Hot/Cold Splitting    | Compile-Time  | Low        | 1 ✓    |
| D1 | CostBenefit Framework | Meta          | Low        | 1 ✓    |
| B2 | Adaptive Recovery     | Runtime       | Low        | 1 ✓    |
| F3 | Lazy Spillover        | NFA Spillover | Medium     | 2      |
| C1 | ContextWeight         | Semiring      | Low-Med    | 2      |
| C2 | ComplexityWeight      | Semiring      | Low        | 2      |
| A4 | Enhanced DCE          | Compile-Time  | Low-Med    | 2      |
| A5 | Ambiguity Targeting   | Compile-Time  | Low        | 2      |
| B1 | Multi-Token Lookahead | Runtime       | Medium     | 3      |
| A1 | Left-Factoring        | Compile-Time  | Medium     | 3      |
| B3 | WFST Minimization     | Runtime       | Low        | 3      |
| C3 | EntropyWeight         | Semiring      | Medium     | 4      |
| C4 | Viterbi-N-Best        | Semiring      | Med-High   | 4      |
| E1 | Transducer Cascade    | Architecture  | High       | 4      |
| A3 | Composed DFA+Min      | Compile-Time  | High       | Future |

---

## 4. Compile-Time vs Runtime Classification

```
┌────────────────────────────────────────────────────────────┐
│  COMPILE-TIME                                              │
│                                                            │
│  Pipeline Analysis       Codegen Transformation            │
│  ┌─────────────────┐     ┌──────────────────────────────┐  │
│  │ D1 CostBenefit  │     │ A2 Hot/Cold Splitting        │  │
│  │ A4 Enhanced DCE │     │ A1 Left-Factoring            │  │
│  │ A5 Ambiguity    │     │ F1 Spillover Pruning         │  │
│  │    Targeting    │     │ F2 Early Termination         │  │
│  │                 │     │ A3 Composed DFA+Min          │  │
│  └─────────────────┘     └──────────────────────────────┘  │
│                                                            │
├────────────────────────────────────────────────────────────┤
│  RUNTIME                                                   │
│                                                            │
│  Generated Code          Infrastructure                    │
│  ┌─────────────────┐     ┌──────────────────────────────┐  │
│  │ B2 Adaptive     │     │ F3 Lazy Spillover            │  │
│  │    Recovery     │     │ B1 Multi-Token Lookahead     │  │
│  │ B3 WFST         │     │ E1 Transducer Cascade        │  │
│  │    Minimization │     │                              │  │
│  └─────────────────┘     └──────────────────────────────┘  │
│                                                            │
├────────────────────────────────────────────────────────────┤
│  SEMIRINGS                                                 │
│                                                            │
│  Existing                Planned                           │
│  ┌─────────────────┐     ┌──────────────────────────────┐  │
│  │ TropicalWeight  │     │ C1 ContextWeight (BitSet)    │  │
│  │ BooleanWeight   │     │ C2 ComplexityWeight          │  │
│  │ CountingWeight  │     │ C3 EntropyWeight (wfst-log)  │  │
│  │ EditWeight      │     │ C4 Viterbi-N-Best            │  │
│  │ ProductWeight   │     │                              │  │
│  └─────────────────┘     └──────────────────────────────┘  │
└────────────────────────────────────────────────────────────┘
```

---

## 5. Semiring Usage Map

Each optimization is powered by one or more semirings:

| Optimization      | Primary Semiring         | Secondary                | Purpose                   |
|-------------------|--------------------------|--------------------------|---------------------------|
| Dispatch ordering | TropicalWeight           | —                        | Sort arms by likelihood   |
| Dead-rule (W01)   | BooleanWeight            | —                        | Reachability analysis     |
| Ambiguity (W02)   | CountingWeight           | —                        | Alternative counting      |
| Recovery costs    | EditWeight               | —                        | Repair strategy selection |
| D1 CostBenefit    | ProductWeight⟨Trop,Trop⟩ | —                        | Speedup × cost ranking    |
| F1 Spillover      | TropicalWeight           | —                        | Beam-width filter         |
| B2 Adaptive       | TropicalWeight           | —                        | Accumulated confidence    |
| A4 Enhanced DCE   | BooleanWeight            | ProductWeight            | Forward-backward          |
| C1 Context        | ContextWeight (BitSet)   | —                        | Rule-set reachability     |
| C2 Complexity     | ComplexityWeight         | ProductWeight⟨Trop,Comp⟩ | Lookahead budget          |
| C3 Entropy        | EntropyWeight            | —                        | Parse distribution        |
| C4 N-Best         | ViterbiNBest             | —                        | Lazy disambiguation       |

---

## 6. Data Flow Diagram

```
┌─────────────────────────────────────────────────────────┐
│  LanguageSpec                                           │
│  ┌──────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │ RuleSpec │  │ CategorySpec │  │ BeamWidth    │       │
│  └─────┬────┘  └──────┬───────┘  └──────┬───────┘       │
│        │              │                 │               │
│        ▼              ▼                 │               │
│  ┌──────────────────────────┐           │               │
│  │ FIRST/FOLLOW set engine  │           │               │
│  └────────────┬─────────────┘           │               │
│               │                         │               │
│               ▼                         │               │
│  ┌──────────────────────────┐           │               │
│  │ Dispatch action tables   │           │               │
│  └────────────┬─────────────┘           │               │
│               │                         │               │
│               ▼                         ▼               │
│  ┌──────────────────────────────────────────────┐       │
│  │ PredictionWfst (per category)                │       │
│  │  ┌──────────┐ ┌──────────┐ ┌───────────────┐ │       │
│  │  │ States   │ │ Actions  │ │ beam_width    │ │       │
│  │  │ (2-level)│ │ (weighted│ │ (TropicalWt)  │ │       │
│  │  └────┬─────┘ └────┬─────┘ └───────┬───────┘ │       │
│  └───────┼────────────┼───────────────┼─────────┘       │
│          │            │               │                 │
│   ┌──────┴──────┬─────┴─────┬─────────┴──────┐          │
│   ▼             ▼           ▼                ▼          │
│  D1 Grammar  A2 Hot/Cold  F1 Beam     F2 Deterministic  │
│  Profile     Partition    Filter      Early-Exit        │
│   │                                                     │
│   ▼                                                     │
│  Recommended                                            │
│  Optimizations                                          │
│   │                                                     │
│   ▼                                                     │
│  Codegen: trampoline.rs, dispatch.rs                    │
│   │                                                     │
│   ▼                                                     │
│  Generated Parser Code                                  │
│  ┌────────────────────────────────────────────┐         │
│  │  Thread-locals:                            │         │
│  │  ├─ NFA_PREFIX_SPILL_CAT                   │         │
│  │  ├─ NFA_FORCED_PREFIX_CAT                  │         │
│  │  ├─ NFA_PRIMARY_WEIGHT_CAT                 │         │
│  │  ├─ RUNNING_WEIGHT_CAT  (B2)               │         │
│  │  └─ FRAME_STATE_CAT                        │         │
│  │                                            │         │
│  │  Functions:                                │         │
│  │  ├─ parse_<Cat>()          [hot path]      │         │
│  │  ├─ parse_<Cat>_cold()     [A2 cold path]  │         │
│  │  ├─ parse_<Cat>_own()      [trampoline]    │         │
│  │  ├─ parse_<Cat>_recovering() [B2 aware]    │         │
│  │  └─ running_weight_<cat>() [B2 accessor]   │         │
│  └────────────────────────────────────────────┘         │
└─────────────────────────────────────────────────────────┘
```

---

## 7. Dependency Graph

```
                      NFA Disambiguation (COMPLETE)
                     ╱           │            ╲
                    ╱            │             ╲
F1 (Spillover)   F2 (Early)   F3 (Lazy Spillover)
       │                              │
       └──────────────┬───────────────┘
                      │
D1 (CostBenefit) ─────┼──────────────────────────────────┐
                      │                                   │
breezy-orbiting   C1 (ContextWeight) ──→ A4 (DCE)       │
-aho (prereq)                                             ├──→ E1 (Cascade)
                                                          │
A5 (Ambiguity) ──→ C2 (Complexity) ──→ B1 (Lookahead) ──┘

A2 (Hot/Cold) ───────────────────── (independent)
B2 (Adaptive Recovery) ────────────  (independent)
C3 (Entropy) ──→ C4 (N-Best) ─────  (wfst-log gated)
```

Sprint 1 deliverables (F1, F2, A2, D1, B2) are all independent or have
completed prerequisites, enabling parallel implementation.

---

## 8. Module Map

### New Modules (Sprint 1)

| Module            | Purpose                        | Lines |
|-------------------|--------------------------------|-------|
| `cost_benefit.rs` | D1 meta-optimization framework | ~320  |

### Modified Modules (Sprint 1)

| Module          | Optimization | Change Description                               |
|-----------------|--------------|--------------------------------------------------|
| `trampoline.rs` | F1           | Beam-width filter in spillover codegen           |
| `trampoline.rs` | F2           | `if nfa_results.is_empty()` guard for weight-0.0 |
| `trampoline.rs` | B2           | `RUNNING_WEIGHT_CAT` thread-local + accumulation |
| `dispatch.rs`   | A2           | Cold-path partitioning with `#[cold]` helper     |
| `pipeline.rs`   | D1           | Grammar profiling + optimization recommendations |

### Planned Modules (Future Sprints)

| Module                             | Optimization   | Sprint |
|------------------------------------|----------------|--------|
| `semiring.rs` (additions)          | C1, C2, C3, C4 | 2, 4   |
| `wfst.rs` (extensions)             | B1, B3, E1     | 3, 4   |
| `forward_backward.rs` (extensions) | A4             | 2      |

---

## 9. Cost-Benefit Meta-Optimization

The D1 framework (`cost_benefit.rs`) uses `ProductWeight<TropicalWeight,
TropicalWeight>` to rank optimization candidates. The left component estimates
speedup (lower = more beneficial), the right estimates compile cost (lower =
cheaper). Lexicographic ordering ensures cheaper optimizations are preferred
among equally-beneficial alternatives.

### Decision Flow

```
Grammar Profile ──→ evaluate_optimizations() ──→ Ranked Candidates
                                                      │
                                                      ▼
                                              Filter: applicable == true
                                                      │
                                                      ▼
                                              Log recommended optimizations
```

### Profile Extraction

`build_grammar_profile()` computes metrics from pipeline data:

| Metric                     | Source                                 | Used By    |
|----------------------------|----------------------------------------|------------|
| `shared_prefix_ratio`      | NFA spillover categories / total       | A1         |
| `cold_fraction`            | WFST actions with weight ≥ 1.0 / total | A2         |
| `ambiguous_fraction`       | Tokens with >1 prediction / total      | A5, B1     |
| `ambiguous_count`          | Count of ambiguous tokens              | B1         |
| `nfa_spillover_categories` | `categories_needing_nfa_spillover()`   | F1, F2, F3 |
| `has_beam_width`           | `BeamWidthConfig::is_enabled()`        | F1         |
| `total_wfst_states`        | Sum of `wfst.states.len()`             | B3         |

---

## 10. Source References

| File                      | Content                                   |
|---------------------------|-------------------------------------------|
| `trampoline.rs:162-412`   | NFA merged prefix arm with F1/F2          |
| `trampoline.rs:1143-1195` | Thread-local declarations (NFA + B2)      |
| `trampoline.rs:1200-1210` | Wrapper function with B2 reset            |
| `trampoline.rs:2990-3025` | Recovery function with B2 weight reading  |
| `dispatch.rs:304-415`     | A2 hot/cold partitioning                  |
| `cost_benefit.rs`         | D1 framework (full module)                |
| `pipeline.rs:963-985`     | D1 integration point                      |
| `wfst.rs:198-228`         | `nfa_alternative_order()`, `beam_width()` |
| `wfst.rs:559-581`         | `compute_action_weight()` weight scale    |
| `semiring.rs:496-620`     | `ProductWeight` (used by D1)              |

### Related Documents

- [Prediction WFSTs](../../design/wfst/prediction.md) — 2-state WFST architecture
- [NFA Disambiguation](../../design/wfst/nfa-disambiguation.md) — Spillover + replay architecture
- [Spillover Pruning](../../design/wfst/spillover-pruning.md) — F1 beam filter
- [Early Termination](../../design/wfst/early-termination.md) — F2 deterministic skip
- [Hot/Cold Splitting](../../design/wfst/hot-cold-splitting.md) — A2 cold path
- [Cost-Benefit Framework](../../design/wfst/cost-benefit-framework.md) — D1 meta-optimization
- [Adaptive Recovery](../../design/wfst/adaptive-recovery.md) — B2 running weight
- [NFA Spillover Architecture](nfa-spillover-architecture.md) — Thread-local design
- [Semirings](../../theory/wfst/semirings.md) — Semiring inventory
