# Analysis Pipeline Overview

| Field   | Value                     |
|---------|---------------------------|
| Date    | 2026-03-09                |
| Status  | Reference documentation   |

---

## Table of Contents

- [1 Architecture Overview](#1-architecture-overview)
- [2 Analysis Module Dependency DAG](#2-analysis-module-dependency-dag)
- [3 Feature Gate Matrix](#3-feature-gate-matrix)
- [4 Pipeline Execution Phases](#4-pipeline-execution-phases)
- [5 Semiring Usage Matrix](#5-semiring-usage-matrix)
- [6 Data Flow: Analysis to Diagnostics](#6-data-flow-analysis-to-diagnostics)
- [7 CtxBuilder Integration: LintContext Fields](#7-ctxbuilder-integration-lintcontext-fields)
- [8 Cost-Benefit Framework](#8-cost-benefit-framework)
- [9 Worked Example: Grammar Through the Pipeline](#9-worked-example-grammar-through-the-pipeline)
- [References](#references)

---

## 1 Architecture Overview

PraTTaIL's analysis pipeline transforms a `LanguageSpec` (the grammar declaration from
`language! { ... }`) into generated Rust code through seven sequential phases, with 23
analysis modules contributing diagnostics, optimization decisions, and correctness
guarantees along the way.

The pipeline is implemented in `prattail/src/pipeline.rs` as function
`generate_parser_code()`, which is invoked by `run_pipeline_with_analysis()`. The
function is approximately 1,500 lines and executes the phases in strict order with
well-defined data dependencies between them.

```text
╔══════════════════════════════════════════════════════════════════════════════╗
║                     PraTTaIL Analysis Pipeline                              ║
║                                                                             ║
║  language! { ... }                                                          ║
║       │                                                                     ║
║       ▼                                                                     ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 1: Extract    │  LanguageSpec → LexerBundle + ParserBundle          ║
║  │   extract_from_spec │  (main thread, !Send isolation)                    ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 2: Core       │  FIRST sets → FOLLOW sets → overlaps               ║
║  │   FIRST/FOLLOW/BP   │  DB01: incremental mode for >=3 categories         ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 3: WFST       │  PredictionWfst + RecoveryWfst per category        ║
║  │   construction +    │  Transducer cascade, beam width, ContextWeight     ║
║  │   optimization      │  B3: minimization gate (>4 states)                 ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 4: Decision   │  PathMap trie per category                         ║
║  │   tree construction │  Segment splitting at NT boundaries                ║
║  │   + diagnostics     │  D01-D09 diagnostics, weight adjustment            ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 5: Analysis   │  WPDS + 15 feature-gated analysis modules          ║
║  │   modules           │  DB03: parallel execution via std::thread::scope   ║
║  │   (feature-gated)   │  DB02: lazy skip for <3 categories                 ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 6: Lint       │  LintContext aggregation → run_lints()             ║
║  │   aggregation       │  DB04: cached lint results                         ║
║  │   + repair          │  Repair enrichment, proof certificates             ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║  ┌─────────────────────┐                                                    ║
║  │ Phase 7: Codegen    │  RD handlers, Pratt parsers, dispatch tables       ║
║  │   emission          │  Trampoline, recovery, WFST static embedding       ║
║  └────────┬────────────┘                                                    ║
║           │                                                                 ║
║           ▼                                                                 ║
║     TokenStream + PipelineAnalysis                                          ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

## 2 Analysis Module Dependency DAG

The 23 analysis modules are organized into five categories with explicit
dependency relationships. Modules within a category can generally execute
in parallel; cross-category dependencies are shown with arrows.

```text
 ┌──────────────────────────────────────────────────────────────────────────┐
 │                        Always-On Core                                    │
 │                                                                          │
 │  ┌──────────────┐  ┌─────────────┐  ┌──────────────────┐               │
 │  │  algebraic    │  │   verify    │  │      cegar       │               │
 │  │  (Tarjan path │  │  (prestar   │  │   (abstraction   │               │
 │  │  expressions) │  │  safety)    │  │   refinement)    │               │
 │  └──────┬───────┘  └──────┬──────┘  └────────┬─────────┘               │
 │         │                 │                   │                          │
 │         └─────────────────┼───────────────────┘                         │
 │                           │                                              │
 │                    ┌──────┴──────┐                                       │
 │                    │    wpds     │ ◄── poststar/prestar saturation       │
 │                    │   (core)   │                                        │
 │                    └──────┬──────┘                                       │
 │                           │                                              │
 │  ┌────────────────────────┴──────────────────────────────────┐          │
 │  │          forward_backward  /  newton  /  repair           │          │
 │  │         (semiring-generic, always available)              │          │
 │  └───────────────────────────────────────────────────────────┘          │
 └──────────────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────────────┐
 │                      TRS Category                                        │
 │                    (feature: trs-analysis)                                │
 │                                                                          │
 │  ┌──────────────┐  ┌──────────────┐                                     │
 │  │  confluence   │  │ termination  │                                     │
 │  │ (critical     │  │ (dependency  │                                     │
 │  │  pairs, K-B)  │  │  pairs)      │                                     │
 │  └──────────────┘  └──────────────┘                                     │
 └──────────────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────────────┐
 │                    Automata Category                                      │
 │                                                                          │
 │  ┌──────────┐  ┌──────────────┐  ┌─────────────┐  ┌──────────┐         │
 │  │   vpa    │  │tree_automaton│  │ alternating  │  │  buchi   │         │
 │  │(feature: │  │ (feature:    │  │  (feature:   │  │(feature: │         │
 │  │  vpa)    │  │ tree-automata│  │ alternating) │  │  omega)  │         │
 │  └──────────┘  └──────────────┘  └─────────────┘  └────┬─────┘         │
 │                                                         │               │
 │  ┌──────────┐                                    ┌──────┴─────┐         │
 │  │ nominal  │                                    │    ltl     │         │
 │  │(feature: │                                    │ (feature:  │         │
 │  │ nominal) │                                    │   ltl)     │         │
 │  └──────────┘                                    └────────────┘         │
 └──────────────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────────────┐
 │                      WPDS Extensions                                     │
 │                                                                          │
 │  ┌──────────┐  ┌──────────────┐                                         │
 │  │  ewpds   │  │     ara      │                                         │
 │  │(feature: │  │  (feature:   │                                         │
 │  │ wpds-    │  │  wpds-ara)   │──── depends on wpds-relational          │
 │  │extended) │  └──────────────┘                                         │
 │  └──────────┘                                                            │
 └──────────────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────────────┐
 │                   Domain-Specific Analysis                                │
 │                                                                          │
 │  ┌──────────┐  ┌──────────────┐  ┌──────────┐  ┌──────────┐            │
 │  │  petri   │  │  provenance  │  │   cra    │  │  tensor  │            │
 │  │(feature: │  │  (feature:   │  │(feature: │  │ (always  │            │
 │  │  petri)  │  │  provenance) │  │   cra)   │  │   on)    │            │
 │  └──────────┘  └──────────────┘  └──────────┘  └──────────┘            │
 └──────────────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────────────┐
 │                        Meta Category                                     │
 │                                                                          │
 │  ┌──────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────┐        │
 │  │   kat    │  │   morphism   │  │ proof_output  │  │  repair  │        │
 │  │(feature: │  │  (feature:   │  │  (feature:    │  │ (always  │        │
 │  │   kat)   │  │  morphisms)  │  │   proofs)     │  │   on)    │        │
 │  └──────────┘  └──────────────┘  └──────────────┘  └──────────┘        │
 └──────────────────────────────────────────────────────────────────────────┘
```

**Dependency edges:**
- `ltl` depends on `buchi` (omega feature)
- `ara` depends on `wpds-relational`
- `proofs` depends on `provenance`
- `verify`, `cegar`, `algebraic`, `ewpds`, `ara`, `ltl`, `kat` all depend on WPDS core output
- `confluence`, `termination`, `vpa`, `tree_automaton`, `petri`, `nominal`, `alternating`, `provenance`, `cra`, `morphism` have no cross-module dependencies

---

## 3 Feature Gate Matrix

Each row is an analysis module; columns indicate which feature flag(s) enable it.
"Always-on" modules compile unconditionally.

| Module            | Feature Gate       | Convenience Groups                                |
|-------------------|--------------------|---------------------------------------------------|
| `wpds`            | always-on          | --                                                |
| `verify`          | always-on          | --                                                |
| `cegar`           | always-on          | --                                                |
| `algebraic`       | always-on          | --                                                |
| `newton`          | always-on          | --                                                |
| `forward_backward`| always-on          | --                                                |
| `repair`          | always-on          | --                                                |
| `tensor`          | always-on          | --                                                |
| `confluence`      | `trs-analysis`     | `analysis`, `full-analysis`                       |
| `termination`     | `trs-analysis`     | `analysis`, `full-analysis`                       |
| `vpa`             | `vpa`              | `analysis`, `full-analysis`                       |
| `tree_automaton`  | `tree-automata`    | `analysis`, `full-analysis`                       |
| `buchi`           | `omega`            | `verification`, `process-algebra`, `full-analysis`|
| `ltl`             | `ltl` (implies `omega`) | `verification`, `full-analysis`              |
| `alternating`     | `alternating`      | `process-algebra`, `full-analysis`                |
| `nominal`         | `nominal`          | `process-algebra`, `full-analysis`                |
| `petri`           | `petri`            | `process-algebra`, `full-analysis`                |
| `cra`             | `cra`              | `full-analysis`                                   |
| `provenance`      | `provenance`       | `full-analysis`                                   |
| `kat`             | `kat`              | `verification`, `full-analysis`                   |
| `morphism`        | `morphisms`        | `full-analysis`                                   |
| `proof_output`    | `proofs` (implies `provenance`) | `full-analysis`                      |
| `ewpds`           | `wpds-extended`    | `full-analysis`                                   |
| `ara`             | `wpds-ara` (implies `wpds-relational`) | `full-analysis`              |
| `relational`      | `wpds-relational`  | `verification`, `full-analysis`                   |

**Additional non-analysis feature gates:**

| Feature            | Purpose                                              |
|--------------------|------------------------------------------------------|
| `wfst-log`         | LogWeight semiring, forward-backward, training       |
| `quantum`          | AmplitudeWeight complex semiring (CTMC simulation)   |
| `grammar-gen`      | Proptest-based expression generator                  |
| `simd-whitespace`  | AL03: portable SIMD whitespace skipping (nightly)    |

---

## 4 Pipeline Execution Phases

### Phase 1: Bundle Extraction

**Function:** `extract_from_spec(spec) -> (LexerBundle, ParserBundle)`

**Location:** `pipeline.rs:1071-1318`

Runs on the main thread to isolate `!Send` types (`proc_macro2::TokenStream`)
from the generation phase. Extracts:

- `LexerBundle`: grammar rules, type infos, literal patterns
- `ParserBundle`: categories, binding power table, rule infos, FOLLOW inputs,
  RD rules, cross-category rules, cast rules, syntax triples, source locations,
  semantic dependency groups, beam width, recovery config

All bundle fields are `Send + Sync`, enabling future parallelism.

### Phase 2: Core Analysis (FIRST/FOLLOW/BP)

**Location:** `pipeline.rs:1786-1857`

1. **FIRST set computation** -- Fixed-point iteration over rule first-items.
   DB01 gate: incremental mode (`compute_first_sets_incremental`) for grammars
   with >=3 categories uses dirty-flag convergence to skip unchanged categories
   on each iteration.

2. **FIRST set augmentation** -- Adds `Ident`, `LParen`, native-type literals
   (`Integer`, `Float`, `Boolean`, `StringLit`), and binder tokens (`Caret`,
   `Dollar*`) to appropriate category FIRST sets.

3. **Cross-category overlap analysis** -- `analyze_cross_category_overlaps()`
   computes which FIRST set tokens are shared between categories.

4. **FOLLOW set computation** -- Fixed-point iteration over rule syntax items.
   DB01 gate: incremental mode with per-category dirty tracking.

### Phase 3: WFST Construction and Optimization

**Location:** `pipeline.rs:1904-2125`

1. **Dispatch action tables** -- `build_dispatch_action_tables()` creates
   structured action data from FIRST sets, RD rules, cross-category rules,
   cast rules, and native type information.

2. **Prediction WFSTs** -- `build_prediction_wfsts()` creates per-category
   weighted transducers mapping dispatch tokens to parse actions with
   TropicalWeight ordering.

3. **Two-token enrichment** -- `enrich_with_two_token_paths()` adds 2-token
   disambiguation paths for NFA-ambiguous groups where the second position
   uniquely identifies the rule.

4. **ContextWeight assignment** -- Sequential bit IDs assigned to rule labels
   in each WFST for `live_rules_context_after()` tracking.

5. **Transducer cascade** -- B3 gate (>4 WFST states): weight normalization,
   dead-state elimination, and minimization until convergence.

6. **Beam width** -- Applied from `BeamWidthConfig`:
   - `Explicit(w)`: fixed TropicalWeight beam on all WFSTs
   - `Auto`: per-category entropy-based beam (requires `wfst-log`)
   - `Disabled`: no pruning

7. **Token ID map** -- `TokenIdMap::from_names()` assigns u16 IDs to all
   FIRST/FOLLOW/structural tokens.

8. **Recovery WFSTs** -- `build_recovery_wfsts()` creates per-category
   weighted repair strategy transducers, threaded with prediction WFSTs
   for Tier 4 cost adjustment.

### Phase 4: Decision Tree Construction

**Location:** `pipeline.rs:2387-2497`

1. **DB02 lazy skip** -- Skips construction for grammars with <3 total rules.

2. **DecisionTreeBuilder** -- Creates `PathMap<DecisionAction>` tries per
   category from RD rules, cross-category rules, and cast rules. Rules
   starting with nonterminals or ident captures are excluded.

3. **Segment splitting** -- Trie is split at nonterminal boundaries into
   linked segments. Each segment handles a terminal prefix.

4. **Diagnostics D01-D09** -- Per-category tree diagnostics: precision
   ambiguity (D01), unresolvable ambiguity (D02), unreachable rules (D03),
   min lookahead (D04), complexity metrics (D05), WFST consistency (D06),
   optimization suggestions (D08), conflict resolution (D09).

5. **Post-DT refinement:**
   - Grammar profile updated with DT metrics (avg depth, ambiguity score)
   - Trie-informed WFST weight scaling (1.2a)
   - Trie+WFST dead-rule confirmation, second pass (1.2b)
   - Sync token depth ranking for recovery (1.3a)
   - NFA spillover pruning from DT dispatch strategy (1.7a)
   - Dead-prefix recovery weight penalty (Sprint 4)

### Phase 5: Mathematical Analysis Modules

**Location:** `pipeline.rs:2766-2960`

1. **WPDS construction** -- G25 gate, requires >=2 categories.
   `analyze_wpds_from_bundle()` builds weighted pushdown system from grammar
   structure and prediction WFSTs.

2. **WPDS refinement:**
   - INT-01: WFST weight tiebreaking from poststar weights
   - COMP-07: WPDS x Trie dead-rule cross-validation
   - INT-02: WPDS-dead rule recording for codegen suppression
   - INT-03: WPDS NFA spillover reduction

3. **Mathematical analyses** -- DB03 gate for parallel execution:

   | Group | Analyses | Dependencies |
   |-------|----------|--------------|
   | A (no WPDS) | confluence, termination, vpa, wta, petri, nominal, alternating, provenance, cra, morphism | Independent |
   | B (WPDS-dependent) | safety, cegar, algebraic, ewpds, ara, ltl, kat | WPDS output |

   When DB03 is enabled and grammar has >=3 categories, all analyses run in
   parallel via `std::thread::scope` with scoped threads sharing borrowed
   references. Otherwise, sequential fallback via `run_math_analyses_sequential`.

4. **DB02 lazy skip** -- Grammars with <3 categories skip all mathematical
   analyses (cross-category interactions too simple to benefit).

### Phase 6: Lint Aggregation

**Location:** `pipeline.rs:2980-3122`

1. **LintContext construction** -- Aggregates all pipeline data into a single
   borrow-based struct with 30+ fields (see [Section 7](#7-ctxbuilder-integration-lintcontext-fields)).

2. **DB04 cached lints** -- `run_lints_cached()` computes a structural hash
   of the grammar spec; if the hash matches the cached value, all 60+ lint
   passes are skipped.

3. **`run_lints()`** -- Executes all lint functions in order:
   - Grammar structure: G01-G10, G24
   - WFST: W01-W06, W10-W12
   - Recovery: R01-R07
   - Cross-category: C01-C04
   - Performance: P02-P06
   - WPDS-derived: W13-W16, D14, COMP08
   - PathMap-derived: W03 hotspot, G32, D10, D13
   - Mathematical: T01-T04, V01-V04, S01-S06, N01-N05, L01-L02, E01-E02, M01-M02, K01-K02
   - Ascent VM: A01-A10
   - Lexer: LEX01-LEX05
   - Parser: PAR01-PAR05
   - Dispatch: DIS01-DIS05

4. **Repair enrichment** -- `enrich_diagnostics_with_repairs()` scans
   diagnostics for specific lint codes and appends semiring-ranked repair
   suggestions from TRS and morphism analyses.

5. **Proof certificates** -- When `proofs` feature is enabled,
   `generate_certificates()` produces Rocq-verifiable proof certificates
   for confluence, termination, and safety results.

6. **Emission** -- `emit_diagnostics_for_grammar()` groups by grammar name,
   filters by `PRATTAIL_LINT_LEVEL`, and outputs ANSI-colorized
   rustc-style diagnostics to stderr.

### Phase 7: Code Generation

**Location:** `pipeline.rs:2131-2250, 3186-3500+`

1. **WFST static embedding** -- Prediction and recovery WFSTs emitted as
   CSR-format static arrays with `LazyLock` constructors.

2. **RD handlers** -- BP04 optimization: trivial rules inlined by trampoline;
   complex rules get standalone `parse_<label>` functions.

3. **Lambda/dollar handlers** -- Generated for primary category when grammar
   has binder rules.

4. **Composed dispatch resolution** -- Ambiguous tokens resolved via
   `compute_composed_dispatch()` with WFST weight tiebreaking.

5. **Trampoline generation** -- Stack-safe parser via explicit continuation
   stack, with DT-informed dispatch strategy per token.

6. **Cross-category dispatch** -- `write_category_dispatch()` with
   optimization gates controlling hot/cold splitting, backtracking
   elimination, and context disambiguation.

7. **Recovery helpers** -- Forward-backward recovery emission.

8. **PipelineAnalysis export** -- Dead rule labels, constructor weights,
   category weights, isomorphic WFST groups, and decision trees captured
   for downstream Ascent codegen optimization.

---

## 5 Semiring Usage Matrix

The pipeline and its analysis modules use different semirings for different
purposes. The columns indicate which semiring type each module produces or
consumes.

| Module / Phase           | Tropical | Boolean | Counting | Product | Log  | Edit | Arctic | Fuzzy | Viterbi | Amplitude | Entropy |
|--------------------------|:--------:|:-------:|:--------:|:-------:|:----:|:----:|:------:|:-----:|:-------:|:---------:|:-------:|
| PredictionWfst           |     x    |         |          |         |      |      |        |       |         |           |         |
| RecoveryWfst             |     x    |         |          |         |      |  x   |        |       |         |           |         |
| cost_benefit             |     x    |         |          |    x    |      |      |        |       |         |           |         |
| forward_backward (A4)    |          |    x    |          |         |      |      |        |       |         |           |         |
| forward_backward (A8)    |          |    x    |    x     |    x    |      |      |        |       |         |           |         |
| forward_backward (wfst-log) |       |         |          |         |  x   |      |        |       |         |           |         |
| transducer cascade       |     x    |         |          |         |      |      |        |       |         |           |         |
| entropy analysis         |          |         |          |         |  x   |      |        |       |         |           |    x    |
| verify (prestar)         |          |    x    |          |         |      |      |        |       |         |           |         |
| cegar                    |          |    x    |    x     |         |      |      |        |       |         |           |         |
| algebraic (Tarjan)       |     x    |         |          |         |      |      |        |       |         |           |         |
| wpds (poststar)          |     x    |         |    x     |         |      |      |        |       |         |           |         |
| newton                   |     x    |         |          |         |      |      |        |       |         |           |         |
| matrix_star (F-W)        |     x    |    x    |    x     |    x    |  x   |  x   |   x    |   x   |    x    |     x     |    x    |
| lattice (WFST)           |     x    |         |    x     |         |      |      |        |       |    x    |           |         |
| compose                  |     x    |         |          |         |      |      |        |       |         |           |         |
| training (wfst-log)      |          |         |          |         |  x   |      |        |       |         |           |         |
| AmplitudeWeight (quantum)|          |         |          |         |      |      |        |       |         |     x     |         |

**Semiring hierarchy:**

```text
  Semiring
    ├── DetectableZero      ← all PraTTaIL semirings
    ├── IdempotentSemiring  ← Tropical, Boolean, Arctic, Fuzzy
    ├── CompleteSemiring    ← all idempotent + Log, Entropy
    └── StarSemiring        ← all 11 semiring types
```

---

## 6 Data Flow: Analysis to Diagnostics

The pipeline's data flows through four stages from raw analysis results to
user-visible diagnostic output:

```text
  ┌─────────────────────────┐
  │ Analysis Modules         │
  │ (confluence, vpa, ...)   │
  │                          │
  │ Each produces:           │
  │   Option<AnalysisResult> │
  └────────────┬─────────────┘
               │
               ▼
  ┌─────────────────────────┐
  │ CtxBuilder / LintContext │
  │                          │
  │ 30+ fields aggregating   │
  │ all pipeline data as     │
  │ borrowed references      │
  └────────────┬─────────────┘
               │
               ▼
  ┌─────────────────────────┐
  │ lint::run_lints()        │
  │                          │
  │ 60+ lint functions       │
  │ Each reads LintContext   │
  │ and pushes LintDiagnostic│
  │ to Vec<LintDiagnostic>   │
  └────────────┬─────────────┘
               │
               ▼
  ┌─────────────────────────┐
  │ Diagnostic Output        │
  │                          │
  │ emit_diagnostic():       │
  │   Filter by lint_level() │
  │   Format with ANSI color │
  │   Group by grammar name  │
  │   Output to stderr       │
  └──────────────────────────┘
```

**Lint severity filtering:**

The `PRATTAIL_LINT_LEVEL` environment variable controls the minimum severity:

| Value       | Shows               |
|-------------|---------------------|
| `"error"`   | Errors only         |
| `"warning"` | Warnings + errors (default) |
| `"note"`    | Notes + warnings + errors |
| `"info"` / `"all"` | Everything |

**Diagnostic format** (rustc-style with ANSI colors):

```text
warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
  --> <macro>:42:5
  = in category `Str`, rule `FloatToStr`
  = hint: remove the rule or add a unique dispatch token
```

---

## 7 CtxBuilder Integration: LintContext Fields

The `LintContext` struct (defined in `lint.rs:156-263`) aggregates all pipeline
data as borrowed references. The pipeline constructs it in the lint aggregation
phase (`pipeline.rs:2999-3057`).

### Core Fields (always present)

| Field                        | Type                                               | Source Phase   | Purpose                                      |
|------------------------------|-----------------------------------------------------|---------------|-----------------------------------------------|
| `grammar_name`               | `&str`                                              | Phase 1       | Grammar identification                        |
| `rule_locations`             | `&HashMap<(String,String), SourceLocation>`         | Phase 1       | Source pointers for diagnostics               |
| `categories`                 | `&[CategoryInfo]`                                   | Phase 1       | Category metadata                             |
| `rules`                      | `&[RuleInfo]`                                       | Phase 1       | Rule analysis info                            |
| `rd_rules`                   | `&[RDRuleInfo]`                                     | Phase 1       | Recursive-descent handler data                |
| `first_sets`                 | `&HashMap<String, FirstSet>`                        | Phase 2       | FIRST sets per category                       |
| `follow_sets`                | `&HashMap<String, FirstSet>`                        | Phase 2       | FOLLOW sets per category                      |
| `bp_table`                   | `&BindingPowerTable`                                | Phase 1       | Binding power assignments                     |
| `prediction_wfsts`           | `&HashMap<String, PredictionWfst>`                  | Phase 3       | Per-category prediction transducers           |
| `recovery_wfsts`             | `&[RecoveryWfst]`                                   | Phase 3       | Per-category recovery transducers             |
| `cast_rules`                 | `&[CastRule]`                                       | Phase 1       | Cast rule definitions                         |
| `cross_rules`                | `&[CrossCategoryRule]`                              | Phase 1       | Cross-category rule definitions               |
| `nfa_spillover_categories`   | `&HashSet<String>`                                  | Phase 3+4     | Categories needing NFA buffers                |
| `recovery_config`            | `&RecoveryConfig`                                   | Phase 1       | 19-field recovery configuration               |
| `all_syntax`                 | `&[(String, String, Vec<SyntaxItemSpec>)]`           | Phase 1       | Per-rule syntax triples                       |
| `follow_inputs`              | `&[FollowSetInput]`                                 | Phase 1       | FOLLOW set computation inputs                 |
| `semantic_dependency_groups` | `&[HashSet<String>]`                                | Phase 1       | Equation/rewrite dependency groups            |
| `pre_collected_diagnostics`  | `&[LintDiagnostic]`                                 | Phase 3       | W05 composed-dispatch diagnostics             |
| `decision_trees`             | `&HashMap<String, CategoryDecisionTree>`            | Phase 4       | PathMap tries per category                    |
| `token_id_map`               | `&TokenIdMap`                                       | Phase 3       | Token variant -> u16 mapping                  |
| `dead_rule_warnings`         | `&[DeadRuleWarning]`                                | Phase 4       | Cached dead-rule warnings                     |
| `grammar_profile`            | `Option<&GrammarProfile>`                           | Phase 3+4     | Grammar metrics for severity modulation       |
| `wpds_analysis`              | `Option<&WpdsAnalysis>`                             | Phase 5       | WPDS stack-aware reachability                 |
| `wpds_elapsed`               | `Option<Duration>`                                  | Phase 5       | P05 timing data                               |

### Always-On Analysis Fields

| Field                        | Type                                               | Source Module  |
|------------------------------|-----------------------------------------------------|---------------|
| `safety_result`              | `Option<&SafetyResult<BooleanWeight>>`              | `verify`       |
| `cegar_result`               | `Option<&CegarLog>`                                | `cegar`        |
| `algebraic_result`           | `Option<&AlgebraicSummary>`                         | `algebraic`    |
| `math_analysis_elapsed`      | `Option<Duration>`                                  | Phase 5        |

### Feature-Gated Analysis Fields

| Field                | Feature Gate     | Type                                    |
|----------------------|------------------|-----------------------------------------|
| `confluence_result`  | `trs-analysis`   | `Option<&ConfluenceAnalysis>`           |
| `termination_result` | `trs-analysis`   | `Option<&TerminationResult>`            |
| `vpa_result`         | `vpa`            | `Option<&VpaAnalysis>`                  |
| `wta_result`         | `tree-automata`  | `Option<&WtaAnalysis>`                  |
| `ewpds_result`       | `wpds-extended`  | `Option<&EwpdsAnalysis>`                |
| `ara_result`         | `wpds-ara`       | `Option<&AraAnalysis>`                  |
| `petri_result`       | `petri`          | `Option<&PetriAnalysis>`                |
| `nominal_result`     | `nominal`        | `Option<&NominalAnalysis>`              |
| `alternating_result` | `alternating`    | `Option<&AlternatingAnalysis>`          |
| `ltl_results`        | `ltl`            | `Option<&Vec<LtlCheckResult>>`          |
| `provenance_result`  | `provenance`     | `Option<&ProvenanceAnalysis>`           |
| `cra_result`         | `cra`            | `Option<&CraAnalysis>`                  |
| `morphism_result`    | `morphisms`      | `Option<&MorphismCheck>`                |
| `kat_result`         | `kat`            | `Option<&KatCheck>`                     |

---

## 8 Cost-Benefit Framework

### GrammarProfile

The `GrammarProfile` struct (`cost_benefit.rs:372-399`) captures 12 grammar
metrics computed from WFST analysis and PathMap decision trees:

| Metric                     | Range      | Computed From                                    |
|----------------------------|------------|--------------------------------------------------|
| `shared_prefix_ratio`      | [0.0, 1.0] | NFA spillover categories / total categories     |
| `cold_fraction`            | [0.0, 1.0] | WFST actions with weight >= 1.0 / total actions |
| `ambiguous_fraction`       | [0.0, 1.0] | Ambiguous dispatch tokens / total dispatch tokens|
| `ambiguous_count`          | [0, inf)   | Count of ambiguous dispatch tokens               |
| `category_count`           | [1, inf)   | Number of grammar categories                     |
| `rule_count`               | [1, inf)   | Number of grammar rules                          |
| `nfa_spillover_categories` | [0, inf)   | Categories needing NFA buffers                   |
| `has_beam_width`           | bool       | Whether beam pruning is configured               |
| `total_wfst_states`        | [0, inf)   | Sum of WFST states across categories             |
| `avg_trie_depth`           | [0, inf)   | Mean max_depth of PathMap tries                  |
| `ambiguity_score`          | [0.0, 1.0] | Ambiguous nodes / total states in DTs            |
| `deterministic_ratio`      | [0.0, 1.0] | Rules with no prefix ambiguity / total rules     |

### Optimization Scoring

Each optimization candidate is scored using `ProductWeight<TropicalWeight, TropicalWeight>`
with lexicographic ordering:

```text
  score = (speedup_weight, compile_cost_weight)

  Comparison: first compare speedup (lower = more beneficial);
              if tied, compare compile_cost (lower = cheaper).
```

### Gate Activation Summary

The 50 optimization variants in `Optimization` enum each have an applicability
predicate based on `GrammarProfile` metrics:

| Optimization Group | Example Gate Predicate                                  |
|--------------------|---------------------------------------------------------|
| A1 LeftFactoring   | `shared_prefix_ratio > 0.3`                             |
| A2 HotColdSplit    | `cold_fraction > 0.4`                                   |
| A4 EnhancedDCE     | `rule_count > 5`                                        |
| A5 AmbiguityTarget | `ambiguous_fraction > 0.1`                              |
| B1 MultiTokenLA    | `ambiguous_fraction > 0.1 && ambiguous_count < 10`      |
| B3 WfstMinimize    | `total_wfst_states > 4`                                 |
| G1 BacktrackElim   | always applicable                                       |
| G25 WpdsReach      | `category_count >= 2`                                   |
| ART01 HashConsing  | `rule_count > 10`                                       |
| BCG02 RuleFusion   | `rule_count > 5`                                        |
| CD03 ComputedGoto  | `rule_count > 20`                                       |
| DB02 LazyAnalysis  | `category_count < 3`                                    |
| DB03 ParallelAnaly | `category_count >= 3`                                   |

The `OptimizationGates` struct (`cost_benefit.rs:1096-1230`) converts recommended
optimizations into boolean flags. The pipeline can override gates via the
`PRATTAIL_AUTO_OPTIMIZE` environment variable:

- `"all"`: enable all gates
- `"none"`: disable all gates
- `"A1,B3,G25"`: enable specific gates by code

---

## 9 Worked Example: Grammar Through the Pipeline

Consider a grammar with 4 categories: `Proc`, `Int`, `Bool`, `Str`.

### Phase 1: Extract

```text
ParserBundle {
  grammar_name: "RhoPi",
  categories: [
    CategoryInfo { name: "Proc", native_type: None, is_primary: true },
    CategoryInfo { name: "Int",  native_type: Some("i32"), is_primary: false },
    CategoryInfo { name: "Bool", native_type: Some("bool"), is_primary: false },
    CategoryInfo { name: "Str",  native_type: Some("String"), is_primary: false },
  ],
  rule_infos: [ /* ~25 rules */ ],
  rd_rules:   [ /* ~18 prefix rules */ ],
  cast_rules: [ CastRule { source: "Int", target: "Proc" }, ... ],
  ...
}
```

### Phase 2: FIRST/FOLLOW

```text
FIRST(Proc) = { "KwNew", "KwFor", "Ident", "LParen", ... }
FIRST(Int)  = { "Integer", "Ident", "LParen", "KwLen", ... }
FIRST(Bool) = { "KwTrue", "KwFalse", "Ident", "LParen", ... }
FIRST(Str)  = { "StringLit", "Ident", "LParen", ... }

DB01: incremental mode (4 categories >= 3 threshold)
  FIRST: 12/16 visits (4 iters, 4 cats)
  FOLLOW: 8/16 visits (4 iters, 4 cats)
```

### Phase 3: WFST Construction

```text
PredictionWfst(Proc): 6 states, 14 actions
PredictionWfst(Int):  3 states, 8 actions
PredictionWfst(Bool): 3 states, 5 actions
PredictionWfst(Str):  3 states, 6 actions

Two-token enrichment: 3 paths added
ContextWeight labels: 9 assigned
Transducer cascade: 8 change(s) across 3 categories (12 iterations)

Total WFST states: 15 (> 4 threshold, cascade runs)
```

### Phase 4: Decision Tree

```text
CategoryDecisionTree(Proc):
  segments[0]:  5 states (3 det, 1 ambiguous), max depth 2
  segments[1]:  2 states (continuation after NonTerminal)

CategoryDecisionTree(Int):
  segments[0]:  3 states (all deterministic), max depth 1

D05: Proc: 5 states, 60% deterministic
D01: Proc: KwFor has 2 ambiguous alternatives
```

### Phase 5: Mathematical Analyses

```text
G25: WPDS construction (4 categories >= 2 threshold)
  poststar: 12 rules, 6 states saturated
  INT-01: refined 2 weight ties via WPDS

DB03: parallel analysis (4 categories >= 3)
  3 always-on phases executed in parallel (12.3ms wall-clock)

[trs-analysis] confluence: 0 critical pairs (confluent)
[trs-analysis] termination: no cycles detected
```

### Phase 6: Lint Aggregation

```text
LintContext constructed with 30 fields

run_lints(): 60+ passes executed
  G01: no left recursion detected
  W01: 1 dead rule (FloatToStr in Str)
  S01: safety verified (no violations)
  ...

Diagnostics emitted:
  warning[W01]: rule `FloatToStr` in category `Str` is unreachable
  note[D05] (RhoPi): Proc: 5 states (3 det, 1 amb), max depth 2
  ...
```

### Phase 7: Codegen

```text
Generated code: ~2,100 lines
  - Token enum with 35 variants
  - Lexer function (hybrid direct-coded + compressed)
  - 18 RD handler functions (4 inlined by BP04)
  - 4 Pratt parsing loops
  - 4 dispatch functions (1 cross-category)
  - WFST static arrays (CSR format)
  - Recovery helpers

PipelineAnalysis exported:
  dead_rule_labels: {"FloatToStr"}
  constructor_weights: {"Add": 0.2, "Sub": 0.3, ...}
  category_weights: {"Proc": 0.4, "Int": 0.3, ...}
  isomorphic_groups: [["Bool", "Str"]]
  decision_trees: { "Proc": ..., "Int": ..., ... }
```

---

## References

- Mohri, M. (2009). "Weighted automata algorithms." Handbook of Weighted Automata, Springer.
- Reps, T., Schwoon, S., Jha, S., Melski, D. (2005). "Weighted pushdown systems and their application to interprocedural dataflow analysis." Science of Computer Programming, 58(1-2).
- Kuich, W. and Salomaa, A. (1986). "Semirings, Automata, Languages." EATCS Monographs on Theoretical Computer Science, Springer.
- Kincaid, Z., Cyphert, J., Breck, J., Reps, T. (2019). "Non-linear reasoning for invariant synthesis." POPL 2019.
- Adams, M.D. (2017). "Principled parsing for indentation-sensitive languages." POPL 2017.

---

*Source files:* [`prattail/src/pipeline.rs`](../../src/pipeline.rs),
[`prattail/src/cost_benefit.rs`](../../src/cost_benefit.rs),
[`prattail/src/lint.rs`](../../src/lint.rs),
[`prattail/src/lib.rs`](../../src/lib.rs)
