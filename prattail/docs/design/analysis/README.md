# PraTTaIL Mathematical Analysis Framework

## Motivation

PraTTaIL generates parsers from `language!` macro specifications.  Beyond
syntactic well-formedness, many non-trivial properties of a grammar can be
decided or approximated statically: is the term rewriting system confluent?
Are recursive categories terminating?  Does the nesting discipline respect
visibly-pushdown constraints?  Can a safety invariant be violated?  The
mathematical analysis framework answers these questions at compile time,
surfacing results as structured lint diagnostics with actionable repair
suggestions.

The framework is organised into 23 modules spanning five abstraction levels,
gated behind 18 Cargo features plus four convenience groups.  All analyses
feed into a shared lint layer (28 analysis-specific codes) and a repair
engine that ranks fix suggestions by semiring-weighted criteria.

---

## Module Taxonomy

Analyses are layered from concrete string-level operations up through
increasingly abstract semantic models.  Lower layers provide inputs to
higher layers; no circular dependencies exist between levels.

```
 ┌─────────────────────────────────────────────────────────────────────┐
 │                       Level 5 — Meta                               │
 │  morphism.rs   kat.rs   tensor.rs   proof_output.rs   repair.rs    │
 │  Cross-theory translation, decidable Hoare logic, semiring         │
 │  products, proof certificates, repair suggestions                  │
 ├─────────────────────────────────────────────────────────────────────┤
 │                   Level 4 — Temporal / Provenance                  │
 │  ltl.rs   buchi.rs   provenance.rs   cra.rs                       │
 │  Infinite-word properties, derivation tracking, streaming costs    │
 ├─────────────────────────────────────────────────────────────────────┤
 │                   Level 3 — Concurrency                            │
 │  petri.rs   nominal.rs   alternating.rs                            │
 │  Deadlock detection, name binding, branching bisimulation          │
 ├─────────────────────────────────────────────────────────────────────┤
 │                   Level 2 — Pushdown / Verification                │
 │  verify.rs   cegar.rs   algebraic.rs   ewpds.rs   ara.rs          │
 │  newton.rs   relational.rs                                         │
 │  Safety, abstraction refinement, path expressions, affine          │
 │  relations, fixpoint acceleration                                  │
 ├─────────────────────────────────────────────────────────────────────┤
 │                   Level 1 — String / Tree                          │
 │  confluence.rs   termination.rs   vpa.rs   tree_automaton.rs       │
 │  Knuth-Bendix critical pairs, dependency pairs, VPA closure,      │
 │  weighted tree automata                                            │
 └─────────────────────────────────────────────────────────────────────┘
```

---

## Feature-Gate Dependency Graph

Features form a DAG.  An edge A --> B means "A depends on B".

```
                    ┌── full-analysis ──┐
                    │   (enables all)   │
                    └─────────┬─────────┘
          ┌───────────────────┼───────────────────┐
          │                   │                   │
    ┌─────┴─────┐     ┌──────┴──────┐     ┌──────┴──────┐
    │ analysis  │     │verification │     │process-alg. │
    └─────┬─────┘     └──────┬──────┘     └──────┬──────┘
          │                  │                   │
   ┌──────┼──────┐     ┌────┼────┐      ┌───────┼───────┐
   │      │      │     │    │    │      │       │       │
tree-aut  vpa  trs   omega  ltl  kat   nominal petri  alternating
                        │    │    │       │
                        │    │    │       │
                        │    └──┘ │       │
                        │   (ltl  │       │
                        │  needs  │       │
                        │  omega) │       │
                        │         │       │
                    ┌───┘   ┌─────┘       │
                    │       │             │
              wpds-relational       (also needs omega)
                    │
              ┌─────┴─────┐
              │  wpds-ara  │
              │(+nalgebra) │
              └────────────┘

Standalone features (no analysis-group deps):
  wpds-extended   provenance   proofs (needs provenance)
  cra   morphisms   quantum   wfst-log
```

---

## Always-On vs Feature-Gated Modules

| Module            | Feature gate       | Always-on? | Source file       |
|-------------------|--------------------|------------|-------------------|
| verify            | --                 | Yes        | `verify.rs`       |
| repair            | --                 | Yes        | `repair.rs`       |
| cegar             | --                 | Yes        | `cegar.rs`        |
| newton            | --                 | Yes        | `newton.rs`       |
| tensor            | --                 | Yes        | `tensor.rs`       |
| algebraic         | --                 | Yes        | `algebraic.rs`    |
| confluence        | `trs-analysis`     | No         | `confluence.rs`   |
| termination       | `trs-analysis`     | No         | `termination.rs`  |
| vpa               | `vpa`              | No         | `vpa.rs`          |
| tree_automaton    | `tree-automata`    | No         | `tree_automaton.rs` |
| buchi             | `omega`            | No         | `buchi.rs`        |
| ltl               | `ltl`              | No         | `ltl.rs`          |
| alternating       | `alternating`      | No         | `alternating.rs`  |
| nominal           | `nominal`          | No         | `nominal.rs`      |
| petri             | `petri`            | No         | `petri.rs`        |
| cra               | `cra`              | No         | `cra.rs`          |
| kat               | `kat`              | No         | `kat.rs`          |
| morphism          | `morphisms`        | No         | `morphism.rs`     |
| provenance        | `provenance`       | No         | `provenance.rs`   |
| proof_output      | `proofs`           | No         | `proof_output.rs` |
| relational        | `wpds-relational`  | No         | `relational.rs`   |
| ewpds             | `wpds-extended`    | No         | `ewpds.rs`        |
| ara               | `wpds-ara`         | No         | `ara.rs`          |

---

## Semiring Usage Matrix

Different analyses exploit different semirings from the PraTTaIL semiring
catalog (`prattail/docs/design/semiring-catalog.md`).  The matrix below
shows which analyses use which semirings.

| Semiring          | verify | cegar | algebraic | newton | tensor | ara | provenance | cra |
|-------------------|:------:|:-----:|:---------:|:------:|:------:|:---:|:----------:|:---:|
| BooleanWeight     |   x    |   x   |     x     |   x    |        |     |            |     |
| TropicalWeight    |   x    |   x   |     x     |   x    |   x    |     |            |  x  |
| CountingWeight    |        |   x   |     x     |   x    |   x    |     |            |  x  |
| LogWeight         |        |       |           |   x    |   x    |     |            |     |
| ViterbiWeight     |        |       |           |        |   x    |     |            |     |
| FuzzyWeight       |        |       |           |        |        |     |            |     |
| EditWeight        |        |       |           |        |        |     |            |     |
| ProductWeight     |        |       |           |        |   x    |     |            |     |
| AmplitudeWeight   |        |       |           |        |   x    |     |            |     |
| N[X] (Provenance) |        |       |           |        |        |     |     x      |     |
| AraWeight (nalg.) |        |       |           |        |        |  x  |            |     |
| RelationalWeight  |        |       |           |        |        |     |            |     |

Key: "x" means the analysis dispatches on or instantiates that semiring.

---

## Pipeline Integration

All analyses run after WPDS construction during `language!` macro expansion.
They execute in six phases with explicit dependency ordering:

```
  WPDS construction (always-on)
       │
       ▼
  Phase 1: TRS ─────────────────────────── confluence, termination
       │
       ▼
  Phase 2: Automata ────────────────────── VPA, WTA
       │
       ▼
  Phase 3: WPDS-dependent ──────────────── verify, cegar, algebraic
       │                                   (+ ewpds, ara if gated)
       ▼
  Phase 4: Concurrency ─────────────────── petri, nominal, alternating
       │
       ▼
  Phase 5: Temporal / Provenance ───────── LTL+Buchi, provenance, CRA
       │
       ▼
  Phase 6: Meta ────────────────────────── morphism, KAT
       │
       ▼
  Lint emission ────────────────────────── 28 analysis lint codes
       │
       ▼
  Repair enrichment ────────────────────── T01, M01 hint augmentation
       │
       ▼
  Proof certificates (proofs feature) ──── Z01 notes
```

---

## Cost-Benefit Integration

Five analysis-specific `Optimization` variants carry
`OptimizationStatus::Diagnostic`, meaning they emit information but do not
gate code generation:

| Variant                | Module      | Lint codes |
|------------------------|-------------|------------|
| `TrsConfluenceCheck`   | confluence  | S01-S06    |
| `VpaInclusionCheck`    | vpa         | V01-V04    |
| `SafetyVerification`   | verify      | T01-T04    |
| `CegarRefinement`      | cegar       | --         |
| `PetriDeadlockCheck`   | petri       | N01-N05    |

---

## Lint Code Catalogue (Analysis-Specific)

| Code | Module       | Severity | Description                           |
|------|-------------|----------|---------------------------------------|
| S01  | confluence  | Warning  | Non-joinable critical pair            |
| S02  | confluence  | Note     | All critical pairs joinable           |
| S03  | termination | Warning  | Potentially non-terminating SCC       |
| S04  | termination | Note     | TRS is terminating                    |
| S05  | confluence  | Note     | Confluence analysis summary           |
| S06  | termination | Note     | Termination analysis summary          |
| T01  | verify      | Warning  | Safety property violated              |
| T02  | verify      | Note     | Safety property verified              |
| T03  | cegar       | Note     | CEGAR refinement completed            |
| T04  | verify      | Note     | Verification summary                  |
| V01  | vpa         | Warning  | VPA non-determinism detected          |
| V02  | vpa         | Note     | VPA inclusion holds                   |
| V03  | wta         | Note     | WTA recognition summary               |
| V04  | vpa         | Note     | VPA analysis summary                  |
| N01  | petri       | Warning  | Potential deadlock detected            |
| N02  | petri       | Note     | System is deadlock-free               |
| N03  | nominal     | Warning  | Scope violation detected              |
| N04  | nominal     | Note     | All names in scope                    |
| N05  | alternating | Note     | Bisimulation check summary            |
| L01  | ltl         | Warning  | LTL property violated                 |
| L02  | ltl         | Note     | LTL property satisfied                |
| E01  | ewpds       | Note     | EWPDS merge sites identified          |
| E02  | ara         | Note     | ARA dimension report                  |
| M01  | morphism    | Warning  | Morphism gap detected                 |
| M02  | morphism    | Note     | Morphism is complete                  |
| K01  | kat         | Warning  | Hoare triple violated                 |
| K02  | kat         | Note     | KAT check summary                    |
| P06  | provenance  | Note     | Provenance tracking summary           |
| Z01  | proof_output| Note     | Proof certificate generated           |

---

## Cross-References to Design Documents

| Document                        | Covers                                   |
|---------------------------------|------------------------------------------|
| `trs-analysis.md`               | Confluence (Knuth-Bendix) + Termination (dependency pairs) |
| `pushdown-verification.md`      | Safety, CEGAR, EWPDS, ARA, Newton, Algebraic |
| `automata-extensions.md`        | VPA, WTA, Buchi, Alternating             |
| `concurrency-analysis.md`       | Petri nets, Nominal automata, Alternating bisimulation |
| `temporal-and-provenance.md`    | LTL, Provenance semiring, CRA            |
| `meta-level-analysis.md`        | Morphisms, KAT, Tensor, Repair engine    |

---

## Reading Order for Newcomers

1. **This README** -- understand the taxonomy, feature gates, and pipeline
2. **`trs-analysis.md`** -- the simplest analyses (pure term rewriting)
3. **`automata-extensions.md`** -- classical automata generalisations
4. **`pushdown-verification.md`** -- WPDS verification stack
5. **`concurrency-analysis.md`** -- process-algebraic models
6. **`temporal-and-provenance.md`** -- temporal logic and provenance tracking
7. **`meta-level-analysis.md`** -- cross-cutting meta analyses and the repair engine

This order mirrors the pipeline phases and introduces concepts from simple
to complex.  The semiring catalog (`semiring-catalog.md`) is a useful
companion reference throughout.
