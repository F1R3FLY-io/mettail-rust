# Requirements Traceability

Last updated: 2026-06-14

This document maps the explicit Dovetail documentation and verification
requirements to the files that satisfy them. It is a reader aid: the detailed
architecture, examples, proofs, citations, and handoff instructions remain in
the linked documents.

All Dovetail terms used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md). Runtime-integration terms
shared with Rho are defined in the Rho-native
[Concepts and Glossary](../rho-native-integration/01-concepts-and-glossary.md).

## Scope

This suite documents Dovetail as a standalone rewrite engine. The Rho-native
integration suite documents one downstream consumer of complete Dovetail
reports. The boundary is:

`language! specification → LanguageDef → LanguageMetadata → Dovetail rules → SatReport → Extraction<T> → DovetailRunReport`

The Dovetail suite may name the direct Dovetail runtime adapter and the
Rho-native consumer, but Dovetail itself remains substrate-neutral. The active
WPDA parser stays upstream, Ascent stays available as a reference/oracle path,
and the CESK runtime backend is the runtime path being replaced by the
Dovetail/Rho production direction.

The documentation makes four kinds of claims:

| Claim kind | Meaning | Evidence location |
|---|---|---|
| architecture claim | The document states an intended component boundary or dataflow. | This documentation suite. |
| mathematical prose claim | The document states an invariant, formula, or proof sketch in human-readable form. | The cited architecture chapter and its references. |
| mechanized claim | A proof artifact is named as existing evidence. | `dovetail/formal/rocq/`, `dovetail/formal/why3/`, `dovetail/formal/creusot/`, and project-level `formal/` gates. |
| executable claim | A Rust test or validator exercises the behavior. | `dovetail/tests/`, `mettail-dovetail-runtime`, and the cited validation scripts. |

This distinction keeps prose from silently upgrading a design obligation into a
mechanized theorem.

## Requirement Map

| Requirement | Coverage |
|---|---|
| Document Dovetail itself, not only the Rho integration. | [README](README.md), [Executive Brief](00-executive-brief.md), and [Engine Architecture](02-engine-architecture.md) define Dovetail as the substrate-neutral rewrite engine. |
| Keep the WPDA parser out of the legacy bucket. | [README](README.md#relation-to-other-subsystems), [Executive Brief](00-executive-brief.md#what-dovetail-replaces), and [Runtime-Facing Reports](10-runtime-facing-reports.md#minirhofor-report-example) state that WPDA remains upstream and active. |
| Explain what Dovetail replaces. | [Executive Brief](00-executive-brief.md#what-dovetail-replaces) and [Engineering Handoff](08-engineering-handoff.md#integration-boundary) distinguish Ascent as legacy production rewrite execution, Ascent as retained oracle evidence, and CESK as the runtime backend path being replaced. |
| Define symbols, acronyms, and key terms before use. | [Concepts and Glossary](01-concepts-and-glossary.md) defines exact keys, e-graphs, WTA, semirings, saturation, extraction, boundedness, reports, and related symbols. |
| Present Dovetail pedagogically for principals and implementers. | [README](README.md#reading-paths) gives separate principal, implementer, and reviewer reading paths; [Executive Brief](00-executive-brief.md) gives the decision view; [Engineering Handoff](08-engineering-handoff.md) gives takeover guidance. |
| Explain the intuition, theoretical basis, and rationale of every component. | [Engine Architecture](02-engine-architecture.md), [Data Model and Exact Keys](03-data-model-and-exact-keys.md), [Rules and Saturation](04-rules-and-saturation.md), [Extraction and Weights](05-extraction-and-weights.md), and [Cyclic Closure and Boundedness](06-cyclic-closure-and-boundedness.md) explain the component rationale and cite the theory lineage in [References](references.md). |
| Use diagrams without overwhelming the docs. | [README](README.md#architecture-at-a-glance), [Engine Architecture](02-engine-architecture.md), [Extraction and Weights](05-extraction-and-weights.md), [Formal Verification and Tests](07-formal-verification-and-tests.md), and [Runtime-Facing Reports](10-runtime-facing-reports.md) use focused PlantUML or Graphviz diagrams with committed SVG outputs. |
| Prefer SVG outputs and diagram source files. | Every diagram under [figures](figures/README.puml) has source plus committed SVG; [README](README.md#diagramming-choices) explains the PlantUML, Graphviz, and SVG policy. |
| Use Unicode mathematical notation and wrap mathematical expressions as literals. | The suite writes expressions such as `∀d. Valid(d) ∧ weight(d) ≠ 0̄ ⇒ EventuallyEnumerated(d)` as code literals; [validate.sh](validate.sh) checks common mathematical symbols outside code literals. |
| Use literate pseudocode for algorithms. | [Rules and Saturation](04-rules-and-saturation.md), [Extraction and Weights](05-extraction-and-weights.md), [Runtime-Facing Reports](10-runtime-facing-reports.md#literate-pseudocode), and [Engineering Handoff](08-engineering-handoff.md#adding-a-new-rule-family) present algorithms as explanatory pseudocode. |
| Explain Dovetail rewrite rules. | [Rules and Saturation](04-rules-and-saturation.md) explains rules-as-data, matching, instantiation, guarded execution, budgets, and saturation outcomes; [Rho-native Dovetail Rewrite Semantics](../rho-native-integration/03-dovetail-rewrite-semantics.md) shows the integration-facing rule-family view. |
| Explain exact keys and why finite hashes are not enough. | [Data Model and Exact Keys](03-data-model-and-exact-keys.md), [Engineering Handoff](08-engineering-handoff.md#adding-a-new-label-type), and [Formal Verification and Tests](07-formal-verification-and-tests.md) cover `SemanticHash`, framed identity bytes, ordered framing, and exact-key proof obligations. |
| Explain weights and the no-pruning requirement. | [Executive Brief](00-executive-brief.md#design-thesis), [Extraction and Weights](05-extraction-and-weights.md), and [Engineering Handoff](08-engineering-handoff.md#adding-a-new-weight-type) state that weights order derivations and do not remove non-`0̄` alternatives. |
| Explain cyclic boundedness. | [Cyclic Closure and Boundedness](06-cyclic-closure-and-boundedness.md), [Runtime-Facing Reports](10-runtime-facing-reports.md#phase-boundaries-and-invariants), and [Formal Verification and Tests](07-formal-verification-and-tests.md) distinguish productive cyclic spaces from finite complete extraction. |
| Explain what Dovetail reports are. | [Runtime-Facing Reports](10-runtime-facing-reports.md) defines `SatReport`, `Extraction<T>`, `DovetailRunReport`, `RuntimeDovetailRunReport`, `RuntimeBackendReport`, and `RhoObservationReport`, and explains why reports are semantic handoff artifacts rather than logs. |
| Show how reports look. | [Runtime-Facing Reports](10-runtime-facing-reports.md#report-shape) shows the logical Rust shapes for `SatReport`, `Extraction<T>`, `DovetailRunReport`, term records, and derivation edges. |
| Provide an end-to-end `language!` example. | [Runtime-Facing Reports](10-runtime-facing-reports.md#minirhofor-report-example) gives the MiniRhoFor fixture from `language!` specification through `LanguageDef`, generated inventory, Dovetail rules, typed AST, report, direct Dovetail output, and Rho AST handoff. |
| Keep `language!` as the language source of truth. | [README](README.md#comprehension-contract), [Runtime-Facing Reports](10-runtime-facing-reports.md#minirhofor-report-example), and [Engineering Handoff](08-engineering-handoff.md) require Dovetail adapters to consume generated inventory rather than backend-local category lists. |
| Distinguish the direct Dovetail runtime lane from the Rho lane. | [README](README.md#cohesive-integration-view) and [Runtime-Facing Reports](10-runtime-facing-reports.md#where-reports-sit-in-the-rewrite-pipeline) show `DovetailRunReport → RuntimeBackendOutput::Dovetail` beside `DovetailRunReport → rhoapi::Par → RhoRuntime → observations`. |
| State the proof and test coverage. | [Formal Verification and Tests](07-formal-verification-and-tests.md) maps claims to Rocq, Why3, Creusot, Rust example, exhaustive, corpus, and property checks. |
| Make the suite self-sufficient for another agent. | [Engineering Handoff](08-engineering-handoff.md) names source-of-truth files, invariants, extension checklists, report-boundary updates, and review commands; [README](README.md#comprehension-contract) states the cross-page artifact chain. |
| Cite local sources and theory references. | [References](references.md) lists local design docs, Rust source, tests, formal artifacts, and external theory references with DOI or stable scholarly links where available. |
| Provide reproducible validation. | [validate.sh](validate.sh) checks proof-hole markers, fenced-block balance, diagram assets, relative links, referenced local paths, mathematical-symbol formatting, and whitespace. |

## Consistency Conditions

The suite should remain coherent under these checks:

| Check | Required result |
|---|---|
| artifact-chain vocabulary | Before `DovetailRunReport`, prose discusses language inventory or Dovetail internals; after `DovetailRunReport`, prose clearly names the consumer. |
| parser boundary | WPDA remains the source-text parser/recognizer; Dovetail consumes typed terms and generated metadata. |
| report boundary | Complete and cycle-bounded extraction results remain distinguishable in prose, APIs, tests, and proofs. |
| runtime output shape | Direct Dovetail output is report-shaped; Rho output is observation-shaped after executing normalized `rhoapi::Par`. |
| no hidden category lists | Category, constructor, rewrite, guard, and handler inventories are derived from `LanguageMetadata` or `LanguageDef`. |
| diagram assets | Every diagram source has a non-empty rendered SVG and no escaped PlantUML color markup. |
| local references | Every local source path listed in [References](references.md) resolves from the repository root. |
| validation script | `docs/architecture/dovetail/validate.sh` passes from the repository root. |

Run the local suite check with:

```text
docs/architecture/dovetail/validate.sh
```

Run the focused implementation and proof checks listed in
[Formal Verification and Tests](07-formal-verification-and-tests.md#required-commands)
when a documentation change makes or updates an implementation or mechanized
claim.
