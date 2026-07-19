# 00 — Requirements Traceability

Last updated: 2026-06-14

This document maps the explicit documentation requirements for the
MeTTaIL / Dovetail / F1r3node / Rholang / Rho-machine integration to the files
that satisfy them.

All terms used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## Scope

The scope of this suite is the architecture and design documentation for the
Rho-native integration. Mechanized formal targets remain in their existing
formal directories and are referenced from the documentation. The documentation
therefore makes two kinds of claims:

| Claim kind | Meaning | Evidence location |
|---|---|---|
| architecture claim | The design states a required invariant or component contract. | This documentation suite. |
| mechanized claim | A named checked theorem, model, or verification target exists as evidence. | `formal/rocq/`, `dovetail/formal/rocq/`, and the cited coverage matrix. |

The distinction prevents prose from silently upgrading a design obligation into
a completed mechanized result.

## Requirement Map

| Requirement | Coverage |
|---|---|
| Place documentation under root `docs/`. | The suite lives at `docs/architecture/rho-native-integration/` and is linked from the project [README](../../../README.md), [docs/README.md](../../README.md), and [docs/architecture.md](../../architecture.md). |
| Document MeTTaIL, Dovetail, F1r3node, Rholang, RSpace, and the Rho machine together. | [README](README.md), [End-to-End Architecture](02-end-to-end-architecture.md), and [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md). |
| Explain what each component is, what it does, how it works, and why it was selected. | [Concepts and Glossary](01-concepts-and-glossary.md) defines terms; [End-to-End Architecture](02-end-to-end-architecture.md) assigns responsibilities; [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md) gives the rationale for RSpace. |
| Provide at-a-glance material for principals. | [Executive Brief](00-executive-brief.md) gives the one-page decision view; [README](README.md) has the reading paths, document map, and component diagram. |
| Use diagrams where appropriate and colorize them. | PlantUML diagrams appear in [README](README.md), [End-to-End Architecture](02-end-to-end-architecture.md), [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md), [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md), [Correctness and Coverage](06-correctness-and-coverage.md), [Verification and Rollout](07-verification-and-rollout.md), and [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md). The production guide also uses Graphviz DOT for a readiness DAG. Each diagram assigns colors to participants, states, proof nodes, or gate nodes. |
| Prefer SVG outputs and choose the best local diagram tool for each concept. | [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md#diagram-tooling-policy) records the pgmcp-discovered local diagram toolbox and the source-plus-SVG policy. |
| Make the design self-sufficient for another agent. | [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md) defines the runtime-backend scope, inventory, AST artifact contract, production gates, diagram policy, and ordered completion checklist. |
| Show the high-level chain from `language!` to runtime dispatch. | [End-to-End Architecture](02-end-to-end-architecture.md#high-level-dispatch-trace) splits the static language-definition track from the runtime snippet track; [Dovetail Runtime-Facing Reports](../dovetail/10-runtime-facing-reports.md#minirhofor-report-example) gives the MiniRhoFor fixture from `language!` specification through `LanguageDef`, `LanguageMetadata`, Dovetail rules, parsed AST, report, and Rho AST handoff. |
| Explain how Dovetail reports differ from runtime observations. | [Dovetail Runtime-Facing Reports](../dovetail/10-runtime-facing-reports.md) defines `SatReport`, `Extraction<T>`, `DovetailRunReport`, `RuntimeDovetailRunReport`, `RuntimeBackendReport`, and `RhoObservationReport`, then shows the direct Dovetail and Rho lanes side by side. |
| Define symbols, acronyms, and key terms before use. | [Concepts and Glossary](01-concepts-and-glossary.md) defines system terms, rewrite terms, Rho/RSpace terms, mathematical symbols, and acronyms. |
| Use Unicode mathematical notation and wrap expressions in backticks. | Mathematical expressions throughout the suite use symbols such as `μ`, `Δ`, `ρ`, `σ`, `⇒`, `∧`, `∨`, `⊆`, `∈`, `≡`, `⊗`, and `⊕`, and are written as inline or block code literals. |
| Use pseudocode rather than code snippets for algorithms. | Algorithms are marked as literate pseudocode in [End-to-End Architecture](02-end-to-end-architecture.md), [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md), [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md), and [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md). |
| Include examples and code snippets where related. | Small Rholang and RhoNet examples appear in [End-to-End Architecture](02-end-to-end-architecture.md) and [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md). Algorithmic material remains pseudocode. |
| Include Dovetail rewrite rules. | [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md) lists seed, equation, directed rewrite, equivalence-respecting rewrite, congruence, native/fold, guarded, saturation, and extraction rule families. |
| Explain predicated types in the Dovetail/Rho backend plan. | [Concepts and Glossary](01-concepts-and-glossary.md) defines predicated types, guard sublanguages, typed predicates, structural predicates, behavioral predicates, theory routing, guard obligations, and guard dispositions; [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md#7-guarded-rules) maps `guards {}` inventory to guarded Dovetail rules; [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md#predicated-type-lowering-contract) maps predicated-type guards to RhoNet guarded contracts, atomic joins, EBA/SFT dispositions, native handlers, or explicit blockers; [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md#predicated-type-and-guard-coverage) adds predicated-type coverage to the flip gate. |
| Distinguish structural and behavioral predicated types. | [Concepts and Glossary](01-concepts-and-glossary.md#language-and-rewrite-terms) defines both terms; [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md#7-guarded-rules) states the structural-first and behavioral-after-match semantics; [Correctness and Coverage](06-correctness-and-coverage.md#theorem-7a-guard-obligation-coverage) proves accepted Rho plans exactly cover both kinds through compatible dispositions. |
| Explain EBA integration. | [Concepts and Glossary](01-concepts-and-glossary.md#language-and-rewrite-terms) defines effective Boolean algebra; [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md#guard-obligation-coverage) explains EBA dispositions for decidable predicate domains; [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md#predicated-type-and-guard-coverage) tells implementers when to choose an EBA disposition. |
| Explain SFT/SFST integration. | [Concepts and Glossary](01-concepts-and-glossary.md#language-and-rewrite-terms) defines symbolic finite-state transducer; [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md#guard-obligation-coverage) explains SFT dispositions for symbolic transformations and pre-image reasoning; [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md#predicated-type-and-guard-coverage) records the production evidence rule. |
| Explain generalized predicated types over all data domains. | [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md#guard-obligation-coverage) states the obligation/disposition mechanism for scalar, algebraic, collection, process/name, and host-backed values; [Production Runtime Backend Completion Guide](08-production-runtime-backend-completion.md#predicated-type-and-guard-coverage) gives the implementation checklist; [Correctness and Coverage](06-correctness-and-coverage.md#theorem-7a-guard-obligation-coverage) states the accepted-plan theorem. |
| Explain compilation of rewrite semantics into a Rho-native dataflow network. | [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md) defines RhoNet, the lowering correspondence, examples, semi-naive channels, rule lowering, deduplication, and name discipline. |
| Explain how RSpace schedules enabled rewrites in parallel. | [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md) maps Dovetail readiness to RSpace readiness, describes atomic joins, disjoint-channel independence, fairness, and ambiguity preservation. |
| Include mathematical and logical proofs of correctness and coverage. | [Correctness and Coverage](06-correctness-and-coverage.md) states and proves saturation soundness/completeness, Rho lowering soundness/completeness, ambiguity preservation, exact-key deduplication, guard atomicity, parallel independence, observation correctness, coverage honesty, and final preservation. |
| Ensure citations exist and are accurately represented. | [References](references.md) records process-calculus, tuple-space, rewrite-system, equality-saturation, weighted-extraction, formal-method, and repository-local sources, with DOI links where available. |
| Link citations to DOIs where available. | DOI links are included for Rho calculus, π-calculus, join calculus, Linda, Huet confluence, and equality saturation in [References](references.md). |
| Tie documentation to repository-local design and proof sources. | [References](references.md) includes Dovetail design docs, the Rholang target design, Rho-flip design docs, Dovetail formal theories, Rho bridge formal theories, and the formal coverage matrix. |
| Extract operational invariants from the north-star paper and settle the matching-execution-locus question. | [Knotted-Topoi Operational Invariants](13-knotted-topoi-operational-invariants.md) extracts the context-labelled-transition-system invariants from [KNOTTED-TOPOI-2026](references.md#knotted-topoi-2026), maps each to the `rholang-codegen` lowering and the `formal/rocq/rho_bridge` suite, and records the evidence-grounded verdict that host-side (set-automaton) matching plus Rho `σ`-injection is a faithful realization. |

## Consistency Conditions

The suite must satisfy these local consistency checks:

| Check | Required result |
|---|---|
| PlantUML balance | Every PlantUML opening marker has a matching closing marker. |
| rendered diagrams | Every PlantUML block has matching `figures/*.puml` source and a non-empty rendered `figures/*.svg` image with an SVG root and closing tag; every `figures/*.dot` source also has a non-empty rendered SVG image. |
| fenced-block balance | Every fenced block has a closing fence. |
| proof-hole marker scan | No admitted proofs, unsupported axioms, or unproved conjectures appear in the documentation text. |
| completion-marker scan | No unfinished-work wording appears in this suite. |
| internal Markdown links | Every relative `.md` link resolves to an existing file. |
| bibliography paths | Every local path listed in [References](references.md) resolves from the repository root. |
| online bibliography links | Every DOI resolves through Crossref and every non-DOI external bibliography link resolves over HTTP when `validate.sh --online` is run with network access. |

These checks are structural. They complement, but do not replace, the proof and
test commands listed in [Verification and Rollout](07-verification-and-rollout.md).
Run them with:

```text
docs/architecture/rho-native-integration/validate.sh
```

Run `docs/architecture/rho-native-integration/validate.sh --online` to include
DOI and external-link checks.
