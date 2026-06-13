# Rho-Native MeTTaIL Integration

Last updated: 2026-06-13

This documentation explains how MeTTaIL, Dovetail, Rholang, F1r3node, RSpace,
and the Rho machine fit together.

Scope note: this integration is a replacement path for the CESK runtime backend.
It is not a replacement for the active WPDA parser/recognizer, and it does not
delete the Ascent reference/oracle path used for differential evidence. Ascent
is legacy for production rewrite execution; its retained role here is oracle
evidence during rollout.

The theoretical background is the Rho calculus
([RHO-2005](references.md#rho-2005)), mobile-process calculi
([PI-1992-I](references.md#pi-1992-i),
[PI-1992-II](references.md#pi-1992-ii)), tuple-space coordination
([LINDA-1985](references.md#linda-1985)), and join-style synchronization
([JOIN-2000](references.md#join-2000)). The implementation-facing behavior of
Rholang and RSpace is taken from the F1r3node documentation
([RHOLANG-DOCS](references.md#rholang-docs),
[RSPACE-DOCS](references.md#rspace-docs)).
The repository-local design lineage comes from the Dovetail engine plans
([DOVETAIL-DESIGN-DOCS](references.md#dovetail-design-docs)), the prior
Rholang target design ([RHOLANG-TARGET-DESIGN](references.md#rholang-target-design)),
and the M-RHO execution-contract work
([RHO-FLIP-DESIGN](references.md#rho-flip-design)).

The short version:

1. A user writes a snippet in a language modeled by MeTTaIL.
2. MeTTaIL parses the snippet and produces typed terms.
3. Dovetail gives those terms a rewrite semantics: equations, rewrites,
   folds, guards, exact keys, saturation, and ambiguity-preserving extraction.
4. The Rho backend lowers the Dovetail rewrite network into Rho-native
   dataflow: facts are RSpace messages, rules are persistent Rholang contracts,
   and multi-premise rewrites are atomic RSpace joins.
5. F1r3node's RhoRuntime executes the resulting Rholang/RSpace network using
   native parallel `P | Q`, non-blocking sends, persistent receives, joins,
   checkpointing, replay logs, and cost/funding machinery.

The design goal is not to make F1r3node depend on MeTTaIL. MeTTaIL remains the
frontend/compiler, while F1r3node remains the runtime. The dependency direction
is one-way: MeTTaIL bridge crates may depend on F1r3node crates; F1r3node does
not depend on MeTTaIL.
The backend therefore reuses F1r3node's existing Rholang interpreter, RSpace
matcher, replay/checkpoint machinery, and cost/funding path; it does not define
a parallel Rho machine inside MeTTaIL.

## Reading Paths

For principals who need an accurate at-a-glance view:

1. [Executive Brief](00-executive-brief.md)
2. [End-to-End Architecture](02-end-to-end-architecture.md)
3. [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md)
4. [Correctness and Coverage](06-correctness-and-coverage.md)

For implementers:

1. [Concepts and Glossary](01-concepts-and-glossary.md)
2. [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md)
3. [RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md)
4. [Verification and Rollout](07-verification-and-rollout.md)

For reviewers checking claims and citations:

1. [Requirements Traceability](00-requirements-traceability.md)
2. [Correctness and Coverage](06-correctness-and-coverage.md)
3. [References](references.md)

## Document Map

| Document | Question answered |
|---|---|
| [00 — Executive Brief](00-executive-brief.md) | What should principals understand at a glance? |
| [00 — Requirements Traceability](00-requirements-traceability.md) | Where is each explicit documentation requirement satisfied? |
| [01 — Concepts and Glossary](01-concepts-and-glossary.md) | What do all names, symbols, and acronyms mean? |
| [02 — End-to-End Architecture](02-end-to-end-architecture.md) | How does a source snippet become native Rho execution? |
| [03 — Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md) | What rewrite rules does Dovetail implement? |
| [04 — Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md) | How are rewrite semantics compiled into Rholang/RSpace? |
| [05 — RSpace Parallel Scheduling](05-rspace-parallel-scheduling.md) | Why does RSpace naturally schedule enabled rewrites in parallel? |
| [06 — Correctness and Coverage](06-correctness-and-coverage.md) | What is proved, under which assumptions, and what is not claimed? |
| [07 — Verification and Rollout](07-verification-and-rollout.md) | How does M-RHO.0 through M-RHO.4 land safely? |
| [References](references.md) | Which papers, docs, and formal artifacts support the design? |
| [Validation Script](validate.sh) | How are the documentation structure checks reproduced locally? |

## Architecture at a Glance

![Rho-native MeTTaIL integration component view](figures/README.svg)

PlantUML source: [figures/README.puml](figures/README.puml).

```plantuml
@startuml
title Rho-Native MeTTaIL Integration — Component View

skinparam backgroundColor #FEFEFE
skinparam componentStyle rectangle
skinparam shadowing false
skinparam ArrowColor #374151
skinparam ArrowThickness 1.4
skinparam component {
  BorderColor #1F2937
  FontColor #111827
}

rectangle "MeTTaIL\nlanguage frontend" as M #DBEAFE {
  component "Grammar + parser" as Parser #BFDBFE
  component "Typed AST" as AST #BFDBFE
  component "Language metadata" as Metadata #BFDBFE
}

rectangle "Dovetail\nrewrite semantics" as D #DCFCE7 {
  component "Exact keys" as Keys #BBF7D0
  component "E-graph + facts" as EGraph #BBF7D0
  component "Saturation" as Saturation #BBF7D0
  component "Extraction" as Extraction #BBF7D0
}

rectangle "Rho backend\ncompile-time bridge" as B #FEF3C7 {
  component "RhoNet IR" as RhoNet #FDE68A
  component "Rholang AST builder" as AstBuilder #FDE68A
  component "Oracle harness" as Oracle #FDE68A
}

rectangle "F1r3node / Rholang\nruntime substrate" as F #FCE7F3 {
  component "RhoRuntime" as Runtime #FBCFE8
  component "RSpace" as RSpace #FBCFE8
  component "Replay + checkpoints" as Replay #FBCFE8
  component "Cost / funding" as Cost #FBCFE8
}

Parser --> AST : parsed terms
AST --> Metadata : typed categories
AST --> EGraph : initial facts
Metadata --> Saturation : rule inventory
Keys --> EGraph : exact identity
EGraph --> Saturation : fact base
Saturation --> Extraction : candidate derivations
Saturation --> RhoNet : supported rewrite network
RhoNet --> AstBuilder : contracts + channels
AstBuilder --> Runtime : normalized Rholang AST (`Par`)
Runtime --> RSpace : produce / consume / join
RSpace --> Replay : event log
Runtime --> Cost : funded execution
RSpace --> Oracle : resting-space facts
Oracle --> Extraction : differential comparison

legend right
  <#DBEAFE> MeTTaIL: frontend/compiler
  <#DCFCE7> Dovetail: rewrite semantics
  <#FEF3C7> Rho backend: lowering and oracle
  <#FCE7F3> F1r3node: execution substrate
endlegend
@enduml
```

## Core Principle

The Rho backend should not implement a Rust scheduler that competes with RSpace.
It should compile rewrite semantics into a Rho-native dataflow network:

- facts are messages;
- rewrite rules are persistent contracts;
- multi-premise rules are atomic joins;
- guards are RSpace commit predicates or native guard handlers;
- ambiguity is explicit candidate data;
- RSpace readiness is the scheduler.

In formula form, the Dovetail fact iteration is:

`Fᵢ₊₁ = Fᵢ ∪ Δᵢ₊₁`

`Δᵢ₊₁ = derive(Fᵢ, Δᵢ) ∖ Fᵢ`

The Rho-native lowering preserves the same fixed point for the covered runtime
semantics, but lets RSpace discover enabled instances by communication instead
of by the CESK runtime backend's centralized scheduling path.

## Local Validation

Run the documentation suite checks from the repository root:

```text
docs/architecture/rho-native-integration/validate.sh
```

The script checks unfinished-work markers, proof-hole markers, fenced-block
balance, PlantUML marker balance, PlantUML syntax, math-symbol formatting,
rendered PlantUML SVG assets, relative Markdown/source/image links,
bibliography-local paths, and `git diff --check` whitespace diagnostics. Link
and whitespace checks include `README.md`, `docs/README.md`, and
`docs/architecture.md` so the suite remains discoverable from the project and
documentation entry points.

When network access is available, run the DOI and external-link checks as well:

```text
docs/architecture/rho-native-integration/validate.sh --online
```
