# Dovetail Rewrite Engine Architecture

Last updated: 2026-06-13

Dovetail is the standalone rewrite engine for MeTTaIL. It is not the Rho
machine backend and it is not the WPDA parser. Dovetail owns the
substrate-neutral rewrite semantics: exact-key equality saturation,
weights-as-ordering, checked best-first extraction, cyclic inside-weight
closure, explicit boundedness reports, and runtime-facing extraction reports.

The Rho-native backend consumes Dovetail semantics, but Dovetail is useful and
reviewable on its own. This suite documents Dovetail itself.

## Reading Paths

For principals:

1. [Executive Brief](00-executive-brief.md)
2. [Engine Architecture](02-engine-architecture.md)
3. [Runtime-Facing Reports](10-runtime-facing-reports.md)
4. [Formal Verification and Tests](07-formal-verification-and-tests.md)

For implementers:

1. [Concepts and Glossary](01-concepts-and-glossary.md)
2. [Data Model and Exact Keys](03-data-model-and-exact-keys.md)
3. [Rules and Saturation](04-rules-and-saturation.md)
4. [Extraction and Weights](05-extraction-and-weights.md)
5. [Cyclic Closure and Boundedness](06-cyclic-closure-and-boundedness.md)
6. [Runtime-Facing Reports](10-runtime-facing-reports.md)
7. [Worked Example](09-worked-example.md)
8. [Engineering Handoff](08-engineering-handoff.md)

For reviewers checking claims:

1. [Formal Verification and Tests](07-formal-verification-and-tests.md)
2. [References](references.md)
3. [Validation Script](validate.sh)

## Document Map

| Document | Question answered |
|---|---|
| [00 - Executive Brief](00-executive-brief.md) | What is Dovetail and why does it replace the production Ascent rewrite path? |
| [01 - Concepts and Glossary](01-concepts-and-glossary.md) | What do Dovetail symbols, acronyms, and terms mean? |
| [02 - Engine Architecture](02-engine-architecture.md) | What are the modules, ownership boundaries, and execution phases? |
| [03 - Data Model and Exact Keys](03-data-model-and-exact-keys.md) | How are e-classes, e-nodes, content keys, and reports represented? |
| [04 - Rules and Saturation](04-rules-and-saturation.md) | How are rules matched, instantiated, and saturated under budgets? |
| [05 - Extraction and Weights](05-extraction-and-weights.md) | How does Dovetail enumerate derivations without missing alternatives? |
| [06 - Cyclic Closure and Boundedness](06-cyclic-closure-and-boundedness.md) | How are cyclic inside weights exact while cyclic enumeration remains explicit about boundedness? |
| [07 - Formal Verification and Tests](07-formal-verification-and-tests.md) | Which Rocq, Why3, Creusot, example, exhaustive, and property checks cover each claim? |
| [08 - Engineering Handoff](08-engineering-handoff.md) | What does another agent need to maintain or complete Dovetail independently? |
| [09 - Worked Example](09-worked-example.md) | How does a small rewrite system move through e-graphing, saturation, extraction, and reporting? |
| [10 - Runtime-Facing Reports](10-runtime-facing-reports.md) | What is a Dovetail report, why does a rewrite engine need one, and what may downstream runtimes rely on? |
| [References](references.md) | Which local source, test, proof, and design artifacts support the suite? |

## Architecture at a Glance

![Dovetail standalone component view](figures/README.svg)

PlantUML source: [figures/README.puml](figures/README.puml).

## Diagramming Choices

The pgmcp toolbox catalog reports a dedicated diagramming domain with
PlantUML, Graphviz, Mermaid, D2, Structurizr, TikZ/PGF, WaveDrom, and related
SVG-capable tools installed. This suite uses:

| Tool | Why it is used here |
|---|---|
| PlantUML | component, lifecycle, and frontier diagrams where named architecture elements are more useful than geometric precision |
| Graphviz DOT | proof-dependency graphs, because graph layout should follow the actual dependency relation |
| SVG output | reviewable repository artifacts that render consistently in GitHub and browser-based documentation |

Other installed tools remain useful for future packet layouts, timing diagrams,
statistical plots, and publication figures, but they would add little signal to
the core Dovetail architecture pages.

## Core Contract

Dovetail treats a MeTTaIL rewrite system as a finite, exact-keyed hypergraph.
Saturation grows equality evidence. Extraction enumerates derivation trees.
Weights rank derivations; they do not delete derivations. A
[runtime-facing report](10-runtime-facing-reports.md) then packages the checked
extraction as a proof-preserving artifact rather than a human-facing log.

In these documents, "report" means a typed engineering artifact, not a prose
diagnostic. Dovetail uses reports at phase boundaries so later components know
exactly what was proved, what was enumerated, and where bounds applied:

| Artifact | Boundary | Main question answered |
|---|---|---|
| `SatReport` | saturation | Did equality growth converge, hit the node bound, or hit the iteration bound? |
| `Extraction<T>` | extraction | What value was extracted, and is it complete or bounded by a cycle cut? |
| `DovetailRunReport` | runtime handoff | Which exact roots, term records, derivation edges, and completeness status may a consumer rely on? |

The theoretical basis is equality saturation over e-graphs
([EGG-2021](references.md#egg-2021)), k-best style lazy enumeration
([HUANG-CHIANG-2005](references.md#huang-chiang-2005)), and semiring fixed-point
closure for cyclic automaton components
([ESPARZA-KIEFER-LUTTENBERGER-2008](references.md#esparza-kiefer-luttenberger-2008),
[ESPARZA-KIEFER-LUTTENBERGER-2010](references.md#esparza-kiefer-luttenberger-2010)).
The repository-local proof boundary is listed in
[Formal Verification and Tests](07-formal-verification-and-tests.md).

The central invariant is:

`∀d. Valid(d) ∧ weight(d) ≠ 0̄ ⇒ EventuallyEnumerated(d)`

The only accepted removals are evidence-based:

`Removed(d) ⇒ weight(d) = 0̄ ∨ key(d) = key(d′)`

Here `0̄` is the semiring zero, meaning semantic refutation for the chosen
weight algebra, and `key(d) = key(d′)` means exact byte-for-byte derivation-tree
identity.

## Relation To Other Subsystems

| Subsystem | Relationship |
|---|---|
| WPDA parser | Upstream producer of typed terms; not replaced by Dovetail. |
| Ascent | Legacy production rewrite backend and reference/oracle path during rollout. |
| CESK runtime backend | Runtime backend path being replaced by Dovetail plus Rho-native execution. |
| Rho backend | Downstream consumer that lowers covered Dovetail rewrite networks to `rhoapi::Par`. |
| F1r3node/RSpace | Runtime substrate for Rho execution; Dovetail does not depend on it. |
| `rigail` | Algebra crate providing semirings, weights, and Newton-SCC solving. |

## Local Validation

Run the Dovetail documentation suite checks from the repository root:

```text
docs/architecture/dovetail/validate.sh
```

Run the implementation and formal verification gates under an RSS cap:

```text
systemd-run --user --scope -p MemoryAccounting=yes -p MemoryMax=8G -p MemorySwapMax=0 -p CPUQuota=200% cargo test -j1 -p dovetail
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail FORMAL_MEMORY_MAX_BYTES=8589934592 FORMAL_MEMORY_HIGH_BYTES=7516192768
```
