# Runtime Backend Replacement Spine

Last updated: 2026-06-14

This page is the connective tissue between the standalone
[Dovetail rewrite-engine suite](dovetail/README.md) and the
[Rho-native integration suite](rho-native-integration/README.md). It exists so
a reader can understand the whole runtime-backend replacement path before
opening the deeper design documents.

Here, **backend** means **runtime backend**. The active WPDA parser/recognizer
remains the source-to-typed-term frontend. The replacement work is about what
happens after parsing.

## One-Sentence Model

MeTTaIL defines and parses languages, Dovetail proves and reports
substrate-neutral rewrite consequences, and the Rho backend optionally compiles
complete Dovetail reports into host Rho-machine work executed by F1r3node.

The compact artifact spine is:

`language! specification → LanguageDef → LanguageMetadata → typed AST → DovetailRunReport → backend artifact → RuntimeBackendReport`

There are two production runtime lanes after the Dovetail report:

| Lane | Artifact chain | Purpose |
|---|---|---|
| direct Dovetail runtime | `DovetailRunReport → RuntimeDovetailRunReport → RuntimeBackendOutput::Dovetail` | expose checked rewrite evidence as the selected runtime result |
| Rho-native runtime | `DovetailRunReport → RhoNet plan → rhoapi::Par → RhoRuntime → RSpace observations → RuntimeBackendReport` | execute covered rewrite semantics as host Rho-machine dataflow |

Both lanes are runtime-backend paths. Neither replaces the parser.

## Responsibilities

| Layer | Owns | Does not own |
|---|---|---|
| `language!` and macro expansion | categories, constructors, syntax, equations, rewrites, guards, handlers, generated inventory | runtime scheduling, Dovetail exact-key proofs, Rho execution |
| WPDA parser/recognizer | source text to typed AST terms | runtime backend selection |
| Dovetail | exact keys, equality saturation, rule saturation, extraction, weights, boundedness, reports | parser generation, hard-coded category lists, RhoRuntime execution |
| direct Dovetail adapter | projection of complete checked reports into `mettail-runtime` report-shaped output | Rho lowering or RSpace observation |
| Rho backend | RhoNet planning, normalized `rhoapi::Par` AST generation, explicit rejection of uncovered rules | Rholang text reparsing, custom Rho machine implementation |
| F1r3node/RhoRuntime/RSpace | Rholang AST execution, COMM, joins, scheduling, replay, checkpoints, cost/funding | MeTTaIL language definition or Dovetail proof construction |
| Ascent path | reference/oracle evidence during rollout | production rewrite execution after Dovetail/Rho gates pass |
| CESK runtime backend | legacy runtime backend path | final target runtime backend after the Rho gate is satisfied |

The main dependency rule is:

`MeTTaIL bridge crates → F1r3node crates`

and not:

`F1r3node crates → MeTTaIL crates`

## Terms Not To Conflate

| Term | Meaning | Reader check |
|---|---|---|
| `LanguageDef` | macro-time language model parsed from `language!` | before Rust code generation |
| `LanguageMetadata` | generated inventory of categories, constructors, rules, guards, handlers, and backend capabilities | available from generated language crates |
| typed AST | source-language term produced by the retained parser | input to runtime backend execution |
| `SatReport` | Dovetail saturation terminal status and statistics | says how equality/rewrite growth stopped |
| `Extraction<T>` | Dovetail extracted value plus terminal completeness | keeps `Complete` and `BoundedByCycleCut` explicit |
| `DovetailRunReport` | exact-keyed derivation forest for downstream consumers | before runtime execution |
| `rhoapi::Par` | normalized host Rholang AST value | executable artifact, not Rholang source text |
| Rho observation | ground value left in RSpace after host execution | after runtime execution |
| `RuntimeBackendReport` | generic MeTTaIL runtime envelope | shape must match selected backend |

The negative rule is:

`DovetailRunReport ≠ rhoapi::Par ≠ RhoObservationReport ≠ RuntimeBackendReport`

Each object sits at a different phase boundary and carries different evidence.

## End-To-End Trace

| Step | Input | Output | Cohesion rule |
|---:|---|---|---|
| 1 | `language!` body | `LanguageDef` | the macro is the source of truth for categories and rules |
| 2 | validated `LanguageDef` | generated AST types and `LanguageMetadata` | downstream engines discover inventory, not hard-coded category lists |
| 3 | source snippet | typed AST term | WPDA parsing remains active |
| 4 | typed AST plus metadata | `SatReport` and `DovetailRunReport` | Dovetail preserves exact identity, ordering, and completeness |
| 5a | complete Dovetail report | `RuntimeBackendOutput::Dovetail` | direct Dovetail runtime stays report-shaped |
| 5b | complete Dovetail report | `RhoNet plan` | Rho lowering is total-or-explicit-reject |
| 6 | RhoNet plan | `rhoapi::Par` | generated execution artifact is AST, never text to reparse |
| 7 | `rhoapi::Par` | RSpace resting observations | host RhoRuntime owns scheduling and COMM |
| 8 | backend-specific result | `RuntimeBackendReport` | output shape must match backend identity |

The direct Dovetail lane uses steps 1 through 5a and 8. The Rho-native lane
uses steps 1 through 4 and then 5b through 8.

## Correctness Spine

The runtime replacement claim is a composition of smaller claims:

`LanguageInventoryValid ∧ DovetailReportComplete ∧ RhoLoweringCovered ∧ RhoArtifactValid ∧ FairRSpaceSchedule ∧ RuntimeReportShapeValid`

For the direct Dovetail lane, the Rho-specific conjuncts are not required:

`LanguageInventoryValid ∧ DovetailReportComplete ∧ RuntimeReportShapeValid`

For the Rho-native lane, the intended observational preservation theorem is:

`obs(run_Rho(lower(report_Dovetail(L, t)))) = project(report_Dovetail(L, t))`

where `L` is a language, `t` is a typed source term, `report_Dovetail(L, t)` is
a complete checked Dovetail report, and `obs` projects the host RhoRuntime's
resting-space result to the documented runtime observation quotient.

Bounded evidence is not discarded, but it is not an exhaustive runtime success:

`completeness(report) = BoundedByCycleCut ⇒ ¬ProductionComplete(report)`

## Reader Path

Use this route when trying to understand or continue the work:

1. Read this page for the artifact spine and ownership boundaries.
2. Read [Dovetail Architecture](dovetail/README.md) for the standalone rewrite
   engine.
3. Read [Runtime-Facing Reports](dovetail/10-runtime-facing-reports.md) for
   the report boundary and MiniRhoFor example.
4. Read [Rho-Native Integration](rho-native-integration/README.md) for the
   whole MeTTaIL/Dovetail/F1r3node chain.
5. Read [End-to-End Architecture](rho-native-integration/02-end-to-end-architecture.md)
   for component contracts and execution modes.
6. Read [Rho-Native Dataflow Lowering](rho-native-integration/04-rho-native-dataflow-lowering.md)
   for AST-first lowering and RSpace scheduling.
7. Read [Production Runtime Backend Completion Guide](rho-native-integration/08-production-runtime-backend-completion.md)
   for the remaining production gates.

## Implementation Checklist

```text
When changing runtime backend behavior:
  Keep parsing concerns in the language/WPDA layer.
  Derive category and rule inventories from generated metadata.
  Preserve Dovetail report exact keys, root order, child indexes, and completeness.
  Reject incomplete Dovetail reports before production Rho execution.
  Generate normalized rhoapi::Par AST values, not Rholang source text.
  Let F1r3node/RSpace schedule enabled Rho communications.
  Return a RuntimeBackendReport whose output shape matches the selected backend.
  Update the relevant Dovetail proof, Rho bridge proof, docs, and coverage matrix.
```

This checklist is intentionally phase-oriented. Most mistakes in this part of
the system come from moving evidence across a boundary while silently changing
what the evidence means.
