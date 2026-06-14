# End-to-End Architecture

Last updated: 2026-06-14

This document explains the whole execution path from a source-language snippet
to native execution on F1r3node's Rho machine, scoped to replacement of the CESK
runtime backend path.

All symbols used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## Design Thesis

The integration should preserve the best responsibility boundary for each
system:

| System | Primary responsibility | Reason |
|---|---|---|
| MeTTaIL | Model and parse source languages. | It already owns grammar, typed terms, metadata, and user-facing language definitions. |
| Dovetail | Define substrate-neutral rewrite semantics. | It can prove exact-key, saturation, cycle, and extraction properties without assuming a runtime. |
| Rho backend | Lower Dovetail semantics to Rho-native dataflow. | It is the bridge between rewrite facts and RSpace communication. |
| F1r3node / Rholang / RSpace | Execute concurrent processes. | RSpace already owns communication, joins, replay, checkpointing, and parallel scheduling. |

The key architectural move is a runtime-backend move:

`CESK runtime backend scheduling` → `Rho-native dataflow network`

In the centralized model, an engine repeatedly scans rules and facts. In the
Rho-native model, facts are messages and rules are persistent contracts.
Readiness is discovered by RSpace communication.

This move is deliberately downstream of parsing. The active WPDA
parser/recognizer still produces the typed terms consumed by Dovetail, and
Ascent is legacy for production rewrite execution. Its retained role is the
reference/oracle path used by differential gates while Dovetail/Rho becomes the
production rewrite path.

This follows the tuple-space idea that communication can be mediated through a
shared space ([LINDA-1985](references.md#linda-1985)), the process-calculus view
that communication is an operational reduction ([PI-1992-I](references.md#pi-1992-i)),
and Rholang's reflective names and COMM rule
([RHO-2005](references.md#rho-2005),
[RHOLANG-DOCS](references.md#rholang-docs)).

## `language!` Versus Dovetail And The Rho Backend

The `language!` macro, Dovetail, and the Rho backend all mention terms,
constructors, rules, and normal forms. They differ by ownership.

`language!` is the source-of-truth specification mechanism for a modeled
language. It declares categories, constructors, concrete display forms,
parsing hooks, equations, rewrites, native folds, guards, predicates, and
metadata. Its expansion produces typed Rust AST values and language inventory
that other crates can consume. When the category set changes, that inventory is
the authority; downstream backends should discover the categories from the
generated metadata instead of keeping hard-coded category whitelists.

Dovetail is not a competing specification macro. It is the rewrite engine that
consumes the inventory emitted by `language!`. It gives the declared equations
and rewrites exact identities, saturates them, extracts alternatives, and emits
checked reports with terminal completeness metadata. It does not own concrete
syntax, category declarations, parser generation, language crate generation,
or native handler implementations.

The Rho backend is not a competing specification macro either. It consumes a
complete Dovetail report, classifies the covered rewrite network as Rho-native
dataflow, and emits normalized Rholang AST values. Documentation may show
Rholang text annotations because they are readable, but the generated execution
artifact is AST such as `rhoapi::Par`, not text that will be reparsed. That AST
boundary is deliberately bytecode-ready: a later Rholang bytecode emitter can
target the same normalized artifact contract.

The ownership pipeline for directly covered Rho-native rewrites is:

`language! spec → semantic inventory → Dovetail reports → RhoNet plan → rhoapi::Par → RhoRuntime observations → RuntimeBackendReport`

The generic call-by-need segment uses the same AST-first execution boundary:

`generated-language computation → RhoAstLiteral payload → CallByNeedThunkSpec → CallByNeedThunkPlan → rhoapi::Par`

| Concern | `language!` | Dovetail | Rho backend |
|---|---|---|---|
| language categories | declares them | consumes generated inventory | uses inventory-derived channels and tags |
| typed AST | generates source-language terms | stores exact-keyed terms and derivations | lowers covered terms to Rholang AST |
| concrete syntax | owns parser/display hooks | does not parse source text | may attach reader text only as annotation |
| rewrite declarations | declares rules and metadata | saturates, extracts, and reports checked consequences | compiles covered rule instances to Rho dataflow |
| predicated types | declares `guards {}` syntax, typed predicates, theory routing, and channels | consumes generated guard inventory as guarded rules | lowers covered guards to RhoNet guards, atomic joins, or native guard handlers |
| native operations | declares and binds handlers | records explicit external contracts | routes handlers through Rho/native boundary |
| runtime scheduling | does not schedule | defines substrate-neutral rewrite semantics | lets RSpace schedule enabled COMM events |
| completeness status | supplies requirement inventory | reports `Complete` or `BoundedByCycleCut` | rejects incomplete reports for production execution |

The apparent overlap is therefore intentional provenance tracking. Dovetail and
the Rho backend repeat enough rule and constructor information to prove that
execution preserves the `language!` semantics, but they do not replace the
macro as the language-definition authority.

Predicated types follow the same ownership rule. The language definition owns
the guard sublanguage and typed predicate metadata; Dovetail turns that
inventory into guarded rewrite obligations; the Rho backend can execute only
covered guards whose no-commit behavior is preserved by RSpace or a verified
native guard handler.

## End-To-End Artifact Spine

The most useful way to read the design is as a sequence of typed artifacts. No
stage should be understood as "the system just has a term now"; every stage
adds or preserves a specific contract.

| Stage | Input | Output | Contract preserved |
|---:|---|---|---|
| 1. macro parse | `language!` token stream | `LanguageDef` | the language specification has a typed macro-time model |
| 2. code generation | validated `LanguageDef` | typed AST constructors and `LanguageMetadata` | downstream code can derive categories and rules from generated inventory, not hard-coded lists |
| 3. snippet parse | source snippet | typed AST term | the active WPDA parser produced a source-language value |
| 4. Dovetail execution | typed AST term plus metadata | `SatReport` and `DovetailRunReport` | rewrite consequences are exact-keyed, ordered, and explicitly complete or bounded |
| 5a. direct Dovetail runtime | complete Dovetail report | `RuntimeBackendOutput::Dovetail` | the runtime exposes Dovetail evidence without fabricating an Ascent graph |
| 5b. Rho planning | complete Dovetail report | `RhoNet plan` | covered rewrites become dataflow contracts and uncovered rewrites are explicit rejections |
| 5c. call-by-need planning | generated-language computation | `CallByNeedThunkSpec` and `CallByNeedThunkPlan` | thunk payload is a closed `RhoAstLiteral`, channels are generated-language parameters, and budget admission plus AST validation are explicit |
| 6. AST generation | RhoNet plan or `CallByNeedThunkPlan` | normalized `rhoapi::Par` | executable output is host Rholang AST, not source text to reparse |
| 7. Rho execution | `rhoapi::Par` | RSpace observations | F1r3node's RhoRuntime and RSpace own COMM, joins, scheduling, replay, and checkpointing |
| 8. runtime return | backend-specific output | `RuntimeBackendReport` | the caller receives an envelope whose shape matches the selected backend |

The split at stage 5 is intentional:

`stage 5a = use Dovetail as the production rewrite backend`

`stage 5b-7 = use Dovetail evidence to generate and execute Rho-native work`

`stage 5c-7 = use a planned call-by-need thunk to execute a generated computation through RhoRuntime`

Both are runtime-backend paths. Neither replaces the parser. The direct
Dovetail path is valuable when the checked rewrite report itself is the runtime
answer. The Rho-native path is valuable when the checked report can be compiled
into host Rho-machine parallelism.

The same split can be read as two cohesive tracks:

| Track | Starts with | Ends with | Main invariant |
|---|---|---|---|
| language-definition track | `language!` body | generated `LanguageMetadata` | categories, constructors, rules, guards, and handlers come from one source of truth |
| snippet-execution track | parsed typed AST | selected runtime output | the runtime output must be derived from checked Dovetail evidence or explicit rejected/delegated contracts |

Those tracks meet when a parsed term is paired with generated metadata. From
that point forward, the backend does not rediscover syntax by string inspection
or hard-coded category names. It consumes the typed term and inventory, then
preserves the evidence through Dovetail and the selected runtime lane.

### Cohesion Checkpoints

Before reading a later section as an implementation detail, identify which
checkpoint it belongs to:

| Checkpoint | Stable artifact | Allowed next step |
|---|---|---|
| language definition | `LanguageDef` | generate typed AST constructors and metadata |
| generated inventory | `LanguageMetadata` | derive Dovetail rules and backend coverage requirements |
| parsed snippet | typed AST | select a runtime backend and seed Dovetail |
| rewrite evidence | `SatReport` plus `DovetailRunReport` | return direct Dovetail output or lower a complete report |
| Rho plan | `RhoNet plan` or `CallByNeedThunkPlan` | validate and build normalized `rhoapi::Par` |
| executable artifact | `rhoapi::Par` | inject into host `RhoRuntime` |
| runtime observation | resting RSpace facts | construct the selected `RuntimeBackendReport` |

These checkpoints give each repeated diagram, formula, and example a fixed
place in the architecture. They also make two negative claims precise:
Dovetail does not execute Rho processes, and the Rho backend does not recover
semantics by reparsing text.

For the MiniRhoFor example used in the Dovetail report documentation, the
cohesive trace is:

`language! MiniRhoFor → LanguageDef → LanguageMetadata → Comm Dovetail rule`

then, for one run:

`{ for (x <- a) { x!(z) } | a!(b) } → Proc::PPar(...) → DovetailRunReport({ b!(z) }) → rhoapi::Par(send b z) → RSpace observation`

The Rholang-looking `send b z` notation in that trace is a reader annotation.
The generated runtime artifact is a normalized `rhoapi::Par` AST. This is both
the current fast path into `RhoRuntime::inj` and the future handoff point for a
Rholang bytecode artifact.

## High-Level Dispatch Trace

The highest-value mental model is two tracks that meet at generated inventory:

| Track | Time | Producer | Output |
|---|---|---|---|
| language-definition track | macro expansion | `language!` parser and validator | `LanguageDef`, typed AST definitions, and `LanguageMetadata` |
| snippet-execution track | runtime invocation | generated language value plus selected backend wrapper | `RuntimeBackendReport` |

For MiniRhoFor, the language-definition track is:

```text
language! specification
  -> LanguageDef
  -> generated Proc and Name AST constructors
  -> generated LanguageMetadata
  -> metadata-derived Dovetail rules: Comm and ParCong
```

The snippet-execution track is:

```text
source snippet
  -> WPDA parser
  -> typed Proc AST
  -> Language::run_default_backend_report
  -> selected runtime backend
```

After dispatch, the selected backend determines the final lane:

| Selected runtime backend | Execution lane | Output shape |
|---|---|---|
| `RuntimeBackend::Dovetail` | `typed Proc AST + LanguageMetadata → SatReport → DovetailRunReport → RuntimeDovetailRunReport` | report-shaped `RuntimeBackendOutput::Dovetail` |
| `RuntimeBackend::RhoMachine` | `complete DovetailRunReport → RhoNet plan → rhoapi::Par → RhoRuntime → RSpace observations` | observation-shaped `RuntimeBackendReport` |
| `RuntimeBackend::Ascent` | generated legacy relation execution | oracle or compatibility output during rollout |

This dispatch trace is intentionally high-level. It names the shape-changing
boundaries without requiring the reader to learn every generated Rust type
first. The important cohesion rule is that every runtime lane starts from the
same language-owned typed AST and metadata, then either exposes a checked
Dovetail report or executes a Rho artifact derived from a complete report.

The MiniRhoFor `language!` fixture in
[`macros/src/doc_examples.rs`](../../../macros/src/doc_examples.rs) parses and
validates as a `LanguageDef`. That fixture is the syntax guard for the example
shown in [Dovetail Runtime-Facing Reports](../dovetail/10-runtime-facing-reports.md#minirhofor-report-example).

## Bridge Crate Boundary

The design uses small one-way bridge crates rather than a runtime fork:

| Crate | Boundary role |
|---|---|
| `dovetail` | substrate-neutral rewrite engine and formal reference |
| `mettail-rho-codegen` | compile-time lowering from Dovetail/RhoNet to Rholang-facing artifacts |
| `mettail-rho-runtime` | binding to F1r3node's RhoRuntime and observation/oracle harness |
| `mettail-rho-adapter` | OSLF/GSLT cost and funding adapter consumed by F1r3node gates |

The boundary is intentionally asymmetric:

`MeTTaIL bridge crates → F1r3node crates`

and not:

`F1r3node crates → MeTTaIL`

That asymmetry preserves F1r3node as the production Rho-machine substrate and
keeps Dovetail extractable as a substrate-neutral rewrite engine. It also
matches the repository-local Rho target design
([RHOLANG-TARGET-DESIGN](references.md#rholang-target-design)) and M-RHO
execution contract ([RHO-FLIP-DESIGN](references.md#rho-flip-design)).

## Source-to-Runtime Lifecycle

![Source snippet to selected runtime backend sequence](figures/02-end-to-end-architecture.svg)

PlantUML source:
[figures/02-end-to-end-architecture.puml](figures/02-end-to-end-architecture.puml).

The diagram is intentionally drawn around the branch after
`DovetailRunReport`. A direct Dovetail runtime backend returns a report-shaped
`RuntimeBackendOutput::Dovetail`. A Rho runtime backend consumes the same
complete report, lowers it to `rhoapi::Par`, injects that AST into F1r3node,
and returns observation-shaped output through `RuntimeBackendReport`. The
branch point is the cohesion rule: Dovetail finishes before runtime execution;
selected runtime backends decide how the checked report is exposed or executed.

## Component Contracts

### MeTTaIL Contract

MeTTaIL supplies:

- a typed term grammar;
- a parser from source text to terms;
- equations `t ≡ u`;
- directed rewrites `t →ᵣ u`;
- native/fold handlers;
- guard and predicate metadata;
- the inventory of categories and constructors.

MeTTaIL does not decide the runtime schedule. It describes the semantics.

### Dovetail Contract

Dovetail consumes MeTTaIL metadata and produces a rewrite model:

- exact term/e-class keys;
- initial facts;
- rule instances;
- saturation outcomes;
- candidate derivations;
- normal-form candidate sets;
- explicit boundedness information when a cyclic extraction cannot be exhaustive.

The Dovetail contract can be summarized as:

`covered(requirement) ⇒ core_proven(requirement) ∨ external_contract(requirement)`

That formula means each MeTTaIL rewrite requirement must either be handled by
proved Dovetail core behavior or delegated to an explicit native/Rho contract.
Silent gaps are not allowed.

### Rho Backend Contract

The Rho backend consumes the Dovetail model and emits:

- a RhoNet dataflow network;
- normalized Rholang AST (`models::rhoapi::Par`) for the supported fragment;
- structured dynamic call and witness payloads as `RhoAstLiteral` values that
  lower directly to `Par`, including scalar, collection, unforgeable-name, and
  rhocalc bag ABI payloads;
- Rholang-text annotations for readers, logs, and documentation;
- native handler registrations for operations that cannot be rendered as pure
  Rholang expressions;
- a differential oracle harness that compares Rho observations with Dovetail or
  Ascent reference behavior.

The Rho backend must be total-or-explicit-reject:

`∀r ∈ Rules. lowered(r) ∨ rejected(r)`

The existing M-RHO.0 lowering proof establishes this shape for the scalar
operator subset. The Rho-native roadmap generalizes the same discipline to
communication, guarded rules, and native handlers.

### F1r3node Contract

F1r3node supplies:

- Rholang AST execution through `RhoRuntime::inj`;
- source parsing and normalization for hand-authored regression oracles;
- RhoRuntime evaluation;
- RSpace data and continuation storage;
- atomic `produce`/`consume` matching;
- persistent receives and contracts;
- replay logs and checkpoints;
- cost and funding checks.

F1r3node does not import MeTTaIL. The bridge is one-way.
The current repository-local bridge proof is recorded in
[RHO-BRIDGE-FORMAL](references.md#rho-bridge-formal).
That proof set includes `HostRhoMachineReuse.v`, which makes accepted backend
plans depend on the host Rholang interpreter and host RSpace while excluding a
MeTTaIL-owned reducer, tuple space, matcher, or replay engine.

## Execution Modes

| Mode | Description | Used for |
|---|---|---|
| Local Dovetail | Dovetail saturates and extracts inside MeTTaIL. | Formal reference, tests, non-Rho deployments. |
| Rho differential | Both Dovetail/Ascent and Rho run; result sets are compared. | M-RHO rollout safety. |
| Rho default | Rho is the selected runtime backend for a language in place of the CESK runtime backend. | M-RHO.4 after proof, oracle, coverage, artifact-validation, scheduler-fairness, and deadlock gates. |

## Pedagogical Example: Communication

Consider the source-level rhocalc communication pattern:

```text
{ (c?x).{*(x)} | c!(p) }
```

The intended source rewrite is:

`{ (c?x).{*(x)} | c!(p) } → p`

The Rho-native lowering does not create a central evaluator that searches for
this redex. It emits a receive and a send on the same channel. RSpace performs
COMM when both are available:

```rholang
new out in {
  for (@x <- @"mtl:c") { @"mtl#out"!(x) } |
  @"mtl:c"!(p)
}
```

This example is intentionally small. Real lowering uses fresh private names,
canonical channel rendering, exact keys, and observation fingerprints.

## Literate Algorithm: End-to-End Execution

The algorithm below is pseudocode. It is not Rust, Rholang, or Rocq code.

```pseudocode
Algorithm: Execute a MeTTaIL-modeled snippet on the Rho machine

Given:
  source text S
  language definition L
  backend policy B

Produce:
  canonical result observation O

Steps:
  1. Parse S with L's MeTTaIL parser.
     The result is a typed term t.

  2. Seed Dovetail with t.
     Dovetail creates the initial fact set F₀.

  3. Classify every requirement in L.
     Each requirement is either Dovetail-core, native-handler, Rho-handler,
     or rejected with evidence.

  4. Run Dovetail on F₀ and L's generated metadata.
     Produce a SatReport and a DovetailRunReport.
     If B selects the direct Dovetail backend:
       return the checked report through RuntimeBackendOutput::Dovetail.

  5. Check the report boundary before Rho lowering.
     If the saturation outcome is not Converged:
       return bounded evidence or a gate failure, according to backend policy.
     If report completeness is BoundedByCycleCut:
       reject exhaustive Rho execution for this invocation.

  6. Lower the complete supported Dovetail report into RhoNet.
     Terms become fact messages.
     Rules become contracts.
     Multi-premise rules become joins.

  7. Lower RhoNet to normalized Rholang AST.
     The AST generator constructs the host `Par` shape directly, including
     De Bruijn indices, locally-free metadata, connective flags, bind counts,
     receive conditions, dynamic input sends, and structured ground payloads.

  8. Inject the normalized `Par` into F1r3node RhoRuntime.
     RSpace schedules every enabled COMM.

  9. At quiescence, inspect the resting space.
     Project out scheduler metadata and canonicalize names.

  10. Return the canonical observation O.
```

### Invariant

At every boundary:

`observable_facts_after_lowering ⊆ observable_facts_after_dovetail`

and, for the supported fragment under fair scheduling:

`observable_facts_after_dovetail ⊆ observable_facts_after_lowering`

Together they imply equality of observable result sets.

## Why Normalized Rholang AST?

The generated bridge path builds `models::rhoapi::Par` directly instead of
emitting text and asking a parser to recover the same AST. The reason is
performance and integration clarity: MeTTaIL is the parser/compiler layer, and
the backend artifact should be what the host interpreter consumes.

The AST generator must own and test:

- De Bruijn indexing;
- locally-free annotations;
- connective flags;
- normalization;
- bind-count conventions;
- receive condition representation.
- dynamic-send payload encoding for scalar values, collections,
  unforgeable names, and tagged rhocalc bags.

The current Rust gate checks these invariants on the generated contracts. The
Rholang-looking examples in this document are annotations for readers; they are
not a parser round-trip requirement for generated code. When Rholang bytecode is
available, it should become another backend artifact form after the same
semantic gates pass.

## What This Enables

This design allows snippets in MeTTaIL-modeled languages to run natively on
F1r3node after compilation. The runtime artifact is a Rholang/RSpace dataflow
network, not an embedded MeTTaIL interpreter.

The practical result is:

`source snippet → native Rho machine execution`

with MeTTaIL and Dovetail still available as the formal reference and
differential oracle during rollout.
