# Production Runtime Backend Completion Guide

Last updated: 2026-06-14

This guide turns the architecture suite into an executable handoff for an
agent completing the runtime backend replacement. Here, **backend** means
**runtime backend**: the parser/recognizer boundary remains the WPDA path.

The target state is:

| Current role | Production role |
|---|---|
| Ascent production rewrite execution | Dovetail production rewrite execution |
| Ascent differential evidence | retained oracle evidence during rollout |
| CESK runtime backend execution | Rho machine execution on F1r3node |
| WPDA parser/recognizer | retained source-to-typed-term frontend |
| Rholang source strings as executable artifacts | direct `rhoapi::Par` AST artifacts |

The full Rho-native runtime path is therefore:

`typed MeTTaIL term -> Dovetail report -> RhoNet plan -> rhoapi::Par -> RhoRuntime -> RSpace observations -> RuntimeBackendReport`

The direct Dovetail runtime-backend path stops at the checked report:

`typed MeTTaIL term -> Dovetail report -> RuntimeDovetailRunReport -> RuntimeBackendOutput::Dovetail`

Both paths are production-relevant. Dovetail replaces the production rewrite
engine; Rho replaces the CESK runtime backend when a language has enough RhoNet
coverage to execute the checked rewrite semantics natively on F1r3node.

## Runtime Scope Diagram

![Runtime backend replacement scope](figures/08-production-runtime-backend-completion.svg)

PlantUML source:
[figures/08-production-runtime-backend-completion.puml](figures/08-production-runtime-backend-completion.puml).

## Completion Evidence DAG

![Runtime backend production readiness DAG](figures/08-production-readiness-dag.svg)

Graphviz source: [figures/08-production-readiness-dag.dot](figures/08-production-readiness-dag.dot).

The DAG is intentionally sparse. It names the evidence nodes that must all be
true before a language can select Dovetail/Rho as its production runtime path.

## Backend Inventory

| Surface | Current evidence | Production completion condition |
|---|---|---|
| `dovetail` core | exact keys, checked extraction reports, bounded-cycle completeness, saturation outcomes, Rocq/Why3/Creusot gates | every MeTTaIL runtime rewrite requirement has a Dovetail-core proof or an explicit external contract |
| `mettail-dovetail-runtime` | one-way projection from checked Dovetail reports into `RuntimeDovetailRunReport`, structural report validation, `RuntimeBackendOutput::Dovetail`, direct Dovetail default wrapper, REPL/simulation/testkit report handling, Rocq wrapper model | generated languages can select Dovetail as the production rewrite backend without fabricating Ascent-shaped graphs, accepting malformed report tables, or accepting incomplete cycle-bounded reports as exhaustive |
| `mettail-rho-codegen` | flip-gated `PlannedRhoBackend`, artifact validation, no source-text generated-backend artifacts | every supported RhoNet rule emits validated `rhoapi::Par` and every rejected rule is exactly listed |
| `mettail-rho-runtime` | host RhoRuntime injection, observation reports, COMM oracle, direct rhocalc AST lowering, checked observation-shaped `RuntimeBackendReport` conversion, `RhoRuntimeBackedLanguage` wrapper | every runtime execution surface consumes validated `Par` plans and reports typed observations through `RuntimeBackendReport` without requiring generated language crates to depend on the Rho runtime or allowing observation-shaped output under non-Rho backend/artifact identities |
| `mettail-rho-adapter` | report handoff proofs and adapter smoke coverage | complete Dovetail reports enter the Rho backend without Ascent-shaped success values |
| Ascent path | oracle and regression baseline | available only as a differential reference for languages whose Dovetail/Rho gate is still under evaluation |
| CESK runtime path | legacy runtime backend | unavailable as the selected production backend once the Rho gate is satisfied for a language |
| WPDA parser | active parser/recognizer | retained; runtime-backend work must not weaken parser guarantees |

## AST Artifact Contract

Generated runtime artifacts are `models::rhoapi::Par` values from the
F1r3node `models` crate. Rholang-looking text in documents and tests is a
reader annotation unless the test explicitly names a hand-authored source
oracle.

| MeTTaIL/rhocalc construct | Rho artifact |
|---|---|
| `PZero` | empty `Par` |
| parallel process bag `PPar` | `Par::append` over members |
| output `n!(p)` | `Send` with lowered channel and payload |
| input join `(n₁?x₁,...,nₖ?xₖ).{p}` | one `Receive` with `k` `ReceiveBind` values |
| new scope `new(x₁,...,xₖ)in{p}` | `New` with adjusted local-free metadata |
| quote/drop `@(...)` and `*(...)` | direct `Par` embedding of the quoted process |
| ground scalar literals: `Int`, `Bool`, `Str` | corresponding `ExprInstance::GInt`, `ExprInstance::GBool`, or `ExprInstance::GString` ground node |
| `List::ListLit` | `ExprInstance::EListBody` |
| `Map::MapLit` | `ExprInstance::EMapBody` |
| `Bag::BagLit` | tagged `EList` ABI: private tag plus ordered `[element, count]` entries |

Mapping a MeTTaIL bag to a Rholang set is incorrect because set lowering
discards multiplicity. The tagged list ABI preserves multiplicity and keeps the
representation nominal by using a private unforgeable tag rather than a user
string.

Dynamic calls and witness facts use the same AST discipline. The generated
builder `mettail_rho_codegen::RhoAstSend` takes `RhoAstLiteral` payloads and
constructs `Par` directly; it does not emit text for the Rholang parser to
recover. `RhoAstLiteral` covers scalar payloads, byte/URI/numeric payloads,
unforgeable names, closed list/tuple/set/map payloads, and rhocalc bags. The
bag tag constant `RHOCALC_BAG_ABI_TAG` is defined in `mettail-rho-codegen` and
re-exported by `mettail-rho-runtime`, so the producer and observer share one
nominal ABI.

## Runtime Observation Payloads

`RuntimeBackendReport` is the common user-facing envelope for Ascent,
Dovetail, and Rho-backed execution. Its output is intentionally variant-shaped:
Ascent returns a legacy rewrite graph, Dovetail returns a checked report
projection, and Rho returns runtime observations. For Rho-backed execution the
report is observation-shaped: it names a quoted RSpace channel and the ground
values left resting there. The planned Rho backend reads closed Rho ground data
into `RuntimeObservationValue`; it rejects arbitrary processes, open collection
remainders, connective bodies, sends, receives, bundles, and operator
expression bodies as non-ground observations.

| Rho ground payload | Generic runtime payload | Example lowerable rules |
|---|---|---|
| `GInt(n)` | `RuntimeObservationValue::Int(n)` | `AddInt`, `SubInt`, `MulInt`, `DivInt`, `ModInt`, unary `Neg` |
| `GBool(b)` | `RuntimeObservationValue::Bool(b)` | `EqInt`, `NeInt`, `LtInt`, `GtInt`, `LtEqInt`, `GtEqInt`, the same six comparisons for `Bool` and `Str`, plus `And`, `Or`, `Not` |
| `GString(s)` | `RuntimeObservationValue::Text(s)` | `Concat`, `AddStr`, ambiguity-witness key/payload facts |
| `GUri(u)` | `RuntimeObservationValue::Uri(u)` | URI-valued native handlers |
| `GByteArray(bytes)` | `RuntimeObservationValue::Bytes(bytes)` | byte-array native handlers and future bytecode-facing data |
| `GDouble(bits)` | `RuntimeObservationValue::DoubleBits(bits)` | bit-exact `Float` payloads |
| `GBigInt(bytes)` | `RuntimeObservationValue::BigIntBytes(bytes)` | arbitrary-precision integer payloads |
| `GBigRat(n,d)` | `RuntimeObservationValue::BigRationalBytes { numerator: n, denominator: d }` | exact rational payloads |
| `GFixedPoint(unscaled, scale)` | `RuntimeObservationValue::FixedPointBytes { unscaled, scale }` | fixed-point decimal payloads |
| unforgeable private/deploy/deployer/sysauth names | `PrivateName`, `DeployId`, `DeployerId`, or `SysAuthToken` | private channels, ABI tags, and host authority names |
| closed `EList`, `ETuple`, `ESet`, `EMap` | recursive `List`, `Tuple`, `Set`, or `Map` values | rhocalc and future language collection payloads |
| rhocalc tagged bag ABI | `RuntimeObservationValue::Bag([(value,count),...])` | `Bag::BagLit` without losing multiplicity |

A production flip must still prove coverage for the actual observed payload
domain of the language being flipped. The envelope being wider than one
language's current needs is not, by itself, a coverage proof. The current
rhocalc gate exercises the structured path in two directions: direct rhocalc
process lowering emits list, map, and bag typed AST payloads to `rhoapi::Par`,
and `RhoAstSend` emits structured dynamic send payloads for list, map, bag,
URI, byte, and private-name values. Both paths execute on the host RhoRuntime
and observe the corresponding recursive runtime values.

Scalar operation coverage is type-sensitive. The generated Rho backend must not
select Rholang operators from terminals alone because the same source token can
have different meanings after MeTTaIL type checking. For the current scalar
family:

| Typed rule | Reader-facing source shape | Required Rho AST operator |
|---|---|---|
| `Int × Int → Int` addition | `a + b` | `EPlus` |
| `Str × Str → Str` concatenation via `+` | `a + b` | `EPlusPlus` |
| `Str × Str → Str` concatenation via `++` | `a ++ b` | `EPlusPlus` |
| `τ × τ → Bool` comparisons for `τ ∈ {Int, Bool, Str}` | `==`, `!=`, `<`, `>`, `<=`, `>=` | matching comparison body |
| `Bool × Bool → Bool` logic | `and`, `or` | matching boolean body |

The proof `formal/rocq/rho_bridge/theories/RhoScalarOperatorTyping.v` captures
this contract. The executable regression
`mettail-rho-codegen::string_plus_lowers_to_rholang_concat_not_integer_plus`
then inspects the generated AST and requires Calculator `AddStr` to use
`ExprInstance::EPlusPlusBody`. Runtime wrapper tests parse `"rho" + "net"` and
observe `RuntimeObservationValue::Text("rhonet")`, completing the end-to-end
chain from source snippet through WPDA parsing, typed invocation mapping,
validated `rhoapi::Par`, RhoRuntime execution, and generic runtime report.

## Production Gates

| Gate | Required evidence |
|---|---|
| semantic coverage | coverage matrix maps each language rewrite requirement to Dovetail, RhoNet, native handler, or exact rejection |
| AST artifact purity | generated backend accepts `rhoapi::Par` artifacts and rejects source-text artifacts |
| RSpace schedule correctness | independent-redex schedules erase to the same visible Dovetail observations |
| guarded join correctness | failed guards release data and valid joins can commit afterward |
| extraction completeness honesty | complete reports and cycle-bounded reports are distinguishable at the API and proof boundary |
| runtime report shape honesty | Dovetail outputs are Dovetail-report-shaped, Rho outputs are observation-shaped and backed by Rho runtime artifacts, Ascent outputs remain Ascent-shaped, and public non-Ascent runtime reports enter only through checked constructors |
| oracle agreement | Rho observations match Ascent oracle observations for the language corpus selected for rollout |
| memory bound | capped tests and stress workloads stay within the agreed RSS envelope |
| backend selection | default runtime backend fails closed unless proof, oracle, coverage, artifact, scheduler, evidence-reference audit, and deadlock gates all pass, and every positive external gate carries nonblank stable evidence references that are either existing repository-local artifacts or explicitly allowed logical evidence namespaces |

## Generated-Language Runtime Wrapper

Generated language crates remain substrate-neutral. They expose `Language`,
metadata, parsing, environments, type inference, direct evaluation helpers, and
the explicit Ascent oracle. The Rho runtime crate supplies
`RhoRuntimeBackedLanguage<L, F>` when a language has passed the Rho flip gate
through the strict audited planner:

```text
Given a generated language L, a planned Rho backend B, and an invocation mapper F:
  build a RhoDefaultBackendPlan with plan_rho_default_backend_with_evidence_audit
  reject missing local proof/test artifacts and unapproved logical evidence namespaces
  keep L as the owner of parsing, environments, type inference, and Ascent oracle execution
  expose RhoMachine as the default runtime backend through Language methods
  delegate explicit non-Rho backend requests back to L
  map each typed term to a RhoBackendInvocation through F
  execute B with the invocation as normalized rhoapi::Par
  return RuntimeBackendReport with RhoMachine, RhoNormalizedAst, observations, and evidence refs
  reject Ascent-shaped seeded facts on the Rho path unless the fact set is empty
```

The wrapper is intentionally outside the generated language crate. This avoids
a Cargo cycle with `mettail-rho-runtime` while still allowing a verified
language instance to become Rho-default. The wrapper does not parse generated
Rholang text; invocation mappers construct `rhoapi::Par` values directly, and
future bytecode variants can use the same report boundary.
The runtime integration tests share a strict evidence-audit policy helper, so
stale proof, scheduler, or oracle evidence paths fail before a
`PlannedRhoBackend` is constructed.

The wrapper has two capability surfaces, and the distinction is operationally
important:

| Surface | Owner | Mutability | Meaning |
|---|---|---|---|
| static metadata, `LanguageMetadata::runtime_backends()` | generated language crate | compile-time constant | backends that the generated crate can execute without an external runtime wrapper |
| runtime view, `Language::runtime_backend_capabilities()` | concrete `Language` value | value-level overlay | backends executable by this particular value, including wrapper-installed defaults and plan-specific evidence references |

For a generated language such as Calculator, static metadata still advertises
the generated Ascent oracle as the default. After the language is wrapped with a
flip-gated `PlannedRhoBackend`, the runtime view starts with
`RuntimeBackendCapability { backend: RhoMachine, is_default: true, … }` and
then appends the inherited generated capabilities with their `is_default` flags
cleared. This is the reason `language.metadata().runtime_backends()` can remain
Ascent-only while `language.default_runtime_backend()` and
`language.run_default_backend_report(…)` select the Rho machine for that
wrapped value. The Rocq model
`formal/rocq/rho_bridge/theories/RhoLanguageBackendWrapper.v` proves that the
runtime capability list supports exactly the backends reported by the wrapper
and that inherited non-Rho capabilities cannot remain default after wrapping.

For the RhoCalc process path, the reusable mappers include
`mettail_rho_runtime::rhocalc_observe_values_invocation` for closed Rho ground
values plus the narrower scalar helpers
`rhocalc_observe_strings_invocation` and `rhocalc_observe_ints_invocation`.
The convenience wrappers are `rho_runtime_backed_rhocalc_values`,
`rho_runtime_backed_rhocalc_strings`, and `rho_runtime_backed_rhocalc_ints`.
They accept the generated
`RhoCalcLanguage` term returned by the retained MeTTaIL/WPDA parser, downcast it
to a typed `Proc` alternative, lower that process directly to `rhoapi::Par`, and
execute it as a dynamic call against a flip-gated `PlannedRhoBackend`. The
Rholang text shown in examples remains reader annotation; the runtime value is
the AST.

## User-Facing REPL Boundary

The REPL is part of the runtime-backend replacement surface because `exec`
selects the language's default runtime backend. Its production-facing execution
path must therefore consume `RuntimeBackendReport`, not only `AscentResults`.

The intended REPL behavior is:

```text
When a user runs exec:
  parse the source with the retained WPDA language frontend
  ask the selected default backend for a RuntimeBackendReport
  if the report is Ascent-shaped:
    keep the historical rewrite-graph display and navigation behavior
  if the report is Dovetail-report-shaped:
    display backend, artifact, completeness, roots, terms, and edge counts
    store the report as the current runtime result
    do not fabricate Ascent rewrite facts
  if the report is observation-shaped:
    display backend, artifact, channel, and observed values
    store the report as the current runtime result
    do not fabricate Ascent rewrite facts

When a user runs step, apply, equations, rewrites, normal-forms, or queries:
  require an Ascent-shaped rewrite graph
  reject non-Ascent selected backends before executing step
  reject Dovetail-report-shaped and observation-shaped reports with an explicit message
```

This preserves old graph-navigation ergonomics while allowing Dovetail-default
languages to return checked report evidence and Rho-default languages to return
typed RSpace observations. The REPL crate also exposes the bundled generated
language registry behind its default `bundled-languages` feature. Normal CLI
builds keep that feature enabled. Focused state tests may disable default
features so report-state behavior can be checked without compiling every
generated language.

## Simulation Runner Boundary

The simulation runner is also part of the runtime-backend replacement surface.
It executes a language's selected default runtime backend during
`SimulationRunner::run_to_normal_form`, so it must consume
`RuntimeBackendReport` rather than forcing every backend into `AscentResults`.

The intended simulation behavior is:

```text
When SimulationRunner executes a term:
  parse with the retained WPDA language frontend
  ask the selected default backend for a RuntimeBackendReport
  if the report is Ascent-shaped:
    keep the existing rewrite-graph BFS normal-form trace
    preserve rule-coverage collection over Ascent rewrite edges
  if the report is Dovetail-report-shaped:
    record one terminal runtime step with backend and artifact identity
    summarize completeness, roots, terms, and edges as TraceOutcome::RuntimeReport
    write the report outcome through the JSONL trace format
    do not fabricate an Ascent rewrite graph or normal-form claim
  if the report is observation-shaped:
    record one terminal runtime step with backend and artifact identity
    summarize observed channels and values as TraceOutcome::RuntimeObservations
    write the observation outcome through the JSONL trace format
    do not fabricate an Ascent rewrite graph or normal-form claim
  if the report has a future output shape:
    fail closed with an unsupported report-shape simulation failure
```

Report-shaped and observation-shaped runtime outputs are terminal simulation
outcomes. They are not normal-form graph evidence, and they intentionally
bypass the Ascent-only normal-form BFS. This preserves the old simulation
semantics for Ascent-default languages while allowing Dovetail-default
languages to expose checked report evidence and Rho-default languages to be
simulated by their actual runtime observations.

`mettail-simulation` remains substrate-neutral: its focused unit tests use a
small mock language that returns a Rho-shaped observation report. Generated
language integration tests and examples live under `mettail-languages`, which
already owns the generated-language dependency graph. That separation keeps the
simulation crate testable under the RSS cap without compiling every generated
language, while still preserving generated-language integration coverage in the
crate that owns those generated artifacts. Focused generated-language
simulation checks should use the owning language feature, for example
`cargo test -p mettail-languages --no-default-features --features calculator --test simulation_integration`,
when the test only exercises Calculator.

## Generated Operational Test Boundary

Generated operational tests are part of the runtime-backend replacement surface
because they define the regression corpus future generated language crates will
compile. Their templates must therefore exercise the selected default runtime
backend through `RuntimeBackendReport`; they must not bake in
`Language::run_ascent` as the only successful execution path.

The intended generated-test behavior is:

```text
When a generated operational test evaluates a parsed term:
  ask the selected default backend for a RuntimeBackendReport
  compare expected values through report-aware helpers
  accept Ascent normal forms, Dovetail report roots, and Rho/runtime observations as backend outputs
  use semantic outputs, not channel-summary diagnostics, for parseability checks
  keep graph-only assertions behind explicit Ascent-shaped graph checks
```

This boundary lets generated expected-output, smoke, precedence,
associativity, type-preservation, and algebraic-property tests continue to
work while a language is Ascent-default, and then continue to test the same
semantic obligation when the language is wrapped as Dovetail-default or
Rho-default. The templates also generate property-based identity-law checks for
both `f(e,a)=a` and `f(a,e)=a`; the side of the identity element is part of the
detected property, not a hard-coded convention.

## Diagram Tooling Policy

pgmcp's local diagramming toolbox includes PlantUML, Structurizr CLI, D2,
Graphviz, Mermaid CLI, Pikchr, TikZ/PGF, Asymptote, WaveDrom, bytefield-svg,
and SVG conversion tools such as Inkscape and `rsvg-convert`.

Use the smallest clear diagram set for each document:

| Concept | Preferred tool | Reason |
|---|---|---|
| component, sequence, state, deployment, C4 views | PlantUML or Structurizr | stable architecture notation and reviewable text source |
| dependency graphs and readiness DAGs | Graphviz DOT | deterministic graph layout and strong DAG rendering |
| polished conceptual architecture | D2 | concise source with good visual defaults |
| GitHub-native quick sketches | Mermaid | readable inline Markdown preview |
| protocol fields, byte layouts, timing | bytefield-svg or WaveDrom | domain-specific visual grammar |
| publication-grade mathematical figures | TikZ/PGF or Asymptote | native mathematical typography |

Prefer committed SVG outputs beside their source files. A source-only diagram is
acceptable only in prose drafts outside this validated suite.

## Agent Completion Checklist

An agent can complete a language runtime backend migration by following this
order:

1. Classify every language rule as Dovetail-core, RhoNet-lowerable,
   native-handler, covered by a typed disposition, or rejected.
2. Add Dovetail proofs for Dovetail-core rules and external contracts for
   native-handler rules.
3. Implement RhoNet lowering to `rhoapi::Par` for each lowerable rule.
4. Add RhoRuntime observation tests that execute the validated `Par` artifact.
5. Add differential oracle tests against the Ascent reference path.
6. Add process-calculus and schedule-family checks for the rule's concurrency
   shape when the rule has multiple independent redexes or guarded joins.
7. Run the language's capped Dovetail/Rho proof and runtime gate suite.
8. Enable the language's Dovetail/Rho backend selection only through the
   flip-gated planner.

Completion means the strict backend selection gate succeeds from current
evidence, not merely that a lowered artifact exists. The non-audited planner is
appropriate for unit tests and pure model construction; production flips must
use `plan_rho_default_backend_with_evidence_audit` so typoed proof, oracle,
coverage, scheduler, or handler references cannot silently authorize a runtime
default.
