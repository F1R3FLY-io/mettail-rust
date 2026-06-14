# Runtime-Facing Reports

A Dovetail report is a proof-preserving extraction artifact. It is the
structured value Dovetail hands to downstream consumers after saturation and
checked extraction. It is not a human-facing log, and it is not a lossy
`success` value.

The report exists because a rewrite engine often has more to say than "here is
one answer." Dovetail must preserve ambiguity, exact identity, derivation
structure, ordering, and terminal completeness across the boundary to an
oracle, a local test, or the Rho-native runtime backend.

Put differently: a report is the machine-readable certificate for what the
rewrite engine just proved, enumerated, and bounded. It is called a report
because it reports checked facts to another component, not because it is a
diagnostic transcript for a human.

## Reader's Mental Model

The shortest useful definition is:

`Dovetail report = checked rewrite result + exact identities + boundary status`

That definition matters because Dovetail is not just an evaluator. It is the
component that explains a rewrite search well enough for another runtime to
consume it without reopening Dovetail internals. A report is therefore the
handoff object between "the rewrite engine has finished a checked phase" and
"a backend, oracle, or tool may now act on the checked result."

Use this quick test when reading or changing the code:

| If the value answers... | It is probably... |
|---|---|
| "How did saturation stop?" | `SatReport` |
| "What did extraction emit, and was that emission complete?" | `Extraction<T>` |
| "What exact derivation forest may a backend or oracle consume?" | `DovetailRunReport` |
| "What did a runtime observe after executing a backend artifact?" | Not a Dovetail report; it is a runtime observation |

So a report is not an extra logging layer. It is the reason Dovetail can remain
substrate-neutral while still giving Rho, Ascent-oracle checks, tests, and
future bytecode paths the same exact semantic payload.

## Why This Belongs In A Rewrite Engine

The word "report" can sound surprising because a rewrite engine is often
introduced as if it only computes a rewritten term. Dovetail has a broader job:
it computes a checked region of a rewrite search space and must hand that
region to components that do not share Dovetail's internal data structures.

That handoff has to answer four questions a plain term cannot answer:

| Question | Why a term alone is insufficient |
|---|---|
| Which exact alternatives were found? | Display text can conflate distinct derivation trees. |
| What derivation structure supports each alternative? | A backend may need ordered children, repeated operands, and shared subterms. |
| Why did the search stop? | Convergence, node limits, iteration limits, and cycle cuts have different meanings. |
| May the consumer claim exhaustiveness? | A finite prefix from a cyclic space is useful evidence, but it is not a complete result. |

The report layer is therefore part of Dovetail's semantic API. It is not an
optional observability feature. Removing it would force each consumer to
reconstruct Dovetail-specific invariants from weaker values, which is exactly
where boundedness, exact identity, and ordering bugs tend to enter runtime
integrations.

For engineering review, use this rule:

`If a value crosses from Dovetail into another subsystem, it must either be a report or be explicitly derived from a report without weakening its obligations.`

## Report Family

"Report" is a family name for typed artifacts at Dovetail phase boundaries. The
types are intentionally small and specific:

| Type | Phase boundary | What it certifies | What it does not certify |
|---|---|---|---|
| `SatReport` | rule saturation | how equality growth stopped under the configured node and iteration bounds | that every possible rule universe was explored without caller-selected bounds |
| `Extraction<T>` | extraction stream termination | the extracted value and whether the stream is exhaustive or cycle-bounded | that saturation converged |
| `DovetailRunReport` | runtime/tool handoff | exact roots, term records, derivation edges, and extraction completeness in a substrate-neutral shape | that a runtime has executed the result |

The end-to-end completeness claim is deliberately conjunctive:

`EndToEndComplete = SaturationConverged ∧ ExtractionComplete`

No single report is allowed to smuggle that stronger claim on its own.

## Definitions

| Term | Meaning |
|---|---|
| report | A typed, machine-readable artifact that carries checked facts across a Dovetail phase boundary. |
| `SatReport` | The saturation terminal-status artifact: `Converged`, `NodeLimit`, or `IterationLimit`, plus saturation statistics. |
| `Extraction<T>` | The checked extraction envelope: extracted value plus terminal completeness. |
| `DovetailRunReport` | The runtime-facing artifact produced by `report_from_extraction`. |
| root | A top-level derivation selected by the extractor for the requested e-class. |
| term record | A unique derivation node, recorded once under exact `ContentKey` identity. |
| derivation edge | A parent-to-child dependency edge inside a derivation tree. |
| completeness | Terminal extraction metadata: `Complete` or `BoundedByCycleCut`. |
| consumer | A downstream adapter, oracle, runtime backend, or test that reads the report. |
| observation | A runtime-visible value produced after a consumer executes or interprets the report. |

The core distinction is:

`DovetailRunReport = checked rewrite/extraction artifact`

`RuntimeBackendReport = generic Language-level backend return envelope`

`RhoObservationReport = Rho-runtime observation artifact`

## Report Means Certificate, Not Debug Output

The word "report" is used in Dovetail in the engineering sense of a typed
result artifact. The artifact is part of the API contract. It can be stored,
compared, checked by proofs, converted into a runtime envelope, or lowered by a
backend.

It is not:

| Not a report meaning | Why Dovetail rejects that interpretation |
|---|---|
| debug log | logs are optional narration; Dovetail reports are semantic artifacts |
| pretty-printed output | display text can conflate distinct exact derivations |
| Boolean success flag | a rewrite run can be bounded, cyclic, partial, or converged |
| single normal form | MeTTaIL rewrite semantics can preserve multiple valid alternatives |
| Rho observation | observations are produced after a runtime consumes a report |

A report answers questions that a plain return value cannot answer:

| Question | Where the answer lives |
|---|---|
| Did saturation converge, or did a bound stop it? | `SatReport::outcome` |
| Which extracted roots were produced, and in what order? | `DovetailRunReport::roots` |
| Which exact derivation tree does each root identify? | `DovetailRunReport::terms` and `derivation_edges` |
| Is the extracted set exhaustive? | `DovetailRunReport::completeness` |
| May a downstream runtime treat the result as complete? | `DovetailRunReport::assert_complete()` |

## Naming Discipline

Dovetail documentation and code should use the noun precisely:

| Phrase | Use it when... |
|---|---|
| Dovetail report | the artifact was produced by Dovetail and carries Dovetail's checked semantics |
| saturation report | the topic is specifically `SatReport` and saturation terminal status |
| extraction envelope | the topic is specifically `Extraction<T>` and terminal completeness |
| runtime backend report | the topic is the `mettail-runtime` envelope around a backend's output |
| runtime observation | the value was produced after a backend artifact was executed or observed |
| diagnostic | the value is human-facing explanatory text, not a semantic handoff artifact |

This distinction matters in the Rho-native path. A Dovetail report can be
lowered into a Rho artifact; a Rho runtime observation is produced later by the
Rho machine. Treating those as the same object would blur compilation evidence
with execution evidence.

## Why Reports Exist

A plain result shape such as `rewrite(input) -> value` is too weak for
Dovetail. It loses the difference between an exhaustive finite result and a
finite prefix from a cyclic derivation space. It also hides whether two visible
values came from distinct exact derivation trees.

Dovetail therefore uses the following boundary:

`saturate(seed, rules, bounds) -> SatReport`

`extract(root) -> Extraction(derivations, completeness)`

`report_from_extraction(extraction) -> DovetailRunReport`

These are three different boundaries:

| Boundary | Producer | Main claim |
|---|---|---|
| saturation | `EGraph::saturate` | equality evidence reached a terminal outcome under configured bounds |
| extraction | `Extractor` / `Derivations` | derivations were emitted with terminal completeness metadata |
| runtime-facing report | `report_from_extraction` | checked extraction was frozen into exact-keyed data for consumers |

The runtime-facing report does not replace `SatReport`. A complete
`DovetailRunReport` says extraction was complete for the saturated graph it was
given. `SatReport` says how that graph was produced. Consumers that need an
end-to-end production claim should check both:

`EndToEndComplete = SaturationConverged ∧ ExtractionComplete`

The report carries the facts that later components are allowed to rely on:

| Fact | Why it matters |
|---|---|
| exact root keys | downstream consumers can compare alternatives without display-string equality |
| extractor root order | deterministic review, oracle comparison, and Rho handoff |
| unique term records | compact table layout without losing exact identity |
| ordered derivation edges | repeated operands and child positions remain observable |
| terminal completeness | bounded cyclic evidence cannot be mistaken for exhaustive evidence |

The central report invariant is:

`ReportComplete(r) ⇔ completeness(r) = Complete`

and the safety condition for cyclic extraction is:

`completeness(r) = BoundedByCycleCut ⇒ ¬ReportComplete(r)`

## Consumer Decision Procedure

Consumers should handle reports mechanically. The recommended control flow is:

```text
When a Dovetail consumer receives a report:
  Read the paired saturation outcome if the consumer needs an end-to-end claim.
  If saturation did not converge:
    Keep the report as bounded evidence, but do not claim full language execution.
  Read the report completeness field.
  If completeness is BoundedByCycleCut:
    Reject exhaustive execution or mark the result as explicitly bounded.
  For every root key in extractor order:
    Resolve the root through the term table by exact ContentKey.
    Preserve ordered derivation edges when lowering or comparing.
  Only after those checks:
    Produce a runtime artifact, oracle comparison, or human presentation.
```

The important sequencing is that a report is consumed before runtime
observation. A Rho backend must not produce a "complete" observation from a
`BoundedByCycleCut` report, and an oracle must not compare display strings when
exact keys are present.

## End-To-End Boundary

![Dovetail report boundary](figures/10-report-boundary.svg)

PlantUML source: [figures/10-report-boundary.puml](figures/10-report-boundary.puml).

The diagram shows the intended lifecycle: saturation grows equality evidence,
checked extraction enumerates derivations and terminal completeness, the report
freezes that checked state into a substrate-neutral artifact, and consumers
must preserve the report's guarantees when producing observations or oracle
comparisons.

## Report Shape

The Rust source of truth is
[`dovetail/src/report.rs`](../../../dovetail/src/report.rs). The primary type
is `DovetailRunReport<L, W>`.

| Field | Meaning | Consumer rule |
|---|---|---|
| `roots` | exact root `ContentKey`s in extractor order | treat as semantic root identities |
| `root_ordinals` | indexes into `terms` for each root | use for table lookup, not semantic equality |
| `terms` | unique derivation records by exact key | preserve keys when lowering |
| `derivation_edges` | ordered parent-child key edges | preserve repeated child uses and child indexes |
| `completeness` | terminal extraction status | reject or explicitly mark bounded reports before exhaustive execution |

Ordinals are stable positions inside one report. They are not semantic
identities. The semantic identity is always `ContentKey`.

## Literate Pseudocode

```text
Algorithm R1: Build a Dovetail report from checked extraction

Given checked extraction output:
  extraction.value is the extractor-ordered root derivation list.
  extraction.completeness is the terminal completeness status.

Create an empty report:
  roots is empty.
  root_ordinals is empty.
  terms is empty.
  derivation_edges is empty.
  completeness is extraction.completeness.

For each root derivation in extraction.value:
  Append root.key to roots.
  Record the root derivation by exact key.
  Append the root's term-table ordinal to root_ordinals.

To record a derivation:
  If its exact key is already present in terms:
    Reuse the existing ordinal.
    Mark the existing record as a root if this occurrence is a root.
  Otherwise:
    Append a new term record with ordinal, class, key, operator, weight, and root flag.
  For each child in child-index order:
    Append a derivation edge from parent key to child key with that child index.
    Record the child derivation recursively.

Return the report.
```

This algorithm is structure-preserving:

`roots(report) = map(key, extraction.value)`

`completeness(report) = completeness(extraction)`

`∀k. k ∈ roots(report) ⇒ k ∈ keys(terms(report))`

## Small Example

Suppose extraction returns two root derivations for the same e-class:

| Extractor order | Display form | Exact key |
|---:|---|---|
| 0 | `S(Z)` | `k₀` |
| 1 | `Add(Z, S(Z))` | `k₁` |

The report root list is:

`roots = [k₀, k₁]`

The term table may record shared sub-derivations once:

| Ordinal | Display form | Exact key | Root? |
|---:|---|---|---|
| 0 | `S(Z)` | `k₀` | yes |
| 1 | `Z` | `k₂` | no |
| 2 | `Add(Z, S(Z))` | `k₁` | yes |

The edge list preserves ordered children:

| Parent | Child | Child index |
|---|---|---:|
| `k₀` | `k₂` | 0 |
| `k₁` | `k₂` | 0 |
| `k₁` | `k₀` | 1 |

The report is therefore a compact graph-shaped representation of the extracted
derivation forest. It is not merely the displayed values `S(Z)` and
`Add(Z, S(Z))`.

## Formal Contract

The proof source of truth is
[`RuntimeReportBridge.v`](../../../dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v).
It proves the facts that downstream consumers may rely on:

| Theorem family | Meaning |
|---|---|
| `report_roots_preserve_extractor_order` | report roots equal extracted root keys in order |
| `report_completeness_matches_extraction` | report completeness is copied from extraction |
| `report_terms_are_deduplicated_exact_keys` | term records are deduplicated |
| `report_root_keys_have_term_records` | every reported root has a term record |
| `bounded_extraction_report_is_not_complete` | bounded cyclic extraction cannot become complete |
| `complete_report_originates_in_complete_extraction` | a complete report came from complete extraction |

The Rho handoff proof then builds on this boundary: complete reports may
produce Rho-visible observations of their root keys, while
`BoundedByCycleCut` reports are rejected before observations are emitted.

## Consumer Obligations

Every report consumer must obey these rules:

1. Use `ContentKey`, not display text or ordinal, as semantic identity.
2. Preserve root order when root order is externally observable.
3. Preserve derivation-edge child indexes and repeated child uses.
4. Treat `Complete` as the only exhaustive status.
5. Treat `BoundedByCycleCut` as useful bounded evidence, not as exhaustive success.
6. Keep runtime observations separate from Dovetail reports; observations are produced after a runtime consumes a report.

These rules keep Dovetail substrate-neutral. The Rho backend can lower a report
to normalized `rhoapi::Par`; an Ascent oracle can compare exact keys; a local
test can inspect derivation edges. None of those consumers change what the
report means.

## Anti-Patterns

| Anti-pattern | Problem |
|---|---|
| Treating a report as a debug log | loses the fact that it is a machine-checked artifact boundary |
| Returning only `Vec<Derivation>` | drops terminal completeness |
| Comparing display strings | conflates presentation with exact semantic identity |
| Treating ordinals as keys | ordinals are local table positions only |
| Collapsing reports into `AscentResults` | hides non-Ascent runtime observations and boundedness |

The report boundary exists to make these mistakes difficult. It is the point
where Dovetail's internal proof obligations become stable engineering data for
the rest of the MeTTaIL runtime stack.
