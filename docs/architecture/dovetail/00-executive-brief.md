# Executive Brief

Dovetail is the MeTTaIL rewrite engine. Its job is to represent rewrite
semantics once, independent of the runtime substrate. It can then feed a local
report, a differential oracle, or a Rho-native backend without baking parser or
runtime assumptions into the rewrite core.

## What Dovetail Replaces

Dovetail replaced the production use of the Ascent-generated rewrite execution
path. The generated Ascent engine was retired in P6; only the fail-closed
`Language::run_ascent` differential-oracle hook survives as a reference oracle.
The WPDA parser remains active and upstream. The CESK runtime backend path was
also retired in P6, replaced by Dovetail plus Rho-native execution.

The value handed to downstream consumers is a Dovetail report: a structured
artifact that preserves exact roots, derivation structure, and extraction
completeness. It is not a debug log. See
[Runtime-Facing Reports](10-runtime-facing-reports.md) for the engineering
contract.

In Dovetail vocabulary, a report is a typed certificate-shaped value at a
phase boundary. `SatReport` certifies how saturation ended. `Extraction<T>`
certifies what extraction emitted and whether it was complete. The
runtime-facing `DovetailRunReport` certifies the exact-keyed derivation forest
that a runtime backend, oracle, or test may consume.

## Design Thesis

Ascent materializes relation facts through generated Datalog. Dovetail instead
uses:

- an exact-keyed runtime e-graph for equality evidence;
- rules-as-data for rewrite semantics;
- weighted tree automaton semantics over e-classes;
- best-first extraction that is exhaustive on demand;
- explicit reports for budget and cycle boundaries.

The user-facing property is:

`weight orders alternatives; weight never prunes alternatives`

That matters because MeTTaIL languages rely on ambiguity, equality, and multiple
valid derivations. Dovetail must not silently keep only the currently cheapest
answer when equal or more expensive alternatives remain semantically valid.

## Current Status

The `dovetail` crate is installed as a production runtime backend — not an inert
core. The proven flip gate
(`Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`) has moved the first
languages off the legacy Ascent path: `CalculatorLanguage` (scalar operations plus
native-fold coverage) and `Ambient` (the in-engine AC reduction composed with the
[binder-congruence handler](11-binder-congruence-handler.md)). Per-language rollout
across the remaining languages and retirement of the legacy Ascent/CESK paths are
the in-progress campaign remainder. Because the gate is **fail-closed**, a language
that is not yet fully covered stays un-flipped rather than mis-flipped — so "not yet
the default for *every* language" is a rollout state, not an engine limitation. Its
public modules are:

| Module | Role |
|---|---|
| `key` | Exact content keys and the unsafe `SemanticHash` contract. |
| `egraph` | Payload-generic e-graph, congruence closure, budgets. |
| `rules` | Patterns, substitutions, rewrite rules, saturation reports. |
| `wta` | Weighted tree automaton view and inside weights. |
| `extract` | Checked lazy best-first derivation extraction. |
| `report` | Runtime-facing extraction report boundary. |
| `space` | Tuple-space shaped rendezvous seam. |

## Principal Risks

| Risk | Dovetail control |
|---|---|
| silently dropping distinct alternatives | exact `ContentKey`, set-valued extraction, equal-weight preservation tests, Rocq exact-key proofs |
| mistaking bounded cyclic evidence for complete evidence | `ExtractionCompleteness::BoundedByCycleCut`, checked stream terminal status, Rocq cycle-cut boundary proofs |
| saturation runaway | explicit `NodeLimit` and `IterationLimit`, no silent success claim |
| non-deterministic review artifacts | exact keys, ordered framing, sorted SCC traversal, deterministic reports |
| runtime lock-in | no parser, runtime, RSpace, or Ascent dependency in `dovetail` |

## Decision Rule

Use Dovetail as the source of rewrite semantics when all of these are true:

`ExactKeys ∧ SaturationOutcomeChecked ∧ ExtractionCompletenessChecked ∧ CoverageEvidenceChecked`

If any conjunct is missing, use Dovetail as an oracle or development artifact,
not as a production default.
