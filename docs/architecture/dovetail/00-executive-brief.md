# Executive Brief

Dovetail is the MeTTaIL rewrite engine. Its job is to represent rewrite
semantics once, independent of the runtime substrate. It can then feed a local
report, a differential oracle, or a Rho-native backend without baking parser or
runtime assumptions into the rewrite core.

## What Dovetail Replaces

Dovetail replaces the production use of the Ascent-generated rewrite execution
path. Ascent remains valuable as a reference/oracle during rollout. The WPDA
parser remains active and upstream. The CESK runtime backend is the runtime
backend path being replaced.

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

The crate `dovetail` is implemented as milestone `M-E.0`, an inert engine core.
It is in the workspace, covered by tests and formal artifacts, but is not the
default live runtime backend for every language. Its public modules are:

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
