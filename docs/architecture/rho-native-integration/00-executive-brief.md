# Executive Brief

Last updated: 2026-06-13

This brief is the shortest accurate path through the MeTTaIL, Dovetail,
Rholang, F1r3node, RSpace, and Rho-machine integration.

All symbols and acronyms used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## One-Sentence Decision

MeTTaIL remains the language frontend, Dovetail supplies the substrate-neutral
rewrite semantics, and F1r3node's existing Rholang/RSpace Rho machine executes
the lowered dataflow network for the CESK runtime backend replacement path.

The dependency direction is:

`MeTTaIL bridge crates → F1r3node crates`

and never:

`F1r3node crates → MeTTaIL`

## At-a-Glance Architecture

![Rho-native MeTTaIL integration component view](figures/README.svg)

| Layer | Role | Principal obligation |
|---|---|---|
| MeTTaIL | Parses source snippets into typed terms and language metadata. | Keep language definitions explicit and total-or-reject. |
| Dovetail | Computes equations, rewrites, saturation, exact keys, and extraction outcomes. | Preserve every non-refuted semantic alternative. |
| Rho backend | Lowers Dovetail facts and rules into RhoNet, Rholang, and RSpace contracts. | Prove every lowered rule is sound and every covered rule is represented. |
| F1r3node | Runs the generated Rholang/RSpace network. | Reuse the production Rho machine for scheduling, joins, replay, checkpoints, and cost/funding. |

## Scope Boundary

This design replaced the CESK runtime backend path (retired in P6); a language
adopts the Rho default backend after passing its flip gate. The active WPDA
parser/recognizer remains the parser front end. The generated Ascent rewrite
engine was retired in P6; only the fail-closed `Language::run_ascent`
differential-oracle hook survives, and `selected_default_runtime_backend`
never selects it.

## Why This Design

The runtime path being replaced centralizes rewrite evaluation:

`facts + rules → centralized fixpoint loop`

The Rho-native path turns the covered runtime semantics into a concurrent
dataflow network:

`facts = messages`

`rules = persistent contracts`

`multi-premise rewrites = atomic joins`

`enabled rewrite = enabled COMM`

That mapping lets RSpace discover ready rewrites through communication instead
of forcing MeTTaIL to implement a second runtime scheduler. Independent
channels can proceed independently, while exact keys and candidate facts keep
deduplication and ambiguity explicit.

## Correctness Claim

For the supported fragment, fair Rho scheduling, injective exact keys, and
satisfied native/Rho contracts, the intended preservation theorem is:

`obs(run_Rho(lower(L, t))) = project(run_Dovetail(L, t))`

The proof is decomposed into:

| Proof area | What it establishes |
|---|---|
| Dovetail saturation | Every produced fact has a valid derivation, and every finite covered derivation appears unless an explicit bound is reported. |
| RhoNet lowering | Every Rho-observed fact corresponds to a Dovetail derivation, and every projected Dovetail fact is eventually emitted under fairness. |
| Exact-key deduplication | Distinct exact keys cannot be merged, and same-key collisions become explicit contract violations. |
| Guard atomicity | A failed guard consumes no input facts. |
| Ambiguity preservation | Semantic alternatives are explicit candidate facts, not scheduler choices. |
| Observation correctness | Runtime traces are projected to canonical result sets before comparison. |
| Host Rho-machine reuse | The backend uses F1r3node's Rholang interpreter and RSpace, excluding a parallel MeTTaIL-owned Rho machine. |

## Runtime Flip Gate

A language may use Rho as its default runtime only when:

`Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`

That means:

- every rewrite requirement is covered, exactly rejected, or delegated to
  an explicit contract;
- the generated `rhoapi::Par` artifact passes the normalized-AST validator;
- the RSpace/Rho scheduler fairness obligation for the covered fragment is
  discharged by the scheduler model and rollout evidence;
- generated communication structure has no newly introduced deadlock class.

## Principal Takeaways

| Question | Answer |
|---|---|
| Does this create a custom Rho machine in MeTTaIL? | No. It reuses F1r3node's Rholang interpreter and RSpace. |
| Did the Rho path replace the CESK runtime backend all at once? | No — per language. The CESK and generated-Ascent runtime paths were retired in P6 (git history is the archive); a language adopts the Rho default backend only after its checkable-coverage, artifact-validation, and deadlock gates pass, with proof/oracle results tracked as verification evidence. WPDA parsing remains active. |
| Does RSpace scheduling change semantics? | It must not. Scheduler order is quotiented away; semantic alternatives are represented as data. |
| Can snippets modeled by MeTTaIL run on F1r3node? | Yes, after MeTTaIL/WPDA parsing and after the language's Rho lowering fragment satisfies its gates. |
| Where is the detailed design? | Start with [End-to-End Architecture](02-end-to-end-architecture.md), [Rho-Native Dataflow Lowering](04-rho-native-dataflow-lowering.md), and [Correctness and Coverage](06-correctness-and-coverage.md). |
