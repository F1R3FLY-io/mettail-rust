# Verification and Rollout

Last updated: 2026-06-13

This document turns the architecture into an implementation evidence ledger and
gate policy. It distinguishes mechanized bridge contracts from per-language
CESK runtime-backend flip gates: a contract can be proved here, while a language
becomes Rho-default only after its proof, oracle, coverage, artifact-validation,
and deadlock gates pass.

All symbols used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## Current Verified Base: M-RHO.0

M-RHO.0 established an inert, one-way bridge and the first scalar-operation
execution path.
The current proof and coverage sources are
[RHO-BRIDGE-FORMAL](references.md#rho-bridge-formal),
[DOVETAIL-FORMAL](references.md#dovetail-formal), and
[COVERAGE-MATRIX](references.md#coverage-matrix).

| Area | Artifact | Status |
|---|---|---|
| bridge direction | `formal/rocq/rho_bridge/theories/BridgeInertness.v` | proved one-way dependency shape |
| host Rho-machine reuse | `HostRhoMachineReuse.v` | proved accepted backend plans include host Rholang/RSpace and exclude custom reducer, tuple-space, matcher, and replay components |
| OSLF/funding adapter | `MettaOslfLawsConformance.v`, `MettaGsltPresentation.v` | proved modeled funding laws |
| total-or-reject lowering | `RhoLoweringTotalOrRejects.v` | proved every rule lowers or is rejected |
| normalized Rholang AST boundary | `RhoParWellFormedness.v`, `RhoArtifactBoundary.v` | proved scalar-contract `Par` shape, positive bind counts, bind-count agreement, return-channel convention, validation soundness/completeness, and generated-backend rejection of source-text artifacts |
| RhoNet/COMM correspondence | `CommReductionCorrespondence.v` | proved lowered pure-rule traces match Dovetail traces |
| linear COMM correspondence | `LinearCommCorrespondence.v` | proved one-shot COMM consumes the matched send and receive, with sound/complete lowering correspondence |
| Rho name grounding | `RhoGroundingAndNames.v` | proved fresh private names avoid capture of grounded facts |
| resting-space fingerprint and observation report | `RhoObservationFingerprint.v`, `RhoObservationReportBoundary.v`, `mettail-rho-runtime::RhoObservationReport` | proved exact-key fingerprints are membership-exact, multiplicity-exact, and order-insensitive; planned runtime reports preserve the planned backend boundary, channel, read-order values, exact set-membership fingerprint, and exact counted fingerprint |
| ambiguity witnesses | `AmbiguityWitnessEnumeration.v` | proved enabled candidates are enumerated independently of schedule order |
| oracle exactness | `OracleQuotientEquivalence.v` | proved weight-erased key equality is exact |
| call-by-need observation | `RhoCallByNeedObservation.v` | proved thunk forcing and memoization preserve weak source observation |
| Δ1 min-cost join | `DeltaOneMinCostJoin.v` | proved selected joins are present and cost-minimal |
| guarded COMM | `GuardedCommSoundness.v` | proved false guards do not commit and attempts fabricate no facts |
| ambiguity-set preservation | `AmbiguitySetPreservation.v` | proved schedule order preserves observed candidate sets |
| cost-axis separation | `RhoCostAxisSeparation.v` | proved ordering costs cannot remove candidates; refutation is explicit |
| backend flip gate | `RhoBackendFlipGate.v` | proved Rho default requires proof, oracle, exact coverage of rejected rules, artifact validation, and deadlock gates |
| planned Rho execution boundary | `RhoPlannedExecutionBoundary.v`, `mettail-rho-runtime::PlannedRhoBackend` | proved and implemented that generated backend execution consumes a flip-gated plan, not merely a raw shape-validated artifact |
| runtime backend dispatch | `RuntimeBackendDispatch.v` | proved default execution succeeds only when the selected backend is installed; absent Dovetail/Rho defaults fail closed instead of falling back to Ascent |
| Dovetail report boundary and Rho handoff | `dovetail::report`, `RuntimeReportBridge.v`, `RhoReportHandoff.v` | proved checked extraction reports preserve exact keys, extractor root order, deduplicated term records, and terminal completeness; Rho handoff observes exactly complete-report roots and rejects `BoundedByCycleCut` without observations |
| finite process projection | `formal/process/rho_comm_slice.json`, `formal/mcrl2/rho_machine/`, `formal/maude/rho_machine/`, `formal/tla/rho_machine/` | generates, model-checks, and rewrite-checks a bounded three-redex RhoNet/Dovetail COMM fragment with Rho-internal reserve phases for no deadlock, all six visible fire/complete schedules, premature-completion unreachability, branching bisimilarity modulo hidden reserve actions, unique matching terminal normal forms, and weak-fair scheduler completion |
| runtime smoke | `mettail-rho-runtime/tests/run_calculator.rs` | runs a validated Rho-default backend plan for lowered calculator ops on RhoRuntime |
| differential oracle | `mettail-rho-runtime/tests/rho_vs_ascent.rs` | compares a validated Rho-default backend plan with Ascent results |

The Rho bridge now has mechanized model contracts for pure COMM, name
grounding, exact observation, call-by-need forcing, `Δ1` cost-minimal joins,
guards, ambiguity preservation, cost-axis separation, normalized-`Par`
well-formedness, source-text artifact exclusion, backend flip gating, and
fail-closed runtime dispatch.
Dovetail-to-runtime handoff now starts from a checked Dovetail report rather
than an Ascent-shaped success value. The handoff proof requires complete
reports before emitting Rho-visible observations, preserves the extractor root
order as the observed exact-key sequence, and rejects `BoundedByCycleCut`
reports without observations.
Generated Rho execution now starts from `PlannedRhoBackend`, which wraps the
`RhoDefaultBackendPlan` produced by the flip gate; raw validated artifacts remain
available for oracle/debug helpers only.
Generated Rho observations now use `RhoObservationReport<T>` rather than
`AscentResults`: the report carries the planned execution boundary, the artifact
kind, the observed channel, the read-order values, an order-insensitive
set-membership fingerprint for set-semantics oracle comparison, and an
order-insensitive counted fingerprint for bag-sensitive observations.
Per-language production flips still require the runtime gates listed below.

## Rollout Phases

![M-RHO rollout phases](figures/07-verification-and-rollout.svg)

PlantUML source:
[figures/07-verification-and-rollout.puml](figures/07-verification-and-rollout.puml).

```plantuml
@startuml
title M-RHO Rollout

skinparam backgroundColor #FEFEFE
skinparam shadowing false
skinparam activity {
  BorderColor #1F2937
  FontColor #111827
  ArrowColor #374151
}

start
:M-RHO.0\nbridge + scalar oracle; <<#DBEAFE>>
:M-RHO.1\nrhocalc COMM\nRho-native dataflow; <<#DCFCE7>>
:M-RHO.2\ngeneric CBN / need\nencoding; <<#FEF3C7>>
:M-RHO.3\nΔ1 joins, guards,\nambiguity hardening; <<#FDE68A>>
:M-RHO.4\nper-language flip\nto Rho default; <<#FCE7F3>>
stop

legend right
  <#DBEAFE> shipped base
  <#DCFCE7> first Rho-native semantics
  <#FEF3C7> generic language support
  <#FDE68A> cost and guard hardening
  <#FCE7F3> production default
endlegend
@enduml
```

## M-RHO.1: rhocalc COMM Fast Path

Verified statement:

`rhocalc Comm → RSpace COMM`

Mechanized coverage:

- `CommReductionCorrespondence.v` proves lowered pure-rule traces and Dovetail
  traces coincide.
- `LinearCommCorrespondence.v` proves the M-RHO.1 linear COMM model:
  classifier totality, one-shot send/receive consumption, soundness,
  completeness, quote/drop name canonicalization, grounding/COMM commutation,
  send-arrival permutation coverage for one-bind races, and statement-only
  fences for strong-bisimulation/full-abstraction non-claims.
- `RhoGroundingAndNames.v` proves fresh `new` names do not capture grounded
  existing fact names and alpha-renaming a fresh private name is observationally
  inert for existing public names.
- `RhoObservationFingerprint.v` proves resting-space fingerprints are exact
  characteristic functions over fact-key membership, and insertion order is
  irrelevant under that observation.
- `AmbiguityWitnessEnumeration.v` proves every enabled candidate witness is
  enumerated and that schedules with the same enabled witness set have the same
  observation.

Acceptance:

`obs_Rho(term) = obs_Dovetail(term)`

for the M-RHO.1 corpus, under the documented observation quotient.

Runtime corpus:

- single-bind receives;
- distinct-channel joins;
- received-name sends;
- process-valued payloads;
- `new` smoke behavior;
- order-sensitive one-bind contention by deterministic send-arrival
  enumeration;
- same-channel duplicate receive joins through direct RSpace `consume_result`;
- same-channel duplicate receive syntax as a negative source-text parser
  boundary.

The historical host parser rejects duplicate receive channels before RSpace
evaluation. The backend therefore verifies the case in two layers: source text
remains a negative parser-boundary regression for hand-authored oracle tests,
while direct RSpace `consume_result` over ADT channel vectors provides the
positive runtime-substrate claim. The generated backend path emits normalized
AST, not source text. The
mechanized model is `LinearCommCorrespondence.v::same_channel_join_sound` and
`same_channel_join_complete`; the runtime gate is
`rho_comm_oracle::duplicate_receive_channels_supported_by_direct_rspace_consume`.

## M-RHO.2: Generic CBN / Call-by-Need Encoding

Verified statement:

Support non-Rho-native languages by compiling computations into thunks.

Core idea:

`thunk = private channel + persistent computation contract`

`force(thunk, k) = send continuation k to thunk`

`call_by_need = force + memo cell`

Mechanized evidence:

`source_eval(t) ≈ weak_observation(rho_need(lower(t)))`

`RhoCallByNeedObservation.v` proves that forcing a sound memoized thunk
observes the same value as source evaluation, that a force miss memoizes the
source value, that repeated force is observationally idempotent, and that a
repeated force after a miss preserves the memo.

Runtime gate:

- `rho_call_by_need::call_by_need_force_miss_memoizes_and_repeated_force_reuses_value`
  forces a cold lowered thunk twice and observes one compute marker plus two
  public values.
- `rho_call_by_need::call_by_need_memo_hit_observes_value_without_compute_marker`
  forces a hot lowered thunk twice and observes no compute marker.

Strong bisimulation is not the contract across force boundaries because the
target has internal communication steps that the source observation hides.

## M-RHO.3: Cost, `Δ1` Join, Guards, and Ambiguity

Verified statement:

Harden advanced runtime behavior.

Gate clauses:

- `Δ1` min-cost matching for n-ary joins;
- two-axis cost model: refutation versus ordering;
- guarded-COMM soundness;
- ambiguity-set preservation under nondeterministic schedules;
- mergeable-channel optimization only when the algebraic contract matches.

Mechanized evidence:

- `DeltaOneMinCostJoin.v`
- `GuardedCommSoundness.v`
- `AmbiguitySetPreservation.v`
- `RhoCostAxisSeparation.v`

Rust adapter evidence:

- `mettail_rho_adapter::DeltaOneCandidate`
- `mettail_rho_adapter::select_delta1_minima`
- `mettail_rho_adapter::delta1_selects_index`
- `delta1_selects_all_enabled_minimal_ties`
- `delta1_refutation_precedes_ordering`
- `delta1_returns_empty_when_no_candidate_is_enabled`
- `rho_guard_oracle::false_single_bind_guard_leaves_data_and_emits_no_output`
- `rho_guard_oracle::guard_filters_multiple_messages_without_consuming_failed_candidate`
- `rho_guard_oracle::false_cross_bind_guard_leaves_all_join_inputs`
- `rho_guard_oracle::cross_bind_guard_can_commit_later_without_consuming_failed_pair`

Acceptance:

`cost_refutes(c) ⇒ c` is absent from `Δ1` selection for evidence reasons.

`cost_orders(c₁, c₂)` may rank enabled candidates but must not remove either
candidate when their ordering costs are equal.

`guard(σ) = false` behaves as no match: no guarded body is emitted, and every
datum considered by the failed match remains resting for a later satisfying
match.

## M-RHO.4: Per-Language Flip

Verified statement:

Make Rho the default runtime backend for a language, in place of the CESK
runtime backend, only after proof, oracle, coverage, artifact-validation, and
deadlock gates pass.

Flip condition for language `L`:

`Proofs(L) ∧ OracleParity(L) ∧ Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`

`RhoBackendFlipGate.v` proves the Boolean flip gate is exactly this conjunction
and that any missing gate blocks the flip. `RhoParWellFormedness.v` supplies the
shape proof for the current scalar-contract `Par` fragment, `RhoArtifactBoundary.v`
proves source-text artifacts are not accepted generated-backend artifacts, and
the Rust validator is the executable gate for generated artifacts.
`RhoBackendFlipGate.v` also models the Rust
default-backend planner's coverage wrapper: every scalar-lowering rejection must
be covered by an exact delegated-rule claim, and stale delegation claims block
the plan. Its
`deadlock_diagnostic_blocks_flip` theorem models the codegen analyzer output:
any non-empty channel-deadlock diagnostic list makes `NoNewDeadlocks(L)` false.
The `clean_deadlock_report_reduces_to_other_gates` theorem proves that an empty
deadlock report leaves the proof, oracle, coverage, and artifact-validation
gates as the remaining flip obligations.
The `no_blockers_iff_can_flip` and `any_blocker_blocks_flip` theorems model the
Rust blocker-list API: a language can flip exactly when no blocker remains.
The `default_backend_gate_iff_all_evidence` theorem models
`plan_rho_default_backend`: proof, oracle, coverage audit, no uncovered rejected
rules, no extraneous delegation claims, and no deadlock diagnostics are jointly
necessary and sufficient.

Rust flip-gate evidence:

- `mettail_rho_codegen::plan_rho_default_backend`
- `mettail_rho_codegen::RhoDefaultBackendPlan`
- `mettail_rho_codegen::RhoDefaultBackendPlanError`
- `mettail_rho_runtime::PlannedRhoBackend`
- `mettail_rho_runtime::RhoObservationReport`
- `mettail_rho_runtime::RhoExecutionBoundary`
- `mettail_rho_codegen::RhoProgram`
- `mettail_rho_codegen::validate_rho_program`
- `mettail_rho_codegen::RhoValidationError`
- `mettail_rho_codegen::RhoDefaultBackendEvidence`
- `mettail_rho_codegen::RhoCoverageEvidence`
- `mettail_rho_codegen::decide_rho_flip`
- `mettail_rho_codegen::RhoFlipDecision::can_flip_to_rho`
- `mettail_rho_codegen::RhoFlipBlocker`
- `mettail_rho_codegen::RhoFlipBlocker::ArtifactValidation`
- `mettail_rho_codegen::analyze_channel_deadlocks`
- `mettail_rho_codegen::ChannelDeadlockReport`
- `mettail_rho_codegen::ChannelDeadlockReport::no_new_deadlocks`
- `mettail_rho_codegen::ChannelDeadlockDiagnostic::MissingProducer`
- `mettail_rho_codegen::ChannelDeadlockDiagnostic::ClosedWaitCycle`
- `scalar_lowering_emits_clean_deadlock_report`
- `missing_internal_producer_blocks_gate`
- `closed_wait_cycle_blocks_gate`
- `seed_breaks_wait_cycle`
- `all_gates_and_clean_deadlock_report_allow_flip`
- `missing_proofs_or_oracle_or_coverage_blocks_flip`
- `channel_deadlock_diagnostics_block_flip`
- `decision_reports_all_blockers_together`
- `artifact_validation_blocks_flip`
- `scalar_lowering_deadlock_report_allows_flip_when_coverage_gate_is_external`
- `lowering_emits_normalized_ast_not_source_text`
- `binary_contract_uses_operands_first_return_channel_last_abi`
- `validates_generated_scalar_contract_ast`
- `rejects_mutated_nonpersistent_contract`
- `rejects_mutated_top_level_metadata`
- `rejects_mutated_pattern_metadata`
- `rejects_mutated_body_metadata`
- `rejects_huge_bind_count_without_allocating_from_it`
- `rejects_mutated_operand_metadata`
- `default_backend_plan_succeeds_when_all_rules_lower`
- `default_backend_plan_blocks_uncovered_rejections`
- `default_backend_plan_accepts_exact_delegated_rejections`
- `default_backend_plan_rejects_stale_delegation_claims`
- `default_backend_plan_reports_all_non_coverage_gate_failures`

The CESK runtime backend remains selectable until this gate passes for a
language. After a language flip, Rho becomes that language's default runtime
backend; the active WPDA parser/recognizer remains upstream, and Ascent remains
available only as the legacy reference/oracle path for differential evidence
and is not deleted by the flip itself.

## Formal Verification Commands

All commands must run under the repository's capped formal entry point or an
equivalent `systemd-run` cap.

```text
Verify Rho bridge Rocq theories:

  make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge
```

```text
Verify Dovetail Rocq theories:

  make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail
```

```text
Verify Dovetail requirement coverage:

  make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail-requirements
```

```text
Verify finite Rho process-calculus projection:

  make -C formal check-capped FORMAL_CAPPED_TARGET=process-rho-comm-slice
```

## Rust Verification Commands

Run under an RSS cap such as:

```text
systemd-run --user --scope \
  -p MemoryMax=8G \
  -p MemorySwapMax=0 \
  -p CPUQuota=200% \
  <command>
```

Required tests:

```text
cargo test -p mettail-rho-codegen
cargo test -p mettail-rho-adapter
cargo test -p mettail-rho-runtime
cargo test -p mettail-languages --no-default-features --features rhocalc --test rhocalc_tests
```

M-RHO.1 Rho machine COMM oracle:

```text
cargo test -p mettail-rho-runtime --test rho_comm_oracle
```

M-RHO.3 guarded-COMM oracle:

```text
cargo test -p mettail-rho-runtime --test rho_guard_oracle
```

The Rho-vs-Ascent differential oracle intentionally compiles the generated
language suite and should be run as an explicit heavyweight gate:

```text
cargo test -p mettail-rho-runtime --features oracle-ascent --test rho_vs_ascent
```

## pgmcp Evidence

Every implementation pass should record:

- task public id;
- proof commands run;
- test commands run;
- git commit;
- any bounded or excluded cases;
- channel-deadlock output if Rho/RSpace code changed.

The channel-deadlock analyzer is the generated-communication-structure gate for
`NoNewDeadlocks(L)`. It checks for static waits without producers and closed
wait cycles without external or seed entry. It complements the semantic Rocq
proofs; it does not replace them.

## Audit Checklist

| Gate | Required condition |
|---|---|
| proof hygiene | no admitted proofs, unsupported axioms, or unproved conjectures in completed target theories |
| claim hygiene | M-RHO.2/.3/.4 claims name the proof/test gates that discharged them; per-language Rho-default flips still require the M-RHO.4 gate |
| exactness | no identity comparison based only on lossy hashes |
| ambiguity | no semantic alternatives represented by scheduler `select` |
| boundedness | no bounded cyclic extraction reported as complete |
| dependency | no reverse dependency from F1r3node to MeTTaIL |
| runtime path | generated bridge execution uses `PlannedRhoBackend` built from a flip-gated `RhoDefaultBackendPlan`; the plan carries a normalized `rhoapi::Par` artifact injected directly through opaque `ValidatedRhoProgram`; observations return `RhoObservationReport<T>` rather than `AscentResults`; source-text evaluation is limited to hand-authored regression oracles |
| source boundary | duplicate receive-channel joins are positive through direct RSpace consume and negative only at the historical source parser boundary |
| docs | coverage matrix and this suite updated together |

## Evidence Loop

1. Define the semantic surface in this suite.
2. Add or update the corresponding Rocq theory.
3. Add AST/direct-injection and differential runtime tests for the same surface.
4. Run the capped proof and test gates.
5. Run proof-hole, claim-hygiene, and documentation validators.
6. Record the command evidence in pgmcp.
7. Update coverage tables only for gates that passed.
