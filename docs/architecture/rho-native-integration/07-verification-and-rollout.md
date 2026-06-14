# Verification and Rollout

Last updated: 2026-06-14

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
| auditable rejected-rule coverage | `RhoRejectedCoverage.v` | proved `AllRulesLowered` accepts only an empty rejected set; `CoveredRejectedRules` must name exactly the rejected rule set; omitted, stale, duplicate, or evidence-less dispositions block the default-backend gate |
| normalized Rholang AST boundary | `RhoParWellFormedness.v`, `RhoArtifactBoundary.v`, `RhoAstSendBoundary.v` | proved scalar-contract `Par` shape, positive bind counts, bind-count agreement, return-channel convention, validation soundness/completeness, generated-backend rejection of source-text artifacts, and dynamic call/witness sends as AST artifacts rather than source text; structured dynamic payloads preserve list, map, and bag literals across the AST boundary |
| type-sensitive scalar operator lowering | `RhoScalarOperatorTyping.v`, `mettail-rho-codegen::lower` | proved and tested that native scalar operators are selected from terminal plus operand/result types; `Int + Int → Int` lowers to Rholang integer addition, `Str + Str → Str` and `Str ++ Str → Str` lower to Rholang string concatenation, and ill-typed or mixed scalar operators are rejected |
| rhocalc AST-first lowering | `RhocalcAstLowering.v`, `mettail-rho-runtime::{lower_rhocalc_proc,lower_rhocalc_term}`, `mettail-rho-runtime/tests/rho_rhocalc_ast.rs` | proved accepted rhocalc lowerings are AST artifacts, quote/drop lowering preserves the body, list order is preserved, map key/value pairs are preserved, bag multiplicities are preserved, ambiguous two-Proc terms preserve both branches, one-input COMM fires the payload, two-input COMM preserves syntactic binder order under f1r3node's de Bruijn convention, and bound-bit filtering removes receive-local variables; runtime tests parse with WPDA, lower to `Par`, preserve every exact-key-distinct ambiguous Proc branch, deduplicate exact duplicates, reject cross-category ambiguity instead of dropping it, inspect list/map/bag AST shape, inject into RhoRuntime, and observe COMM results |
| RhoNet/COMM correspondence | `CommReductionCorrespondence.v` | proved lowered pure-rule traces match Dovetail traces |
| linear COMM correspondence | `LinearCommCorrespondence.v` | proved one-shot COMM consumes the matched send and receive, with sound/complete lowering correspondence |
| Rho name grounding | `RhoGroundingAndNames.v` | proved fresh private names avoid capture of grounded facts |
| resting-space fingerprint and observation report | `RhoObservationFingerprint.v`, `RhoObservationReportBoundary.v`, `RhoRuntimeBackendReportBridge.v`, `mettail-rho-runtime::RhoObservationReport`, `mettail_runtime::RuntimeBackendReport::try_observations` | proved exact-key fingerprints are membership-exact, multiplicity-exact, and order-insensitive; planned runtime reports preserve the planned backend boundary, channel, read-order values, exact set-membership fingerprint, and exact counted fingerprint; conversion to the generic `RuntimeBackendReport` preserves Rho backend identity, normalized-AST artifact kind, channel, read-order values, observed count, evidence references, and scalar plus structured observation payload tags without fabricating an Ascent-shaped result; the generic runtime envelope rejects observation-shaped reports unless the backend is `RhoMachine` and the artifact is a Rho runtime artifact |
| ambiguity witnesses | `AmbiguityWitnessEnumeration.v` | proved enabled candidates are enumerated independently of schedule order |
| oracle exactness | `OracleQuotientEquivalence.v` | proved weight-erased key equality is exact |
| call-by-need observation, planned AST artifact, and budget | `RhoCallByNeedObservation.v`, `RhoCallByNeedBudget.v` | proved thunk forcing and memoization preserve weak source observation, accepted need artifacts are AST rather than source text and carry the call-by-need validation profile rather than the scalar-contract profile, accepted planned need execution wraps an accepted artifact, admits both force steps, carries evidence references, cold/hot AST thunk plans observe the source value twice with the expected memo behavior, and bounded force admission respects lookahead and heap budgets |
| Δ1 candidate minima | `DeltaOneMinCostJoin.v` | proved selected preformed join candidates are present, non-refuted, and cost-minimal |
| Δ1 min-cost matching | `DeltaOneMinCostMatching.v` | proved selected left-perfect bipartite join-frontier matchings are endpoint-valid, non-refuted, duplicate-free, left-covering, and globally cost-minimal |
| guarded COMM | `GuardedCommSoundness.v` | proved false guards do not commit and attempts fabricate no facts |
| ambiguity-set preservation | `AmbiguitySetPreservation.v` | proved schedule order preserves observed candidate sets |
| cost-axis separation | `RhoCostAxisSeparation.v` | proved ordering costs cannot remove candidates; refutation is explicit |
| escrow/refund settlement | `RhoEscrowSettlement.v`, `mettail-rho-adapter::settlement` | proved reserve/commit/refund conservation, fail-closed blockers, bounded `u64` overflow blockers, and reserve/refund restoration |
| per-purse determinism | `RhoPurseDeterminism.v`, `formal/tla/rho_settlement/`, `mettail-rho-adapter::LocatedEscrowLedger` | proved duplicate purses reject, missing purses reject, local blockers preserve the ledger, located actions are deterministic, and distinct-purse final ledgers commute |
| backend flip gate | `RhoBackendFlipGate.v` | proved Rho default requires proof, oracle, exact coverage of rejected rules, artifact validation, scheduler-fairness, evidence-reference validity, and deadlock gates |
| planned Rho execution boundary | `RhoPlannedExecutionBoundary.v`, `mettail-rho-runtime::PlannedRhoBackend` | proved and implemented that generated backend execution consumes a flip-gated plan, not merely a raw shape-validated artifact |
| runtime backend dispatch and wrappers | `RuntimeBackendDispatch.v`, `DovetailLanguageBackendWrapper.v`, `RhoLanguageBackendWrapper.v`, `RhoRuntimeBackendReportBridge.v`, `mettail_runtime::RuntimeBackendReport`, `mettail_dovetail_runtime::DovetailRuntimeBackedLanguage`, `mettail_rho_runtime::RhoRuntimeBackedLanguage` | proved default report execution succeeds only when the selected backend is installed; absent Dovetail/Rho defaults fail closed instead of falling back to Ascent; installed Dovetail defaults return Dovetail-report-shaped runtime output and are rejected by the legacy Ascent-shaped compatibility wrapper; the Dovetail wrapper selects `Dovetail` as the default, delegates non-Dovetail backend support to the inner generated language, requires a complete and structurally well-formed checked report, rejects `BoundedByCycleCut`, rejects malformed projected report tables, and rejects Ascent-shaped seeded facts on the Dovetail path; installed Rho defaults return observation-shaped reports backed by Rho runtime artifacts and are rejected by the legacy Ascent-shaped compatibility wrapper; checked `RuntimeBackendReport::try_dovetail` and `try_observations` constructors are the only public non-Ascent report constructors, and `RuntimeBackendReport` fields are private, so malformed report-shaped and observation-shaped outputs cannot enter through an unchecked runtime API or external struct literal; the runtime report bridge preserves observation value tags for native scalar payloads and structured list/map/bag payloads; the Rho wrapper selects `RhoMachine` as the default, delegates non-Rho backend support to the inner generated language, requires a planned backend plus total typed invocation for Rho reports, and rejects Ascent-shaped seeded facts on the Rho path |
| Dovetail report boundary and Rho handoff | `dovetail::report`, `RuntimeReportBridge.v`, `RhoReportHandoff.v` | proved checked extraction reports preserve exact keys, extractor root order, deduplicated term records, and terminal completeness; Rho handoff observes exactly complete-report roots and rejects `BoundedByCycleCut` without observations |
| COMM schedule family and guarded joins | `RhoCommScheduleFamily.v`, `formal/process/rho_comm_slice.json`, `formal/mcrl2/rho_machine/`, `formal/maude/rho_machine/`, `formal/tla/rho_machine/` | proves every finite independent-redex Rho reserve/fire schedule erases to the same visible observations as the direct Dovetail fire schedule, full permutation schedules enable completion, missing-redex prefixes reject completion, and permutation schedules preserve the fired-redex set; the generated process-calculus suite independently checks no deadlock, all 24 visible fire/complete schedules, premature-completion unreachability, branching bisimilarity modulo hidden reserve actions, unique matching terminal normal forms, weak-fair scheduler completion, and guarded-join non-consumption: a failed guard releases data, a valid join can commit afterward, and the rejected bad datum remains observable |
| runtime smoke | `mettail-rho-runtime/tests/run_calculator.rs` | runs a validated Rho-default backend plan for lowered calculator ops on RhoRuntime using `RhoAstSend` call artifacts |
| AST ambiguity witness smoke | `mettail-rho-runtime/tests/rho_ambiguity_ast.rs` | injects receive-less ambiguity witness facts as normalized AST, observes grouped key/payload tuples, and feeds them into `AmbiguityWitnessSet` |
| differential oracle | `mettail-rho-runtime/tests/rho_vs_ascent.rs` | compares a validated Rho-default backend plan with Ascent results |

The Rho bridge now has mechanized model contracts for pure COMM, name
grounding, exact observation, call-by-need forcing, `Δ1` cost-minimal candidate
selection and exact bipartite matching, guards, ambiguity preservation,
cost-axis separation, escrow/refund settlement, per-purse determinism, exact
rejected-rule delegation, normalized-`Par`
well-formedness, source-text artifact exclusion, backend flip gating, and
fail-closed runtime dispatch.
Dovetail-to-runtime handoff now starts from a checked Dovetail report rather
than an Ascent-shaped success value. The handoff proof requires complete
reports before emitting Rho-visible observations, preserves the extractor root
order as the observed exact-key sequence, and rejects `BoundedByCycleCut`
reports without observations.
Generated Rho execution now starts from `PlannedRhoBackend`, which wraps the
`RhoDefaultBackendPlan` produced by the flip gate; raw validated artifacts remain
available for oracle/debug helpers only. Dynamic contract calls and ambiguity
witnesses are constructed with `mettail_rho_codegen::RhoAstSend`. Its
`RhoAstLiteral` payloads lower scalar values, collections, unforgeable names,
and rhocalc bags directly to normalized `Par`; the rhocalc bag ABI tag is owned
by `mettail-rho-codegen` and re-exported by `mettail-rho-runtime` so send-side
encoding and runtime observation decoding cannot drift. The rhocalc process
bridge lowers MeTTaIL/WPDA `Proc` and `Name` values with `lower_rhocalc_proc`
and `lower_rhocalc_name`, and lowers generated `RhoCalcTerm` values with
`lower_rhocalc_term`, so both dynamic calls and transport-pure rhocalc
programs cross the runtime boundary as normalized `Par` values. Ambiguous
`Proc` terms cross as exact-key-deduplicated parallel branches, while
cross-category ambiguity fails closed rather than choosing one branch. Their
Rholang-looking strings are annotations for logs, tests, and documentation, not
executable source.
Generated Rho observations now use typed `RhoObservationReport<T>` at the
Rho-runtime boundary and `mettail_runtime::RuntimeBackendReport` at the generic
`Language` boundary rather than forcing Rho results into `AscentResults`.
The typed report carries the planned execution boundary, the artifact kind, the
observed channel, the read-order values, an order-insensitive set-membership
fingerprint for set-semantics oracle comparison, and an order-insensitive
counted fingerprint for bag-sensitive observations. With the optional
`mettail-rho-runtime/runtime-report` feature, typed Rho observation payloads
convert through `try_into_runtime_backend_report`, which fails closed for future
unknown artifact kinds and then through `RuntimeBackendReport::try_observations`,
which rejects observation-shaped output unless it names `RhoMachine` and a Rho
runtime artifact. The generic report carries the selected backend, artifact
kind, evidence references, and channel observations so callers can select
`RhoMachine` without depending on Ascent-shaped fact materialization.
The current planned Rho backend observes lowered native scalar and collection
payloads through `RuntimeObservationValue`: `Int`, `Bool`, and `Str` become
`Int`, `Bool`, and `Text`; byte, URI, bit-exact numeric, unforgeable-name, list,
tuple, set, map, and tagged rhocalc-bag payloads retain their own runtime value
tags. `RhoRuntimeBackendReportBridge.v` names the tag-preservation contract.
`mettail-rho-runtime/tests/run_calculator.rs` executes the full native
calculator scalar family currently admitted by the lowerer on the real
in-memory RhoRuntime: integer arithmetic, integer, boolean, and string
comparisons, boolean `and`/`or`/`not`, and string concatenation.
`mettail-rho-runtime/tests/rho_rhocalc_ast.rs` exercises the structured path by
lowering rhocalc list, map, and bag typed AST payloads directly to `rhoapi::Par`
and observing recursive runtime values from RSpace.
The string-valued check is deliberately end-to-end at the wrapper boundary:
the Calculator snippets `"rho" ++ "net"` and `"rho" + "net"` are parsed by the
retained MeTTaIL/WPDA frontend, mapped to typed `Str::Concat` and `Str::AddStr`
terms, converted by the Rho wrapper's invocation mapper into normalized
`rhoapi::Par` contract calls, executed by RhoRuntime, and returned as
`RuntimeObservationValue::Text("rhonet")` observations in the generic runtime
report. The second snippet is an important regression: the source token is `+`,
but the typed rule is `Str × Str → Str`, so the generated AST body must be
`EPlusPlus`, not integer `EPlus`.
Generated languages do not need to depend on `mettail-rho-runtime` to become
Rho-default. `RhoRuntimeBackedLanguage<L, F>` lives in the Rho runtime crate and
wraps an existing generated `Language`: `L` still owns parsing, environments,
type inference, CEK decomposition, and explicit Ascent oracle execution, while
`F` maps a typed generated term into a dynamic `rhoapi::Par` call or direct
observation request. The wrapper advertises `RhoMachine` as the default
runtime backend through the concrete `Language::runtime_backend_capabilities()`
view, not by mutating the generated `LanguageMetadata::runtime_backends()`
table. Static metadata therefore remains a statement about the generated crate;
the runtime capability view is a statement about the particular wrapped value,
including the flip-gated Rho plan evidence attached to it. This keeps the
dependency direction one-way and keeps Rho execution AST-first: generated calls
are `rhoapi::Par` values, with any Rholang-looking text remaining only a reader
annotation.
Generated languages likewise do not need a reverse dependency loop to expose
Dovetail as a selected runtime backend. `DovetailRuntimeBackedLanguage<L, F>`
lives in `mettail-dovetail-runtime`, wraps an existing generated `Language`,
makes `RuntimeBackend::Dovetail` the concrete default, projects
`dovetail::report::DovetailRunReport` into `RuntimeDovetailRunReport`, and
returns `RuntimeBackendOutput::Dovetail`. It rejects incomplete
`BoundedByCycleCut` reports for production default execution, validates that
the projected runtime report table is well formed, and rejects Ascent-shaped
seeded facts on the Dovetail path. The well-formedness gate checks root
ordinals, unique term keys, root flags, and non-dangling derivation edges, which
keeps Dovetail reports, Ascent graphs, and Rho observations separate at the
runtime API boundary.
Per-language production flips still require the runtime gates listed below.

## Rollout Phases

![M-RHO rollout phases](figures/07-verification-and-rollout.svg)

PlantUML source:
[figures/07-verification-and-rollout.puml](figures/07-verification-and-rollout.puml).

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
- `RhocalcAstLowering.v` proves the concrete AST-first rhocalc bridge model:
  accepted lowerings produce AST artifacts rather than source text, quote/drop
  lowers to the quoted body, ambiguous two-branch Proc terms preserve both
  branches, one-input COMM fires the lowered payload, two-input COMM is one
  atomic receive over both channels, syntactic binder order matches f1r3node's
  `k - 1 - i` de Bruijn convention, and receive-local bound bits are removed
  from the enclosing local-free set.
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
- WPDA rhocalc source parsing followed by direct normalized-`Par` lowering;
- generated-term ambiguity followed by exact-key branch preservation, exact
  duplicate deduplication, and fail-closed cross-category ambiguity rejection;
- received-name channel reuse through the AST path;
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
repeated force after a miss preserves the memo. The source value is arbitrary in
the model, so the proof applies to generated-language payloads rather than only
to the sample string used by tests. It also models the generated artifact
boundary: accepted call-by-need plans are AST artifacts, not Rholang source
text, and they must carry the call-by-need validation profile rather than the
scalar-contract profile. The current cold/hot thunk plans both observe the
source value twice while preserving the expected memo state.

`RhoCallByNeedBudget.v` proves the bounded admission contract for
`Lookahead[n] + HeapBudget`: zero lookahead blocks a force before observation,
a memo hit consumes only lookahead, a memo miss consumes lookahead plus exactly
one heap cell, a memo miss without heap budget blocks without changing the
budget, every successful bounded force has passed admission, and every
successful bounded observation still matches `source_eval(t)`.

Rust/runtime gate:

- `mettail_rho_codegen::admit_call_by_need_force` is the executable admission
  contract mirrored by `RhoCallByNeedBudget.v`.
- `mettail_rho_codegen::CallByNeedBudget` carries the remaining lookahead and
  heap-cell budgets.
- `mettail_rho_codegen::CallByNeedBudgetBlocker::LookaheadExceeded` and
  `mettail_rho_codegen::CallByNeedBudgetBlocker::HeapBudgetExceeded` report the
  explicit boundedness reason.
- `mettail_rho_codegen::CallByNeedThunkSpec` is the generated-language
  parameter block for the thunk artifact. It carries the initial cold/hot state,
  source value, evaluation marker, public value channel, and evaluation-trace
  channel; it rejects empty fields and rejects equal public/evaluation channels
  so observations remain unambiguous.
- `mettail_rho_codegen::build_call_by_need_thunk_ast` constructs the current
  memoized-thunk execution slice as normalized `rhoapi::Par`; its
  `text_annotation` is reader/debug metadata and is not parsed for execution.
- `mettail_rho_codegen::build_call_by_need_thunk_ast_from_spec` constructs the
  same verified topology from generated-language parameters: one private thunk
  contract, one state cell, one memo cell, and two observer continuations. The
  parameterized value and channels are embedded directly in the AST.
- `mettail_rho_codegen::build_call_by_need_thunk_program` wraps that AST in a
  `RhoProgram` carrying `RhoAstValidationProfile::CallByNeedThunk`, and
  `ValidatedRhoProgram::try_from` rejects the same thunk if it is mislabeled as
  a scalar-contract artifact.
- `mettail_rho_codegen::plan_call_by_need_thunk` is the need-specific planned
  execution boundary: it admits the two-force sequence under the configured
  lookahead/heap budget, validates the call-by-need AST artifact, and requires
  proof/runtime-oracle/budget evidence references before returning a
  `CallByNeedThunkPlan`.
- `mettail_rho_codegen::plan_call_by_need_thunk_with_spec` is the
  generated-language entry point. The compatibility helper
  `plan_call_by_need_thunk` delegates to it with the sample
  `value`/`compute`/`OUT`/`EVAL` fixture.
- `mettail_rho_runtime::PlannedCallByNeedThunk` consumes `CallByNeedThunkPlan`
  for runtime execution, so M-RHO.2 tests do not inject a bare
  `ValidatedRhoProgram` as the generated need path.

- `rho_call_by_need::call_by_need_force_miss_memoizes_and_repeated_force_reuses_value`
  validates a generated cold thunk AST, injects the validated artifact, forces
  it twice in one RhoRuntime run, and observes one compute marker plus two
  public values.
- `rho_call_by_need::call_by_need_memo_hit_observes_value_without_compute_marker`
  validates a generated hot thunk AST, injects the validated artifact, forces it
  twice in one RhoRuntime run, and observes no compute marker.
- `rho_call_by_need::call_by_need_parameterized_payload_and_channels_observe_generated_values`
  validates a generated cold thunk AST with value `answer`, evaluation marker
  `calculator-add`, public channel `RESULT`, and trace channel `TRACE`; runtime
  execution observes `answer` twice on `RESULT` and `calculator-add` once on
  `TRACE`.

Strong bisimulation is not the contract across force boundaries because the
target has internal communication steps that the source observation hides.

## M-RHO.3: Cost, `Δ1` Join, Guards, and Ambiguity

Verified statement:

Harden advanced runtime behavior.

Gate clauses:

- `Δ1` candidate minima for already-formed n-ary join candidates;
- `Δ1` min-cost left-perfect matching over the finite admitted join frontier, where
  the left side is the required join obligations and the right side is the
  message/witness slots admitted to that frontier; all required left obligations
  are covered, and extra right witnesses may remain unused;
- two-axis cost model: refutation versus ordering;
- per-purse determinism: a located funding operation affects exactly one
  unique purse, duplicate purse states reject, and distinct-purse operations
  commute on the final ledger;
- escrow settlement: reserve before candidate commit, charge only committed
  winners, and refund failed or abandoned candidates;
- guarded-COMM soundness;
- ambiguity-set preservation under nondeterministic schedules;
- mergeable-channel optimization only when the algebraic contract matches.

The current Rust matching selector is an exact exhaustive reference search over
the finite enabled frontier: it enumerates feasible left-perfect matchings, sums
edge costs exactly as `u128`, and returns every globally minimum-cost matching. A
Hungarian or min-cost-flow implementation may replace that search only as a
performance optimization behind the same public contract; because semantic
ambiguity is observable, an optimized implementation must still surface every
equal-cost optimum or return a checked certificate that drives an
ambiguity-preserving completion step. This matching frontier is a normalized
`Par`/RSpace-level data structure, not generated Rholang source text.

Mechanized evidence:

- `RhoAstSendBoundary.v`
- `DeltaOneMinCostJoin.v`
- `DeltaOneMinCostMatching.v`
- `GuardedCommSoundness.v`
- `AmbiguityWitnessEnumeration.v`
- `AmbiguitySetPreservation.v`
- `RhoCostAxisSeparation.v`
- `RhoEscrowSettlement.v`
- `RhoPurseDeterminism.v`
- `formal/tla/rho_settlement/RhoPurseSettlement.tla`

Rust adapter evidence:

- `mettail_rho_codegen::RhoAstSend`
- `mettail_rho_codegen::RhoAstLiteral`, including scalar, collection,
  unforgeable-name, and tagged rhocalc-bag payloads
- `mettail_rho_adapter::DeltaOneCandidate`
- `mettail_rho_adapter::DeltaOneMatchEdge`
- `mettail_rho_adapter::DeltaOneMatching`
- `mettail_rho_adapter::AmbiguityCandidate`
- `mettail_rho_adapter::AmbiguityWitnessSet`
- `mettail_rho_adapter::AmbiguityWitnessConflict`
- `mettail_rho_adapter::select_delta1_minima`
- `mettail_rho_adapter::select_delta1_min_cost_left_perfect_matchings`
- `mettail_rho_adapter::collect_enabled_ambiguity_witnesses`
- `mettail_rho_adapter::ambiguity_observes_key`
- `mettail_rho_adapter::{reserve_escrow, commit_escrow, refund_escrow}`
- `mettail_rho_adapter::{LocatedEscrowLedger, SettlementAction}`
- `mettail_rho_adapter::delta1_selects_index`
- `mettail_rho_adapter::delta1_selects_left_perfect_matching_indices`
- `delta1_selects_all_enabled_minimal_ties`
- `delta1_refutation_precedes_ordering`
- `delta1_returns_empty_when_no_candidate_is_enabled`
- `delta1_matching_selects_cheapest_left_perfect_assignment`
- `delta1_matching_preserves_equal_cost_ambiguity`
- `delta1_matching_is_globally_optimal_not_greedy`
- `delta1_matching_refutation_precedes_ordering`
- `delta1_matching_returns_empty_without_left_perfect_assignment`
- `delta1_matching_allows_unused_right_witnesses`
- `delta1_matching_ignores_edges_outside_declared_frontier`
- `delta1_matching_empty_frontier_has_empty_left_perfect_matching`
- `ambiguity::collects_every_enabled_witness`
- `ambiguity::schedule_order_preserves_observed_witness_set`
- `ambiguity::exact_duplicate_witness_is_idempotent`
- `ambiguity::duplicate_key_with_different_payload_is_rejected`
- `ambiguity::disabled_conflicting_payload_is_ignored`
- `ambiguity::observes_key_only_when_enabled_and_conflict_free`
- `rho_ambiguity_ast::ast_witness_facts_preserve_ambiguity_set_across_schedule_order`
- `rho_ambiguity_ast::ast_witness_exact_duplicates_are_idempotent_after_runtime_observation`
- `rho_ambiguity_ast::ast_witness_conflicting_payload_rejects_after_runtime_observation`
- `settlement::located_ledger_rejects_duplicate_purse_states`
- `settlement::located_ledger_missing_purse_preserves_ledger`
- `settlement::located_ledger_updates_only_matching_purse`
- `settlement::located_ledger_local_blocker_preserves_whole_ledger`
- `settlement::located_ledger_distinct_purse_actions_commute`
- `settlement::located_ledger_same_sequence_is_deterministic`
- `settlement::located_ledger_owned_apply_matches_borrowed_apply`
- `settlement::reserve_moves_available_to_escrow_and_returns_ticket`
- `settlement::commit_moves_escrow_to_charged_and_preserves_total`
- `settlement::refund_reverses_a_successful_reserve`
- `settlement::reserve_overflow_preserves_state`
- `settlement::commit_overflow_preserves_state`
- `settlement::refund_overflow_preserves_state`
- `rho_guard_oracle::false_single_bind_guard_leaves_data_and_emits_no_output`
- `rho_guard_oracle::guard_filters_multiple_messages_without_consuming_failed_candidate`
- `rho_guard_oracle::false_cross_bind_guard_leaves_all_join_inputs`
- `rho_guard_oracle::cross_bind_guard_can_commit_later_without_consuming_failed_pair`

Acceptance:

`cost_refutes(c) ⇒ c` is absent from `Δ1` selection for evidence reasons.

`cost_orders(c₁, c₂)` may rank enabled candidates but must not remove either
candidate when their ordering costs are equal.

`ambiguity_enabled(w)` inserts witness `w` into the exact-key witness set.
Scheduler order may change the sequence in which witnesses arrive, but not the
observed set. Exact duplicate witnesses are idempotent; the same exact key with
a different payload rejects as `AmbiguityWitnessConflict` rather than
overwriting one semantic alternative with another. Generated witness facts are
receive-less normalized AST sends of the shape `@"witness"!("key", "payload")`;
runtime observation reads the key/payload tuple as one fact before handing it to
`AmbiguityWitnessSet`.

`located(action)` first selects the unique purse named by the action. If no
purse exists, the ledger is preserved with `MissingPurse`. If duplicate purse
states exist, construction rejects the ledger with `DuplicatePurse`. For
distinct purse IDs `p₁ ≠ p₂`, applying an action at `p₁` and then an action at
`p₂` produces the same final ledger as applying them in the opposite order.

`reserve(c)` moves funds from available balance into escrow and returns a
ticket. `commit(ticket)` moves exactly the ticket amount from escrow to charged.
`refund(ticket)` returns exactly the ticket amount from escrow to available.
Mismatched purses, insufficient available funds, insufficient escrow, and
bounded-machine arithmetic overflow preserve the input state and report an
explicit blocker.

`guard(σ) = false` behaves as no match: no guarded body is emitted, and every
datum considered by the failed match remains resting for a later satisfying
match.

## M-RHO.4: Per-Language Flip

Verified statement:

Make Rho the default runtime backend for a language, in place of the CESK
runtime backend, only after proof, oracle, coverage, artifact-validation,
scheduler-fairness, evidence-reference audit, and deadlock gates pass.

Flip condition for language `L`:

`Proofs(L) ∧ OracleParity(L) ∧ Coverage(L) ∧ ArtifactValidation(L) ∧ SchedulerFairness(L) ∧ EvidenceRefsValid(L) ∧ NoNewDeadlocks(L)`

`RhoBackendFlipGate.v` proves the Boolean flip gate is exactly this conjunction
and that any missing gate blocks the flip. `RhoParWellFormedness.v` supplies the
shape proof for the current scalar-contract `Par` fragment, `RhoArtifactBoundary.v`
proves source-text artifacts are not accepted generated-backend artifacts, and
the Rust validator is the executable gate for generated artifacts.
`RhoRejectedCoverage.v` proves the Rust default-backend planner's exact
coverage wrapper at the rule-identity level: `AllRulesLowered` is valid only
when the rejected set is empty; `CoveredRejectedRules` is valid only when typed
dispositions name exactly the rejected rule set; and omitted, stale, duplicate,
blank-rule, or blank-evidence dispositions block the default-backend gate.
`RhoBackendFlipGate.v` also models the coverage counters consumed by the flip
gate, including the `invalid_dispositions` counter. Its
`deadlock_diagnostic_blocks_flip` theorem models the codegen analyzer output:
any non-empty channel-deadlock diagnostic list makes `NoNewDeadlocks(L)` false.
The same theory also models Rust-side evidence-reference hygiene with
`default_backend_gate_with_refs`: if a positive proof, oracle, coverage-audit,
or scheduler-fairness gate has zero stable evidence references, or if any gate
evidence reference is blank or invalid under the selected audit policy, the
default-backend gate is false.
The `missing_scheduler_fairness_blocks_flip` theorem proves that a language
cannot flip while the scheduler-fairness obligation is open. The
`clean_deadlock_report_reduces_to_other_gates` theorem proves that an empty
deadlock report leaves the proof, oracle, coverage, artifact-validation, and
scheduler-fairness gates as the remaining flip obligations.
The `no_blockers_iff_can_flip` and `any_blocker_blocks_flip` theorems model the
Rust blocker-list API: a language can flip exactly when no blocker remains.
The `default_backend_gate_iff_all_evidence` theorem models
`plan_rho_default_backend`: proof, oracle, scheduler fairness, coverage audit,
no uncovered rejected rules, no extraneous disposition claims, no invalid
dispositions, and no deadlock diagnostics are jointly necessary and sufficient.
The Rust planner strengthens that Boolean model by requiring non-empty,
nonblank evidence-reference lists for every positive externally supplied gate.
Production callers use `plan_rho_default_backend_with_evidence_audit`, which
also rejects missing repository-local evidence artifacts, absolute or
parent-traversing local paths, and logical evidence identifiers whose prefix was
not explicitly allowed by the caller. The non-audited planner remains available
for pure model construction and focused unit tests.
Accepted `RhoDefaultBackendPlan` values expose the resulting sorted
`evidence_refs` vector so generated language metadata can populate
`BackendCapabilityDef::evidence_refs` without inventing claims after the fact.

Rust flip-gate evidence:

- `mettail_rho_codegen::plan_rho_default_backend`
- `mettail_rho_codegen::plan_rho_default_backend_with_evidence_audit`
- `mettail_rho_codegen::RhoEvidenceRefAuditPolicy`
- `mettail_rho_codegen::RhoEvidenceRefAuditDiagnostic`
- `mettail_rho_codegen::RhoDefaultBackendPlan`
- `mettail_rho_codegen::RhoDefaultBackendPlanError`
- `mettail_runtime::RuntimeBackendReport`
- `mettail_runtime::RuntimeBackendArtifact`
- `mettail_runtime::RuntimeChannelObservation`
- `mettail_rho_runtime::PlannedRhoBackend`
- `mettail_rho_runtime::RhoObservationReport`
- `mettail_rho_runtime::IntoRuntimeObservationValue`
- `mettail_rho_runtime::RuntimeReportConversionError`
- `mettail_rho_runtime::RhoExecutionBoundary`
- `mettail_rho_codegen::RhoProgram`
- `mettail_rho_codegen::validate_rho_program`
- `mettail_rho_codegen::RhoValidationError`
- `mettail_rho_codegen::RhoDefaultBackendEvidence`
- `mettail_rho_codegen::RhoDefaultBackendEvidenceGate`
- `mettail_rho_codegen::RhoGateEvidenceDiagnostic`
- `mettail_rho_codegen::RhoDefaultBackendPlan::evidence_refs`
- `mettail_rho_codegen::RhoCoverageEvidence`
- `mettail_rho_codegen::RhoRejectedRuleDisposition`
- `mettail_rho_codegen::RhoRejectedRuleDispositionKind`
- `mettail_rho_codegen::RhoRejectedRuleDispositionDiagnostic`
- `mettail_rho_codegen::decide_rho_flip`
- `mettail_rho_codegen::RhoFlipDecision::can_flip_to_rho`
- `mettail_rho_codegen::RhoFlipBlocker`
- `mettail_rho_codegen::RhoFlipBlocker::ArtifactValidation`
- `mettail_rho_codegen::RhoFlipBlocker::SchedulerFairness`
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
- `default_backend_plan_accepts_exact_covered_rejections`
- `default_backend_plan_rejects_stale_disposition_claims`
- `default_backend_plan_rejects_inauditable_dispositions`
- `default_backend_plan_rejects_duplicate_dispositions`
- `default_backend_plan_reports_all_non_coverage_gate_failures`
- `default_backend_plan_rejects_passed_gate_without_evidence_refs`
- `default_backend_plan_rejects_blank_gate_evidence_refs`
- `audited_default_backend_plan_succeeds_for_existing_local_evidence_refs`
- `audited_default_backend_plan_rejects_missing_local_evidence_refs`
- `audited_default_backend_plan_requires_allowed_logical_evidence_prefixes`

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
Verify Dovetail cyclic extraction boundary:

  make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail-cyclic-boundary
```

```text
Verify Dovetail budget contracts:

  make -C formal check-capped FORMAL_CAPPED_TARGET=why3-dovetail-budget
  make -C formal check-capped FORMAL_CAPPED_TARGET=creusot-dovetail-budget
```

```text
Verify Dovetail/Rho proof-hole hygiene:

  make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-critical-zero-admission
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
| boundedness | no bounded cyclic extraction reported as complete; `CyclicEnumerationImpossibility.v` explains why productive cyclic spaces cannot be finitely exhausted |
| dependency | no reverse dependency from F1r3node to MeTTaIL |
| runtime path | generated bridge execution uses `PlannedRhoBackend` built from a flip-gated `RhoDefaultBackendPlan`; the plan carries a normalized `rhoapi::Par` artifact injected directly through opaque `ValidatedRhoProgram`; `RhoRuntimeBackedLanguage` can wrap a generated language as Rho-default without adding a reverse dependency from generated crates to the Rho runtime; static generated backend metadata remains crate-local, while `Language::runtime_backend_capabilities()` exposes the concrete wrapper-installed Rho default and its evidence references; the generic `Language` path returns `RuntimeBackendReport` for selected backends, and the Rho boundary returns `RhoObservationReport<T>` rather than `AscentResults`; source-text evaluation is limited to hand-authored regression oracles |
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
