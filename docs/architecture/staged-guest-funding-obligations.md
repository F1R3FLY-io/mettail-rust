# Staged guest funding obligations

Status: formal interface design, not production activation. The existing Rust
runtime does not yet record this proposed guest-obligation journal in native
offered-funded evidence. The physical-prefix supply contract remains a separate
dependency. This document does not claim that Rust implements the model.

OSLF means *Operational Semantics in Logical Form*. A guest **obligation** is
a proof requirement attached to an existing semantic invocation. It is not a
new native charge, funding case, ledger, evaluator, or permission to publish.
The [resource-logic conformance account](oslf-resource-logic-conformance.md)
defines the distinction between exact demand and a conservative bound.

## Existing boundaries

The design uses the following existing mechanisms. Their current guarantees
do not imply that guest obligations already pass through those mechanisms.

| Existing boundary | Source-backed behavior | Obligation extension |
|---|---|---|
| Native preparation and recording | `NativeObservationPreparation` retains a private generation. `reserve_record` checks that generation and the session. Dropped unpublished tickets invalidate recording. `ensure_recording_complete` rejects pending, invalid, or exhausted recordings. | A guest record must belong to that same private execution, not a process-global journal. |
| Native operations | `NativeOperationRecord` binds occurrence, source, locked footprint, predecessors, observation links, completion, and budget prefix. | Bind each guest invocation to its operation and checked prefix. Do not replace the native record. |
| Native replay | The replay ledger waits for declared operation and retry predecessors. `NativeAttemptReplay.v` permits replay permutations while preserving recorded decisions, occurrence multiplicity, and accepted usage. | Preserve that permitted scheduling. Compare the separate canonical guest journal exactly. |
| Installed semantic publication | `InstalledSemanticPublication::authorize` calls `with_authorized_batch_and_hosts` at commit time, under the table lock. | Recheck the retained language and host-profile capabilities at the actual publication boundary. Preparation is not a lease. |
| Complete guest roster | `prepare_host_demand_roster` and its proofs retain all candidates in order, including receipts, and refuse any failed candidate. | Require the complete roster and one authenticated supply witness that covers every alternative. Do not truncate, deduplicate, or choose a cheapest candidate. |
| Offered-funded acceptance | `compare_state_bound_observations` compares complete private observations and roots. `authorize_publication_after_replay` checks the certified replay and activation gate. | Add obligation evidence to the authenticated comparison before obtaining the existing permit. Keep the activation gate. |
| Existing settlement | The producer constructs one `PhloFundingCase`. Replay chooses the pre-state root on failure. | Add no second case or monetary debit. Refusal and cancellation discard private guest effects with the existing rollback. |

## Identity, order, and multiplicity

An invocation identity contains six fields:

1. The native session identifies the execution attempt.
2. The private generation rejects preparations retained across reset or retry.
3. The root identifies the state against which the invocation was checked.
4. The prefix identifies the authenticated native prefix seen by that invocation.
5. The operation identifies its native causal operation.
6. The invocation ordinal distinguishes repeated calls inside that operation.

The journal records these identities in the canonical guest-invocation order
supplied by the execution boundary. Native observation completion order is not
that canonical order. Independent native operations retain their existing
predecessor-based replay freedom. The model does not add a global native lock
or an arbitrary total order to their observations.

Each journal row contains the complete ordered list of projected candidates.
A candidate is represented by its canonical host output and checked receipt.
Two equal candidate values may occur more than once. Equality compares lists,
not sets or only lengths, so it preserves those occurrences. Invocation
identities, unlike candidate values, must be unique in the complete journal.

An independent replay must produce the same identity sequence and the same
candidate sequence in every row. Changing any identity field, omitting a row,
duplicating an invocation, reordering rows, or changing candidate multiplicity
must refuse publication.

## Checker assumptions

The model deliberately keeps five implementation obligations explicit.

1. The execution boundary supplies the complete expected invocation sequence.
   Its derivation from actual native operation and guest-call records needs
   implementation and replay tests. An untrusted list is not that sequence.
2. The installed projection supplies a complete candidate roster for each
   invocation. The existing `CostGradeFundingBoundary` preparation theorem
   preserves its complete list, output order, receipts, owners, and meter.
   It assumes the trusted matcher minted the completeness evidence.
3. The candidate checker is sound for the installed owner, selected relation,
   typed inverse, verified host demand, and authenticated per-signature supply.
   The [physical-prefix supply contract](cost-g-native-prefix-supply.md)
   remains a separate named dependency.
4. `roster_supply_check` validates one authenticated supply witness for the
   complete candidate roster. Its soundness contract places the witness outside
   the universal candidate check. Separate witnesses for separate alternatives
   do not establish this contract.
5. The native validated replay artifact binds the guest evidence to the same
   execution artifact before durable publication. Wire encoding, commitment
   collision resistance, and Rust ownership refinement are not proved here.

The candidate-funding predicate is abstract. It is not defined by native byte
charges or their numeric total. Abstract signature tokens, host work, phlo,
and REV retain their separate meanings. No equation in this model converts
one into another.

The common witness is separate from candidate authentication. For example,
two candidates require one token in different lanes that share one custody.
Capacity one can fund either candidate independently. It cannot supply a common
lane allocation that covers both. Capacity two can. Repeated occurrences of the
same alternative remain in the journal, but they do not become additional
monetary charges. The [prefix contract](cost-g-native-prefix-supply.md) proves
why changing this quantifier order weakens the approved requirement.

The composition theorem is conditional on these checker contracts. It cannot
discharge them by assuming that equal fingerprints prove all semantic facts.

`live_at_commit` is an input Boolean in the Rocq model. The runtime must derive
it from the locked capability table at publication. The model does not prove
that connection or the lock's atomicity. Likewise, complete native recording
guards TLA+ `Seal`. Native prefix validity is a premise of the separate replay
composition theorem, not another check inside `publish_guest_stage`.

## Proposed staged lifecycle

Preparation appends one fully checked row at a time to the private journal.
The expected next invocation identity controls append order. A denied or
cancelled invocation prevents successful sealing. Native refusal evidence
continues to belong to the existing native recording.

Sealing requires complete native recording and the complete guest journal.
Independent replay then reconstructs guest rows and native evidence. Checking
the replay compares complete guest lists and uses the existing native replay
contract. No publication occurs during preparation or replay.

At commit, the host rechecks live capability authority and verifies that no
refusal or cancellation occurred. The existing validated-artifact publisher
then inserts durable evidence before a cache entry. A conflicting durable
entry preserves the previous state. The obligation layer does not alter the
existing monetary projection or create another funding case.

Refusal and cancellation return the captured publication baseline. This
preserves the modeled durable store, cache, money, and published journal.
The theorem does not establish tuple-space, session, or recording-ticket
restoration. Those runtime effects require separate correspondence checks.
It does not refund work or reverse an external callback.
The existing guarded reply
model places observer and receiver callbacks after the authority-held mutation
boundary; arbitrary external callback rollback remains outside that model.

## Formal artifacts and acceptance

The node's [Rocq model][obligation-proof] imports
`NativeAttemptReplay.v` and `ReplayAdmissionPublication.v`. It reuses their
accepted-usage permutation law and conflict-preserving durable publisher.
The guest checker is a parametric composition seam. The Rocq model does not
import or replicate the MeTTaIL matcher or native resource analyzer.

The bounded [TLA+ model][obligation-model] composes the existing
`NativeAttemptReplay` state machine with guest preparation, replay, capability
revocation, publication, refusal, and cancellation. Its expected roster has
two invocations and repeated candidate values. Candidate funding verdicts are
independent of native byte costs.

Rocq checks candidate funding during append. TLA+ `AppendGuest` stages rows
and postpones those checks until `Verify`. Both require checked candidates
before publication. The TLA+ model tests publication safety, not the exact
timing or work consumption of the Rocq append operation.

| Obligation | Rocq theorem | TLA+ invariant |
|---|---|---|
| Complete authenticated candidate roster | `checked_record_has_complete_authenticated_roster` | `PublishedRosterExact`, `AllCandidatesFundedAtPublication` |
| One authenticated supply witness covers every alternative | `checked_record_retains_one_common_supply`, `failed_common_supply_refuses_record` | `CommonSupplyAtPublication` |
| Complete ordered invocation identities | `checked_journal_is_complete_ordered_and_unique` | `CompleteAppend`, `PublishedRosterExact` |
| Omitted, reordered, or duplicated invocation identities refuse | `omitted_reordered_or_duplicated_identity_refuses_journal` | `PublishedRosterExact` |
| Candidate occurrences are not deduplicated | `checked_candidate_multiplicity_is_exact` | `PublishedRosterExact` |
| Append preserves the checked prefix | `successful_append_preserves_prefix_and_next_identity`, `successful_append_preserves_valid_journal_prefix` | `CompleteAppend` |
| All guards precede accepted publication | `accepted_publication_requires_all_obligations` | `PublicationRequiresVerification`, `AuthorityAtPublication` |
| Replay differences refuse publication | `replay_difference_cannot_publish` | `PublishedRosterExact` |
| Cancellation and refusal preserve the baseline | `cancellation_or_refusal_restores_baseline` | `RollbackNoGuestLeak` |
| A revoked capability cannot publish | `revoked_capability_cannot_publish` | `AuthorityAtPublication` |
| Monetary values and case identity do not change | `every_guest_outcome_preserves_monetary_projection` | `NoExtraMonetaryCharge` |
| One existing funding case remains one | `one_existing_funding_case_remains_one` | `OneExistingFundingCase` |
| A durable conflict leaves evidence and cache unchanged | `conflicting_durable_evidence_refuses_without_cache_change` | `RollbackNoGuestLeak`; conflicting initial durable state cannot satisfy `Publish` |
| Ordinary native-only execution needs no fabricated guest row | `empty_guest_journal_preserves_native_only_eligibility` | Not covered by the fixed two-invocation bounded instance |
| Native replay order remains permitted | `guest_extension_preserves_native_replay_usage_and_ceiling` | `NativeSafety`, through the unchanged `NativeAttemptReplay` instance |

`guest_extension_preserves_native_replay_usage_and_ceiling` uses the existing
native permutation theorem. It is not a proof that arbitrary permutations
satisfy the runtime's channel-predecessor constraints. The runtime still checks
those constraints. The bounded native instance retains its existing
independent-worker scheduling abstraction.

The positive configuration is `StagedGuestFundingObligations.cfg`. Each
negative configuration starts with `StagedGuestFundingObligations` and has
the following suffix:

| Negative suffix | Deliberate defect | Required counterexample |
|---|---|---|
| `OmissionUnsafe.cfg` | Accept a replay missing the second invocation | `PublishedRosterExact` |
| `DuplicationUnsafe.cfg` | Accept the first invocation twice | `PublishedRosterExact` |
| `ReorderingUnsafe.cfg` | Accept reversed invocation order | `PublishedRosterExact` |
| `StaleIdentityUnsafe.cfg` | Accept a changed session, generation, root, prefix, operation, or invocation field | `PublishedRosterExact` |
| `CandidateMultiplicityUnsafe.cfg` | Accept a shortened repeated-candidate roster | `PublishedRosterExact` |
| `FirstCandidateOnlyUnsafe.cfg` | Check only the first candidate of each complete roster | `AllCandidatesFundedAtPublication` |
| `IndependentCandidateSupplyUnsafe.cfg` | Use a different shared-custody witness for each candidate | `CommonSupplyAtPublication` |
| `StaleCapabilityUnsafe.cfg` | Publish after capability revocation | `AuthorityAtPublication` |
| `CancelLeakUnsafe.cfg` | Leak prepared evidence on cancellation | `RollbackNoGuestLeak` |
| `RefusalLeakUnsafe.cfg` | Leak prepared evidence on refusal | `RollbackNoGuestLeak` |
| `ExtraFundingCaseUnsafe.cfg` | Create a second monetary funding case at publication | `NoExtraMonetaryCharge` or `OneExistingFundingCase` |

The stale-identity configuration enables six possible field mutations. One
reported counterexample establishes the defect, not six separate exhaustive
mutation reports. Exact record equality in the positive model covers all six.

Required positive checks cover complete append and replay, all-candidate
checking, fresh authority, rollback, unchanged monetary projections, and one
existing funding case. Negative configurations must expose omitted, reordered,
duplicated, and stale guest evidence, skipped candidate checks, stale
capability acceptance, rollback leakage, and a second funding case.

The model includes a two-lane shared-custody oracle. Its capacity is
one or two. `RosterHasCommonSupply` checks all feasible allocations, independently
of the native allocator. The positive configuration must establish
`CommonSupplyAtPublication`. The new negative control permits independent
candidate witnesses and must violate that invariant.

The updated Rocq model passed compilation and independent kernel checking on
2026-10-10. All six assumption reports were closed. The positive TLA+
configuration explored 76,712 generated states and 23,608 distinct states.
No invariant failed, and no states remained in the queue. All eleven negative
configurations failed at their specified invariant. The shared-custody control
violated `CommonSupplyAtPublication`.

`staged_common_supply_iff_concrete_prefix` in
[NativePrefixSupply.v](../../formal/rocq/rho_bridge/theories/NativePrefixSupply.v)
connects this model's common witness to the concrete native-prefix relation.
It retains the invocation's root and prefix. The separate
`same_invocation_two_axis_composition` theorem indexes physical and monetary
evidence by the same invocation identity. These are composition results, not
proofs that the runtime already extracts authenticated inputs.

The current logs are `target/verification/staged-common-supply-rocq-20261010.log`
and `target/verification/staged-common-supply-tla-summary-20261010.log`.
Individual bounded-check logs use the `common-supply-StagedGuestFundingObligations`
prefix in that directory.

The checks ran serially under a 512 MiB memory limit. Logs are under
`target/verification` in the MeTTaIL workspace. The finite instance cannot prove
all Rust interleavings, allocation bounds, arbitrary syntax, cryptographic
provenance, or protocol activation. The physical-prefix implementation and
execution-boundary correspondence remain separate obligations.

The focused proof command, from the node workspace, is:

```sh
coqc -Q formal/rocq/cost_accounted_rho/theories CostAccountedRho formal/rocq/cost_accounted_rho/theories/StagedGuestFundingObligations.v
coqchk -Q formal/rocq/cost_accounted_rho/theories CostAccountedRho CostAccountedRho.StagedGuestFundingObligations
```

The imported native proof artifacts must be current first. From the node's
`formal/tlaplus/cost_accounted_rho` directory, run the positive bounded check:

```sh
tlc -workers 1 -config StagedGuestFundingObligations.cfg StagedGuestFundingObligations.tla
```

Run each negative configuration with the same module. Its expected outcome
is the named invariant violation, not a parse error or an exhausted checker.

## Source references

- [Native recording][recording] and [operation records][operations].
- [Native replay predecessor checks][native-replay] and [replay sessions][sessions].
- [Deterministic reduction identities][reduction].
- [Installed semantic publication](../../rholang-runtime/src/semantic_service.rs).
- [Complete host-demand roster](../../formal/rocq/rho_bridge/theories/CostGradeFundingBoundary.v).
- [Guarded reply publication](../../formal/rocq/runtime_grammar/theories/GuardedReplyPublication.v).
- [Offered-funded acceptance][acceptance], [producer][producer], and [replay][offered-replay].
- [Native attempt proof][attempt-proof] and [validated publication proof][publication-proof].

[recording]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/recording.rs
[operations]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/operations.rs
[native-replay]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/checked_operations/trace/replay.rs
[sessions]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/checked_operations/trace/replay/session.rs
[reduction]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/deterministic_reduction.rs
[acceptance]: ../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/acceptance.rs
[producer]: ../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution/producer.rs
[offered-replay]: ../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution/replay.rs
[attempt-proof]: ../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/NativeAttemptReplay.v
[publication-proof]: ../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/ReplayAdmissionPublication.v
[obligation-proof]: ../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/StagedGuestFundingObligations.v
[obligation-model]: ../../../../f1r3node-rust-f1r3lang/formal/tlaplus/cost_accounted_rho/StagedGuestFundingObligations.tla
