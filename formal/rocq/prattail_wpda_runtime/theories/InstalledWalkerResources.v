(** Per-instance guards at existing canonical-WPDA observation boundaries.

    Source correspondence (not a second parser or allocator):
    - wpda_walker::step_canonical_pure dequeues a descriptor and checks work
      BEFORE normalization, add-once dedup and the existing engine callback.
      One admitted dequeue charges one parse item, including dedup hits.
    - sppf::intern_* checks its existing identity table first. Only a miss
      charges one forest node, BEFORE text interning/node push. A hit still
      runs its original body, including Packing weight aggregation.
    - shared fallible intern workers return an explicit error, never a fake
      SPPF_ID_NONE. Original unbounded entry points forward to those same
      workers with no installed limit. Canonical call sites propagate errors
      before subsequent reads, writes or engine callbacks. The first failure
      is retained at the driver/publication boundary, not treated as no-match.
    - Sppf::default/new starts with nodes = []. WpdaWalker::new_for_category
      constructs that empty SPPF (current lines 6263-6335); its seed GSS/stack
      entries are not SPPF nodes. Installed limits are constructor parameters,
      so no forest allocation precedes admission. Any future reserved SPPF
      node must use the same fallible interner, not an uncharged constructor.
    - complete realization uses the existing k-best demand/exhaustion and
      all-demanded-node truncation observations. It cannot publish a bounded
      prefix as a complete family. Existing static bounded/election APIs are
      not changed by this complete-request protocol.

    The observations below are supplied by those original workers. This file
    does not prove their algorithm, semantic quotient, or exhaustion theorem.
    Node/work counts are not RSS, byte, or CPU-time bounds. Existing capability,
    key-cache and reconstruction errors remain prior failures, not overflow.
    ResourceBounds.v separately establishes request/host minimum admission;
    these guards consume the already effective installed per-instance limits. *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget RealizationFailureBoundary.
Import ListNotations.
Local Open Scope type_scope.

Module InstalledWalkerResources.
Definition reused_checked_debit := @successful_debit_is_exact.
Definition reused_failure_publication := @failure_publishes_no_candidate_prefix.

Inductive resource := ParseItems | ForestNodes | Results.
Record limit_fault := { exhausted_resource : resource; configured_limit : nat }.

(** None preserves the original unguarded worker; installed callers supply
    explicit limits, independently of the static environment/default budget. *)
Definition reserve (which : resource) (limit : option nat) (used : nat)
    : limit_fault + nat :=
  match limit with
  | None => inr (S used)
  | Some cap =>
      if used <? cap then inr (S used)
      else inl {| exhausted_resource := which; configured_limit := cap |}
  end.

Theorem successful_reservation_is_bounded : forall which cap used next,
  reserve which (Some cap) used = inr next -> next = S used /\ next <= cap.
Proof.
  intros which cap used next H. unfold reserve in H.
  destruct (used <? cap) eqn:E; [|discriminate].
  apply Nat.ltb_lt in E. inversion H; subst. split; lia.
Qed.

Theorem zero_limit_refuses_first_charge : forall which,
  reserve which (Some 0) 0 =
    inl {| exhausted_resource := which; configured_limit := 0 |}.
Proof. reflexivity. Qed.

Theorem exactly_full_refuses_next_charge : forall which cap,
  reserve which (Some cap) cap =
    inl {| exhausted_resource := which; configured_limit := cap |}.
Proof. intros; unfold reserve; now rewrite Nat.ltb_irrefl. Qed.

Section OriginalWorker.
Context {State Output : Type}.
Variable original : State -> Output * State.

Definition guarded which limit used state : limit_fault + (Output * State * nat) :=
  match reserve which limit used with
  | inl fault => inl fault
  | inr next => let '(output, after) := original state in inr (output, after, next)
  end.

Theorem successful_guard_forwards_original_body : forall which limit used state next,
  reserve which limit used = inr next ->
  guarded which limit used state =
    let '(output, after) := original state in inr (output, after, next).
Proof. intros; unfold guarded; now rewrite H. Qed.

Theorem failed_guard_invokes_no_worker : forall which limit used state fault,
  reserve which limit used = inl fault -> guarded which limit used state = inl fault.
Proof. intros; unfold guarded; now rewrite H. Qed.

Theorem default_guard_keeps_original_body : forall which used state,
  guarded which None used state =
    let '(output, after) := original state in inr (output, after, S used).
Proof. reflexivity. Qed.
End OriginalWorker.

(** The table hit/miss is the existing interner observation, not a new key or
    lookup. No charge on hit does NOT skip the original hit's weight update. *)
Definition allocation_reserve limit used (hit : bool) : limit_fault + nat :=
  if hit then inr used else reserve ForestNodes limit used.

Theorem dedup_hit_never_consumes_a_node : forall limit used,
  allocation_reserve limit used true = inr used.
Proof. reflexivity. Qed.

Theorem fresh_node_uses_the_same_checked_charge : forall limit used,
  allocation_reserve limit used false = reserve ForestNodes limit used.
Proof. reflexivity. Qed.

Definition initial_forest : list unit := [].

Theorem original_empty_initialization_respects_every_cap : forall cap,
  length initial_forest <= cap.
Proof. intros; cbn; lia. Qed.

Section FallibleContinuation.
Context {Fault Input Output : Type}.
Definition bind (result : Fault + Input) (next : Input -> Fault + Output) :=
  match result with inl fault => inl fault | inr value => next value end.

Theorem failed_allocation_never_runs_its_continuation : forall fault next,
  bind (inl fault) next = inl fault.
Proof. reflexivity. Qed.

Theorem successful_allocation_keeps_its_original_continuation : forall value next,
  bind (inr value) next = next value.
Proof. reflexivity. Qed.
End FallibleContinuation.

Section AtomicPublication.
Context {PriorFault Value State : Type}.
Inductive failure :=
| OriginalFailure : PriorFault -> failure
| LimitFailure : limit_fault -> failure.

Definition latch (previous : option failure) (new_failure : failure) :=
  match previous with Some prior => Some prior | None => Some new_failure end.

Theorem first_fault_wins : forall prior later,
  latch (Some prior) later = Some prior.
Proof. reflexivity. Qed.

Definition mutate_if_live (fault : option failure) (original : State -> State) state :=
  match fault with Some _ => state | None => original state end.

Theorem aborted_forest_has_no_further_mutation : forall fault original state,
  mutate_if_live (Some fault) original state = state.
Proof. reflexivity. Qed.

Definition publish_complete (fault : option failure) (root_exhausted truncated : bool)
    (cap : nat) (candidates : list Value) : failure + list Value :=
  match fault with
  | Some error => inl error
  | None =>
      if root_exhausted && negb truncated && (length candidates <=? cap)
      then inr candidates
      else inl (LimitFailure {| exhausted_resource := Results; configured_limit := cap |})
  end.

Theorem prior_failure_discards_all_provisional_candidates : forall fault exhausted truncated cap values,
  publish_complete (Some fault) exhausted truncated cap values = inl fault.
Proof. reflexivity. Qed.

Theorem truncation_cannot_publish_a_complete_prefix : forall exhausted cap values,
  publish_complete None exhausted true cap values =
    inl (LimitFailure {| exhausted_resource := Results; configured_limit := cap |}).
Proof. intros [] cap values; reflexivity. Qed.

Theorem pending_demand_cannot_publish_complete : forall truncated cap values,
  publish_complete None false truncated cap values =
    inl (LimitFailure {| exhausted_resource := Results; configured_limit := cap |}).
Proof. reflexivity. Qed.

Theorem successful_complete_publication_requires_all_observations :
  forall fault exhausted truncated cap values output,
  publish_complete fault exhausted truncated cap values = inr output ->
  fault = None /\ exhausted = true /\ truncated = false /\
    length values <= cap /\ output = values.
Proof.
  intros [fault|] [] [] cap values output H; cbn in H; try discriminate.
  destruct (length values <=? cap) eqn:E; [|discriminate].
  apply Nat.leb_le in E. inversion H; subst. repeat split; auto.
Qed.

Theorem complete_admitted_output_is_not_reordered : forall cap values,
  length values <= cap -> publish_complete None true false cap values = inr values.
Proof. intros; cbn. apply Nat.leb_le in H. now rewrite H. Qed.

Theorem resource_and_original_errors_remain_distinct : forall original resource_fault,
  OriginalFailure original <> LimitFailure resource_fault.
Proof. discriminate. Qed.
End AtomicPublication.

(** A complete bounded request asks the original extractor for cap+1. This
    check precedes machine addition; usize::MAX is not saturated or wrapped. *)
Theorem lookahead_demand_is_machine_safe : forall cap machine_max,
  cap < machine_max -> S cap <= machine_max.
Proof. intros; lia. Qed.

Print Assumptions reused_checked_debit.
Print Assumptions reused_failure_publication.
Print Assumptions successful_reservation_is_bounded.
Print Assumptions zero_limit_refuses_first_charge.
Print Assumptions exactly_full_refuses_next_charge.
Print Assumptions successful_guard_forwards_original_body.
Print Assumptions failed_guard_invokes_no_worker.
Print Assumptions default_guard_keeps_original_body.
Print Assumptions dedup_hit_never_consumes_a_node.
Print Assumptions fresh_node_uses_the_same_checked_charge.
Print Assumptions original_empty_initialization_respects_every_cap.
Print Assumptions failed_allocation_never_runs_its_continuation.
Print Assumptions successful_allocation_keeps_its_original_continuation.
Print Assumptions first_fault_wins.
Print Assumptions aborted_forest_has_no_further_mutation.
Print Assumptions prior_failure_discards_all_provisional_candidates.
Print Assumptions truncation_cannot_publish_a_complete_prefix.
Print Assumptions pending_demand_cannot_publish_complete.
Print Assumptions successful_complete_publication_requires_all_observations.
Print Assumptions complete_admitted_output_is_not_reordered.
Print Assumptions resource_and_original_errors_remain_distinct.
Print Assumptions lookahead_demand_is_machine_safe.
End InstalledWalkerResources.
