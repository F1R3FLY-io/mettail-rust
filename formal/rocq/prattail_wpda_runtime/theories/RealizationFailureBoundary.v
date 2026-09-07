(*
 * Atomic publication of one realization request. An internal callback can
 * discover a key-cache or reconstruction failure after provisional candidates
 * exist. The public boundary must return that failure, never those candidates
 * and never an apparently exhaustive empty result. This model does not claim
 * that a successful bounded request is exhaustive; enumeration completeness
 * is a separate, stronger protocol.
 *)
From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.

Section Publication.
  Context {Value KeyFault ReconstructionFault : Type}.

  Inductive realization_failure :=
  | KeyFailure : KeyFault -> realization_failure
  | ReconstructionFailure : ReconstructionFault -> realization_failure.

  Definition remember_failure (previous : option realization_failure)
    (new_failure : realization_failure) : option realization_failure :=
    match previous with Some _ => previous | None => Some new_failure end.

  Record request_state := {
    provisional : list Value;
    first_failure : option realization_failure
  }.

  Inductive observation :=
  | Candidate : Value -> observation
  | Failed : realization_failure -> observation.

  Definition observe (state : request_state) (event : observation) : request_state :=
    match event with
    | Candidate value =>
        {| provisional := value :: provisional state;
           first_failure := first_failure state |}
    | Failed failure =>
        {| provisional := provisional state;
           first_failure := remember_failure (first_failure state) failure |}
    end.

  Definition run (events : list observation) (state : request_state) :=
    fold_left observe events state.

  Definition publish (state : request_state) : realization_failure + list Value :=
    match first_failure state with
    | Some failure => inl failure
    | None => inr (rev (provisional state))
    end.

  Theorem first_failure_survives_every_observation : forall state event failure,
    first_failure state = Some failure ->
    first_failure (observe state event) = Some failure.
  Proof.
    intros state [value|next] failure H; cbn; [exact H |].
    unfold remember_failure. now rewrite H.
  Qed.

  Theorem first_failure_survives_the_remaining_request : forall events state failure,
    first_failure state = Some failure ->
    first_failure (run events state) = Some failure.
  Proof.
    induction events as [|event rest IH]; intros state failure H; cbn; [exact H |].
    apply IH. now apply first_failure_survives_every_observation.
  Qed.

  Theorem failure_publishes_no_candidate_prefix : forall events state failure,
    first_failure state = Some failure ->
    publish (run events state) = inl failure.
  Proof.
    intros events state failure H. unfold publish.
    now rewrite (first_failure_survives_the_remaining_request events state H).
  Qed.

  Corollary failure_is_not_successful_absence : forall events state failure,
    first_failure state = Some failure -> publish (run events state) <> inr [].
  Proof.
    intros events state failure H.
    rewrite (failure_publishes_no_candidate_prefix events state H). discriminate.
  Qed.

  Theorem successful_publication_has_no_recorded_failure : forall state values,
    publish state = inr values -> first_failure state = None.
  Proof.
    intros state values H. unfold publish in H.
    destruct (first_failure state); [discriminate | reflexivity].
  Qed.

  Theorem key_and_reconstruction_failures_remain_distinct : forall key reconstruction,
    KeyFailure key <> ReconstructionFailure reconstruction.
  Proof. discriminate. Qed.

  (* Facade adapters add positions/ranges while retaining the failure itself.
     They do not project the sum back into the old key-cache error type. *)
  Context {Position : Type}.
  Definition add_position (position : Position)
    (result : realization_failure + list Value)
    : (realization_failure * Position) + list Value :=
    match result with
    | inl failure => inl (failure, position)
    | inr values => inr values
    end.

  Theorem facade_retains_the_exact_failure : forall position state failure,
    first_failure state = Some failure ->
    add_position position (publish state) = inl (failure, position).
  Proof.
    intros position state failure H. unfold publish. rewrite H. reflexivity.
  Qed.
End Publication.

Section PartialActionPublication.
  Context {Value Fault : Type}.
  Variable undrained : Fault.

  (* A trusted generated constructor is a partial function. No result means
     this one combination is outside its domain; it need not consume all
     unused arguments on that path. Actual recorded protocol/resource faults
     still dominate, and a constructed result requires a completed frame. *)
  Definition finish_partial_action (failure : option Fault) (frame_complete : bool)
    (result : option Value) : Fault + option Value :=
    match failure with
    | Some fault => inl fault
    | None =>
        match result with
        | None => inr None
        | Some value => if frame_complete then inr (Some value) else inl undrained
        end
    end.

  Theorem rejected_combination_need_not_drain_unused_arguments : forall complete,
    finish_partial_action None complete None = inr None.
  Proof. reflexivity. Qed.

  Theorem protocol_failure_is_never_candidate_rejection : forall fault complete result,
    finish_partial_action (Some fault) complete result = inl fault.
  Proof. reflexivity. Qed.

  Theorem constructed_result_requires_completed_frame : forall failure complete input value,
    finish_partial_action failure complete input = inr (Some value) ->
    failure = None /\ complete = true /\ input = Some value.
  Proof.
    intros [fault|] [|] [result|] value H; cbn in H; try discriminate.
    inversion H; subst. repeat split; reflexivity.
  Qed.
End PartialActionPublication.

Print Assumptions first_failure_survives_the_remaining_request.
Print Assumptions failure_publishes_no_candidate_prefix.
Print Assumptions failure_is_not_successful_absence.
Print Assumptions successful_publication_has_no_recorded_failure.
Print Assumptions key_and_reconstruction_failures_remain_distinct.
Print Assumptions facade_retains_the_exact_failure.
Print Assumptions rejected_combination_need_not_drain_unused_arguments.
Print Assumptions protocol_failure_is_never_candidate_rejection.
Print Assumptions constructed_result_requires_completed_frame.
