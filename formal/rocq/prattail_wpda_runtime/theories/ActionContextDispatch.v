(** Exact action-context forwarding for the owned action consumer.

    WpdaEngine's new contextual hook must default to the original
    execute_action once, without evaluating/inspecting the supplied context.
    The owned consumer may require a checked source span, but absence is an
    explicit fault before any decoder/native callback, not a guessed span or
    semantic rejection.

    Span is opaque evidence supplied by original observation sites. This file
    does NOT prove any SPPF-to-byte reconstruction: in particular Terminal
    pos+1 is not accepted here as a lattice endpoint. Rust source correspondence
    must identify the actual frame/edge witnesses for every provided span.
    ActionDispatchAdapter owns the unchanged action/frame error boundary;
    OwnedActionAdapter owns the subsequent exact reduction worker sequence.
*)
From Stdlib Require Import List.
Set Implicit Arguments.
Local Open Scope type_scope.

Module ActionContextDispatch.
Section Context.
Context {Args Value Fault Span State : Type}.

Record ActionContext := { checked_span : option Span }.
Definition Execution := (Fault + option Value) * State.

Definition original_dispatch (run : Args -> State -> Execution) args state :=
  run args state.

Definition static_context_dispatch (run : Args -> State -> Execution)
    (_context : ActionContext) args state :=
  original_dispatch run args state.

Theorem static_default_calls_original_once_without_context_observation :
  forall run context args state,
  static_context_dispatch run context args state = original_dispatch run args state.
Proof. reflexivity. Qed.

Definition owned_context_dispatch
    (run : Span -> Args -> State -> Execution) (missing_context : Fault)
    context args state :=
  match checked_span context with
  | None => (inl missing_context, state)
  | Some source_span => run source_span args state
  end.

Theorem exact_context_is_forwarded_without_reconstruction :
  forall run missing_context source_span args state,
  owned_context_dispatch run missing_context
    {| checked_span := Some source_span |} args state = run source_span args state.
Proof. reflexivity. Qed.

Theorem absent_context_fails_before_callbacks :
  forall run missing_context args state,
  owned_context_dispatch run missing_context
    {| checked_span := None |} args state = (inl missing_context, state).
Proof. reflexivity. Qed.

Theorem equal_actual_context_and_worker_preserve_execution :
  forall left right missing_context left_context right_context args state,
  checked_span left_context = checked_span right_context ->
  (forall span actual_args actual_state,
    left span actual_args actual_state = right span actual_args actual_state) ->
  owned_context_dispatch left missing_context left_context args state =
  owned_context_dispatch right missing_context right_context args state.
Proof.
  intros. unfold owned_context_dispatch. rewrite H.
  destruct (checked_span right_context); [apply H0|reflexivity].
Qed.

End Context.
Print Assumptions static_default_calls_original_once_without_context_observation.
Print Assumptions exact_context_is_forwarded_without_reconstruction.
Print Assumptions absent_context_fails_before_callbacks.
Print Assumptions equal_actual_context_and_worker_preserve_execution.
End ActionContextDispatch.
