(** Fallible observations around the ONE original constructor-label selector.

    Source: grammar-core/src/constructor_labels.rs::generate_literal_label_observed.
    The intended Rust extension takes three FnOnce callbacks returning Result:
    byte probe, native observation, and selected constructor. Existing total
    APIs forward through infallible observation/constructor wrappers; their
    generic Label may itself be a Result and is not flattened by that wrapper.

    Schedule: request byte; propagate its error immediately; on true construct
    BytesLit; otherwise request native; propagate its error immediately; feed
    its successful value into the imported original nonbyte selection and
    construct exactly once. No NativeType match, fallback spelling, opaque
    sentinel, classifier, or constructor is duplicated here.

    A callback may change state even when it fails. The returned state and
    trace retain that effect, but contain no later callback. Traces use the
    existing original event vocabulary, with each failed request recorded at
    its original call site. These are finite interface laws, not an allocator,
    evaluator, decoder, machine-code, or arbitrary callback-correctness proof.

    Owned availability uses the already checked retained SourceObservation.
    Known None is a positive absence, not Unavailable or CanonicalOpaque. Both
    are distinct failures when a native value is actually requested. A true
    byte probe suppresses either; this is not a global store rejection policy.
*)
From Stdlib Require Import List String Bool.
From PrattailWpdaRuntime Require Import ConstructorLabelProjection
  CanonicalOpaqueLabelProjection AuthoredNativeObservationsProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module FallibleConstructorLabelProjection.
Module P := ConstructorLabelProjection.ConstructorLabelProjection.
Module L := CanonicalOpaqueLabelProjection.CanonicalOpaqueLabelProjection.
Module A := AuthoredNativeObservationsProjection.AuthoredNativeObservationsProjection.

Section Callbacks.
Context {State Label Error : Type}.

Definition lift {Value : Type} (callback : State -> Value * State)
    (state : State) : (Value + Error) * State :=
  let '(value, next) := callback state in (inl value, next).

Definition try_literal
    (byte_probe : State -> (bool + Error) * State)
    (observe : State -> (L.LiteralNativeObservation + Error) * State)
    (construct : string -> State -> (Label + Error) * State)
    (state : State) : (Label + Error) * State * list P.Event :=
  let '(byte_result, after_byte) := byte_probe state in
  match byte_result with
  | inr error => (inr error, after_byte, [P.ByteProbe])
  | inl true => P.invoke construct [P.ByteProbe] "BytesLit" after_byte
  | inl false =>
      let '(native_result, after_native) := observe after_byte in
      match native_result with
      | inr error => (inr error, after_native, [P.ByteProbe; P.NativeClassification])
      | inl native =>
          let '(label, probes) := L.nonbyte_selection native in
          P.invoke construct ([P.ByteProbe; P.NativeClassification] ++ probes)
            label after_native
      end
  end.

Theorem byte_error_stops_all_later_callbacks : forall byte observe construct state error failed,
  byte state = (inr error, failed) ->
  try_literal byte observe construct state = (inr error, failed, [P.ByteProbe]).
Proof. intros; unfold try_literal; rewrite H; reflexivity. Qed.

Theorem byte_true_skips_every_native_observation : forall byte observe construct state ready,
  byte state = (inl true, ready) ->
  try_literal byte observe construct state = P.invoke construct [P.ByteProbe] "BytesLit" ready.
Proof. intros; unfold try_literal; rewrite H; reflexivity. Qed.

Theorem native_error_stops_constructor : forall byte observe construct state ready error failed,
  byte state = (inl false, ready) -> observe ready = (inr error, failed) ->
  try_literal byte observe construct state =
    (inr error, failed, [P.ByteProbe; P.NativeClassification]).
Proof. intros; unfold try_literal; rewrite H, H0; reflexivity. Qed.

Theorem successful_probes_reuse_exact_original_selection :
  forall byte observe construct state ready selected native label probes,
  byte state = (inl false, ready) -> observe ready = (inl native, selected) ->
  L.nonbyte_selection native = (label, probes) ->
  try_literal byte observe construct state =
    P.invoke construct ([P.ByteProbe; P.NativeClassification] ++ probes) label selected.
Proof. intros; unfold try_literal; rewrite H, H0, H1; reflexivity. Qed.

Theorem selected_constructor_failure_is_preserved :
  forall byte observe construct state ready selected native label probes error failed,
  byte state = (inl false, ready) -> observe ready = (inl native, selected) ->
  L.nonbyte_selection native = (label, probes) ->
  construct label selected = (inr error, failed) ->
  try_literal byte observe construct state =
    (inr error, failed, ([P.ByteProbe; P.NativeClassification] ++ probes) ++ [P.Construct label]).
Proof.
  intros; unfold try_literal; rewrite H, H0, H1; unfold P.invoke; rewrite H2; reflexivity.
Qed.

Theorem byte_constructor_failure_is_preserved :
  forall byte observe construct state ready error failed,
  byte state = (inl true, ready) -> construct "BytesLit" ready = (inr error, failed) ->
  try_literal byte observe construct state =
    (inr error, failed, [P.ByteProbe; P.Construct "BytesLit"]).
Proof. intros; unfold try_literal; rewrite H; unfold P.invoke; rewrite H0; reflexivity. Qed.

Theorem infallible_probes_preserve_full_old_state_result_and_trace :
  forall byte observe construct state,
  try_literal (lift byte) (lift observe) construct state =
    L.observed_literal byte construct observe state.
Proof.
  intros; unfold try_literal, lift, L.observed_literal.
  destruct (byte state) as [value ready]; destruct value; [reflexivity|].
  destruct (observe ready) as [native selected]; reflexivity.
Qed.

Theorem exact_native_wrapper_reuses_original_label_worker :
  forall byte classify construct state,
  try_literal (lift byte) (lift (L.exact_callback classify)) construct state =
    P.original_literal byte classify construct state.
Proof.
  intros; rewrite infallible_probes_preserve_full_old_state_result_and_trace.
  apply L.exact_wrapper_preserves_full_state_result_and_trace.
Qed.

Theorem canonical_opaque_keeps_single_generic_construction :
  forall byte observe construct state ready selected,
  byte state = (inl false, ready) -> observe ready = (inl L.CanonicalOpaque, selected) ->
  try_literal byte observe construct state =
    P.invoke construct [P.ByteProbe; P.NativeClassification] "Lit" selected.
Proof. intros; unfold try_literal; rewrite H, H0; reflexivity. Qed.
End Callbacks.

(** Separate diagnostic values preserve the source information; production may
    embed these in its existing typed error without manufacturing a label. *)
Inductive ReadError := ByteUnavailable | NativeUnavailable | NativeAbsent.
Definition read_byte (observation : A.SourceObservation bool) : bool + ReadError :=
  match observation with A.Unavailable => inr ByteUnavailable | A.Known byte => inl byte end.
Definition read_native (observation : A.SourceObservation (option L.LiteralNativeObservation))
    : L.LiteralNativeObservation + ReadError :=
  match observation with
  | A.Unavailable => inr NativeUnavailable
  | A.Known None => inr NativeAbsent
  | A.Known (Some native) => inl native
  end.

Theorem known_absence_and_unavailability_have_distinct_errors :
  read_native (A.Known None) = inr NativeAbsent /\
  read_native A.Unavailable = inr NativeUnavailable /\
  read_native (A.Known None) <> read_native A.Unavailable.
Proof. repeat split; try reflexivity; discriminate. Qed.

Theorem known_native_is_not_reclassified : forall native,
  read_native (A.Known (Some native)) = inl native.
Proof. reflexivity. Qed.

Section OwnedCallbacks.
Context {State Label : Type}.
Variable construct : string -> State -> (Label + ReadError) * State.
Definition owned_literal byte native state :=
  try_literal (fun ready => (read_byte byte, ready))
    (fun ready => (read_native native, ready)) construct state.

Theorem missing_byte_is_not_default_false : forall native state,
  owned_literal A.Unavailable native state = (inr ByteUnavailable, state, [P.ByteProbe]).
Proof. reflexivity. Qed.

Theorem byte_true_accepts_even_unavailable_native : forall native state,
  owned_literal (A.Known true) native state = P.invoke construct [P.ByteProbe] "BytesLit" state.
Proof. reflexivity. Qed.

Theorem nonbyte_unavailable_native_does_not_construct : forall state,
  owned_literal (A.Known false) A.Unavailable state =
    (inr NativeUnavailable, state, [P.ByteProbe; P.NativeClassification]).
Proof. reflexivity. Qed.

Theorem nonbyte_absence_is_not_generic_opaque : forall state,
  owned_literal (A.Known false) (A.Known None) state =
    (inr NativeAbsent, state, [P.ByteProbe; P.NativeClassification]).
Proof. reflexivity. Qed.

Theorem owned_present_inputs_retain_old_callback_schedule : forall byte native state,
  owned_literal (A.Known byte) (A.Known (Some native)) state =
    L.observed_literal (fun ready => (byte, ready)) construct (fun ready => (native, ready)) state.
Proof.
  intros; unfold owned_literal, try_literal, read_byte, read_native, L.observed_literal.
  destruct byte; reflexivity.
Qed.
End OwnedCallbacks.

Print Assumptions byte_error_stops_all_later_callbacks.
Print Assumptions byte_true_skips_every_native_observation.
Print Assumptions native_error_stops_constructor.
Print Assumptions successful_probes_reuse_exact_original_selection.
Print Assumptions selected_constructor_failure_is_preserved.
Print Assumptions byte_constructor_failure_is_preserved.
Print Assumptions infallible_probes_preserve_full_old_state_result_and_trace.
Print Assumptions exact_native_wrapper_reuses_original_label_worker.
Print Assumptions canonical_opaque_keeps_single_generic_construction.
Print Assumptions known_absence_and_unavailability_have_distinct_errors.
Print Assumptions known_native_is_not_reclassified.
Print Assumptions missing_byte_is_not_default_false.
Print Assumptions byte_true_accepts_even_unavailable_native.
Print Assumptions nonbyte_unavailable_native_does_not_construct.
Print Assumptions nonbyte_absence_is_not_generic_opaque.
Print Assumptions owned_present_inputs_retain_old_callback_schedule.
End FallibleConstructorLabelProjection.
