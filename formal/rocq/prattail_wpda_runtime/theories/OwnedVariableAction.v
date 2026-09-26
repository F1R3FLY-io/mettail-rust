(** Minimal variable-carrier seam for task 8514.

    runtime/binding.rs's VAR_CACHE and its four public operations move intact
    below the runtime -> prattail dependency edge. Runtime reexports those same
    operations; generated Var actions keep their original calls and argument
    extraction. This is one cache, not a second interner.

    Owned actions observe the original VarRule classifier and the existing
    authored declaration binding/category admits_variables. They attach a
    native FreeVar identity payload, not text or a template hole.
    No ConstructorId is allocated: generated AST constructor IDs remain owned
    by the existing semantic signature producer, while the dynamic free-variable
    carrier is explicitly category indexed, like the native token carrier.

    Identity below is the actual native identity, never a byte encoding.
    Moniker allocation is process-global and history-dependent. No canonical
    SemanticVariableV1 projection is asserted. That remains a full-parity
    obligation. Portable publication and semantic keys explicitly reject this
    ephemeral leaf; they must not turn it into a hole, no-match, or omission.

    DynamicValue lifecycle/wire changes are leaf cases; old variant tags and
    encodings must remain unchanged. This file does not model a whole semantic
    image conversion, binding scope algorithm, or fresh-ID overflow repair.
*)
From Stdlib Require Import List Bool.
Set Implicit Arguments.
Local Open Scope type_scope.

Module OwnedVariableAction.
Section Adapter.
Context {Name Identity State Category Span : Type}.
Record NativeVariablePayload := { variable_category : Category; variable_identity : Identity }.
Record Carrier := { carrier_span : Span; syntax : NativeVariablePayload; value : NativeVariablePayload }.

Definition original (intern : Name -> State -> Identity * State) name state :=
  intern name state.
Definition relocated (intern : Name -> State -> Identity * State) name state :=
  intern name state.

Theorem generated_default_reuses_exact_identity_state : forall intern name state,
  relocated intern name state = original intern name state.
Proof. reflexivity. Qed.

Definition owned intern category span name state :=
  let '(identity, next) := relocated intern name state in
  let payload := {| variable_category := category; variable_identity := identity |} in
  ({| carrier_span := span; syntax := payload; value := payload |}, next).

Theorem one_original_call_same_identity_in_both_projections :
  forall intern category span name state identity next,
  original intern name state = (identity, next) ->
  owned intern category span name state =
    ({| carrier_span := span;
        syntax := {| variable_category := category; variable_identity := identity |};
        value := {| variable_category := category; variable_identity := identity |} |}, next).
Proof. intros; unfold owned, relocated, original in *; rewrite H; reflexivity. Qed.

Definition admitted intern category span name state (allowed : bool) :=
  if allowed then let '(result, next) := owned intern category span name state in
    (Some result, next) else (None, state).

Theorem category_refusal_precedes_identity_worker : forall intern category span name state,
  admitted intern category span name state false = (None, state).
Proof. reflexivity. Qed.

Theorem admitted_category_is_not_inferred_from_name :
  forall intern category span name state identity next,
  intern name state = (identity, next) ->
  variable_category (syntax (fst (owned intern category span name state))) = category.
Proof. intros; unfold owned, relocated; rewrite H; reflexivity. Qed.

Theorem native_payload_preserves_inequality : forall category (left right : Identity),
  left <> right ->
  {| variable_category := category; variable_identity := left |} <>
  {| variable_category := category; variable_identity := right |}.
Proof. intros category left right different equal; inversion equal; contradiction. Qed.

Theorem existing_carrier_projections_unchanged :
  forall (existing : NativeVariablePayload) span,
  syntax {| carrier_span := span; syntax := existing; value := existing |} = existing /\
  value {| carrier_span := span; syntax := existing; value := existing |} = existing.
Proof. intros; split; reflexivity. Qed.
End Adapter.

(** The existing iterative flat traversal observes every leaf, including nested
    leaves. These laws cover its publication guard, not a new traversal or wire
    format. [old_encode] is the original encoder, including its old failures. *)
Section Publication.
Context {OldValue Bytes Fault : Type}.
Inductive PublicationError := NativeVariable | ExistingEncoding (fault : Fault).
Definition publish (has_native : bool)
    (old_encode : OldValue -> Fault + Bytes) (old_value : OldValue)
    : PublicationError + Bytes :=
  if has_native then inl NativeVariable else
    match old_encode old_value with
    | inl fault => inl (ExistingEncoding fault)
    | inr bytes => inr bytes
    end.

Theorem native_publication_is_explicit_error : forall old_encode old_value,
  publish true old_encode old_value = inl NativeVariable.
Proof. reflexivity. Qed.

Theorem existing_wire_bytes_unchanged : forall old_encode old_value bytes,
  old_encode old_value = inr bytes ->
  publish false old_encode old_value = inr bytes.
Proof. intros; unfold publish; rewrite H; reflexivity. Qed.

Theorem existing_encoding_failure_is_preserved : forall old_encode old_value fault,
  old_encode old_value = inl fault ->
  publish false old_encode old_value = inl (ExistingEncoding fault).
Proof. intros; unfold publish; rewrite H; reflexivity. Qed.

Theorem native_error_distinct_from_encoding_failure : forall fault,
  NativeVariable <> ExistingEncoding fault.
Proof. intros fault equal; discriminate equal. Qed.

Theorem nested_native_leaf_cannot_be_omitted : forall before after old_encode old_value,
  publish (existsb (fun native => native) (before ++ true :: after)) old_encode old_value =
    inl NativeVariable.
Proof.
  intros; unfold publish; rewrite existsb_app; simpl.
  destruct (existsb (fun native => native) before); reflexivity.
Qed.
End Publication.
Print Assumptions generated_default_reuses_exact_identity_state.
Print Assumptions one_original_call_same_identity_in_both_projections.
Print Assumptions category_refusal_precedes_identity_worker.
Print Assumptions admitted_category_is_not_inferred_from_name.
Print Assumptions native_payload_preserves_inequality.
Print Assumptions existing_carrier_projections_unchanged.
Print Assumptions native_publication_is_explicit_error.
Print Assumptions existing_wire_bytes_unchanged.
Print Assumptions existing_encoding_failure_is_preserved.
Print Assumptions native_error_distinct_from_encoding_failure.
Print Assumptions nested_native_leaf_cannot_be_omitted.
End OwnedVariableAction.
