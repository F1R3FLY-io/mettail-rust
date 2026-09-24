(** Numeric checkpoints in the existing binder workers.

    This is a local refinement of BinderRuleProjection and
    BinderOptionalProjection, not another binder classifier or frame machine.
    The six sites name the exact original Rust arithmetic locations. The
    existing checked_increment is reused, including its strict increment bound:
    slot counter 254 can become 255; counter 255 cannot allocate another slot.
    Final action arity is instead an inclusive u8 narrowing (255 is accepted).

    Main plain Sep invokes its key/value helper BEFORE the slot checkpoint.
    Mapped Sep finishes the existing map body and binder-presence validation
    BEFORE its checkpoint. Optional Sep consumes its literal close BEFORE the
    checkpoint, but invokes key/value AFTER a successful assignment. Group
    assignment precedes child entry. These are deliberately different orders.

    Checked holds a completed value or a typed numeric failure with the already
    reached callback/counter prefix. Private partially built descriptors are not
    exposed as values. Earlier caller-visible callback/counter effects are not
    rolled back. The original optional rejection/close-cursor laws are imported.
    Legacy wrappers may erase already-checked optional/group errors to None;
    newly checked main increments/casts explicitly refuse outside the original
    representable domain. No debug-panic/release-wrap parity is asserted there.

    Rust must replace only these sites in the SAME loops and propagate optional
    numeric errors without turning them into semantic nonmatches. Theorems below
    certify the pointwise replacements, numeric bounds, prefix composition and
    original state updates. Existing source-reader/finite-execution proofs and
    exact source review/differential tests remain necessary for the full worker.
    No preflight validator, recursive runtime traversal, resource estimator,
    parser algorithm, allocator/unwind claim or extracted Rust is introduced.
*)
From Stdlib Require Import List String Bool NArith Lia.
From PrattailWpdaRuntime Require Import BinderRuleProjection BinderOptionalProjection.
Import ListNotations.
Set Implicit Arguments.

Module BinderNumericAdmission.
Module B := BinderRuleProjection.BinderRuleProjection.
Module O := BinderOptionalProjection.BinderOptionalProjection.

Inductive Site := MainPlainSlot | MainMappedSlot | MainOptionalGroup
  | OptionalGroup | OptionalSlot | FinalActionArity.

Definition checked_narrow value :=
  if N.leb value O.u8_max then Some value else None.
Theorem checked_narrow_exact : forall value narrowed,
  checked_narrow value = Some narrowed <->
    (value <= O.u8_max)%N /\ narrowed = value.
Proof.
  intros value narrowed; unfold checked_narrow.
  destruct (N.leb value O.u8_max) eqn:E.
  - apply N.leb_le in E; split.
    + intro H; injection H as Equal; subst narrowed; split; [exact E|reflexivity].
    + intros [_ ->]; reflexivity.
  - apply N.leb_gt in E; split; [discriminate|intros [H _]; lia].
Qed.
Theorem representable_cast_is_identity : forall value,
  (value <= O.u8_max)%N -> N.modulo value 256%N = value.
Proof. intros value H; apply N.mod_small; unfold O.u8_max in H; lia. Qed.

Section Effects.
Context {State : Type}.
Inductive Checked (A : Type) :=
  | Passed (value : A)
  | Failed (site : Site) (prefix : @O.Effects State).
Arguments Passed {A} _.
Arguments Failed {A} _ _.
Definition bind {A D} (result : Checked A) (next : A -> Checked D) :=
  match result with Passed value => next value | Failed site prefix => Failed site prefix end.
Theorem first_failure_is_terminal : forall A D site prefix (next : A -> Checked D),
  bind (@Failed A site prefix) next = Failed site prefix.
Proof. reflexivity. Qed.

Definition increment_at {A} site limit value prefix (next : N -> Checked A) :=
  match O.checked_increment limit value with
  | Some updated => next updated | None => Failed site prefix end.
Theorem increment_success_reuses_original : forall A site limit value prefix
  (next : N -> Checked A),
  (value < limit)%N -> increment_at site limit value prefix next = next (N.succ value).
Proof.
  intros A site limit value prefix next H; unfold increment_at, O.checked_increment.
  apply N.ltb_lt in H; now rewrite H.
Qed.
Theorem increment_failure_keeps_exact_prefix : forall A site limit value prefix
  (next : N -> Checked A),
  (limit <= value)%N -> increment_at site limit value prefix next = Failed site prefix.
Proof.
  intros A site limit value prefix next H; unfold increment_at, O.checked_increment.
  apply N.ltb_ge in H; now rewrite H.
Qed.

(** The successful update is the original modeled update, not a second one. *)
Definition main_slot_at {A} site (state : @B.MainState State)
  (next : @B.MainState State -> Checked A) :=
  increment_at site O.u8_max (O.collection_slots (B.effect state)) (B.effect state)
    (fun _ => next (B.unchecked_slot_increment state)).
Theorem main_slot_success_is_original_update : forall A site state
  (next : @B.MainState State -> Checked A),
  (O.collection_slots (B.effect state) < O.u8_max)%N ->
  main_slot_at site state next = next (B.unchecked_slot_increment state).
Proof. intros; unfold main_slot_at; now apply increment_success_reuses_original. Qed.
Theorem main_slot_success_retains_representability : forall (state : @B.MainState State),
  B.representable state = true ->
  (O.collection_slots (B.effect state) < O.u8_max)%N ->
  B.representable (B.unchecked_slot_increment state) = true /\
  O.collection_slots (B.effect (B.unchecked_slot_increment state)) =
    N.succ (O.collection_slots (B.effect state)).
Proof.
  intros state H R; unfold B.unchecked_slot_increment; cbn [B.with_effect B.effect B.representable O.set_slots O.collection_slots].
  apply N.ltb_lt in R; rewrite H, R; split; reflexivity.
Qed.

Variable key_value : option nat -> nat -> State -> option string * State.
Definition main_plain_checkpoint {A} declared kind state
  (next : option string -> @B.MainState State -> Checked A) :=
  let e := B.effect state in
  let '(pair_value, callback_state) := key_value declared kind (O.callback_state e) in
  let called := O.after_callback e callback_state
    (O.KeyValueCall kind (O.next_group e) (O.collection_slots e)) in
  main_slot_at MainPlainSlot (B.with_effect state called (B.representable state)) (next pair_value).
Theorem main_plain_failure_occurs_after_callback : forall A declared kind state pair_value called
  (next : option string -> @B.MainState State -> Checked A),
  key_value declared kind (O.callback_state (B.effect state)) = (pair_value, called) ->
  O.collection_slots (B.effect state) = O.u8_max ->
  main_plain_checkpoint declared kind state next =
    Failed MainPlainSlot (O.after_callback (B.effect state) called
      (O.KeyValueCall kind (O.next_group (B.effect state)) (O.collection_slots (B.effect state)))).
Proof.
  intros A declared kind state pair_value called next Call Full.
  unfold main_plain_checkpoint; rewrite Call; unfold main_slot_at.
  cbn [B.with_effect B.effect O.after_callback O.collection_slots].
  apply increment_failure_keeps_exact_prefix; now rewrite Full.
Qed.
Theorem main_plain_success_keeps_original_order : forall A declared kind state pair_value called
  (next : option string -> @B.MainState State -> Checked A),
  key_value declared kind (O.callback_state (B.effect state)) = (pair_value, called) ->
  (O.collection_slots (B.effect state) < O.u8_max)%N ->
  main_plain_checkpoint declared kind state next =
    next pair_value (B.unchecked_slot_increment
      (B.with_effect state (O.after_callback (B.effect state) called
        (O.KeyValueCall kind (O.next_group (B.effect state)) (O.collection_slots (B.effect state))))
        (B.representable state))).
Proof.
  intros A declared kind state pair_value called next Call Bound.
  unfold main_plain_checkpoint; rewrite Call.
  apply main_slot_success_is_original_update; exact Bound.
Qed.

(** [body] is the result of the original B.walk_map_body at its callsite. *)
Definition main_mapped_checkpoint {A} (body : option B.MapBody) state
  (next : B.MapBody -> @B.MainState State -> Checked (option A)) :=
  match body with
  | None => Passed None
  | Some inner => if B.contains_binder inner
      then main_slot_at MainMappedSlot state (next inner)
      else Passed None end.
Theorem mapped_invalid_body_precedes_width_check : forall A state
  (next : B.MapBody -> @B.MainState State -> Checked (option A)),
  main_mapped_checkpoint None state next = Passed None.
Proof. reflexivity. Qed.
Theorem mapped_no_binder_precedes_width_check : forall A inner state
  (next : B.MapBody -> @B.MainState State -> Checked (option A)),
  B.contains_binder inner = false ->
  main_mapped_checkpoint (Some inner) state next = Passed None.
Proof. intros A inner state next H; unfold main_mapped_checkpoint; now rewrite H. Qed.
Theorem mapped_valid_body_reaches_original_slot : forall A inner state
  (next : B.MapBody -> @B.MainState State -> Checked (option A)),
  B.contains_binder inner = true ->
  (O.collection_slots (B.effect state) < O.u8_max)%N ->
  main_mapped_checkpoint (Some inner) state next = next inner (B.unchecked_slot_increment state).
Proof.
  intros A inner state next H Bound; unfold main_mapped_checkpoint; rewrite H.
  now apply main_slot_success_is_original_update.
Qed.

Definition optional_slot_at {A} prefix (next : @O.Effects State -> Checked A) :=
  increment_at OptionalSlot O.u8_max (O.collection_slots prefix) prefix
    (fun updated => next (O.set_slots prefix updated)).
Definition group_at {A} site prefix (next : @O.Effects State -> Checked A) :=
  increment_at site O.u32_max (O.next_group prefix) prefix
    (fun updated => next (O.set_group prefix updated)).
Theorem optional_slot_failure_precedes_callback : forall A prefix
  (next : @O.Effects State -> Checked A),
  O.collection_slots prefix = O.u8_max ->
  optional_slot_at prefix next = Failed OptionalSlot prefix.
Proof.
  intros A prefix next H; unfold optional_slot_at.
  apply increment_failure_keeps_exact_prefix; now rewrite H.
Qed.
Theorem optional_slot_success_assigns_before_callback : forall A prefix
  (next : @O.Effects State -> Checked A),
  (O.collection_slots prefix < O.u8_max)%N ->
  optional_slot_at prefix next = next (O.set_slots prefix (N.succ (O.collection_slots prefix))).
Proof. intros; unfold optional_slot_at; now apply increment_success_reuses_original. Qed.
Theorem group_failure_precedes_child : forall A site prefix
  (next : @O.Effects State -> Checked A),
  O.next_group prefix = O.u32_max -> group_at site prefix next = Failed site prefix.
Proof.
  intros A site prefix next H; unfold group_at.
  apply increment_failure_keeps_exact_prefix; now rewrite H.
Qed.
Theorem group_success_is_original_assignment : forall A site prefix
  (next : @O.Effects State -> Checked A),
  (O.next_group prefix < O.u32_max)%N ->
  group_at site prefix next = next (O.set_group prefix (N.succ (O.next_group prefix))).
Proof. intros; unfold group_at; now apply increment_success_reuses_original. Qed.

(** The original optional machine supplies the private cursor/failure state;
    the new tag refines only the reason for that existing rejection. *)
Theorem optional_collection_failure_refines_original : forall A
  (parameters : string -> option O.ParamKind)
  (kv : nat -> State -> option string * State)
  reader frame rest prefix name separator close element kind
  (next : @O.Effects State -> Checked A),
  O.syntax_at reader (O.items frame) (O.next frame) = Some (O.Literal close) ->
  parameters name = Some (O.Collection element kind) ->
  O.collection_slots prefix = O.u8_max ->
  O.separator_step parameters kv reader frame rest prefix name separator =
    O.reject (O.advance frame) rest prefix /\
  optional_slot_at prefix next = Failed OptionalSlot prefix.
Proof.
  intros A parameters kv reader frame rest prefix name separator close element kind next Close Param Full.
  split.
  - eapply O.collection_overflow_advances_close_but_never_calls; eauto.
  - now apply optional_slot_failure_precedes_callback.
Qed.
Theorem optional_group_failure_refines_original : forall A
  (parameters : string -> option O.ParamKind)
  (kv : nat -> State -> option string * State)
  reader frame rest prefix operation child
  (next : @O.Effects State -> Checked A),
  O.operation_at reader operation = O.Opt child ->
  O.next_group prefix = O.u32_max ->
  O.operation_step parameters kv reader frame rest prefix operation =
    O.reject frame rest prefix /\
  group_at OptionalGroup prefix next = Failed OptionalGroup prefix.
Proof.
  intros A parameters kv reader frame rest prefix operation child next Op Full.
  split.
  - eapply O.option_overflow_retains_effect_prefix; eauto.
  - now apply group_failure_precedes_child.
Qed.

Definition final_arity_at {A} state (next : N -> Checked A) :=
  match checked_narrow (N.of_nat (List.length (B.rule_actions state))) with
  | Some arity => next arity | None => Failed FinalActionArity (B.effect state) end.
Definition finish_checked reader state : Checked (option B.BinderShape) :=
  if (match B.rule_positions state with
      | [] => negb (B.leading_capture (B.rule_leading state)) | _ => false end)
    then Passed None
  else match B.rule_actions state with
    | [] => Passed None
    | _ :: _ => final_arity_at state (fun _ => Passed (B.finish reader state)) end.
Theorem original_finish_field_equals_checked_arity : forall reader (state : @B.MainState State) shape,
  B.finish reader state = Some shape ->
  (N.of_nat (List.length (B.rule_actions state)) <= O.u8_max)%N ->
  B.action_arity shape = N.of_nat (List.length (B.rule_actions state)) /\
  (B.action_arity shape <= O.u8_max)%N.
Proof.
  intros reader state shape Returned Bound; unfold B.finish in Returned.
  destruct (match B.rule_positions state with
    | [] => negb (B.leading_capture (B.rule_leading state)) | _ => false end);
    [discriminate|].
  destruct (B.rule_actions state) as [|first tail] eqn:Args; [discriminate|].
  inversion Returned; subst shape; cbn [B.action_arity].
  rewrite representable_cast_is_identity by exact Bound.
  split; [reflexivity|exact Bound].
Qed.
Theorem final_arity_failure_publishes_no_shape : forall A state (next : N -> Checked A),
  (O.u8_max < N.of_nat (List.length (B.rule_actions state)))%N ->
  final_arity_at state next = Failed FinalActionArity (B.effect state).
Proof.
  intros A state next H; unfold final_arity_at, checked_narrow.
  apply N.leb_gt in H; now rewrite H.
Qed.
Theorem representable_finish_is_original : forall reader state,
  (N.of_nat (List.length (B.rule_actions state)) <= O.u8_max)%N ->
  finish_checked reader state = Passed (B.finish reader state).
Proof.
  intros reader state H; unfold finish_checked, B.finish.
  destruct (match B.rule_positions state with
    | [] => negb (B.leading_capture (B.rule_leading state)) | _ => false end); [reflexivity|].
  destruct (B.rule_actions state) as [|first tail] eqn:Args; [reflexivity|].
  unfold final_arity_at, checked_narrow; rewrite Args.
  apply N.leb_le in H; now rewrite H.
Qed.

Inductive LegacyResult (A : Type) :=
  | LegacyValue (value : option A) | ExplicitOutOfRange (site : Site).
Arguments LegacyValue {A} _.
Arguments ExplicitOutOfRange {A} _.
Definition legacy {A} (result : Checked (option A)) := match result with
  | Passed value => LegacyValue value
  | Failed site _ => match site with
      | MainOptionalGroup | OptionalGroup | OptionalSlot => LegacyValue None
      | _ => ExplicitOutOfRange site end end.
Theorem old_optional_group_refusal_stays_none : forall A prefix,
  legacy (@Failed (option A) MainOptionalGroup prefix) = LegacyValue None /\
  legacy (@Failed (option A) OptionalGroup prefix) = LegacyValue None /\
  legacy (@Failed (option A) OptionalSlot prefix) = LegacyValue None.
Proof. intros; repeat split; reflexivity. Qed.
Theorem new_main_width_refusal_is_explicit : forall A prefix,
  legacy (@Failed (option A) MainPlainSlot prefix) = ExplicitOutOfRange MainPlainSlot /\
  legacy (@Failed (option A) MainMappedSlot prefix) = ExplicitOutOfRange MainMappedSlot /\
  legacy (@Failed (option A) FinalActionArity prefix) = ExplicitOutOfRange FinalActionArity.
Proof. intros; repeat split; reflexivity. Qed.
End Effects.

Print Assumptions checked_narrow_exact.
Print Assumptions representable_cast_is_identity.
Print Assumptions first_failure_is_terminal.
Print Assumptions increment_success_reuses_original.
Print Assumptions increment_failure_keeps_exact_prefix.
Print Assumptions main_slot_success_is_original_update.
Print Assumptions main_slot_success_retains_representability.
Print Assumptions main_plain_failure_occurs_after_callback.
Print Assumptions main_plain_success_keeps_original_order.
Print Assumptions mapped_invalid_body_precedes_width_check.
Print Assumptions mapped_no_binder_precedes_width_check.
Print Assumptions mapped_valid_body_reaches_original_slot.
Print Assumptions optional_slot_failure_precedes_callback.
Print Assumptions optional_slot_success_assigns_before_callback.
Print Assumptions group_failure_precedes_child.
Print Assumptions group_success_is_original_assignment.
Print Assumptions optional_collection_failure_refines_original.
Print Assumptions optional_group_failure_refines_original.
Print Assumptions original_finish_field_equals_checked_arity.
Print Assumptions final_arity_failure_publishes_no_shape.
Print Assumptions representable_finish_is_original.
Print Assumptions old_optional_group_refusal_stays_none.
Print Assumptions new_main_width_refusal_is_explicit.
End BinderNumericAdmission.
