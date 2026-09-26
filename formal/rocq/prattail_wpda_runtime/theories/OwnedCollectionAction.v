(** Collection action composition, not a new collection evaluator.

    Source schedule: binder.rs emit_binder_action_entry first extracts every
    CollectionId among the source-ordered arguments. Its collection_drain_sites
    loop is REVERSED; each iteration drains and immediately materializes before
    proceeding to the next site. Rejection therefore stops later drains.

    Dynamic materialization calls the existing DynamicValue::collection on
    syntax first and values second, as runtime.rs FinalizeCollection does.
    The supplied finalizer is opaque; its normalization semantics are not
    reimplemented here. Rust retains source indices for publishing the original
    argument order. Extraction/category validation and the surrounding action
    frame's final protocol check belong to ActionDispatchAdapter.
*)
From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope type_scope.

Module OwnedCollectionAction.
Section Composition.
Context {Arg Payload Fault State : Type}.
Record PayloadPair := { syntax : Payload; value : Payload }.

Definition finalize_pair
    (finalize : list Payload -> Fault + Payload) (items : list PayloadPair) :=
  match finalize (map syntax items) with
  | inl fault => inl fault
  | inr syntax_value =>
    match finalize (map value items) with
    | inl fault => inl fault
    | inr evaluated_value =>
      inr {| syntax := syntax_value; value := evaluated_value |}
    end
  end.

Theorem syntax_failure_skips_value_finalization : forall finalize items fault,
  finalize (map syntax items) = inl fault ->
  finalize_pair finalize items = inl fault.
Proof. intros; unfold finalize_pair; rewrite H; reflexivity. Qed.

Theorem both_projections_use_the_same_ordered_items : forall finalize items s v,
  finalize (map syntax items) = inr s ->
  finalize (map value items) = inr v ->
  finalize_pair finalize items = inr {| syntax := s; value := v |}.
Proof. intros; unfold finalize_pair; rewrite H, H0; reflexivity. Qed.

Definition Result := Fault + option (list (nat * PayloadPair)).

Fixpoint drain_sites
    (drain : nat -> State -> list Arg * State)
    (materialize : nat -> list Arg -> Fault + option PayloadPair)
    (sites : list nat) (state : State) : Result * (list nat * State) :=
  match sites with
  | [] => (inr (Some []), ([], state))
  | site :: rest =>
    let '(items, next) := drain site state in
    match materialize site items with
    | inl fault => (inl fault, ([site], next))
    | inr None => (inr None, ([site], next))
    | inr (Some payload_pair) =>
      let '(result, (history, final_state)) := drain_sites drain materialize rest next in
      (match result with
       | inl fault => inl fault
       | inr None => inr None
       | inr (Some values) => inr (Some ((site, payload_pair) :: values))
       end, (site :: history, final_state))
    end
  end.

Definition original_schedule drain materialize source_sites state :=
  drain_sites drain materialize (rev source_sites) state.
Definition owned_schedule drain materialize source_sites state :=
  original_schedule drain materialize source_sites state.

Theorem owned_reuses_reverse_source_schedule : forall drain materialize sites state,
  owned_schedule drain materialize sites state =
  drain_sites drain materialize (rev sites) state.
Proof. reflexivity. Qed.

Theorem rejection_stops_before_earlier_source_drains :
  forall drain materialize site rest state items next,
  drain site state = (items, next) -> materialize site items = inr None ->
  drain_sites drain materialize (site :: rest) state = (inr None, ([site], next)).
Proof. intros; cbn; rewrite H, H0; reflexivity. Qed.

Theorem fault_preserves_post_drain_state :
  forall drain materialize site rest state items next fault,
  drain site state = (items, next) -> materialize site items = inl fault ->
  drain_sites drain materialize (site :: rest) state = (inl fault, ([site], next)).
Proof. intros; cbn; rewrite H, H0; reflexivity. Qed.

Theorem two_slots_keep_source_indices_and_reverse_callback_order :
  forall drain materialize first second state a b middle final_state x y,
  drain second state = (b, middle) -> materialize second b = inr (Some y) ->
  drain first middle = (a, final_state) -> materialize first a = inr (Some x) ->
  owned_schedule drain materialize [first; second] state =
    (inr (Some [(second, y); (first, x)]), ([second; first], final_state)).
Proof. intros; unfold owned_schedule, original_schedule; cbn; rewrite H, H0; cbn; rewrite H1, H2; reflexivity. Qed.

End Composition.
Print Assumptions syntax_failure_skips_value_finalization.
Print Assumptions both_projections_use_the_same_ordered_items.
Print Assumptions owned_reuses_reverse_source_schedule.
Print Assumptions rejection_stops_before_earlier_source_drains.
Print Assumptions fault_preserves_post_drain_state.
Print Assumptions two_slots_keep_source_indices_and_reverse_callback_order.
End OwnedCollectionAction.
