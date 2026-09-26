(** Borrowed semantic-result category observation, task 8514.

    The existing two walker sites observe the last main-stack argument after
    action execution and result-count checks, before take_dyn_result drains it.
    Today a Term's debug type-name is passed once to cat_of_type_name. The
    proposed hook receives the same term payload by shared borrow and the same
    tag. Its static default ignores the payload and calls the original lookup.

    Source correspondence for the bounded Rust change:
    - SemanticBuilder::top_term, beside top_term_type_name in wpda_runtime.rs,
      must inspect self.stack.back(), not active_arg_stack, and return borrowed
      payload plus the stored tag only for ActionArg::Term. No clone/pop/search.
      The existing top_term_type_name behavior is unchanged.
    - WpdaEngine::term_category, beside cat_of_type_name in wpda_walker.rs,
      defaults to self.cat_of_type_name(type_name), exactly once.
    - finish_packing_term_witness and the realization action-result path replace
      only their output_cat observation, at baseline lines 23060 and 23278.
      Action errors, arity/result-count checks, take_dyn_result, and publication
      stay in their original order. ActionDispatchAdapter.v retains ownership
      of their existing action/normalization/error obligations.

    Lists below model the main stack in push order; their last item is observed.
    Value is a payload identity, not a copy operation. This model does not prove
    Rust lifetimes or allocation behavior. Lookup state records any observable
    effects of the existing type-name lookup, so static equivalence does not
    assume purity. Dynamic carrier indices are observed fields, not inferred
    from debug tags or constructor spelling. The carrier theorem is conditional
    on the actual downcast; it does not assert every payload is a carrier.

    These are observer/adapter laws, not a new parser or semantic-action
    algorithm. TransitionBodyRelocation.v still requires exact source binding
    and callback order. No equality of distinct classifiers is postulated.
*)
From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.

Module TermCategoryObservation.

Section Observation.
Context {Value Name Category State : Type}.

Inductive StackItem :=
| Term (value : Value) (type_name : Name)
| NonTerm.

Definition top_term_view (main_stack : list StackItem) : option (Value * Name) :=
  match hd_error (rev main_stack) with
  | Some (Term value type_name) => Some (value, type_name)
  | _ => None
  end.

(** Independent transcription of the existing type-name-only accessor. *)
Definition original_top_type_name (main_stack : list StackItem) : option Name :=
  match hd_error (rev main_stack) with
  | Some (Term _ type_name) => Some type_name
  | _ => None
  end.

Theorem borrowed_view_preserves_stored_tag : forall main_stack,
  option_map snd (top_term_view main_stack) = original_top_type_name main_stack.
Proof.
  intros. unfold top_term_view, original_top_type_name.
  destruct (hd_error (rev main_stack)) as [item|]; [destruct item|]; reflexivity.
Qed.

Theorem borrowed_view_returns_exact_last_payload : forall main_stack value type_name,
  top_term_view (main_stack ++ [Term value type_name]) = Some (value, type_name).
Proof. intros; unfold top_term_view; rewrite rev_app_distr; reflexivity. Qed.

Theorem nonterm_top_does_not_search_below : forall main_stack,
  top_term_view (main_stack ++ [NonTerm]) = None.
Proof. intros; unfold top_term_view; rewrite rev_app_distr; reflexivity. Qed.

Definition original_observation
    (lookup : Name -> State -> option Category * State) main_stack state :=
  match original_top_type_name main_stack with
  | Some type_name => lookup type_name state
  | None => (None, state)
  end.

Definition observe_with
    (hook : Value -> Name -> State -> option Category * State) main_stack state :=
  match top_term_view main_stack with
  | Some (value, type_name) => hook value type_name state
  | None => (None, state)
  end.

Definition static_default
    (lookup : Name -> State -> option Category * State)
    (_value : Value) type_name state := lookup type_name state.

Theorem static_default_preserves_category_and_lookup_state :
  forall lookup main_stack state,
  observe_with (static_default lookup) main_stack state =
  original_observation lookup main_stack state.
Proof.
  intros. unfold observe_with, static_default, original_observation,
    top_term_view, original_top_type_name.
  destruct (hd_error (rev main_stack)) as [item|]; [destruct item|]; reflexivity.
Qed.

Theorem absent_term_skips_hook : forall hook main_stack state,
  top_term_view main_stack = None ->
  observe_with hook main_stack state = (None, state).
Proof. intros; unfold observe_with; rewrite H; reflexivity. Qed.

Theorem present_term_calls_hook_on_same_payload_and_tag :
  forall hook main_stack value type_name state,
  top_term_view main_stack = Some (value, type_name) ->
  observe_with hook main_stack state = hook value type_name state.
Proof. intros; unfold observe_with; rewrite H; reflexivity. Qed.

Theorem equal_actual_hook_behavior_preserves_observation :
  forall left right main_stack state,
  (forall value type_name observed_state,
    left value type_name observed_state = right value type_name observed_state) ->
  observe_with left main_stack state = observe_with right main_stack state.
Proof.
  intros. unfold observe_with.
  destruct (top_term_view main_stack) as [[value type_name]|]; [apply H|reflexivity].
Qed.

End Observation.

(** The category field models the existing u16 carrier index without performing
    arithmetic or validating an engine's category table. Such table validity is
    a separate owned-engine construction obligation. *)
Record IndexedCarrier (Payload : Type) := {
  carrier_category : nat;
  carrier_payload : Payload
}.

Arguments carrier_category {Payload} _.
Arguments carrier_payload {Payload} _.

Definition carrier_category_hook {Value Name Payload State : Type}
    (downcast : Value -> option (IndexedCarrier Payload))
    (value : Value) (_type_name : Name) (state : State) : option nat * State :=
  (option_map carrier_category (downcast value), state).

Theorem carrier_index_is_observed_exactly :
  forall (Value Name Payload State : Type)
    (downcast : Value -> option (IndexedCarrier Payload))
    value carrier (type_name : Name) (state : State),
  downcast value = Some carrier ->
  carrier_category_hook downcast value type_name state =
    (Some (carrier_category carrier), state).
Proof. intros; unfold carrier_category_hook; rewrite H; reflexivity. Qed.

Theorem carrier_observation_is_independent_of_debug_tag :
  forall (Value Name Payload State : Type)
    (downcast : Value -> option (IndexedCarrier Payload))
    value (left_tag right_tag : Name) (state : State),
  carrier_category_hook downcast value left_tag state =
  carrier_category_hook downcast value right_tag state.
Proof. reflexivity. Qed.

Theorem failed_downcast_does_not_guess_a_category :
  forall (Value Name Payload State : Type)
    (downcast : Value -> option (IndexedCarrier Payload))
    value (type_name : Name) (state : State),
  downcast value = None ->
  carrier_category_hook downcast value type_name state = (None, state).
Proof. intros; unfold carrier_category_hook; rewrite H; reflexivity. Qed.

Print Assumptions borrowed_view_preserves_stored_tag.
Print Assumptions borrowed_view_returns_exact_last_payload.
Print Assumptions nonterm_top_does_not_search_below.
Print Assumptions static_default_preserves_category_and_lookup_state.
Print Assumptions absent_term_skips_hook.
Print Assumptions present_term_calls_hook_on_same_payload_and_tag.
Print Assumptions equal_actual_hook_behavior_preserves_observation.
Print Assumptions carrier_index_is_observed_exactly.
Print Assumptions carrier_observation_is_independent_of_debug_tag.
Print Assumptions failed_downcast_does_not_guess_a_category.

End TermCategoryObservation.
