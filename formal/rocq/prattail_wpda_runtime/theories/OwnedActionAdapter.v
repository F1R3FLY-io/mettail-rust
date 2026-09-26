(** Owned semantic payload adapter, task 8514.

    Source correspondence is restricted to the original runtime.rs
    ForestBuilder::apply_rule Reduce arm: project ordered semantic inputs,
    then ordered syntax inputs, apply ReductionPlan to values, apply it to
    syntax, and only then invoke the declared native evaluator on the SAME
    semantic inputs and supplied span. The owned adapter does not call the
    recognizer or interpret RuntimeRule tables. apply, wrap_term, and native
    below denote those existing workers, not alternative evaluators.

    ReductionPlan::apply is pure. Native/decoder state is explicit: preserving
    outcomes includes the state returned by the single callback, without any
    assumption that a host is pure. Trace events name actual observation sites.
    Rust correspondence must preserve their arguments and early-error order.

    The carrier adds an admitted u16 category and checked SourceSpan supplied
    by the caller; this model does not invent span recovery from ActionArg.
    Input shape routing, category admission, collection normalization, and
    source-span reconstruction remain caller obligations. TermCategoryObservation
    owns the borrowed category hook. ActionDispatchAdapter owns callback/frame
    failure ordering and atomic publication at the existing walker boundary.
*)
From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope type_scope.

Module OwnedActionAdapter.
Section Adapter.
Context {Payload Term Fault Category Span Capture State Token Text : Type}.

Record Pair := { syntax_payload : Payload; value_payload : Payload }.
Record Carrier := {
  category : Category;
  span : Span;
  payload : Pair
}.

Inductive Event :=
| ApplyValues (inputs : list Payload)
| ApplySyntax (inputs : list Payload)
| InvokeNative (inputs : list Payload)
| Decode (token : Token) (text : Text).

Definition Observation := (Fault + Pair) * (list Event * State).
Definition OwnedObservation := (Fault + Carrier) * (list Event * State).

Definition original_reduce
    (apply : list Payload -> list Capture -> Span -> Fault + Term)
    (wrap_term : Term -> Payload)
    (native : option (list Payload -> Span -> State -> (Fault + Payload) * State))
    (inputs : list Pair) captures source_span state : Observation :=
  let values := map value_payload inputs in
  let syntax := map syntax_payload inputs in
  match apply values captures source_span with
  | inl fault => (inl fault, ([ApplyValues values], state))
  | inr value_term =>
    match apply syntax captures source_span with
    | inl fault => (inl fault, ([ApplyValues values; ApplySyntax syntax], state))
    | inr syntax_term =>
      match native with
      | None =>
          (inr {| syntax_payload := wrap_term syntax_term;
                  value_payload := wrap_term value_term |},
           ([ApplyValues values; ApplySyntax syntax], state))
      | Some evaluate =>
          let '(result, next) := evaluate values source_span state in
          (match result with
           | inl fault => inl fault
           | inr value => inr {| syntax_payload := wrap_term syntax_term;
                                value_payload := value |}
           end,
           ([ApplyValues values; ApplySyntax syntax; InvokeNative values], next))
      end
    end
  end.

Definition attach category source_span (observation : Observation) : OwnedObservation :=
  let '(result, history) := observation in
  (match result with
   | inl fault => inl fault
   | inr payload_pair => inr {| category := category; span := source_span; payload := payload_pair |}
   end, history).

Definition erase (observation : OwnedObservation) : Observation :=
  let '(result, history) := observation in
  (match result with inl fault => inl fault | inr carrier => inr (payload carrier) end,
   history).

Theorem attachment_preserves_payload_fault_trace_and_state : forall cat source_span observation,
  erase (attach cat source_span observation) = observation.
Proof. intros cat source_span [[fault|payload_pair] history]; reflexivity. Qed.

Definition owned_reduce apply wrap_term native cat inputs captures source_span state :=
  attach cat source_span (original_reduce apply wrap_term native inputs captures source_span state).

Theorem owned_reduction_calls_the_original_composition : forall apply wrap_term native cat inputs captures source_span state,
  erase (owned_reduce apply wrap_term native cat inputs captures source_span state) =
  original_reduce apply wrap_term native inputs captures source_span state.
Proof. intros; apply attachment_preserves_payload_fault_trace_and_state. Qed.

Theorem argument_projection_preserves_each_position : forall inputs index payload_pair,
  nth_error inputs index = Some payload_pair ->
  nth_error (map value_payload inputs) index = Some (value_payload payload_pair) /\
  nth_error (map syntax_payload inputs) index = Some (syntax_payload payload_pair).
Proof. intros; rewrite !nth_error_map, H; split; reflexivity. Qed.

Theorem first_apply_failure_skips_syntax_and_native : forall apply wrap_term native inputs captures source_span state fault,
  apply (map value_payload inputs) captures source_span = inl fault ->
  original_reduce apply wrap_term native inputs captures source_span state =
    (inl fault, ([ApplyValues (map value_payload inputs)], state)).
Proof. intros; unfold original_reduce; rewrite H; reflexivity. Qed.

Theorem second_apply_failure_skips_native : forall apply wrap_term native inputs captures source_span state value_term fault,
  apply (map value_payload inputs) captures source_span = inr value_term ->
  apply (map syntax_payload inputs) captures source_span = inl fault ->
  original_reduce apply wrap_term native inputs captures source_span state =
    (inl fault, ([ApplyValues (map value_payload inputs); ApplySyntax (map syntax_payload inputs)], state)).
Proof. intros; unfold original_reduce; rewrite H, H0; reflexivity. Qed.

Theorem native_receives_values_once_after_both_applications : forall apply wrap_term evaluate inputs captures source_span state value_term syntax_term result next,
  apply (map value_payload inputs) captures source_span = inr value_term ->
  apply (map syntax_payload inputs) captures source_span = inr syntax_term ->
  evaluate (map value_payload inputs) source_span state = (result, next) ->
  snd (original_reduce apply wrap_term (Some evaluate) inputs captures source_span state) =
    ([ApplyValues (map value_payload inputs); ApplySyntax (map syntax_payload inputs);
      InvokeNative (map value_payload inputs)], next).
Proof. intros; unfold original_reduce; rewrite H, H0, H1; reflexivity. Qed.

Theorem failure_remains_failure_with_no_carrier : forall cat source_span fault history,
  attach cat source_span (inl fault, history) = (inl fault, history).
Proof. reflexivity. Qed.

Definition decoded_token
    (decode : Token -> Text -> State -> (Fault + Payload) * State)
    cat source_span token text state : OwnedObservation :=
  let '(result, next) := decode token text state in
  attach cat source_span
    (match result with
     | inl fault => inl fault
     | inr value => inr {| syntax_payload := value; value_payload := value |}
     end, ([Decode token text], next)).

Theorem successful_decode_is_one_call_and_both_projections : forall decode cat source_span token text state value next,
  decode token text state = (inr value, next) ->
  decoded_token decode cat source_span token text state =
    (inr {| category := cat; span := source_span;
            payload := {| syntax_payload := value; value_payload := value |} |},
     ([Decode token text], next)).
Proof. intros; unfold decoded_token; rewrite H; reflexivity. Qed.

Theorem decoder_failure_is_not_rejection : forall decode cat source_span token text state fault next,
  decode token text state = (inl fault, next) ->
  decoded_token decode cat source_span token text state =
    (inl fault, ([Decode token text], next)).
Proof. intros; unfold decoded_token; rewrite H; reflexivity. Qed.

Definition structural_hole cat source_span hole_value state : OwnedObservation :=
  (inr {| category := cat; span := source_span;
          payload := {| syntax_payload := hole_value; value_payload := hole_value |} |},
   ([], state)).

Theorem structural_hole_never_invokes_text_decoder : forall cat source_span hole_value state,
  snd (structural_hole cat source_span hole_value state) = ([], state).
Proof. reflexivity. Qed.

End Adapter.

Print Assumptions attachment_preserves_payload_fault_trace_and_state.
Print Assumptions owned_reduction_calls_the_original_composition.
Print Assumptions argument_projection_preserves_each_position.
Print Assumptions first_apply_failure_skips_syntax_and_native.
Print Assumptions second_apply_failure_skips_native.
Print Assumptions native_receives_values_once_after_both_applications.
Print Assumptions failure_remains_failure_with_no_carrier.
Print Assumptions successful_decode_is_one_call_and_both_projections.
Print Assumptions decoder_failure_is_not_rejection.
Print Assumptions structural_hole_never_invokes_text_decoder.
End OwnedActionAdapter.
