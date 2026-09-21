(** Shared semantic-action dispatch, without changing action interpretation.

    Source correspondence:
    - ActionEntry keeps its static function pointer and metadata ABI.
      ActionSignature borrows the same ordered input-category slice. Lists
      here observe slice contents; this is not a Rust lifetime/ownership proof.
    - WpdaEngine::action_signature projects action_for by default. The default
      execute_action invokes that entry's original function, or reports the
      explicit MissingAction(category, rule) error.
    - SemanticBuilder::invoke_action_with checks arity and creates the existing
      collection frame before invoking one callback on the same ordered args.
      Frame failure is checked first, then the callback's returned error, then
      the existing open-state/result-count/result-kind checks. A provisional
      result cannot turn either kind of failure into semantic rejection.
    - invoke_selected_action_with retains the existing selected-collection and
      optional-group normalization. It is a supplied operation below, not a
      replacement implementation. OccurrenceCollectionAssembly.v and
      SelectedOccurrencePlan.v own its indexing/order/assembly obligations.

    The returned observation records callback invocations as argument lists:
    [] means validation failed before dispatch; [args] means one invocation.
    The static wrapper proof compares this trace as well as all three result
    cases (term, partial-action rejection, error). Contextual callbacks are
    equivalent when they implement the same behavior on the actual frame and
    arguments; no axiom identifies different callback implementations.

    RealizationFailureBoundary.finish_partial_action is reused for frame
    completion, including permitted unused slots on semantic rejection. Its
    atomic-publication theorem is reused for walker error propagation. Caller
    routing through all execution sites, exact Rust error constructors, and
    unchanged collection normalization require source-correspondence tests.
    No ranking, parser algorithm, grammar completeness, allocator, or full
    runtime-parser correctness theorem is asserted by this adapter model.
*)
From Stdlib Require Import List Arith Bool.
From PrattailWpdaRuntime Require Import RealizationFailureBoundary.
Import ListNotations.
Set Implicit Arguments.

Module ActionDispatchAdapter.

Record ActionSignature := {
  action_arity : nat;
  expected_input_categories : list nat;
  output_category : nat
}.

Section Dispatch.
Context {Arg Value Fault Collection SelectedArg : Type}.

(** Fault values are the existing ActionInvocationError values. Named
    operations below select their exact source-specific payloads; they do not
    erase faults to booleans or semantic None. The undrained value represents
    the existing frame's first undrained slot for this invocation. *)
Record FailureKinds := {
  arity_fault : nat -> nat -> Fault;
  undrained_fault : Fault;
  open_state_fault : Fault;
  result_count_fault : nat -> Fault;
  nonterm_fault : nat -> Fault;
  missing_action_fault : nat -> nat -> Fault
}.

Inductive StackResult := TermResult (value : Value) | NonTermResult (kind : nat).
Record BuilderState := {
  frame_failure : option Fault;
  frame_complete : bool;
  open_parser_state : bool;
  results : list StackResult
}.
Record CallbackExecution := {
  after_callback : BuilderState;
  returned_fault : option Fault
}.
Definition Callback := BuilderState -> list Arg -> CallbackExecution.

Record ActionEntry := {
  entry_arity : nat;
  entry_input_categories : list nat;
  entry_output_category : nat;
  entry_action : BuilderState -> list Arg -> BuilderState
}.

Definition signature_of entry :=
  {| action_arity := entry_arity entry;
     expected_input_categories := entry_input_categories entry;
     output_category := entry_output_category entry |}.

Theorem signature_projection_preserves_all_metadata : forall entry,
  action_arity (signature_of entry) = entry_arity entry /\
  expected_input_categories (signature_of entry) = entry_input_categories entry /\
  output_category (signature_of entry) = entry_output_category entry.
Proof. intros; repeat split; reflexivity. Qed.

Theorem signature_preserves_each_input_position : forall entry index,
  nth_error (expected_input_categories (signature_of entry)) index =
  nth_error (entry_input_categories entry) index.
Proof. reflexivity. Qed.

Definition signature_for (lookup : nat -> nat -> option ActionEntry) category rule :=
  option_map signature_of (lookup category rule).

Theorem absent_metadata_remains_absent : forall lookup category rule,
  lookup category rule = None -> signature_for lookup category rule = None.
Proof. intros; unfold signature_for; rewrite H; reflexivity. Qed.

Theorem present_metadata_is_exact_projection : forall lookup category rule entry,
  lookup category rule = Some entry ->
  signature_for lookup category rule = Some (signature_of entry).
Proof. intros; unfold signature_for; rewrite H; reflexivity. Qed.

Definition lift_static (action : BuilderState -> list Arg -> BuilderState) : Callback :=
  fun builder args => {| after_callback := action builder args; returned_fault := None |}.

Definition execute_default faults (lookup : nat -> nat -> option ActionEntry)
    category rule builder args : CallbackExecution :=
  match lookup category rule with
  | Some entry => lift_static (entry_action entry) builder args
  | None => {| after_callback := builder;
               returned_fault := Some (missing_action_fault faults category rule) |}
  end.

Theorem default_execution_uses_original_action : forall faults lookup category rule entry builder args,
  lookup category rule = Some entry ->
  execute_default faults lookup category rule builder args =
    lift_static (entry_action entry) builder args.
Proof. intros; unfold execute_default; rewrite H; reflexivity. Qed.

Theorem missing_execution_is_explicit_error : forall faults lookup category rule builder args,
  lookup category rule = None ->
  after_callback (execute_default faults lookup category rule builder args) = builder /\
  returned_fault (execute_default faults lookup category rule builder args) =
    Some (missing_action_fault faults category rule).
Proof. intros; unfold execute_default; rewrite H; split; reflexivity. Qed.

Definition frame_result faults builder : Fault + option unit :=
  @finish_partial_action unit Fault (undrained_fault faults)
    (frame_failure builder) (frame_complete builder)
    (match results builder with [] => None | _ => Some tt end).

Definition classify_results faults builder : Fault + option Value :=
  if open_parser_state builder then inl (open_state_fault faults)
  else match results builder with
       | [] => inr None
       | [TermResult value] => inr (Some value)
       | [NonTermResult kind] => inl (nonterm_fault faults kind)
       | values => inl (result_count_fault faults (length values))
       end.

(** Transcription of the old unit-returning static invocation boundary. *)
Definition finish_static faults builder : Fault + option Value :=
  match frame_result faults builder with
  | inl fault => inl fault
  | inr _ => classify_results faults builder
  end.

(** The only added decision: a callback's explicit Err is checked after the
    unchanged frame protocol boundary and before publishing any result. *)
Definition finish_with faults execution : Fault + option Value :=
  match frame_result faults (after_callback execution) with
  | inl fault => inl fault
  | inr _ => match returned_fault execution with
             | Some fault => inl fault
             | None => classify_results faults (after_callback execution)
             end
  end.

Theorem lifted_static_finish_is_identical : forall faults action builder args,
  finish_with faults (lift_static action builder args) =
    finish_static faults (action builder args).
Proof. intros; unfold finish_with, lift_static, finish_static; reflexivity. Qed.

Theorem sticky_frame_fault_dominates_callback_fault_and_results : forall faults execution fault,
  frame_failure (after_callback execution) = Some fault ->
  finish_with faults execution = inl fault.
Proof.
  intros faults execution fault H. unfold finish_with, frame_result.
  rewrite H. reflexivity.
Qed.

Theorem callback_fault_survives_valid_frame : forall faults execution fault complete,
  frame_result faults (after_callback execution) = inr complete ->
  returned_fault execution = Some fault -> finish_with faults execution = inl fault.
Proof. intros; unfold finish_with; rewrite H, H0; reflexivity. Qed.

Theorem callback_failure_never_publishes_a_provisional_result : forall faults execution fault,
  returned_fault execution = Some fault ->
  exists actual_fault, finish_with faults execution = inl actual_fault.
Proof.
  intros faults execution fault H. unfold finish_with.
  destruct (frame_result faults (after_callback execution)) as [protocol|complete].
  - exists protocol; reflexivity.
  - rewrite H. exists fault; reflexivity.
Qed.

Corollary callback_failure_is_not_semantic_rejection : forall faults execution fault,
  returned_fault execution = Some fault -> finish_with faults execution <> inr None.
Proof.
  intros faults execution fault H.
  destruct (callback_failure_never_publishes_a_provisional_result faults execution H)
    as [actual Hactual]. rewrite Hactual; discriminate.
Qed.

Theorem successful_result_requires_completed_clean_frame : forall faults execution value,
  finish_with faults execution = inr (Some value) ->
  returned_fault execution = None /\
  frame_failure (after_callback execution) = None /\
  frame_complete (after_callback execution) = true /\
  open_parser_state (after_callback execution) = false /\
  results (after_callback execution) = [TermResult value].
Proof.
  intros faults [builder callback_fault] value H.
  destruct builder as [protocol complete opened produced].
  unfold finish_with, frame_result, classify_results in H; cbn in H.
  destruct protocol; cbn in H; try discriminate.
  destruct produced as [|first rest]; cbn in H.
  - destruct callback_fault; destruct opened; discriminate.
  - destruct complete; cbn in H; try discriminate.
    destruct callback_fault; cbn in H; try discriminate.
    destruct opened; cbn in H; try discriminate.
    destruct first; destruct rest as [|second rest]; cbn in H; try discriminate.
    inversion H; subst. repeat split; reflexivity.
Qed.

Theorem empty_partial_action_still_rejects_without_drain : forall faults complete,
  finish_with faults
    {| after_callback := {| frame_failure := None; frame_complete := complete;
         open_parser_state := false; results := [] |}; returned_fault := None |} = inr None.
Proof. reflexivity. Qed.

Record InvocationObservation := {
  observed_result : Fault + option Value;
  callback_arguments : list (list Arg)
}.
Definition refused_before_callback fault : InvocationObservation :=
  {| observed_result := inl fault; callback_arguments := [] |}.

Definition invoke_with faults signature
    (prepare : list Collection -> Fault + BuilderState) (callback : Callback)
    (args : list Arg) (collections : list Collection) : InvocationObservation :=
  if Nat.eqb (length args) (action_arity signature) then
    match prepare collections with
    | inl fault => refused_before_callback fault
    | inr builder =>
        {| observed_result := finish_with faults (callback builder args);
           callback_arguments := [args] |}
    end
  else refused_before_callback (arity_fault faults (action_arity signature) (length args)).

Definition invoke_static faults entry
    (prepare : list Collection -> Fault + BuilderState)
    (args : list Arg) (collections : list Collection) : InvocationObservation :=
  if Nat.eqb (length args) (entry_arity entry) then
    match prepare collections with
    | inl fault => refused_before_callback fault
    | inr builder =>
        {| observed_result := finish_static faults (entry_action entry builder args);
           callback_arguments := [args] |}
    end
  else refused_before_callback (arity_fault faults (entry_arity entry) (length args)).

Theorem static_wrapper_is_observationally_identical : forall faults entry prepare args collections,
  invoke_with faults (signature_of entry) prepare (lift_static (entry_action entry)) args collections =
    invoke_static faults entry prepare args collections.
Proof.
  intros. unfold invoke_with, invoke_static, signature_of; cbn.
  destruct (Nat.eqb (length args) (entry_arity entry)); [|reflexivity].
  destruct (prepare collections); [reflexivity|].
  rewrite lifted_static_finish_is_identical. reflexivity.
Qed.

Theorem callback_receives_same_ordered_arguments_once : forall faults signature prepare callback args collections builder,
  length args = action_arity signature -> prepare collections = inr builder ->
  callback_arguments (invoke_with faults signature prepare callback args collections) = [args].
Proof. intros; unfold invoke_with; rewrite H, Nat.eqb_refl, H0; reflexivity. Qed.

Theorem arity_error_invokes_no_callback : forall faults signature prepare callback args collections,
  length args <> action_arity signature ->
  callback_arguments (invoke_with faults signature prepare callback args collections) = [].
Proof.
  intros. unfold invoke_with. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Theorem callback_behavior_substitution : forall faults signature prepare left right args collections,
  (forall builder ordered_args, left builder ordered_args = right builder ordered_args) ->
  invoke_with faults signature prepare left args collections =
    invoke_with faults signature prepare right args collections.
Proof.
  intros. unfold invoke_with.
  destruct (Nat.eqb (length args) (action_arity signature)); [|reflexivity].
  destruct (prepare collections); [reflexivity|]. rewrite H. reflexivity.
Qed.

(** Normalization is exactly the pre-existing selected-collection operation.
    Both entry points do the same outer arity check, normalization, and inner
    arity/frame checks; normalization faults return before invoking callbacks. *)
Definition invoke_selected_with faults signature
    (normalize : list SelectedArg -> Fault + (list Arg * list Collection)) prepare callback
    (selected : list SelectedArg) : InvocationObservation :=
  if Nat.eqb (length selected) (action_arity signature) then
    match normalize selected with
    | inl fault => refused_before_callback fault
    | inr (args, collections) => invoke_with faults signature prepare callback args collections
    end
  else refused_before_callback (arity_fault faults (action_arity signature) (length selected)).

Definition invoke_selected_static faults entry
    (normalize : list SelectedArg -> Fault + (list Arg * list Collection)) prepare
    (selected : list SelectedArg) : InvocationObservation :=
  if Nat.eqb (length selected) (entry_arity entry) then
    match normalize selected with
    | inl fault => refused_before_callback fault
    | inr (args, collections) => invoke_static faults entry prepare args collections
    end
  else refused_before_callback (arity_fault faults (entry_arity entry) (length selected)).

Theorem selected_static_wrapper_preserves_all_outcomes : forall faults entry normalize prepare selected,
  invoke_selected_with faults (signature_of entry) normalize prepare
    (lift_static (entry_action entry)) selected =
  invoke_selected_static faults entry normalize prepare selected.
Proof.
  intros. unfold invoke_selected_with, invoke_selected_static, signature_of; cbn.
  destruct (Nat.eqb (length selected) (entry_arity entry)); [|reflexivity].
  destruct (normalize selected) as [fault|[args collections]]; [reflexivity|].
  apply static_wrapper_is_observationally_identical.
Qed.

Theorem selected_callback_behavior_substitution : forall faults signature normalize prepare left right selected,
  (forall builder ordered_args, left builder ordered_args = right builder ordered_args) ->
  invoke_selected_with faults signature normalize prepare left selected =
    invoke_selected_with faults signature normalize prepare right selected.
Proof.
  intros. unfold invoke_selected_with.
  destruct (Nat.eqb (length selected) (action_arity signature)); [|reflexivity].
  destruct (normalize selected) as [fault|[args collections]]; [reflexivity|].
  apply callback_behavior_substitution; exact H.
Qed.

Corollary owned_and_borrowed_contexts_are_observationally_equivalent :
  forall (Owned Borrowed : Type) faults signature normalize prepare
    (run_owned : Owned -> Callback) (run_borrowed : Borrowed -> Callback)
    owned borrowed selected,
  (forall builder ordered_args,
    run_owned owned builder ordered_args = run_borrowed borrowed builder ordered_args) ->
  invoke_selected_with faults signature normalize prepare (run_owned owned) selected =
    invoke_selected_with faults signature normalize prepare (run_borrowed borrowed) selected.
Proof. intros; apply selected_callback_behavior_substitution; exact H. Qed.

(** Caller error propagation is the existing atomic publication boundary.
    ReconstructionFailure models the Rust RealizationError::Action { rule,
    cause } wrapper at this boundary, retaining the exact dispatch cause.
    The caller must record the dispatch error as ReconstructionFailure; this
    theorem does not silently assume that all Rust callers already do so. *)
Theorem recorded_callback_error_discards_all_provisional_terms :
  forall (state : @request_state Value unit Fault) events fault,
  first_failure state = None ->
  publish (run events (observe state (Failed (ReconstructionFailure fault)))) =
    inl (ReconstructionFailure fault).
Proof.
  intros state events fault H. apply failure_publishes_no_candidate_prefix.
  cbn. unfold remember_failure. rewrite H. reflexivity.
Qed.

End Dispatch.

Print Assumptions signature_projection_preserves_all_metadata.
Print Assumptions default_execution_uses_original_action.
Print Assumptions missing_execution_is_explicit_error.
Print Assumptions static_wrapper_is_observationally_identical.
Print Assumptions selected_static_wrapper_preserves_all_outcomes.
Print Assumptions owned_and_borrowed_contexts_are_observationally_equivalent.
Print Assumptions callback_failure_never_publishes_a_provisional_result.
Print Assumptions recorded_callback_error_discards_all_provisional_terms.
End ActionDispatchAdapter.
