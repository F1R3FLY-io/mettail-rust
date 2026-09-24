(** Result refinement for the ORIGINAL FIRST, Ident and prefix workers.

    This is a callback-interface proof, NOT another FIRST/bucket algorithm.
    OriginalFirstSetProjection, OriginalIdentSummaryProjection and
    OriginalPrefixBucketDriverProjection remain the source/algorithm laws.
    Rust retains one copy of each loop; legacy wrappers supply Infallible
    callbacks, while Try contexts propagate the first error at its call site.

    A finite callback program includes the exact original continuation after
    each response. Its request retains arguments/occurrence identity; responses
    are dependent on that request. In particular Ok None can select an existing
    fallback, but Err never evaluates that continuation. Read-only context
    observations are requests too. Reader observations outside these contexts
    and pure operations belong to the unchanged continuation.

    CORRESPONDENCE OBLIGATION: the Rust worker must realize this program in the
    original observation order, including short circuits, nested helper calls,
    duplicate classifications and deferred publication. This generic theorem
    does not establish that obligation by itself. Exact source review, original
    macro differentials and failure injection at every reached callback close
    the interface evidence. The old models do not record every newly fallible
    read-only observation: their traces are appropriate projections, not an
    asserted identity with this complete context-call trace.

    Callback state after a failed call is retained; no rollback of arbitrary
    effects is promised. Partial worker output is private and not published.
    Fuel is proof instrumentation only, not a new runtime rule/count limit.
    Inner mathematical recursion does not prescribe recursive Rust code.
    Allocation, panic recovery, formatter keys, semantic FIRST completeness,
    owned-context instantiation and runtime-parser cutover are outside scope.
*)
From Stdlib Require Import List.
From PrattailWpdaRuntime Require Import OriginalFirstSetProjection
  OriginalIdentSummaryProjection OriginalPrefixBucketDriverProjection.
Import ListNotations.
Set Implicit Arguments.

Module PrefixCallbackFailure.
Module F := OriginalFirstSetProjection.OriginalFirstSetProjection.
Module I := OriginalIdentSummaryProjection.OriginalIdentSummaryProjection.
Module P := OriginalPrefixBucketDriverProjection.OriginalPrefixBucketDriverProjection.

(** Explicit reuse, without restating/reimplementing the three algorithms. *)
Definition reused_first_source_law := @F.finite_first_entry_projection.
Definition reused_ident_source_law := @I.complete_finite_source_substitution.
Definition reused_prefix_source_law := @P.complete_original_driver_source_projection.

(** Exact public context method taxonomy. Arguments and result types belong to
    the Request/Response family below, rather than lossy strings or tags. *)
Inductive CallbackKind :=
| RulesLen | RuleAt | FindCategory | IsData | CollectionOpen | LegacyFirst
| NativeFirst | Atomic | PatternedFirst | BinderLeading | PredicateParts
| CategoriesLen | CategoryAt | CategorySpelling | LegacyLen | LegacyAt
| Infix | CategoryNames | BindingPowerTable | ExplicitPrefixBp
| BinderShape | AtomicRows | NestedGuestOpeners.

Section Interface.
Context {Request : Type} (kind : Request -> CallbackKind).
Context (Response : Request -> Type) (State Error Value : Type).

Inductive Program : Type :=
| Return (value : Value)
| Call (request : Request) (next : Response request -> Program).

Arguments Call request next : clear implicits.

Definition Handler := forall request, State -> (Response request + Error) * State.
Definition PlainHandler := forall request, State -> Response request * State.

Inductive Outcome :=
| Complete (value : Value) (state : State) (trace : list Request)
| Failed (error : Error) (state : State) (trace : list Request)
| Interrupted (state : State) (trace : list Request).

Definition prepend request outcome := match outcome with
| Complete value state trace => Complete value state (request :: trace)
| Failed error state trace => Failed error state (request :: trace)
| Interrupted state trace => Interrupted state (request :: trace)
end.

Fixpoint run fuel (handler : Handler) program state : Outcome :=
  match fuel with
  | O => Interrupted state []
  | S remaining => match program with
    | Return value => Complete value state []
    | Call request next =>
      let '(answer, after) := handler request state in
      match answer with
      | inl value => prepend request (run remaining handler (next value) after)
      | inr error => Failed error after [request]
      end
    end
  end.

Fixpoint plain_run fuel (handler : PlainHandler) program state : Outcome :=
  match fuel with
  | O => Interrupted state []
  | S remaining => match program with
    | Return value => Complete value state []
    | Call request next =>
      let '(value, after) := handler request state in
      prepend request (plain_run remaining handler (next value) after)
    end
  end.

Definition all_ok (handler : PlainHandler) : Handler :=
  fun request state => let '(value, after) := handler request state in
                      (inl value, after).

Theorem all_ok_exact_original : forall fuel handler program state,
  run fuel (all_ok handler) program state = plain_run fuel handler program state.
Proof.
  induction fuel as [|fuel IH]; intros handler program state; [reflexivity|].
  destruct program as [value|request next]; cbn; [reflexivity|].
  unfold all_ok. destruct (handler request state) as [value after].
  cbn. unfold all_ok in IH. rewrite IH. reflexivity.
Qed.

(** This relation records EVERY attempted call, with successful replies before
    the final failed reply. There is no constructor that continues after Err. *)
Inductive Rejects (handler : Handler) : Program -> State -> Error -> State -> list Request -> Prop :=
| RejectHere : forall request next state error after,
    handler request state = (inr error, after) ->
    Rejects handler (Call request next) state error after [request]
| RejectLater : forall request next state value after error final trace,
    handler request state = (inl value, after) ->
    Rejects handler (next value) after error final trace ->
    Rejects handler (Call request next) state error final (request :: trace).

Theorem failed_run_has_exact_first_failure : forall fuel handler program state error final trace,
  run fuel handler program state = Failed error final trace ->
  Rejects handler program state error final trace.
Proof.
  induction fuel as [|fuel IH]; intros handler program state error final trace H;
    [discriminate|].
  destruct program as [value|request next]; cbn in H; [discriminate|].
  destruct (handler request state) as [[value|failure] after] eqn:Hcall.
  - destruct (run fuel handler (next value) after) as
      [result last calls|failure last calls|last calls] eqn:Hrun;
      cbn in H; try discriminate.
    inversion H; subst. eapply RejectLater; [exact Hcall|].
    eapply IH; exact Hrun.
  - inversion H; subst. apply RejectHere. exact Hcall.
Qed.

Theorem first_error_skips_any_continuation : forall fuel handler request next state error after,
  handler request state = (inr error, after) ->
  run (S fuel) handler (Call request next) state = Failed error after [request].
Proof. intros. cbn. rewrite H. reflexivity. Qed.

Theorem failed_continuation_irrelevant : forall fuel handler request left right state error after,
  handler request state = (inr error, after) ->
  run (S fuel) handler (Call request left) state =
  run (S fuel) handler (Call request right) state.
Proof. intros. cbn. rewrite H. reflexivity. Qed.

Definition published outcome := match outcome with
| Complete value _ _ => Some value
| Failed _ _ _ | Interrupted _ _ => None
end.

Lemma failure_has_no_partial_output : forall error state trace,
  published (Failed error state trace) = None.
Proof. reflexivity. Qed.
Lemma exhaustion_is_not_successful_empty : forall state trace,
  published (Interrupted state trace) = None.
Proof. reflexivity. Qed.

(** Response-sensitive continuation equality: the same next observations occur
    for each answer, without choosing or manufacturing an answer on failure. *)
Inductive Related : Program -> Program -> Prop :=
| RelatedReturn : forall value, Related (Return value) (Return value)
| RelatedCall : forall request left right,
    (forall response, Related (left response) (right response)) ->
    Related (Call request left) (Call request right).

Theorem source_program_substitution : forall left right,
  Related left right -> forall fuel handler state,
  run fuel handler left state = run fuel handler right state.
Proof.
  intros left right relation. induction relation as [value|request left right relation IH];
    intros fuel handler state; destruct fuel as [|fuel]; cbn; try reflexivity.
  destruct (handler request state) as [[response|error] after]; cbn; [|reflexivity].
  rewrite IH. reflexivity.
Qed.

Theorem callback_reader_substitution : forall fuel left right program state,
  (forall request before, left request before = right request before) ->
  run fuel left program state = run fuel right program state.
Proof.
  induction fuel as [|fuel IH]; intros left right program state Heq; [reflexivity|].
  destruct program as [value|request next]; cbn; [reflexivity|].
  rewrite Heq. destruct (right request state) as [[response|error] after]; cbn;
    [|reflexivity]. rewrite (IH left right (next response) after Heq). reflexivity.
Qed.

(** All-ok specialization composed with an EXISTING source outcome law.
    The equality premise is the explicitly required worker/program bridge, not
    a theorem manufactured from equal final outputs or a rewritten algorithm. *)
Theorem original_source_law_lifts : forall fuel handler left right state,
  plain_run fuel handler left state = plain_run fuel handler right state ->
  run fuel (all_ok handler) left state = run fuel (all_ok handler) right state.
Proof. intros. rewrite !all_ok_exact_original. exact H. Qed.

Definition callback_trace outcome := match outcome with
| Complete _ _ trace | Failed _ _ trace | Interrupted _ trace => map kind trace
end.

Lemma first_failure_trace_ends_at_failed_call : forall fuel handler request next state error after,
  handler request state = (inr error, after) ->
  callback_trace (run (S fuel) handler (Call request next) state) = [kind request].
Proof. intros. cbn. rewrite H. reflexivity. Qed.

End Interface.

Print Assumptions all_ok_exact_original.
Print Assumptions failed_run_has_exact_first_failure.
Print Assumptions first_error_skips_any_continuation.
Print Assumptions failed_continuation_irrelevant.
Print Assumptions failure_has_no_partial_output.
Print Assumptions exhaustion_is_not_successful_empty.
Print Assumptions source_program_substitution.
Print Assumptions callback_reader_substitution.
Print Assumptions original_source_law_lifts.
Print Assumptions first_failure_trace_ends_at_failed_call.
End PrefixCallbackFailure.
