(** Retain the exact selected publication context before fallible restoration.
    The attempt parameter covers restoration, execution, validation and result
    reflection. Its outcome and final usage are arbitrary, including failure;
    this control refinement neither proves that semantic pipeline nor models
    Rust allocation. Publication delegates to the existing guarded host model.
    The legacy projection theorem checks unchanged typed success/error/usage
    behavior while the richer report also retains context for negative replies. *)
From Stdlib Require Import List.
From RuntimeGrammar Require Import CapabilitySeparation InstalledLanguageAuthority
  GuardedReplyPublication.
Import ListNotations.

Module SemanticPreparationContext.
Module G := GuardedReplyPublication.

Record Selection := selection {
  action : nat;
  input_sort : nat;
  required : list LanguageRight
}.
Record Context := context {
  owner : InstalledHandle;
  rights : list LanguageRight
}.

Section Reports.
Context {Value Error Usage : Type}.
Record Report := report {
  outcome : Value + Error;
  publication : option Context;
  usage : Usage
}.

Definition prepare entry handle denied
    (selected : (Selection + Error) * Usage)
    (attempt : Selection -> Usage -> (Value + Error) * Usage) :=
  let '(choice, prefix) := selected in
  match choice with
  | inr error => report (inr error) None prefix
  | inl s =>
      if G.authorized entry handle (required s) then
        let retained := context handle (required s) in
        let '(result, final) := attempt s prefix in
        report result (Some retained) final
      else report (inr denied) None prefix
  end.

Definition legacy_prepare entry handle denied
    (selected : (Selection + Error) * Usage)
    (attempt : Selection -> Usage -> (Value + Error) * Usage)
    : ((Value * Context) + Error) * Usage :=
  let '(choice, prefix) := selected in
  match choice with
  | inr error => (inr error, prefix)
  | inl s =>
      if G.authorized entry handle (required s) then
        let '(result, final) := attempt s prefix in
        match result with
        | inl value => (inl (value, context handle (required s)), final)
        | inr error => (inr error, final)
        end
      else (inr denied, prefix)
  end.

Definition typed_projection missing r : ((Value * Context) + Error) * Usage :=
  (match outcome r with
   | inr error => inr error
   | inl value => match publication r with
       | Some retained => inl (value, retained)
       | None => inr missing end
   end, usage r).

Theorem existing_typed_outcomes_and_usage_are_preserved :
  forall entry handle denied missing selected attempt,
  typed_projection missing (prepare entry handle denied selected attempt) =
  legacy_prepare entry handle denied selected attempt.
Proof.
  intros entry handle denied missing [[s|error] prefix] attempt; cbn.
  - destruct (G.authorized entry handle (required s)); cbn; [| reflexivity].
    destruct (attempt s prefix) as [[value|error] final]; reflexivity.
  - reflexivity.
Qed.

Theorem every_authorized_outcome_retains_the_same_context_and_final_usage :
  forall entry handle denied s prefix attempt result final,
  G.authorized entry handle (required s) = true ->
  attempt s prefix = (result, final) ->
  prepare entry handle denied (inl s, prefix) attempt =
    report result (Some (context handle (required s))) final.
Proof. intros. unfold prepare. now rewrite H, H0. Qed.

Theorem selection_failure_has_no_publication_context :
  forall entry handle denied error prefix attempt,
  prepare entry handle denied (inr error, prefix) attempt =
    report (inr error) None prefix.
Proof. reflexivity. Qed.

Theorem incomplete_authorization_has_no_publication_context :
  forall entry handle denied s prefix attempt,
  G.authorized entry handle (required s) = false ->
  prepare entry handle denied (inl s, prefix) attempt =
    report (inr denied) None prefix.
Proof. intros. unfold prepare. now rewrite H. Qed.

Definition publish r entry state mutation events :=
  match publication r with
  | None => None
  | Some c => G.run (owner c) (rights c) mutation events (G.initial entry state)
  end.

Theorem retained_authority_is_independent_of_success_or_failure :
  forall result final c entry state mutation events,
  publish (report result (Some c) final) entry state mutation events =
  G.run (owner c) (rights c) mutation events (G.initial entry state).
Proof. reflexivity. Qed.

Theorem missing_context_cannot_invoke_the_host :
  forall result final entry state mutation events,
  publish (report result None final) entry state mutation events = None.
Proof. reflexivity. Qed.

Theorem late_revocation_refuses_every_retained_outcome :
  forall result final c entry state mutation,
  publish (report result (Some c) final) entry state mutation
    [G.RevokeAuthority; G.AcquireAuthority] =
  Some {| G.phase := G.Refused; G.authority := revoke entry;
          G.host := state; G.mutation_count := 0 |}.
Proof. intros. apply G.revoke_before_guard_refuses_even_a_prepared_reply. Qed.

Theorem every_retained_outcome_uses_live_full_rights :
  forall result final c entry state mutation,
  G.authorized entry (owner c) (rights c) = true ->
  publish (report result (Some c) final) entry state mutation G.publication_events =
  Some {| G.phase := G.ReceiverInvoked; G.authority := entry;
          G.host := mutation state; G.mutation_count := 1 |}.
Proof. intros. now apply G.authorized_publication_applies_exactly_the_supplied_mutation. Qed.

End Reports.
End SemanticPreparationContext.

Print Assumptions SemanticPreparationContext.existing_typed_outcomes_and_usage_are_preserved.
Print Assumptions SemanticPreparationContext.every_authorized_outcome_retains_the_same_context_and_final_usage.
Print Assumptions SemanticPreparationContext.selection_failure_has_no_publication_context.
Print Assumptions SemanticPreparationContext.incomplete_authorization_has_no_publication_context.
Print Assumptions SemanticPreparationContext.retained_authority_is_independent_of_success_or_failure.
Print Assumptions SemanticPreparationContext.missing_context_cannot_invoke_the_host.
Print Assumptions SemanticPreparationContext.late_revocation_refuses_every_retained_outcome.
Print Assumptions SemanticPreparationContext.every_retained_outcome_uses_live_full_rights.
