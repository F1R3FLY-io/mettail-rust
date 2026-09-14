(** Original enclosing-category comparison, including Map constructor fields.
    Existing constructor certificates and actual task-batch execution are
    composed here. Distinct live scheduled owners come from construction,
    not from semantic certificates. The source remains the original bound
    arm, typed Map callback and by-value discard interpretation. No new
    executor, non-Map restriction, result or parked-frame oracle is added.
    Rust census/selector and move correspondence remain the scoped source
    audit boundary; this theorem concerns successful completed source traces,
    not the existence or resource success of every execution. *)
From Stdlib Require Import List.
From RhoBridge Require Import GeneratedMapSourceComparison GeneratedMapCategoryProjection
  GeneratedCategorySourceAssociation GeneratedMapProjectedTasks GeneratedMapOwnerTraversal
  GeneratedMapSourceOwnership GeneratedSourceRowComparison
  GeneratedConstructorSourceProjection GeneratedConstructorComparisonClasses.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.
Import GeneratedMapProjectedTasks.GeneratedMapProjectedTasks.
Import GeneratedMapCategoryProjection.GeneratedMapCategoryProjection.
Import GeneratedMapSourceComparison.GeneratedMapSourceComparison.
Import GeneratedCategorySourceAssociation.GeneratedCategorySourceAssociation.
Import GeneratedChildTraversal.GeneratedChildTraversal.

Module GeneratedMapCategoryComparison.
Section OriginalCategoryExecution.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variables maximum owner_ceiling : nat.
Variable category_callback : Cat -> nat.
Variables uid_digest binder_digest : nat -> nat.
Local Notation Position := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Variable signature : Cat -> list (@Row Cat).
Variable observe : forall category, Term category -> SourceObservation signature Term category.
Variable alias : forall category, Term category -> Term category -> bool.
Variable category_eq_dec : forall lhs rhs : Cat, {lhs = rhs} + {lhs <> rhs}.
Hypothesis original_alias_identity : forall category lhs rhs,
  alias category lhs rhs = true -> lhs = rhs.
Hypothesis ORDINALS : signature_ordinals_ordered signature.
Local Notation Cells := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation Make := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.make_map_box
  Cat Term maximum owner_ceiling category_callback).
Local Notation Binding := (@CategoryArmBinding Cat signature Term Cells uid_digest binder_digest observe lookup Make).
Local Notation OriginalArm := (@GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.arm_source
  Cat Term maximum owner_ceiling category_callback uid_digest binder_digest lookup signature observe).
Local Notation OriginalCore := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.core_source
  Cat Term maximum alias category_callback lookup).
Local Notation OriginalDiscard := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.discard_source Cat Term).
Local Notation Trace := (@ChildTraversal Cells OriginalArm OriginalCore OriginalDiscard).
Local Notation View := (source_view signature Term uid_digest binder_digest observe).

Section OneHeightStep.
Variable height : nat.
Local Notation children := (category_order signature height).
Local Notation next := (fun category child => View height category child).
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  View height category left = Some left_key -> View height category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = key_compare signature height category left_key right_key.

Theorem the_original_bound_handler_factors_at_the_enclosing_category :
  forall category position left right before exit events after,
  Binding category position left right before exit events after ->
  forall left_key right_key,
  View (S height) category left = Some left_key -> View (S height) category right = Some right_key ->
  match exit with
  | Signalled result => result = key_compare signature (S height) category left_key right_key
  | Scheduled tasks => forall count suffix_events result last,
      Trace [] count Run tasks after suffix_events result last ->
      result = key_compare signature (S height) category left_key right_key
  end.
Proof.
  intros category position left right before exit events after BINDING left_key right_key LEFT RIGHT.
  pose proof (the_original_category_binding_certifies_its_enclosing_projected_handler
    signature Term maximum owner_ceiling category_callback uid_digest binder_digest observe lookup
    ORDINALS height category position left right before exit events after BINDING
    left_key right_key LEFT RIGHT) as CERTIFICATE.
  destruct exit as [tasks|decision]; [|exact CERTIFICATE].
  intros count suffix_events result last TRAVERSAL.
  eapply an_actual_original_task_batch_returns_its_projected_fold;
    [exact category_eq_dec|exact original_alias_identity|exact lower_height_completed_child|
     exact CERTIFICATE| |exact TRAVERSAL].
  eapply a_scheduled_original_category_binding_has_distinct_live_initial_owners; exact BINDING.
Qed.

Theorem an_actual_original_category_traversal_factors_from_lower_height_children :
  forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  View (S height) category left = Some left_key -> View (S height) category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = key_compare signature (S height) category left_key right_key.
Proof.
  intros category position left right left_key right_key PAIR LEFT RIGHT
    count state events result last TRAVERSAL.
  unfold child_task in TRAVERSAL.
  inversion TRAVERSAL as [| |n mode head rest before first next_mode prefix middle later final ending STEP TAIL]; subst.
  repeat rewrite app_nil_r in STEP. inversion STEP; subst.
  - match goal with ARM : OriginalArm position state (Scheduled _) _ _ |- _ =>
      pose proof (the_concrete_source_recovers_the_callers_original_constructor_binding
        category_eq_dec Term lookup maximum owner_ceiling category_callback uid_digest binder_digest
        signature observe category position left right _ _ _ _ PAIR ARM) as BOUND
    end.
    pose proof (the_original_bound_handler_factors_at_the_enclosing_category
      category position left right _ _ _ _ BOUND left_key right_key LEFT RIGHT) as FACTOR.
    repeat rewrite app_nil_r in TAIL. exact (FACTOR _ _ _ _ TAIL).
  - match goal with ARM : OriginalArm position state (Signalled _) _ _ |- _ =>
      pose proof (the_concrete_source_recovers_the_callers_original_constructor_binding
        category_eq_dec Term lookup maximum owner_ceiling category_callback uid_digest binder_digest
        signature observe category position left right _ _ _ _ PAIR ARM) as BOUND
    end.
    pose proof (the_original_bound_handler_factors_at_the_enclosing_category
      category position left right _ _ _ _ BOUND left_key right_key LEFT RIGHT) as FACTOR.
    inversion TAIL; subst. exact FACTOR.
Qed.
End OneHeightStep.

(** The induction quantifies over every successfully projected original pair,
    not just the enclosing left/right roster. Thus same-roster sorting requests
    and cross-roster comparisons use the very same lower-height theorem. *)
Theorem every_completed_original_category_comparison_matches_its_successful_projection :
  forall height category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  View height category left = Some left_key -> View height category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = key_compare signature height category left_key right_key.
Proof.
  intro height. induction height as [|height IH];
    intros category position left right left_key right_key PAIR LEFT RIGHT
      count state events result last TRAVERSAL.
  - discriminate LEFT.
  - exact (an_actual_original_category_traversal_factors_from_lower_height_children
      height IH category position left right left_key right_key PAIR LEFT RIGHT
      count state events result last TRAVERSAL).
Qed.
End OriginalCategoryExecution.
End GeneratedMapCategoryComparison.

Print Assumptions GeneratedMapCategoryComparison.the_original_bound_handler_factors_at_the_enclosing_category.
Print Assumptions GeneratedMapCategoryComparison.an_actual_original_category_traversal_factors_from_lower_height_children.
Print Assumptions GeneratedMapCategoryComparison.every_completed_original_category_comparison_matches_its_successful_projection.
