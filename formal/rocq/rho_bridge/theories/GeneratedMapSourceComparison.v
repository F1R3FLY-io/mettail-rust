(** Actual execution of the original constructor-created task batch.

    Each head is justified by the existing borrowed-child proof or the actual
    Map segment theorem. The untouched tail retains both its distinct live
    owners and their complete payloads across the actual framed head trace.
    Its state-indexed certificates are transported to that resulting state
    before continuing. A decisive answer uses the existing disposal rule for
    non-Resume tasks, including unstarted Map owners. No executor, result
    oracle, or generic suspended-Resume certificate is introduced here. *)
From Stdlib Require Import List.
From RhoBridge Require Import GeneratedMapActualSegment GeneratedMapProjectedTasks
  GeneratedMapOwnerTraversal GeneratedMapSourceOwnership GeneratedSourceRowComparison
  GeneratedConstructorSourceProjection GeneratedConstructorComparisonClasses
  GeneratedCollectionOwnerFrame GeneratedComparisonFieldResults.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.
Import GeneratedMapProjectedTasks.GeneratedMapProjectedTasks.
Import GeneratedMapActualSegment.GeneratedMapActualSegment.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.
Import GeneratedComparisonFieldResults.GeneratedComparisonFieldResults.
Import GeneratedChildTraversal.GeneratedChildTraversal.
Import AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.

Module GeneratedMapSourceComparison.
Section OriginalBatchExecution.
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
Local Notation Cells := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation OriginalArm := (@GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.arm_source
  Cat Term maximum owner_ceiling category_callback uid_digest binder_digest lookup signature observe).
Local Notation OriginalCore := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.core_source
  Cat Term maximum alias category_callback lookup).
Local Notation OriginalDiscard := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.discard_source Cat Term).
Local Notation Trace := (@ChildTraversal Cells OriginalArm OriginalCore OriginalDiscard).
Variable children : Cat -> Ordered.
Variable next : forall category, Term category -> option (carrier (children category)).
Local Notation InitialTask := (@ProjectedInitialTask Cat Term maximum uid_digest binder_digest
  lookup category_callback children next).
Local Notation InitialBatch := (@ProjectedInitialBatch Cat Term maximum uid_digest binder_digest
  lookup category_callback children next).
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  next category left = Some left_key -> next category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = comparison_function (children category) left_key right_key.

Theorem an_actual_initial_task_returns_its_original_projected_comparison :
  forall state task decision, InitialTask state task decision ->
  forall count events result after,
  Trace [] count Run [task] state events result after -> result = decision.
Proof.
  intros state task decision BOUND.
  destruct BOUND as [task decision BORROWED|
    category owner buffers left right left_key right_key LEFT_BOUND RIGHT_BOUND LEFT RIGHT STORED];
    intros count events result after TRAVERSAL.
  - eapply an_actual_borrowed_child_returns_its_projected_comparison;
      [exact lower_height_completed_child|eassumption|exact TRAVERSAL].
  - exact (@an_actual_original_map_start_returns_its_projected_map_comparison
      Cat Term maximum owner_ceiling category_callback uid_digest binder_digest lookup
      signature observe alias children next lower_height_completed_child category_eq_dec
      original_alias_identity category owner buffers left right left_key right_key count state
      events result after LEFT_BOUND RIGHT_BOUND LEFT RIGHT STORED TRAVERSAL).
Qed.

Theorem an_actual_original_task_batch_constructs_its_projected_consultation :
  forall tasks state decisions,
  Forall2 (InitialTask state) tasks decisions -> pending_owners_valid tasks state ->
  forall count events result after,
  Trace [] count Run tasks state events result after -> Consultation decisions result.
Proof.
  intro tasks. induction tasks as [|task tasks IH];
    intros state decisions BOUND VALID count events result after TRAVERSAL.
  - inversion BOUND; subst. inversion TRAVERSAL; subst. constructor.
  - inversion BOUND as [|head decision tail remaining HEAD TAIL]; subst head tail.
    destruct (@running_child_trace_splits_before_its_untouched_frame
      Cells OriginalArm OriginalCore OriginalDiscard count [task] tasks state events result after TRAVERSAL)
      as [child_count [later_count [child_result [middle [child_events [later_events
        [CHILD [CONTINUATION [COUNTS EVENTS]]]]]]]]].
    pose proof (@finite_child_traversal_strips_to_a_genuine_isolated_trace
      Cells OriginalArm OriginalCore OriginalDiscard tasks child_count Run [task]
      state child_events child_result middle CHILD) as ISOLATED.
    pose proof (an_actual_initial_task_returns_its_original_projected_comparison
      state task decision HEAD child_count child_events child_result middle ISOLATED) as ANSWER.
    assert (PARKED : pending_owners_valid tasks middle /\
      preserves_owner_frame (owner_refs tasks) state middle).
    { eapply GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.an_actual_child_traversal_preserves_the_complete_parked_owner_frame;
        [exact CHILD|exact VALID]. }
    destruct PARKED as [TAIL_LIVE FRAME].
    assert (TAIL_CURRENT : Forall2 (InitialTask middle) tasks remaining).
    { eapply original_batch_certificates_follow_their_complete_owner_frame; eassumption. }
    subst child_result. destruct decision.
    + apply ConsultEqual. eapply IH; [exact TAIL_CURRENT|exact TAIL_LIVE|exact CONTINUATION].
    + assert (RESULT : result = Lt).
      { eapply delivery_over_nonresume_tasks_cannot_change_the_decision;
          [exact CONTINUATION|reflexivity|].
        eapply original_initial_batch_has_no_resume. exact TAIL_CURRENT. }
      subst result. apply ConsultDecisive. discriminate.
    + assert (RESULT : result = Gt).
      { eapply delivery_over_nonresume_tasks_cannot_change_the_decision;
          [exact CONTINUATION|reflexivity|].
        eapply original_initial_batch_has_no_resume. exact TAIL_CURRENT. }
      subst result. apply ConsultDecisive. discriminate.
Qed.

Theorem an_actual_original_task_batch_returns_its_projected_fold :
  forall state tasks decision,
  InitialBatch state tasks decision -> pending_owners_valid tasks state ->
  forall count events result after,
  Trace [] count Run tasks state events result after -> result = decision.
Proof.
  intros state tasks decision [decisions [BOUND FOLD]] VALID count events result after TRAVERSAL.
  pose proof (an_actual_original_task_batch_constructs_its_projected_consultation
    tasks state decisions BOUND VALID count events result after TRAVERSAL) as RESULT.
  apply completed_consultation_returns_the_lexicographic_result in RESULT.
  now rewrite FOLD in RESULT.
Qed.
End OriginalBatchExecution.
End GeneratedMapSourceComparison.

Print Assumptions GeneratedMapSourceComparison.an_actual_initial_task_returns_its_original_projected_comparison.
Print Assumptions GeneratedMapSourceComparison.an_actual_original_task_batch_constructs_its_projected_consultation.
Print Assumptions GeneratedMapSourceComparison.an_actual_original_task_batch_returns_its_projected_fold.
