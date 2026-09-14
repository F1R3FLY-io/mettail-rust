(** Enclosing-category certificates from the original constructor binding.

    Construction already fixes the original row, field selectors and scope
    boundary. Successful source projection gives its finite-height keys.
    This file joins those two witnesses without executing a scheduled task:
    a decisive handler has its original result, while a scheduled handler
    retains the existing state-indexed initial-task certificate. Its distinct
    live owners are derived separately from the actual construction.

    Map fields are included through GeneratedMapProjectedTasks; no whole-Map
    result, child execution result or non-Map restriction is assumed here.
    Actual batch execution and the enclosing height induction remain separate
    compositions. No new task, owner store or source observation is defined. *)
From Stdlib Require Import List.
From RhoBridge Require Import GeneratedMapProjectedTasks GeneratedMapSourceOwnership
  GeneratedSourceRowComparison GeneratedConstructorSourceProjection
  GeneratedConstructorComparisonClasses GeneratedCollectionOwnerFrame.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.
Import GeneratedMapProjectedTasks.GeneratedMapProjectedTasks.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.
Import GeneratedChildTraversal.GeneratedChildTraversal.
Import SemanticComparisonLaws.SemanticComparisonLaws.

Module GeneratedMapCategoryProjection.
Section OriginalConstructorCertificate.
Context {Cat : Type}.
Variable signature : Cat -> list (@Row Cat).
Variable Term : Cat -> Type.
Variables maximum owner_ceiling : nat.
Variable category_callback : Cat -> nat.
Variables uid_digest binder_digest : nat -> nat.
Variable observe : forall category, Term category -> SourceObservation signature Term category.
Variable lookup : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  option { category : Cat & (Term category * Term category)%type }.
Local Notation Cells := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation Make := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.make_map_box
  Cat Term maximum owner_ceiling category_callback).
Local Notation Binding := (@CategoryArmBinding Cat signature Term Cells uid_digest binder_digest
  observe lookup Make).
Local Notation View := (source_view signature Term uid_digest binder_digest observe).
Hypothesis ORDINALS : signature_ordinals_ordered signature.
Variable height : nat.
Local Notation children := (category_order signature height).
Local Notation next := (fun category child => View height category child).
Local Notation InitialHandler := (@ProjectedInitialHandler Cat Term maximum uid_digest binder_digest
  lookup category_callback children next).

Theorem the_original_category_binding_certifies_its_enclosing_projected_handler :
  forall category position left right before exit events after,
  Binding category position left right before exit events after ->
  forall left_key right_key,
  View (S height) category left = Some left_key ->
  View (S height) category right = Some right_key ->
  InitialHandler after exit (key_compare signature (S height) category left_key right_key).
Proof.
  intros category position left right before exit events after BINDING.
  destruct BINDING as [state events PAIR DIFFERENT
    |ordinal fields trailer_fields positions path left_fields right_fields left_trailer right_trailer
      before exit events after PAIR OBSERVED_LEFT OBSERVED_RIGHT CONSTRUCTION];
    intros left_key right_key LEFT RIGHT.
  - unfold ProjectedInitialHandler. symmetry.
    eapply source_constructor_mismatch_factors_without_an_arm_result_premise; eassumption.
  - cbn [source_view] in LEFT, RIGHT.
    rewrite OBSERVED_LEFT in LEFT. rewrite OBSERVED_RIGHT in RIGHT.
    change (option_map (inject_row children path)
      (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
        (append_source_fields Term fields trailer_fields left_fields left_trailer)) = Some left_key) in LEFT.
    change (option_map (inject_row children path)
      (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
        (append_source_fields Term fields trailer_fields right_fields right_trailer)) = Some right_key) in RIGHT.
    destruct (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
      (append_source_fields Term fields trailer_fields left_fields left_trailer)) as [left_payload|] eqn:PL;
      cbn [option_map] in LEFT; try discriminate.
    destruct (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
      (append_source_fields Term fields trailer_fields right_fields right_trailer)) as [right_payload|] eqn:PR;
      cbn [option_map] in RIGHT; try discriminate.
    injection LEFT as LEFT_KEY. injection RIGHT as RIGHT_KEY. subst left_key right_key.
    destruct (successful_appended_projection_splits_at_the_original_scope_boundary
      Term children uid_digest binder_digest next fields trailer_fields left_fields left_trailer left_payload PL)
      as [lk [tlk [LP [TL LEFT_PAYLOAD]]]].
    destruct (successful_appended_projection_splits_at_the_original_scope_boundary
      Term children uid_digest binder_digest next fields trailer_fields right_fields right_trailer right_payload PR)
      as [rk [trk [RP [TR RIGHT_PAYLOAD]]]].
    subst left_payload right_payload.
    assert (KEY_RESULT : key_compare signature (S height) category
        (inject_row children path (append_field_keys children fields trailer_fields lk tlk))
        (inject_row children path (append_field_keys children fields trailer_fields rk trk)) =
      lex (comparison_function (fields_order children fields) lk rk)
        (comparison_function (fields_order children trailer_fields) tlk trk)).
    { unfold key_compare. cbn [category_order].
      rewrite same_row_injection_preserves_field_comparison.
      apply appended_field_keys_keep_original_lexicographic_priority. }
    rewrite KEY_RESULT.
    eapply the_original_arm_certifies_its_entire_projected_row_at_the_resulting_owner_state;
      eassumption.
Qed.

Theorem a_scheduled_original_category_binding_has_distinct_live_initial_owners :
  forall category position left right before tasks events after,
  Binding category position left right before (Scheduled tasks) events after ->
  pending_owners_valid tasks after.
Proof.
  intros category position left right before tasks events after BINDING.
  inversion BINDING; subst.
  eapply a_scheduled_original_arm_has_distinct_live_initial_owners; eassumption.
Qed.
End OriginalConstructorCertificate.
End GeneratedMapCategoryProjection.

Print Assumptions GeneratedMapCategoryProjection.the_original_category_binding_certifies_its_enclosing_projected_handler.
Print Assumptions GeneratedMapCategoryProjection.a_scheduled_original_category_binding_has_distinct_live_initial_owners.
