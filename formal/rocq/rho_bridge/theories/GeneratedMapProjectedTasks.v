(** State-indexed certificates for original constructor-created task batches.

    Borrowed tasks reuse ProjectedBorrowed unchanged. A Map Start certificate
    additionally retains the original rosters, successful field projections,
    bounds and exact initial owner payload at its current cell. Preserving
    that complete cell transports the certificate across preceding siblings.

    There is deliberately no Resume constructor: an arbitrary suspended
    continuation is not a newly constructed field, and treating it as one
    would invalidate the first-decisive field fold. These are propositions
    about existing tasks, not runtime tasks or a new execution relation. The
    expected Map comparison is derived from successful source keys; actual
    execution must be connected by the separately proved Map segment. *)
From Stdlib Require Import List.
From RhoBridge Require Import GeneratedMapSourceOwnership GeneratedCollectionOwnerFrame
  GeneratedMapOwnerTraversal
  GeneratedSourceRowComparison GeneratedConstructorSourceProjection
  GeneratedConstructorComparisonClasses GeneratedComparisonFieldResults
  AdmittedGeneratedCollectionScheduling GeneratedMapCoreSource.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.
Import GeneratedComparisonFieldResults.GeneratedComparisonFieldResults.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.
Import AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.

Module GeneratedMapProjectedTasks.
Section OriginalTaskCertificates.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable maximum : nat.
Variables uid_digest binder_digest : nat -> nat.
Variable lookup : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  option { category : Cat & (Term category * Term category)%type }.
Variable category_callback : Cat -> nat.
Variable children : Cat -> Ordered.
Variable next : forall category, Term category -> option (carrier (children category)).
Local Notation State := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation owned_map := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.owned_map Cat Term).
Local Notation initial_map := GeneratedMapCoreSource.GeneratedMapCoreSource.initial_map.
Local Notation PB := (@ProjectedBorrowed Cat Term lookup children next).
Local Notation ProjectBase := (project_base Term uid_digest binder_digest children next).

Inductive ProjectedInitialTask (state : State) : Task -> comparison -> Prop :=
| OriginalBorrowedTask : forall task decision,
    PB task decision -> ProjectedInitialTask state task decision
| OriginalMapStart : forall category owner buffers left right left_key right_key,
    length left <= maximum -> length right <= maximum ->
    ProjectBase (MapPairs category) left = Some left_key ->
    ProjectBase (MapPairs category) right = Some right_key ->
    nth_error state owner = Some (Some (category_callback category,
      owned_map category buffers (initial_map maximum left right (length left) (length right)))) ->
    ProjectedInitialTask state (Start owner (category_callback category))
      (comparison_function (base_order children (MapPairs category)) left_key right_key).

Definition ProjectedInitialBatch state tasks decision :=
  exists decisions, Forall2 (ProjectedInitialTask state) tasks decisions /\
    fold_decisions decisions = decision.

Theorem original_initial_task_is_not_a_suspended_resume : forall state task decision,
  ProjectedInitialTask state task decision -> not_resume task = true.
Proof.
  intros state task decision BOUND. destruct BOUND.
  - eapply a_projected_borrowed_task_has_no_owner_continuation. eassumption.
  - reflexivity.
Qed.

Theorem original_task_certificate_follows_its_complete_owner_payload :
  forall before task decision,
  ProjectedInitialTask before task decision -> forall after,
  preserves_owner_frame (task_owners task) before after ->
  ProjectedInitialTask after task decision.
Proof.
  intros before task decision BOUND.
  destruct BOUND as [task decision BORROWED|
    category owner buffers left right left_key right_key LEFT_BOUND RIGHT_BOUND LEFT RIGHT CELL];
    intros after FRAME.
  - constructor. exact BORROWED.
  - eapply OriginalMapStart; [exact LEFT_BOUND|exact RIGHT_BOUND|exact LEFT|exact RIGHT|].
    rewrite (FRAME owner); [exact CELL|left; reflexivity].
Qed.

Theorem original_batch_certificates_follow_their_complete_owner_frame :
  forall before tasks decisions,
  Forall2 (ProjectedInitialTask before) tasks decisions -> forall after,
  preserves_owner_frame (owner_refs tasks) before after ->
  Forall2 (ProjectedInitialTask after) tasks decisions.
Proof.
  intros before tasks decisions BOUND. induction BOUND; intros after FRAME.
  - constructor.
  - constructor.
    + eapply original_task_certificate_follows_its_complete_owner_payload; [exact H|].
      intros owner IN. apply FRAME.
      rewrite original_task_head_partitions_owner_references. apply in_or_app. left. exact IN.
    + apply IHBOUND. intros owner IN. apply FRAME.
      rewrite original_task_head_partitions_owner_references. apply in_or_app. right. exact IN.
Qed.

Theorem existing_borrowed_bindings_are_original_initial_certificates :
  forall tasks decisions, Forall2 PB tasks decisions -> forall state,
  Forall2 (ProjectedInitialTask state) tasks decisions.
Proof.
  intros tasks decisions BOUND. induction BOUND; intro state; constructor; auto.
  now constructor.
Qed.

Theorem original_initial_batch_has_no_resume : forall state tasks decisions,
  Forall2 (ProjectedInitialTask state) tasks decisions ->
  Forall (fun task => not_resume task = true) tasks.
Proof.
  intros state tasks decisions BOUND. induction BOUND; constructor; auto.
  eapply original_initial_task_is_not_a_suspended_resume. exact H.
Qed.

Lemma original_initial_bindings_append : forall state first decisions rest results,
  Forall2 (ProjectedInitialTask state) first decisions ->
  Forall2 (ProjectedInitialTask state) rest results ->
  Forall2 (ProjectedInitialTask state) (first ++ rest) (decisions ++ results).
Proof.
  intros state first decisions rest results FIRST REST.
  induction FIRST; cbn [app]; [exact REST|constructor; assumption].
Qed.

Lemma original_initial_batch_append : forall state first a rest b,
  ProjectedInitialBatch state first a -> ProjectedInitialBatch state rest b ->
  ProjectedInitialBatch state (first ++ rest)
    (SemanticComparisonLaws.SemanticComparisonLaws.lex a b).
Proof.
  intros state first a rest b [xs [FIRST A]] [ys [REST B]].
  exists (xs ++ ys). split.
  - now apply original_initial_bindings_append.
  - now rewrite fold_decisions_app, A, B.
Qed.

Theorem existing_borrowed_batch_lifts_without_rederiving_its_recipes :
  forall tasks decision,
  @ProjectedBatch Cat Term lookup children next tasks decision -> forall state,
  ProjectedInitialBatch state tasks decision.
Proof.
  intros tasks decision [decisions [BOUND RESULT]] state.
  exists decisions. split; [now apply existing_borrowed_bindings_are_original_initial_certificates|exact RESULT].
Qed.

Lemma a_complete_owner_frame_transports_the_original_batch :
  forall before tasks decision, ProjectedInitialBatch before tasks decision -> forall after,
  preserves_owner_frame (owner_refs tasks) before after -> ProjectedInitialBatch after tasks decision.
Proof.
  intros before tasks decision [decisions [BOUND RESULT]] after FRAME.
  exists decisions. split; [|exact RESULT].
  eapply original_batch_certificates_follow_their_complete_owner_frame; eassumption.
Qed.

Lemma an_empty_pending_word_has_valid_owner_inventory : forall state : State,
  pending_owners_valid [] state.
Proof. intro state. split; constructor. Qed.

Section OriginalConstruction.
Variable owner_ceiling : nat.
Local Notation Make := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.make_map_box
  Cat Term maximum owner_ceiling category_callback).
Local Notation BC := (@BaseConstruction Cat Term State uid_digest binder_digest lookup Make).
Local Notation FC := (@FieldConstruction Cat Term State uid_digest binder_digest lookup Make).
Local Notation ProjectField := (project_field Term uid_digest binder_digest children next).

Theorem original_map_factory_constructs_its_current_start_certificate :
  forall category left right before owner callback after,
  Make category left right before owner callback after -> forall left_key right_key,
  ProjectBase (MapPairs category) left = Some left_key ->
  ProjectBase (MapPairs category) right = Some right_key ->
  ProjectedInitialBatch after [Start owner callback]
    (comparison_function (base_order children (MapPairs category)) left_key right_key).
Proof.
  intros category left right before owner callback after FACTORY left_key right_key LEFT RIGHT.
  destruct FACTORY as [before extended after buffers WIDTH_LEFT WIDTH_RIGHT ALLOCATE WRITE].
  exists [comparison_function (base_order children (MapPairs category)) left_key right_key]. split.
  - constructor; [|constructor].
    eapply OriginalMapStart; [exact WIDTH_LEFT|exact WIDTH_RIGHT|exact LEFT|exact RIGHT|].
    eapply successful_write_contains_exactly_the_tagged_payload. exact WRITE.
  - destruct (comparison_function (base_order children (MapPairs category)) left_key right_key);
      reflexivity.
Qed.

Lemma existing_nonmap_base_construction_lifts_to_current_initial_certificates :
  forall base left right position before word events after,
  BC base left right position before word events after -> nonmap_base base ->
  forall left_key right_key,
  ProjectBase base left = Some left_key -> ProjectBase base right = Some right_key ->
  ProjectedInitialBatch after (rev word)
    (comparison_function (base_order children base) left_key right_key).
Proof.
  intros base left right position before word events after BUILD NONMAP left_key right_key LEFT RIGHT.
  apply existing_borrowed_batch_lifts_without_rederiving_its_recipes.
  eapply constructed_nonmap_base_binds_its_successful_projection; eassumption.
Qed.

Theorem original_base_construction_certifies_its_successful_projection :
  forall base left right position before word events after,
  BC base left right position before word events after -> forall left_key right_key,
  ProjectBase base left = Some left_key -> ProjectBase base right = Some right_key ->
  ProjectedInitialBatch after (rev word)
    (comparison_function (base_order children base) left_key right_key).
Proof.
  intros base left right position before word events after BUILD.
  pose proof BUILD as ORIGINAL. destruct BUILD; intros left_key right_key LEFT RIGHT.
  - eapply existing_nonmap_base_construction_lifts_to_current_initial_certificates;
      [exact ORIGINAL|exact I|exact LEFT|exact RIGHT].
  - eapply existing_nonmap_base_construction_lifts_to_current_initial_certificates;
      [exact ORIGINAL|exact I|exact LEFT|exact RIGHT].
  - eapply existing_nonmap_base_construction_lifts_to_current_initial_certificates;
      [exact ORIGINAL|exact I|exact LEFT|exact RIGHT].
  - eapply original_map_factory_constructs_its_current_start_certificate; eassumption.
Qed.

Theorem original_field_construction_certifies_its_successful_projection :
  forall field left right position before word events after,
  FC field left right position before word events after -> forall left_key right_key,
  ProjectField field left = Some left_key -> ProjectField field right = Some right_key ->
  ProjectedInitialBatch after (rev word)
    (comparison_function (field_order children field) left_key right_key).
Proof.
  intros field left right position before word events after BUILD.
  destruct BUILD; intros left_key right_key LEFT RIGHT.
  - eapply original_base_construction_certifies_its_successful_projection; eassumption.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    inversion LEFT; inversion RIGHT; subst.
    apply existing_borrowed_batch_lifts_without_rederiving_its_recipes. apply projected_batch_empty.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base right) as [key|] eqn:KEY; try discriminate.
    inversion LEFT; inversion RIGHT; subst.
    apply existing_borrowed_batch_lifts_without_rederiving_its_recipes. apply projected_batch_verdict.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base left) as [key|] eqn:KEY; try discriminate.
    inversion LEFT; inversion RIGHT; subst.
    apply existing_borrowed_batch_lifts_without_rederiving_its_recipes. apply projected_batch_verdict.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base left) as [lk|] eqn:LK; try discriminate.
    destruct (ProjectBase base right) as [rk|] eqn:RK; try discriminate.
    inversion LEFT; inversion RIGHT; subst.
    eapply original_base_construction_certifies_its_successful_projection; eassumption.
Qed.

Section OriginalReverseFields.
Variable field_position : nat -> AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.
Local Notation RC := (@ReverseFieldsConstruction Cat Term State uid_digest binder_digest lookup Make field_position).
Local Notation ProjectFields := (project_fields Term uid_digest binder_digest children next).

Theorem reverse_constructed_original_fields_have_distinct_live_owners :
  forall fields left right index before word groups events after,
  RC fields left right index before word groups events after ->
  pending_owners_valid (rev word) after.
Proof.
  intros fields left right index before word groups events after BUILD.
  pose proof (GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.reverse_field_construction_retains_every_previously_parked_owner
    Term maximum owner_ceiling category_callback uid_digest binder_digest lookup field_position
    fields left right index before word groups events after BUILD []
    (an_empty_pending_word_has_valid_owner_inventory before)) as [LIVE FRAME].
  now rewrite app_nil_r in LIVE.
Qed.

Theorem reverse_field_construction_certifies_the_original_forward_field_order :
  forall fields left right index before word groups events after,
  RC fields left right index before word groups events after -> forall left_key right_key,
  ProjectFields fields left = Some left_key -> ProjectFields fields right = Some right_key ->
  ProjectedInitialBatch after (rev word)
    (comparison_function (fields_order children fields) left_key right_key).
Proof.
  intros fields left right index before word groups events after BUILD.
  induction BUILD as [index state|
    field rest left right left_rest right_rest index before tail_word tail_groups tail_events middle
    head_word head_events after TAIL IH HEAD]; intros left_key right_key LEFT RIGHT.
  - destruct left_key, right_key.
    apply existing_borrowed_batch_lifts_without_rederiving_its_recipes. apply projected_batch_empty.
  - destruct left_key as [lk lks], right_key as [rk rks].
    apply successful_pair_projection_keeps_both_original_positions in LEFT as [LEFT_HEAD LEFT_TAIL].
    apply successful_pair_projection_keeps_both_original_positions in RIGHT as [RIGHT_HEAD RIGHT_TAIL].
    pose proof (IH _ _ LEFT_TAIL RIGHT_TAIL) as TAIL_CERTIFICATES.
    pose proof (reverse_constructed_original_fields_have_distinct_live_owners
      _ _ _ _ _ _ _ _ _ TAIL) as TAIL_LIVE.
    pose proof (GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.original_field_construction_preserves_its_complete_pending_owner_frame
      Term maximum owner_ceiling category_callback uid_digest binder_digest lookup
      _ _ _ _ _ _ _ _ HEAD (rev tail_word) TAIL_LIVE) as [FINAL_LIVE TAIL_FRAME].
    rewrite rev_app_distr. apply original_initial_batch_append.
    + eapply original_field_construction_certifies_its_successful_projection; eassumption.
    + eapply a_complete_owner_frame_transports_the_original_batch; eassumption.
Qed.
End OriginalReverseFields.
End OriginalConstruction.
End OriginalTaskCertificates.
End GeneratedMapProjectedTasks.

Print Assumptions GeneratedMapProjectedTasks.original_initial_task_is_not_a_suspended_resume.
Print Assumptions GeneratedMapProjectedTasks.original_task_certificate_follows_its_complete_owner_payload.
Print Assumptions GeneratedMapProjectedTasks.original_batch_certificates_follow_their_complete_owner_frame.
Print Assumptions GeneratedMapProjectedTasks.existing_borrowed_bindings_are_original_initial_certificates.
Print Assumptions GeneratedMapProjectedTasks.original_initial_batch_has_no_resume.
Print Assumptions GeneratedMapProjectedTasks.original_initial_bindings_append.
Print Assumptions GeneratedMapProjectedTasks.original_initial_batch_append.
Print Assumptions GeneratedMapProjectedTasks.existing_borrowed_batch_lifts_without_rederiving_its_recipes.
Print Assumptions GeneratedMapProjectedTasks.original_map_factory_constructs_its_current_start_certificate.
Print Assumptions GeneratedMapProjectedTasks.existing_nonmap_base_construction_lifts_to_current_initial_certificates.
Print Assumptions GeneratedMapProjectedTasks.original_base_construction_certifies_its_successful_projection.
Print Assumptions GeneratedMapProjectedTasks.original_field_construction_certifies_its_successful_projection.
Print Assumptions GeneratedMapProjectedTasks.a_complete_owner_frame_transports_the_original_batch.
Print Assumptions GeneratedMapProjectedTasks.an_empty_pending_word_has_valid_owner_inventory.
Print Assumptions GeneratedMapProjectedTasks.reverse_constructed_original_fields_have_distinct_live_owners.
Print Assumptions GeneratedMapProjectedTasks.reverse_field_construction_certifies_the_original_forward_field_order.
