(** Complete parked-owner preservation through the original generated traversal.

    Construction uses the existing Base/Field/Trailer/ArmConstruction witnesses
    with the concrete fresh Map factory. The scope is constructed before the
    reverse field suffix; proof states follow that same order. Execution is
    the existing SourceStep/ChildTraversal, instantiated with original
    CategoryArmBinding, typed RawResume callbacks, and original discard.
    No new execution relation, allocator, store, source AST, or comparator is
    introduced. An untouched frame retains its COMPLETE tagged owner payload,
    not merely its owner names or allocation credits.

    The arm_source definition below selects the already modeled original
    constructor association; it is not inferred from a key view. Its binding
    to Rust remains the audited census/index/selector and by-value move
    association. Native receipts, pointer validity and admitted buffer credit
    remain their existing obligations. No semantic Map result is asserted. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import GeneratedMapSourceOwnership GeneratedCollectionOwnerFrame
  GeneratedSourceRowComparison GeneratedChildTraversal AdmittedGeneratedCollectionScheduling.
Import ListNotations.
Import AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.
Import GeneratedChildTraversal.GeneratedChildTraversal.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.

Module GeneratedMapOwnerTraversal.
Section OriginalConstructionAndExecution.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variables maximum owner_ceiling : nat.
Variable category_callback : Cat -> nat.
Local Notation State := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation Make := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.make_map_box
  Cat Term maximum owner_ceiling category_callback).
Local Notation Position := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.

Lemma reversed_original_word_reverses_only_its_owner_references : forall word,
  owner_refs (rev word) = rev (owner_refs word).
Proof.
  intro word. induction word as [|task rest IH]; [reflexivity|].
  change (owner_refs (rev rest ++ [task]) = rev (task_owners task ++ owner_refs rest)).
  rewrite owner_references_partition_at_a_stack_split, rev_app_distr, IH.
  assert (SINGLE : owner_refs [task] = task_owners task).
  { destruct task; reflexivity. }
  rewrite SINGLE. destruct task; reflexivity.
Qed.
Lemma original_child_pair_word_has_no_owner_references : forall positions,
  owner_refs (map child_task positions) = [].
Proof.
  intro positions. induction positions as [|position rest IH]; [reflexivity|].
  exact IH.
Qed.
Lemma ownerless_original_word_keeps_pending_ownership : forall word pending (cells : State),
  owner_refs word = [] -> pending_owners_valid pending cells ->
  pending_owners_valid (word ++ pending) cells.
Proof.
  intros word pending cells EMPTY VALID. unfold pending_owners_valid in *.
  rewrite owner_references_partition_at_a_stack_split, EMPTY. exact VALID.
Qed.
Lemma a_preserved_original_tail_preserves_its_saved_suffix : forall prefix frame (before after : State),
  preserves_owner_frame (owner_refs (prefix ++ frame)) before after ->
  preserves_owner_frame (owner_refs frame) before after.
Proof.
  intros prefix frame before after PRESERVED owner IN. apply PRESERVED.
  rewrite owner_references_partition_at_a_stack_split. apply in_or_app. right. exact IN.
Qed.

Variables uid_digest binder_digest : nat -> nat.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Local Notation BC := (@BaseConstruction Cat Term State uid_digest binder_digest lookup Make).
Local Notation FC := (@FieldConstruction Cat Term State uid_digest binder_digest lookup Make).
Local Notation TC := (@TrailerConstruction Cat Term State uid_digest binder_digest lookup).

Theorem original_base_construction_preserves_its_complete_pending_owner_frame :
  forall base left right position before word events after,
  BC base left right position before word events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (rev word ++ pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros base left right position before word events after BUILD.
  destruct BUILD as [atom left right position state
    |category left right position state PAIR
    |category left right position state positions PAIRS
    |category left right position before owner callback after FACTORY]; intros pending VALID.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split.
    + apply ownerless_original_word_keeps_pending_ownership; [|exact VALID].
      rewrite reversed_original_word_reverses_only_its_owner_references.
      rewrite original_task_head_partitions_owner_references.
      cbn [verdict_task task_owners app].
      rewrite reversed_original_word_reverses_only_its_owner_references,
        original_child_pair_word_has_no_owner_references. reflexivity.
    + intros owner IN. reflexivity.
  - eapply GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.factory_adds_one_fresh_start_without_changing_parked_owners;
      eassumption.
Qed.

Theorem original_field_construction_preserves_its_complete_pending_owner_frame :
  forall field left right position before word events after,
  FC field left right position before word events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (rev word ++ pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros field left right position before word events after BUILD.
  destruct BUILD; intros pending VALID.
  - eapply original_base_construction_preserves_its_complete_pending_owner_frame; eassumption.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - eapply original_base_construction_preserves_its_complete_pending_owner_frame; eassumption.
Qed.

Theorem original_scope_construction_keeps_all_existing_owner_payloads :
  forall fields left right before word events after,
  TC fields left right before word events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (rev word ++ pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros fields left right before word events after BUILD.
  destruct BUILD; intros pending VALID;
    (split; [exact VALID|intros owner IN; reflexivity]).
Qed.

Section PerOriginalArmPositions.
Variable positions : nat -> Position.
Local Notation RC := (@ReverseFieldsConstruction Cat Term State uid_digest binder_digest lookup Make positions).
Theorem reverse_field_construction_retains_every_previously_parked_owner :
  forall fields left right index before word groups events after,
  RC fields left right index before word groups events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (rev word ++ pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros fields left right index before word groups events after BUILD.
  induction BUILD as [index state
    |field rest left right left_rest right_rest index before tail_word tail_groups tail_events middle
      head_word head_events after TAIL IH HEAD]; intros pending VALID.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - destruct (IH pending VALID) as [MIDDLE TAIL_FRAME].
    destruct (original_field_construction_preserves_its_complete_pending_owner_frame
      _ _ _ _ _ _ _ _ HEAD (rev tail_word ++ pending) MIDDLE) as [FINAL HEAD_FRAME].
    split.
    + rewrite rev_app_distr, <- app_assoc. exact FINAL.
    + eapply owner_frame_preservation_composes; [exact TAIL_FRAME|].
      eapply a_preserved_original_tail_preserves_its_saved_suffix. exact HEAD_FRAME.
Qed.

Variable trailer_fields : list (@GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.Field Cat).
Variables trailer_left trailer_right : GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.source_fields_type Term trailer_fields.
Local Notation AC := (@ArmConstruction Cat Term State uid_digest binder_digest lookup Make positions
  trailer_fields trailer_left trailer_right).
Theorem original_arm_construction_retains_its_complete_owner_frame :
  forall fields left right index before exit events after,
  AC fields left right index before exit events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (match exit with Scheduled tasks => tasks ++ pending | Signalled _ => pending end) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros fields left right index before exit events after BUILD.
  induction BUILD as [atom rest left right left_rest right_rest index state DECISIVE
    |atom rest left right left_rest right_rest index before exit events after EQUAL TAIL IH
    |field rest left right index before scope_word scope_events middle field_word groups field_events after STACK SCOPE FIELDS
    |index before word events after SCOPE]; intros pending VALID.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - exact (IH pending VALID).
  - destruct (original_scope_construction_keeps_all_existing_owner_payloads
      _ _ _ _ _ _ _ SCOPE pending VALID) as [MIDDLE SCOPE_FRAME].
    destruct (reverse_field_construction_retains_every_previously_parked_owner
      _ _ _ _ _ _ _ _ _ FIELDS (rev scope_word ++ pending) MIDDLE) as [FINAL FIELD_FRAME].
    split.
    + cbn. rewrite rev_app_distr, <- app_assoc. exact FINAL.
    + eapply owner_frame_preservation_composes; [exact SCOPE_FRAME|].
      eapply a_preserved_original_tail_preserves_its_saved_suffix. exact FIELD_FRAME.
  - eapply original_scope_construction_keeps_all_existing_owner_payloads; eassumption.
Qed.
End PerOriginalArmPositions.

Variable signature : Cat -> list (@GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.Row Cat).
Variable observe : forall category, Term category ->
  GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.SourceObservation signature Term category.

(** An instantiation of the existing SourceStep arm parameter. Its witness is
    original constructor selection/construction, never a comparison answer. *)
Definition arm_source position before exit events after :=
  exists category (left right : Term category),
    @CategoryArmBinding Cat signature Term State uid_digest binder_digest observe lookup Make
      category position left right before exit events after.

Theorem the_bound_original_arm_preserves_its_live_pending_owner_frame :
  forall position before exit events after,
  arm_source position before exit events after ->
  forall pending, pending_owners_valid pending before ->
  pending_owners_valid (match exit with Scheduled tasks => tasks ++ pending | Signalled _ => pending end) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros position before exit events after [category [left [right BINDING]]] pending VALID.
  destruct BINDING.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - eapply original_arm_construction_retains_its_complete_owner_frame; eassumption.
Qed.

Variable alias : forall category, Term category -> Term category -> bool.
Local Notation CoreSource := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.core_source
  Cat Term maximum alias category_callback lookup).
Local Notation DiscardSource := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.discard_source Cat Term).
Local Notation Step := (@SourceStep State arm_source CoreSource DiscardSource).
Local Notation Trace := (@ChildTraversal State arm_source CoreSource DiscardSource).

Theorem every_original_source_step_preserves_live_owners_and_its_complete_tail :
  forall mode head rest before events next_mode after next,
  Step mode (head :: rest) before events next_mode after next ->
  pending_owners_valid (head :: rest) before ->
  pending_owners_valid after next /\ preserves_owner_frame (owner_refs rest) before next.
Proof.
  intros mode head rest before events next_mode after next STEP VALID.
  inversion STEP; subst.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - match goal with ARM : arm_source ?position ?before (Scheduled ?tasks) ?events ?after |- _ =>
      exact (the_bound_original_arm_preserves_its_live_pending_owner_frame
        position before (Scheduled tasks) events after ARM rest VALID)
    end.
  - lazymatch goal with ARM : arm_source ?position ?before (Signalled ?decision) ?events ?after
      |- pending_owners_valid ?remaining _ /\ _ =>
      exact (the_bound_original_arm_preserves_its_live_pending_owner_frame
        position before (Signalled decision) events after ARM remaining VALID)
    end.
  - match goal with CORE : CoreSource ?owner ?callback _ _ _ _ _ |- _ =>
      eapply GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.source_callback_preserves_the_live_continuation_and_all_other_complete_owners
        with (head := Start owner callback); [exact CORE|reflexivity|exact VALID]
    end.
  - match goal with CORE : CoreSource ?owner ?callback _ _ _ _ _ |- _ =>
      eapply GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.source_callback_preserves_the_live_continuation_and_all_other_complete_owners
        with (head := Resume owner callback); [exact CORE|reflexivity|exact VALID]
    end.
  - match goal with CORE : CoreSource ?owner ?callback _ _ _ _ _ |- _ =>
      eapply GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.source_callback_preserves_the_live_continuation_and_all_other_complete_owners
        with (head := Resume owner callback); [exact CORE|reflexivity|exact VALID]
    end.
  - eapply GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.actual_discard_preserves_every_remaining_live_owner;
      eassumption.
Qed.

Theorem an_actual_child_traversal_preserves_the_complete_parked_owner_frame :
  forall frame count mode prefix before events result after,
  Trace frame count mode prefix before events result after ->
  pending_owners_valid (prefix ++ frame) before ->
  pending_owners_valid frame after /\ preserves_owner_frame (owner_refs frame) before after.
Proof.
  intros frame count mode prefix before events result after TRAVERSAL.
  induction TRAVERSAL as [state|state ordering DECISIVE
    |count mode head rest state first next_mode prefix next later result last STEP TAIL IH];
    intro VALID.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - destruct (every_original_source_step_preserves_live_owners_and_its_complete_tail
      mode head (rest ++ frame) state first next_mode (prefix ++ frame) next STEP VALID)
      as [NEXT_VALID FIRST_FRAME].
    destruct (IH NEXT_VALID) as [FINAL LATER_FRAME]. split; [exact FINAL|].
    eapply owner_frame_preservation_composes; [|exact LATER_FRAME].
    eapply a_preserved_original_tail_preserves_its_saved_suffix. exact FIRST_FRAME.
Qed.

Theorem a_completed_child_retains_its_exact_parent_resume_payload :
  forall owner callback outer count mode prefix before events result after tag payload,
  Trace (Resume owner callback :: outer) count mode prefix before events result after ->
  pending_owners_valid (prefix ++ Resume owner callback :: outer) before ->
  List.nth_error before owner = Some (Some (tag, payload)) ->
  List.nth_error after owner = Some (Some (tag, payload)).
Proof.
  intros owner callback outer count mode prefix before events result after tag payload TRACE VALID ORIGINAL.
  destruct (an_actual_child_traversal_preserves_the_complete_parked_owner_frame
    (Resume owner callback :: outer) count mode prefix before events result after TRACE VALID)
    as [LIVE FRAME].
  rewrite (FRAME owner); [exact ORIGINAL|].
  rewrite original_task_head_partitions_owner_references. left. reflexivity.
Qed.
End OriginalConstructionAndExecution.

Print Assumptions reversed_original_word_reverses_only_its_owner_references.
Print Assumptions original_child_pair_word_has_no_owner_references.
Print Assumptions ownerless_original_word_keeps_pending_ownership.
Print Assumptions a_preserved_original_tail_preserves_its_saved_suffix.
Print Assumptions original_base_construction_preserves_its_complete_pending_owner_frame.
Print Assumptions original_field_construction_preserves_its_complete_pending_owner_frame.
Print Assumptions original_scope_construction_keeps_all_existing_owner_payloads.
Print Assumptions reverse_field_construction_retains_every_previously_parked_owner.
Print Assumptions original_arm_construction_retains_its_complete_owner_frame.
Print Assumptions the_bound_original_arm_preserves_its_live_pending_owner_frame.
Print Assumptions every_original_source_step_preserves_live_owners_and_its_complete_tail.
Print Assumptions an_actual_child_traversal_preserves_the_complete_parked_owner_frame.
Print Assumptions a_completed_child_retains_its_exact_parent_resume_payload.
End GeneratedMapOwnerTraversal.
