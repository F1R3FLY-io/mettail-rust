(** Original Map Box creation and callback ownership association.

    MapCore below is a proof-only typed observation of the existing erased
    CollectionCmpPda payload. Its category is determined by the generated
    callback and typed pointer casts. It is not a new runtime union, registry,
    driver, source AST, or comparison-result oracle. State reuses the owner
    cells already used by AdmittedCollectionComparisonOwnership.

    The factory stores the original paired rosters, unit totals, initial_map,
    and the exact category callback. A callback takes that original owner,
    performs the existing comparator-free RawResume, and refills the SAME
    cell only when requesting a child. The returned position is bound to the
    actual typed raw request. Completion and discarded Start consume their
    owner without publishing another owner reference.

    These relations are operational source-association witnesses. Binding
    them to Rust still requires the audited by-value Box moves, original
    typed rosters/callbacks, valid immutable borrows, and buffer-inventory
    association. Buffer inventories of the ACTIVE Box may legitimately
    change during RawResume; the proofs retain every other complete owner.
    They do not infer reservation, allocation credit, or a whole Map result.

    The empty internal Observation list means there is no generated native
    LEAF comparison inside the callback itself. Native core operations are
    retained by RawResume, with their charges covered by the existing core
    admission model. GeneratedChildTraversal adds the original callback
    entry/request/completion envelopes. Child execution and the complete
    constructor/ChildTraversal frame lift remain separate composition work. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import IndexedCopySlots AdmittedCollectionComparisonOwnership
  AdmittedGeneratedCollectionScheduling GeneratedCollectionOwnerFrame
  GeneratedMapCoreSource GeneratedChildTraversal GeneratedSourceRowComparison.
Import ListNotations.
Import IndexedCopySlots.IndexedCopySlots.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.

Module GeneratedMapSourceOwnership.
Section OriginalSourceBinding.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable maximum owner_ceiling : nat.
Variable alias : forall category, Term category -> Term category -> bool.
Variable category_callback : Cat -> nat.
Local Notation RawMapState := GeneratedMapCoreSource.GeneratedMapCoreSource.RawMapState.
Local Notation RawResume := GeneratedMapCoreSource.GeneratedMapCoreSource.RawResume.
Local Notation RawRequests := GeneratedMapCoreSource.GeneratedMapCoreSource.Requests.
Local Notation RawCompletes := GeneratedMapCoreSource.GeneratedMapCoreSource.Completes.
Local Notation RawPrimary := GeneratedMapCoreSource.GeneratedMapCoreSource.PrimaryRequest.
Local Notation RawSecondary := GeneratedMapCoreSource.GeneratedMapCoreSource.SecondaryRequest.
Local Notation initial_map := GeneratedMapCoreSource.GeneratedMapCoreSource.initial_map.
Local Notation Buffer := AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer.
Definition MapCore := { category : Cat & @RawMapState (Term category) (Term category) }.
Definition MapOwner := @AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Owner MapCore.
Definition State := @Slots MapOwner.
Local Notation take_owner := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner MapCore).
Local Notation finish_owner_transfer := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.finish_owner_transfer MapCore).
Local Notation AwaitComparison := AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.AwaitComparison.
Local Notation ComparisonDone := AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.ComparisonDone.
Local Notation Task := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Task.
Local Notation Borrowed := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Borrowed.
Local Notation Start := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Start.
Local Notation Resume := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Resume.
Local Notation owner_refs := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.owner_refs.
Local Notation task_owners := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.task_owners.
Local Notation Primary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary.
Local Notation Secondary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary.
Local Notation Observation := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Observation.
Local Notation Position := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.
Local Notation CoreReply := GeneratedChildTraversal.GeneratedChildTraversal.CoreReply.
Local Notation Requests := GeneratedChildTraversal.GeneratedChildTraversal.Requests.
Local Notation Completes := GeneratedChildTraversal.GeneratedChildTraversal.Completes.
Local Notation reply_prefix := GeneratedChildTraversal.GeneratedChildTraversal.reply_prefix.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Local Notation pair_at := (GeneratedSourceRowComparison.GeneratedSourceRowComparison.pair_at Term lookup).

Definition owned_map category (buffers : list Buffer)
    (raw : @RawMapState (Term category) (Term category)) : MapOwner :=
  {| AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.owned_buffers := buffers;
     AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.core_state := existT _ category raw |}.

(** This signature is exactly the make_map_box interface of ArmConstruction.
    Owner names are fresh logical cells, not stack indices or pointer values. *)
Inductive make_map_box category (left right : list (Term category * Term category)) :
    State -> nat -> nat -> State -> Prop :=
| CreateOriginalMapBox : forall before extended after buffers,
    length left <= maximum -> length right <= maximum ->
    allocate owner_ceiling 1 before = Some extended ->
    write_slot (category_callback category) (category_callback category)
      (owned_map category buffers (initial_map maximum left right (length left) (length right)))
      (length before) extended = Some after ->
    make_map_box category left right before (length before) (category_callback category) after.

Theorem factory_keeps_the_original_rosters_unit_totals_and_callback :
  forall category left right before owner callback after,
  make_map_box category left right before owner callback after ->
  owner = length before /\ callback = category_callback category /\
  exists buffers, nth_error after owner = Some (Some (callback,
    owned_map category buffers (initial_map maximum left right (length left) (length right)))).
Proof.
  intros category left right before owner callback after FACTORY.
  destruct FACTORY. split; [reflexivity|]. split; [reflexivity|]. exists buffers.
  eapply successful_write_contains_exactly_the_tagged_payload; eassumption.
Qed.

Theorem factory_adds_one_fresh_start_without_changing_parked_owners :
  forall category left right before owner callback after pending,
  make_map_box category left right before owner callback after ->
  pending_owners_valid pending before ->
  pending_owners_valid (Start owner callback :: pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros category left right before owner callback after pending FACTORY VALID.
  destruct FACTORY. eapply fresh_appended_map_owner_preserves_live_task_ownership; eassumption.
Qed.

(** The concrete core_source interface retains raw control, not a predicted
    comparison result. Arbitrary supplied Orderings enter RawResume itself. *)
Inductive core_source : nat -> nat -> option comparison -> State ->
    CoreReply -> list Observation -> State -> Prop :=
| SourcePrimaryRequest : forall category owner input before emptied after buffers next_buffers
    raw next_raw left right position,
    take_owner owner (category_callback category) before =
      Some (owned_map category buffers raw, emptied) ->
    @RawResume (Term category) (Term category) (alias category) (alias category) maximum
      raw input (RawRequests (RawPrimary left right)) next_raw ->
    pair_at category position left right ->
    finish_owner_transfer AwaitComparison owner (category_callback category)
      (owned_map category next_buffers next_raw) emptied = Some after ->
    core_source owner (category_callback category) input before (Requests Primary position) [] after
| SourceSecondaryRequest : forall category owner input before emptied after buffers next_buffers
    raw next_raw left right position,
    take_owner owner (category_callback category) before =
      Some (owned_map category buffers raw, emptied) ->
    @RawResume (Term category) (Term category) (alias category) (alias category) maximum
      raw input (RawRequests (RawSecondary left right)) next_raw ->
    pair_at category position left right ->
    finish_owner_transfer AwaitComparison owner (category_callback category)
      (owned_map category next_buffers next_raw) emptied = Some after ->
    core_source owner (category_callback category) input before (Requests Secondary position) [] after
| SourceCompleted : forall category owner input before emptied after buffers next_buffers
    raw next_raw result,
    take_owner owner (category_callback category) before =
      Some (owned_map category buffers raw, emptied) ->
    @RawResume (Term category) (Term category) (alias category) (alias category) maximum
      raw input (RawCompletes result) next_raw ->
    finish_owner_transfer ComparisonDone owner (category_callback category)
      (owned_map category next_buffers next_raw) emptied = Some after ->
    core_source owner (category_callback category) input before (Completes result) [] after.

Theorem every_callback_request_has_its_original_typed_operand_pair :
  forall owner callback input before role position events after,
  core_source owner callback input before (Requests role position) events after ->
  exists category left right, callback = category_callback category /\ pair_at category position left right.
Proof.
  intros owner callback input before role position events after SOURCE.
  inversion SOURCE; subst;
    (eexists; eexists; eexists; split; [reflexivity|eassumption]).
Qed.

Theorem source_callback_preserves_the_live_continuation_and_all_other_complete_owners :
  forall owner callback input before reply events after,
  core_source owner callback input before reply events after ->
  forall head pending, task_owners head = [owner] ->
  pending_owners_valid (head :: pending) before ->
  pending_owners_valid (reply_prefix owner callback reply ++ pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros owner callback input before reply events after SOURCE.
  destruct SOURCE as [category owner input before emptied after buffers next_buffers raw next_raw left right position TAKE RAW PAIR REFILL
    |category owner input before emptied after buffers next_buffers raw next_raw left right position TAKE RAW PAIR REFILL
    |category owner input before emptied after buffers next_buffers raw next_raw result TAKE RAW DONE];
    intros head pending HEAD VALID.
  - destruct (taking_the_original_owned_head_preserves_all_parked_owners
      head owner pending (category_callback category) before (owned_map category buffers raw)
      emptied HEAD VALID TAKE) as [INFLIGHT BEFORE_FRAME].
    destruct (requested_child_resume_refills_only_its_detached_owner
      owner (category_callback category) pending (category_callback category) emptied
      (owned_map category next_buffers next_raw) after INFLIGHT REFILL) as [RESUMED AFTER_FRAME].
    split.
    + apply borrowed_child_shell_preserves_the_existing_owner_inventory. exact RESUMED.
    + eapply owner_frame_preservation_composes; eassumption.
  - destruct (taking_the_original_owned_head_preserves_all_parked_owners
      head owner pending (category_callback category) before (owned_map category buffers raw)
      emptied HEAD VALID TAKE) as [INFLIGHT BEFORE_FRAME].
    destruct (requested_child_resume_refills_only_its_detached_owner
      owner (category_callback category) pending (category_callback category) emptied
      (owned_map category next_buffers next_raw) after INFLIGHT REFILL) as [RESUMED AFTER_FRAME].
    split.
    + apply borrowed_child_shell_preserves_the_existing_owner_inventory. exact RESUMED.
    + eapply owner_frame_preservation_composes; eassumption.
  - change (Some emptied = Some after) in DONE. injection DONE as <-.
    destruct (taking_the_original_owned_head_preserves_all_parked_owners
      head owner pending (category_callback category) before (owned_map category buffers raw)
      emptied HEAD VALID TAKE) as [[REST [OUTSIDE EMPTY]] FRAME].
    split; assumption.
Qed.

Theorem a_requested_callback_refills_the_same_cell_with_its_returned_native_state :
  forall owner callback input before role position events after,
  core_source owner callback input before (Requests role position) events after ->
  exists category buffers raw,
    callback = category_callback category /\
    nth_error after owner = Some (Some (callback, owned_map category buffers raw)).
Proof.
  intros owner callback input before role position events after SOURCE.
  inversion SOURCE; subst;
    (eexists; eexists; eexists; split; [reflexivity|];
      eapply successful_write_contains_exactly_the_tagged_payload; eassumption).
Qed.

(** Discard has no Resume case: the original delivery path intercepts it. *)
Inductive discard_source : Task -> State -> State -> Prop :=
| DiscardBorrowed : forall borrowed cells,
    discard_source (Borrowed borrowed) cells cells
| DiscardOriginalStart : forall owner callback cells payload emptied,
    take_owner owner callback cells = Some (payload, emptied) ->
    discard_source (Start owner callback) cells emptied.

Theorem actual_discard_preserves_every_remaining_live_owner :
  forall task before after, discard_source task before after ->
  forall pending, pending_owners_valid (task :: pending) before ->
  pending_owners_valid pending after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros task before after SOURCE. destruct SOURCE; intros pending VALID.
  - split; [exact VALID|]. intros owner IN. reflexivity.
  - destruct (discarding_an_unstarted_head_does_not_resume_or_change_a_parked_owner
      owner callback pending callback cells payload emptied VALID H)
      as [REST [EMPTY FRAME]]. split; assumption.
Qed.

(** These corollaries fit the existing SourceStep exactly; they do not define
    another transition relation. The constructor-arm case still needs the
    existing ArmConstruction induction with this concrete make_map_box. *)
Theorem a_source_start_step_has_its_original_owned_local_footprint :
  forall arm_source owner callback pending before events next_mode after next,
  @GeneratedChildTraversal.GeneratedChildTraversal.SourceStep State arm_source core_source discard_source
    GeneratedChildTraversal.GeneratedChildTraversal.Run (Start owner callback :: pending)
    before events next_mode after next ->
  pending_owners_valid (Start owner callback :: pending) before ->
  pending_owners_valid after next /\ preserves_owner_frame (owner_refs pending) before next.
Proof.
  intros arm_source owner callback pending before events next_mode after next STEP VALID.
  inversion STEP; subst.
  eapply source_callback_preserves_the_live_continuation_and_all_other_complete_owners
      with (head := Start owner callback);
    [eassumption|reflexivity|exact VALID].
Qed.

Theorem a_source_resume_step_has_its_original_owned_local_footprint :
  forall arm_source mode owner callback pending before events next_mode after next,
  @GeneratedChildTraversal.GeneratedChildTraversal.SourceStep State arm_source core_source discard_source
    mode (Resume owner callback :: pending) before events next_mode after next ->
  pending_owners_valid (Resume owner callback :: pending) before ->
  pending_owners_valid after next /\ preserves_owner_frame (owner_refs pending) before next.
Proof.
  intros arm_source mode owner callback pending before events next_mode after next STEP VALID.
  inversion STEP; subst;
    try match goal with BAD : AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.not_resume (Resume _ _) = true |- _ => discriminate BAD end;
    (eapply source_callback_preserves_the_live_continuation_and_all_other_complete_owners
      with (head := Resume owner callback);
      [eassumption|reflexivity|exact VALID]).
Qed.
End OriginalSourceBinding.

Print Assumptions factory_keeps_the_original_rosters_unit_totals_and_callback.
Print Assumptions factory_adds_one_fresh_start_without_changing_parked_owners.
Print Assumptions every_callback_request_has_its_original_typed_operand_pair.
Print Assumptions source_callback_preserves_the_live_continuation_and_all_other_complete_owners.
Print Assumptions a_requested_callback_refills_the_same_cell_with_its_returned_native_state.
Print Assumptions actual_discard_preserves_every_remaining_live_owner.
Print Assumptions a_source_start_step_has_its_original_owned_local_footprint.
Print Assumptions a_source_resume_step_has_its_original_owned_local_footprint.
End GeneratedMapSourceOwnership.
