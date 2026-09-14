(** Disjoint-cell preservation for the existing generated collection-owner
    inventory. IndexedCopySlots is already used by
    AdmittedCollectionComparisonOwnership to interpret by-value owner moves;
    these lemmas do not introduce a runtime owner registry or another driver.

    Equality preserves the complete tagged payload, not just its allocation
    credit. Instantiating A with the existing Owner Core therefore retains
    buffers, cursors, pending comparison and the other native Core fields.

    These are local storage facts. Actual generated execution must separately
    establish that live task-owner identities are distinct, fresh owners use
    newly appended cells, and each source action touches only its local owner.
    Untouched task suffixes alone do not imply these premises. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import IndexedCopySlots AdmittedCollectionComparisonOwnership
  AdmittedGeneratedCollectionScheduling.
Import ListNotations.
Import IndexedCopySlots.IndexedCopySlots.

Module GeneratedCollectionOwnerFrame.
Section Frames.
Context {A : Type}.

Theorem filling_another_cell_preserves_the_complete_parked_cell :
  forall changed entry (before after : @Slots A),
  fill changed entry before = Some after ->
  forall parked, changed <> parked ->
  nth_error after parked = nth_error before parked.
Proof.
  induction changed as [|changed IH]; intros entry before after FILL parked DIFFERENT;
    destruct before as [|head rest]; cbn [fill] in FILL; try discriminate.
  - destruct head; try discriminate. injection FILL as <-.
    destruct parked; [contradiction|reflexivity].
  - destruct (fill changed entry rest) as [updated|] eqn:UPDATE; try discriminate.
    injection FILL as <-. destruct parked as [|parked]; [reflexivity|].
    cbn [nth_error]. eapply IH; [exact UPDATE|lia].
Qed.

Theorem writing_another_cell_preserves_the_complete_parked_cell :
  forall expected actual value changed (before after : @Slots A),
  write_slot expected actual value changed before = Some after ->
  forall parked, changed <> parked ->
  nth_error after parked = nth_error before parked.
Proof.
  intros expected actual value changed before after WRITE parked DIFFERENT.
  unfold write_slot in WRITE. destruct (expected =? actual); try discriminate.
  eapply filling_another_cell_preserves_the_complete_parked_cell; eassumption.
Qed.

Theorem taking_another_cell_preserves_the_complete_parked_cell :
  forall changed expected (before : @Slots A) value after,
  take_slot changed expected before = Some (value, after) ->
  forall parked, changed <> parked ->
  nth_error after parked = nth_error before parked.
Proof.
  induction changed as [|changed IH]; intros expected before value after TAKE parked DIFFERENT;
    destruct before as [|head rest]; cbn [take_slot] in TAKE; try discriminate.
  - destruct head as [[actual found]|]; try discriminate.
    destruct (expected =? actual); try discriminate.
    injection TAKE as <- <-. destruct parked; [contradiction|reflexivity].
  - destruct (take_slot changed expected rest) as [[found updated]|] eqn:UPDATE;
      try discriminate.
    injection TAKE as <- <-. destruct parked as [|parked]; [reflexivity|].
    cbn [nth_error]. eapply IH; [exact UPDATE|lia].
Qed.

Theorem allocating_fresh_cells_preserves_every_existing_parked_cell :
  forall ceiling count (before after : @Slots A),
  allocate ceiling count before = Some after ->
  forall parked, parked < length before ->
  nth_error after parked = nth_error before parked.
Proof.
  intros ceiling count before after ALLOCATE parked EXISTING.
  apply allocation_exact in ALLOCATE as [AFTER _]. rewrite AFTER.
  now apply nth_error_app1.
Qed.

(** A frame records equality of complete cells for its original ghost owner
    names. It is a proposition about the existing inventory, not storage. *)
Definition preserves_owner_frame (owners : list nat) (before after : @Slots A) :=
  forall owner, In owner owners -> nth_error after owner = nth_error before owner.

Theorem owner_frame_preservation_composes : forall owners before middle after,
  preserves_owner_frame owners before middle ->
  preserves_owner_frame owners middle after ->
  preserves_owner_frame owners before after.
Proof. intros owners before middle after FIRST SECOND owner IN.
  rewrite (SECOND owner IN). exact (FIRST owner IN).
Qed.

Theorem take_and_refill_another_owner_preserves_the_parked_frame :
  forall owners changed expected actual value replacement (before emptied after : @Slots A),
  ~ In changed owners ->
  take_slot changed expected before = Some (value, emptied) ->
  write_slot expected actual replacement changed emptied = Some after ->
  preserves_owner_frame owners before after.
Proof.
  intros owners changed expected actual value replacement before emptied after
    OUTSIDE TAKE WRITE owner IN.
  assert (DIFFERENT : changed <> owner) by (intros SAME; subst; contradiction).
  rewrite (writing_another_cell_preserves_the_complete_parked_cell
    expected actual replacement changed emptied after WRITE owner DIFFERENT).
  eapply taking_another_cell_preserves_the_complete_parked_cell; eassumption.
Qed.
End Frames.

Print Assumptions filling_another_cell_preserves_the_complete_parked_cell.
Print Assumptions writing_another_cell_preserves_the_complete_parked_cell.
Print Assumptions taking_another_cell_preserves_the_complete_parked_cell.
Print Assumptions allocating_fresh_cells_preserves_every_existing_parked_cell.
Print Assumptions owner_frame_preservation_composes.
Print Assumptions take_and_refill_another_owner_preserves_the_parked_frame.
(** Selected-cell facts supplement the disjoint-cell laws above. Their value
    is the moved original payload, never a copy created by the proof model. *)
Section SelectedCells.
Context {A : Type}.
Theorem successful_fill_contains_exactly_the_written_payload :
  forall index entry (before after : @Slots A),
  fill index entry before = Some after -> nth_error after index = Some (Some entry).
Proof.
  induction index as [|index IH]; intros entry before after FILL;
    destruct before as [|head rest]; cbn [fill] in FILL; try discriminate.
  - destruct head; try discriminate. injection FILL as <-. reflexivity.
  - destruct (fill index entry rest) as [updated|] eqn:UPDATE; try discriminate.
    injection FILL as <-. cbn [nth_error]. eapply IH; exact UPDATE.
Qed.
Theorem successful_write_contains_exactly_the_tagged_payload :
  forall expected actual value index (before after : @Slots A),
  write_slot expected actual value index before = Some after ->
  nth_error after index = Some (Some (actual, value)).
Proof.
  intros expected actual value index before after WRITE.
  unfold write_slot in WRITE. destruct (expected =? actual); try discriminate.
  eapply successful_fill_contains_exactly_the_written_payload; exact WRITE.
Qed.
Theorem successful_take_moves_the_original_payload_and_empties_its_cell :
  forall index expected (before : @Slots A) value after,
  take_slot index expected before = Some (value, after) ->
  nth_error before index = Some (Some (expected, value)) /\
  nth_error after index = Some None /\ length after = length before.
Proof.
  induction index as [|index IH]; intros expected before value after TAKE;
    destruct before as [|head rest]; cbn [take_slot] in TAKE; try discriminate.
  - destruct head as [[actual found]|]; try discriminate.
    destruct (expected =? actual) eqn:TAG; try discriminate.
    apply Nat.eqb_eq in TAG. subst actual. injection TAKE as <- <-.
    repeat split; reflexivity.
  - destruct (take_slot index expected rest) as [[found updated]|] eqn:UPDATE;
      try discriminate.
    injection TAKE as <- <-.
    destruct (IH expected rest found updated UPDATE) as [ORIGINAL [EMPTY WIDTH]].
    cbn [nth_error length]. repeat split; auto.
Qed.
End SelectedCells.

(** These are invariants of the EXISTING proof-only owner-slot interpretation.
    The transient owner is precisely the value returned by take_owner to the
    by-value callback. No new registry, task, executor or persistent inflight
    storage is introduced. Buffer-allocation uniqueness does not imply these
    task-owner invariants; the following lemmas establish their distinct moves.

    Rust association remains explicit: each actual Map construction must use
    the fresh append/write interpretation; a callback may mutate only its
    detached Box and refill that same owner cell on Compare; normal discard
    consumes only its popped owner. A complete SourceStep/ChildTraversal lift
    still needs these operational bindings, rather than assuming that an
    untouched task list already guarantees an untouched owner payload. *)
Section OriginalOwnerMoves.
Context {Core : Type}.
Local Notation Owner := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Owner Core).
Local Notation Task := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Task.
Local Notation owner_refs := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.owner_refs.
Local Notation task_owners := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.task_owners.
Local Notation Start := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Start.
Local Notation Resume := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Resume.
Local Notation take_owner := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner Core).
Local Notation finish_owner_transfer := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.finish_owner_transfer Core).
Local Notation AwaitComparison := AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.AwaitComparison.

Definition live_owner (cells : @Slots Owner) index :=
  exists tag payload, nth_error cells index = Some (Some (tag, payload)).
Definition pending_owners_valid (pending : list Task) (cells : @Slots Owner) :=
  NoDup (owner_refs pending) /\ Forall (live_owner cells) (owner_refs pending).
Definition inflight_owner_valid owner pending (emptied : @Slots Owner) :=
  pending_owners_valid pending emptied /\
  ~ In owner (owner_refs pending) /\ nth_error emptied owner = Some None.

Lemma original_task_head_partitions_owner_references : forall task pending,
  owner_refs (task :: pending) = task_owners task ++ owner_refs pending.
Proof. reflexivity. Qed.
Lemma a_live_owner_is_an_existing_cell : forall cells owner,
  live_owner cells owner -> owner < length cells.
Proof.
  intros cells owner [tag [payload PRESENT]]. apply nth_error_Some.
  rewrite PRESENT. discriminate.
Qed.
Lemma complete_frame_preservation_retains_pending_owner_validity :
  forall pending before after,
  pending_owners_valid pending before ->
  preserves_owner_frame (owner_refs pending) before after ->
  pending_owners_valid pending after.
Proof.
  intros pending before after [UNIQUE LIVE] FRAME. split; [exact UNIQUE|].
  apply Forall_forall. intros owner IN.
  rewrite Forall_forall in LIVE. destruct (LIVE owner IN) as [tag [payload PRESENT]].
  exists tag, payload. rewrite (FRAME owner IN). exact PRESENT.
Qed.
Theorem pending_and_detached_owner_identities_are_unique : forall owner pending emptied,
  inflight_owner_valid owner pending emptied -> NoDup (owner :: owner_refs pending).
Proof. intros owner pending emptied [[UNIQUE LIVE] [OUTSIDE EMPTY]]. constructor; assumption. Qed.

Theorem fresh_appended_map_owner_preserves_live_task_ownership :
  forall ceiling pending before extended after tag (payload : Owner) callback,
  pending_owners_valid pending before ->
  allocate ceiling 1 before = Some extended ->
  write_slot tag tag payload (length before) extended = Some after ->
  pending_owners_valid (Start (length before) callback :: pending) after /\
  preserves_owner_frame (owner_refs pending) before after.
Proof.
  intros ceiling pending before extended after tag payload callback VALID ALLOCATE WRITE.
  assert (BOUND : forall owner, In owner (owner_refs pending) -> owner < length before).
  { intros owner IN. destruct VALID as [UNIQUE LIVE]. rewrite Forall_forall in LIVE.
    apply a_live_owner_is_an_existing_cell. apply LIVE. exact IN. }
  assert (FRAME : preserves_owner_frame (owner_refs pending) before after).
  { intros owner IN.
    rewrite (writing_another_cell_preserves_the_complete_parked_cell
      tag tag payload (length before) extended after WRITE owner) by (specialize (BOUND owner IN); lia).
    eapply allocating_fresh_cells_preserves_every_existing_parked_cell;
      [exact ALLOCATE|apply BOUND; exact IN]. }
  split; [|exact FRAME].
  destruct (complete_frame_preservation_retains_pending_owner_validity pending before after VALID FRAME)
    as [UNIQUE LIVE].
  unfold pending_owners_valid. rewrite original_task_head_partitions_owner_references.
  cbn [AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.task_owners app].
  split.
  - constructor; [intro IN; specialize (BOUND (length before) IN); lia|exact UNIQUE].
  - constructor; [|exact LIVE]. exists tag, payload.
    eapply successful_write_contains_exactly_the_tagged_payload; exact WRITE.
Qed.

Theorem taking_the_original_owned_head_preserves_all_parked_owners :
  forall task owner pending tag before (payload : Owner) emptied,
  task_owners task = [owner] ->
  pending_owners_valid (task :: pending) before ->
  take_owner owner tag before = Some (payload, emptied) ->
  inflight_owner_valid owner pending emptied /\
  preserves_owner_frame (owner_refs pending) before emptied.
Proof.
  intros task owner pending tag before payload emptied HEAD [UNIQUE LIVE] TAKE.
  rewrite original_task_head_partitions_owner_references, HEAD in UNIQUE, LIVE.
  cbn [app] in UNIQUE, LIVE.
  inversion UNIQUE as [|selected remaining OUTSIDE REST_UNIQUE]; subst.
  inversion LIVE as [|selected remaining OWNED REST_LIVE]; subst.
  assert (FRAME : preserves_owner_frame (owner_refs pending) before emptied).
  { intros parked IN. eapply taking_another_cell_preserves_the_complete_parked_cell;
      [exact TAKE|]. intro SAME. subst parked. contradiction. }
  split; [|exact FRAME]. unfold inflight_owner_valid. split.
  - eapply complete_frame_preservation_retains_pending_owner_validity;
      [split; eassumption|exact FRAME].
  - split; [exact OUTSIDE|].
    exact (proj1 (proj2 (successful_take_moves_the_original_payload_and_empties_its_cell
      owner tag before payload emptied TAKE))).
Qed.

Theorem requested_child_resume_refills_only_its_detached_owner :
  forall owner callback pending tag emptied (replacement : Owner) after,
  inflight_owner_valid owner pending emptied ->
  finish_owner_transfer AwaitComparison owner tag replacement emptied = Some after ->
  pending_owners_valid (Resume owner callback :: pending) after /\
  preserves_owner_frame (owner_refs pending) emptied after.
Proof.
  intros owner callback pending tag emptied replacement after [VALID [OUTSIDE EMPTY]] REFILL.
  change (write_slot tag tag replacement owner emptied = Some after) in REFILL.
  assert (FRAME : preserves_owner_frame (owner_refs pending) emptied after).
  { intros parked IN. eapply writing_another_cell_preserves_the_complete_parked_cell;
      [exact REFILL|]. intro SAME. subst parked. contradiction. }
  split; [|exact FRAME].
  destruct (complete_frame_preservation_retains_pending_owner_validity pending emptied after VALID FRAME)
    as [UNIQUE LIVE].
  unfold pending_owners_valid. rewrite original_task_head_partitions_owner_references.
  cbn [AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.task_owners app].
  split.
  - constructor; assumption.
  - constructor; [|exact LIVE]. exists tag, replacement.
    eapply successful_write_contains_exactly_the_tagged_payload; exact REFILL.
Qed.

Theorem a_finished_or_failed_callback_keeps_only_the_remaining_task_owners :
  forall exit owner pending tag emptied (replacement : Owner),
  inflight_owner_valid owner pending emptied -> exit <> AwaitComparison ->
  finish_owner_transfer exit owner tag replacement emptied = Some emptied /\
  pending_owners_valid pending emptied /\ nth_error emptied owner = Some None.
Proof.
  intros exit owner pending tag emptied replacement [VALID [OUTSIDE EMPTY]] TERMINAL.
  split.
  - destruct exit; [contradiction|reflexivity|reflexivity].
  - split; assumption.
Qed.

Theorem discarding_an_unstarted_head_does_not_resume_or_change_a_parked_owner :
  forall owner callback pending tag before (payload : Owner) emptied,
  pending_owners_valid (Start owner callback :: pending) before ->
  take_owner owner tag before = Some (payload, emptied) ->
  pending_owners_valid pending emptied /\ nth_error emptied owner = Some None /\
  preserves_owner_frame (owner_refs pending) before emptied.
Proof.
  intros owner callback pending tag before payload emptied VALID TAKE.
  destruct (taking_the_original_owned_head_preserves_all_parked_owners
    (Start owner callback) owner pending tag before payload emptied eq_refl VALID TAKE)
    as [[REST [OUTSIDE EMPTY]] FRAME]. split; [exact REST|]. split; assumption.
Qed.

Theorem borrowed_child_shell_preserves_the_existing_owner_inventory :
  forall child pending cells,
  pending_owners_valid pending cells ->
  pending_owners_valid
    (AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Borrowed child :: pending) cells.
Proof. intros child pending cells VALID. exact VALID. Qed.
End OriginalOwnerMoves.

Print Assumptions successful_fill_contains_exactly_the_written_payload.
Print Assumptions successful_write_contains_exactly_the_tagged_payload.
Print Assumptions successful_take_moves_the_original_payload_and_empties_its_cell.
Print Assumptions original_task_head_partitions_owner_references.
Print Assumptions a_live_owner_is_an_existing_cell.
Print Assumptions complete_frame_preservation_retains_pending_owner_validity.
Print Assumptions pending_and_detached_owner_identities_are_unique.
Print Assumptions fresh_appended_map_owner_preserves_live_task_ownership.
Print Assumptions taking_the_original_owned_head_preserves_all_parked_owners.
Print Assumptions requested_child_resume_refills_only_its_detached_owner.
Print Assumptions a_finished_or_failed_callback_keeps_only_the_remaining_task_owners.
Print Assumptions discarding_an_unstarted_head_does_not_resume_or_change_a_parked_owner.
Print Assumptions borrowed_child_shell_preserves_the_existing_owner_inventory.
End GeneratedCollectionOwnerFrame.
