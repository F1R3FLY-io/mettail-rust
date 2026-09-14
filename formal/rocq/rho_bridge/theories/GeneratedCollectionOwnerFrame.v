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
From RhoBridge Require Import IndexedCopySlots.
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
End GeneratedCollectionOwnerFrame.
