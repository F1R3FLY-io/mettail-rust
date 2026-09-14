(** Borrowed next-based scanning of the pinned native HashBag table.
    Source groups list original FULL bucket positions, not key values or a
    replacement runtime table. The source interpretation binds [full] to
    native control bytes, items to their count, and the current ordered list
    to BitMaskIter's lowest-set-bit enumeration. Small-table padding is EMPTY;
    the singleton still loads its static initial control group.

    This projects RawIterRange::new, next_impl(false), and RawIter::next.
    The consumer stops at its first None; repeated terminal calls and fold
    are different paths. GroupLoad counts one logical load of 16 control
    bytes, not one byte. Refusal before iterator construction has no events
    and is outside the initialized cursor below. No cost bound is assumed. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module NativeHashBagBorrowedScan.

Definition group_count buckets := 1 + (buckets - 1) / 16.
Definition source_groups buckets (full : nat -> bool) :=
  map (fun group => filter full
    (seq (group * 16) (Nat.min 16 (buckets - group * 16))))
    (seq 0 (group_count buckets)).

Inductive Phase := Ready | Searching | Stopped.
Record Cursor := cursor {
  group_index : nat;
  current_mask : list nat;
  future_groups : list (list nat);
  remaining : nat;
  phase : Phase
}.
Definition pending state := current_mask state ++ concat (future_groups state).
Definition valid_cursor state :=
  remaining state = length (pending state) /\
  (phase state = Searching -> 0 < remaining state) /\
  (phase state = Stopped -> remaining state = 0).
Definition initial_cursor first rest :=
  cursor 0 first rest (length (first ++ concat rest)) Ready.

Inductive Event := Construct | GroupLoad | OuterNext | MaskProbe | MaskClear
  | GroupAdvance | Yield.
Definition initial_events := [Construct; GroupLoad].

Inductive ScanStep : Cursor -> list Event -> list nat -> Cursor -> Prop :=
| NextStops : forall group mask rest,
    ScanStep (cursor group mask rest 0 Ready) [OuterNext] []
      (cursor group mask rest 0 Stopped)
| NextEnters : forall group mask rest count,
    ScanStep (cursor group mask rest (S count) Ready) [OuterNext] []
      (cursor group mask rest (S count) Searching)
| MaskYields : forall group position mask rest count,
    ScanStep (cursor group (position :: mask) rest (S count) Searching)
      [MaskProbe; MaskClear; Yield] [position]
      (cursor group mask rest count Ready)
| MaskAdvances : forall group next rest count,
    ScanStep (cursor group [] (next :: rest) (S count) Searching)
      [MaskProbe; GroupAdvance; GroupLoad] []
      (cursor (S group) next rest (S count) Searching).

Theorem construction_has_a_valid_cursor : forall first rest,
  valid_cursor (initial_cursor first rest).
Proof.
  intros. unfold valid_cursor, initial_cursor, pending. cbn.
  repeat split; try reflexivity; discriminate.
Qed.

Theorem each_step_preserves_remaining_and_original_slot_order :
  forall before events yielded after,
    ScanStep before events yielded after -> valid_cursor before ->
    valid_cursor after /\ pending before = yielded ++ pending after /\
    remaining before = length yielded + remaining after.
Proof.
  intros before events yielded after STEP VALID. destruct STEP;
    unfold valid_cursor, pending in *; cbn in *;
    destruct VALID as [BALANCE [SEARCH STOP]];
    repeat split; try reflexivity; try discriminate; try lia.
Qed.

Theorem an_empty_search_mask_has_an_unloaded_group : forall state,
  valid_cursor state -> phase state = Searching -> current_mask state = [] ->
  future_groups state <> [].
Proof.
  intros state [BALANCE [SEARCH STOP]] PHASE EMPTY NONE.
  specialize (SEARCH PHASE). unfold pending in BALANCE.
  rewrite EMPTY, NONE in BALANCE. cbn in BALANCE. lia.
Qed.

End NativeHashBagBorrowedScan.

Print Assumptions NativeHashBagBorrowedScan.construction_has_a_valid_cursor.
Print Assumptions NativeHashBagBorrowedScan.each_step_preserves_remaining_and_original_slot_order.
Print Assumptions NativeHashBagBorrowedScan.an_empty_search_mask_has_an_unloaded_group.
