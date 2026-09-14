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

Definition event_unit wanted actual :=
  match wanted, actual with
  | Construct, Construct | GroupLoad, GroupLoad | OuterNext, OuterNext
  | MaskProbe, MaskProbe | MaskClear, MaskClear
  | GroupAdvance, GroupAdvance | Yield, Yield => 1
  | _, _ => 0
  end.
Fixpoint event_count wanted events :=
  match events with
  | [] => 0
  | event :: rest => event_unit wanted event + event_count wanted rest
  end.
Lemma event_count_app : forall wanted first rest,
  event_count wanted (first ++ rest) =
  event_count wanted first + event_count wanted rest.
Proof.
  intros wanted first. induction first; intros; cbn; [reflexivity|].
  rewrite IHfirst. lia.
Qed.

Definition outstanding_next state :=
  match phase state with Ready => 0 | Searching | Stopped => 1 end.
Inductive ScanPrefix first rest : list Event -> list nat -> Cursor -> Prop :=
| PrefixInitial : ScanPrefix first rest initial_events [] (initial_cursor first rest)
| PrefixStep : forall trace output before events yielded after,
    ScanPrefix first rest trace output before ->
    ScanStep before events yielded after ->
    ScanPrefix first rest (trace ++ events) (output ++ yielded) after.

Definition prefix_facts first rest trace output state :=
  valid_cursor state /\
  first ++ concat rest = output ++ pending state /\
  event_count Construct trace = 1 /\
  event_count GroupLoad trace = event_count GroupAdvance trace + 1 /\
  event_count MaskProbe trace = event_count Yield trace + event_count GroupAdvance trace /\
  event_count MaskClear trace = event_count Yield trace /\
  remaining state + event_count Yield trace = length (first ++ concat rest) /\
  event_count OuterNext trace = event_count Yield trace + outstanding_next state /\
  event_count GroupLoad trace + length (future_groups state) = S (length rest) /\
  event_count Yield trace = length output.

Theorem every_actual_prefix_conserves_source_slots_and_events :
  forall first rest trace output state,
    ScanPrefix first rest trace output state ->
    prefix_facts first rest trace output state.
Proof.
  intros first rest trace output state PREFIX. induction PREFIX.
  - unfold prefix_facts. split; [apply construction_has_a_valid_cursor|].
    cbn [initial_events initial_cursor pending event_count event_unit
      remaining future_groups outstanding_next phase]. repeat split; lia.
  - unfold prefix_facts in *.
    destruct IHPREFIX as [VALID [ORDER [CTOR [LOAD [PROBE [CLEAR
      [REMAIN [NEXT [GROUPS YIELDS]]]]]]]]].
    pose proof (each_step_preserves_remaining_and_original_slot_order
      _ _ _ _ H VALID) as [AFTER [SLOTS ITEMS]].
    split; [exact AFTER|]. split.
    { rewrite ORDER, SLOTS, app_assoc. reflexivity. }
    repeat rewrite event_count_app.
    destruct H; cbn [event_count event_unit outstanding_next phase remaining
      future_groups] in *; repeat rewrite length_app in *;
      cbn [length] in *; repeat split; lia.
Qed.

Lemma native_source_groups_have_the_exact_group_count : forall buckets full,
  length (source_groups buckets full) = group_count buckets.
Proof. intros. unfold source_groups. rewrite length_map, length_seq. reflexivity. Qed.

Theorem native_source_groups_always_have_an_initial_load : forall buckets full,
  exists first rest, source_groups buckets full = first :: rest.
Proof.
  intros buckets full. destruct (source_groups buckets full) as [|first rest] eqn:GROUPS.
  - pose proof (native_source_groups_have_the_exact_group_count buckets full).
    rewrite GROUPS in H. unfold group_count in H. cbn in H. lia.
  - eauto.
Qed.

End NativeHashBagBorrowedScan.

Print Assumptions NativeHashBagBorrowedScan.construction_has_a_valid_cursor.
Print Assumptions NativeHashBagBorrowedScan.each_step_preserves_remaining_and_original_slot_order.
Print Assumptions NativeHashBagBorrowedScan.an_empty_search_mask_has_an_unloaded_group.
Print Assumptions NativeHashBagBorrowedScan.event_count_app.
Print Assumptions NativeHashBagBorrowedScan.every_actual_prefix_conserves_source_slots_and_events.
Print Assumptions NativeHashBagBorrowedScan.native_source_groups_have_the_exact_group_count.
Print Assumptions NativeHashBagBorrowedScan.native_source_groups_always_have_an_initial_load.
