(** FullBucketsIndices source frontiers during native resize.
    raw.rs:2808 always loads the first aligned group. next:3991 checks items
    before next_impl:3941 pops local mask bits or advances an aligned group.
    The definitions below only project those fields into the existing Cursor;
    they introduce no second scanner or assumed trace-cost bound.

    Source association binds group_first_index and ctrl offset to 16*group,
    local bits to the original ordered FULL mask, and unread groups to the
    immutable original controls. The successful-return cut includes items--.
    Padding is EMPTY. Native bit operations, pointer validity and word bounds
    remain explicit source obligations, not consequences of Nat notation.
    Hash callbacks, target occupancy, copies and allocation release are separate. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RhoBridge Require Import NativeHashBagBorrowedScan NativeHashBagScanBound.
Import ListNotations.

Module NativeHashBagResizeScan.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.
Import NativeHashBagScanBound.NativeHashBagScanBound.

Definition absolute_bits base (bits : list nat) := map (fun bit => base + bit) bits.
Definition indices_frontier group bits unread items phase :=
  cursor group (absolute_bits (16 * group) bits) unread items phase.

Theorem indices_constructor_is_the_existing_initial_cursor :
  forall bits unread items,
  items = length (absolute_bits 0 bits ++ concat unread) ->
  indices_frontier 0 bits unread items Ready =
    initial_cursor (absolute_bits 0 bits) unread.
Proof. intros bits unread items COUNT. subst items. reflexivity. Qed.

Theorem indices_zero_guard_stops_without_loading : forall group bits unread,
  ScanStep (indices_frontier group bits unread 0 Ready) [OuterNext] []
    (indices_frontier group bits unread 0 Stopped).
Proof. intros. apply NextStops. Qed.

Theorem indices_positive_guard_enters_the_same_search : forall group bits unread items,
  ScanStep (indices_frontier group bits unread (S items) Ready) [OuterNext] []
    (indices_frontier group bits unread (S items) Searching).
Proof. intros. apply NextEnters. Qed.

Theorem indices_lowest_bit_return_is_the_original_absolute_slot :
  forall group bit bits unread items,
  ScanStep (indices_frontier group (bit :: bits) unread (S items) Searching)
    [MaskProbe; MaskClear; Yield] [16 * group + bit]
    (indices_frontier group bits unread items Ready).
Proof. intros. unfold indices_frontier, absolute_bits. cbn [map]. apply MaskYields. Qed.

Theorem indices_exhausted_mask_loads_the_next_original_group :
  forall group next unread items,
  ScanStep (indices_frontier group []
      (absolute_bits (16 * S group) next :: unread) (S items) Searching)
    [MaskProbe; GroupAdvance; GroupLoad] []
    (indices_frontier (S group) next unread (S items) Searching).
Proof. intros. unfold indices_frontier, absolute_bits. cbn [map]. apply MaskAdvances. Qed.

Theorem indices_output_addition_stays_in_the_native_table :
  forall buckets word_limit group bit,
  buckets <= word_limit -> bit < Nat.min 16 (buckets - 16 * group) ->
  16 * group + bit < buckets /\ 16 * group + bit < word_limit.
Proof.
  intros buckets word_limit group bit WORD BIT.
  pose proof (Nat.le_min_r 16 (buckets - 16 * group)). lia.
Qed.

Lemma indices_reload_uses_the_actual_base_increment : forall group,
  16 * group + 16 = 16 * S group.
Proof. intros. lia. Qed.

Theorem indices_prefix_preserves_original_source_order_and_items :
  forall buckets full bits unread trace output state native_items,
  source_groups buckets full = absolute_bits 0 bits :: unread ->
  length (concat (source_groups buckets full)) = native_items ->
  ScanPrefix (absolute_bits 0 bits) unread trace output state ->
  concat (source_groups buckets full) = output ++ pending state /\
    remaining state + length output = native_items.
Proof.
  intros buckets full bits unread trace output state native_items GROUPS COHERENCE PREFIX.
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ PREFIX) as [VALID [ORDER REST]].
  split.
  - rewrite GROUPS. cbn [concat]. exact ORDER.
  - destruct VALID as [COUNT _]. rewrite GROUPS in COHERENCE.
    cbn [concat] in COHERENCE. rewrite ORDER, length_app in COHERENCE. lia.
Qed.

End NativeHashBagResizeScan.

Print Assumptions NativeHashBagResizeScan.indices_constructor_is_the_existing_initial_cursor.
Print Assumptions NativeHashBagResizeScan.indices_zero_guard_stops_without_loading.
Print Assumptions NativeHashBagResizeScan.indices_positive_guard_enters_the_same_search.
Print Assumptions NativeHashBagResizeScan.indices_lowest_bit_return_is_the_original_absolute_slot.
Print Assumptions NativeHashBagResizeScan.indices_exhausted_mask_loads_the_next_original_group.
Print Assumptions NativeHashBagResizeScan.indices_output_addition_stays_in_the_native_table.
Print Assumptions NativeHashBagResizeScan.indices_reload_uses_the_actual_base_increment.
Print Assumptions NativeHashBagResizeScan.indices_prefix_preserves_original_source_order_and_items.
