(** Original-entry projection for the shared paid native next-based scan.
    This is a refinement of NativeHashBagBorrowedScan, not another iterator.
    [entry] names the immutable key/count stored at an original FULL slot.
    Counts are arbitrary natural numbers: neither positivity, their sum, nor
    the bag's transported total is a premise of entry visitation.

    The consumer reserves the entire native scan before constructing it,
    reserves each explicit next call before advancing, then calls its visitor
    exactly once for a returned pair. Visitor work, storage and any scheduled
    category tasks need their own reservations through the same callback.
    These theorems cover the native scan and its original pair projection;
    they do not supply an arbitrary visitor's cost or effect contract. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagHistory
  NativeHashBagBorrowedScan NativeHashBagScanBound.
Import ListNotations.

Module NativeHashBagEntryVisit.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagHistory.NativeHashBagHistory.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.
Import NativeHashBagScanBound.NativeHashBagScanBound.

Section OriginalEntries.
Context {Key : Type}.
Variable entry : nat -> Key * nat.

Theorem each_native_step_preserves_exact_original_pairs :
  forall before events yielded after,
  ScanStep before events yielded after -> valid_cursor before ->
  map entry (pending before) = map entry yielded ++ map entry (pending after).
Proof.
  intros before events yielded after STEP VALID.
  destruct (each_step_preserves_remaining_and_original_slot_order
    _ _ _ _ STEP VALID) as [_ [ORDER _]].
  now rewrite ORDER, map_app.
Qed.

Theorem every_native_prefix_preserves_exact_original_pairs :
  forall first rest trace output state,
  ScanPrefix first rest trace output state ->
  map entry (first ++ concat rest) =
    map entry output ++ map entry (pending state) /\
  length (map entry output) = event_count Yield trace.
Proof.
  intros first rest trace output state PREFIX.
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ PREFIX) as [_ [ORDER [_ [_ [_ [_ [_ [_ [_ YIELDS]]]]]]]]].
  split; [now rewrite ORDER, map_app|now rewrite length_map].
Qed.

Theorem a_stopped_native_scan_visits_all_original_pairs :
  forall first rest trace output state,
  ScanPrefix first rest trace output state -> phase state = Stopped ->
  map entry output = map entry (first ++ concat rest).
Proof.
  intros first rest trace output state PREFIX STOPPED.
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ PREFIX) as [[BALANCE [_ STOP]] [ORDER _]].
  specialize (STOP STOPPED).
  assert (EMPTY : pending state = []).
  { apply length_zero_iff_nil. lia. }
  rewrite EMPTY, app_nil_r in ORDER. now rewrite ORDER.
Qed.

Theorem original_pair_projection_keeps_the_existing_native_scan_allowance :
  forall table full first rest trace output state,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  source_entry_count table full = items table ->
  ScanPrefix first rest trace output state ->
  length (map entry output) <= items table /\
  weighted_counts borrowed_scan_weight (fun event => event_count event trace) <=
    borrowed_scan_work (items table) (historical_group_bound table).
Proof.
  intros table full first rest trace output state REACHABLE GROUPS COHERENCE PREFIX.
  split.
  - pose proof (every_actual_prefix_conserves_source_slots_and_events
      _ _ _ _ _ PREFIX) as [_ [ORDER _]].
    assert (WIDTH : length (first ++ concat rest) = items table).
    { unfold source_entry_count in COHERENCE. now rewrite GROUPS in COHERENCE. }
    rewrite ORDER, length_app in WIDTH. rewrite length_map. lia.
  - eapply native_item_count_admits_each_borrowed_scan_prefix; eassumption.
Qed.

End OriginalEntries.
End NativeHashBagEntryVisit.

Print Assumptions NativeHashBagEntryVisit.each_native_step_preserves_exact_original_pairs.
Print Assumptions NativeHashBagEntryVisit.every_native_prefix_preserves_exact_original_pairs.
Print Assumptions NativeHashBagEntryVisit.a_stopped_native_scan_visits_all_original_pairs.
Print Assumptions NativeHashBagEntryVisit.original_pair_projection_keeps_the_existing_native_scan_allowance.
