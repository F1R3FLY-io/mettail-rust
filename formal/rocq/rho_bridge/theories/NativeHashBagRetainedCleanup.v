(** Normal cleanup of the native table retained by try_rebuild_entries_with.
    Its input is a Vec, not a consuming HashBag iterator. RawTable::drop
    invokes drop_inner_table, which skips the singleton, conditionally scans
    allocated nonempty tables whose entry type needs Drop, then frees the
    allocation. This scan starts FRESH; no earlier borrowed cursor is reused.

    The wrapper below selects an existing ScanPrefix, not a second iterator.
    Source association binds table scalars, FULL controls and needs_drop to
    the actual retained HashMap<T, usize>. Full key-destructor receipts,
    allocation-layout recovery and the allocator call are separate from scan
    control. Normal return only; no panic-unwind or allocator/RSS claim. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia Sorting.Permutation.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagHistory
  NativeHashBagBorrowedScan NativeHashBagScanBound NativeHashBagOwnedScan
  GeneratedBindingOutputReservation RequiredHashBagBindingReservation.
Import ListNotations.

Module NativeHashBagRetainedCleanup.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagHistory.NativeHashBagHistory.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.
Import NativeHashBagScanBound.NativeHashBagScanBound.
Import NativeHashBagOwnedScan.NativeHashBagOwnedScan.

Definition allocated table := negb (buckets table =? 1).
Definition scans table needs_drop :=
  allocated table && needs_drop && negb (items table =? 0).

Definition fresh_drop_scan table full needs_drop trace output : Prop :=
  if scans table needs_drop then
    exists first rest final,
      source_groups (buckets table) full = first :: rest /\
      ScanPrefix first rest trace output final /\ phase final = Stopped
  else trace = [] /\ output = [].

Theorem skipped_retained_cleanup_has_no_scan :
  forall table full needs_drop trace output,
  scans table needs_drop = false ->
  fresh_drop_scan table full needs_drop trace output -> trace = [] /\ output = [].
Proof.
  intros table full needs_drop trace output SKIP RUN.
  unfold fresh_drop_scan in RUN. now rewrite SKIP in RUN.
Qed.

Theorem retained_cleanup_yields_exact_original_slots :
  forall table full needs_drop trace output,
  scans table needs_drop = true ->
  fresh_drop_scan table full needs_drop trace output ->
  output = concat (source_groups (buckets table) full).
Proof.
  intros table full needs_drop trace output SCANS RUN.
  unfold fresh_drop_scan in RUN. rewrite SCANS in RUN.
  destruct RUN as [first [rest [final [GROUPS [PREFIX STOPPED]]]]].
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ PREFIX) as FACTS.
  destruct FACTS as [VALID [ORDER REST]].
  assert (ZERO : remaining final = 0).
  { destruct VALID as [_ [_ STOP]]. now apply STOP. }
  rewrite (zero_remaining_has_no_pending_slots final VALID ZERO), app_nil_r in ORDER.
  rewrite GROUPS. cbn [concat]. symmetry. exact ORDER.
Qed.

Theorem retained_cleanup_cursor_has_one_historical_envelope :
  forall table full needs_drop trace output,
  Reachable table -> fresh_drop_scan table full needs_drop trace output ->
  forall event, event_count event trace <=
    if scans table needs_drop then scan_allowance event
      (source_entry_count table full) (historical_group_bound table) else 0.
Proof.
  intros table full needs_drop trace output REACHABLE RUN event.
  unfold fresh_drop_scan in RUN. destruct (scans table needs_drop) eqn:SCANS.
  - destruct RUN as [first [rest [final [GROUPS [PREFIX STOPPED]]]]].
    eapply historical_capacity_covers_every_actual_scan_prefix; eassumption.
  - destruct RUN as [-> _]. reflexivity.
Qed.

(** Source wrapper invocation counts accompany the ordered output slot list.
    BucketDropDispatch invokes the FULL independent-root destructor; it does
    not charge its body as one unit. RecoverAllocationLayout and FreeAllocation
    name native invocations, not fixed allocator costs or a layout proof.
    Source association must bind each output slot to Bucket::as_ptr() and the
    actual retained tuple. No Bucket::read occurs on this retained-table path. *)
Inductive CleanupEvent := EnterTableDrop | CheckSingleton | CheckNeedsDrop
  | CheckItems | BucketDropDispatch | BucketRead | RecoverAllocationLayout
  | FreeAllocation.

Definition wrapper_count table needs_drop (output : list nat) event :=
  match event with
  | EnterTableDrop | CheckSingleton => 1
  | CheckNeedsDrop | RecoverAllocationLayout | FreeAllocation =>
      if allocated table then 1 else 0
  | CheckItems => if allocated table && needs_drop then 1 else 0
  | BucketDropDispatch => length output
  | BucketRead => 0
  end.

Theorem retained_wrapper_has_no_moves_and_exact_dispatch_counts :
  forall table needs_drop output,
  wrapper_count table needs_drop output BucketRead = 0 /\
  wrapper_count table needs_drop output BucketDropDispatch = length output /\
  wrapper_count table needs_drop output FreeAllocation =
    (if allocated table then 1 else 0).
Proof. intros. exact (conj eq_refl (conj eq_refl eq_refl)). Qed.

Import GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.

(** The native physical order need not equal the reconstruction model's list
    order. SOURCE associates physical FULL slots to retained OWNERSHIP
    OCCURRENCES by permutation, never by key equality or address quotienting.
    On Insert refusal, pending includes the already-moved current input key.
    Existing receipt validity covers full root bodies; this theorem only
    transfers those receipts, not native flat scan or allocation costs. *)
Theorem retained_native_order_preserves_existing_root_allowances :
  forall table full needs_drop trace output (slot_owner : nat -> nat)
    (receipt : nat -> OutputReceipt) original retained discarded pending event,
  fresh_drop_scan table full needs_drop trace output ->
  Permutation (map slot_owner (concat (source_groups (buckets table) full))) retained ->
  Permutation original (retained ++ discarded ++ pending) ->
  Forall bounded (map receipt original) ->
  sum_counts output_root (map receipt (map slot_owner output)) event +
    sum_counts output_root (map receipt discarded) event +
    sum_counts output_root (map receipt pending) event <=
  sum_counts output_credit (map receipt original) event.
Proof.
  intros table full needs_drop trace output slot_owner receipt original
    retained discarded pending event RUN SOURCE PARTITION BOUNDED.
  pose proof
    (RequiredHashBagBindingReservation.RequiredHashBagBindingReservation.partitioned_partial_root_cleanup_is_covered
      receipt original retained discarded pending event PARTITION BOUNDED) as COVER.
  destruct (scans table needs_drop) eqn:SCANS.
  - pose proof (retained_cleanup_yields_exact_original_slots
      _ _ _ _ _ SCANS RUN) as OUTPUT.
    assert (RECEIPTS : Permutation (map receipt (map slot_owner output))
      (map receipt retained)).
    { apply Permutation_map. now rewrite OUTPUT. }
    rewrite (sum_counts_permutation OutputReceipt output_root _ _ RECEIPTS event).
    exact COVER.
  - destruct (skipped_retained_cleanup_has_no_scan
      _ _ _ _ _ SCANS RUN) as [_ OUTPUT].
    rewrite OUTPUT. change (0 +
      sum_counts output_root (map receipt discarded) event +
      sum_counts output_root (map receipt pending) event <=
      sum_counts output_credit (map receipt original) event).
    lia.
Qed.

End NativeHashBagRetainedCleanup.

Print Assumptions NativeHashBagRetainedCleanup.skipped_retained_cleanup_has_no_scan.
Print Assumptions NativeHashBagRetainedCleanup.retained_cleanup_yields_exact_original_slots.
Print Assumptions NativeHashBagRetainedCleanup.retained_cleanup_cursor_has_one_historical_envelope.
Print Assumptions NativeHashBagRetainedCleanup.retained_wrapper_has_no_moves_and_exact_dispatch_counts.
Print Assumptions NativeHashBagRetainedCleanup.retained_native_order_preserves_existing_root_allowances.
