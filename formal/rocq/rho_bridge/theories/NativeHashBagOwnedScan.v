(** Consuming prefixes and normal iterator cleanup share one native cursor.
    RawIntoIter::next delegates to RawIter::next and moves the yielded record;
    RawIntoIter::drop invokes drop_elements on that SAME remaining RawIter.
    The relation below merely composes existing ScanStep transitions. It adds
    no iterator engine, duplicate initial load, or key destruction cost.

    Normal cleanup starts at a returned Ready or Stopped frontier. If the key
    type needs no destructor, or remaining is zero, no cleanup scan occurs.
    Otherwise the existing next-based loop yields remaining original slots.
    Owner/allocation transfer, owned record reads, full root destructors and
    conditional deallocation require their separate source-bound receipts.
    Panic unwinding and allocator/RSS bounds are outside this projection. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagHistory
  NativeHashBagBorrowedScan NativeHashBagScanBound.
Import ListNotations.

Module NativeHashBagOwnedScan.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagHistory.NativeHashBagHistory.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.
Import NativeHashBagScanBound.NativeHashBagScanBound.

Inductive ScanContinuation : Cursor -> list Event -> list nat -> Cursor -> Prop :=
| ContinueRefl : forall state, ScanContinuation state [] [] state
| ContinueStep : forall before events yielded middle trace output after,
    ScanStep before events yielded middle ->
    ScanContinuation middle trace output after ->
    ScanContinuation before (events ++ trace) (yielded ++ output) after.

Theorem continuing_an_actual_prefix_is_one_original_scan :
  forall first rest prefix moved before trace output after,
  ScanPrefix first rest prefix moved before ->
  ScanContinuation before trace output after ->
  ScanPrefix first rest (prefix ++ trace) (moved ++ output) after.
Proof.
  intros first rest prefix moved before trace output after PREFIX CONT.
  revert prefix moved PREFIX. induction CONT as
    [state|before events yielded middle trace output after STEP CONT IH];
    intros prefix moved PREFIX.
  - now rewrite !app_nil_r.
  - rewrite !app_assoc. apply IH.
    eapply PrefixStep; [exact PREFIX|exact STEP].
Qed.

Theorem continuation_preserves_exact_pending_slots :
  forall before trace output after,
  ScanContinuation before trace output after -> valid_cursor before ->
  valid_cursor after /\ pending before = output ++ pending after /\
  remaining before = length output + remaining after.
Proof.
  intros before trace output after CONT. induction CONT as
    [state|before events yielded middle trace output after STEP CONT IH]; intro VALID.
  - exact (conj VALID (conj eq_refl eq_refl)).
  - destruct (each_step_preserves_remaining_and_original_slot_order
      _ _ _ _ STEP VALID) as [MIDDLE [SLOTS ITEMS]].
    destruct (IH MIDDLE) as [AFTER [TAIL REST]].
    split; [exact AFTER|]. split.
    + rewrite SLOTS, TAIL, app_assoc. reflexivity.
    + rewrite length_app. lia.
Qed.

Theorem zero_remaining_has_no_pending_slots : forall state,
  valid_cursor state -> remaining state = 0 -> pending state = [].
Proof.
  intros state [COUNT _] ZERO. destruct (pending state); [reflexivity|].
  cbn [length] in COUNT. lia.
Qed.

Theorem terminal_continuation_yields_exact_pending_slots :
  forall before trace output after,
  ScanContinuation before trace output after -> valid_cursor before ->
  phase after = Stopped -> output = pending before.
Proof.
  intros before trace output after CONT VALID STOPPED.
  destruct (continuation_preserves_exact_pending_slots _ _ _ _ CONT VALID)
    as [AFTER [SLOTS COUNT]].
  assert (ZERO : remaining after = 0).
  { destruct AFTER as [_ [_ STOP]]. now apply STOP. }
  rewrite (zero_remaining_has_no_pending_slots after AFTER ZERO), app_nil_r in SLOTS.
  symmetry. exact SLOTS.
Qed.

(** Exhaustion need not include a terminal next call: after the last Some,
    remaining is already zero and normal drop skips its scan entirely. *)
Theorem exhausted_consuming_and_cleanup_partition_original_slots :
  forall first rest prefix moved before cleanup dropped after,
  ScanPrefix first rest prefix moved before ->
  ScanContinuation before cleanup dropped after -> remaining after = 0 ->
  first ++ concat rest = moved ++ dropped.
Proof.
  intros first rest prefix moved before cleanup dropped after PREFIX CONT ZERO.
  pose proof (continuing_an_actual_prefix_is_one_original_scan
    _ _ _ _ _ _ _ _ PREFIX CONT) as WHOLE.
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ WHOLE) as FACTS.
  destruct FACTS as [VALID [ORDER REST]].
  rewrite (zero_remaining_has_no_pending_slots after VALID ZERO), app_nil_r in ORDER.
  exact ORDER.
Qed.

Corollary exhausted_consumer_requires_no_cleanup_scan :
  forall first rest prefix moved state,
  ScanPrefix first rest prefix moved state -> remaining state = 0 ->
  ScanContinuation state [] [] state /\ first ++ concat rest = moved.
Proof.
  intros first rest prefix moved state PREFIX ZERO.
  split; [constructor|].
  pose proof (exhausted_consuming_and_cleanup_partition_original_slots
    _ _ _ _ _ [] [] state PREFIX (ContinueRefl state) ZERO) as ORDER.
  now rewrite app_nil_r in ORDER.
Qed.

Theorem one_historical_envelope_covers_both_cursor_segments :
  forall table full first rest prefix moved before cleanup dropped after,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  ScanPrefix first rest prefix moved before ->
  ScanContinuation before cleanup dropped after -> forall event,
  event_count event (prefix ++ cleanup) <= scan_allowance event
    (source_entry_count table full) (historical_group_bound table).
Proof.
  intros table full first rest prefix moved before cleanup dropped after
    REACHABLE GROUPS PREFIX CONT event.
  eapply historical_capacity_covers_every_actual_scan_prefix;
    [exact REACHABLE|exact GROUPS|].
  eapply continuing_an_actual_prefix_is_one_original_scan; eassumption.
Qed.

(** These are cursor-control weights only. Owned record moves, full key
    destruction and allocation cleanup are not certified by this envelope. *)
Corollary shared_cursor_segments_preserve_declared_weights :
  forall table full first rest prefix moved before cleanup dropped after weight,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  ScanPrefix first rest prefix moved before ->
  ScanContinuation before cleanup dropped after ->
  weighted_counts weight (fun event => event_count event (prefix ++ cleanup)) <=
  weighted_counts weight (fun event => scan_allowance event
    (source_entry_count table full) (historical_group_bound table)).
Proof.
  intros table full first rest prefix moved before cleanup dropped after weight
    REACHABLE GROUPS PREFIX CONT.
  apply componentwise_scan_coverage_preserves_declared_weights. intro event.
  eapply one_historical_envelope_covers_both_cursor_segments; eassumption.
Qed.

End NativeHashBagOwnedScan.

Print Assumptions NativeHashBagOwnedScan.continuing_an_actual_prefix_is_one_original_scan.
Print Assumptions NativeHashBagOwnedScan.continuation_preserves_exact_pending_slots.
Print Assumptions NativeHashBagOwnedScan.zero_remaining_has_no_pending_slots.
Print Assumptions NativeHashBagOwnedScan.terminal_continuation_yields_exact_pending_slots.
Print Assumptions NativeHashBagOwnedScan.exhausted_consuming_and_cleanup_partition_original_slots.
Print Assumptions NativeHashBagOwnedScan.exhausted_consumer_requires_no_cleanup_scan.
Print Assumptions NativeHashBagOwnedScan.one_historical_envelope_covers_both_cursor_segments.
Print Assumptions NativeHashBagOwnedScan.shared_cursor_segments_preserve_declared_weights.
