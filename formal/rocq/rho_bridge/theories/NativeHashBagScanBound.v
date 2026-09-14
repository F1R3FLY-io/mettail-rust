(** Compose native control-group layout with the verified capacity history.
    This layer bounds source groups and every actual next-based scan prefix
    through the existing native cursor model. It introduces no iterator implementation
    and does not turn a natural-number formula into unchecked word arithmetic. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagHistory
  NativeHashBagBorrowedScan.

Module NativeHashBagScanBound.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagHistory.NativeHashBagHistory.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.

Lemma native_group_count_is_monotone : forall first second,
  first <= second -> group_count first <= group_count second.
Proof.
  intros first second ORDER. unfold group_count.
  assert (PRED : first - 1 <= second - 1) by lia.
  assert (DIV : (first - 1) / 16 <= (second - 1) / 16).
  { apply Nat.Div0.div_le_mono. exact PRED. }
  lia.
Qed.

Definition historical_group_bound state :=
  group_count (historical_bucket_bound state).

Theorem historical_capacity_bounds_native_source_groups : forall state full,
  Reachable state ->
  length (source_groups (buckets state) full) <= historical_group_bound state.
Proof.
  intros state full REACHABLE. rewrite native_source_groups_have_the_exact_group_count.
  apply native_group_count_is_monotone.
  now apply every_completed_native_execution_has_bounded_bucket_extent.
Qed.

(** Counts are componentwise, so callers can apply their declared logical
    event weights without replacing the original scan by a cost oracle.
    GroupLoad's sixteen-byte span can be charged separately from the load
    event; Yield identifies one original slot and its key/count projection. *)
Definition scan_allowance event entries groups :=
  match event with
  | Construct => 1
  | GroupLoad => groups
  | OuterNext => entries + 1
  | MaskProbe => entries + (groups - 1)
  | MaskClear | Yield => entries
  | GroupAdvance => groups - 1
  end.

Definition source_entry_count table full :=
  length (concat (source_groups (buckets table) full)).

Theorem historical_capacity_covers_every_actual_scan_prefix :
  forall table full first rest trace output state,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  ScanPrefix first rest trace output state -> forall event,
  event_count event trace <= scan_allowance event
    (source_entry_count table full) (historical_group_bound table).
Proof.
  intros table full first rest trace output state REACHABLE GROUPS PREFIX event.
  pose proof (every_actual_prefix_conserves_source_slots_and_events
    _ _ _ _ _ PREFIX) as FACTS.
  unfold prefix_facts in FACTS.
  destruct FACTS as [VALID [ORDER [CTOR [LOAD [PROBE [CLEAR
    [REMAIN [NEXT [FUTURE YIELDS]]]]]]]]].
  assert (ENTRIES : length (first ++ concat rest) = source_entry_count table full).
  { unfold source_entry_count. rewrite GROUPS. reflexivity. }
  pose proof (historical_capacity_bounds_native_source_groups
    table full REACHABLE) as GROUP_BOUND.
  rewrite GROUPS in GROUP_BOUND. cbn [length] in GROUP_BOUND.
  assert (NEXT_BOUND : outstanding_next state <= 1).
  { unfold outstanding_next. destruct (phase state); lia. }
  destruct event; cbn [scan_allowance]; lia.
Qed.

Definition weighted_counts (weight counts : Event -> nat) :=
  weight Construct * counts Construct + weight GroupLoad * counts GroupLoad +
  weight OuterNext * counts OuterNext + weight MaskProbe * counts MaskProbe +
  weight MaskClear * counts MaskClear + weight GroupAdvance * counts GroupAdvance +
  weight Yield * counts Yield.

Lemma componentwise_scan_coverage_preserves_declared_weights :
  forall weight actual admitted,
  (forall event, actual event <= admitted event) ->
  weighted_counts weight actual <= weighted_counts weight admitted.
Proof.
  intros weight actual admitted COVER. unfold weighted_counts.
  repeat apply Nat.add_le_mono; apply Nat.mul_le_mono_l; apply COVER.
Qed.

Corollary historical_scan_allowance_covers_every_weighted_prefix :
  forall table full first rest trace output state weight,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  ScanPrefix first rest trace output state ->
  weighted_counts weight (fun event => event_count event trace) <=
  weighted_counts weight (fun event => scan_allowance event
    (source_entry_count table full) (historical_group_bound table)).
Proof.
  intros table full first rest trace output state weight REACHABLE GROUPS PREFIX.
  apply componentwise_scan_coverage_preserves_declared_weights. intro event.
  eapply historical_capacity_covers_every_actual_scan_prefix; eassumption.
Qed.

(** Fixed borrowed iterator setup/projection are scalar source groups. A load
    additionally reads sixteen control bytes. No key operation or owned-key
    destruction occurs in this borrowed pass. *)
Definition borrowed_scan_weight event :=
  match event with GroupLoad => 17 | _ => 1 end.
Definition borrowed_scan_work entries groups := 4 * entries + 19 * groups.

Lemma declared_borrowed_scan_work_is_the_weighted_allowance : forall entries groups,
  0 < groups ->
  weighted_counts borrowed_scan_weight
    (fun event => scan_allowance event entries groups) = borrowed_scan_work entries groups.
Proof.
  intros entries groups POSITIVE.
  unfold weighted_counts, borrowed_scan_weight, scan_allowance, borrowed_scan_work.
  lia.
Qed.

(** Native source correspondence includes items = number of FULL controls.
    The scalar history projection alone intentionally does not assert this
    relation for an arbitrary Boolean [full] argument. The adapter must bind
    [full] to this immutable native table, not its bag occurrence counts. *)
Theorem native_item_count_admits_each_borrowed_scan_prefix :
  forall table full first rest trace output state,
  Reachable table -> source_groups (buckets table) full = first :: rest ->
  source_entry_count table full = items table ->
  ScanPrefix first rest trace output state ->
  weighted_counts borrowed_scan_weight (fun event => event_count event trace) <=
  borrowed_scan_work (items table) (historical_group_bound table).
Proof.
  intros table full first rest trace output state REACHABLE GROUPS COHERENCE PREFIX.
  pose proof (historical_scan_allowance_covers_every_weighted_prefix
    _ _ _ _ _ _ _ borrowed_scan_weight REACHABLE GROUPS PREFIX) as COVER.
  rewrite declared_borrowed_scan_work_is_the_weighted_allowance in COVER.
  - now rewrite COHERENCE in COVER.
  - unfold historical_group_bound, group_count. lia.
Qed.

End NativeHashBagScanBound.

Print Assumptions NativeHashBagScanBound.native_group_count_is_monotone.
Print Assumptions NativeHashBagScanBound.historical_capacity_bounds_native_source_groups.
Print Assumptions NativeHashBagScanBound.historical_capacity_covers_every_actual_scan_prefix.
Print Assumptions NativeHashBagScanBound.componentwise_scan_coverage_preserves_declared_weights.
Print Assumptions NativeHashBagScanBound.historical_scan_allowance_covers_every_weighted_prefix.
Print Assumptions NativeHashBagScanBound.declared_borrowed_scan_work_is_the_weighted_allowance.
Print Assumptions NativeHashBagScanBound.native_item_count_admits_each_borrowed_scan_prefix.
