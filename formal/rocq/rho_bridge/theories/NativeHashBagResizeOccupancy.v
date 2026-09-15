(** Control occupancy during pinned hashbrown resize_inner (raw.rs:2904).
    Native target items/growth_left stay 0/full_capacity until the loop ends.
    A completed pair records a byte relocation, NOT a destructor-ownership
    transfer. prepare_insert_index writes the destination FULL tag before
    copy_nonoverlapping initializes its bytes; there is at most one such
    pending pair. Original keys retain destructor authority until mem::swap.

    This is a finite source-association ledger, not another table or scanner.
    The original roster comes from the existing old-table scan. Its source
    association, actual EMPTY destination returned by placement, physical
    mirror writes, pointer/layout validity, and byte-copy correctness are
    explicit surrounding obligations. Fresh target controls have only EMPTY
    and FULL tags: initialization is EMPTY, insertion writes FULL, and no
    operation introduces DELETED. Under this native source association,
    [full index = false] means EMPTY, not a possible tombstone. In particular,
    this file does not
    prove placement termination by assuming that it returned a fresh slot.
    It proves that every associated prefix has EMPTY originals available,
    which the separate probe proof can use BEFORE running placement. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Permutation Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagGrowth
  NativeHashBagProbeWindows.
Import ListNotations.

Module NativeHashBagResizeOccupancy.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagGrowth.NativeHashBagGrowth.
Import NativeHashBagScanBound.NativeHashBagScanBound.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.

Definition pending_pairs (pending : option (nat * nat)) :=
  match pending with None => [] | Some entry => [entry] end.
Definition tagged_destinations copied pending :=
  map (@snd nat nat) (copied ++ pending_pairs pending).

Definition relocation_prefix original bucket_count full copied pending unread :=
  original = map (@fst nat nat) (copied ++ pending_pairs pending) ++ unread /\
  NoDup (tagged_destinations copied pending) /\
  Forall (fun index => index < bucket_count) (tagged_destinations copied pending) /\
  (forall index, index < bucket_count ->
    (full index = true <-> In index (tagged_destinations copied pending))).

Definition mark_full (full : nat -> bool) destination index :=
  if index =? destination then true else full index.

Theorem empty_target_starts_the_original_relocation_prefix : forall original bucket_count,
  relocation_prefix original bucket_count (fun _ => false) [] None original.
Proof.
  intros. unfold relocation_prefix, tagged_destinations, pending_pairs. cbn.
  split; [reflexivity|]. split; [constructor|]. split; [constructor|].
  intros index INSIDE. split; [discriminate|contradiction].
Qed.

Theorem setting_an_empty_destination_records_one_pending_copy :
  forall original bucket_count full copied source unread destination,
  relocation_prefix original bucket_count full copied None (source :: unread) ->
  destination < bucket_count -> full destination = false ->
  relocation_prefix original bucket_count (mark_full full destination)
    copied (Some (source, destination)) unread.
Proof.
  intros original bucket_count full copied source unread destination
    [ORIGINAL [UNIQUE [RANGE TAGS]]] INSIDE EMPTY.
  unfold tagged_destinations, pending_pairs in *.
  rewrite !app_nil_r in *.
  assert (FRESH : ~ In destination (map snd copied)).
  { intro MEMBER. apply (proj2 (TAGS destination INSIDE)) in MEMBER. congruence. }
  unfold relocation_prefix, tagged_destinations, pending_pairs.
  rewrite !map_app. cbn [map fst snd].
  split; [rewrite <- app_assoc; exact ORIGINAL|]. split.
  - apply NoDup_app; [exact UNIQUE|constructor; [intro BAD; exact BAD|constructor]|].
    intros index MEMBER [SAME|BAD]; [subst index; contradiction|contradiction].
  - split; [apply Forall_app; split; [exact RANGE|constructor; [exact INSIDE|constructor]]|].
    intros index BOUND. unfold mark_full.
    destruct (index =? destination) eqn:SAME.
    + apply Nat.eqb_eq in SAME. subst index. split.
      * intro. apply in_or_app. right. now left.
      * intro. reflexivity.
    + apply Nat.eqb_neq in SAME. rewrite (TAGS index BOUND), in_app_iff.
      cbn. intuition congruence.
Qed.

Theorem copying_the_pending_bytes_preserves_the_tagged_frontier :
  forall original bucket_count full copied source destination unread,
  relocation_prefix original bucket_count full copied (Some (source, destination)) unread ->
  relocation_prefix original bucket_count full (copied ++ [(source, destination)]) None unread.
Proof.
  intros. unfold relocation_prefix, tagged_destinations, pending_pairs in *.
  now rewrite app_nil_r.
Qed.

Theorem tagged_destinations_are_exactly_the_original_full_slots :
  forall original bucket_count full copied pending unread,
  relocation_prefix original bucket_count full copied pending unread ->
  Permutation (filter full (seq 0 bucket_count)) (tagged_destinations copied pending).
Proof.
  intros original bucket_count full copied pending unread
    [ORIGINAL [UNIQUE [RANGE TAGS]]].
  apply NoDup_Permutation; [apply NoDup_filter, seq_NoDup|exact UNIQUE|].
  intro index. rewrite filter_In, in_seq. split.
  - intros [[LOW HIGH] FULL]. apply (proj1 (TAGS index HIGH)). exact FULL.
  - intro MEMBER. assert (HIGH : index < bucket_count).
    { rewrite Forall_forall in RANGE. now apply RANGE. }
    split; [lia|]. apply (proj2 (TAGS index HIGH)). exact MEMBER.
Qed.

Theorem each_prefix_tags_no_more_than_the_original_roster :
  forall original bucket_count full copied pending unread,
  relocation_prefix original bucket_count full copied pending unread ->
  length (filter full (seq 0 bucket_count)) + length unread = length original.
Proof.
  intros original bucket_count full copied pending unread PREFIX.
  pose proof (tagged_destinations_are_exactly_the_original_full_slots
    _ _ _ _ _ _ PREFIX) as ORDER.
  apply Permutation_length in ORDER.
  destruct PREFIX as [ORIGINAL _]. rewrite ORIGINAL, length_app, length_map.
  unfold tagged_destinations in ORDER. rewrite length_map in ORDER. lia.
Qed.

(** The source relocation block has two set_ctrl writes, two bucket_ptr
    projections and one copy_nonoverlapping of the complete tuple size.
    Count both tag writes even when their addresses coincide. The pending
    record's entire copy block is covered before its bytes are initialized;
    this is an upper allowance, not a claim those operations already ran.

    These counts cover only those flat transfer blocks. Hash bodies, probe
    bodies, old-table iteration, setup/control initialization, pointer and
    layout validity, final swap/free, and destructor authority retain their
    separate source obligations. No native items counter is used here. *)
Theorem relocation_frontiers_partition_original_record_counts :
  forall original bucket_count full copied pending unread,
  relocation_prefix original bucket_count full copied pending unread ->
  length copied + length (pending_pairs pending) + length unread = length original.
Proof.
  intros original bucket_count full copied pending unread [ORIGINAL _].
  rewrite ORIGINAL, length_app, length_map, length_app. reflexivity.
Qed.

Theorem every_relocation_frontier_covers_its_flat_transfer_blocks :
  forall original bucket_count full copied pending unread tuple_bytes,
  relocation_prefix original bucket_count full copied pending unread ->
  2 * length (tagged_destinations copied pending) <= 2 * length original /\
  tuple_bytes * length copied <=
    tuple_bytes * length (tagged_destinations copied pending) /\
  tuple_bytes * length (tagged_destinations copied pending) <=
    tuple_bytes * length original.
Proof.
  intros original bucket_count full copied pending unread tuple_bytes PREFIX.
  pose proof (relocation_frontiers_partition_original_record_counts
    _ _ _ _ _ _ PREFIX) as PARTITION.
  unfold tagged_destinations. rewrite length_map, length_app.
  repeat split; nia.
Qed.

Theorem pending_transfer_reservation_is_unchanged_when_copy_finishes :
  forall copied source destination,
  length (tagged_destinations copied (Some (source, destination))) =
    length (tagged_destinations (copied ++ [(source, destination)]) None).
Proof.
  intros. unfold tagged_destinations, pending_pairs. now rewrite app_nil_r.
Qed.

Theorem completed_relocation_has_exact_record_and_byte_volume :
  forall original bucket_count full copied tuple_bytes,
  relocation_prefix original bucket_count full copied None [] ->
  length copied = length original /\
  2 * length (tagged_destinations copied None) = 2 * length original /\
  tuple_bytes * length copied = tuple_bytes * length original.
Proof.
  intros original bucket_count full copied tuple_bytes PREFIX.
  pose proof (relocation_frontiers_partition_original_record_counts
    _ _ _ _ _ _ PREFIX) as PARTITION.
  cbn [pending_pairs length] in PARTITION.
  unfold tagged_destinations, pending_pairs. rewrite app_nil_r, length_map.
  repeat split; nia.
Qed.

(** No native item-counter hypothesis appears here. Even the pending FULL
    tag is included although its destination bytes are not initialized yet. *)
Theorem each_resize_prefix_has_a_nonfull_original_destination :
  forall original bucket_count full copied pending unread,
  NativeBuckets bucket_count -> length original <= full_capacity bucket_count ->
  relocation_prefix original bucket_count full copied pending unread ->
  exists destination, destination < bucket_count /\ full destination = false.
Proof.
  intros original bucket_count full copied pending unread NATIVE ROOM PREFIX.
  pose proof (each_prefix_tags_no_more_than_the_original_roster _ _ _ _ _ _ PREFIX) as COUNT.
  pose proof (native_full_capacity_is_strictly_below_bucket_count _ NATIVE) as CAPACITY.
  assert (NONEMPTY : 0 < length (filter (fun index => negb (full index))
    (seq 0 bucket_count))).
  { pose proof (filter_length full (seq 0 bucket_count)) as PARTITION.
    rewrite length_seq in PARTITION. lia. }
  destruct (filter (fun index => negb (full index)) (seq 0 bucket_count))
    as [|destination rest] eqn:EMPTY; [cbn in NONEMPTY; lia|].
  assert (MEMBER : In destination
    (filter (fun index => negb (full index)) (seq 0 bucket_count))).
  { rewrite EMPTY. now left. }
  apply filter_In in MEMBER. destruct MEMBER as [RANGE FALSE].
  apply in_seq in RANGE. apply Bool.negb_true_iff in FALSE.
  exists destination. split; [lia|exact FALSE].
Qed.

Corollary the_source_resize_policy_supplies_prefix_room :
  forall before original full copied pending unread,
  valid_counters before -> length original = items before ->
  relocation_prefix original (source_resize_buckets before) full copied pending unread ->
  exists destination, destination < source_resize_buckets before /\ full destination = false.
Proof.
  intros before original full copied pending unread VALID COUNT PREFIX.
  destruct (valid_resize_selection_is_native_and_has_room before VALID) as [NATIVE ROOM].
  apply (each_resize_prefix_has_a_nonfull_original_destination
    original (source_resize_buckets before) full copied pending unread);
    [exact NATIVE|lia|exact PREFIX].
Qed.

Theorem finishing_the_roster_justifies_the_delayed_item_count :
  forall original bucket_count full copied,
  relocation_prefix original bucket_count full copied None [] ->
  map (@fst nat nat) copied = original /\
  length (filter full (seq 0 bucket_count)) = length original.
Proof.
  intros original bucket_count full copied PREFIX.
  pose proof (each_prefix_tags_no_more_than_the_original_roster _ _ _ _ _ _ PREFIX) as COUNT.
  destruct PREFIX as [ORIGINAL _].
  cbn [pending_pairs] in ORIGINAL. rewrite !app_nil_r in ORIGINAL.
  cbn [length] in COUNT.
  split; [symmetry; exact ORIGINAL|lia].
Qed.

Theorem final_counter_assignments_match_the_existing_clean_table : forall before,
  valid_counters before ->
  valid_counters (clean_table before (source_resize_buckets before)).
Proof.
  intros before VALID.
  destruct (valid_resize_selection_is_native_and_has_room before VALID) as [NATIVE ROOM].
  unfold valid_counters, clean_table. cbn. split; [exact NATIVE|lia].
Qed.

Theorem completed_control_ledger_matches_the_final_native_counters :
  forall before original full copied,
  valid_counters before -> length original = items before ->
  relocation_prefix original (source_resize_buckets before) full copied None [] ->
  coherent_control_counts (clean_table before (source_resize_buckets before))
    full (fun _ => false).
Proof.
  intros before original full copied VALID COUNT PREFIX.
  destruct (valid_resize_selection_is_native_and_has_room before VALID) as [NATIVE ROOM].
  pose proof (native_full_capacity_is_strictly_below_bucket_count _ NATIVE) as CAPACITY.
  assert (POSITIVE : 0 < source_resize_buckets before) by lia.
  destruct (finishing_the_roster_justifies_the_delayed_item_count _ _ _ _ PREFIX)
    as [ORIGINAL FULL].
  unfold coherent_control_counts, source_entry_count.
  cbn [clean_table buckets items deleted].
  rewrite !source_groups_count_the_original_filtered_bucket_range by exact POSITIVE.
  rewrite filter_false. repeat split; congruence.
Qed.

End NativeHashBagResizeOccupancy.

Print Assumptions NativeHashBagResizeOccupancy.empty_target_starts_the_original_relocation_prefix.
Print Assumptions NativeHashBagResizeOccupancy.setting_an_empty_destination_records_one_pending_copy.
Print Assumptions NativeHashBagResizeOccupancy.copying_the_pending_bytes_preserves_the_tagged_frontier.
Print Assumptions NativeHashBagResizeOccupancy.tagged_destinations_are_exactly_the_original_full_slots.
Print Assumptions NativeHashBagResizeOccupancy.each_prefix_tags_no_more_than_the_original_roster.
Print Assumptions NativeHashBagResizeOccupancy.relocation_frontiers_partition_original_record_counts.
Print Assumptions NativeHashBagResizeOccupancy.every_relocation_frontier_covers_its_flat_transfer_blocks.
Print Assumptions NativeHashBagResizeOccupancy.pending_transfer_reservation_is_unchanged_when_copy_finishes.
Print Assumptions NativeHashBagResizeOccupancy.completed_relocation_has_exact_record_and_byte_volume.
Print Assumptions NativeHashBagResizeOccupancy.each_resize_prefix_has_a_nonfull_original_destination.
Print Assumptions NativeHashBagResizeOccupancy.the_source_resize_policy_supplies_prefix_room.
Print Assumptions NativeHashBagResizeOccupancy.finishing_the_roster_justifies_the_delayed_item_count.
Print Assumptions NativeHashBagResizeOccupancy.final_counter_assignments_match_the_existing_clean_table.
Print Assumptions NativeHashBagResizeOccupancy.completed_control_ledger_matches_the_final_native_counters.
