(** Immutable control-lane projections for pinned hashbrown 0.17.1/SSE2.
    raw.rs:2564 set_ctrl writes original tags and their trailing mirrors.
    With B >= 16 the trailing group repeats the first 16 originals. With
    B = 4 or 8, [B,16) is EMPTY padding and [16,16+B) mirrors originals.
    SSE2 Group::load reads 16 consecutive bytes, not aligned scan groups.

    [Some i] identifies original bucket i; [None] identifies EMPTY padding.
    The allocated projection is interpreted ONLY on [0,B+16), and each
    window starts at p<B. Its total-function behavior outside that domain
    is not a source claim. The empty singleton uses its separate static
    EMPTY group and never owns an allocated bucket or a key.

    Source association must bind all predicates and counters to the SAME
    immutable native table, with initialized readable controls, original
    FULL/DELETED counts, valid native tags and the set_ctrl mirror layout.
    Physical observations are related through [physical_predicate_projects];
    pointer validity and this association are not derived from scalar counts.
    Tag::EMPTY is neither FULL nor DELETED only for valid native tags.

    This tranche establishes individual windows and coherent scalar counts.
    It does not yet compose the triangular permutation into full-cycle
    windows, find a physical EMPTY lane, or bound candidates/native loops.
    Machine addition/layout guards and callback work remain separate. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagBorrowedScan
  NativeHashBagScanBound.
Import ListNotations.

Module NativeHashBagProbeWindows.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagBorrowedScan.NativeHashBagBorrowedScan.
Import NativeHashBagScanBound.NativeHashBagScanBound.

Definition allocated_lane (bucket_count physical : nat) : option nat :=
  if physical <? bucket_count then Some physical
  else if bucket_count <? 16 then
    if physical <? 16 then None else Some (physical - 16)
  else Some (physical - bucket_count).
Definition allocated_window bucket_count start :=
  map (allocated_lane bucket_count) (seq start 16).
Definition original_slots (lanes : list (option nat)) :=
  flat_map (fun lane => match lane with Some index => [index] | None => [] end) lanes.
Definition singleton_window : list (option nat) := repeat None 16.
Definition observe_lane padding_value (original : nat -> bool) lane :=
  match lane with Some index => original index | None => padding_value end.
Definition physical_predicate_projects bucket_count original padding_value physical :=
  forall offset, offset < bucket_count + 16 ->
  physical offset = observe_lane padding_value original (allocated_lane bucket_count offset).

Lemma map_add_over_sequence : forall count offset start,
  map (fun index => offset + index) (seq start count) = seq (offset + start) count.
Proof.
  induction count as [|count IH]; intros offset start; cbn [seq map].
  - reflexivity.
  - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma a_sequence_starts_by_translation : forall count start,
  seq start count = map (fun index => start + index) (seq 0 count).
Proof. intros. rewrite map_add_over_sequence, Nat.add_0_r. reflexivity. Qed.

Lemma original_slots_of_original_lanes : forall slots,
  original_slots (map (@Some nat) slots) = slots.
Proof.
  induction slots as [|index rest IH]; [reflexivity|].
  change (index :: original_slots (map Some rest) = index :: rest). now rewrite IH.
Qed.

Lemma original_slots_of_padding : forall count,
  original_slots (repeat None count) = [].
Proof. induction count; cbn [original_slots flat_map repeat]; assumption || reflexivity. Qed.

Lemma original_slots_append : forall first rest,
  original_slots (first ++ rest) = original_slots first ++ original_slots rest.
Proof. intros. unfold original_slots. apply flat_map_app. Qed.

Lemma allocated_original_lane : forall bucket_count index,
  index < bucket_count -> allocated_lane bucket_count index = Some index.
Proof.
  intros bucket_count index INSIDE. unfold allocated_lane.
  assert (TEST : (index <? bucket_count) = true) by (apply Nat.ltb_lt; exact INSIDE).
  now rewrite TEST.
Qed.

Lemma allocated_small_padding_lane : forall bucket_count index,
  bucket_count < 16 -> bucket_count <= index < 16 ->
  allocated_lane bucket_count index = None.
Proof.
  intros bucket_count index SMALL RANGE. unfold allocated_lane.
  assert (ORIGINAL : (index <? bucket_count) = false) by (apply Nat.ltb_ge; lia).
  assert (NARROW : (bucket_count <? 16) = true) by (apply Nat.ltb_lt; lia).
  assert (PADDING : (index <? 16) = true) by (apply Nat.ltb_lt; lia).
  now rewrite ORIGINAL, NARROW, PADDING.
Qed.

Lemma allocated_small_mirror_lane : forall bucket_count index,
  bucket_count < 16 -> index < bucket_count ->
  allocated_lane bucket_count (16 + index) = Some index.
Proof.
  intros bucket_count index SMALL RANGE. unfold allocated_lane.
  assert (ORIGINAL : (16 + index <? bucket_count) = false) by (apply Nat.ltb_ge; lia).
  assert (NARROW : (bucket_count <? 16) = true) by (apply Nat.ltb_lt; lia).
  assert (PADDING : (16 + index <? 16) = false) by (apply Nat.ltb_ge; lia).
  rewrite ORIGINAL, NARROW, PADDING. f_equal. lia.
Qed.

Theorem large_allocated_lane_is_the_circular_original : forall bucket_count physical,
  16 <= bucket_count -> physical < bucket_count + 16 ->
  allocated_lane bucket_count physical = Some (physical mod bucket_count).
Proof.
  intros bucket_count physical LARGE DOMAIN. unfold allocated_lane.
  destruct (physical <? bucket_count) eqn:ORIGINAL.
  - apply Nat.ltb_lt in ORIGINAL. now rewrite Nat.mod_small by lia.
  - apply Nat.ltb_ge in ORIGINAL.
    assert (NARROW : (bucket_count <? 16) = false) by (apply Nat.ltb_ge; lia).
    rewrite NARROW. f_equal. apply Nat.mod_unique with (q := 1); lia.
Qed.

Theorem large_allocated_window_is_shifted_and_circular : forall bucket_count start,
  16 <= bucket_count -> start < bucket_count ->
  allocated_window bucket_count start =
    map (fun lane => Some ((start + lane) mod bucket_count)) (seq 0 16).
Proof.
  intros bucket_count start LARGE START. unfold allocated_window.
  rewrite (a_sequence_starts_by_translation 16 start), map_map.
  apply map_ext_in. intros lane MEMBER. apply in_seq in MEMBER.
  apply large_allocated_lane_is_the_circular_original; lia.
Qed.

Theorem small_allocated_window_is_originals_padding_then_mirrors :
  forall bucket_count start,
  (bucket_count = 4 \/ bucket_count = 8) -> start < bucket_count ->
  allocated_window bucket_count start =
    map Some (seq start (bucket_count - start)) ++
    repeat None (16 - bucket_count) ++ map Some (seq 0 start).
Proof.
  intros bucket_count start SMALL START.
  assert (NARROW : bucket_count < 16) by lia.
  assert (ORIGINAL : map (allocated_lane bucket_count) (seq start (bucket_count - start)) =
    map Some (seq start (bucket_count - start))).
  { apply map_ext_in. intros index MEMBER. apply in_seq in MEMBER.
    apply allocated_original_lane. lia. }
  assert (PADDING : map (allocated_lane bucket_count) (seq bucket_count (16 - bucket_count)) =
    repeat None (16 - bucket_count)).
  { assert (CONSTANT : forall count offset, bucket_count <= offset -> offset + count <= 16 ->
      map (allocated_lane bucket_count) (seq offset count) = repeat None count).
    { induction count as [|count IH]; intros offset LOW HIGH; cbn [seq map repeat].
      - reflexivity.
      - rewrite allocated_small_padding_lane by lia. rewrite IH by lia. reflexivity. }
    apply CONSTANT; lia. }
  assert (MIRROR : map (allocated_lane bucket_count) (seq 16 start) = map Some (seq 0 start)).
  { rewrite (a_sequence_starts_by_translation start 16), map_map.
    apply map_ext_in. intros index MEMBER. apply in_seq in MEMBER.
    apply allocated_small_mirror_lane; lia. }
  unfold allocated_window.
  replace 16 with ((bucket_count - start) + ((16 - bucket_count) + start)) at 1 by lia.
  rewrite seq_app, map_app.
  replace (start + (bucket_count - start)) with bucket_count by lia.
  rewrite seq_app, map_app.
  replace (bucket_count + (16 - bucket_count)) with 16 by lia.
  now rewrite ORIGINAL, PADDING, MIRROR.
Qed.

Theorem small_window_originals_have_no_duplicates : forall bucket_count start,
  (bucket_count = 4 \/ bucket_count = 8) -> start < bucket_count ->
  NoDup (original_slots (allocated_window bucket_count start)).
Proof.
  intros bucket_count start SMALL START.
  rewrite small_allocated_window_is_originals_padding_then_mirrors by assumption.
  rewrite !original_slots_append, !original_slots_of_original_lanes, original_slots_of_padding.
  cbn [app]. apply NoDup_app; [apply seq_NoDup|apply seq_NoDup|].
  intros index SUFFIX PREFIX. apply in_seq in SUFFIX. apply in_seq in PREFIX. lia.
Qed.

Theorem large_window_originals_have_no_duplicates : forall bucket_count start,
  16 <= bucket_count -> start < bucket_count ->
  NoDup (original_slots (allocated_window bucket_count start)).
Proof.
  intros bucket_count start LARGE START.
  assert (RESIDUE : forall lane, lane < 16 ->
    (start + lane) mod bucket_count =
      if start + lane <? bucket_count then start + lane else start + lane - bucket_count).
  { intros lane RANGE. destruct (start + lane <? bucket_count) eqn:INSIDE.
    - apply Nat.ltb_lt in INSIDE. now rewrite Nat.mod_small by lia.
    - apply Nat.ltb_ge in INSIDE. symmetry. apply Nat.mod_unique with (q := 1); lia. }
  rewrite large_allocated_window_is_shifted_and_circular by assumption.
  replace (map (fun lane => Some ((start + lane) mod bucket_count)) (seq 0 16))
    with (map Some (map (fun lane => (start + lane) mod bucket_count) (seq 0 16)))
    by (rewrite map_map; reflexivity).
  rewrite original_slots_of_original_lanes.
  apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros left right LEFT RIGHT SAME. apply in_seq in LEFT. apply in_seq in RIGHT.
  rewrite !RESIDUE in SAME by lia.
  destruct (start + left <? bucket_count) eqn:LEFT_TEST;
    destruct (start + right <? bucket_count) eqn:RIGHT_TEST;
    (apply Nat.ltb_lt in LEFT_TEST || apply Nat.ltb_ge in LEFT_TEST);
    (apply Nat.ltb_lt in RIGHT_TEST || apply Nat.ltb_ge in RIGHT_TEST); lia.
Qed.

Lemma clipped_group_prefix_is_a_contiguous_sequence : forall groups bucket_count,
  concat (map (fun group => seq (group * 16) (Nat.min 16 (bucket_count - group * 16)))
    (seq 0 groups)) = seq 0 (Nat.min bucket_count (16 * groups)).
Proof.
  induction groups as [|groups IH]; intro bucket_count.
  - cbn [seq map concat Nat.mul]. now rewrite Nat.min_0_r.
  - rewrite seq_S, map_app, concat_app.
    cbn [map concat]. rewrite app_nil_r, IH.
    replace ((0 + groups) * 16) with (16 * groups) by lia.
    destruct (Nat.le_gt_cases bucket_count (16 * groups)) as [FINISHED|REMAINS].
    + rewrite Nat.min_l by lia.
      replace (bucket_count - 16 * groups) with 0 by lia.
      cbn [Nat.min seq]. rewrite app_nil_r, Nat.min_l by lia. reflexivity.
    + rewrite Nat.min_r by lia.
      change (seq 0 (16 * groups) ++ seq (0 + 16 * groups)
        (Nat.min 16 (bucket_count - 16 * groups)) =
        seq 0 (Nat.min bucket_count (16 * S groups))).
      rewrite <- seq_app. f_equal.
      destruct (Nat.le_gt_cases bucket_count (16 * S groups)) as [LAST|MORE].
      * rewrite (Nat.min_l bucket_count (16 * S groups)) by lia.
        rewrite (Nat.min_r 16 (bucket_count - 16 * groups)) by lia. lia.
      * rewrite (Nat.min_r bucket_count (16 * S groups)) by lia.
        rewrite (Nat.min_l 16 (bucket_count - 16 * groups)) by lia. lia.
Qed.

Lemma filtering_concatenated_groups : forall (predicate : nat -> bool) (groups : list (list nat)),
  filter predicate (concat groups) = concat (map (filter predicate) groups).
Proof.
  intros predicate groups. induction groups as [|group rest IH]; cbn [concat map].
  - reflexivity.
  - now rewrite filter_app, IH.
Qed.

Theorem source_groups_count_the_original_filtered_bucket_range : forall bucket_count full,
  0 < bucket_count ->
  concat (source_groups bucket_count full) = filter full (seq 0 bucket_count).
Proof.
  intros bucket_count full POSITIVE.
  assert (EXTENT : bucket_count <= 16 * group_count bucket_count).
  { unfold group_count.
    pose proof (Nat.div_mod (bucket_count - 1) 16 ltac:(lia)) as DIVISION.
    pose proof (Nat.mod_upper_bound (bucket_count - 1) 16 ltac:(lia)) as REMAINDER. lia. }
  unfold source_groups.
  rewrite <- (@map_map nat (list nat) (list nat)
    (fun group => seq (group * 16) (Nat.min 16 (bucket_count - group * 16)))
    (filter full) (seq 0 (group_count bucket_count))).
  rewrite <- filtering_concatenated_groups, clipped_group_prefix_is_a_contiguous_sequence.
  now rewrite Nat.min_l by exact EXTENT.
Qed.

Definition empty_slot (full tombstone : nat -> bool) index :=
  negb (full index || tombstone index).
Definition coherent_control_counts table full tombstone :=
  source_entry_count table full = items table /\
  source_entry_count table tombstone = deleted table /\
  (forall index, index < buckets table -> full index = true -> tombstone index = false).

Lemma disjoint_control_classes_partition_original_slots : forall slots full tombstone,
  (forall index, In index slots -> full index = true -> tombstone index = false) ->
  length (filter full slots) + length (filter tombstone slots) +
    length (filter (empty_slot full tombstone) slots) = length slots.
Proof.
  induction slots as [|index rest IH]; intros full tombstone DISJOINT.
  - reflexivity.
  - assert (TAIL : forall entry, In entry rest -> full entry = true -> tombstone entry = false).
    { intros entry MEMBER. apply DISJOINT. now right. }
    specialize (IH full tombstone TAIL).
    unfold empty_slot in *.
    cbn [filter length].
    destruct (full index) eqn:FULL; destruct (tombstone index) eqn:TOMBSTONE;
      cbn [orb negb length] in *; try lia.
    specialize (DISJOINT index (or_introl eq_refl) FULL). congruence.
Qed.

Lemma native_full_capacity_is_strictly_below_bucket_count : forall bucket_count,
  NativeBuckets bucket_count -> full_capacity bucket_count < bucket_count.
Proof.
  intros bucket_count NATIVE. destruct NATIVE as [|exponent].
  - change (0 < 1). lia.
  - destruct exponent as [|[|exponent]]; [change (3 < 4); lia|change (7 < 8); lia|].
    assert (POWER : 2 ^ (S (S exponent) + 2) = 16 * 2 ^ exponent).
    { replace (S (S exponent) + 2) with (exponent + 4) by lia.
      rewrite Nat.pow_add_r. cbn [Nat.pow]. lia. }
    assert (POSITIVE : 0 < 2 ^ exponent).
    { pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
    rewrite POWER, large_native_capacity_counts_seven_eighths by exact POSITIVE. lia.
Qed.

Theorem coherent_native_counts_have_a_positive_empty_class : forall table full tombstone,
  valid_counters table -> coherent_control_counts table full tombstone ->
  source_entry_count table (empty_slot full tombstone) =
    buckets table - full_capacity (buckets table) + growth_left table /\
  0 < source_entry_count table (empty_slot full tombstone).
Proof.
  intros table full tombstone [NATIVE BALANCE] [FULL [TOMBSTONE DISJOINT]].
  pose proof (native_full_capacity_is_strictly_below_bucket_count (buckets table) NATIVE)
    as CAPACITY.
  assert (POSITIVE : 0 < buckets table) by lia.
  pose proof (disjoint_control_classes_partition_original_slots
    (seq 0 (buckets table)) full tombstone) as PARTITION.
  specialize (PARTITION ltac:(intros index MEMBER; apply DISJOINT; apply in_seq in MEMBER; lia)).
  unfold source_entry_count in *.
  rewrite !source_groups_count_the_original_filtered_bucket_range in * by exact POSITIVE.
  rewrite length_seq in PARTITION. split; lia.
Qed.

End NativeHashBagProbeWindows.

Print Assumptions NativeHashBagProbeWindows.large_allocated_lane_is_the_circular_original.
Print Assumptions NativeHashBagProbeWindows.large_allocated_window_is_shifted_and_circular.
Print Assumptions NativeHashBagProbeWindows.small_allocated_window_is_originals_padding_then_mirrors.
Print Assumptions NativeHashBagProbeWindows.small_window_originals_have_no_duplicates.
Print Assumptions NativeHashBagProbeWindows.large_window_originals_have_no_duplicates.
Print Assumptions NativeHashBagProbeWindows.source_groups_count_the_original_filtered_bucket_range.
Print Assumptions NativeHashBagProbeWindows.coherent_native_counts_have_a_positive_empty_class.
