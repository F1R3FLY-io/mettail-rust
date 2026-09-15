(** Full mathematical cycles of the pinned native triangular probe.
    Reuse the checked integer triangular permutation and immutable physical
    window projection; this file is neither a probe engine nor a replacement
    table. Every Z-to-nat conversion below has its domain proved explicitly.

    For B=16*q and p=16*a+r, starts retain residue r and translated triangular
    group coordinates. Flattening these SHIFTED windows permutes original
    bucket positions, even when r is nonzero. Coverage is derived, not a
    premise. FULL/DELETED counters alone do not establish control coherence.

    Physical EMPTY observations require the SAME immutable source table's
    valid native tag predicates, initialized readable control extent and
    exact original/mirror/padding association. The theorems locate a lane in
    the mathematical cycle; they do not assert that Rust actually reaches or
    loads it. Plain usize additions still require valid layout and reached
    prefix nonoverflow guards. Source loop steps, Eq callbacks and work are
    separate obligations. Small-table EMPTY padding is not an insertion slot;
    the singleton remains a separate static group without an owned bucket. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Permutation
  ZArith.BinInt ZArith.Znat Lia.
From RhoBridge Require Import NativeHashBagProbeSequence NativeHashBagProbeWindows
  NativeHashBagExtent NativeHashBagScanBound.
Import ListNotations.
Open Scope nat_scope.

Module NativeHashBagProbeCoverage.
Import NativeHashBagProbeSequence.NativeHashBagProbeSequence.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagScanBound.NativeHashBagScanBound.

Definition power_group_count exponent := Z.to_nat (group_modulus exponent).
Definition power_bucket_count exponent := 16 * power_group_count exponent.
Definition mathematical_start exponent initial step :=
  Z.to_nat (source_probe_position (Z.of_nat (power_bucket_count exponent))
    (Z.of_nat initial) step).
Definition complete_windows exponent initial :=
  map (fun step => allocated_window (power_bucket_count exponent)
    (mathematical_start exponent initial step)) (seq 0 (power_group_count exponent)).
Definition complete_originals exponent initial :=
  original_slots (concat (complete_windows exponent initial)).
Definition translated_group exponent initial_group step :=
  (initial_group + triangular_residue exponent step) mod power_group_count exponent.
Definition circular_block bucket_count residue group :=
  map (fun lane => (residue + (16 * group + lane)) mod bucket_count) (seq 0 16).

Lemma group_count_returns_the_original_integer : forall exponent,
  Z.of_nat (power_group_count exponent) = group_modulus exponent.
Proof.
  intro exponent. unfold power_group_count.
  rewrite Z2Nat.id; [reflexivity|]. pose proof (group_modulus_is_positive exponent). lia.
Qed.

Lemma power_group_count_is_positive : forall exponent, 0 < power_group_count exponent.
Proof.
  intro exponent. apply Nat2Z.inj_lt.
  rewrite group_count_returns_the_original_integer. apply group_modulus_is_positive.
Qed.

Lemma power_bucket_count_is_positive : forall exponent, 0 < power_bucket_count exponent.
Proof. intro exponent. unfold power_bucket_count. pose proof (power_group_count_is_positive exponent). lia. Qed.

Lemma triangular_residue_returns_the_original_integer : forall exponent step,
  Z.of_nat (triangular_residue exponent step) =
    (triangle step mod group_modulus exponent)%Z.
Proof.
  intros exponent step. unfold triangular_residue. rewrite Z2Nat.id; [reflexivity|].
  pose proof (group_modulus_is_positive exponent) as POSITIVE.
  pose proof (Z.mod_pos_bound (triangle step) (group_modulus exponent) POSITIVE). lia.
Qed.

Theorem every_mathematical_start_is_within_its_table : forall exponent initial step,
  mathematical_start exponent initial step < power_bucket_count exponent.
Proof.
  intros exponent initial step. pose proof (power_bucket_count_is_positive exponent) as POSITIVE.
  unfold mathematical_start, source_probe_position. apply Nat2Z.inj_lt.
  pose proof (Z.mod_pos_bound (Z.of_nat initial + 16 * triangle step)%Z
    (Z.of_nat (power_bucket_count exponent)) ltac:(lia)) as RANGE.
  rewrite Z2Nat.id by lia. exact (proj2 RANGE).
Qed.

Theorem mathematical_starts_have_translated_triangular_group_coordinates :
  forall exponent initial_group residue step,
  initial_group < power_group_count exponent -> residue < 16 ->
  mathematical_start exponent (16 * initial_group + residue) step =
    16 * translated_group exponent initial_group step + residue.
Proof.
  intros exponent initial_group residue step GROUP RESIDUE.
  assert (INTEGER : source_probe_position (Z.of_nat (power_bucket_count exponent))
      (Z.of_nat (16 * initial_group + residue)) step =
      Z.of_nat (16 * translated_group exponent initial_group step + residue)).
  { unfold power_bucket_count, translated_group.
    repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul.
    repeat rewrite Nat2Z.inj_mod. repeat rewrite Nat2Z.inj_add.
    rewrite !group_count_returns_the_original_integer, triangular_residue_returns_the_original_integer.
    change (source_probe_position (16 * group_modulus exponent)
      (16 * Z.of_nat initial_group + Z.of_nat residue) step =
      16 * ((Z.of_nat initial_group + triangle step mod group_modulus exponent)
        mod group_modulus exponent) + Z.of_nat residue)%Z.
    rewrite large_table_starts_keep_the_original_unaligned_residue.
    - rewrite Z.add_mod_idemp_r by (pose proof (group_modulus_is_positive exponent); lia).
      reflexivity.
    - apply group_modulus_is_positive.
    - lia. }
  unfold mathematical_start. rewrite INTEGER, Nat2Z.id. reflexivity.
Qed.

Lemma a_residue_with_at_most_one_wrap : forall modulus value,
  0 < modulus -> value < 2 * modulus ->
  value mod modulus = if value <? modulus then value else value - modulus.
Proof.
  intros modulus value POSITIVE BOUND. destruct (value <? modulus) eqn:BELOW.
  - apply Nat.ltb_lt in BELOW. now rewrite Nat.mod_small by lia.
  - apply Nat.ltb_ge in BELOW. symmetry. apply Nat.mod_unique with (q := 1); lia.
Qed.

Lemma cyclic_translation_is_injective_on_its_range : forall modulus offset left right,
  0 < modulus -> offset < modulus -> left < modulus -> right < modulus ->
  (offset + left) mod modulus = (offset + right) mod modulus -> left = right.
Proof.
  intros modulus offset left right POSITIVE OFFSET LEFT RIGHT SAME.
  rewrite !a_residue_with_at_most_one_wrap in SAME by lia.
  destruct (offset + left <? modulus) eqn:LEFT_TEST;
    destruct (offset + right <? modulus) eqn:RIGHT_TEST;
    (apply Nat.ltb_lt in LEFT_TEST || apply Nat.ltb_ge in LEFT_TEST);
    (apply Nat.ltb_lt in RIGHT_TEST || apply Nat.ltb_ge in RIGHT_TEST); lia.
Qed.

Lemma cyclic_translation_permutes_the_complete_range : forall modulus offset,
  0 < modulus -> offset < modulus ->
  Permutation (map (fun index => (offset + index) mod modulus) (seq 0 modulus))
    (seq 0 modulus).
Proof.
  intros modulus offset POSITIVE OFFSET. apply Permutation_map_same_l.
  - apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros left right LEFT RIGHT SAME. apply in_seq in LEFT. apply in_seq in RIGHT.
    apply (cyclic_translation_is_injective_on_its_range modulus offset left right); assumption || lia.
  - intros index MEMBER. apply in_map_iff in MEMBER as [original [INDEX _]]. subst index.
    apply in_seq. split; [lia|]. cbn [Nat.add]. apply Nat.mod_upper_bound. lia.
Qed.

Lemma translated_triangular_groups_permute_the_range : forall exponent initial_group,
  initial_group < power_group_count exponent ->
  Permutation (map (translated_group exponent initial_group) (seq 0 (power_group_count exponent)))
    (seq 0 (power_group_count exponent)).
Proof.
  intros exponent initial_group GROUP. unfold translated_group.
  rewrite <- (@map_map nat nat nat (triangular_residue exponent)
    (fun index => (initial_group + index) mod power_group_count exponent)
    (seq 0 (power_group_count exponent))).
  eapply Permutation_trans.
  - apply Permutation_map. apply triangular_residues_permute_the_complete_power_of_two_range.
  - apply cyclic_translation_permutes_the_complete_range; [apply power_group_count_is_positive|exact GROUP].
Qed.

Lemma original_slots_of_concatenated_windows : forall windows,
  original_slots (concat windows) = flat_map original_slots windows.
Proof.
  induction windows as [|window rest IH]; [reflexivity|].
  cbn [concat flat_map]. now rewrite original_slots_append, IH.
Qed.

Lemma an_original_group_window_is_its_circular_block : forall groups group residue,
  0 < groups -> group < groups -> residue < 16 ->
  original_slots (allocated_window (16 * groups) (16 * group + residue)) =
    circular_block (16 * groups) residue group.
Proof.
  intros groups group residue POSITIVE GROUP RESIDUE.
  rewrite large_allocated_window_is_shifted_and_circular by lia.
  rewrite <- (@map_map nat nat (option nat)
    (fun lane => (16 * group + residue + lane) mod (16 * groups)) Some (seq 0 16)).
  rewrite original_slots_of_original_lanes. unfold circular_block.
  apply map_ext. intro lane. f_equal. lia.
Qed.

Lemma complete_originals_are_translated_circular_blocks : forall exponent initial_group residue,
  initial_group < power_group_count exponent -> residue < 16 ->
  complete_originals exponent (16 * initial_group + residue) =
    flat_map (circular_block (power_bucket_count exponent) residue)
      (map (translated_group exponent initial_group) (seq 0 (power_group_count exponent))).
Proof.
  intros exponent initial_group residue GROUP RESIDUE.
  unfold complete_originals, complete_windows. rewrite original_slots_of_concatenated_windows.
  rewrite !flat_map_concat_map, !map_map. f_equal. apply map_ext_in.
  intros step MEMBER. rewrite mathematical_starts_have_translated_triangular_group_coordinates by assumption.
  unfold power_bucket_count. apply an_original_group_window_is_its_circular_block.
  - apply power_group_count_is_positive.
  - unfold translated_group. apply Nat.mod_upper_bound. pose proof (power_group_count_is_positive exponent). lia.
  - exact RESIDUE.
Qed.

Lemma canonical_group_blocks_flatten_to_the_bucket_range : forall groups,
  flat_map (fun group => seq (16 * group) 16) (seq 0 groups) = seq 0 (16 * groups).
Proof.
  intro groups.
  pose proof (clipped_group_prefix_is_a_contiguous_sequence groups (16 * groups)) as CLIPPED.
  rewrite Nat.min_id in CLIPPED. rewrite flat_map_concat_map, <- CLIPPED.
  f_equal. apply map_ext_in. intros group MEMBER. apply in_seq in MEMBER.
  rewrite Nat.min_l by lia. f_equal. lia.
Qed.

Lemma mapping_flattened_blocks : forall (transform : nat -> nat) (blocks : nat -> list nat) indices,
  flat_map (fun index => map transform (blocks index)) indices =
    map transform (flat_map blocks indices).
Proof.
  intros transform blocks indices. induction indices as [|index rest IH]; [reflexivity|].
  cbn [flat_map]. now rewrite map_app, IH.
Qed.

Lemma circular_blocks_flatten_to_a_translated_range : forall groups residue,
  flat_map (circular_block (16 * groups) residue) (seq 0 groups) =
    map (fun index => (residue + index) mod (16 * groups)) (seq 0 (16 * groups)).
Proof.
  intros groups residue.
  assert (BLOCK : forall group, circular_block (16 * groups) residue group =
    map (fun index => (residue + index) mod (16 * groups)) (seq (16 * group) 16)).
  { intro group. rewrite (a_sequence_starts_by_translation 16 (16 * group)), map_map. reflexivity. }
  rewrite (flat_map_ext _ _ BLOCK).
  rewrite mapping_flattened_blocks, canonical_group_blocks_flatten_to_the_bucket_range. reflexivity.
Qed.

Theorem a_complete_mathematical_cycle_permutes_all_original_buckets : forall exponent initial,
  initial < power_bucket_count exponent ->
  Permutation (complete_originals exponent initial) (seq 0 (power_bucket_count exponent)).
Proof.
  intros exponent initial INITIAL. pose proof (power_group_count_is_positive exponent) as POSITIVE.
  pose proof (Nat.div_mod initial 16 ltac:(lia)) as DIVISION.
  pose proof (Nat.mod_upper_bound initial 16 ltac:(lia)) as RESIDUE.
  assert (GROUP : initial / 16 < power_group_count exponent).
  { unfold power_bucket_count in INITIAL. nia. }
  replace initial with (16 * (initial / 16) + initial mod 16) at 1 by lia.
  rewrite complete_originals_are_translated_circular_blocks by assumption.
  apply Permutation_trans with (l' := flat_map
    (circular_block (power_bucket_count exponent) (initial mod 16))
    (seq 0 (power_group_count exponent))).
  - apply Permutation_flat_map. apply translated_triangular_groups_permute_the_range. exact GROUP.
  - unfold power_bucket_count. rewrite circular_blocks_flatten_to_a_translated_range.
    apply cyclic_translation_permutes_the_complete_range; lia.
Qed.

Theorem a_complete_mathematical_cycle_never_repeats_an_original_bucket : forall exponent initial,
  initial < power_bucket_count exponent -> NoDup (complete_originals exponent initial).
Proof.
  intros exponent initial INITIAL.
  eapply Permutation_NoDup; [symmetry; apply a_complete_mathematical_cycle_permutes_all_original_buckets; exact INITIAL|].
  apply seq_NoDup.
Qed.

Lemma an_original_cycle_member_has_a_physical_lane : forall exponent initial index,
  In index (complete_originals exponent initial) ->
  exists step lane, step < power_group_count exponent /\ lane < 16 /\
    allocated_lane (power_bucket_count exponent)
      (mathematical_start exponent initial step + lane) = Some index.
Proof.
  intros exponent initial index MEMBER. unfold complete_originals, original_slots in MEMBER.
  apply in_flat_map in MEMBER as [slot [IN_WINDOWS ORIGINAL]].
  destruct slot as [original|]; cbn in ORIGINAL; [|contradiction].
  destruct ORIGINAL as [SAME|IMPOSSIBLE]; [subst original|contradiction].
  apply in_concat in IN_WINDOWS as [window [IN_CYCLE IN_WINDOW]].
  unfold complete_windows in IN_CYCLE. apply in_map_iff in IN_CYCLE as [step [WINDOW STEP]].
  subst window. apply in_seq in STEP. unfold allocated_window in IN_WINDOW.
  apply in_map_iff in IN_WINDOW as [physical [SLOT POSITION]]. apply in_seq in POSITION.
  exists step, (physical - mathematical_start exponent initial step).
  repeat split; try lia.
  replace (mathematical_start exponent initial step +
    (physical - mathematical_start exponent initial step)) with physical by lia. exact SLOT.
Qed.

(** This witness interface also applies to resize target prefixes whose
    physical FULL occupancy is not yet reflected in native items counters.
    The caller must derive an actual EMPTY predicate witness; a nonFULL
    witness alone is insufficient when DELETED controls are possible. *)
Theorem an_original_empty_witness_has_a_physical_lane_in_the_mathematical_cycle :
  forall exponent initial original_empty physical_empty index,
  initial < power_bucket_count exponent -> index < power_bucket_count exponent ->
  original_empty index = true ->
  physical_predicate_projects (power_bucket_count exponent) original_empty true physical_empty ->
  exists step lane, step < power_group_count exponent /\ lane < 16 /\
    physical_empty (mathematical_start exponent initial step + lane) = true.
Proof.
  intros exponent initial original_empty physical_empty index INITIAL INDEX EMPTY PHYSICAL.
  assert (IN_CYCLE : In index (complete_originals exponent initial)).
  { eapply Permutation_in.
    - symmetry. apply a_complete_mathematical_cycle_permutes_all_original_buckets. exact INITIAL.
    - apply in_seq. lia. }
  destruct (an_original_cycle_member_has_a_physical_lane exponent initial index IN_CYCLE)
    as [step [lane [STEP [LANE SLOT]]]].
  exists step, lane. split; [exact STEP|]. split; [exact LANE|].
  pose proof (every_mathematical_start_is_within_its_table exponent initial step) as START.
  unfold physical_predicate_projects in PHYSICAL. rewrite PHYSICAL by lia.
  rewrite SLOT. exact EMPTY.
Qed.

Theorem coherent_source_controls_have_an_empty_lane_in_the_mathematical_cycle :
  forall exponent initial table full tombstone physical_empty,
  valid_counters table -> coherent_control_counts table full tombstone ->
  buckets table = power_bucket_count exponent -> initial < power_bucket_count exponent ->
  physical_predicate_projects (power_bucket_count exponent) (empty_slot full tombstone) true physical_empty ->
  exists step lane, step < power_group_count exponent /\ lane < 16 /\
    physical_empty (mathematical_start exponent initial step + lane) = true.
Proof.
  intros exponent initial table full tombstone physical_empty VALID COHERENT BUCKETS INITIAL PHYSICAL.
  pose proof (coherent_native_counts_have_a_positive_empty_class table full tombstone VALID COHERENT)
    as [_ EMPTY_COUNT].
  unfold source_entry_count in EMPTY_COUNT. rewrite BUCKETS in EMPTY_COUNT.
  rewrite source_groups_count_the_original_filtered_bucket_range in EMPTY_COUNT
    by apply power_bucket_count_is_positive.
  destruct (filter (empty_slot full tombstone) (seq 0 (power_bucket_count exponent)))
    as [|index rest] eqn:EMPTY_SLOTS; [cbn in EMPTY_COUNT; lia|].
  assert (MEMBER : In index (filter (empty_slot full tombstone) (seq 0 (power_bucket_count exponent)))).
  { rewrite EMPTY_SLOTS. now left. }
  apply filter_In in MEMBER as [BUCKET EMPTY]. apply in_seq in BUCKET.
  apply (an_original_empty_witness_has_a_physical_lane_in_the_mathematical_cycle
    exponent initial (empty_slot full tombstone) physical_empty index); assumption || lia.
Qed.

Theorem small_source_windows_have_empty_padding_without_counter_premises :
  forall bucket_count initial full tombstone physical_empty,
  (bucket_count = 4 \/ bucket_count = 8) -> initial < bucket_count ->
  physical_predicate_projects bucket_count (empty_slot full tombstone) true physical_empty ->
  exists lane, lane < 16 /\ physical_empty (initial + lane) = true.
Proof.
  intros bucket_count initial full tombstone physical_empty SMALL INITIAL PHYSICAL.
  exists (bucket_count - initial). split; [lia|].
  replace (initial + (bucket_count - initial)) with bucket_count by lia.
  unfold physical_predicate_projects in PHYSICAL. rewrite PHYSICAL by lia.
  rewrite allocated_small_padding_lane by lia. reflexivity.
Qed.

Theorem the_static_singleton_projects_only_empty_lanes : forall original,
  map (observe_lane true original) singleton_window = repeat true 16 /\
  original_slots singleton_window = [].
Proof. intro original. split; reflexivity. Qed.

End NativeHashBagProbeCoverage.

Print Assumptions NativeHashBagProbeCoverage.every_mathematical_start_is_within_its_table.
Print Assumptions NativeHashBagProbeCoverage.mathematical_starts_have_translated_triangular_group_coordinates.
Print Assumptions NativeHashBagProbeCoverage.a_complete_mathematical_cycle_permutes_all_original_buckets.
Print Assumptions NativeHashBagProbeCoverage.a_complete_mathematical_cycle_never_repeats_an_original_bucket.
Print Assumptions NativeHashBagProbeCoverage.an_original_empty_witness_has_a_physical_lane_in_the_mathematical_cycle.
Print Assumptions NativeHashBagProbeCoverage.coherent_source_controls_have_an_empty_lane_in_the_mathematical_cycle.
Print Assumptions NativeHashBagProbeCoverage.small_source_windows_have_empty_padding_without_counter_premises.
Print Assumptions NativeHashBagProbeCoverage.the_static_singleton_projects_only_empty_lanes.
