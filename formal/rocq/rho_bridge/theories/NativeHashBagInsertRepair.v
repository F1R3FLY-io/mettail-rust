(** Local source refinement of pinned hashbrown 0.17.1 fix_insert_index.
    raw.rs:1709 tests is_bucket_full(index), whose :2644 implementation
    reads the original control byte and applies Tag::is_full. Only the FULL
    branch loads Group::load_aligned(ctrl(0)), selects the lowest special
    bit, unwraps it and returns that bit directly. There is no second probe
    loop and no second index mask in this branch.

    An incoming index must originate in find_insert_index_in_group (:1749),
    possibly retained by fill_absent_cache from an earlier window of the SAME
    immutable controls. The origin below retains that source requirement;
    it does not assume that the index denotes a nonFULL original bucket.
    Large-table nonFULL validity is derived from the original/mirror map.
    Small-table repair validity is derived from an original special witness
    before padding, not from the mere existence of EMPTY padding.

    The FULL/special identity is proved for natural tag values using the
    exact bit operations; no extra cap on native byte tags is imposed.
    Reading initialized controls, the control-base alignment and allocation
    provenance, and intrinsic contracts are source obligations. Existing
    Layout laws cover the originating position+bit addition and aligned
    control offset. These mathematical tags do not establish pointer safety.
    The empty singleton is not an allocated repair target. Source callers
    must obtain an original EMPTY/nonFULL witness before invoking placement;
    coherent original counts or the fresh resize occupancy proof supply it.

    [NativeRepairReturn] records only the exact aligned-load address list,
    not arbitrary costs or callback events. A successful fallback constructor
    retains the native Some guard; the final theorem derives its existence
    and valid destination rather than requiring either as a premise. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagProbeWindows NativeHashBagProbeMasks.
Import ListNotations.

Module NativeHashBagInsertRepair.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.
Import NativeHashBagProbeMasks.NativeHashBagProbeMasks.

Theorem native_full_is_the_complement_of_the_special_bit : forall tag,
  tag_is_full tag = negb (tag_is_special tag).
Proof.
  intro tag. unfold tag_is_full, tag_is_special.
  destruct (Nat.testbit tag 7) eqn:SPECIAL; cbn [negb].
  - apply Nat.eqb_neq. intro ZERO.
    pose proof (Nat.land_spec tag 128 7) as BIT.
    change (Nat.testbit (Nat.land tag 128) 7 = Nat.testbit tag 7 && true) in BIT.
    rewrite ZERO, Nat.bits_0, SPECIAL in BIT. discriminate BIT.
  - apply Nat.eqb_eq. apply Nat.bits_inj_0. intro bit. rewrite Nat.land_spec.
    change (Nat.testbit tag bit && Nat.testbit (2 ^ 7) bit = false).
    rewrite Nat.pow2_bits_eqb. destruct (7 =? bit) eqn:POSITION.
    + apply Nat.eqb_eq in POSITION. subst bit. now rewrite SPECIAL.
    + apply Bool.andb_false_r.
Qed.

Lemma an_original_empty_tag_is_nonfull : tag_is_full 255 = false.
Proof. reflexivity. Qed.

(** Work directly with the existing ordered predicate, avoiding symbolic
    pack_mask expansion when extracting the fixed-width least-bit facts. *)
Lemma selected_lane_is_the_least_matching_physical_lane : forall predicate bit,
  lowest_mask predicate = Some bit ->
  bit < 16 /\ predicate bit = true /\
  (forall earlier, earlier < bit -> predicate earlier = false).
Proof.
  intros predicate bit LOWEST. rewrite native_lowest_bit_agrees_with_ordered_lanes in LOWEST.
  destruct (first_filtered_sequence_member_is_least 16 0 predicate bit LOWEST)
    as [RANGE [MATCH EARLIER]].
  split; [lia|]. split; [exact MATCH|]. intros earlier BEFORE. apply EARLIER. lia.
Qed.

Definition insertion_origin bucket_count physical cached :=
  exists position, position < bucket_count /\
    insertion_slot bucket_count position physical = Some cached.
Definition cache_has_insertion_origin bucket_count physical cached :=
  match cached with None => True | Some index => insertion_origin bucket_count physical index end.

Theorem filling_an_absent_cache_preserves_its_original_selection :
  forall bucket_count physical position cached,
  position < bucket_count -> cache_has_insertion_origin bucket_count physical cached ->
  cache_has_insertion_origin bucket_count physical
    (fill_absent_cache bucket_count position physical cached).
Proof.
  intros bucket_count physical position [cached|] POSITION ORIGIN; [exact ORIGIN|].
  change (cache_has_insertion_origin bucket_count physical
    (insertion_slot bucket_count position physical)).
  destruct (insertion_slot bucket_count position physical) as [index|] eqn:SLOT;
    cbn [cache_has_insertion_origin]; [|exact I].
  exists position. now split.
Qed.

(** Keep option inversion abstract. Directly destructing the concrete
    lowest_mask expression and inverting its mapped Some equation caused
    coqc1 to spend its 60-second limit checking the caller's Qed: conversion
    can expand the symbolic 16-lane packed mask. This opaque helper performs
    the same inversion without exposing any mask or native-index operation. *)
Lemma a_mapped_optional_selection_exposes_its_selected_value :
  forall (selection : option nat) (project : nat -> nat) result,
  (match selection with Some value => Some (project value) | None => None end) =
    Some result ->
  exists value, selection = Some value /\ result = project value.
Proof.
  intros [value|] project result SELECTED; [|discriminate SELECTED].
  exists value. split; [reflexivity|].
  injection SELECTED as EQUAL. now symmetry.
Qed.

(** coqc2 checked the abstract helper immediately but timed out converting
    SLOT at its concrete application. Unfold only the source wrapper; keep
    the already verified lowest-mask implementation opaque during this
    bridge so conversion compares the identical selection expressions. *)
Local Opaque lowest_mask.
Lemma an_insertion_origin_exposes_its_actual_masked_lane :
  forall bucket_count physical cached,
  insertion_origin bucket_count physical cached ->
  exists position bit, position < bucket_count /\ bit < 16 /\
    special_match physical position bit = true /\
    cached = Nat.land (position + bit) (bucket_count - 1).
Proof.
  intros bucket_count physical cached [position [POSITION SLOT]].
  unfold insertion_slot in SLOT.
  destruct (a_mapped_optional_selection_exposes_its_selected_value
    (lowest_mask (special_match physical position))
    (fun bit => Nat.land (position + bit) (bucket_count - 1)) cached SLOT)
    as [bit [LOWEST MASK]].
  destruct (selected_lane_is_the_least_matching_physical_lane _ _ LOWEST)
    as [BIT [SPECIAL _]].
  exists position, bit. repeat split; assumption || reflexivity.
Qed.
Local Transparent lowest_mask.

Theorem an_original_selected_index_is_within_the_native_table :
  forall exponent physical cached,
  insertion_origin (2 ^ (exponent + 2)) physical cached -> cached < 2 ^ (exponent + 2).
Proof.
  intros exponent physical cached ORIGIN.
  destruct (an_insertion_origin_exposes_its_actual_masked_lane _ _ _ ORIGIN)
    as [position [bit [_ [_ [_ MASK]]]]].
  rewrite MASK, native_power_of_two_mask_is_modulo.
  apply Nat.mod_upper_bound. apply Nat.pow_nonzero. lia.
Qed.

Theorem a_large_table_original_selection_cannot_trigger_repair :
  forall exponent original physical cached,
  16 <= 2 ^ (exponent + 2) ->
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  insertion_origin (2 ^ (exponent + 2)) physical cached ->
  tag_is_full (physical cached) = false.
Proof.
  intros exponent original physical cached LARGE PROJECT ORIGIN.
  pose proof (an_original_selected_index_is_within_the_native_table _ _ _ ORIGIN) as CACHED.
  destruct (an_insertion_origin_exposes_its_actual_masked_lane _ _ _ ORIGIN)
    as [position [bit [POSITION [BIT [SPECIAL MASK]]]]].
  assert (SLOT : allocated_lane (2 ^ (exponent + 2)) (position + bit) = Some cached).
  { rewrite large_allocated_lane_is_the_circular_original by lia.
    rewrite MASK, native_power_of_two_mask_is_modulo. reflexivity. }
  pose proof (PROJECT (position + bit) ltac:(lia)) as SELECTED.
  rewrite SLOT in SELECTED.
  pose proof (PROJECT cached ltac:(lia)) as ORIGINAL.
  rewrite allocated_original_lane in ORIGINAL by exact CACHED.
  unfold special_match in SPECIAL. rewrite SELECTED in SPECIAL.
  rewrite ORIGINAL, native_full_is_the_complement_of_the_special_bit, SPECIAL. reflexivity.
Qed.

Theorem a_true_repair_guard_implies_a_small_allocated_table :
  forall exponent original physical cached,
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  insertion_origin (2 ^ (exponent + 2)) physical cached ->
  tag_is_full (physical cached) = true ->
  2 ^ (exponent + 2) = 4 \/ 2 ^ (exponent + 2) = 8.
Proof.
  intros exponent original physical cached PROJECT ORIGIN FULL.
  destruct (allocated_power_size_is_small_or_large exponent) as [FOUR|[EIGHT|LARGE]];
    [now left|now right|].
  pose proof (a_large_table_original_selection_cannot_trigger_repair
    exponent original physical cached LARGE PROJECT ORIGIN). congruence.
Qed.

Theorem a_small_aligned_scan_selects_an_original_special_before_padding :
  forall bucket_count original physical witness,
  (bucket_count = 4 \/ bucket_count = 8) ->
  physical_tags_project bucket_count original physical ->
  witness < bucket_count -> tag_is_full (original witness) = false ->
  exists bit, lowest_mask (special_match physical 0) = Some bit /\
    bit <= witness /\ bit < bucket_count /\
    allocated_lane bucket_count bit = Some bit /\ tag_is_full (physical bit) = false.
Proof.
  intros bucket_count original physical witness SMALL PROJECT WITNESS NONFULL.
  assert (SPECIAL : special_match physical 0 witness = true).
  { unfold special_match. rewrite Nat.add_0_l, PROJECT by lia.
    rewrite allocated_original_lane by exact WITNESS.
    rewrite native_full_is_the_complement_of_the_special_bit in NONFULL.
    now apply Bool.negb_false_iff in NONFULL. }
  destruct (a_matching_lane_enables_native_lowest_bit
    (special_match physical 0) witness ltac:(lia) SPECIAL) as [bit LOWEST].
  destruct (selected_lane_is_the_least_matching_physical_lane _ _ LOWEST)
    as [LANE [MATCH EARLIER]].
  assert (BEFORE : bit <= witness).
  { destruct (bit <=? witness) eqn:ORDER; [now apply Nat.leb_le in ORDER|].
    apply Nat.leb_gt in ORDER. specialize (EARLIER witness ORDER). congruence. }
  exists bit. split; [exact LOWEST|]. split; [exact BEFORE|]. split; [lia|]. split.
  - apply allocated_original_lane. lia.
  - unfold special_match in MATCH. rewrite Nat.add_0_l in MATCH.
    rewrite native_full_is_the_complement_of_the_special_bit, MATCH. reflexivity.
Qed.

(** Aligned-load addresses only: [] or [0]. The actual function does not
    loop or request equality callbacks. The fallback returns its bit as-is. *)
Inductive NativeRepairReturn (physical : nat -> nat) : nat -> list nat -> nat -> Prop :=
| RepairKeepsOriginal : forall cached,
    tag_is_full (physical cached) = false -> NativeRepairReturn physical cached [] cached
| RepairLoadsAlignedOnce : forall cached bit,
    tag_is_full (physical cached) = true ->
    lowest_mask (special_match physical 0) = Some bit ->
    NativeRepairReturn physical cached [0] bit.

Theorem every_repair_return_has_exactly_the_branch_load_trace :
  forall physical cached loads result,
  NativeRepairReturn physical cached loads result ->
  length loads <= 1 /\
  (tag_is_full (physical cached) = false -> loads = [] /\ result = cached) /\
  (tag_is_full (physical cached) = true -> loads = [0]).
Proof.
  intros physical cached loads result RETURN.
  destruct RETURN as [cached NONFULL|cached bit FULL LOWEST].
  - split; [cbn; lia|]. split.
    + intro GUARD. split; reflexivity.
    + intro GUARD. congruence.
  - split; [cbn; lia|]. split.
    + intro GUARD. congruence.
    + intro GUARD. reflexivity.
Qed.

Theorem an_original_selected_index_repairs_to_a_nonfull_original_slot :
  forall exponent original physical cached witness,
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  insertion_origin (2 ^ (exponent + 2)) physical cached ->
  witness < 2 ^ (exponent + 2) -> tag_is_full (original witness) = false ->
  exists loads result, NativeRepairReturn physical cached loads result /\
    result < 2 ^ (exponent + 2) /\ tag_is_full (physical result) = false /\ length loads <= 1.
Proof.
  intros exponent original physical cached witness PROJECT ORIGIN WITNESS NONFULL.
  destruct (tag_is_full (physical cached)) eqn:FULL.
  - pose proof (a_true_repair_guard_implies_a_small_allocated_table
      exponent original physical cached PROJECT ORIGIN FULL) as SMALL.
    destruct (a_small_aligned_scan_selects_an_original_special_before_padding
      _ original physical witness SMALL PROJECT WITNESS NONFULL)
      as [bit [LOWEST [BEFORE [BOUND [SLOT SPECIAL]]]]].
    exists [0], bit. split; [now apply RepairLoadsAlignedOnce|].
    split; [exact BOUND|]. split; [exact SPECIAL|cbn; lia].
  - exists [], cached. split; [now apply RepairKeepsOriginal|].
    split; [exact (an_original_selected_index_is_within_the_native_table
      exponent physical cached ORIGIN)|].
    split; [exact FULL|cbn; lia].
Qed.

End NativeHashBagInsertRepair.

Print Assumptions NativeHashBagInsertRepair.native_full_is_the_complement_of_the_special_bit.
Print Assumptions NativeHashBagInsertRepair.filling_an_absent_cache_preserves_its_original_selection.
Print Assumptions NativeHashBagInsertRepair.an_original_selected_index_is_within_the_native_table.
Print Assumptions NativeHashBagInsertRepair.a_large_table_original_selection_cannot_trigger_repair.
Print Assumptions NativeHashBagInsertRepair.a_true_repair_guard_implies_a_small_allocated_table.
Print Assumptions NativeHashBagInsertRepair.a_small_aligned_scan_selects_an_original_special_before_padding.
Print Assumptions NativeHashBagInsertRepair.every_repair_return_has_exactly_the_branch_load_trace.
Print Assumptions NativeHashBagInsertRepair.an_original_selected_index_repairs_to_a_nonfull_original_slot.
