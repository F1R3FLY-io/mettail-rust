(** Native probe masks for pinned hashbrown 0.17.1 on its SSE2 backend.
    control/group/sse2.rs uses 16 byte lanes, cmpeq_epi8 followed by
    movemask_epi8 for tag equality, and movemask_epi8 directly for the
    special-tag mask. control/bitmask.rs uses u16, stride 1 and an all-ones
    iteration mask. Its nonzero trailing_zeros result is the least set bit.

    [pack_mask] is the integer denotation of those 16 output bits, not a
    replacement runtime probe. [lowest_word] denotes the fixed-width least
    set bit; the theorems connect it to bit positions and ordered lanes.
    Interpreting these definitions as the compiled intrinsics still requires
    their ordinary instruction contracts. No compiler or x86 semantics is
    axiomatized here. The numeric clear-lowest operation m & (m-1), subsequent
    BitMaskIter steps, and callback entry/return events remain later work.

    raw.rs:1754 computes the insertion (pos+bit)&bucket_mask; :1824 computes
    the matched candidate and :1834 fills an absent cache before checking
    EMPTY. The mask/modulo equality below is
    proved, not substituted by fiat. Physical tags must describe the same
    readable immutable native controls and set_ctrl mirror layout as the
    preceding window/coverage models. Mathematical positions are not proof
    of native loop reachability; Layout supplies the addition guard only.
    Padding may enable the insertion cache but is not an insertion bucket.
    Singleton storage, insertion repair, callback completion/work and the
    eventual EMPTY barrier of the source loop are deliberately separate. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagProbeWindows NativeHashBagLayout.
Import ListNotations.

Module NativeHashBagProbeMasks.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.
Import NativeHashBagLayout.NativeHashBagLayout.

Fixpoint pack_mask (width offset : nat) (predicate : nat -> bool) : nat :=
  match width with
  | 0 => 0
  | S rest =>
      if predicate offset then 2 * pack_mask rest (S offset) predicate + 1
      else 2 * pack_mask rest (S offset) predicate
  end.
Definition movemask predicate := pack_mask 16 0 predicate.
Definition ordered_lanes predicate := filter predicate (seq 0 16).
Definition lowest_word word :=
  hd_error (filter (Nat.testbit word) (seq 0 16)).
Definition lowest_mask predicate := lowest_word (movemask predicate).
Definition any_mask predicate := negb (Nat.eqb (movemask predicate) 0).

Lemma packed_bits_are_exact : forall width offset predicate bit,
  Nat.testbit (pack_mask width offset predicate) bit =
    if bit <? width then predicate (offset + bit) else false.
Proof.
  induction width as [|width IH]; intros offset predicate [|bit].
  - apply Nat.bits_0.
  - apply Nat.bits_0.
  - cbn [pack_mask]. rewrite Nat.add_0_r.
    destruct (predicate offset); [apply Nat.testbit_odd_0|apply Nat.testbit_even_0].
  - cbn [pack_mask]. destruct (predicate offset).
    + rewrite Nat.testbit_odd_succ', IH.
      replace (offset + S bit) with (S offset + bit) by lia. reflexivity.
    + rewrite Nat.testbit_even_succ', IH.
      replace (offset + S bit) with (S offset + bit) by lia. reflexivity.
Qed.

Lemma packed_bits_fit_their_width : forall width offset predicate,
  pack_mask width offset predicate < 2 ^ width.
Proof.
  induction width as [|width IH]; intros offset predicate; cbn [pack_mask Nat.pow].
  - lia.
  - specialize (IH (S offset) predicate). destruct (predicate offset); lia.
Qed.

Theorem sse2_mask_has_exact_lane_bits_and_u16_range : forall predicate,
  movemask predicate < 2 ^ 16 /\
  (forall bit, Nat.testbit (movemask predicate) bit =
    if bit <? 16 then predicate bit else false).
Proof.
  intros predicate. split; [apply packed_bits_fit_their_width|].
  intro bit. unfold movemask. rewrite packed_bits_are_exact. reflexivity.
Qed.

Lemma mask_bit_inside : forall predicate bit, bit < 16 ->
  Nat.testbit (movemask predicate) bit = predicate bit.
Proof.
  intros predicate bit INSIDE. unfold movemask. rewrite packed_bits_are_exact.
  rewrite (proj2 (Nat.ltb_lt bit 16) INSIDE). reflexivity.
Qed.

Theorem native_lowest_bit_agrees_with_ordered_lanes : forall predicate,
  lowest_mask predicate = hd_error (ordered_lanes predicate).
Proof.
  intro predicate. unfold lowest_mask, lowest_word, ordered_lanes.
  f_equal. apply filter_ext_in. intros bit MEMBER. apply in_seq in MEMBER.
  apply mask_bit_inside. lia.
Qed.

Lemma first_filtered_sequence_member_is_least : forall count start predicate bit,
  hd_error (filter predicate (seq start count)) = Some bit ->
  start <= bit < start + count /\ predicate bit = true /\
  (forall earlier, start <= earlier < bit -> predicate earlier = false).
Proof.
  induction count as [|count IH]; intros start predicate bit FIRST.
  - discriminate FIRST.
  - cbn [seq filter] in FIRST. destruct (predicate start) eqn:HEAD.
    + inversion FIRST; subst bit. repeat split; try lia; assumption.
    + destruct (IH (S start) predicate bit FIRST) as [RANGE [MATCH EARLIER]].
      repeat split; try lia; try assumption.
      intros earlier BOUNDS. destruct (Nat.eq_dec earlier start) as [->|DIFFERENT].
      * exact HEAD.
      * apply EARLIER. lia.
Qed.

Theorem native_lowest_bit_has_the_trailing_zeros_specification : forall predicate bit,
  lowest_mask predicate = Some bit ->
  bit < 16 /\ Nat.testbit (movemask predicate) bit = true /\
  (forall earlier, earlier < bit ->
    Nat.testbit (movemask predicate) earlier = false).
Proof.
  intros predicate bit FIRST. rewrite native_lowest_bit_agrees_with_ordered_lanes in FIRST.
  destruct (first_filtered_sequence_member_is_least 16 0 predicate bit FIRST)
    as [RANGE [MATCH EARLIER]]. split; [lia|]. split.
  - rewrite mask_bit_inside by lia. exact MATCH.
  - intros earlier BEFORE. rewrite mask_bit_inside by lia. apply EARLIER. lia.
Qed.

Lemma mask_zero_iff_no_ordered_lanes : forall predicate,
  movemask predicate = 0 <-> ordered_lanes predicate = [].
Proof.
  intro predicate. split.
  - intros ZERO. destruct (ordered_lanes predicate) as [|bit rest] eqn:LANES;
      [reflexivity|].
    assert (MEMBER : In bit (ordered_lanes predicate)) by (rewrite LANES; now left).
    unfold ordered_lanes in MEMBER. apply filter_In in MEMBER.
    destruct MEMBER as [RANGE MATCH]. apply in_seq in RANGE.
    pose proof (mask_bit_inside predicate bit ltac:(lia)) as BIT.
    rewrite ZERO, Nat.bits_0, MATCH in BIT. discriminate BIT.
  - intros EMPTY. apply Nat.bits_inj_0. intro bit.
    unfold movemask. rewrite packed_bits_are_exact. cbn [Nat.add].
    destruct (bit <? 16) eqn:INSIDE; [|reflexivity].
    apply Nat.ltb_lt in INSIDE. destruct (predicate bit) eqn:MATCH; [|reflexivity].
    assert (MEMBER : In bit (ordered_lanes predicate)).
    { unfold ordered_lanes. apply filter_In. split; [apply in_seq; lia|exact MATCH]. }
    rewrite EMPTY in MEMBER. contradiction.
Qed.

Theorem a_matching_lane_enables_native_lowest_bit : forall predicate bit,
  bit < 16 -> predicate bit = true ->
  exists first, lowest_mask predicate = Some first.
Proof.
  intros predicate bit INSIDE MATCH.
  rewrite native_lowest_bit_agrees_with_ordered_lanes.
  assert (MEMBER : In bit (ordered_lanes predicate)).
  { apply filter_In. split; [apply in_seq; lia|exact MATCH]. }
  destruct (ordered_lanes predicate) as [|first rest]; [contradiction|].
  exists first. reflexivity.
Qed.

Theorem native_any_bit_set_iff_a_matching_lane : forall predicate,
  any_mask predicate = true <-> exists bit, bit < 16 /\ predicate bit = true.
Proof.
  intro predicate. unfold any_mask. rewrite Bool.negb_true_iff, Nat.eqb_neq.
  split.
  - intros NONZERO. destruct (ordered_lanes predicate) as [|bit rest] eqn:LANES.
    + exfalso. apply NONZERO. apply mask_zero_iff_no_ordered_lanes. exact LANES.
    + exists bit. assert (MEMBER : In bit (ordered_lanes predicate))
        by (rewrite LANES; now left).
      apply filter_In in MEMBER. destruct MEMBER as [RANGE MATCH].
      apply in_seq in RANGE. split; [lia|exact MATCH].
  - intros [bit [INSIDE MATCH]] ZERO.
    pose proof (mask_bit_inside predicate bit INSIDE) as BIT.
    rewrite ZERO, Nat.bits_0, MATCH in BIT. discriminate BIT.
Qed.

Definition optional_trailing_zeros_spec word result :=
  match result with
  | None => word = 0
  | Some bit => bit < 16 /\ Nat.testbit word bit = true /\
      (forall earlier, earlier < bit -> Nat.testbit word earlier = false)
  end.

Theorem the_optional_native_lowest_bit_is_uniquely_characterized : forall predicate result,
  lowest_mask predicate = result <->
  optional_trailing_zeros_spec (movemask predicate) result.
Proof.
  intros predicate [bit|]; cbn [optional_trailing_zeros_spec].
  - split; [apply native_lowest_bit_has_the_trailing_zeros_specification|].
    intros [INSIDE [SET EARLIER]].
    assert (MATCH : predicate bit = true) by (rewrite <- mask_bit_inside by assumption; exact SET).
    destruct (a_matching_lane_enables_native_lowest_bit predicate bit INSIDE MATCH)
      as [first FIRST].
    destruct (native_lowest_bit_has_the_trailing_zeros_specification predicate first FIRST)
      as [FIRST_INSIDE [FIRST_SET FIRST_EARLIER]].
    assert (SAME : first = bit).
    { destruct (Nat.lt_trichotomy first bit) as [LESS|[SAME|GREATER]]; [|assumption|].
      - rewrite (EARLIER first LESS) in FIRST_SET. discriminate FIRST_SET.
      - rewrite (FIRST_EARLIER bit GREATER) in SET. discriminate SET. }
    now subst first.
  - rewrite native_lowest_bit_agrees_with_ordered_lanes.
    rewrite mask_zero_iff_no_ordered_lanes.
    destruct (ordered_lanes predicate); cbn [hd_error]; split; congruence.
Qed.

(** The bitwise AND in native slot calculation is retained literally. *)
Theorem native_power_of_two_mask_is_modulo : forall value exponent,
  Nat.land value (2 ^ exponent - 1) = value mod (2 ^ exponent).
Proof.
  intros value exponent.
  replace (2 ^ exponent - 1) with (Nat.ones exponent).
  - apply Nat.land_ones.
  - rewrite Nat.ones_equiv. lia.
Qed.

Definition full_tag top_seven := Nat.land top_seven 127.
Definition tag_is_full tag := Nat.eqb (Nat.land tag 128) 0.
Definition tag_is_special tag := Nat.testbit tag 7.
Definition tag_match (physical : nat -> nat) start tag bit :=
  Nat.eqb (physical (start + bit)) tag.
Definition special_match (physical : nat -> nat) start bit :=
  tag_is_special (physical (start + bit)).

Lemma full_tag_is_in_the_entire_seven_bit_range : forall top_seven,
  full_tag top_seven < 128.
Proof.
  intro top_seven. unfold full_tag.
  change (Nat.land top_seven (2 ^ 7 - 1) < 2 ^ 7).
  rewrite native_power_of_two_mask_is_modulo. apply Nat.mod_upper_bound. discriminate.
Qed.

Lemma a_seven_bit_tag_is_native_full : forall tag,
  tag < 128 -> tag_is_full tag = true.
Proof.
  intros tag FULL. unfold tag_is_full. apply Nat.eqb_eq.
  apply Nat.bits_inj_0. intro bit. rewrite Nat.land_spec.
  change (Nat.testbit tag bit && Nat.testbit (2 ^ 7) bit = false).
  rewrite Nat.pow2_bits_eqb. destruct (7 =? bit) eqn:POSITION.
  - apply Nat.eqb_eq in POSITION. subst bit. rewrite Bool.andb_true_r.
    replace tag with (tag mod 2 ^ 7) at 1 by (apply Nat.mod_small; exact FULL).
    apply Nat.mod_pow2_bits_high. lia.
  - apply Bool.andb_false_r.
Qed.

Definition physical_tags_project bucket_count original physical :=
  forall offset, offset < bucket_count + 16 ->
  physical offset = match allocated_lane bucket_count offset with
    | Some index => original index
    | None => 255
    end.

Lemma small_original_lane_projects_to_the_native_modulus : forall bucket_count physical index,
  (bucket_count = 4 \/ bucket_count = 8) -> physical < bucket_count + 16 ->
  allocated_lane bucket_count physical = Some index ->
  index < bucket_count /\ index = physical mod bucket_count.
Proof.
  intros bucket_count physical index SMALL DOMAIN LANE.
  unfold allocated_lane in LANE. destruct (physical <? bucket_count) eqn:ORIGINAL.
  - apply Nat.ltb_lt in ORIGINAL. inversion LANE; subst index.
    split; [assumption|symmetry; apply Nat.mod_small; assumption].
  - assert (NARROW : (bucket_count <? 16) = true) by (apply Nat.ltb_lt; lia).
    rewrite NARROW in LANE. destruct (physical <? 16) eqn:PADDING;
      [discriminate LANE|].
    apply Nat.ltb_ge in PADDING. inversion LANE; subst index. split; [lia|].
    destruct SMALL as [FOUR|EIGHT]; subst bucket_count.
    + apply Nat.mod_unique with (q := 4); lia.
    + apply Nat.mod_unique with (q := 2); lia.
Qed.

Lemma allocated_power_size_is_small_or_large : forall exponent,
  2 ^ (exponent + 2) = 4 \/ 2 ^ (exponent + 2) = 8 \/ 16 <= 2 ^ (exponent + 2).
Proof.
  intros [|[|exponent]];
    [left; reflexivity|right; left; reflexivity|right; right].
  replace (S (S exponent) + 2) with (exponent + 4) by lia.
  rewrite Nat.pow_add_r.
  pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). cbn [Nat.pow]. nia.
Qed.

Lemma allocated_original_lane_has_the_bitmasked_index : forall exponent physical index,
  physical < 2 ^ (exponent + 2) + 16 ->
  allocated_lane (2 ^ (exponent + 2)) physical = Some index ->
  index < 2 ^ (exponent + 2) /\
  index = Nat.land physical (2 ^ (exponent + 2) - 1).
Proof.
  intros exponent physical index DOMAIN LANE.
  rewrite native_power_of_two_mask_is_modulo.
  destruct (allocated_power_size_is_small_or_large exponent) as [SMALL|[SMALL|LARGE]].
  - eapply small_original_lane_projects_to_the_native_modulus; eauto.
  - eapply small_original_lane_projects_to_the_native_modulus; eauto.
  - rewrite large_allocated_lane_is_the_circular_original in LANE by assumption.
    inversion LANE; subst index. split; [apply Nat.mod_upper_bound; lia|reflexivity].
Qed.

Theorem a_tag_matched_lane_is_an_original_full_native_candidate :
  forall exponent original physical start tag bit,
  start < 2 ^ (exponent + 2) -> bit < 16 -> tag < 128 ->
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  tag_match physical start tag bit = true ->
  exists index,
    allocated_lane (2 ^ (exponent + 2)) (start + bit) = Some index /\
    index < 2 ^ (exponent + 2) /\
    index = Nat.land (start + bit) (2 ^ (exponent + 2) - 1) /\
    original index = tag /\ tag_is_full (original index) = true.
Proof.
  intros exponent original physical start tag bit START BIT TAG PROJECT MATCH.
  unfold tag_match in MATCH. apply Nat.eqb_eq in MATCH.
  specialize (PROJECT (start + bit) ltac:(lia)).
  destruct (allocated_lane (2 ^ (exponent + 2)) (start + bit)) as [index|] eqn:LANE.
  - destruct (allocated_original_lane_has_the_bitmasked_index
      exponent (start + bit) index ltac:(lia) LANE) as [BOUND INDEX].
    exists index. repeat split; try assumption; try reflexivity.
    + congruence.
    + apply a_seven_bit_tag_is_native_full. lia.
  - lia.
Qed.

Definition insertion_slot bucket_count start physical :=
  match lowest_mask (special_match physical start) with
  | Some bit => Some (Nat.land (start + bit) (bucket_count - 1))
  | None => None
  end.
Definition fill_absent_cache bucket_count start physical (cached : option nat) :=
  match cached with
  | Some index => Some index
  | None => insertion_slot bucket_count start physical
  end.

Theorem an_empty_lane_enables_the_combined_insertion_cache :
  forall bucket_count start physical cached,
  any_mask (tag_match physical start 255) = true ->
  exists index, fill_absent_cache bucket_count start physical cached = Some index.
Proof.
  intros bucket_count start physical [index|] EMPTY.
  - exists index. reflexivity.
  - apply native_any_bit_set_iff_a_matching_lane in EMPTY.
    destruct EMPTY as [bit [INSIDE MATCH]]. unfold tag_match in MATCH.
    apply Nat.eqb_eq in MATCH.
    assert (SPECIAL : special_match physical start bit = true).
    { unfold special_match, tag_is_special. rewrite MATCH. reflexivity. }
    destruct (a_matching_lane_enables_native_lowest_bit
      (special_match physical start) bit INSIDE SPECIAL) as [first LOWEST].
    unfold fill_absent_cache, insertion_slot. rewrite LOWEST. eexists. reflexivity.
Qed.

Theorem candidate_index_addition_fits_the_accepted_native_layout :
  forall signed_limit word_limit alignment_exponent words bucket_exponent start bit,
  accepted_layout signed_limit alignment_exponent words bucket_exponent ->
  signed_limit <= word_limit -> start < allocated_buckets bucket_exponent ->
  bit < 16 -> start + bit <= word_limit.
Proof.
  intros signed_limit word_limit alignment_exponent words bucket_exponent start bit
    ACCEPTED WORD START BIT.
  pose proof (accepted_layout_covers_native_intermediate_arithmetic
    _ _ _ _ ACCEPTED) as [_ [_ [CONTROL _]]]. lia.
Qed.

End NativeHashBagProbeMasks.

Print Assumptions NativeHashBagProbeMasks.sse2_mask_has_exact_lane_bits_and_u16_range.
Print Assumptions NativeHashBagProbeMasks.native_lowest_bit_has_the_trailing_zeros_specification.
Print Assumptions NativeHashBagProbeMasks.native_any_bit_set_iff_a_matching_lane.
Print Assumptions NativeHashBagProbeMasks.the_optional_native_lowest_bit_is_uniquely_characterized.
Print Assumptions NativeHashBagProbeMasks.native_power_of_two_mask_is_modulo.
Print Assumptions NativeHashBagProbeMasks.a_tag_matched_lane_is_an_original_full_native_candidate.
Print Assumptions NativeHashBagProbeMasks.an_empty_lane_enables_the_combined_insertion_cache.
Print Assumptions NativeHashBagProbeMasks.candidate_index_addition_fits_the_accepted_native_layout.
