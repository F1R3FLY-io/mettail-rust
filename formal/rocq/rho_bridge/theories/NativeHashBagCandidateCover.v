(** Candidate occurrence coverage for the pinned native lookup bodies.
    hashbrown 0.17.1 raw.rs:1819 and :2026 exhaust matching tag bits before
    testing EMPTY. An early true Eq answer stops earlier; even a candidate
    after EMPTY padding is visited if its bit precedes the end of that mask.

    Observations below are lists of returns from the EXISTING SuccessfulPrefix
    relation, indexed by the EXISTING ReachedGroup position. They are not a
    new probe executor or an Eq interpreter. Callback outcomes are unrestricted
    in this conservative coverage: early returns only remove observations.
    The last emitted bit may already have entered a callback that has not yet
    returned. No bound, fuel or guessed collision count is assumed.

    Occurrence domination, rather than a second window-injectivity proof,
    transports mask prefixes into original window slots. Existing whole-cycle
    NoDup then forbids duplicate original bucket callbacks. Identity here is
    a bucket OCCURRENCE, not semantic key equality or cached hash equality.

    Typed callback costs, scratch, inspection and relocation stability remain
    separate provider obligations. In this repository std::HashMap::insert
    calls incoming.eq(stored); std::HashMap::entry dispatches to rustc_entry
    (:35), which calls stored.eq(incoming), NOT public hashbrown::entry.
    Clone's vacant rustc entry reserves first and then insert_no_grow performs
    one insertion-only placement search, with no Eq callback. None of these
    source directions is replaced by a symmetry or native HashBag::eq claim.
    Native intrinsic/pointer interpretation and FULL-count/retained-roster
    association remain explicit; no production scanner or comparator changes. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagProbeWindows NativeHashBagProbeMasks
  NativeHashBagMaskIteration NativeHashBagProbeCoverage NativeHashBagProbeControl.
Import ListNotations.
Open Scope nat_scope.

Module NativeHashBagCandidateCover.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.
Import NativeHashBagProbeMasks.NativeHashBagProbeMasks.
Import NativeHashBagMaskIteration.NativeHashBagMaskIteration.
Import NativeHashBagProbeCoverage.NativeHashBagProbeCoverage.
Import NativeHashBagProbeControl.NativeHashBagProbeControl.

Definition occurrences slots index := count_occ Nat.eq_dec slots index.
Definition native_candidate bucket_count position bit :=
  Nat.land (position + bit) (bucket_count - 1).
Definition group_candidates bucket_count position emitted :=
  map (native_candidate bucket_count position) emitted.
Definition original_full_slots bucket_count original :=
  filter (fun index => tag_is_full (original index)) (seq 0 bucket_count).

Lemma original_mask_lanes_are_the_original_predicate : forall predicate,
  word_lanes (movemask predicate) = ordered_lanes predicate.
Proof.
  intro predicate. unfold word_lanes, ordered_lanes.
  apply filter_ext_in. intros bit MEMBER. apply in_seq in MEMBER.
  apply mask_bit_inside. lia.
Qed.

Lemma a_successful_mask_prefix_keeps_the_original_selected_suffix :
  forall predicate emitted current,
  SuccessfulPrefix (movemask predicate) emitted current ->
  ordered_lanes predicate = emitted ++ word_lanes current.
Proof.
  intros predicate emitted current PREFIX.
  destruct (sse2_mask_has_exact_lane_bits_and_u16_range predicate) as [BOUND _].
  destruct (every_successful_prefix_preserves_the_exact_original_suffix
    _ _ _ PREFIX BOUND) as [_ SUFFIX].
  now rewrite original_mask_lanes_are_the_original_predicate in SUFFIX.
Qed.

Lemma successful_mask_return_is_an_original_matching_lane :
  forall predicate emitted current bit,
  SuccessfulPrefix (movemask predicate) emitted current -> In bit emitted ->
  bit < 16 /\ predicate bit = true.
Proof.
  intros predicate emitted current bit PREFIX MEMBER.
  pose proof (a_successful_mask_prefix_keeps_the_original_selected_suffix
    _ _ _ PREFIX) as SUFFIX.
  assert (SELECTED : In bit (ordered_lanes predicate)).
  { rewrite SUFFIX. apply in_or_app. now left. }
  unfold ordered_lanes in SELECTED. apply filter_In in SELECTED as [RANGE MATCH].
  apply in_seq in RANGE. split; assumption || lia.
Qed.

Lemma prefix_projection_cannot_add_selected_occurrences :
  forall predicate emitted current project index,
  SuccessfulPrefix (movemask predicate) emitted current ->
  occurrences (map project emitted) index <=
    occurrences (map project (ordered_lanes predicate)) index.
Proof.
  intros predicate emitted current project index PREFIX.
  rewrite (a_successful_mask_prefix_keeps_the_original_selected_suffix _ _ _ PREFIX), map_app.
  unfold occurrences. rewrite count_occ_app. lia.
Qed.

(** Generic list arithmetic: selecting a lane whose optional projection is
    present cannot create an original-slot occurrence. Padding is dropped
    only by the original-slot projection, not by an early EMPTY cutoff. *)
Lemma selected_projection_is_occurrence_bounded :
  forall tokens (predicate : nat -> bool) (project : nat -> option nat) image,
  (forall token, In token tokens -> predicate token = true ->
    project token = Some (image token)) ->
  forall index,
  occurrences (map image (filter predicate tokens)) index <=
    occurrences (flat_map (fun token =>
      match project token with Some slot => [slot] | None => [] end) tokens) index.
Proof.
  induction tokens as [|token tokens IH]; intros predicate project image PROJECT index.
  - reflexivity.
  - specialize (IH predicate project image
      (fun item MEMBER MATCH => PROJECT item (or_intror MEMBER) MATCH) index).
    cbn [filter map flat_map]. destruct (predicate token) eqn:SELECTED.
    + rewrite (PROJECT token ltac:(now left) SELECTED).
      cbn [filter map flat_map].
      unfold occurrences in *.
      rewrite count_occ_app.
      destruct (Nat.eq_dec (image token) index) as [EQUAL|DISTINCT].
      * rewrite (count_occ_cons_eq Nat.eq_dec _ EQUAL).
        rewrite (count_occ_cons_eq Nat.eq_dec _ EQUAL).
        apply le_n_S. exact IH.
      * rewrite (count_occ_cons_neq Nat.eq_dec _ DISTINCT).
        rewrite (count_occ_cons_neq Nat.eq_dec _ DISTINCT).
        exact IH.
    + destruct (project token) as [slot|].
      * unfold occurrences in *.
        rewrite count_occ_app.
        destruct (Nat.eq_dec slot index) as [EQUAL|DISTINCT].
        -- rewrite (count_occ_cons_eq Nat.eq_dec _ EQUAL).
           lia.
        -- rewrite (count_occ_cons_neq Nat.eq_dec _ DISTINCT).
           lia.
      * exact IH.
Qed.

Lemma window_originals_are_projected_lane_offsets : forall bucket_count position,
  original_slots (allocated_window bucket_count position) =
  flat_map (fun bit => match allocated_lane bucket_count (position + bit) with
    Some slot => [slot] | None => [] end) (seq 0 16).
Proof.
  intros bucket_count position. unfold allocated_window.
  rewrite a_sequence_starts_by_translation. unfold original_slots.
  rewrite !flat_map_concat_map, !map_map. reflexivity.
Qed.

Theorem each_emitted_candidate_is_its_original_full_slot :
  forall exponent position original physical tag emitted current index,
  position < 2 ^ (exponent + 2) -> tag < 128 ->
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  SuccessfulPrefix (movemask (tag_match physical position tag)) emitted current ->
  In index (group_candidates (2 ^ (exponent + 2)) position emitted) ->
  index < 2 ^ (exponent + 2) /\ original index = tag /\
    tag_is_full (original index) = true.
Proof.
  intros exponent position original physical tag emitted current index
    POSITION TAG PROJECT PREFIX MEMBER.
  apply in_map_iff in MEMBER as [bit [INDEX MEMBER]].
  destruct (successful_mask_return_is_an_original_matching_lane
    _ _ _ _ PREFIX MEMBER) as [BIT MATCH].
  destruct (a_tag_matched_lane_is_an_original_full_native_candidate
    exponent original physical position tag bit POSITION BIT TAG PROJECT MATCH)
    as [slot [LANE [SLOT [MASK [VALUE FULL]]]]].
  unfold native_candidate in INDEX. assert (SAME : index = slot) by congruence.
  rewrite SAME. split; [exact SLOT|]. split; [exact VALUE|exact FULL].
Qed.

Theorem each_group_prefix_is_dominated_by_its_original_window :
  forall exponent position original physical tag emitted current,
  position < 2 ^ (exponent + 2) -> tag < 128 ->
  physical_tags_project (2 ^ (exponent + 2)) original physical ->
  SuccessfulPrefix (movemask (tag_match physical position tag)) emitted current ->
  forall index,
  occurrences (group_candidates (2 ^ (exponent + 2)) position emitted) index <=
    occurrences (original_slots (allocated_window (2 ^ (exponent + 2)) position)) index.
Proof.
  intros exponent position original physical tag emitted current POSITION TAG PROJECT PREFIX index.
  eapply Nat.le_trans.
  - exact (prefix_projection_cannot_add_selected_occurrences _ _ _ _ index PREFIX).
  - rewrite window_originals_are_projected_lane_offsets.
    unfold ordered_lanes. apply selected_projection_is_occurrence_bounded.
    intros bit MEMBER MATCH. apply in_seq in MEMBER.
    destruct (a_tag_matched_lane_is_an_original_full_native_candidate
      exponent original physical position tag bit POSITION ltac:(lia) TAG PROJECT MATCH)
      as [slot [LANE [_ [MASK _]]]].
    unfold native_candidate. now rewrite <- MASK.
Qed.

Lemma occurrence_domination_preserves_NoDup : forall selected originals,
  NoDup originals -> (forall index, occurrences selected index <= occurrences originals index) ->
  NoDup selected.
Proof.
  intros selected originals DISTINCT COVER. apply (proj2 (NoDup_count_occ Nat.eq_dec selected)).
  intro index. specialize (COVER index).
  pose proof ((proj1 (NoDup_count_occ Nat.eq_dec originals)) DISTINCT index) as ORIGINAL.
  eapply Nat.le_trans; [exact COVER|exact ORIGINAL].
Qed.

Lemma flattened_occurrence_bounds_compose : forall (indices : list nat)
  (selected originals : nat -> list nat),
  (forall group, In group indices -> forall index,
    occurrences (selected group) index <= occurrences (originals group) index) ->
  forall index, occurrences (flat_map selected indices) index <=
    occurrences (flat_map originals indices) index.
Proof.
  induction indices as [|group rest IH]; intros selected originals COVER index.
  - reflexivity.
  - specialize (IH selected originals
      (fun item MEMBER slot => COVER item (or_intror MEMBER) slot) index).
    pose proof (COVER group ltac:(now left) index) as HEAD.
    cbn [flat_map]. unfold occurrences in *. rewrite !count_occ_app. lia.
Qed.

Lemma a_group_range_prefix_cannot_add_occurrences : forall groups reached originals index,
  reached <= groups ->
  occurrences (flat_map originals (seq 0 reached)) index <=
    occurrences (flat_map originals (seq 0 groups)) index.
Proof.
  intros groups reached originals index BOUND.
  replace groups with (reached + (groups - reached)) by lia.
  rewrite seq_app, flat_map_app. unfold occurrences. rewrite count_occ_app. lia.
Qed.

Definition observed_candidates exponent initial last (emitted : nat -> list nat) :=
  flat_map (fun group => group_candidates (power_bucket_count exponent)
    (mathematical_start exponent initial group) (emitted group)) (seq 0 (S last)).

Definition group_prefixes physical tag exponent initial last emitted : Prop :=
  forall group, group <= last -> exists current,
    SuccessfulPrefix (movemask (tag_match physical
      (mathematical_start exponent initial group) tag)) (emitted group) current.

Lemma power_buckets_are_allocated_buckets : forall exponent,
  power_bucket_count exponent = 2 ^ ((exponent + 2) + 2).
Proof.
  intro exponent. rewrite power_buckets_have_the_native_mask_shape.
  f_equal. lia.
Qed.

(** The only group-limit input below is an EXISTING reached state. Its
    coverage barrier derives the range bound; observations carry no cap. *)
Theorem a_reached_candidate_prefix_is_dominated_by_the_complete_original_cycle :
  forall mode exponent initial original original_empty physical empty_index tag
    last position stride cached emitted,
  initial < power_bucket_count exponent -> empty_index < power_bucket_count exponent ->
  original_empty empty_index = true ->
  physical_predicate_projects (power_bucket_count exponent) original_empty true
    (fun offset => Nat.eqb (physical offset) 255) ->
  physical_tags_project (power_bucket_count exponent) original physical -> tag < 128 ->
  ReachedGroup mode (power_bucket_count exponent) initial physical last position stride cached ->
  group_prefixes physical tag exponent initial last emitted ->
  forall index, occurrences (observed_candidates exponent initial last emitted) index <=
    occurrences (complete_originals exponent initial) index.
Proof.
  intros mode exponent initial original original_empty physical empty_index tag
    last position stride cached emitted INITIAL EMPTY_INDEX EMPTY EMPTY_PROJECT PROJECT TAG REACHED PREFIXES index.
  destruct (an_original_empty_witness_bounds_group_visits_and_moves
    _ _ _ _ _ _ _ _ _ _ INITIAL EMPTY_INDEX EMPTY EMPTY_PROJECT REACHED) as [BOUND _].
  unfold observed_candidates, complete_originals, complete_windows.
  rewrite original_slots_of_concatenated_windows, !flat_map_concat_map, !map_map.
  rewrite <- !flat_map_concat_map.
  apply Nat.le_trans with
    (m := occurrences (flat_map (fun group => original_slots
      (allocated_window (power_bucket_count exponent)
        (mathematical_start exponent initial group)))
      (seq 0 (S last))) index).
  - apply flattened_occurrence_bounds_compose. intros group GROUP slot.
    apply in_seq in GROUP. destruct (PREFIXES group ltac:(lia)) as [current PREFIX].
    rewrite power_buckets_are_allocated_buckets in PROJECT |- *.
    eapply (each_group_prefix_is_dominated_by_its_original_window
      (exponent + 2)); [|exact TAG|exact PROJECT|exact PREFIX].
    pose proof (every_mathematical_start_is_within_its_table exponent initial group) as START.
    rewrite power_buckets_are_allocated_buckets in START.
    exact START.
  - apply a_group_range_prefix_cannot_add_occurrences. exact BOUND.
Qed.

Theorem a_reached_candidate_prefix_has_no_duplicate_original_callbacks :
  forall mode exponent initial original original_empty physical empty_index tag
    last position stride cached emitted,
  initial < power_bucket_count exponent -> empty_index < power_bucket_count exponent ->
  original_empty empty_index = true ->
  physical_predicate_projects (power_bucket_count exponent) original_empty true
    (fun offset => Nat.eqb (physical offset) 255) ->
  physical_tags_project (power_bucket_count exponent) original physical -> tag < 128 ->
  ReachedGroup mode (power_bucket_count exponent) initial physical last position stride cached ->
  group_prefixes physical tag exponent initial last emitted ->
  NoDup (observed_candidates exponent initial last emitted) /\
  length (observed_candidates exponent initial last emitted) <=
    length (original_full_slots (power_bucket_count exponent) original).
Proof.
  intros mode exponent initial original original_empty physical empty_index tag
    last position stride cached emitted INITIAL EMPTY_INDEX EMPTY EMPTY_PROJECT PROJECT TAG REACHED PREFIXES.
  assert (DISTINCT : NoDup (observed_candidates exponent initial last emitted)).
  { eapply occurrence_domination_preserves_NoDup.
    - apply a_complete_mathematical_cycle_never_repeats_an_original_bucket. exact INITIAL.
    - eapply a_reached_candidate_prefix_is_dominated_by_the_complete_original_cycle;
        eassumption. }
  split; [exact DISTINCT|]. apply NoDup_incl_length; [exact DISTINCT|].
  intros index MEMBER. apply in_flat_map in MEMBER as [group [GROUP MEMBER]].
  apply in_seq in GROUP. destruct (PREFIXES group ltac:(lia)) as [current PREFIX].
  assert (POSITION : mathematical_start exponent initial group < power_bucket_count exponent)
    by apply every_mathematical_start_is_within_its_table.
  rewrite power_buckets_are_allocated_buckets in POSITION, PROJECT, MEMBER |- *.
  destruct (each_emitted_candidate_is_its_original_full_slot
    _ _ _ _ _ _ _ _ POSITION TAG PROJECT PREFIX MEMBER) as [INDEX [_ FULL]].
  apply filter_In. split; [apply in_seq; lia|exact FULL].
Qed.

Theorem a_small_reached_group_has_no_duplicate_original_callbacks :
  forall mode exponent initial original physical tag step position stride cached emitted current,
  (2 ^ (exponent + 2) = 4 \/ 2 ^ (exponent + 2) = 8) ->
  initial < 2 ^ (exponent + 2) ->
  physical_tags_project (2 ^ (exponent + 2)) original physical -> tag < 128 ->
  ReachedGroup mode (2 ^ (exponent + 2)) initial physical step position stride cached ->
  SuccessfulPrefix (movemask (tag_match physical initial tag)) emitted current ->
  step = 0 /\ NoDup (group_candidates (2 ^ (exponent + 2)) initial emitted) /\
    length (group_candidates (2 ^ (exponent + 2)) initial emitted) <=
      length (original_full_slots (2 ^ (exponent + 2)) original).
Proof.
  intros mode exponent initial original physical tag step position stride cached emitted current
    SMALL INITIAL PROJECT TAG REACHED PREFIX.
  split.
  - eapply allocated_small_table_group_search_never_advances; eassumption.
  - assert (DISTINCT : NoDup (group_candidates (2 ^ (exponent + 2)) initial emitted)).
    { eapply occurrence_domination_preserves_NoDup.
      - apply (small_window_originals_have_no_duplicates
          (2 ^ (exponent + 2)) initial).
        exact SMALL.
        exact INITIAL.
      - eapply each_group_prefix_is_dominated_by_its_original_window; eassumption. }
    split; [exact DISTINCT|]. apply NoDup_incl_length; [exact DISTINCT|].
    intros index MEMBER. destruct (each_emitted_candidate_is_its_original_full_slot
      _ _ _ _ _ _ _ _ INITIAL TAG PROJECT PREFIX MEMBER) as [INDEX [_ FULL]].
    apply filter_In. split; [apply in_seq; lia|exact FULL].
Qed.

Theorem a_static_empty_singleton_emits_no_candidates :
  forall physical tag emitted current,
  (forall bit, bit < 16 -> physical bit = 255) -> tag < 128 ->
  SuccessfulPrefix (movemask (tag_match physical 0 tag)) emitted current -> emitted = [].
Proof.
  intros physical tag emitted current STATIC TAG PREFIX.
  destruct emitted as [|bit rest]; [reflexivity|].
  destruct (successful_mask_return_is_an_original_matching_lane
    _ _ _ _ PREFIX ltac:(now left)) as [BIT MATCH].
  unfold tag_match in MATCH. rewrite Nat.add_0_l, STATIC in MATCH by exact BIT.
  apply Nat.eqb_eq in MATCH. lia.
Qed.

End NativeHashBagCandidateCover.

Print Assumptions NativeHashBagCandidateCover.each_emitted_candidate_is_its_original_full_slot.
Print Assumptions NativeHashBagCandidateCover.each_group_prefix_is_dominated_by_its_original_window.
Print Assumptions NativeHashBagCandidateCover.a_reached_candidate_prefix_is_dominated_by_the_complete_original_cycle.
Print Assumptions NativeHashBagCandidateCover.a_reached_candidate_prefix_has_no_duplicate_original_callbacks.
Print Assumptions NativeHashBagCandidateCover.a_small_reached_group_has_no_duplicate_original_callbacks.
Print Assumptions NativeHashBagCandidateCover.a_static_empty_singleton_emits_no_candidates.
