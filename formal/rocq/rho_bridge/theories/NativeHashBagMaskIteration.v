(** Successful-return prefixes of pinned hashbrown 0.17.1 BitMaskIter.
    control/bitmask.rs:28 clears m & (m-1); :89 initializes with the
    iteration mask; :103 calls lowest_set_bit, returns None immediately on
    zero, otherwise updates the word and returns Some(bit). SSE2 uses u16,
    stride 1 and an all-ones iteration mask (control/group/sse2.rs:10-13).

    [NativeNext] projects exactly those native word fields and return cuts.
    It is a relation, not a replacement iterator or an executable probe.
    The subtraction is present only in its successful Some constructor.
    No constructor assumes a word bound, a list-tail law or termination.
    The numeric clear-bit identity is proved first from binary arithmetic;
    the original ordered-lane tail and finite prefix bound follow from it.

    ProbeMasks supplies the exact fixed-width least-bit characterization.
    Its intrinsic contracts and the source association to the actual loaded
    control group remain explicit at the Rust interpretation boundary.
    Prefixes here count successful Some returns, not Eq callbacks or their
    work. The final theorem describes a consumer stopping at its FIRST None;
    arbitrary repeated calls after None are not bounded. Lookup-group
    reachability, EMPTY barriers, insertion repair and callbacks remain
    separate. No Rust source, native table or allocation policy is changed. *)
From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From RhoBridge Require Import NativeHashBagProbeMasks.
Import ListNotations.

Module NativeHashBagMaskIteration.
Import NativeHashBagProbeMasks.NativeHashBagProbeMasks.

Definition clear_lowest word := Nat.land word (word - 1).
Definition word_lanes word := ordered_lanes (Nat.testbit word).

(** Induction on the least set bit uses the exact even/odd forms of AND.
    In the even branch, the lower half is nonzero before predecessor
    arithmetic is rewritten. No wrapping subtraction is assumed. *)
Theorem numeric_clear_lowest_changes_exactly_the_least_set_bit :
  forall least word,
  Nat.testbit word least = true ->
  (forall earlier, earlier < least -> Nat.testbit word earlier = false) ->
  forall bit, Nat.testbit (clear_lowest word) bit =
    if bit =? least then false else Nat.testbit word bit.
Proof.
  induction least as [|least IH]; intros word SET EARLIER.
  - destruct (Nat.exists_div2 word) as [half [parity SHAPE]].
    destruct parity.
    + change (word = 2 * half + 1) in SHAPE. subst word.
      assert (CLEAR : clear_lowest (2 * half + 1) = 2 * half).
      { unfold clear_lowest. replace (2 * half + 1 - 1) with (2 * half) by lia.
        rewrite Nat.land_odd_even, Nat.land_diag. reflexivity. }
      intros [|bit]; rewrite CLEAR.
      * apply Nat.testbit_even_0.
      * rewrite Nat.testbit_even_succ', Nat.testbit_odd_succ'. reflexivity.
    + change (word = 2 * half + 0) in SHAPE.
      rewrite Nat.add_0_r in SHAPE. subst word.
      rewrite Nat.testbit_even_0 in SET. discriminate SET.
  - destruct (Nat.exists_div2 word) as [half [parity SHAPE]].
    destruct parity.
    + change (word = 2 * half + 1) in SHAPE.
      subst word. specialize (EARLIER 0 ltac:(lia)).
      rewrite Nat.testbit_odd_0 in EARLIER. discriminate EARLIER.
    + change (word = 2 * half + 0) in SHAPE.
      rewrite Nat.add_0_r in SHAPE. subst word.
      rewrite Nat.testbit_even_succ' in SET.
      assert (POSITIVE : 0 < half).
      { destruct half; [rewrite Nat.bits_0 in SET; discriminate SET|lia]. }
      assert (LOWER : forall earlier, earlier < least -> Nat.testbit half earlier = false).
      { intros earlier BEFORE. specialize (EARLIER (S earlier) ltac:(lia)).
        now rewrite Nat.testbit_even_succ' in EARLIER. }
      assert (CLEAR : clear_lowest (2 * half) = 2 * clear_lowest half).
      { unfold clear_lowest. replace (2 * half - 1) with (2 * (half - 1) + 1) by lia.
        apply Nat.land_even_odd. }
      intros [|bit]; rewrite CLEAR.
      * rewrite !Nat.testbit_even_0. reflexivity.
      * rewrite !Nat.testbit_even_succ', (IH half SET LOWER bit). reflexivity.
Qed.

Lemma a_u16_word_is_reconstructed_by_its_mask_bits : forall word,
  word < 2 ^ 16 -> movemask (Nat.testbit word) = word.
Proof.
  intros word BOUND. apply Nat.bits_inj. intro bit.
  destruct (sse2_mask_has_exact_lane_bits_and_u16_range (Nat.testbit word))
    as [_ BITS]. rewrite BITS. destruct (bit <? 16) eqn:INSIDE; [reflexivity|].
  apply Nat.ltb_ge in INSIDE. symmetry.
  replace word with (word mod 2 ^ 16) at 1 by (apply Nat.mod_small; exact BOUND).
  apply Nat.mod_pow2_bits_high. exact INSIDE.
Qed.

Theorem native_iterator_initialization_preserves_every_u16_word : forall word,
  word < 2 ^ 16 -> Nat.land word (2 ^ 16 - 1) = word.
Proof.
  intros word BOUND. rewrite native_power_of_two_mask_is_modulo.
  apply Nat.mod_small. exact BOUND.
Qed.

Lemma a_bounded_word_is_zero_iff_its_ordered_lanes_are_empty : forall word,
  word < 2 ^ 16 -> (word = 0 <-> word_lanes word = []).
Proof.
  intros word BOUND. split.
  - intros ZERO. rewrite ZERO. unfold word_lanes, ordered_lanes.
    transitivity (filter (fun _ : nat => false) (seq 0 16)).
    + apply filter_ext. apply Nat.bits_0.
    + apply filter_false.
  - intros EMPTY. apply Nat.bits_inj_0. intro bit.
    destruct (bit <? 16) eqn:POSITION.
    + apply Nat.ltb_lt in POSITION.
      destruct (Nat.testbit word bit) eqn:SET; [|reflexivity].
      assert (MEMBER : In bit (word_lanes word)).
      { unfold word_lanes, ordered_lanes. apply filter_In.
        split; [apply in_seq; lia|exact SET]. }
      rewrite EMPTY in MEMBER. contradiction.
    + apply Nat.ltb_ge in POSITION.
      replace word with (word mod 2 ^ 16) at 1 by (apply Nat.mod_small; exact BOUND).
      apply Nat.mod_pow2_bits_high. lia.
Qed.

(** Avoid specializing the packed-mask theorem at symbolic testbit(word):
    broad rewrite and explicit eq_ind both trigger costly expansion of the
    duplicated branches in pack_mask 16 during conversion. This direct
    filtered-word proof reuses the same least-element characterization. *)
Lemma bounded_word_has_the_exact_lowest_specification : forall word result,
  word < 2 ^ 16 ->
  (lowest_word word = result <-> optional_trailing_zeros_spec word result).
Proof.
  intros word [bit|] BOUND; cbn [optional_trailing_zeros_spec].
  - split.
    + intros FIRST. unfold lowest_word in FIRST.
      destruct (first_filtered_sequence_member_is_least
        16 0 (Nat.testbit word) bit FIRST) as [RANGE [SET EARLIER]].
      split; [lia|]. split; [exact SET|]. intros earlier BEFORE. apply EARLIER. lia.
    + intros [INSIDE [SET EARLIER]]. unfold lowest_word.
      assert (MEMBER : In bit (filter (Nat.testbit word) (seq 0 16))).
      { apply filter_In. split; [apply in_seq; lia|exact SET]. }
      destruct (filter (Nat.testbit word) (seq 0 16)) as [|first rest] eqn:LANES;
        [contradiction|].
      assert (FIRST : hd_error (filter (Nat.testbit word) (seq 0 16)) = Some first)
        by (rewrite LANES; reflexivity).
      destruct (first_filtered_sequence_member_is_least
        16 0 (Nat.testbit word) first FIRST) as [RANGE [FIRST_SET FIRST_EARLIER]].
      assert (SAME : first = bit).
      { destruct (Nat.lt_trichotomy first bit) as [LESS|[SAME|GREATER]]; [|assumption|].
        - rewrite (EARLIER first LESS) in FIRST_SET. discriminate FIRST_SET.
        - rewrite (FIRST_EARLIER bit ltac:(lia)) in SET. discriminate SET. }
      now subst first.
  - change (hd_error (word_lanes word) = None <-> word = 0).
    rewrite a_bounded_word_is_zero_iff_its_ordered_lanes_are_empty by exact BOUND.
    destruct (word_lanes word); cbn [hd_error]; split; congruence.
Qed.

Lemma word_lanes_are_original_ordered_distinct_bits : forall word,
  NoDup (word_lanes word) /\ length (word_lanes word) <= 16.
Proof.
  intro word. unfold word_lanes, ordered_lanes. split.
  - apply NoDup_filter, seq_NoDup.
  - pose proof (filter_length_le (Nat.testbit word) (seq 0 16)) as BOUND.
    rewrite length_seq in BOUND. exact BOUND.
Qed.

Lemma filtering_out_a_bit_commutes_with_the_mask_filter : forall slots predicate removed,
  filter (fun bit => if bit =? removed then false else predicate bit) slots =
  filter (fun bit => negb (bit =? removed)) (filter predicate slots).
Proof.
  induction slots as [|bit rest IH]; intros predicate removed; [reflexivity|].
  cbn [filter]. destruct (bit =? removed) eqn:REMOVE;
    destruct (predicate bit); cbn [filter]; rewrite ?REMOVE;
    cbn [negb]; now rewrite IH.
Qed.

Lemma filtering_out_an_absent_bit_preserves_the_list : forall slots removed,
  ~ In removed slots -> filter (fun bit => negb (bit =? removed)) slots = slots.
Proof.
  induction slots as [|bit rest IH]; intros removed ABSENT; [reflexivity|].
  assert (DIFFERENT : (bit =? removed) = false).
  { apply Nat.eqb_neq. intro SAME. subst bit. apply ABSENT. now left. }
  cbn [filter]. rewrite DIFFERENT. cbn [negb]. f_equal.
  apply IH. intro MEMBER. apply ABSENT. now right.
Qed.

Theorem actual_numeric_clear_lowest_removes_the_first_ordered_lane : forall word bit,
  word < 2 ^ 16 -> lowest_word word = Some bit ->
  word_lanes word = bit :: word_lanes (clear_lowest word).
Proof.
  intros word bit BOUND LOWEST.
  pose proof (proj1 (bounded_word_has_the_exact_lowest_specification
    word (Some bit) BOUND) LOWEST) as [INSIDE [SET EARLIER]].
  assert (CLEAR : word_lanes (clear_lowest word) =
    filter (fun index => negb (index =? bit)) (word_lanes word)).
  { unfold word_lanes, ordered_lanes.
    rewrite <- filtering_out_a_bit_commutes_with_the_mask_filter.
    apply filter_ext. intro index.
    apply numeric_clear_lowest_changes_exactly_the_least_set_bit; assumption. }
  change (hd_error (word_lanes word) = Some bit) in LOWEST.
  destruct (word_lanes_are_original_ordered_distinct_bits word) as [DISTINCT _].
  destruct (word_lanes word) as [|first rest] eqn:LANES; [discriminate LOWEST|].
  inversion LOWEST; subst first. inversion DISTINCT as [|head tail ABSENT NODUP]; subst.
  rewrite CLEAR. cbn [filter]. rewrite Nat.eqb_refl. cbn [negb].
  now rewrite filtering_out_an_absent_bit_preserves_the_list by exact ABSENT.
Qed.

(** These constructors retain precisely the source return branches. *)
Inductive NativeNext : nat -> option nat -> nat -> Prop :=
| NextNone : forall word,
    lowest_word word = None -> NativeNext word None word
| NextSome : forall word bit,
    lowest_word word = Some bit -> NativeNext word (Some bit) (clear_lowest word).

Theorem a_successful_native_next_has_safe_subtraction_and_the_exact_tail :
  forall word bit next,
  word < 2 ^ 16 -> NativeNext word (Some bit) next ->
  0 < word /\ word - 1 < 2 ^ 16 /\ next < 2 ^ 16 /\
  word_lanes word = bit :: word_lanes next.
Proof.
  intros word bit next BOUND STEP. inversion STEP; subst.
  match goal with LOWEST : lowest_word word = Some bit |- _ =>
    pose proof (proj1 (bounded_word_has_the_exact_lowest_specification
      word (Some bit) BOUND) LOWEST) as [INSIDE [SET EARLIER]]
  end.
  assert (POSITIVE : 0 < word).
  { destruct word; [rewrite Nat.bits_0 in SET; discriminate SET|lia]. }
  pose proof (Nat.land_le_l word (word - 1)) as DECREASE.
  repeat split; try lia.
  - unfold clear_lowest. lia.
  - apply actual_numeric_clear_lowest_removes_the_first_ordered_lane; assumption.
Qed.

Theorem native_next_none_preserves_the_word_and_means_zero : forall word next,
  word < 2 ^ 16 -> NativeNext word None next -> next = word /\ word = 0.
Proof.
  intros word next BOUND STEP. inversion STEP; subst. split; [reflexivity|].
  apply (proj1 (bounded_word_has_the_exact_lowest_specification _ None BOUND)).
  assumption.
Qed.

(** Prefix constructors contain no bound and only successful return cuts. *)
Inductive SuccessfulPrefix : nat -> list nat -> nat -> Prop :=
| PrefixEmpty : forall initial, SuccessfulPrefix initial [] initial
| PrefixSome : forall initial emitted current bit next,
    SuccessfulPrefix initial emitted current -> NativeNext current (Some bit) next ->
    SuccessfulPrefix initial (emitted ++ [bit]) next.

Theorem every_successful_prefix_preserves_the_exact_original_suffix :
  forall initial emitted current,
  SuccessfulPrefix initial emitted current -> initial < 2 ^ 16 ->
  current < 2 ^ 16 /\ word_lanes initial = emitted ++ word_lanes current.
Proof.
  intros initial emitted current PREFIX. induction PREFIX as
    [initial|initial emitted current bit next PREFIX IH NEXT]; intro INITIAL.
  - split; [assumption|reflexivity].
  - destruct (IH INITIAL) as [CURRENT ORIGINAL].
    destruct (a_successful_native_next_has_safe_subtraction_and_the_exact_tail
      current bit next CURRENT NEXT) as [_ [_ [BOUND TAIL]]].
    split; [exact BOUND|]. rewrite ORIGINAL, TAIL, <- app_assoc. reflexivity.
Qed.

Theorem every_successful_prefix_has_no_repeated_lane_and_at_most_sixteen_returns :
  forall initial emitted current,
  initial < 2 ^ 16 -> SuccessfulPrefix initial emitted current ->
  NoDup emitted /\ length emitted <= 16 /\
  (forall bit, In bit emitted -> bit < 16 /\ Nat.testbit initial bit = true).
Proof.
  intros initial emitted current INITIAL PREFIX.
  destruct (every_successful_prefix_preserves_the_exact_original_suffix
    initial emitted current PREFIX INITIAL) as [_ ORIGINAL].
  destruct (word_lanes_are_original_ordered_distinct_bits initial) as [DISTINCT BOUND].
  rewrite ORIGINAL in DISTINCT, BOUND. rewrite app_length in BOUND.
  split.
  - eapply NoDup_app_remove_r. exact DISTINCT.
  - split; [lia|]. intros bit MEMBER.
    assert (SOURCE : In bit (word_lanes initial)).
    { rewrite ORIGINAL. apply in_or_app. now left. }
    unfold word_lanes, ordered_lanes in SOURCE. apply filter_In in SOURCE.
    destruct SOURCE as [RANGE SET]. apply in_seq in RANGE. split; [lia|exact SET].
Qed.

(** Exactly one terminal call after the successful prefix; it cannot mutate.
    Repeated terminal calls are intentionally not represented as successes. *)
Inductive FirstNoneConsumer : nat -> list nat -> nat -> Prop :=
| StopAtFirstNone : forall initial emitted current final,
    SuccessfulPrefix initial emitted current -> NativeNext current None final ->
    FirstNoneConsumer initial emitted final.

Theorem a_consumer_stopping_at_first_none_returns_every_original_lane_once :
  forall initial emitted final,
  initial < 2 ^ 16 -> FirstNoneConsumer initial emitted final ->
  final = 0 /\ emitted = word_lanes initial /\ NoDup emitted /\ length emitted <= 16.
Proof.
  intros initial emitted final INITIAL CONSUMER.
  inversion CONSUMER as [initial' emitted' current final' PREFIX NONE]; subst.
  destruct (every_successful_prefix_preserves_the_exact_original_suffix
    initial emitted current PREFIX INITIAL) as [CURRENT ORIGINAL].
  destruct (native_next_none_preserves_the_word_and_means_zero current final CURRENT NONE)
    as [UNCHANGED ZERO].
  assert (EMPTY : word_lanes current = []).
  { rewrite ZERO. unfold word_lanes, ordered_lanes.
    transitivity (filter (fun _ : nat => false) (seq 0 16)).
    - apply filter_ext. apply Nat.bits_0.
    - apply filter_false. }
  rewrite EMPTY, app_nil_r in ORIGINAL.
  destruct (every_successful_prefix_has_no_repeated_lane_and_at_most_sixteen_returns
    initial emitted current INITIAL PREFIX) as [DISTINCT [BOUND _]].
  repeat split; congruence || assumption.
Qed.

End NativeHashBagMaskIteration.

Print Assumptions NativeHashBagMaskIteration.numeric_clear_lowest_changes_exactly_the_least_set_bit.
Print Assumptions NativeHashBagMaskIteration.native_iterator_initialization_preserves_every_u16_word.
Print Assumptions NativeHashBagMaskIteration.actual_numeric_clear_lowest_removes_the_first_ordered_lane.
Print Assumptions NativeHashBagMaskIteration.a_successful_native_next_has_safe_subtraction_and_the_exact_tail.
Print Assumptions NativeHashBagMaskIteration.native_next_none_preserves_the_word_and_means_zero.
Print Assumptions NativeHashBagMaskIteration.every_successful_prefix_preserves_the_exact_original_suffix.
Print Assumptions NativeHashBagMaskIteration.every_successful_prefix_has_no_repeated_lane_and_at_most_sixteen_returns.
Print Assumptions NativeHashBagMaskIteration.a_consumer_stopping_at_first_none_returns_every_original_lane_once.
