(** Result algebra for the existing repeated-item lexicographic comparison.
    [expand] is a proof-only denotation: the runtime retains borrowed items
    and remaining-count cursors; it never allocates an expanded roster.
    Bag entries have no secondary operand, so an accepted primary response
    is the item result. Establishing that request/source association remains
    separate from these result laws.

    UnitLexCursor has a historical name, but its four fields and existing
    advance_equal_counts are precisely the general min/subtract/zero-test
    operation in collection_cmp_pda.rs:657. Successful current_left/right
    restore an original positive count when its remaining counter is zero.
    Equal responses need not identify original terms: only their comparison
    result is used when cancelling equally long repeated prefixes.

    The terminal rule retains an explicit common-consumption invariant.
    Whole-execution integration must derive it from initialization and the
    transition laws below; it is not a comparison-result oracle. Stored-total
    lead is independent of repetition sums. Both checked rosters must still
    be constructed before the runtime evaluates that lead, so no result law
    bypasses zero-count, overflow or resource refusal. Sorting, source
    callbacks, owner scheduling and full category factorization are separate. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RhoBridge Require Import CollectionPairAndUnitLexResults
  GeneratedBagComparisonInitialization MergeSortPdaRun.
From RuntimeGrammar Require Import SemanticComparisonLaws.
Import ListNotations.

Module CollectionWeightedLexResults.
Import CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.

Section WeightedSuffixes.
Context {A : Type}.
Variable compare : A -> A -> comparison.

Definition expand (roster : list (A * nat)) :=
  flat_map (fun entry => repeat (fst entry) (snd entry)) roster.
Definition effective_count count remaining := if remaining =? 0 then count else remaining.
Definition remaining_suffix (roster : list (A * nat)) index remaining :=
  match skipn index roster with
  | [] => []
  | (value, count) :: rest => repeat value (effective_count count remaining) ++ expand rest
  end.
Definition left_suffix roster cursor :=
  remaining_suffix roster (lex_left_index cursor) (lex_left_remaining cursor).
Definition right_suffix roster cursor :=
  remaining_suffix roster (lex_right_index cursor) (lex_right_remaining cursor).
Definition current_repeated_counts left_count right_count cursor :=
  {| lex_left_index := lex_left_index cursor;
     lex_right_index := lex_right_index cursor;
     lex_left_remaining := effective_count left_count (lex_left_remaining cursor);
     lex_right_remaining := effective_count right_count (lex_right_remaining cursor) |}.

Theorem expanded_length_is_the_original_repetition_sum : forall roster,
  length (expand roster) =
    GeneratedBagComparisonInitialization.GeneratedBagComparisonInitialization.source_count roster.
Proof.
  induction roster as [|[value count] rest IH].
  - reflexivity.
  - change (length (repeat value count ++ expand rest) = count +
      GeneratedBagComparisonInitialization.GeneratedBagComparisonInitialization.source_count rest).
    rewrite length_app, repeat_length, IH. reflexivity.
Qed.

Lemma zero_remaining_denotes_the_complete_original_suffix : forall roster index,
  remaining_suffix roster index 0 = expand (skipn index roster).
Proof.
  intros roster index. unfold remaining_suffix.
  destruct (skipn index roster) as [|[value count] rest]; reflexivity.
Qed.

Lemma present_item_exposes_its_original_run : forall roster index value count remaining,
  nth_error roster index = Some (value, count) ->
  remaining_suffix roster index remaining =
    repeat value (effective_count count remaining) ++ expand (skipn (S index) roster).
Proof.
  intros roster index value count remaining PRESENT. unfold remaining_suffix.
  now rewrite (MergeSortPdaRun.MergeSortPdaRun.skipn_at_present_index
    index roster (value, count) PRESENT).
Qed.

Lemma restoring_the_original_count_preserves_the_suffix :
  forall roster index value count remaining,
  nth_error roster index = Some (value, count) ->
  remaining_suffix roster index remaining =
    remaining_suffix roster index (effective_count count remaining).
Proof.
  intros roster index value count remaining PRESENT.
  rewrite !present_item_exposes_its_original_run with (value := value) (count := count)
    by exact PRESENT.
  unfold effective_count. destruct remaining as [|remaining];
    [destruct count|]; reflexivity.
Qed.

Theorem successful_current_calls_preserve_both_suffixes :
  forall left right cursor left_value left_count right_value right_count,
  nth_error left (lex_left_index cursor) = Some (left_value, left_count) ->
  nth_error right (lex_right_index cursor) = Some (right_value, right_count) ->
  left_suffix left cursor = left_suffix left (current_repeated_counts left_count right_count cursor) /\
  right_suffix right cursor = right_suffix right (current_repeated_counts left_count right_count cursor).
Proof.
  intros left right cursor left_value left_count right_value right_count LEFT RIGHT.
  unfold left_suffix, right_suffix. cbn [current_repeated_counts]. split;
    eapply restoring_the_original_count_preserves_the_suffix; eassumption.
Qed.

Lemma consuming_a_positive_run_exposes_the_exact_remaining_suffix :
  forall roster index value count remaining consumed,
  nth_error roster index = Some (value, count) ->
  0 < remaining -> consumed <= remaining ->
  remaining_suffix roster index remaining = repeat value consumed ++
    remaining_suffix roster
      (if remaining - consumed =? 0 then S index else index) (remaining - consumed).
Proof.
  intros roster index value count remaining consumed PRESENT POSITIVE BOUND.
  destruct (remaining - consumed =? 0) eqn:EXHAUSTED.
  - apply Nat.eqb_eq in EXHAUSTED.
    assert (SAME : consumed = remaining) by lia. subst consumed.
    rewrite Nat.sub_diag, zero_remaining_denotes_the_complete_original_suffix.
    rewrite present_item_exposes_its_original_run with (value := value) (count := count)
      by exact PRESENT.
    unfold effective_count.
    assert (ACTIVE : (remaining =? 0) = false) by (apply Nat.eqb_neq; lia).
    now rewrite ACTIVE.
  - apply Nat.eqb_neq in EXHAUSTED.
    rewrite !present_item_exposes_its_original_run with (value := value) (count := count)
      by exact PRESENT.
    unfold effective_count.
    assert (ACTIVE : (remaining =? 0) = false) by (apply Nat.eqb_neq; lia).
    assert (REST : (remaining - consumed =? 0) = false) by (apply Nat.eqb_neq; lia).
    rewrite ACTIVE, REST.
    replace remaining with (consumed + (remaining - consumed)) at 1 by lia.
    rewrite repeat_app, app_assoc. reflexivity.
Qed.

Lemma equal_repeated_prefixes_cancel_without_term_identity :
  forall left_value right_value count left right,
  compare left_value right_value = Eq ->
  list_compare compare (repeat left_value count ++ left) (repeat right_value count ++ right) =
    list_compare compare left right.
Proof.
  intros left_value right_value count left right EQUAL.
  induction count; cbn [repeat app list_compare]; [reflexivity|].
  now rewrite EQUAL.
Qed.

Theorem equal_advance_preserves_comparison_and_consumes_the_same_count :
  forall left right cursor left_value left_count right_value right_count,
  nth_error left (lex_left_index cursor) = Some (left_value, left_count) ->
  nth_error right (lex_right_index cursor) = Some (right_value, right_count) ->
  0 < lex_left_remaining cursor -> 0 < lex_right_remaining cursor ->
  compare left_value right_value = Eq ->
  let consumed := Nat.min (lex_left_remaining cursor) (lex_right_remaining cursor) in
  list_compare compare (left_suffix left cursor) (right_suffix right cursor) =
    list_compare compare (left_suffix left (advance_equal_counts cursor))
      (right_suffix right (advance_equal_counts cursor)) /\
  length (left_suffix left cursor) = consumed + length (left_suffix left (advance_equal_counts cursor)) /\
  length (right_suffix right cursor) = consumed + length (right_suffix right (advance_equal_counts cursor)).
Proof.
  intros left right cursor left_value left_count right_value right_count
    LEFT RIGHT LEFT_POS RIGHT_POS EQUAL consumed.
  assert (LEFT_SUFFIX : left_suffix left cursor =
    repeat left_value consumed ++ left_suffix left (advance_equal_counts cursor)).
  { unfold left_suffix. cbn [advance_equal_counts]. unfold consumed.
    eapply consuming_a_positive_run_exposes_the_exact_remaining_suffix;
      [exact LEFT|exact LEFT_POS|apply Nat.le_min_l]. }
  assert (RIGHT_SUFFIX : right_suffix right cursor =
    repeat right_value consumed ++ right_suffix right (advance_equal_counts cursor)).
  { unfold right_suffix. cbn [advance_equal_counts]. unfold consumed.
    eapply consuming_a_positive_run_exposes_the_exact_remaining_suffix;
      [exact RIGHT|exact RIGHT_POS|apply Nat.le_min_r]. }
  split.
  - rewrite LEFT_SUFFIX, RIGHT_SUFFIX.
    now apply equal_repeated_prefixes_cancel_without_term_identity.
  - split; [rewrite LEFT_SUFFIX|rewrite RIGHT_SUFFIX];
      now rewrite length_app, repeat_length.
Qed.

Theorem a_decisive_positive_run_returns_the_original_head_result :
  forall left_value right_value left_count right_count left right,
  0 < left_count -> 0 < right_count -> compare left_value right_value <> Eq ->
  list_compare compare (repeat left_value left_count ++ left)
    (repeat right_value right_count ++ right) = compare left_value right_value.
Proof.
  intros left_value right_value [|left_count] [|right_count] left right LP RP DECISIVE;
    try lia. cbn [repeat app list_compare].
  destruct (compare left_value right_value); [contradiction|reflexivity|reflexivity].
Qed.

Theorem original_totals_match_the_exhausted_suffix_clause :
  forall left right left_total right_total consumed,
  left_total = consumed + length left -> right_total = consumed + length right ->
  (left = [] \/ right = []) ->
  Nat.compare left_total right_total = list_compare compare left right.
Proof.
  intros [|left_value left] [|right_value right] left_total right_total consumed LT RT END;
    cbn [length list_compare] in *.
  - apply Nat.compare_eq_iff. lia.
  - apply Nat.compare_lt_iff. lia.
  - apply Nat.compare_gt_iff. lia.
  - destruct END; discriminate.
Qed.

Theorem stored_total_lead_is_a_separate_lexicographic_component :
  forall left_stored right_stored left right,
  SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare left_stored right_stored)
    (list_compare compare left right) =
  SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare (list_compare compare)
    (left_stored, left) (right_stored, right).
Proof. reflexivity. Qed.

End WeightedSuffixes.
End CollectionWeightedLexResults.

Print Assumptions CollectionWeightedLexResults.expanded_length_is_the_original_repetition_sum.
Print Assumptions CollectionWeightedLexResults.successful_current_calls_preserve_both_suffixes.
Print Assumptions CollectionWeightedLexResults.equal_repeated_prefixes_cancel_without_term_identity.
Print Assumptions CollectionWeightedLexResults.equal_advance_preserves_comparison_and_consumes_the_same_count.
Print Assumptions CollectionWeightedLexResults.a_decisive_positive_run_returns_the_original_head_result.
Print Assumptions CollectionWeightedLexResults.original_totals_match_the_exhausted_suffix_clause.
Print Assumptions CollectionWeightedLexResults.stored_total_lead_is_a_separate_lexicographic_component.
