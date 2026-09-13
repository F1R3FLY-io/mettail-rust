(** Successful source-result projection for CollectionCmpPda Map pairs.

    request_item_comparison / request_secondary_or_accept /
    accept_term_comparison implement key.then_with(value). Primary alias skips
    the primary request; primary non-Equal never requests secondary. A
    secondary response is forwarded unchanged to the saved destination.
    The source producer pair() supplies Some(value), repetitions=1;
    absent-secondary and weighted Bag branches are deliberately not modeled.

    Alias soundness concerns valid typed immutable borrows and reflexivity of
    their comparison classes. It does not require injective class views or
    term Eq iff comparison Equal. Response functions denote completed original
    native/generated comparisons, not a category helper's scheduling Equal.
    Their concrete source factorization remains a separate induction.

    Unit lex projection starts after sorting, on the actual resulting
    immutable rosters, with Equal lead and zero indices/remaining counts.
    Existing native-sort correspondence supplies those rosters and preserves
    lengths. Source admission/owner/refusal laws remain separate: these result
    laws do not assert that every request or full profile is admitted. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Lia.
From RhoBridge Require Import AdmittedCollectionComparisonOwnership
  AdmittedGeneratedCollectionScheduling AdmittedComparisonClasses MergeSortPdaRun.
From RuntimeGrammar Require Import SemanticComparisonLaws.
Import ListNotations.

Module CollectionPairAndUnitLexResults.

Theorem alias_class_views_suffice_for_the_native_shortcut :
  forall (Term Key : Type) (compare : Term -> Term -> comparison)
    (key_compare : Key -> Key -> comparison) (view : Term -> Key),
  SemanticComparisonLaws.SemanticComparisonLaws.Laws key_compare ->
  (forall x y, compare x y = key_compare (view x) (view y)) ->
  forall x y, view x = view y -> compare x y = Eq.
Proof.
  intros Term Key compare key_compare view LAWS FACTOR x y SAME.
  apply (@AdmittedComparisonClasses.AdmittedComparisonClasses.class_equality
    Term Key compare key_compare view LAWS FACTOR x y). exact SAME.
Qed.

Section PairRequests.
Context {Key Value : Type}.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Hypothesis key_alias_sound : forall x y, key_alias x y = true -> key_compare x y = Eq.
Hypothesis value_alias_sound : forall x y, value_alias x y = true -> value_compare x y = Eq.

Definition Answer := (AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Role * comparison)%type.

Inductive SecondaryProtocol (lhs rhs : Value) : list Answer -> comparison -> Prop :=
| SecondaryAlias : value_alias lhs rhs = true -> SecondaryProtocol lhs rhs [] Eq
| SecondaryAnswered : forall result,
    value_alias lhs rhs = false -> value_compare lhs rhs = result ->
    SecondaryProtocol lhs rhs
      [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary, result)] result.

Inductive PairProtocol (lhs rhs : Key * Value) : list Answer -> comparison -> Prop :=
| PairPrimaryAlias : forall answers result,
    key_alias (fst lhs) (fst rhs) = true ->
    SecondaryProtocol (snd lhs) (snd rhs) answers result -> PairProtocol lhs rhs answers result
| PairPrimaryDecisive : forall result,
    key_alias (fst lhs) (fst rhs) = false ->
    key_compare (fst lhs) (fst rhs) = result -> result <> Eq ->
    PairProtocol lhs rhs
      [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, result)] result
| PairPrimaryEqual : forall answers result,
    key_alias (fst lhs) (fst rhs) = false -> key_compare (fst lhs) (fst rhs) = Eq ->
    SecondaryProtocol (snd lhs) (snd rhs) answers result ->
    PairProtocol lhs rhs
      ((AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, Eq) :: answers) result.

Lemma secondary_protocol_returns_the_original_value_result : forall lhs rhs answers result,
  SecondaryProtocol lhs rhs answers result -> result = value_compare lhs rhs.
Proof.
  intros lhs rhs answers result HS. destruct HS as [HA|result HA HR].
  - symmetry. now apply value_alias_sound.
  - symmetry. exact HR.
Qed.

Theorem pair_request_accept_returns_key_then_value : forall lhs rhs answers result,
  PairProtocol lhs rhs answers result ->
  result = SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare lhs rhs.
Proof.
  intros lhs rhs answers result HP.
  destruct HP as [answers result HA HS|result HA HK HD|answers result HA HK HS];
    unfold SemanticComparisonLaws.SemanticComparisonLaws.pair_compare.
  - rewrite (key_alias_sound _ _ HA).
    eapply secondary_protocol_returns_the_original_value_result. exact HS.
  - rewrite HK. destruct result; [contradiction|reflexivity|reflexivity].
  - rewrite HK. eapply secondary_protocol_returns_the_original_value_result. exact HS.
Qed.

Lemma secondary_protocol_requests_at_most_one_term : forall lhs rhs answers result,
  SecondaryProtocol lhs rhs answers result -> length answers <= 1.
Proof. intros lhs rhs answers result HS. destruct HS; cbn [length]; lia. Qed.

Theorem pair_protocol_requests_at_most_two_terms : forall lhs rhs answers result,
  PairProtocol lhs rhs answers result -> length answers <= 2.
Proof.
  intros lhs rhs answers result HP.
  destruct HP as [answers result HA HS | result HA HK HD | answers result HA HK HS].
  - pose proof (secondary_protocol_requests_at_most_one_term _ _ _ _ HS). lia.
  - cbn [length]. lia.
  - pose proof (secondary_protocol_requests_at_most_one_term _ _ _ _ HS). cbn [length]. lia.
Qed.

Lemma original_secondary_response_constructs_its_protocol : forall lhs rhs,
  exists answers result, SecondaryProtocol lhs rhs answers result.
Proof.
  intros lhs rhs. destruct (value_alias lhs rhs) eqn:HA.
  - exists [], Eq. now apply SecondaryAlias.
  - exists [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary,
      value_compare lhs rhs)], (value_compare lhs rhs).
    apply SecondaryAnswered; [exact HA|reflexivity].
Qed.

Theorem original_pair_responses_construct_the_request_protocol : forall lhs rhs,
  exists answers result, PairProtocol lhs rhs answers result.
Proof.
  intros lhs rhs. destruct (key_alias (fst lhs) (fst rhs)) eqn:HA.
  - destruct (original_secondary_response_constructs_its_protocol (snd lhs) (snd rhs)) as [answers [result HS]].
    exists answers, result. eapply PairPrimaryAlias; eassumption.
  - destruct (key_compare (fst lhs) (fst rhs)) eqn:HK.
    + destruct (original_secondary_response_constructs_its_protocol (snd lhs) (snd rhs)) as [answers [result HS]].
      exists ((AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, Eq) :: answers), result.
      eapply PairPrimaryEqual; eassumption.
    + exists [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, Lt)], Lt.
      apply PairPrimaryDecisive; try assumption; discriminate.
    + exists [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, Gt)], Gt.
      apply PairPrimaryDecisive; try assumption; discriminate.
Qed.

Theorem actual_pair_storage_is_secondary_present_and_unit : forall pair : Key * Value,
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.primary
    (AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry pair) = fst pair /\
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.secondary
    (AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry pair) = Some (snd pair) /\
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.repetitions
    (AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry pair) = 1.
Proof. intros. repeat split; reflexivity. Qed.

Lemma paired_roster_repetition_sum_is_its_length : forall pairs : list (Key * Value),
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.repetition_sum
    (map AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry pairs) = length pairs.
Proof.
  intro pairs. induction pairs as [|pair rest IH]; [reflexivity|].
  change (1 + AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.repetition_sum
    (map AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry rest) = S (length rest)).
  rewrite IH. lia.
Qed.

Theorem native_sort_permutation_preserves_the_exact_paired_unit_representation :
  forall pairs sorted,
  Permutation
    (map (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry Key Value) pairs) sorted ->
  exists sorted_pairs,
    sorted = map AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry sorted_pairs /\
    Permutation pairs sorted_pairs /\ length sorted_pairs = length pairs /\
    AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.repetition_sum sorted = length pairs.
Proof.
  intros pairs sorted HP.
  destruct (@Permutation_map_inv (Key * Value)
    (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Entry Key Value)
    (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.paired_entry Key Value)
    sorted pairs (Permutation_sym HP)) as [sorted_pairs [HS PERM]].
  pose proof (Permutation_length PERM) as LEN.
  exists sorted_pairs. split; [exact HS|]. split; [exact PERM|]. split; [lia|].
  rewrite HS, paired_roster_repetition_sum_is_its_length. lia.
Qed.

Record UnitLexCursor := { lex_left_index : nat; lex_right_index : nat;
  lex_left_remaining : nat; lex_right_remaining : nat }.
Definition unit_cursor index := {| lex_left_index := index; lex_right_index := index;
  lex_left_remaining := 0; lex_right_remaining := 0 |}.
Definition current_unit_counts cursor :=
  {| lex_left_index := lex_left_index cursor; lex_right_index := lex_right_index cursor;
     lex_left_remaining := if lex_left_remaining cursor =? 0 then 1 else lex_left_remaining cursor;
     lex_right_remaining := if lex_right_remaining cursor =? 0 then 1 else lex_right_remaining cursor |}.
Definition advance_equal_counts cursor :=
  let consumed := Nat.min (lex_left_remaining cursor) (lex_right_remaining cursor) in
  let left := lex_left_remaining cursor - consumed in
  let right := lex_right_remaining cursor - consumed in
  {| lex_left_index := if left =? 0 then S (lex_left_index cursor) else lex_left_index cursor;
     lex_right_index := if right =? 0 then S (lex_right_index cursor) else lex_right_index cursor;
     lex_left_remaining := left; lex_right_remaining := right |}.

(** current_left/right restore 1 from 0; the existing min/subtract/zero-test
    block consumes both and increments both indices. *)
Theorem current_and_equal_advance_preserve_synchronized_unit_indices : forall index,
  advance_equal_counts (current_unit_counts (unit_cursor index)) = unit_cursor (S index).
Proof. reflexivity. Qed.

Lemma present_index_is_bounded : forall (items : list (Key * Value)) index item,
  nth_error items index = Some item -> index < length items.
Proof. intros items index item HN. apply nth_error_Some. rewrite HN. discriminate. Qed.

Lemma exhausted_left_total_comparison_is_the_list_terminal_clause : forall lhs rhs index,
  index <= length lhs -> index <= length rhs -> nth_error lhs index = None ->
  Nat.compare (length lhs) (length rhs) =
    list_compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare)
      (skipn index lhs) (skipn index rhs).
Proof.
  intros lhs rhs index BL BR END. apply nth_error_None in END.
  assert (EMPTY : skipn index lhs = []) by (apply skipn_all2; lia).
  rewrite EMPTY. pose proof (length_skipn index rhs) as LEN.
  destruct (skipn index rhs) as [|head rest] eqn:TAIL;
    cbn [length] in LEN; cbn [list_compare].
  - apply Nat.compare_eq_iff. lia.
  - apply Nat.compare_lt_iff. lia.
Qed.

Lemma exhausted_right_total_comparison_is_the_list_terminal_clause : forall lhs rhs index,
  index <= length lhs -> index <= length rhs -> nth_error rhs index = None ->
  Nat.compare (length lhs) (length rhs) =
    list_compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare)
      (skipn index lhs) (skipn index rhs).
Proof.
  intros lhs rhs index BL BR END. apply nth_error_None in END.
  assert (EMPTY : skipn index rhs = []) by (apply skipn_all2; lia).
  rewrite EMPTY. pose proof (length_skipn index lhs) as LEN.
  destruct (skipn index lhs) as [|head rest] eqn:TAIL;
    cbn [length] in LEN; cbn [list_compare].
  - apply Nat.compare_eq_iff. lia.
  - apply Nat.compare_gt_iff. lia.
Qed.

(** Each constructor is one actual Lexicographic phase outcome. The shared
    index follows the unit-count transition, initially unit_cursor 0. A
    decisive accepted pair sets lead and Phase::Lead, whose next match returns
    the same result. Exhaustion uses original totals, instantiated to roster
    lengths by the complete Map producer and sort length preservation. *)
Inductive UnitLexExecution (lhs rhs : list (Key * Value)) : nat -> nat -> comparison -> Prop :=
| UnitLeftExhausted : forall index,
    nth_error lhs index = None ->
    UnitLexExecution lhs rhs index 0 (Nat.compare (length lhs) (length rhs))
| UnitRightExhausted : forall index left,
    nth_error lhs index = Some left -> nth_error rhs index = None ->
    UnitLexExecution lhs rhs index 0 (Nat.compare (length lhs) (length rhs))
| UnitEqualPair : forall index count left right answers result,
    nth_error lhs index = Some left -> nth_error rhs index = Some right ->
    PairProtocol left right answers Eq ->
    UnitLexExecution lhs rhs (S index) count result ->
    UnitLexExecution lhs rhs index (S count) result
| UnitDecisivePair : forall index left right answers result,
    nth_error lhs index = Some left -> nth_error rhs index = Some right ->
    PairProtocol left right answers result -> result <> Eq ->
    UnitLexExecution lhs rhs index 1 result.

Theorem unit_roster_lex_returns_the_existing_list_comparison :
  forall lhs rhs index count result,
  UnitLexExecution lhs rhs index count result ->
  index <= length lhs -> index <= length rhs ->
  result = list_compare
    (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare)
    (skipn index lhs) (skipn index rhs).
Proof.
  intros lhs rhs index count result HX.
  induction HX as [index END|index left NL END
    |index count left right answers result NL NR PAIR NEXT IH
    |index left right answers result NL NR PAIR DEC]; intros BL BR.
  - eapply exhausted_left_total_comparison_is_the_list_terminal_clause; eassumption.
  - eapply exhausted_right_total_comparison_is_the_list_terminal_clause; eassumption.
  - pose proof (present_index_is_bounded lhs index left NL) as LL.
    pose proof (present_index_is_bounded rhs index right NR) as LR.
    pose proof (pair_request_accept_returns_key_then_value left right answers Eq PAIR) as PC.
    rewrite (MergeSortPdaRun.MergeSortPdaRun.skipn_at_present_index index lhs left NL),
      (MergeSortPdaRun.MergeSortPdaRun.skipn_at_present_index index rhs right NR).
    cbn [list_compare]. rewrite <- PC. apply IH; lia.
  - pose proof (pair_request_accept_returns_key_then_value left right answers result PAIR) as PC.
    rewrite (MergeSortPdaRun.MergeSortPdaRun.skipn_at_present_index index lhs left NL),
      (MergeSortPdaRun.MergeSortPdaRun.skipn_at_present_index index rhs right NR).
    cbn [list_compare]. rewrite <- PC. destruct result; [contradiction|reflexivity|reflexivity].
Qed.

Theorem unit_roster_visits_a_bounded_synchronized_prefix :
  forall lhs rhs index count result,
  UnitLexExecution lhs rhs index count result ->
  index <= length lhs -> index <= length rhs ->
  count + index <= length lhs /\ count + index <= length rhs.
Proof.
  intros lhs rhs index count result HX.
  induction HX as [index END|index left NL END
    |index count left right answers result NL NR PAIR NEXT IH
    |index left right answers result NL NR PAIR DEC]; intros BL BR.
  - cbn [Nat.add]. split; assumption.
  - cbn [Nat.add]. split; assumption.
  - pose proof (present_index_is_bounded lhs index left NL) as LL.
    pose proof (present_index_is_bounded rhs index right NR) as LR.
    destruct (IH ltac:(lia) ltac:(lia)) as [HL HR]. split; lia.
  - pose proof (present_index_is_bounded lhs index left NL) as LL.
    pose proof (present_index_is_bounded rhs index right NR) as LR. split; lia.
Qed.

Theorem zero_initialized_map_lex_returns_sorted_pair_list_comparison :
  forall lhs rhs count result,
  UnitLexExecution lhs rhs 0 count result ->
  result = list_compare
    (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare) lhs rhs.
Proof.
  intros lhs rhs count result HX.
  exact (unit_roster_lex_returns_the_existing_list_comparison
    lhs rhs 0 count result HX (Nat.le_0_l _) (Nat.le_0_l _)).
Qed.

(** Pure successful-response progress, not admission totality. *)
Lemma original_unit_pair_responses_complete_with_sufficient_index_fuel :
  forall fuel lhs rhs index,
  index <= length lhs -> index <= length rhs -> length lhs - index <= fuel ->
  exists count result, UnitLexExecution lhs rhs index count result.
Proof.
  intro fuel. induction fuel as [|fuel IH]; intros lhs rhs index BL BR HB.
  - assert (END : nth_error lhs index = None) by (apply nth_error_None; lia).
    exists 0, (Nat.compare (length lhs) (length rhs)). now apply UnitLeftExhausted.
  - destruct (nth_error lhs index) as [left|] eqn:NL.
    + destruct (nth_error rhs index) as [right|] eqn:NR.
      * pose proof (present_index_is_bounded lhs index left NL) as LL.
        pose proof (present_index_is_bounded rhs index right NR) as LR.
        destruct (original_pair_responses_construct_the_request_protocol left right)
          as [answers [result PAIR]]. destruct result.
        -- destruct (IH lhs rhs (S index) ltac:(lia) ltac:(lia) ltac:(lia)) as [count [result NEXT]].
           exists (S count), result. eapply UnitEqualPair; eassumption.
        -- exists 1, Lt. eapply UnitDecisivePair; try eassumption; discriminate.
        -- exists 1, Gt. eapply UnitDecisivePair; try eassumption; discriminate.
      * exists 0, (Nat.compare (length lhs) (length rhs)). eapply UnitRightExhausted; eassumption.
    + exists 0, (Nat.compare (length lhs) (length rhs)). now apply UnitLeftExhausted.
Qed.

Theorem original_unit_map_responses_construct_a_complete_lex_trace : forall lhs rhs,
  exists count result, UnitLexExecution lhs rhs 0 count result /\
    count <= length lhs /\ count <= length rhs /\
    result = list_compare
      (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare) lhs rhs.
Proof.
  intros lhs rhs.
  destruct (original_unit_pair_responses_complete_with_sufficient_index_fuel
    (length lhs) lhs rhs 0 (Nat.le_0_l _) (Nat.le_0_l _) ltac:(lia)) as [count [result HX]].
  destruct (unit_roster_visits_a_bounded_synchronized_prefix
    lhs rhs 0 count result HX (Nat.le_0_l _) (Nat.le_0_l _)) as [HL HR].
  exists count, result. split; [exact HX|]. split; [lia|]. split; [lia|].
  now apply zero_initialized_map_lex_returns_sorted_pair_list_comparison with count.
Qed.
End PairRequests.

Print Assumptions alias_class_views_suffice_for_the_native_shortcut.
Print Assumptions secondary_protocol_returns_the_original_value_result.
Print Assumptions pair_request_accept_returns_key_then_value.
Print Assumptions pair_protocol_requests_at_most_two_terms.
Print Assumptions original_pair_responses_construct_the_request_protocol.
Print Assumptions actual_pair_storage_is_secondary_present_and_unit.
Print Assumptions paired_roster_repetition_sum_is_its_length.
Print Assumptions native_sort_permutation_preserves_the_exact_paired_unit_representation.
Print Assumptions current_and_equal_advance_preserve_synchronized_unit_indices.
Print Assumptions exhausted_left_total_comparison_is_the_list_terminal_clause.
Print Assumptions exhausted_right_total_comparison_is_the_list_terminal_clause.
Print Assumptions unit_roster_lex_returns_the_existing_list_comparison.
Print Assumptions unit_roster_visits_a_bounded_synchronized_prefix.
Print Assumptions zero_initialized_map_lex_returns_sorted_pair_list_comparison.
Print Assumptions original_unit_map_responses_construct_a_complete_lex_trace.
End CollectionPairAndUnitLexResults.
