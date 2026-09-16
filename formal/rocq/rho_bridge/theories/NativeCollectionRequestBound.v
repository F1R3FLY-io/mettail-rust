(** Aggregate request counts for the EXISTING CollectionCmpPda.

    A proof-only counter instruments the original comparison callback, with
    exactly its original operands, result and state. Run/Pass/OuterExecution
    are imported unchanged. Lifting relates original derivations to this
    instrumentation; there is no second sorter or production tracing code.
    No comparator coherence, sortedness or fabricated Equal reply is assumed.

    The lexicographic annotation uses original nth_error records and the
    existing current_repeated_counts/advance_equal_counts definitions. Positive
    counts are the existing checked-roster prerequisite, not a new input cap.
    Widths count record occurrences, including aliased/equal keys. Map records
    may instantiate Entry to their original heterogeneous key/value pair;
    PairProtocol's existing two-request bound preserves their distinct roles.

    These are callback COUNTS, not callback costs, native stdlib-sort bounds,
    metadata-inspection charges or complete generated comparison receipts. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import MergeSortPdaRun MergeSortPdaPass MergeSortPdaOuter
  MergeSortPdaCursor CollectionPairAndUnitLexResults CollectionWeightedLexResults.
Import ListNotations.

Module NativeCollectionRequestBound.
Module R := MergeSortPdaRun.MergeSortPdaRun.
Module P := MergeSortPdaPass.MergeSortPdaPass.
Module O := MergeSortPdaOuter.MergeSortPdaOuter.
Module C := MergeSortPdaCursor.MergeSortPdaCursor.
Module L := CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.
Module W := CollectionWeightedLexResults.CollectionWeightedLexResults.

Section SortRequests.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Definition counted_compare left right (state : State * nat) :=
  let '(result, next) := compare left right (fst state) in
  (result, (next, S (snd state))).

Lemma original_step_lifts : forall prefix left right state next_prefix next_left next_right next,
  @R.RunStep Entry State compare prefix left right state next_prefix next_left next_right next ->
  forall before, exists after,
    @R.RunStep Entry (State * nat) counted_compare prefix left right (state, before)
      next_prefix next_left next_right (next, after).
Proof.
  intros prefix left right state next_prefix next_left next_right next STEP.
  destruct STEP; intros before.
  - exists (S before). eapply R.ComparedLeft; [|eassumption].
    unfold counted_compare. cbn [fst snd]. now rewrite H.
  - exists (S before). apply R.ComparedRight.
    unfold counted_compare. cbn [fst snd]. now rewrite H.
  - exists before. apply R.LeftTail.
  - exists before. apply R.RightTail.
Qed.

Lemma original_run_lifts : forall count prefix left right state output next,
  @R.RunExecution Entry State compare count prefix left right state output next ->
  forall before, exists after,
    @R.RunExecution Entry (State * nat) counted_compare count prefix left right
      (state, before) output (next, after).
Proof.
  intros count prefix left right state output next RUN.
  induction RUN; intros before.
  - exists before. constructor.
  - destruct (original_step_lifts _ _ _ _ _ _ _ _ H before) as [middle STEP].
    destruct (IHRUN middle) as [after REST]. exists after.
    eapply R.RunMore; eassumption.
Qed.

Lemma original_pass_lifts : forall width input state output next,
  @P.PassExecution Entry State compare width input state output next ->
  forall before, exists after,
    @P.PassExecution Entry (State * nat) counted_compare width input
      (state, before) output (next, after).
Proof.
  intros width input state output next PASS. induction PASS; intros before.
  - exists before. constructor.
  - destruct (original_run_lifts _ _ _ _ _ _ _ H before) as [middle RUN].
    destruct (IHPASS middle) as [after REST]. exists after.
    eapply P.PassMore; eassumption.
Qed.

Theorem original_sort_lifts_without_changing_operands_or_results :
  forall maximum passes width input state output next,
  @O.OuterExecution Entry State compare maximum passes width input state output next ->
  forall before, exists after,
    @O.OuterExecution Entry (State * nat) counted_compare maximum passes width
      input (state, before) output (next, after).
Proof.
  intros maximum passes width input state output next SORT.
  induction SORT; intros before.
  - exists before. constructor. assumption.
  - destruct (original_pass_lifts _ _ _ _ _ H0 before) as [middle PASS].
    destruct (IHSORT middle) as [after REST]. exists after.
    eapply O.OuterPass; eassumption.
Qed.

Lemma counted_step_uses_at_most_one_request :
  forall prefix left right state next_prefix next_left next_right next,
  @R.RunStep Entry (State * nat) counted_compare
    prefix left right state next_prefix next_left next_right next ->
  snd next <= S (snd state).
Proof.
  intros prefix left right state next_prefix next_left next_right next STEP.
  destruct STEP; try lia;
    unfold counted_compare in H;
    destruct (compare value other (fst state)) as [result changed] eqn:CALL;
    inversion H; subst; cbn [snd]; lia.
Qed.

Lemma counted_run_is_bounded_by_its_copies :
  forall count prefix left right state output next,
  @R.RunExecution Entry (State * nat) counted_compare count prefix left right state output next ->
  snd next <= snd state + count.
Proof.
  intros count prefix left right state output next RUN. induction RUN.
  - lia.
  - pose proof (counted_step_uses_at_most_one_request _ _ _ _ _ _ _ _ H). lia.
Qed.

Lemma counted_pass_is_bounded_by_source_width : forall width input state output next,
  @P.PassExecution Entry (State * nat) counted_compare width input state output next ->
  snd next <= snd state + length input.
Proof.
  intros width input state output next PASS. induction PASS.
  - cbn [length]. lia.
  - pose proof (counted_run_is_bounded_by_its_copies _ _ _ _ _ _ _ H) as REQUESTS.
    pose proof (@R.completed_source_run_copies_exactly_its_remaining_width
      Entry (State * nat) counted_compare _ _ _ _ _ _ _ H) as COPIES.
    rewrite !firstn_length, !length_skipn in COPIES.
    rewrite !length_skipn in IHPASS. cbn [length] in *. lia.
Qed.

Lemma counted_sort_is_bounded_by_passes_times_width :
  forall maximum passes width input state output next,
  @O.OuterExecution Entry (State * nat) counted_compare maximum passes width input state output next ->
  0 < width -> length input <= maximum ->
  snd next <= snd state + passes * length input.
Proof.
  intros maximum passes width input state output next SORT. induction SORT;
    intros POSITIVE BOUNDED.
  - cbn. lia.
  - pose proof (counted_pass_is_bounded_by_source_width _ _ _ _ _ H0) as REQUESTS.
    pose proof (@P.completed_source_pass_preserves_the_allocated_width
      Entry (State * nat) counted_compare _ _ _ _ _ POSITIVE H0) as WIDTH.
    destruct (C.doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length input) width BOUNDED POSITIVE H) as [PROGRESS _].
    specialize (IHSORT ltac:(lia) ltac:(lia)). nia.
Qed.

Theorem source_sort_request_envelope : forall maximum passes input state output next,
  @O.OuterExecution Entry (State * nat) counted_compare maximum passes 1 input state output next ->
  length input <= maximum ->
  snd next <= snd state + length input * (length input - 1).
Proof.
  intros maximum passes input state output next SORT BOUNDED.
  pose proof (counted_sort_is_bounded_by_passes_times_width
    _ _ _ _ _ _ _ SORT ltac:(lia) BOUNDED) as REQUESTS.
  pose proof (@O.source_outer_progress_bounds_the_number_of_passes
    Entry (State * nat) counted_compare _ _ _ _ _ _ _ SORT ltac:(lia) BOUNDED) as PASSES.
  nia.
Qed.
End SortRequests.

Section LexRequests.
Context {Entry : Type}.
Variable compare : Entry -> Entry -> comparison.

Definition pending_width (left right : list (Entry * nat)) cursor :=
  length left - L.lex_left_index cursor + length right - L.lex_right_index cursor.
Definition next_equal left_count right_count cursor :=
  L.advance_equal_counts (W.current_repeated_counts left_count right_count cursor).

Lemma equal_cursor_moves_forward : forall left_count right_count cursor,
  L.lex_left_index cursor <= L.lex_left_index (next_equal left_count right_count cursor) /\
  L.lex_right_index cursor <= L.lex_right_index (next_equal left_count right_count cursor) /\
  L.lex_left_index (next_equal left_count right_count cursor) <= S (L.lex_left_index cursor) /\
  L.lex_right_index (next_equal left_count right_count cursor) <= S (L.lex_right_index cursor) /\
  S (L.lex_left_index cursor + L.lex_right_index cursor) <=
    L.lex_left_index (next_equal left_count right_count cursor) +
    L.lex_right_index (next_equal left_count right_count cursor).
Proof.
  intros. unfold next_equal, L.advance_equal_counts, W.current_repeated_counts.
  cbn [L.lex_left_index L.lex_right_index L.lex_left_remaining L.lex_right_remaining].
  set (l := W.effective_count left_count (L.lex_left_remaining cursor)).
  set (r := W.effective_count right_count (L.lex_right_remaining cursor)).
  destruct (Nat.le_ge_cases l r) as [ORDER|ORDER].
  - rewrite (Nat.min_l _ _ ORDER), Nat.sub_diag. cbn.
    destruct (r - l =? 0); repeat split; lia.
  - rewrite (Nat.min_r _ _ ORDER), Nat.sub_diag. cbn.
    destruct (l - r =? 0); repeat split; lia.
Qed.

(** An annotation of the actual request/response prefix. PrefixStop admits
    stopping before a request (including admission refusal); decisive result
    terminates after its original requested operands. The next constructor
    follows ONLY an actual Equal result, never a chosen stand-in response. *)
Inductive LexRequests (left right : list (Entry * nat)) :
    L.UnitLexCursor -> list (Entry * Entry) -> Prop :=
| PrefixStop : forall cursor, LexRequests left right cursor []
| Decisive : forall cursor lhs lc rhs rc,
    nth_error left (L.lex_left_index cursor) = Some (lhs, lc) ->
    nth_error right (L.lex_right_index cursor) = Some (rhs, rc) ->
    0 < lc -> 0 < rc -> compare lhs rhs <> Eq ->
    LexRequests left right cursor [(lhs, rhs)]
| EqualMore : forall cursor lhs lc rhs rc rest,
    nth_error left (L.lex_left_index cursor) = Some (lhs, lc) ->
    nth_error right (L.lex_right_index cursor) = Some (rhs, rc) ->
    0 < lc -> 0 < rc -> compare lhs rhs = Eq ->
    LexRequests left right (next_equal lc rc cursor) rest ->
    LexRequests left right cursor ((lhs, rhs) :: rest).

Lemma original_present_index_is_inside : forall (items : list (Entry * nat)) index item,
  nth_error items index = Some item -> index < length items.
Proof.
  intros items index item PRESENT. apply nth_error_Some. rewrite PRESENT. discriminate.
Qed.

Theorem weighted_lex_request_prefix_is_width_bounded : forall left right cursor requests,
  LexRequests left right cursor requests ->
  length requests <= pending_width left right cursor.
Proof.
  intros left right cursor requests RUN. induction RUN.
  - cbn [length]. lia.
  - pose proof (original_present_index_is_inside _ _ _ H).
    pose proof (original_present_index_is_inside _ _ _ H0).
    cbn [length]. unfold pending_width. lia.
  - pose proof (original_present_index_is_inside _ _ _ H).
    pose proof (original_present_index_is_inside _ _ _ H0).
    pose proof (equal_cursor_moves_forward lc rc cursor) as MOVES.
    unfold pending_width in *. cbn [length]. intuition lia.
Qed.

Theorem initial_weighted_lex_requests_do_not_expand_multiplicities :
  forall left right requests,
  LexRequests left right (L.unit_cursor 0) requests ->
  length requests <= length left + length right.
Proof.
  intros. pose proof (weighted_lex_request_prefix_is_width_bounded _ _ _ _ H).
  unfold pending_width, L.unit_cursor in H0. cbn in H0. lia.
Qed.

Theorem every_lex_request_retains_original_operands : forall left right cursor requests,
  LexRequests left right cursor requests -> forall lhs rhs,
  In (lhs, rhs) requests ->
  (exists count, In (lhs, count) left) /\ (exists count, In (rhs, count) right).
Proof.
  intros left right cursor requests RUN. induction RUN; intros wanted_left wanted_right MEMBER.
  - contradiction.
  - destruct MEMBER as [SAME|IMPOSSIBLE]; [inversion SAME; subst|contradiction].
    split; eexists; eapply nth_error_In; eassumption.
  - destruct MEMBER as [SAME|MEMBER].
    + inversion SAME; subst. split; eexists; eapply nth_error_In; eassumption.
    + now apply IHRUN.
Qed.
End LexRequests.

End NativeCollectionRequestBound.

Print Assumptions NativeCollectionRequestBound.original_sort_lifts_without_changing_operands_or_results.
Print Assumptions NativeCollectionRequestBound.source_sort_request_envelope.
Print Assumptions NativeCollectionRequestBound.equal_cursor_moves_forward.
Print Assumptions NativeCollectionRequestBound.weighted_lex_request_prefix_is_width_bounded.
Print Assumptions NativeCollectionRequestBound.initial_weighted_lex_requests_do_not_expand_multiplicities.
Print Assumptions NativeCollectionRequestBound.every_lex_request_retains_original_operands.
