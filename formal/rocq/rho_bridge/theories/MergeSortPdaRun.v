(** Indexed PDA run projection to the existing SemanticResultMerge.merge.

    The proof-only frame is (written target prefix, remaining left/right source
    slices, logical comparison state). It is not a runtime plan or new sorter.
    Cursor proofs establish that each original indexed overwrite appends one
    exact source record and advances exactly one slice. Readiness requests
    two nonempty heads; accept selects left on Less/Equal and right on Greater;
    exhausted-side tails copy without comparison.

    Admission controls are erased in this semantic projection. Its comparison
    state is not the runtime's entire budget: guards, tails and resets have
    separate charges in the existing source-event and consuming-owner models.
    Refusal publishes no sorted roster. Run progress requires a legal driver
    answering pending comparisons and successful admissions, not autonomous
    progress when a caller stops resuming. Pass swaps and final sort composition
    remain a separate source projection. No Eq/Cmp coherence is used here. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Lia.
From RhoBridge Require Import MergeSortPdaCursor.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.

Module MergeSortPdaRun.
Section SourceSlices.
Context {Entry : Type}.
Definition source_slice (source : list Entry) begin finish :=
  firstn (finish - begin) (skipn begin source).
Lemma skipn_at_present_index : forall index (source : list Entry) value,
  nth_error source index = Some value ->
  skipn index source = value :: skipn (S index) source.
Proof.
  induction index as [|index IH]; intros [|head rest] value HN;
    cbn [nth_error skipn] in *; try discriminate.
  - inversion HN; subst. reflexivity.
  - now apply IH.
Qed.
Theorem source_slice_head_is_the_native_indexed_record :
  forall source begin finish value,
  begin < finish -> nth_error source begin = Some value ->
  source_slice source begin finish = value :: source_slice source (S begin) finish.
Proof.
  intros source begin finish value HB HN. unfold source_slice.
  rewrite (skipn_at_present_index begin source value HN).
  replace (finish - begin) with (S (finish - S begin)) by lia.
  reflexivity.
Qed.
Theorem exhausted_slice_is_empty : forall source index,
  source_slice source index index = [].
Proof. intros. unfold source_slice. now rewrite Nat.sub_diag. Qed.
Theorem bounded_slice_length_is_the_cursor_remainder : forall source begin finish,
  begin <= finish -> finish <= length source ->
  length (source_slice source begin finish) = finish - begin.
Proof.
  intros source begin finish HB HE. unfold source_slice.
  rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.
Definition left_slice source cursor := source_slice source (left_index cursor) (run_middle cursor).
Definition right_slice source cursor := source_slice source (right_index cursor) (run_end cursor).
Definition selected_slice side source cursor := match side with
  | FromLeft => left_slice source cursor | FromRight => right_slice source cursor end.
Definition other_slice side source cursor := match side with
  | FromLeft => right_slice source cursor | FromRight => left_slice source cursor end.

Theorem native_cursor_copy_projects_one_exact_merge_record :
  forall width cursor side (source target : list Entry),
  length source = width -> length target = width ->
  valid_cursor width cursor -> can_copy side cursor ->
  exists value next,
    copy_record side cursor source target = Some (advance side cursor, next) /\
    length next = width /\ valid_cursor width (advance side cursor) /\
    firstn (output_index (advance side cursor)) next =
      firstn (output_index cursor) target ++ [value] /\
    selected_slice side source cursor = value :: selected_slice side source (advance side cursor) /\
    other_slice side source cursor = other_slice side source (advance side cursor) /\
    remaining cursor = S (remaining (advance side cursor)).
Proof.
  intros width cursor side source target LS LT HV HC.
  destruct (source_indexed_copy_preserves_the_completed_prefix
    width cursor side source target LS LT HV HC)
    as [value [next [HN [HCOPY [HL [HPOLD [HP [HNEXT HREM]]]]]]]].
  exists value, next. split; [exact HCOPY|]. split; [exact HL|].
  split; [exact HNEXT|]. split; [exact HP|]. split.
  - destruct side; unfold selected_slice, left_slice, right_slice, advance;
      cbn [left_index right_index run_middle run_end];
      apply source_slice_head_is_the_native_indexed_record; assumption.
  - split; [destruct side; reflexivity|exact HREM].
Qed.
End SourceSlices.

Section ProjectedRun.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.
Definition prefix_result (prefix : list Entry) (result : option (list Entry) * State) :=
  (option_map (app prefix) (fst result), snd result).
Definition run_result prefix lhs rhs state := prefix_result prefix
  (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
    (length lhs + length rhs) lhs rhs state).

Lemma prefix_result_empty : forall result, prefix_result [] result = result.
Proof. intros [[items|] state]; reflexivity. Qed.
Lemma copied_record_extends_prefix : forall prefix value result,
  prefix_result prefix (@SemanticResultMerge.SemanticResultMerge.prepend Entry State value result) =
  prefix_result (prefix ++ [value]) result.
Proof.
  intros prefix value [[items|] state]; [|reflexivity].
  change ((Some (prefix ++ value :: items), state) =
    (Some ((prefix ++ [value]) ++ items), state)).
  now rewrite <- app_assoc.
Qed.
Lemma merge_empty_left : forall fuel rhs state,
  @SemanticResultMerge.SemanticResultMerge.merge Entry State compare fuel [] rhs state = (Some rhs, state).
Proof. intros [|fuel] rhs state; reflexivity. Qed.
Lemma merge_empty_right : forall fuel lhs state,
  @SemanticResultMerge.SemanticResultMerge.merge Entry State compare fuel lhs [] state = (Some lhs, state).
Proof. intros [|fuel] [|head rest] state; reflexivity. Qed.
Lemma compared_left_is_the_existing_merge_clause :
  forall fuel prefix value rest other others state next decision,
  compare value other state = (Some decision, next) -> decision <> Gt ->
  prefix_result prefix
    (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
      (S fuel) (value :: rest) (other :: others) state) =
  prefix_result (prefix ++ [value])
    (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
      fuel rest (other :: others) next).
Proof.
  intros fuel prefix value rest other others state next decision HC HD.
  cbn [SemanticResultMerge.SemanticResultMerge.merge]. rewrite HC.
  destruct decision; [apply copied_record_extends_prefix|apply copied_record_extends_prefix|contradiction].
Qed.
Lemma compared_right_is_the_existing_merge_clause :
  forall fuel prefix value rest other others state next,
  compare value other state = (Some Gt, next) ->
  prefix_result prefix
    (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
      (S fuel) (value :: rest) (other :: others) state) =
  prefix_result (prefix ++ [other])
    (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
      fuel (value :: rest) others next).
Proof.
  intros fuel prefix value rest other others state next HC.
  cbn [SemanticResultMerge.SemanticResultMerge.merge]. rewrite HC.
  apply copied_record_extends_prefix.
Qed.

(** Exact projected copy cases. A compared step represents the legal
    readiness/yield/accept pair; no native comparison occurs during a tail.
    The physical slot/slice projection is proved above. *)
Inductive RunStep : list Entry -> list Entry -> list Entry -> State ->
    list Entry -> list Entry -> list Entry -> State -> Prop :=
| ComparedLeft : forall prefix value rest other others state next decision,
    compare value other state = (Some decision, next) -> decision <> Gt ->
    RunStep prefix (value :: rest) (other :: others) state
      (prefix ++ [value]) rest (other :: others) next
| ComparedRight : forall prefix value rest other others state next,
    compare value other state = (Some Gt, next) ->
    RunStep prefix (value :: rest) (other :: others) state
      (prefix ++ [other]) (value :: rest) others next
| LeftTail : forall prefix value rest state,
    RunStep prefix (value :: rest) [] state (prefix ++ [value]) rest [] state
| RightTail : forall prefix value rest state,
    RunStep prefix [] (value :: rest) state (prefix ++ [value]) [] rest state.

Theorem projected_source_step_preserves_existing_merge_result :
  forall prefix lhs rhs state next_prefix next_lhs next_rhs next_state,
  RunStep prefix lhs rhs state next_prefix next_lhs next_rhs next_state ->
  run_result prefix lhs rhs state = run_result next_prefix next_lhs next_rhs next_state.
Proof.
  intros prefix lhs rhs state next_prefix next_lhs next_rhs next_state HS.
  destruct HS as [prefix value rest other others state next decision HC HD
    |prefix value rest other others state next HC
    |prefix value rest state|prefix value rest state]; unfold run_result.
  - change (prefix_result prefix
      (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
        (S (length rest + length (other :: others))) (value :: rest) (other :: others) state) =
      prefix_result (prefix ++ [value])
      (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
        (length rest + length (other :: others)) rest (other :: others) next)).
    eapply compared_left_is_the_existing_merge_clause; eassumption.
  - replace (length (value :: rest) + length (other :: others)) with
      (S (length (value :: rest) + length others)) by (cbn [length]; lia).
    now apply compared_right_is_the_existing_merge_clause.
  - rewrite !merge_empty_right.
    change ((Some (prefix ++ value :: rest), state) =
      (Some ((prefix ++ [value]) ++ rest), state)). now rewrite <- app_assoc.
  - rewrite !merge_empty_left.
    change ((Some (prefix ++ value :: rest), state) =
      (Some ((prefix ++ [value]) ++ rest), state)). now rewrite <- app_assoc.
Qed.
Theorem projected_source_step_consumes_exactly_one_record :
  forall prefix lhs rhs state next_prefix next_lhs next_rhs next_state,
  RunStep prefix lhs rhs state next_prefix next_lhs next_rhs next_state ->
  length lhs + length rhs = S (length next_lhs + length next_rhs).
Proof.
  intros prefix lhs rhs state next_prefix next_lhs next_rhs next_state HS.
  destruct HS; cbn [length]; lia.
Qed.

Inductive RunExecution : nat -> list Entry -> list Entry -> list Entry -> State ->
    list Entry -> State -> Prop :=
| RunDone : forall prefix state, RunExecution 0 prefix [] [] state prefix state
| RunMore : forall count prefix lhs rhs state next_prefix next_lhs next_rhs next_state final last,
    RunStep prefix lhs rhs state next_prefix next_lhs next_rhs next_state ->
    RunExecution count next_prefix next_lhs next_rhs next_state final last ->
    RunExecution (S count) prefix lhs rhs state final last.

Theorem completed_source_run_is_the_existing_merge :
  forall count prefix lhs rhs state final last,
  RunExecution count prefix lhs rhs state final last ->
  run_result prefix lhs rhs state = (Some final, last).
Proof.
  intros count prefix lhs rhs state final last HR. induction HR.
  - unfold run_result. rewrite merge_empty_left.
    change ((Some (prefix ++ []), state) = (Some prefix, state)). now rewrite app_nil_r.
  - erewrite projected_source_step_preserves_existing_merge_result; [exact IHHR|eassumption].
Qed.
Theorem completed_source_run_copies_exactly_its_remaining_width :
  forall count prefix lhs rhs state final last,
  RunExecution count prefix lhs rhs state final last -> count = length lhs + length rhs.
Proof.
  intros count prefix lhs rhs state final last HR. induction HR.
  - reflexivity.
  - pose proof (projected_source_step_consumes_exactly_one_record _ _ _ _ _ _ _ _ H). lia.
Qed.
Theorem completed_empty_prefix_run_preserves_whole_records :
  forall count lhs rhs state final last,
  RunExecution count [] lhs rhs state final last -> Permutation (lhs ++ rhs) final.
Proof.
  intros count lhs rhs state final last HR.
  pose proof (completed_source_run_is_the_existing_merge _ _ _ _ _ _ _ HR) as HM.
  unfold run_result in HM. rewrite prefix_result_empty in HM.
  eapply (@SemanticResultMerge.SemanticResultMerge.merge_preserves_occurrences Entry State compare).
  exact HM.
Qed.

Lemma responding_driver_completes_with_sufficient_copy_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall fuel prefix lhs rhs state, length lhs + length rhs <= fuel ->
  exists count final last, RunExecution count prefix lhs rhs state final last.
Proof.
  intros total fuel. induction fuel as [|fuel IH];
    intros prefix [|value rest] [|other others] state HB;
    cbn [length] in HB; try lia;
    try (exists 0, prefix, state; constructor).
  - destruct (IH (prefix ++ [other]) [] others state ltac:(cbn [length]; lia))
      as [count [final [last HR]]].
    exists (S count), final, last. eapply RunMore; [apply RightTail|exact HR].
  - destruct (IH (prefix ++ [value]) rest [] state ltac:(cbn [length]; lia))
      as [count [final [last HR]]].
    exists (S count), final, last. eapply RunMore; [apply LeftTail|exact HR].
  - destruct (total value other state) as [decision [next HC]]. destruct decision.
    + destruct (IH (prefix ++ [value]) rest (other :: others) next ltac:(cbn [length]; lia))
        as [count [final [last HR]]].
      exists (S count), final, last.
      eapply RunMore; [eapply ComparedLeft; [exact HC|discriminate]|exact HR].
    + destruct (IH (prefix ++ [value]) rest (other :: others) next ltac:(cbn [length]; lia))
        as [count [final [last HR]]].
      exists (S count), final, last.
      eapply RunMore; [eapply ComparedLeft; [exact HC|discriminate]|exact HR].
    + destruct (IH (prefix ++ [other]) (value :: rest) others next ltac:(cbn [length]; lia))
        as [count [final [last HR]]].
      exists (S count), final, last.
      eapply RunMore; [apply ComparedRight; exact HC|exact HR].
Qed.
Lemma run_step_rebases_its_output_prefix :
  forall prefix lhs rhs state next_prefix next_lhs next_rhs next_state,
  RunStep prefix lhs rhs state next_prefix next_lhs next_rhs next_state ->
  exists value, next_prefix = prefix ++ [value] /\
    forall replacement,
      RunStep replacement lhs rhs state (replacement ++ [value])
        next_lhs next_rhs next_state.
Proof.
  intros prefix lhs rhs state next_prefix next_lhs next_rhs next_state HS.
  destruct HS as [prefix value rest other others state next decision HC HD
    |prefix value rest other others state next HC
    |prefix value rest state|prefix value rest state].
  - exists value. split; [reflexivity|]. intros replacement.
    eapply ComparedLeft; eassumption.
  - exists other. split; [reflexivity|]. intros replacement.
    apply ComparedRight; exact HC.
  - exists value. split; [reflexivity|]. intros replacement. apply LeftTail.
  - exists value. split; [reflexivity|]. intros replacement. apply RightTail.
Qed.

(** Changing a proof frame's output prefix changes neither its comparisons
    nor the copied records. This relates absolute native target prefixes to
    the relative empty-prefix runs consumed by the pass model. *)
Theorem run_execution_rebases_its_output_prefix :
  forall count prefix lhs rhs state final last,
  RunExecution count prefix lhs rhs state final last ->
  forall replacement, exists copied,
    final = prefix ++ copied /\
    RunExecution count replacement lhs rhs state (replacement ++ copied) last.
Proof.
  intros count prefix lhs rhs state final last HR.
  induction HR as [prefix state
    |count prefix lhs rhs state next_prefix next_lhs next_rhs next_state final last HS HT IH];
    intros replacement.
  - exists []. split; [now rewrite app_nil_r|].
    rewrite app_nil_r. constructor.
  - destruct (run_step_rebases_its_output_prefix
      _ _ _ _ _ _ _ _ HS) as [value [HP HSTEP]].
    destruct (IH (replacement ++ [value])) as [copied [HF HREST]].
    exists (value :: copied). split.
    + rewrite HF, HP, <- app_assoc. reflexivity.
    + replace (replacement ++ value :: copied)
        with ((replacement ++ [value]) ++ copied)
        by (rewrite <- app_assoc; reflexivity).
      eapply RunMore; [apply HSTEP|exact HREST].
Qed.
Corollary run_execution_strips_its_existing_output_prefix :
  forall count prefix lhs rhs state final last,
  RunExecution count prefix lhs rhs state final last ->
  exists copied,
    RunExecution count [] lhs rhs state copied last /\ final = prefix ++ copied.
Proof.
  intros count prefix lhs rhs state final last HR.
  destruct (run_execution_rebases_its_output_prefix
    _ _ _ _ _ _ _ HR []) as [copied [HF HC]].
  cbn in HC. exists copied. split; assumption.
Qed.

Theorem responding_driver_completes_the_projected_run :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall prefix lhs rhs state,
  exists final last, RunExecution (length lhs + length rhs) prefix lhs rhs state final last.
Proof.
  intros total prefix lhs rhs state.
  destruct (responding_driver_completes_with_sufficient_copy_fuel total
    (length lhs + length rhs) prefix lhs rhs state (Nat.le_refl _))
    as [count [final [last HR]]].
  pose proof (completed_source_run_copies_exactly_its_remaining_width _ _ _ _ _ _ _ HR) as HC.
  subst count. now exists final, last.
Qed.
End ProjectedRun.

Print Assumptions source_slice_head_is_the_native_indexed_record.
Print Assumptions exhausted_slice_is_empty.
Print Assumptions bounded_slice_length_is_the_cursor_remainder.
Print Assumptions native_cursor_copy_projects_one_exact_merge_record.
Print Assumptions projected_source_step_preserves_existing_merge_result.
Print Assumptions projected_source_step_consumes_exactly_one_record.
Print Assumptions completed_source_run_is_the_existing_merge.
Print Assumptions completed_source_run_copies_exactly_its_remaining_width.
Print Assumptions completed_empty_prefix_run_preserves_whole_records.
Print Assumptions run_step_rebases_its_output_prefix.
Print Assumptions run_execution_rebases_its_output_prefix.
Print Assumptions run_execution_strips_its_existing_output_prefix.
Print Assumptions responding_driver_completes_the_projected_run.
End MergeSortPdaRun.
