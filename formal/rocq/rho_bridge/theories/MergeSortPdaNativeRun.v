(** Actual indexed run branches to the existing RunStep relation.

    NativeRequest records both reads made by the readiness branch. An accepted
    response requires this same cursor/source request and exact comparison
    response; source and target do not change while waiting. This models the
    successful legal step/yield/accept handshake, not a replacement sorter or
    autonomous progress when a caller stops responding. Tail branches require
    the opposite run exhausted. Admission events and refusals are accounted
    separately; this is their successful semantic erasure. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaRun.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import MergeSortPdaRun.MergeSortPdaRun.

Module MergeSortPdaNativeRun.
Section IndexedRecords.
Context {Entry : Type}.

Lemma exact_indexed_copy_projection : forall width cursor side
    (source target next : list Entry),
  length source = width -> length target = width ->
  valid_cursor width cursor -> can_copy side cursor ->
  copy_record side cursor source target = Some (advance side cursor, next) ->
  exists value,
    nth_error source (selected_index side cursor) = Some value /\
    firstn (output_index (advance side cursor)) next =
      firstn (output_index cursor) target ++ [value] /\
    selected_slice side source cursor =
      value :: selected_slice side source (advance side cursor) /\
    other_slice side source cursor = other_slice side source (advance side cursor) /\
    length next = width /\ valid_cursor width (advance side cursor) /\
    remaining cursor = S (remaining (advance side cursor)).
Proof.
  intros width cursor side source target next LS LT HV HC COPY.
  destruct (source_indexed_copy_preserves_the_completed_prefix
    width cursor side source target LS LT HV HC)
    as [value [actual [HN [HA [HL [HOLD [HP [HVN HR]]]]]]]].
  rewrite COPY in HA. inversion HA; subst actual.
  exists value. split; [exact HN|]. split; [exact HP|]. split.
  - destruct side; unfold selected_slice, left_slice, right_slice, advance;
      cbn [left_index right_index run_middle run_end];
      apply source_slice_head_is_the_native_indexed_record; assumption.
  - split; [destruct side; reflexivity|]. split; [exact HL|].
    split; [exact HVN|exact HR].
Qed.

Definition NativeRequest (source : list Entry) cursor lhs rhs :=
  can_copy FromLeft cursor /\ can_copy FromRight cursor /\
  nth_error source (left_index cursor) = Some lhs /\
  nth_error source (right_index cursor) = Some rhs.

Lemma native_request_projects_both_live_heads : forall source cursor lhs rhs,
  NativeRequest source cursor lhs rhs ->
  left_slice source cursor = lhs :: left_slice source (advance FromLeft cursor) /\
  right_slice source cursor = rhs :: right_slice source (advance FromRight cursor).
Proof.
  intros source cursor lhs rhs [HL [HR [NL NR]]]. split.
  - unfold left_slice, advance; cbn [left_index run_middle].
    apply source_slice_head_is_the_native_indexed_record; assumption.
  - unfold right_slice, advance; cbn [right_index run_end].
    apply source_slice_head_is_the_native_indexed_record; assumption.
Qed.

Lemma actual_failed_readiness_with_live_left_exhausts_right : forall width cursor,
  valid_cursor width cursor -> can_copy FromLeft cursor ->
  ~ (can_copy FromLeft cursor /\ can_copy FromRight cursor) ->
  right_index cursor = run_end cursor.
Proof.
  intros width cursor HV HL HN. unfold valid_cursor in HV.
  unfold can_copy in *. destruct (Nat.lt_ge_cases (right_index cursor) (run_end cursor));
    [exfalso; apply HN; auto|lia].
Qed.
Lemma actual_left_tail_exit_exhausts_left : forall width cursor,
  valid_cursor width cursor -> ~ can_copy FromLeft cursor ->
  left_index cursor = run_middle cursor.
Proof. intros width cursor HV HN. unfold valid_cursor in HV. unfold can_copy in HN. lia. Qed.
End IndexedRecords.

Section NativeBranches.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Lemma actual_left_accept_projects_RunStep : forall width cursor source target next
    lhs rhs state next_state decision,
  length source = width -> length target = width -> valid_cursor width cursor ->
  NativeRequest source cursor lhs rhs ->
  compare lhs rhs state = (Some decision, next_state) -> decision <> Gt ->
  copy_record FromLeft cursor source target = Some (advance FromLeft cursor, next) ->
  RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromLeft cursor)) next)
    (left_slice source (advance FromLeft cursor))
    (right_slice source (advance FromLeft cursor)) next_state.
Proof.
  intros width cursor source target next lhs rhs state next_state decision
    LS LT HV REQ CMP DEC COPY.
  pose proof (native_request_projects_both_live_heads source cursor lhs rhs REQ)
    as [HEADL HEADR]. destruct REQ as [LIVE [LIVER [NL NR]]].
  destruct (exact_indexed_copy_projection width cursor FromLeft source target next
    LS LT HV LIVE COPY) as [value [HN [HP [HSEL [HOTHER REST]]]]].
  change (nth_error source (left_index cursor) = Some value) in HN.
  rewrite NL in HN. inversion HN; subst value.
  change (left_slice source cursor = lhs :: left_slice source (advance FromLeft cursor)) in HSEL.
  change (RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromLeft cursor)) next)
    (left_slice source (advance FromLeft cursor)) (right_slice source cursor) next_state).
  rewrite HP, HSEL, HEADR. eapply ComparedLeft; eassumption.
Qed.
Lemma actual_right_accept_projects_RunStep : forall width cursor source target next
    lhs rhs state next_state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  NativeRequest source cursor lhs rhs ->
  compare lhs rhs state = (Some Gt, next_state) ->
  copy_record FromRight cursor source target = Some (advance FromRight cursor, next) ->
  RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromRight cursor)) next)
    (left_slice source (advance FromRight cursor))
    (right_slice source (advance FromRight cursor)) next_state.
Proof.
  intros width cursor source target next lhs rhs state next_state LS LT HV REQ CMP COPY.
  pose proof (native_request_projects_both_live_heads source cursor lhs rhs REQ)
    as [HEADL HEADR]. destruct REQ as [LIVEL [LIVE [NL NR]]].
  destruct (exact_indexed_copy_projection width cursor FromRight source target next
    LS LT HV LIVE COPY) as [value [HN [HP [HSEL [HOTHER REST]]]]].
  change (nth_error source (right_index cursor) = Some value) in HN.
  rewrite NR in HN. inversion HN; subst value.
  change (right_slice source cursor = rhs :: right_slice source (advance FromRight cursor)) in HSEL.
  change (RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromRight cursor)) next)
    (left_slice source cursor) (right_slice source (advance FromRight cursor)) next_state).
  rewrite HP, HEADL, HSEL. eapply ComparedRight; exact CMP.
Qed.
Lemma actual_left_tail_projects_RunStep : forall width cursor source target next state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  can_copy FromLeft cursor -> right_index cursor = run_end cursor ->
  copy_record FromLeft cursor source target = Some (advance FromLeft cursor, next) ->
  RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromLeft cursor)) next)
    (left_slice source (advance FromLeft cursor))
    (right_slice source (advance FromLeft cursor)) state.
Proof.
  intros width cursor source target next state LS LT HV LIVE EX COPY.
  destruct (exact_indexed_copy_projection width cursor FromLeft source target next
    LS LT HV LIVE COPY) as [value [HN [HP [HSEL [HOTHER REST]]]]].
  change (left_slice source cursor = value :: left_slice source (advance FromLeft cursor)) in HSEL.
  assert (EMPTY : right_slice source cursor = []).
  { unfold right_slice. rewrite EX. apply exhausted_slice_is_empty. }
  change (RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromLeft cursor)) next)
    (left_slice source (advance FromLeft cursor)) (right_slice source cursor) state).
  rewrite HP, HSEL, EMPTY. apply LeftTail.
Qed.
Lemma actual_right_tail_projects_RunStep : forall width cursor source target next state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  left_index cursor = run_middle cursor -> can_copy FromRight cursor ->
  copy_record FromRight cursor source target = Some (advance FromRight cursor, next) ->
  RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromRight cursor)) next)
    (left_slice source (advance FromRight cursor))
    (right_slice source (advance FromRight cursor)) state.
Proof.
  intros width cursor source target next state LS LT HV EX LIVE COPY.
  destruct (exact_indexed_copy_projection width cursor FromRight source target next
    LS LT HV LIVE COPY) as [value [HN [HP [HSEL [HOTHER REST]]]]].
  change (right_slice source cursor = value :: right_slice source (advance FromRight cursor)) in HSEL.
  assert (EMPTY : left_slice source cursor = []).
  { unfold left_slice. rewrite EX. apply exhausted_slice_is_empty. }
  change (RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index (advance FromRight cursor)) next)
    (left_slice source cursor) (right_slice source (advance FromRight cursor)) state).
  rewrite HP, HSEL, EMPTY. apply RightTail.
Qed.

(** Collapse only a legal readiness/yield/accept pair: the two reads and its
    response refer to an identical source/cursor. Tails do not compare; their
    exhausted-side premises follow from the native guard lemmas above. *)
Inductive NativeCopyStep (source : list Entry) :
    Cursor -> list Entry -> State -> Cursor -> list Entry -> State -> Prop :=
| NativeAccepted : forall cursor target next lhs rhs state next_state decision,
    NativeRequest source cursor lhs rhs ->
    compare lhs rhs state = (Some decision, next_state) ->
    copy_record (accept_side decision) cursor source target =
      Some (advance (accept_side decision) cursor, next) ->
    NativeCopyStep source cursor target state
      (advance (accept_side decision) cursor) next next_state
| NativeLeftTail : forall cursor target next state,
    can_copy FromLeft cursor -> right_index cursor = run_end cursor ->
    copy_record FromLeft cursor source target = Some (advance FromLeft cursor, next) ->
    NativeCopyStep source cursor target state (advance FromLeft cursor) next state
| NativeRightTail : forall cursor target next state,
    left_index cursor = run_middle cursor -> can_copy FromRight cursor ->
    copy_record FromRight cursor source target = Some (advance FromRight cursor, next) ->
    NativeCopyStep source cursor target state (advance FromRight cursor) next state.

Lemma native_copy_step_has_an_enabled_indexed_copy :
  forall source cursor target state next_cursor next next_state,
  NativeCopyStep source cursor target state next_cursor next next_state ->
  exists side, can_copy side cursor /\ next_cursor = advance side cursor /\
    copy_record side cursor source target = Some (advance side cursor, next).
Proof.
  intros source cursor target state next_cursor next next_state HS.
  destruct HS as [cursor target next lhs rhs state next_state decision REQ CMP COPY
    |cursor target next state LIVE EX COPY|cursor target next state EX LIVE COPY].
  - exists (accept_side decision). split.
    + destruct REQ as [HL [HR REST]]. destruct decision; assumption.
    + split; [reflexivity|exact COPY].
  - exists FromLeft. split; [exact LIVE|]. split; [reflexivity|exact COPY].
  - exists FromRight. split; [exact LIVE|]. split; [reflexivity|exact COPY].
Qed.
Theorem native_copy_step_preserves_the_bounded_cursor :
  forall source cursor target state next_cursor next next_state,
  NativeCopyStep source cursor target state next_cursor next next_state ->
  forall width, length source = width -> length target = width -> valid_cursor width cursor ->
  length next = width /\ valid_cursor width next_cursor /\
  run_end next_cursor = run_end cursor /\ remaining cursor = S (remaining next_cursor).
Proof.
  intros source cursor target state next_cursor next next_state HS width LS LT HV.
  destruct (native_copy_step_has_an_enabled_indexed_copy _ _ _ _ _ _ _ HS)
    as [side [LIVE [HC COPY]]]. subst next_cursor.
  destruct (exact_indexed_copy_projection width cursor side source target next LS LT HV LIVE COPY)
    as [value [HN [HP [HSEL [HOTHER [LN [VN REM]]]]]]].
  split; [exact LN|]. split; [exact VN|]. split; [destruct side; reflexivity|exact REM].
Qed.
Theorem native_copy_step_projects_the_existing_RunStep :
  forall source cursor target state next_cursor next next_state,
  NativeCopyStep source cursor target state next_cursor next next_state ->
  forall width, length source = width -> length target = width -> valid_cursor width cursor ->
  RunStep compare (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index next_cursor) next)
    (left_slice source next_cursor) (right_slice source next_cursor) next_state.
Proof.
  intros source cursor target state next_cursor next next_state HS.
  destruct HS as [cursor target next lhs rhs state next_state decision REQ CMP COPY
    |cursor target next state LIVE EX COPY|cursor target next state EX LIVE COPY];
    intros width LS LT HV.
  - destruct decision; cbn [accept_side] in COPY |- *.
    + eapply actual_left_accept_projects_RunStep; try eassumption; discriminate.
    + eapply actual_left_accept_projects_RunStep; try eassumption; discriminate.
    + eapply actual_right_accept_projects_RunStep; eassumption.
  - eapply actual_left_tail_projects_RunStep; eassumption.
  - eapply actual_right_tail_projects_RunStep; eassumption.
Qed.

Lemma native_both_exhausted_is_the_completed_output_boundary :
  forall width cursor (source : list Entry),
  valid_cursor width cursor -> left_index cursor = run_middle cursor ->
  right_index cursor = run_end cursor ->
  output_index cursor = run_end cursor /\
  left_slice source cursor = [] /\ right_slice source cursor = [].
Proof.
  intros width cursor source HV EL ER. split.
  - unfold valid_cursor in HV. lia.
  - split.
    + unfold left_slice. rewrite EL. apply exhausted_slice_is_empty.
    + unfold right_slice. rewrite ER. apply exhausted_slice_is_empty.
Qed.

Inductive IndexedRunExecution (source : list Entry) : nat ->
    Cursor -> list Entry -> State -> Cursor -> list Entry -> State -> Prop :=
| IndexedRunDone : forall cursor target state,
    left_index cursor = run_middle cursor -> right_index cursor = run_end cursor ->
    IndexedRunExecution source 0 cursor target state cursor target state
| IndexedRunMore : forall count cursor target state middle next next_state
    final_cursor final_target last,
    NativeCopyStep source cursor target state middle next next_state ->
    IndexedRunExecution source count middle next next_state final_cursor final_target last ->
    IndexedRunExecution source (S count) cursor target state final_cursor final_target last.

Theorem indexed_run_projects_RunExecution_and_preserves_buffers :
  forall source count cursor target state final_cursor final_target last,
  IndexedRunExecution source count cursor target state final_cursor final_target last ->
  forall width, length source = width -> length target = width -> valid_cursor width cursor ->
  RunExecution compare count (firstn (output_index cursor) target)
    (left_slice source cursor) (right_slice source cursor) state
    (firstn (output_index final_cursor) final_target) last /\
  length final_target = width /\ valid_cursor width final_cursor /\
  run_end final_cursor = run_end cursor /\ output_index final_cursor = run_end cursor.
Proof.
  intros source count cursor target state final_cursor final_target last HR.
  induction HR as [cursor target state EL ER
    |count cursor target state middle next next_state final_cursor final_target last HS HR IH];
    intros width LS LT HV.
  - destruct (native_both_exhausted_is_the_completed_output_boundary width cursor source HV EL ER)
      as [OUT [EMPTYL EMPTYR]].
    split; [rewrite EMPTYL, EMPTYR; constructor|].
    split; [exact LT|]. split; [exact HV|]. split; [reflexivity|exact OUT].
  - destruct (native_copy_step_preserves_the_bounded_cursor
      source cursor target state middle next next_state HS width LS LT HV)
      as [LN [VN [END REM]]].
    destruct (IH width LS LN VN) as [RUN [LF [VF [EF OF]]]].
    split.
    + eapply RunMore; [eapply native_copy_step_projects_the_existing_RunStep; eassumption|exact RUN].
    + split; [exact LF|]. split; [exact VF|]. split; congruence.
Qed.
Theorem indexed_run_copies_exactly_the_native_remaining_width :
  forall source count cursor target state final_cursor final_target last,
  IndexedRunExecution source count cursor target state final_cursor final_target last ->
  forall width, length source = width -> length target = width -> valid_cursor width cursor ->
  count = remaining cursor.
Proof.
  intros source count cursor target state final_cursor final_target last HR.
  induction HR as [cursor target state EL ER
    |count cursor target state middle next next_state final_cursor final_target last HS HR IH];
    intros width LS LT HV.
  - unfold remaining. rewrite EL, ER. lia.
  - destruct (native_copy_step_preserves_the_bounded_cursor
      source cursor target state middle next next_state HS width LS LT HV)
      as [LN [VN [END REM]]].
    specialize (IH width LS LN VN). lia.
Qed.
Theorem indexed_run_copy_count_is_bounded_by_source_length :
  forall source count cursor target state final_cursor final_target last,
  IndexedRunExecution source count cursor target state final_cursor final_target last ->
  forall width, length source = width -> length target = width -> valid_cursor width cursor ->
  count <= width.
Proof.
  intros source count cursor target state final_cursor final_target last HR width LS LT HV.
  pose proof (indexed_run_copies_exactly_the_native_remaining_width
    source count cursor target state final_cursor final_target last HR width LS LT HV) as HC.
  unfold remaining in HC. unfold valid_cursor in HV. lia.
Qed.

Lemma enabled_native_record_exists : forall width cursor side (source : list Entry),
  length source = width -> valid_cursor width cursor -> can_copy side cursor ->
  exists value, nth_error source (selected_index side cursor) = Some value.
Proof.
  intros width cursor side source LS HV HC.
  destruct (enabled_copy_has_valid_source_and_target_indices width cursor side HV HC) as [HI HO].
  destruct (nth_error source (selected_index side cursor)) as [value|] eqn:HN.
  - exists value. reflexivity.
  - apply nth_error_None in HN. lia.
Qed.
Lemma enabled_native_copy_exists : forall width cursor side (source target : list Entry),
  length source = width -> length target = width ->
  valid_cursor width cursor -> can_copy side cursor ->
  exists next, copy_record side cursor source target = Some (advance side cursor, next).
Proof.
  intros width cursor side source target LS LT HV HC.
  destruct (source_indexed_copy_preserves_the_completed_prefix
    width cursor side source target LS LT HV HC)
    as [value [next [HN [COPY REST]]]]. now exists next.
Qed.
Theorem responding_driver_enables_an_actual_native_copy :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall width source cursor target state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  0 < remaining cursor ->
  exists next_cursor next next_state,
    NativeCopyStep source cursor target state next_cursor next next_state.
Proof.
  intros TOTAL width source cursor target state LS LT HV MORE.
  destruct (Nat.lt_ge_cases (left_index cursor) (run_middle cursor)) as [LL|LE];
    destruct (Nat.lt_ge_cases (right_index cursor) (run_end cursor)) as [RL|RE].
  - assert (LC : can_copy FromLeft cursor) by exact LL.
    assert (RC : can_copy FromRight cursor) by exact RL.
    destruct (enabled_native_record_exists width cursor FromLeft source LS HV LC) as [lhs NL].
    destruct (enabled_native_record_exists width cursor FromRight source LS HV RC) as [rhs NR].
    destruct (TOTAL lhs rhs state) as [decision [next_state CMP]].
    assert (LIVE : can_copy (accept_side decision) cursor)
      by (destruct decision; assumption).
    destruct (enabled_native_copy_exists width cursor (accept_side decision) source target LS LT HV LIVE)
      as [next COPY].
    exists (advance (accept_side decision) cursor), next, next_state.
    eapply NativeAccepted with (lhs := lhs) (rhs := rhs).
    + unfold NativeRequest. split; [exact LC|]. split; [exact RC|].
      split; [exact NL|exact NR].
    + exact CMP.
    + exact COPY.
  - assert (LIVE : can_copy FromLeft cursor) by exact LL.
    assert (EX : right_index cursor = run_end cursor) by (unfold valid_cursor in HV; lia).
    destruct (enabled_native_copy_exists width cursor FromLeft source target LS LT HV LIVE) as [next COPY].
    exists (advance FromLeft cursor), next, state. eapply NativeLeftTail; eassumption.
  - assert (LIVE : can_copy FromRight cursor) by exact RL.
    assert (EX : left_index cursor = run_middle cursor) by (unfold valid_cursor in HV; lia).
    destruct (enabled_native_copy_exists width cursor FromRight source target LS LT HV LIVE) as [next COPY].
    exists (advance FromRight cursor), next, state. eapply NativeRightTail; eassumption.
  - unfold remaining in MORE. lia.
Qed.
Lemma responding_driver_constructs_an_indexed_run_with_sufficient_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall fuel width source cursor target state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  remaining cursor <= fuel ->
  exists count final_cursor final_target last,
    IndexedRunExecution source count cursor target state final_cursor final_target last.
Proof.
  intros TOTAL fuel. induction fuel as [|fuel IH];
    intros width source cursor target state LS LT HV HB.
  - exists 0, cursor, target, state. apply IndexedRunDone;
      unfold remaining in HB; unfold valid_cursor in HV; lia.
  - destruct (Nat.eq_dec (remaining cursor) 0) as [DONE|MORE].
    + exists 0, cursor, target, state. apply IndexedRunDone;
        unfold remaining in DONE; unfold valid_cursor in HV; lia.
    + destruct (responding_driver_enables_an_actual_native_copy TOTAL
        width source cursor target state LS LT HV ltac:(lia))
        as [middle [next [next_state STEP]]].
      destruct (native_copy_step_preserves_the_bounded_cursor
        source cursor target state middle next next_state STEP width LS LT HV)
        as [LN [VN [END REM]]].
      destruct (IH width source middle next next_state LS LN VN ltac:(lia))
        as [count [final_cursor [final_target [last RUN]]]].
      exists (S count), final_cursor, final_target, last.
      eapply IndexedRunMore; eassumption.
Qed.
Theorem responding_driver_completes_the_actual_indexed_run :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall width source cursor target state,
  length source = width -> length target = width -> valid_cursor width cursor ->
  exists final_cursor final_target last,
    IndexedRunExecution source (remaining cursor) cursor target state final_cursor final_target last.
Proof.
  intros TOTAL width source cursor target state LS LT HV.
  destruct (responding_driver_constructs_an_indexed_run_with_sufficient_fuel TOTAL
    (remaining cursor) width source cursor target state LS LT HV (Nat.le_refl _))
    as [count [final_cursor [final_target [last RUN]]]].
  pose proof (indexed_run_copies_exactly_the_native_remaining_width
    source count cursor target state final_cursor final_target last RUN width LS LT HV) as COUNT.
  subst count. now exists final_cursor, final_target, last.
Qed.
End NativeBranches.

Print Assumptions exact_indexed_copy_projection.
Print Assumptions native_request_projects_both_live_heads.
Print Assumptions actual_failed_readiness_with_live_left_exhausts_right.
Print Assumptions actual_left_tail_exit_exhausts_left.
Print Assumptions actual_left_accept_projects_RunStep.
Print Assumptions actual_right_accept_projects_RunStep.
Print Assumptions actual_left_tail_projects_RunStep.
Print Assumptions actual_right_tail_projects_RunStep.
Print Assumptions native_copy_step_preserves_the_bounded_cursor.
Print Assumptions native_copy_step_projects_the_existing_RunStep.
Print Assumptions native_both_exhausted_is_the_completed_output_boundary.
Print Assumptions indexed_run_projects_RunExecution_and_preserves_buffers.
Print Assumptions indexed_run_copies_exactly_the_native_remaining_width.
Print Assumptions indexed_run_copy_count_is_bounded_by_source_length.
Print Assumptions responding_driver_enables_an_actual_native_copy.
Print Assumptions responding_driver_completes_the_actual_indexed_run.
End MergeSortPdaNativeRun.
