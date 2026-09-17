(** Completed generic merge-control inventory.

    This is a proof projection of the existing CollectionCmpPda merge sorter,
    not a second sorting algorithm. The original Entry values, directed
    callback operands, callback state, response, indexed copy and raw control
    state are retained. Counts below are indices of derivations of those
    operations; none is supplied as an unconstrained trace-length allowance.

    A run-boundary mark counts one completed clipped run. A tail mark counts
    one indexed copy outside the comparison/accept handshake. Scratch setup
    has neither mark. Native buffer ownership, source materialization and
    generated continuation scheduling retain their separate models. These
    statements concern completed ordinary callbacks, not panic unwinding or
    checked-admission refusal prefixes. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaNativeRun
  MergeSortPdaNativePass MergeSortPdaNativeOuter MergeSortPdaOuter
  GeneratedMapCoreSource GeneratedCollectionWorkCover AdmittedCollectionComparisonOwnership
  NativeCollectionRequestBound.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import MergeSortPdaNativeRun.MergeSortPdaNativeRun.
Import MergeSortPdaNativePass.MergeSortPdaNativePass.
Import MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import GeneratedCollectionWorkCover.GeneratedCollectionWorkCover.
Import AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.

Module NativeCollectionCoreInventory.
Module G := GeneratedMapCoreSource.GeneratedMapCoreSource.
Module N := NativeCollectionRequestBound.NativeCollectionRequestBound.
Module L := CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.

Definition tail_mark mark := match mark with LeftMark | RightMark => 1 | _ => 0 end.
Definition finish_mark mark := match mark with FinishMark _ _ => 1 | _ => 0 end.
Definition tails := fold_right (fun mark total => tail_mark mark + total) 0.
Definition finishes := fold_right (fun mark total => finish_mark mark + total) 0.

Section GenericControl.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.
Variable maximum : nat.

(** Each exchange is the source's immediate ready return, followed by the
    original callback and its exact waiting response. Silent operations are
    not hidden inside that return. Compression into whole step invocations
    is proved separately, after the complete source inventory is derived. *)
Inductive ControlTrace : @RawMergeState Entry -> State -> nat -> nat -> nat ->
    @RawMergeState Entry -> State -> Prop :=
| TraceDone : forall source state, ControlTrace source state 0 0 0 source state
| TraceSilent : forall source middle final state last accepted tail_count block_count,
    RawMergeSilent maximum source middle ->
    ControlTrace middle state accepted tail_count block_count final last ->
    ControlTrace source state accepted
      (tail_mark (silent_mark source middle) + tail_count)
      (finish_mark (silent_mark source middle) + block_count) final last
| TraceAnswer : forall source target lhs rhs state next_state ordering middle final last
      accepted tail_count block_count,
    merge_waiting source = false -> merge_done source = false ->
    merge_target source = Some target ->
    NativeRequest (merge_source source) (merge_cursor source) lhs rhs ->
    compare lhs rhs state = (Some ordering, next_state) ->
    raw_merge_accept (merge_set_waiting source true) ordering = Some middle ->
    ControlTrace middle next_state accepted tail_count block_count final last ->
    ControlTrace source state (S accepted) tail_count block_count final last.

Lemma traces_compose : forall first state a t b middle next c u d final last,
  ControlTrace first state a t b middle next ->
  ControlTrace middle next c u d final last ->
  ControlTrace first state (a+c) (t+u) (b+d) final last.
Proof.
  intros first state a t b middle next c u d final last FIRST SECOND.
  induction FIRST.
  - exact SECOND.
  - replace (tail_mark (silent_mark source middle) + tail_count + u)
      with (tail_mark (silent_mark source middle) + (tail_count+u)) by lia.
    replace (finish_mark (silent_mark source middle) + block_count + d)
      with (finish_mark (silent_mark source middle) + (block_count+d)) by lia.
    eapply TraceSilent; [eassumption|now apply IHFIRST].
  - cbn [Nat.add]. eapply TraceAnswer; try eassumption. now apply IHFIRST.
Qed.

Lemma trace_left_tail : forall source width cursor target next state,
  can_copy FromLeft cursor -> right_index cursor = run_end cursor ->
  copy_record FromLeft cursor source target = Some (advance FromLeft cursor, next) ->
  ControlTrace (merge_state source (Some target) width cursor false false) state 0 1 0
    (merge_state source (Some next) width (advance FromLeft cursor) false false) state.
Proof.
  intros source width cursor target next state LIVE END COPY.
  pose proof (silent_mark_left
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromLeft cursor) false false)
    target eq_refl LIVE) as MARK.
  replace 1 with (tail_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromLeft cursor) false false))+0)
    by (rewrite MARK; reflexivity).
  replace 0 with (finish_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromLeft cursor) false false))+0)
    at 3 by (rewrite MARK; reflexivity).
  eapply TraceSilent; [|constructor].
  eapply MergeLeftTail with (target:=target); try reflexivity; try eassumption.
  change (~can_copy FromRight cursor). unfold can_copy; lia.
Qed.

Lemma trace_right_tail : forall source width cursor target next state,
  left_index cursor = run_middle cursor -> can_copy FromRight cursor ->
  copy_record FromRight cursor source target = Some (advance FromRight cursor, next) ->
  ControlTrace (merge_state source (Some target) width cursor false false) state 0 1 0
    (merge_state source (Some next) width (advance FromRight cursor) false false) state.
Proof.
  intros source width cursor target next state END LIVE COPY.
  assert (EMPTY : ~can_copy FromLeft cursor) by (unfold can_copy; lia).
  pose proof (silent_mark_right
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromRight cursor) false false)
    target eq_refl EMPTY LIVE) as MARK.
  replace 1 with (tail_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromRight cursor) false false))+0)
    by (rewrite MARK; reflexivity).
  replace 0 with (finish_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_state source (Some next) width (advance FromRight cursor) false false))+0)
    at 3 by (rewrite MARK; reflexivity).
  eapply TraceSilent; [|constructor].
  eapply MergeRightTail with (target:=target); try reflexivity; assumption.
Qed.

Lemma trace_run_end : forall source width cursor target state,
  left_index cursor = run_middle cursor -> right_index cursor = run_end cursor ->
  ControlTrace (merge_state source (Some target) width cursor false false) state 0 0 1
    (merge_after_run maximum
      (merge_state source (Some target) width cursor false false) target) state.
Proof.
  intros source width cursor target state EL ER.
  assert (EMPTY_L : ~can_copy FromLeft cursor) by (unfold can_copy; lia).
  assert (EMPTY_R : ~can_copy FromRight cursor) by (unfold can_copy; lia).
  pose proof (silent_mark_finish
    (merge_state source (Some target) width cursor false false)
    (merge_after_run maximum
      (merge_state source (Some target) width cursor false false) target)
    target eq_refl EMPTY_L EMPTY_R) as MARK.
  replace 0 with (tail_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_after_run maximum
      (merge_state source (Some target) width cursor false false) target))+0)
    at 2 by (rewrite MARK; reflexivity).
  replace 1 with (finish_mark (silent_mark
    (merge_state source (Some target) width cursor false false)
    (merge_after_run maximum
      (merge_state source (Some target) width cursor false false) target))+0)
    by (rewrite MARK; reflexivity).
  eapply TraceSilent; [|constructor].
  eapply MergeEndsRun with (target:=target); try reflexivity; assumption.
Qed.

Theorem native_run_constructs_counted_control :
  forall source count cursor target state final_cursor final_target last width,
  IndexedRunExecution compare source count cursor target state final_cursor final_target last ->
  exists a t,
    ControlTrace (merge_state source (Some target) width cursor false false) state a t 0
      (merge_state source (Some final_target) width final_cursor false false) last /\
    a+t=count /\ left_index final_cursor=run_middle final_cursor /\
    right_index final_cursor=run_end final_cursor.
Proof.
  intros source count cursor target state final_cursor final_target last width RUN.
  induction RUN as [cursor target state EL ER|
    count cursor target state middle next next_state final_cursor final_target last STEP RUN IH].
  - exists 0,0. split; [constructor|auto].
  - destruct IH as [a [t [TRACE [COUNT ENDS]]]].
    destruct STEP as
      [cursor target next lhs rhs state next_state decision REQ CMP COPY|
       cursor target next state LIVE END COPY|cursor target next state END LIVE COPY].
    + exists (S a),t. split; [|split; [lia|exact ENDS]].
      eapply TraceAnswer with (target:=target) (lhs:=lhs) (rhs:=rhs)
        (ordering:=decision); try reflexivity; try eassumption.
      apply arbitrary_waiting_response_copies_its_selected_side. exact COPY.
    + exists a,(S t). split; [|split; [lia|exact ENDS]].
      eapply traces_compose with (a:=0) (t:=1) (b:=0) (c:=a) (u:=t) (d:=0);
        [eapply trace_left_tail; eassumption|exact TRACE].
    + exists a,(S t). split; [|split; [lia|exact ENDS]].
      eapply traces_compose with (a:=0) (t:=1) (b:=0) (c:=a) (u:=t) (d:=0);
        [eapply trace_right_tail; eassumption|exact TRACE].
Qed.

Lemma reset_run_count : forall source count cursor target state final_cursor next last
    start width,
  length source<=maximum -> start<length source -> 0<width ->
  length target=length source ->
  cursor=reset_cursor maximum (length source) start width ->
  IndexedRunExecution compare source count cursor target state final_cursor next last ->
  length next=length source /\ run_end final_cursor=start+count /\ 0<count.
Proof.
  intros source count cursor target state final_cursor next last start width HM HS HW LT -> RUN.
  assert (VALID : valid_cursor (length source)
    (reset_cursor maximum (length source) start width))
    by (apply reset_initializes_a_valid_empty_output_run; lia).
  pose proof (indexed_run_copies_exactly_the_native_remaining_width compare
    source count _ target state final_cursor next last RUN (length source)
    eq_refl LT VALID) as COUNT.
  destruct (indexed_run_projects_RunExecution_and_preserves_buffers compare
    source count _ target state final_cursor next last RUN (length source)
    eq_refl LT VALID) as [_ [LN [_ [END _]]]].
  destruct (positive_run_end_strictly_advances maximum (length source) start width HM HS HW)
    as [PROGRESS BOUND].
  unfold remaining in COUNT. unfold valid_cursor in VALID.
  cbn [reset_cursor left_index right_index run_middle run_start run_end output_index]
    in COUNT, VALID, END.
  repeat split; try assumption; lia.
Qed.

(** The final run boundary is deliberately left for the outer swap. Thus b
    below counts the earlier boundaries, and b+1 counts all runs in this pass. *)
Theorem native_nonempty_pass_constructs_counted_control :
  forall width source start target state final_target last,
  IndexedPassExecution compare maximum width source start target state final_target last ->
  length source<=maximum -> 0<width -> length target=length source ->
  start<length source ->
  exists final_cursor a t b,
    ControlTrace (merge_state source (Some target) width
      (reset_cursor maximum (length source) start width) false false) state a t b
      (merge_state source (Some final_target) width final_cursor false false) last /\
    run_end final_cursor=length source /\
    left_index final_cursor=run_middle final_cursor /\
    right_index final_cursor=run_end final_cursor /\
    a+t=length source-start /\ S b<=a+t /\ length final_target=length source.
Proof.
  intros width source start target state final_target last PASS.
  induction PASS as [target state|
    start target state count final_cursor next next_state final_target last LIVE RUN PASS IH];
    intros HM HW LT NONEMPTY.
  - lia.
  - destruct (reset_run_count source count _ target state final_cursor next next_state
      start width HM LIVE HW LT eq_refl RUN) as [LN [END POS]].
    destruct (native_run_constructs_counted_control source count _ target state
      final_cursor next next_state width RUN) as [a [t [TRACE [COUNT [EL ER]]]]].
    assert (BOUND : run_end final_cursor<=length source) by (destruct PASS; lia).
    destruct (Nat.lt_ge_cases (run_end final_cursor) (length source)) as [MORE|FINISHED].
    + destruct (IH HM HW LN MORE)
        as [last_cursor [c [u [d [TAIL [LAST [LL [RR [SUM [BLOCKS LEN]]]]]]]]]].
      exists last_cursor,(a+c),(t+u),(S d). split.
      * eapply traces_compose with (a:=a) (t:=t) (b:=0) (c:=c) (u:=u) (d:=1+d);
          [exact TRACE|].
        eapply traces_compose with (a:=0) (t:=0) (b:=1) (c:=c) (u:=u) (d:=d);
          [eapply trace_run_end; eassumption|].
        rewrite nonfinal_run_reset_uses_the_actual_absolute_end by exact MORE.
        exact TAIL.
      * repeat split; try assumption; lia.
    + assert (LAST : run_end final_cursor=length source) by lia.
      inversion PASS; subst; [|lia].
      exists final_cursor,a,t,0. split; [exact TRACE|].
      repeat split; try assumption; lia.
Qed.

Theorem native_outer_constructs_counted_control :
  forall passes width source scratch state output final_scratch last,
  NativeOuterExecution compare maximum passes width source scratch state output final_scratch last ->
  0<width -> length source<=maximum -> scratch_valid source scratch ->
  forall cursor,
  (width<length source -> cursor=reset_cursor maximum (length source) 0 width) ->
  exists final_width final_cursor a t b,
    ControlTrace
      (merge_state source scratch width cursor false (length source<=?width)) state a t b
      (merge_state output final_scratch final_width final_cursor false true) last /\
    a+t=passes*length source /\ b<=a+t.
Proof.
  intros passes width source scratch state output final_scratch last OUTER.
  induction OUTER as [width source scratch state DONE|
    passes width source scratch state completed next output final_scratch last LIVE PASS OUTER IH];
    intros HW HM HS cursor CURSOR.
  - exists width,cursor,0,0,0.
    rewrite (proj2 (Nat.leb_le _ _) DONE). split; [constructor|cbn; lia].
  - rewrite (CURSOR LIVE), (proj2 (Nat.leb_gt _ _) LIVE).
    destruct (native_nonempty_pass_constructs_counted_control width source 0
      (scratch_payload source scratch) state completed next PASS HM HW
      (valid_scratch_payload_has_source_width source scratch HS) ltac:(lia))
      as [last_cursor [a [t [b [TRACE [END [EL [ER [SUM [BLOCKS LEN]]]]]]]]]].
    assert (ALLOCATED : ControlTrace
      (merge_state source scratch width (reset_cursor maximum (length source) 0 width)
        false false) state a t b
      (merge_state source (Some completed) width last_cursor false false) next).
    { destruct scratch as [target|]; [exact TRACE|].
      change (ControlTrace
        (merge_state source None width (reset_cursor maximum (length source) 0 width)
          false false) state a (0+t) (0+b)
        (merge_state source (Some completed) width last_cursor false false) next).
      eapply TraceSilent with
        (source:=merge_state source None width
          (reset_cursor maximum (length source) 0 width) false false)
        (middle:=merge_state source (Some source) width
          (reset_cursor maximum (length source) 0 width) false false)
        (tail_count:=t) (block_count:=b);
        [apply MergeAllocatesScratch; reflexivity|exact TRACE]. }
    set (next_width:=saturated_double maximum width).
    set (next_cursor:=if length completed<=?next_width then cursor_after_run last_cursor
      else reset_cursor maximum (length completed) 0 next_width).
    assert (NEXT_CURSOR : next_width<length completed ->
      next_cursor=reset_cursor maximum (length completed) 0 next_width).
    { intro H. unfold next_cursor. now rewrite (proj2 (Nat.leb_gt _ _) H). }
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length source) width HM HW LIVE) as [GROW _].
    assert (NEXT_VALID : scratch_valid completed (Some source))
      by (unfold scratch_valid; lia).
    destruct (IH ltac:(unfold next_width in *; lia) ltac:(lia)
      NEXT_VALID next_cursor NEXT_CURSOR)
      as [final_width [final_cursor [c [u [d [TAIL [TOTAL REST]]]]]]].
    exists final_width,final_cursor,(a+c),(t+u),(b+S d). split.
    + eapply traces_compose with (a:=a) (t:=t) (b:=b) (c:=c) (u:=u) (d:=S d);
        [exact ALLOCATED|].
      eapply traces_compose with (a:=0) (t:=0) (b:=1) (c:=c) (u:=u) (d:=d);
        [eapply trace_run_end; eassumption|].
      unfold merge_after_run. cbn [merge_state merge_source merge_cursor merge_width].
      rewrite END, Nat.ltb_irrefl. fold next_width.
      fold next_width in TAIL. unfold next_cursor in TAIL.
      destruct (length completed<=?next_width); exact TAIL.
    + rewrite LEN in TOTAL. cbn [Nat.mul] in *. split; nia.
Qed.

Theorem initial_sort_inventory_is_source_bounded :
  forall passes source state output final_scratch last,
  length source<=maximum ->
  NativeOuterExecution compare maximum passes 1 source None state output final_scratch last ->
  exists final_width final_cursor a t b,
    ControlTrace (initial_merge maximum source) state a t b
      (merge_state output final_scratch final_width final_cursor false true) last /\
    a+t<=length source*(length source-1) /\ b<=a+t.
Proof.
  intros passes source state output final_scratch last HM OUTER.
  destruct (native_outer_constructs_counted_control passes 1 source None state output
    final_scratch last OUTER ltac:(lia) HM I
    (reset_cursor maximum (length source) 0 1) ltac:(intros; reflexivity))
    as [width [cursor [a [t [b [TRACE [COUNT BLOCKS]]]]]]].
  destruct (actual_buffer_lifecycle_projects_to_the_existing_outer_trace compare
    maximum passes 1 source None state output final_scratch last OUTER ltac:(lia) HM I)
    as [PROJECTED _].
  pose proof (MergeSortPdaOuter.MergeSortPdaOuter.source_outer_progress_bounds_the_number_of_passes
    compare maximum passes 1 source state output last PROJECTED ltac:(lia) HM) as PASSES.
  exists width,cursor,a,t,b. split.
  - unfold initial_merge. replace (length source<?2) with (length source<=?1).
    + exact TRACE.
    + destruct (length source) as [|[|n]]; reflexivity.
  - split; [nia|exact BLOCKS].
Qed.
Inductive Handshakes : @RawMergeState Entry -> State -> nat -> nat -> nat -> nat ->
    @RawMergeState Entry -> State -> Prop :=
| HandshakeDone : forall source final state kind word
    (STEP : RawMergeStep maximum source MergeCompletes final),
    raw_step_word maximum kind source MergeCompletes final STEP word ->
    Handshakes source state 1 0 (tails word) (finishes word) final state
| HandshakeAnswer : forall source waiting lhs rhs ordering middle final state next last
    kind word calls a t b
    (STEP : RawMergeStep maximum source (MergeRequests lhs rhs) waiting),
    raw_step_word maximum kind source (MergeRequests lhs rhs) waiting STEP word ->
    compare lhs rhs state=(Some ordering,next) ->
    raw_merge_accept waiting ordering=Some middle ->
    Handshakes middle next calls a t b final last ->
    Handshakes source state (S calls) (S a) (tails word+t) (finishes word+b) final last.

Lemma silent_prefix_prepends_to_the_first_actual_invocation :
  forall source middle final state last calls a t b,
  RawMergeSilent maximum source middle ->
  Handshakes middle state calls a t b final last ->
  Handshakes source state calls a
    (tail_mark (silent_mark source middle)+t)
    (finish_mark (silent_mark source middle)+b) final last.
Proof.
  intros source middle final state last calls a t b SILENT REST.
  destruct REST as [middle final state kind word STEP WORD|
    middle waiting lhs rhs ordering after final state next last kind word calls a t b
    STEP WORD CMP ACCEPT REST].
  - change (Handshakes source state 1 0
      (tails (silent_mark source middle::word))
      (finishes (silent_mark source middle::word)) final state).
    eapply HandshakeDone with (STEP := MergeStepInternal maximum source middle
      MergeCompletes final SILENT STEP).
    eapply raw_step_word_internal. exact WORD.
  - replace (tail_mark (silent_mark source middle)+(tails word+t))
      with (tails (silent_mark source middle::word)+t) by (cbn; lia).
    replace (finish_mark (silent_mark source middle)+(finishes word+b))
      with (finishes (silent_mark source middle::word)+b) by (cbn; lia).
    eapply HandshakeAnswer with (STEP := MergeStepInternal maximum source middle
      (MergeRequests lhs rhs) waiting SILENT STEP); try eassumption.
    eapply raw_step_word_internal. exact WORD.
Qed.

Theorem completed_control_trace_constructs_actual_invocations :
  forall source state a t b final last,
  ControlTrace source state a t b final last ->
  merge_waiting final=false -> merge_done final=true ->
  Handshakes source state (S a) a t b final last.
Proof.
  intros source state a t b final last TRACE.
  induction TRACE as [source state|
    source middle final state last accepted tail_count block_count SILENT TRACE IH|
    source target lhs rhs state next_state ordering middle final last accepted
    tail_count block_count READY NOTDONE TARGET REQUEST CMP ACCEPT TRACE IH];
    intros WAIT DONE.
  - change (Handshakes source state 1 0 (tails []) (finishes []) source state).
    eapply HandshakeDone with (STEP := MergeStepDone maximum source WAIT DONE).
    apply raw_step_word_done.
  - eapply silent_prefix_prepends_to_the_first_actual_invocation;
      [eassumption|now apply IH].
  - change (Handshakes source state (S (S accepted)) (S accepted)
      (tails []+tail_count) (finishes []+block_count) final last).
    eapply HandshakeAnswer with (STEP:=MergeStepRequests maximum source target lhs rhs
      READY NOTDONE TARGET REQUEST); try eassumption.
    + apply raw_step_word_requests.
    + now apply IH.
Qed.
End GenericControl.

Lemma mark_sums_append : forall first second,
  tails (first++second)=tails first+tails second /\
  finishes (first++second)=finishes first+finishes second.
Proof.
  induction first as [|mark rest IH]; intro second; [split; reflexivity|].
  destruct (IH second) as [T F].
  change (tail_mark mark+tails (rest++second)=tail_mark mark+tails rest+tails second /\
    finish_mark mark+finishes (rest++second)=finish_mark mark+finishes rest+finishes second).
  rewrite T,F; split; lia.
Qed.

Lemma repeated_mark_sums : forall count mark,
  tails (repeat mark count)=count*tail_mark mark /\
  finishes (repeat mark count)=count*finish_mark mark.
Proof.
  induction count as [|count IH]; intro mark; [split; reflexivity|].
  destruct (IH mark) as [T F].
  change (tail_mark mark+tails (repeat mark count)=S count*tail_mark mark /\
    finish_mark mark+finishes (repeat mark count)=S count*finish_mark mark).
  rewrite T,F; split; lia.
Qed.

Lemma block_word_counts_are_exact : forall blocks,
  tails (blocks_marks blocks)=total_tails blocks /\
  finishes (blocks_marks blocks)=length blocks.
Proof.
  induction blocks as [|[l r p s] rest [T F]]; [split; reflexivity|].
  unfold blocks_marks in *. cbn [flat_map].
  destruct (mark_sums_append (block_marks {|block_left:=l;block_right:=r;
    block_pass:=p;block_reset:=s|}) (flat_map block_marks rest)) as [A B].
  rewrite A,B,T,F. unfold block_marks.
  cbn [block_left block_right block_pass block_reset].
  destruct (mark_sums_append (repeat LeftMark l)
    (repeat RightMark r++[FinishMark p s])) as [C D].
  destruct (mark_sums_append (repeat RightMark r) [FinishMark p s]) as [E FF].
  destruct (repeated_mark_sums l LeftMark) as [G H].
  destruct (repeated_mark_sums r RightMark) as [I J].
  rewrite C,D,E,FF,G,H,I,J.
  cbn [tails finishes fold_right tail_mark finish_mark total_tails block_left block_right length].
  split; lia.
Qed.

Lemma grouped_word_counts_are_exact : forall Entry (state : @RawMergeState Entry)
    word scratch blocks,
  grouped_word state word scratch blocks ->
  tails word=total_tails blocks /\ finishes word=length blocks.
Proof.
  intros Entry state word scratch blocks [WORD _]. rewrite WORD.
  pose proof (block_word_counts_are_exact blocks) as [T F].
  destruct scratch; cbn [app tails finishes fold_right tail_mark finish_mark] in *;
    split; assumption.
Qed.

Lemma raw_silent_successor_is_determined :
  forall Entry maximum (source first second : @RawMergeState Entry),
  RawMergeSilent maximum source first -> RawMergeSilent maximum source second -> first=second.
Proof.
  intros Entry maximum source first second FIRST SECOND.
  destruct FIRST; inversion SECOND; subst; try reflexivity; intuition congruence.
Qed.

Lemma silent_source_is_not_done : forall Entry maximum (source next : @RawMergeState Entry),
  RawMergeSilent maximum source next -> merge_done source=false.
Proof. intros Entry maximum source next STEP; destruct STEP; assumption. Qed.

Lemma silent_source_cannot_request : forall Entry maximum (source next : @RawMergeState Entry)
    target lhs rhs,
  RawMergeSilent maximum source next -> merge_target source=Some target ->
  NativeRequest (merge_source source) (merge_cursor source) lhs rhs -> False.
Proof.
  intros Entry maximum source next target lhs rhs STEP TARGET [LEFT [RIGHT REST]].
  destruct STEP; intuition congruence.
Qed.

(** Word uniqueness follows from executable source guards, not equality of
    proof objects. Both comparison-ready and done returns exclude every
    silent branch; every remaining silent successor is uniquely determined. *)
Lemma raw_word_exposes_its_original_head :
  forall Entry maximum state reply next (STEP : @RawMergeStep Entry maximum state reply next)
    kind word,
  raw_step_word maximum kind state reply next STEP word ->
  (reply=MergeCompletes /\ next=state /\ word=[] /\ merge_done state=true) \/
  (exists target lhs rhs, reply=MergeRequests lhs rhs /\
    next=merge_set_waiting state true /\ word=[] /\ merge_done state=false /\
    merge_target state=Some target /\
    NativeRequest (merge_source state) (merge_cursor state) lhs rhs) \/
  (exists middle suffix child_kind
    (REST : RawMergeStep maximum middle reply next),
    RawMergeSilent maximum state middle /\
    word=silent_mark state middle::suffix /\
    raw_step_word maximum child_kind middle reply next REST suffix).
Proof.
  intros Entry maximum state reply next STEP kind word WORD.
  destruct WORD as [state WAIT DONE|
    state target lhs rhs WAIT DONE TARGET REQUEST|
    state middle reply next kind suffix SILENT REST WORD].
  - left; repeat split; assumption.
  - right; left; exists target,lhs,rhs.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact DONE|]. split; [exact TARGET|exact REQUEST].
  - right; right; exists middle,suffix,kind,REST.
    split; [exact SILENT|]. split; [reflexivity|exact WORD].
Qed.

Lemma raw_invocation_is_determined_by_its_source :
  forall Entry maximum state reply next (STEP : @RawMergeStep Entry maximum state reply next)
    kind word,
  raw_step_word maximum kind state reply next STEP word ->
  forall reply' next' (STEP' : RawMergeStep maximum state reply' next') kind' word',
  raw_step_word maximum kind' state reply' next' STEP' word' ->
  reply=reply' /\ next=next' /\ word=word'.
Proof.
  intros Entry maximum state reply next STEP kind word FIRST.
  induction FIRST as [state WAIT DONE|
    state target lhs rhs WAIT DONE TARGET REQUEST|
    state middle reply next kind suffix SILENT REST WORD IH];
    intros reply' next' STEP' kind' word' SECOND;
    pose proof (raw_word_exposes_its_original_head Entry maximum state reply' next'
      STEP' kind' word' SECOND) as VIEW.
  all: destruct VIEW as [DONEVIEW|[READYVIEW|SILENTVIEW]].
  all: try destruct DONEVIEW as [REPLY [NEXT [WORDS DONE']]].
  all: try destruct READYVIEW as
    [target' [lhs' [rhs' [REPLY [NEXT [WORDS [DONE' [TARGET' REQUEST']]]]]]]].
  all: try destruct SILENTVIEW as
    [middle' [suffix' [child_kind [CHILD_STEP [SILENT' [WORDS CHILD]]]]]].
  all: try subst reply'; try subst next'; subst word'.
  - repeat split; reflexivity.
  - congruence.
  - pose proof (silent_source_is_not_done _ _ _ _ SILENT'); congruence.
  - congruence.
  - unfold NativeRequest in REQUEST,REQUEST'.
    assert (lhs=lhs' /\ rhs=rhs') as [LEFT RIGHT] by (intuition congruence).
    subst lhs' rhs'; repeat split; reflexivity.
  - exfalso; eapply silent_source_cannot_request; eassumption.
  - pose proof (silent_source_is_not_done _ _ _ _ SILENT); congruence.
  - exfalso; eapply silent_source_cannot_request; eassumption.
  - assert (MIDDLE : middle=middle') by
      (eapply raw_silent_successor_is_determined; eassumption).
    subst middle'.
    destruct (IH _ _ _ _ _ CHILD) as [REPLY [NEXT WORDS]].
    repeat split; congruence.
Qed.

Lemma raw_invocation_step_is_determined_by_its_source :
  forall Entry maximum source reply next (STEP : @RawMergeStep Entry maximum source reply next)
    reply' next',
  RawMergeStep maximum source reply' next' -> reply=reply' /\ next=next'.
Proof.
  intros Entry maximum source reply next STEP reply' next' OTHER.
  destruct (every_actual_raw_step_has_its_word maximum source reply next STEP)
    as [kind [word WORD]].
  destruct (every_actual_raw_step_has_its_word maximum source reply' next' OTHER)
    as [kind' [word' WORD']].
  destruct (raw_invocation_is_determined_by_its_source Entry maximum source reply next
    STEP kind word WORD reply' next' OTHER kind' word' WORD') as [REPLY [NEXT _]].
  now split.
Qed.

Lemma words_of_the_same_step_have_the_same_counts :
  forall Entry maximum state reply next (STEP : @RawMergeStep Entry maximum state reply next)
    kind word kind' word',
  raw_step_word maximum kind state reply next STEP word ->
  raw_step_word maximum kind' state reply next STEP word' ->
  tails word=tails word' /\ finishes word=finishes word'.
Proof.
  intros Entry maximum state reply next STEP kind word kind' word' FIRST SECOND.
  destruct (raw_invocation_is_determined_by_its_source Entry maximum state reply next
    STEP kind word FIRST reply next STEP kind' word' SECOND) as [_ [_ SAME]].
  now rewrite SAME.
Qed.

Lemma every_counted_invocation_has_source_derived_work :
  forall Entry maximum state reply next (STEP : @RawMergeStep Entry maximum state reply next)
    kind word,
  raw_step_word maximum kind state reply next STEP word ->
  exists blocks,
    groups_work (invocation_groups reply blocks)<=
      5+7*finishes word+2*tails word /\
    exists other_kind other_word scratch,
      raw_step_word maximum other_kind state reply next STEP other_word /\
      grouped_word state other_word scratch blocks.
Proof.
  intros Entry maximum state reply next STEP kind word WORD.
  destruct (actual_raw_step_derives_completed_run_grouping maximum state reply next STEP)
    as [other_kind [other_word [scratch [blocks [OTHER GROUP]]]]].
  destruct (words_of_the_same_step_have_the_same_counts Entry maximum state reply next
    STEP kind word other_kind other_word WORD OTHER) as [T F].
  destruct (grouped_word_counts_are_exact Entry state other_word scratch blocks GROUP)
    as [TG FG].
  exists blocks. split.
  - pose proof (grouped_invocation_control_is_covered_by_its_actual_paid_markers
      Entry reply blocks) as [BOUND _]. rewrite T,F,TG,FG. exact BOUND.
  - exists other_kind,other_word,scratch. now split.
Qed.

Print Assumptions initial_sort_inventory_is_source_bounded.
Print Assumptions completed_control_trace_constructs_actual_invocations.
Print Assumptions words_of_the_same_step_have_the_same_counts.
Print Assumptions every_counted_invocation_has_source_derived_work.

Section Aggregate.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.
Variable maximum : nat.

(** The work witness exposes the actual source group list for every complete
    invocation. It does not take an allowance or an arbitrary cost callback. *)
Inductive SourceWork : @RawMergeState Entry -> State -> @RawMergeState Entry -> State -> nat -> Prop :=
| WorkDone : forall source final state kind word scratch blocks
    (STEP : RawMergeStep maximum source MergeCompletes final),
    raw_step_word maximum kind source MergeCompletes final STEP word ->
    grouped_word source word scratch blocks ->
    SourceWork source state final state (groups_work (@invocation_groups Entry MergeCompletes blocks))
| WorkAnswer : forall source waiting lhs rhs ordering middle final state next last
    kind word scratch blocks rest
    (STEP : RawMergeStep maximum source (MergeRequests lhs rhs) waiting),
    raw_step_word maximum kind source (MergeRequests lhs rhs) waiting STEP word ->
    grouped_word source word scratch blocks ->
    compare lhs rhs state=(Some ordering,next) ->
    raw_merge_accept waiting ordering=Some middle ->
    SourceWork middle next final last rest ->
    SourceWork source state final last
      (groups_work (invocation_groups (MergeRequests lhs rhs) blocks)+rest).

Theorem counted_handshakes_derive_their_source_work :
  forall source state calls a t b final last,
  Handshakes compare maximum source state calls a t b final last ->
  exists work, SourceWork source state final last work /\ work<=5*calls+7*b+2*t.
Proof.
  intros source state calls a t b final last HANDSHAKES.
  induction HANDSHAKES as
    [source final state kind word STEP WORD|
     source waiting lhs rhs ordering middle final state next last kind word calls a t b
     STEP WORD CMP ACCEPT REST IH].
  - destruct (every_counted_invocation_has_source_derived_work Entry maximum source
      MergeCompletes final STEP kind word WORD)
      as [blocks [BOUND [other_kind [other_word [scratch [OTHER GROUP]]]]]].
    exists (groups_work (@invocation_groups Entry MergeCompletes blocks)).
    split; [eapply WorkDone; eassumption|lia].
  - destruct (every_counted_invocation_has_source_derived_work Entry maximum source
      (MergeRequests lhs rhs) waiting STEP kind word WORD)
      as [blocks [BOUND [other_kind [other_word [scratch [OTHER GROUP]]]]]].
    destruct IH as [work [WORK BUDGET]].
    exists (groups_work (invocation_groups (MergeRequests lhs rhs) blocks)+work).
    split; [eapply WorkAnswer; eassumption|lia].
Qed.

Theorem completed_native_sort_has_source_derived_finite_core_work :
  forall passes source state output final_scratch last,
  length source<=maximum ->
  NativeOuterExecution compare maximum passes 1 source None state output final_scratch last ->
  exists width cursor a t b work,
    Handshakes compare maximum (initial_merge maximum source) state (S a) a t b
      (merge_state output final_scratch width cursor false true) last /\
    SourceWork (initial_merge maximum source) state
      (merge_state output final_scratch width cursor false true) last work /\
    a+t<=length source*(length source-1) /\ b<=a+t /\
    work<=5*(S a)+7*b+2*t /\
    work<=12*(length source*(length source-1))+5.
Proof.
  intros passes source state output final_scratch last HM SORT.
  destruct (initial_sort_inventory_is_source_bounded compare maximum passes source state
    output final_scratch last HM SORT)
    as [width [cursor [a [t [b [TRACE [COPIES BLOCKS]]]]]]].
  pose proof (completed_control_trace_constructs_actual_invocations compare maximum
    _ _ _ _ _ _ _ TRACE eq_refl eq_refl) as STEPS.
  destruct (counted_handshakes_derive_their_source_work _ _ _ _ _ _ _ _ STEPS)
    as [work [WORK BOUND]].
  exists width,cursor,a,t,b,work. repeat split; try assumption; nia.
Qed.
End Aggregate.

Print Assumptions counted_handshakes_derive_their_source_work.
Print Assumptions completed_native_sort_has_source_derived_finite_core_work.

Section ItemRoute.
Context {Key Payload Secondary : Type}.
Variable payload_secondary : Payload -> option Secondary.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Local Notation Entry := (Key*Payload)%type.
Local Notation Answer := ((@RawRequest Key Secondary)*comparison)%type.

(** These words annotate the existing request_item_comparison,
    request_secondary_or_accept, and accept_term_comparison branches.
    ResumeEntry denotes the actual later resume for each external answer.
    The terminal AcceptItem group is included here; its destination-specific
    merge copy or equal-run advance is accounted by its enclosing phase.
    Response values and directed operands remain in the original answers. *)
Inductive SecondaryRoute (lhs rhs : Entry) : list ControlGroup -> list Answer -> comparison -> Prop :=
| SelectedSecondary : forall ordering,
    select_secondary secondary_alias (payload_secondary (snd lhs))
      (payload_secondary (snd rhs))=SecondaryAccept ordering ->
    SecondaryRoute lhs rhs [RequestSecondary;AcceptItem] [] ordering
| AnsweredSecondary : forall left right ordering,
    select_secondary secondary_alias (payload_secondary (snd lhs))
      (payload_secondary (snd rhs))=SecondaryCompare left right ->
    SecondaryRoute lhs rhs [RequestSecondary;ResumeEntry;AcceptTerm;AcceptItem]
      [(SecondaryRequest left right,ordering)] ordering.

Inductive ItemRoute (lhs rhs : Entry) : list ControlGroup -> list Answer -> comparison -> Prop :=
| AliasedPrimary : forall word answers ordering,
    key_alias (fst lhs) (fst rhs)=true -> SecondaryRoute lhs rhs word answers ordering ->
    ItemRoute lhs rhs (RequestPrimary::word) answers ordering
| DecisivePrimary : forall ordering,
    key_alias (fst lhs) (fst rhs)=false -> ordering<>Eq ->
    ItemRoute lhs rhs [RequestPrimary;ResumeEntry;AcceptTerm;AcceptItem]
      [(PrimaryRequest (fst lhs) (fst rhs),ordering)] ordering
| EqualPrimary : forall word answers ordering,
    key_alias (fst lhs) (fst rhs)=false -> SecondaryRoute lhs rhs word answers ordering ->
    ItemRoute lhs rhs ([RequestPrimary;ResumeEntry;AcceptTerm]++word)
      ((PrimaryRequest (fst lhs) (fst rhs),Eq)::answers) ordering.

Lemma secondary_route_uses_at_most_one_original_response : forall lhs rhs word answers ordering,
  SecondaryRoute lhs rhs word answers ordering ->
  length answers<=1 /\ groups_work word=2+2*length answers.
Proof.
  intros lhs rhs word answers ordering ROUTE; destruct ROUTE;
    cbn [groups_work fold_right control_work length]; split; lia.
Qed.

Theorem item_route_work_is_bounded_by_source_cases : forall lhs rhs word answers ordering,
  ItemRoute lhs rhs word answers ordering ->
  length answers<=2 /\ groups_work word<=3+2*length answers /\ groups_work word<=7.
Proof.
  intros lhs rhs word answers ordering ROUTE.
  destruct ROUTE as [word answers ordering ALIAS SECONDARY|
    ordering FRESH DECISIVE|word answers ordering FRESH SECONDARY].
  - destruct (secondary_route_uses_at_most_one_original_response _ _ _ _ _ SECONDARY)
      as [COUNT WORK].
    change (length answers<=2 /\ 1+groups_work word<=3+2*length answers /\
      1+groups_work word<=7). repeat split; lia.
  - cbn [groups_work fold_right control_work length]. repeat split; lia.
  - destruct (secondary_route_uses_at_most_one_original_response _ _ _ _ _ SECONDARY)
      as [COUNT WORK].
    change (S (length answers)<=2 /\ 3+groups_work word<=3+2*S (length answers) /\
      3+groups_work word<=7). repeat split; lia.
Qed.

(** A count bound never replaces this operand projection: a primary answer
    names the original primary fields, and a secondary answer names the two
    operands selected from those same original payloads. *)
Theorem item_route_answers_retain_original_operands : forall lhs rhs word answers ordering,
  ItemRoute lhs rhs word answers ordering -> forall request answer,
  In (request,answer) answers ->
  request=PrimaryRequest (fst lhs) (fst rhs) \/
  exists left right,
    select_secondary secondary_alias (payload_secondary (snd lhs))
      (payload_secondary (snd rhs))=SecondaryCompare left right /\
    request=SecondaryRequest left right.
Proof.
  intros lhs rhs word answers ordering ROUTE.
  destruct ROUTE as [word answers ordering ALIAS SECONDARY|
    ordering FRESH DECISIVE|word answers ordering FRESH SECONDARY];
    intros request answer MEMBER.
  - destruct SECONDARY; cbn in MEMBER; [contradiction|].
    destruct MEMBER as [SAME|[]]. inversion SAME; subst. right; eauto.
  - cbn in MEMBER. destruct MEMBER as [SAME|[]]. inversion SAME; subst. now left.
  - cbn in MEMBER. destruct MEMBER as [SAME|MEMBER].
    + inversion SAME; subst. now left.
    + destruct SECONDARY; cbn in MEMBER; [contradiction|].
      destruct MEMBER as [SAME|[]]. inversion SAME; subst. right; eauto.
Qed.

Variable payload_repetitions : Payload -> nat.
Variable maximum : nat.
Local Notation Path := (@RawPayloadCorePath Key Payload Secondary
  payload_secondary payload_repetitions key_alias secondary_alias maximum).
Local Notation Dialogue := (@RawPayloadDialogue Key Payload Secondary
  payload_secondary payload_repetitions key_alias secondary_alias maximum).

Lemma prepend_existing_payload_path : forall first state middle parked answers last next,
  Path first state middle parked -> Dialogue middle parked answers last next ->
  Dialogue first state answers last next.
Proof.
  intros first state middle parked answers last next PATH DIALOGUE.
  destruct DIALOGUE.
  - apply DialogueQuiet. eapply raw_payload_core_paths_compose; eassumption.
  - eapply DialogueAnswer; [|eassumption].
    eapply raw_payload_core_paths_compose; eassumption.
Qed.

Lemma secondary_word_constructs_existing_source_dialogue :
  forall lhs rhs word answers ordering destination state,
  SecondaryRoute lhs rhs word answers ordering -> map_pending state=None ->
  Dialogue (G.RequestSecondary destination lhs rhs) state answers
    (G.AcceptItem destination ordering) state.
Proof.
  intros lhs rhs word answers ordering destination state ROUTE NONE.
  destruct ROUTE as [ordering SELECT|left right ordering SELECT].
  - apply DialogueQuiet. eapply CorePathMore;
      [eapply RequestSelectedSecondary; exact SELECT|constructor].
  - pose proof (clearing_the_just_created_pending_restores_the_payload state
      (PendingSecondary destination) NONE) as RESTORE.
    eapply DialogueAnswer with
      (request:=SecondaryRequest left right)
      (parked:=set_pending state (Some (PendingSecondary destination)))
      (ordering:=ordering).
    + eapply CorePathMore; [eapply RequestComparedSecondary; exact SELECT|constructor].
    + apply DialogueQuiet. eapply CorePathMore.
      * apply IngressSecondary; reflexivity.
      * rewrite RESTORE; constructor.
Qed.

Theorem item_word_constructs_existing_source_dialogue :
  forall lhs rhs word answers ordering destination state,
  ItemRoute lhs rhs word answers ordering -> map_pending state=None ->
  Dialogue (G.RequestItem destination lhs rhs) state answers
    (G.AcceptItem destination ordering) state.
Proof.
  intros lhs rhs word answers ordering destination state ROUTE NONE.
  destruct ROUTE as [word answers ordering ALIAS SECONDARY|
    ordering FRESH DECISIVE|word answers ordering FRESH SECONDARY].
  - eapply prepend_existing_payload_path.
    + eapply CorePathMore; [apply RequestAliasedPrimary; exact ALIAS|constructor].
    + eapply secondary_word_constructs_existing_source_dialogue; eassumption.
  - pose proof (clearing_the_just_created_pending_restores_the_payload state
      (PendingPrimary lhs rhs destination) NONE) as RESTORE.
    eapply DialogueAnswer with
      (request:=PrimaryRequest (fst lhs) (fst rhs))
      (parked:=set_pending state (Some (PendingPrimary lhs rhs destination)))
      (ordering:=ordering).
    + eapply CorePathMore; [apply RequestFreshPrimary; exact FRESH|constructor].
    + apply DialogueQuiet. eapply CorePathMore.
      * eapply IngressPrimaryDecisive; [reflexivity|exact DECISIVE].
      * rewrite RESTORE; constructor.
  - pose proof (clearing_the_just_created_pending_restores_the_payload state
      (PendingPrimary lhs rhs destination) NONE) as RESTORE.
    eapply DialogueAnswer with
      (request:=PrimaryRequest (fst lhs) (fst rhs))
      (parked:=set_pending state (Some (PendingPrimary lhs rhs destination)))
      (ordering:=Eq).
    + eapply CorePathMore; [apply RequestFreshPrimary; exact FRESH|constructor].
    + eapply prepend_existing_payload_path.
      * eapply CorePathMore.
        -- apply IngressPrimaryEqual; reflexivity.
        -- rewrite RESTORE; constructor.
      * eapply secondary_word_constructs_existing_source_dialogue; eassumption.
Qed.
End ItemRoute.

Print Assumptions item_route_work_is_bounded_by_source_cases.
Print Assumptions item_route_answers_retain_original_operands.
Print Assumptions item_word_constructs_existing_source_dialogue.

Section SortPhaseWord.
Context {Key Payload Secondary State : Type}.
Variable payload_secondary : Payload -> option Secondary.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Local Notation Entry := (Key*Payload)%type.
Variable compare : Entry -> Entry -> State -> option comparison * State.
Variable maximum : nat.
Local Notation Route := (@ItemRoute Key Payload Secondary
  payload_secondary key_alias secondary_alias).
Local Notation H := (@Handshakes Entry State compare maximum).

(** The phase word decorates the SAME handshake derivation. It therefore
    cannot attach a cheaper unrelated trace to the source request inventory.
    Scratch storage itself is separate; ReleaseScratch here is its one
    named control group. Each item word has the source dialogue proved above. *)
Inductive SourceSortPhaseWord : forall source state calls a t b final last,
    H source state calls a t b final last -> list ControlGroup -> Prop :=
| SortWordDone : forall source final state kind word scratch blocks
    (STEP : RawMergeStep maximum source MergeCompletes final)
    (WORD : raw_step_word maximum kind source MergeCompletes final STEP word),
    grouped_word source word scratch blocks ->
    SourceSortPhaseWord source state 1 0 (tails word) (finishes word) final state
      (HandshakeDone compare maximum source final state kind word STEP WORD)
      ([PhaseAttempt]++@invocation_groups Entry MergeCompletes blocks++[SortReturn;ReleaseScratch])
| SortWordAnswer : forall source waiting lhs rhs ordering middle final state next last
    kind word scratch blocks calls a t b pair_word answers rest_word
    (STEP : RawMergeStep maximum source (MergeRequests lhs rhs) waiting)
    (WORD : raw_step_word maximum kind source (MergeRequests lhs rhs) waiting STEP word)
    (CMP : compare lhs rhs state=(Some ordering,next))
    (ACCEPT : raw_merge_accept waiting ordering=Some middle)
    (REST : H middle next calls a t b final last),
    grouped_word source word scratch blocks ->
    Route lhs rhs pair_word answers ordering ->
    SourceSortPhaseWord middle next calls a t b final last REST rest_word ->
    SourceSortPhaseWord source state (S calls) (S a)
      (tails word+t) (finishes word+b) final last
      (HandshakeAnswer compare maximum source waiting lhs rhs ordering middle final state next last
        kind word calls a t b STEP WORD CMP ACCEPT REST)
      ([PhaseAttempt]++invocation_groups (MergeRequests lhs rhs) blocks++[SortReturn]++
        pair_word++[MergeAcceptRoute;MergeAcceptCopy]++rest_word).

Theorem sort_phase_word_derives_its_control_multiplicities :
  forall source state calls a t b final last (TRACE : H source state calls a t b final last) word,
  SourceSortPhaseWord source state calls a t b final last TRACE word ->
  groups_work word<=5*calls+7*b+2*t+11*a+3.
Proof.
  intros source state calls a t b final last TRACE word PHASE.
  induction PHASE as [source final state kind word scratch blocks STEP WORD GROUP|
    source waiting lhs rhs ordering middle final state next last kind word scratch blocks
    calls a t b pair_word answers rest_word STEP WORD CMP ACCEPT REST GROUP ROUTE PHASE IH].
  - destruct (grouped_word_counts_are_exact Entry source word scratch blocks GROUP)
      as [TAILS BLOCKS].
    pose proof (grouped_invocation_control_is_covered_by_its_actual_paid_markers
      Entry MergeCompletes blocks) as [BOUND _].
    rewrite !groups_work_append.
    change (1+groups_work (@invocation_groups Entry MergeCompletes blocks)+2<=
      5*1+7*finishes word+2*tails word+11*0+3).
    rewrite TAILS,BLOCKS; lia.
  - destruct (grouped_word_counts_are_exact Entry source word scratch blocks GROUP)
      as [TAILS BLOCKS].
    pose proof (grouped_invocation_control_is_covered_by_its_actual_paid_markers
      Entry (MergeRequests lhs rhs) blocks) as [BOUND _].
    destruct (item_route_work_is_bounded_by_source_cases payload_secondary key_alias secondary_alias
      lhs rhs pair_word answers ordering ROUTE) as [_ [_ PAIR]].
    rewrite !groups_work_append.
    change (1+groups_work (invocation_groups (MergeRequests lhs rhs) blocks)+
      (1+(groups_work pair_word+(2+groups_work rest_word)))<=
      5*S calls+7*(finishes word+b)+2*(tails word+t)+11*S a+3).
    rewrite TAILS,BLOCKS; lia.
Qed.

Theorem original_native_sort_supplies_the_phase_word_envelope :
  forall passes source state output final_scratch last,
  length source<=maximum ->
  NativeOuterExecution compare maximum passes 1 source None state output final_scratch last ->
  exists width cursor a t b
    (TRACE : H (initial_merge maximum source) state (S a) a t b
      (merge_state output final_scratch width cursor false true) last),
    forall word,
    SourceSortPhaseWord _ _ _ _ _ _ _ _ TRACE word ->
    groups_work word<=23*(length source*(length source-1))+8.
Proof.
  intros passes source state output final_scratch last HM SORT.
  destruct (initial_sort_inventory_is_source_bounded compare maximum passes source state
    output final_scratch last HM SORT)
    as [width [cursor [a [t [b [TRACE [COPIES BLOCKS]]]]]]].
  pose proof (completed_control_trace_constructs_actual_invocations compare maximum
    _ _ _ _ _ _ _ TRACE eq_refl eq_refl) as HANDSHAKES.
  exists width,cursor,a,t,b,HANDSHAKES. intros word WORD.
  pose proof (sort_phase_word_derives_its_control_multiplicities
    _ _ _ _ _ _ _ _ HANDSHAKES word WORD) as BOUND. nia.
Qed.
End SortPhaseWord.

Print Assumptions sort_phase_word_derives_its_control_multiplicities.
Print Assumptions original_native_sort_supplies_the_phase_word_envelope.

Section LexPhaseWord.
Context {Key Payload Secondary : Type}.
Variable payload_secondary : Payload -> option Secondary.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Local Notation Entry := (Key*Payload)%type.
Variable compare : Entry -> Entry -> comparison.
Local Notation Route := (@ItemRoute Key Payload Secondary
  payload_secondary key_alias secondary_alias).

(** Normal lexicographic completion uses the original exhausted-side checks
    or the original decisive response. An Equal branch advances only under
    the existing LexRequests equality premise and positive-count profile. *)
Inductive SourceLexWord (left right : list (Entry*nat)) :
    forall cursor requests, N.LexRequests compare left right cursor requests ->
    list ControlGroup -> Prop :=
| LexWordLeftExhausted : forall cursor,
    nth_error left (L.lex_left_index cursor)=None ->
    SourceLexWord left right cursor [] (N.PrefixStop compare left right cursor)
      [PhaseAttempt;CurrentLeft;ExhaustedTotalCmp]
| LexWordRightExhausted : forall cursor lhs count,
    nth_error left (L.lex_left_index cursor)=Some (lhs,count) ->
    nth_error right (L.lex_right_index cursor)=None ->
    SourceLexWord left right cursor [] (N.PrefixStop compare left right cursor)
      [PhaseAttempt;CurrentLeft;CurrentRight;ExhaustedTotalCmp]
| LexWordDecisive : forall cursor lhs lc rhs rc pair_word answers
    (LEFT : nth_error left (L.lex_left_index cursor)=Some (lhs,lc))
    (RIGHT : nth_error right (L.lex_right_index cursor)=Some (rhs,rc))
    (LC : 0<lc) (RC : 0<rc) (DECISIVE : compare lhs rhs<>Eq),
    Route lhs rhs pair_word answers (compare lhs rhs) ->
    SourceLexWord left right cursor [(lhs,rhs)]
      (N.Decisive compare left right cursor lhs lc rhs rc LEFT RIGHT LC RC DECISIVE)
      ([PhaseAttempt;CurrentLeft;CurrentRight]++pair_word++[PhaseAttempt])
| LexWordEqual : forall cursor lhs lc rhs rc requests pair_word answers rest_word
    (LEFT : nth_error left (L.lex_left_index cursor)=Some (lhs,lc))
    (RIGHT : nth_error right (L.lex_right_index cursor)=Some (rhs,rc))
    (LC : 0<lc) (RC : 0<rc) (EQUAL : compare lhs rhs=Eq)
    (REST : N.LexRequests compare left right (N.next_equal lc rc cursor) requests),
    Route lhs rhs pair_word answers Eq ->
    SourceLexWord left right (N.next_equal lc rc cursor) requests REST rest_word ->
    SourceLexWord left right cursor ((lhs,rhs)::requests)
      (N.EqualMore compare left right cursor lhs lc rhs rc requests LEFT RIGHT LC RC EQUAL REST)
      ([PhaseAttempt;CurrentLeft;CurrentRight]++pair_word++[EqualRun]++rest_word).

Theorem lex_word_work_is_derived_from_its_actual_requests :
  forall left right cursor requests (RUN : N.LexRequests compare left right cursor requests) word,
  SourceLexWord left right cursor requests RUN word ->
  groups_work word<=11*length requests+5.
Proof.
  intros left right cursor requests RUN word WORD.
  induction WORD as [cursor EMPTY|cursor lhs count LEFT EMPTY|
    cursor lhs lc rhs rc pair_word answers LEFT RIGHT LC RC DECISIVE ROUTE|
    cursor lhs lc rhs rc requests pair_word answers rest_word LEFT RIGHT LC RC EQUAL REST ROUTE WORD IH].
  - cbn [groups_work fold_right control_work length]; lia.
  - cbn [groups_work fold_right control_work length]; lia.
  - destruct (item_route_work_is_bounded_by_source_cases payload_secondary key_alias secondary_alias
      lhs rhs pair_word answers (compare lhs rhs) ROUTE) as [_ [_ PAIR]].
    rewrite !groups_work_append.
    change (3+(groups_work pair_word+1)<=11*1+5). lia.
  - destruct (item_route_work_is_bounded_by_source_cases payload_secondary key_alias secondary_alias
      lhs rhs pair_word answers Eq ROUTE) as [_ [_ PAIR]].
    rewrite !groups_work_append.
    change (3+(groups_work pair_word+(1+groups_work rest_word))<=11*S (length requests)+5).
    lia.
Qed.

Theorem original_weighted_lex_supplies_the_word_envelope :
  forall left right requests
    (RUN : N.LexRequests compare left right (L.unit_cursor 0) requests) word,
  SourceLexWord left right (L.unit_cursor 0) requests RUN word ->
  groups_work word<=11*(length left+length right)+5.
Proof.
  intros left right requests RUN word WORD.
  pose proof (lex_word_work_is_derived_from_its_actual_requests _ _ _ _ _ _ WORD) as WORK.
  pose proof (N.initial_weighted_lex_requests_do_not_expand_multiplicities
    compare left right requests RUN) as WIDTH. nia.
Qed.
End LexPhaseWord.

Definition core_setup_word : list ControlGroup :=
  [FromParts;MergeInit;ResetRun;MergeInit;ResetRun;ResumeEntry;PhaseAttempt].
Definition equal_lead_core_word left right lex := core_setup_word++left++right++lex.

Lemma core_setup_is_the_original_seven_groups : groups_work core_setup_word=7.
Proof. reflexivity. Qed.

Lemma decisive_initial_lead_is_already_covered : forall n m,
  groups_work core_setup_word<=23*(n*(n-1)+m*(m-1))+11*(n+m)+28.
Proof. intros; rewrite core_setup_is_the_original_seven_groups; lia. Qed.

Print Assumptions lex_word_work_is_derived_from_its_actual_requests.
Print Assumptions original_weighted_lex_supplies_the_word_envelope.

Section CompleteCoreWord.
Context {Key Payload Secondary State : Type}.
Variable payload_secondary : Payload -> option Secondary.
Variable payload_repetitions : Payload -> nat.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Local Notation Entry := (Key*Payload)%type.
Variable compare : Entry -> Entry -> State -> option comparison * State.
Variable lex_compare : Entry -> Entry -> comparison.
Variable maximum : nat.
Local Notation H := (@Handshakes Entry State compare maximum).
Local Notation PhaseWord := (@SourceSortPhaseWord Key Payload Secondary State
  payload_secondary key_alias secondary_alias compare maximum).
Local Notation LexWord := (@SourceLexWord Key Payload Secondary
  payload_secondary key_alias secondary_alias lex_compare).
Definition repeated_roster (source : list Entry) :=
  map (fun entry => (entry,payload_repetitions (snd entry))) source.

(** This is the componentwise source-word contract: the two phase words
    decorate the actual handshakes CONSTRUCTED from the original two native
    sorts, and the lex word decorates an actual weighted request derivation
    on those sorted rosters. Its item words retain their RawPayloadDialogue
    witnesses. No numeric bound on a callback, pass count, run count or
    trace length is a premise. Native term bodies, materialization, flat
    storage ownership and generated continuation scheduling are additional.

    The annotation is a logical source association, not a theorem about
    compilation of Rust or an additional runtime interpreter. In particular
    an arbitrary response function need not have an item-route annotation;
    the actual collection request protocol supplies that source evidence. *)
Theorem completed_core_word_has_a_source_derived_allowance :
  forall passes_left left state sorted_left scratch_left middle
    passes_right right sorted_right scratch_right last,
  length left<=maximum -> length right<=maximum ->
  NativeOuterExecution compare maximum passes_left 1 left None state
    sorted_left scratch_left middle ->
  NativeOuterExecution compare maximum passes_right 1 right None middle
    sorted_right scratch_right last ->
  exists wl cl al tl bl
    (HL : H (initial_merge maximum left) state (S al) al tl bl
      (merge_state sorted_left scratch_left wl cl false true) middle),
  exists wr cr ar tr br
    (HR : H (initial_merge maximum right) middle (S ar) ar tr br
      (merge_state sorted_right scratch_right wr cr false true) last),
  forall left_word right_word requests
    (LEX : N.LexRequests lex_compare (repeated_roster sorted_left)
      (repeated_roster sorted_right) (L.unit_cursor 0) requests) lex_word,
  PhaseWord _ _ _ _ _ _ _ _ HL left_word ->
  PhaseWord _ _ _ _ _ _ _ _ HR right_word ->
  LexWord _ _ _ _ LEX lex_word ->
  groups_work (equal_lead_core_word left_word right_word lex_word)<=
    23*(length left*(length left-1)+length right*(length right-1))+
    11*(length left+length right)+28.
Proof.
  intros passes_left left state sorted_left scratch_left middle
    passes_right right sorted_right scratch_right last ML MR SORT_LEFT SORT_RIGHT.
  destruct (original_native_sort_supplies_the_phase_word_envelope
    payload_secondary key_alias secondary_alias compare maximum
    passes_left left state sorted_left scratch_left middle ML SORT_LEFT)
    as [wl [cl [al [tl [bl [HL LEFT]]]]]].
  destruct (original_native_sort_supplies_the_phase_word_envelope
    payload_secondary key_alias secondary_alias compare maximum
    passes_right right middle sorted_right scratch_right last MR SORT_RIGHT)
    as [wr [cr [ar [tr [br [HR RIGHT]]]]]].
  exists wl,cl,al,tl,bl,HL,wr,cr,ar,tr,br,HR.
  intros left_word right_word requests LEX lex_word WORD_LEFT WORD_RIGHT WORD_LEX.
  specialize (LEFT left_word WORD_LEFT). specialize (RIGHT right_word WORD_RIGHT).
  pose proof (original_weighted_lex_supplies_the_word_envelope
    payload_secondary key_alias secondary_alias lex_compare _ _ _ LEX lex_word WORD_LEX)
    as LEX_WORK.
  destruct (actual_buffer_lifecycle_projects_to_the_existing_outer_trace compare
    maximum passes_left 1 left None state sorted_left scratch_left middle
    SORT_LEFT ltac:(lia) ML I) as [_ [LEN_LEFT _]].
  destruct (actual_buffer_lifecycle_projects_to_the_existing_outer_trace compare
    maximum passes_right 1 right None middle sorted_right scratch_right last
    SORT_RIGHT ltac:(lia) MR I) as [_ [LEN_RIGHT _]].
  unfold repeated_roster in LEX_WORK. rewrite !map_length,LEN_LEFT,LEN_RIGHT in LEX_WORK.
  unfold equal_lead_core_word. rewrite !groups_work_append,core_setup_is_the_original_seven_groups.
  nia.
Qed.
End CompleteCoreWord.

Print Assumptions completed_core_word_has_a_source_derived_allowance.

End NativeCollectionCoreInventory.
