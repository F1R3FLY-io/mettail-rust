(** Control-work accounting for the existing collection comparison core.
    Source: collection_cmp_pda.rs741-802 and its named ControlGroup sites.
    A completed run pays both terminal tail guards, but a final pass breaks
    without another outer guard. Charge lists below describe these source
    blocks, not a second state-transition engine. Scratch allocation and
    disposal retain their separate flat-slot receipt; neither is included in
    the control allowance. Native surcharge is additional to preflight credit.

    Grouping annotates complete original RawMergeStep derivations and covers
    their successful control work only. It does not establish complete native
    key-callback coverage or pre-admit an execution. Rust pointer validity and
    the association of each named group with its actual policy call remain
    explicit source boundaries. *)
From Stdlib Require Import List Arith.PeanoNat Lia Program.Equality.
From RhoBridge Require Import GeneratedMapCoreSource MergeSortPdaCursor
  AdmittedCollectionComparisonOwnership.
Import ListNotations.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.

Module GeneratedCollectionWorkCover.
Section SourceInvariants.
Context {Entry : Type}.

Lemma successful_copy_preserves_every_exhausted_side :
  forall side cursor (source target : list Entry) next_cursor next exhausted,
  copy_record side cursor source target = Some (next_cursor, next) ->
  ~ can_copy exhausted cursor -> ~ can_copy exhausted next_cursor.
Proof.
  intros side cursor source target next_cursor next exhausted COPY EMPTY.
  unfold copy_record in COPY.
  destruct (nth_error source (selected_index side cursor)) as [value|];
    [|discriminate].
  destruct (overwrite (output_index cursor) value target); [|discriminate].
  inversion COPY; subst next_cursor.
  destruct side, exhausted; cbn [advance can_copy left_index right_index
    run_middle run_end] in *; lia.
Qed.

Lemma every_silent_operation_has_an_allocated_target :
  forall maximum (state next : @RawMergeState Entry),
  RawMergeSilent maximum state next -> exists target, merge_target next = Some target.
Proof.
  intros maximum state next STEP. destruct STEP.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - unfold merge_after_run.
    destruct (run_end (merge_cursor state) <? length (merge_source state));
      [eexists; reflexivity|].
    destruct (length target <=? saturated_double maximum (merge_width state));
      eexists; reflexivity.
Qed.

Lemma allocated_target_survives_a_complete_raw_step :
  forall maximum (state : @RawMergeState Entry) reply next,
  RawMergeStep maximum state reply next ->
  (exists target, merge_target state = Some target) ->
  exists target, merge_target next = Some target.
Proof.
  intros maximum state reply next STEP. induction STEP; intro TARGET.
  - exact TARGET.
  - destruct TARGET as [original TARGET]. exists original. exact TARGET.
  - apply IHSTEP. eapply every_silent_operation_has_an_allocated_target; eassumption.
Qed.
End SourceInvariants.

Definition groups_work := fold_right (fun group total => control_work group + total) 0.
Fixpoint tail_groups attempt count := match count with
  | 0 => [attempt]
  | S rest => attempt :: TailCopy :: tail_groups attempt rest
  end.
Definition completed_run_groups left_copies right_copies (pass reset : bool) :=
  [MergeOuterAttempt; MergeCompareReady] ++ tail_groups LeftTailAttempt left_copies ++
  tail_groups RightTailAttempt right_copies ++ [RunEnd] ++
  (if pass then [PassFinish] else []) ++ (if reset then [ResetRun] else []).

Lemma groups_work_append : forall first second,
  groups_work (first ++ second) = groups_work first + groups_work second.
Proof.
  induction first as [|group rest IH]; intro second; [reflexivity|].
  change (control_work group + groups_work (rest ++ second) =
    (control_work group + groups_work rest) + groups_work second). rewrite IH; lia.
Qed.

Lemma tail_guard_and_copy_work : forall count attempt,
  control_work attempt = 1 -> groups_work (tail_groups attempt count) = 2 * count + 1.
Proof.
  induction count; intros attempt ATTEMPT.
  - change (control_work attempt + 0 = 1). now rewrite ATTEMPT.
  - change (control_work attempt + (1 + groups_work (tail_groups attempt count)) =
      2 * S count + 1). rewrite ATTEMPT, IHcount by exact ATTEMPT; lia.
Qed.

Lemma completed_run_control_work_is_covered : forall lhs rhs pass reset,
  groups_work (completed_run_groups lhs rhs pass reset) <= 7 + 2 * (lhs + rhs).
Proof.
  intros. unfold completed_run_groups. rewrite !groups_work_append.
  rewrite !tail_guard_and_copy_work by reflexivity.
  destruct pass, reset; cbn [groups_work fold_right control_work]; lia.
Qed.
Inductive MergeMark := ScratchMark | LeftMark | RightMark
  | FinishMark (pass reset : bool).
Record RunBlock := {
  block_left : nat; block_right : nat;
  block_pass : bool; block_reset : bool
}.
Definition block_marks block :=
  repeat LeftMark (block_left block) ++ repeat RightMark (block_right block) ++
  [FinishMark (block_pass block) (block_reset block)].
Definition blocks_marks blocks := flat_map block_marks blocks.
Definition prepend_left block :=
  {| block_left := S (block_left block); block_right := block_right block;
     block_pass := block_pass block; block_reset := block_reset block |}.
Definition prepend_right block :=
  {| block_left := block_left block; block_right := S (block_right block);
     block_pass := block_pass block; block_reset := block_reset block |}.

Lemma prepend_left_has_the_original_mark : forall block,
  block_marks (prepend_left block) = LeftMark :: block_marks block.
Proof. intros []; reflexivity. Qed.
Lemma prepend_right_has_the_original_mark : forall block,
  block_left block = 0 ->
  block_marks (prepend_right block) = RightMark :: block_marks block.
Proof. intros [lhs rhs pass reset] LEFT. cbn in LEFT. subst lhs. reflexivity. Qed.

Section DerivationGrouping.
Context {Entry : Type}.
Variable maximum : nat.
Definition silent_mark (state next : @RawMergeState Entry) :=
  match merge_target state with
  | None => ScratchMark
  | Some _ =>
      if left_index (merge_cursor state) <? run_middle (merge_cursor state) then LeftMark
      else if right_index (merge_cursor state) <? run_end (merge_cursor state) then RightMark
      else FinishMark (negb (run_end (merge_cursor state) <? length (merge_source state)))
        (negb (merge_done next))
  end.

(** This proposition annotates an existing derivation. It cannot advance a
    machine, select a callback answer or supply a replacement transition. *)
Inductive RawStepWordKind := DoneWord | RequestWord | InternalWord.

Inductive raw_step_word : RawStepWordKind ->
    forall (state : @RawMergeState Entry) (reply : @RawMergeReply Entry)
      (next : @RawMergeState Entry), list MergeMark -> Prop :=
| raw_step_word_done : forall state,
    raw_step_word DoneWord state MergeCompletes state []
| raw_step_word_requests : forall state lhs rhs,
    raw_step_word RequestWord state (MergeRequests lhs rhs)
      (merge_set_waiting state true) []
| raw_step_word_internal : forall state middle reply next kind suffix,
    raw_step_word kind middle reply next suffix ->
    raw_step_word InternalWord state reply next
      (silent_mark state middle :: suffix).

Lemma every_actual_raw_step_has_its_word : forall state reply next
    (STEP : @RawMergeStep Entry maximum state reply next),
  exists kind word, raw_step_word kind state reply next word.
Proof.
  intros state reply next STEP.
  induction STEP as
    [state WAIT DONE|state target lhs rhs WAIT DONE TARGET REQUEST|
     state middle reply next SILENT REST IH].
  - exists DoneWord, []; apply raw_step_word_done.
  - exists RequestWord, []; apply raw_step_word_requests.
  - destruct IH as [kind [word WORD]]. exists InternalWord, (silent_mark state middle :: word).
    eapply raw_step_word_internal. exact WORD.
Qed.

Lemma silent_mark_none : forall state next,
  merge_target state = None -> silent_mark state next = ScratchMark.
Proof. intros; unfold silent_mark; rewrite H; reflexivity. Qed.

Lemma silent_mark_left : forall state next target,
  merge_target state = Some target -> can_copy FromLeft (merge_cursor state) ->
  silent_mark state next = LeftMark.
Proof.
  intros state next target TARGET LIVE. unfold silent_mark; rewrite TARGET.
  assert (LT : (selected_index FromLeft (merge_cursor state) <? run_middle (merge_cursor state)) = true)
    by (apply Nat.ltb_lt; exact LIVE).
  cbn [selected_index] in LT. rewrite LT. reflexivity.
Qed.

Lemma silent_mark_right : forall state next target,
  merge_target state = Some target -> ~ can_copy FromLeft (merge_cursor state) ->
  can_copy FromRight (merge_cursor state) -> silent_mark state next = RightMark.
Proof.
  intros state next target TARGET EMPTY LIVE. unfold silent_mark; rewrite TARGET.
  assert (GE : (selected_index FromLeft (merge_cursor state) <? run_middle (merge_cursor state)) = false)
    by (apply Nat.ltb_ge; unfold can_copy in EMPTY; cbn in *; lia).
  assert (LT : (selected_index FromRight (merge_cursor state) <? run_end (merge_cursor state)) = true)
    by (apply Nat.ltb_lt; exact LIVE).
  cbn [selected_index] in LT, GE. rewrite GE, LT. reflexivity.
Qed.

Lemma silent_mark_finish : forall state next target,
  merge_target state = Some target -> ~ can_copy FromLeft (merge_cursor state) ->
  ~ can_copy FromRight (merge_cursor state) ->
  silent_mark state next = FinishMark
    (negb (run_end (merge_cursor state) <? length (merge_source state)))
    (negb (merge_done next)).
Proof.
  intros state next target TARGET EMPTY_L EMPTY_R. unfold silent_mark; rewrite TARGET.
  assert (GE_L : (selected_index FromLeft (merge_cursor state) <? run_middle (merge_cursor state)) = false)
    by (apply Nat.ltb_ge; unfold can_copy in EMPTY_L; cbn in *; lia).
  assert (GE_R : (selected_index FromRight (merge_cursor state) <? run_end (merge_cursor state)) = false)
    by (apply Nat.ltb_ge; unfold can_copy in EMPTY_R; cbn in *; lia).
  cbn [selected_index] in GE_L, GE_R. rewrite GE_L, GE_R. reflexivity.
Qed.

Ltac rewrite_silent_mark :=
  first [
    match goal with
    | TARGET : merge_target ?state = None |- context [silent_mark ?state ?next] =>
        rewrite (silent_mark_none ?state ?next TARGET)
    | TARGET : merge_target ?state = Some ?target,
      LIVE : can_copy FromLeft (merge_cursor ?state),
      EMPTY : ~ can_copy FromRight (merge_cursor ?state) |- context [silent_mark ?state ?next] =>
        rewrite (silent_mark_left ?state ?next ?target TARGET LIVE)
    | TARGET : merge_target ?state = Some ?target,
      EMPTY : ~ can_copy FromLeft (merge_cursor ?state),
      LIVE : can_copy FromRight (merge_cursor ?state) |- context [silent_mark ?state ?next] =>
        rewrite (silent_mark_right ?state ?next ?target TARGET EMPTY LIVE)
    | TARGET : merge_target ?state = Some ?target,
      EMPTY_L : ~ can_copy FromLeft (merge_cursor ?state),
      EMPTY_R : ~ can_copy FromRight (merge_cursor ?state) |- context [silent_mark ?state ?next] =>
        rewrite (silent_mark_finish ?state ?next ?target TARGET EMPTY_L EMPTY_R)
    end ].
Definition first_left blocks := match blocks with [] => 0 | block :: _ => block_left block end.
Definition first_right blocks := match blocks with [] => 0 | block :: _ => block_right block end.
Definition grouped_word (state : @RawMergeState Entry) word (scratch : bool) blocks :=
  word = (if scratch then [ScratchMark] else []) ++ blocks_marks blocks /\
  (scratch = true -> merge_target state = None) /\
  (blocks = [] -> merge_done state = true \/
    (can_copy FromLeft (merge_cursor state) /\ can_copy FromRight (merge_cursor state))) /\
  (~ can_copy FromLeft (merge_cursor state) -> first_left blocks = 0) /\
  (~ can_copy FromRight (merge_cursor state) -> first_right blocks = 0).

(** No grouping is supplied by a caller. The original derivation produces it;
    in particular neither a pending tail nor another allocation can be hidden
    in the word between completed runs. *)
Theorem actual_raw_step_derives_completed_run_grouping : forall state reply next
    (STEP : @RawMergeStep Entry maximum state reply next),
  exists kind word,
    exists scratch blocks,
      raw_step_word kind state reply next word /\
      grouped_word state word scratch blocks.
Proof.
  intros state reply next STEP.
  induction STEP as
    [state WAIT DONE|state target lhs rhs WAIT DONE TARGET REQUEST|
     state middle reply next SILENT REST IH].
  - exists DoneWord, [], false, []. split; [apply raw_step_word_done|].
    split; [reflexivity|]. split; [discriminate|].
    split; [intros _; now left|]. split; intros; reflexivity.
  - exists RequestWord, [], false, []. split; [apply raw_step_word_requests|].
    destruct REQUEST as [READY_L [READY_R READS]].
    split; [reflexivity|]. split; [discriminate|].
    split; [intros _; right; now split|]. split; intros; reflexivity.
  - destruct IH as [kind [word [scratch [blocks [WORD GROUP]]]]].
    exists InternalWord, (silent_mark state middle :: word).
    destruct GROUP as [EQ [SC [EMPTY [LEFT RIGHT]]]].
    destruct SILENT as
      [state WAIT DONE TARGET|
       state target cursor after WAIT DONE TARGET LIVE_L EMPTY_R COPY|
       state target cursor after WAIT DONE TARGET EMPTY_L LIVE_R COPY|
       state target WAIT DONE TARGET EMPTY_L EMPTY_R];
      assert (NO_SCRATCH : scratch = false) by
        (destruct scratch; [specialize (SC eq_refl); cbn [merge_set_target merge_after_copy
          merge_state merge_target] in SC; try discriminate;
          destruct (every_silent_operation_has_an_allocated_target maximum _ _
            (MergeEndsRun maximum state target WAIT DONE TARGET EMPTY_L EMPTY_R))
            as [allocated ALLOCATED]; congruence|reflexivity]);
      subst scratch; cbn [app] in EQ; unfold grouped_word.
    + exists true, blocks. split; [eapply raw_step_word_internal; exact WORD|].
      split.
      * cbn. rewrite (silent_mark_none state
          (merge_set_target state (Some (merge_source state))) TARGET).
        f_equal; exact EQ.
      * split; [intros _; exact TARGET|]. split; [exact EMPTY|]. split; assumption.
    + pose proof (successful_copy_preserves_every_exhausted_side FromLeft
        (merge_cursor state) (merge_source state) target cursor after FromRight COPY EMPTY_R)
        as NEXT_EMPTY_R.
      destruct blocks as [|block blocks].
      * specialize (EMPTY eq_refl). destruct EMPTY as [IS_DONE|[_ READY_R]].
        -- change (merge_done state = true) in IS_DONE. congruence.
        -- exact (False_rect _ (NEXT_EMPTY_R READY_R)).
      * exists false, (prepend_left block :: blocks). split.
        -- eapply raw_step_word_internal; exact WORD.
        -- cbn [app]. rewrite (silent_mark_left state
             (merge_after_copy state cursor after) target TARGET LIVE_L).
           split.
           ++ cbn [blocks_marks flat_map]. rewrite EQ.
              rewrite prepend_left_has_the_original_mark. reflexivity.
           ++ split; [discriminate|]. split; [discriminate|]. split.
              { intro IMPOSSIBLE. contradiction. }
              { intro H. change (block_right block = 0). exact (RIGHT NEXT_EMPTY_R). }
    + pose proof (successful_copy_preserves_every_exhausted_side FromRight
        (merge_cursor state) (merge_source state) target cursor after FromLeft COPY EMPTY_L)
        as NEXT_EMPTY_L.
      destruct blocks as [|block blocks].
      * specialize (EMPTY eq_refl). destruct EMPTY as [IS_DONE|[READY_L _]].
        -- change (merge_done state = true) in IS_DONE. congruence.
        -- exact (False_rect _ (NEXT_EMPTY_L READY_L)).
      * assert (NO_LEFT : block_left block = 0) by exact (LEFT NEXT_EMPTY_L).
        exists false, (prepend_right block :: blocks). split.
        -- eapply raw_step_word_internal; exact WORD.
        -- cbn [app]. rewrite (silent_mark_right state
             (merge_after_copy state cursor after) target TARGET EMPTY_L LIVE_R).
           split.
           ++ cbn [blocks_marks flat_map]. rewrite EQ.
              rewrite prepend_right_has_the_original_mark by exact NO_LEFT. reflexivity.
           ++ split; [discriminate|]. split; [discriminate|]. split.
              { intros _. exact NO_LEFT. }
              { intro IMPOSSIBLE. contradiction. }
    + exists false,
        ({| block_left := 0; block_right := 0;
            block_pass := negb (run_end (merge_cursor state) <? length (merge_source state));
            block_reset := negb (merge_done (merge_after_run maximum state target)) |} :: blocks).
      split.
      * eapply raw_step_word_internal; exact WORD.
      * rewrite (silent_mark_finish state
          (merge_after_run maximum state target) target TARGET EMPTY_L EMPTY_R).
        cbn [app blocks_marks flat_map block_marks block_left block_right block_pass
          block_reset repeat]. now rewrite EQ.
Qed.
End DerivationGrouping.

Definition run_groups block := completed_run_groups (block_left block) (block_right block)
  (block_pass block) (block_reset block).
Definition total_tails := fold_right (fun block total => block_left block + block_right block + total) 0.
Definition sparse_group group := match group with
  | MergeStepEntry | RunEnd | TailCopy => true
  | _ => false
  end.
Definition sparse_work groups := groups_work (filter sparse_group groups).
Definition finish_groups {Entry : Type} (reply : @RawMergeReply Entry) (blocks : list RunBlock) :=
  match reply with
  | MergeRequests _ _ => [MergeOuterAttempt; MergeCompareReady]
  | MergeCompletes => match blocks with [] => [MergeOuterAttempt] | _ :: _ => [] end
  end.
Definition invocation_groups {Entry : Type} (reply : @RawMergeReply Entry) blocks :=
  MergeStepEntry :: flat_map run_groups blocks ++ finish_groups reply blocks.

Lemma sparse_work_append : forall first second,
  sparse_work (first ++ second) = sparse_work first + sparse_work second.
Proof. intros. unfold sparse_work. rewrite filter_app. apply groups_work_append. Qed.

Lemma sparse_markers_are_paid_original_occurrences : forall groups,
  sparse_work groups <= groups_work groups.
Proof.
  induction groups as [|group groups IH]; [reflexivity|]. unfold sparse_work in *.
  cbn [filter]. destruct (sparse_group group); cbn [groups_work fold_right] in *; lia.
Qed.

Lemma tail_groups_retain_each_paid_copy : forall count attempt,
  sparse_group attempt = false -> sparse_work (tail_groups attempt count) = count.
Proof.
  induction count; intros attempt ATTEMPT.
  - unfold sparse_work. cbn [tail_groups filter]. rewrite ATTEMPT. reflexivity.
  - unfold sparse_work in *. cbn [tail_groups filter]. rewrite ATTEMPT.
    change (1 + groups_work (filter sparse_group (tail_groups attempt count)) = S count).
    rewrite IHcount by exact ATTEMPT. lia.
Qed.

Lemma completed_run_retains_exact_paid_markers : forall block,
  sparse_work (run_groups block) = 1 + block_left block + block_right block.
Proof.
  intros [lhs rhs pass reset]. unfold run_groups, completed_run_groups.
  rewrite !sparse_work_append. rewrite !tail_groups_retain_each_paid_copy by reflexivity.
  destruct pass, reset; cbn [sparse_work filter sparse_group groups_work fold_right
    control_work block_left block_right block_pass block_reset]; lia.
Qed.

Lemma completed_blocks_have_the_derived_work_bound : forall blocks,
  groups_work (flat_map run_groups blocks) <= 7 * length blocks + 2 * total_tails blocks.
Proof.
  induction blocks as [|block blocks IH]; [reflexivity|].
  cbn [flat_map]. rewrite groups_work_append.
  pose proof (completed_run_control_work_is_covered (block_left block) (block_right block)
    (block_pass block) (block_reset block)) as LOCAL.
  change (groups_work (run_groups block) <= 7 + 2 * (block_left block + block_right block)) in LOCAL.
  cbn [length total_tails fold_right]. lia.
Qed.

Lemma completed_blocks_retain_exact_paid_markers : forall blocks,
  sparse_work (flat_map run_groups blocks) = length blocks + total_tails blocks.
Proof.
  induction blocks as [|block blocks IH]; [reflexivity|].
  cbn [flat_map]. rewrite sparse_work_append, completed_run_retains_exact_paid_markers, IH.
  cbn [length total_tails fold_right]. lia.
Qed.

Lemma groups_work_entry : forall groups,
  groups_work (MergeStepEntry :: groups) = 1 + groups_work groups.
Proof. intros. reflexivity. Qed.

Lemma sparse_work_entry : forall groups,
  sparse_work (MergeStepEntry :: groups) = 1 + sparse_work groups.
Proof. intros. reflexivity. Qed.

Theorem grouped_invocation_control_is_covered_by_its_actual_paid_markers :
  forall Entry (reply : @RawMergeReply Entry) blocks,
  groups_work (invocation_groups reply blocks) <=
    5 + 7 * length blocks + 2 * total_tails blocks /\
  sparse_work (invocation_groups reply blocks) = 1 + length blocks + total_tails blocks /\
  groups_work (invocation_groups reply blocks) <=
    7 * sparse_work (invocation_groups reply blocks).
Proof.
  intros Entry reply blocks.
  pose proof (completed_blocks_have_the_derived_work_bound blocks) as BOUND.
  pose proof (completed_blocks_retain_exact_paid_markers blocks) as SPARSE.
  assert (EXIT : groups_work (finish_groups reply blocks) <= 2 /\
    sparse_work (finish_groups reply blocks) = 0).
  { destruct reply; [split; reflexivity|destruct blocks; split; cbn [finish_groups
      sparse_work filter sparse_group groups_work fold_right control_work]; lia]. }
  destruct EXIT as [EXIT EMPTY]. unfold invocation_groups.
  rewrite groups_work_entry, sparse_work_entry.
  rewrite groups_work_append, sparse_work_append, SPARSE, EMPTY.
  cbn [control_work]. lia.
Qed.

(** Only the first Return of this same invocation determines its suffix. A
    completed final run has no invented outer guard after break. ScratchMark
    records the separate allocation boundary but contributes no control credit.
    The association with Rust is the original source guard/operation audit,
    not a hypothesis granting a caller a desired trace bound. *)
Theorem every_actual_raw_step_has_a_derived_control_cover :
  forall Entry maximum state reply next (STEP : @RawMergeStep Entry maximum state reply next),
  exists kind word scratch blocks,
    raw_step_word kind state reply next word /\
    grouped_word state word scratch blocks /\
    groups_work (invocation_groups reply blocks) <=
      7 * sparse_work (invocation_groups reply blocks).
Proof.
  intros Entry maximum state reply next STEP.
  destruct (actual_raw_step_derives_completed_run_grouping maximum state reply next STEP)
    as [kind [word [scratch [blocks [WORD GROUPED]]]]].
  exists kind, word, scratch, blocks. split; [exact WORD|]. split; [exact GROUPED|].
  exact (proj2 (proj2 (grouped_invocation_control_is_covered_by_its_actual_paid_markers
    Entry reply blocks))).
Qed.
End GeneratedCollectionWorkCover.

Print Assumptions GeneratedCollectionWorkCover.successful_copy_preserves_every_exhausted_side.
Print Assumptions GeneratedCollectionWorkCover.every_silent_operation_has_an_allocated_target.
Print Assumptions GeneratedCollectionWorkCover.allocated_target_survives_a_complete_raw_step.
Print Assumptions GeneratedCollectionWorkCover.groups_work_append.
Print Assumptions GeneratedCollectionWorkCover.tail_guard_and_copy_work.
Print Assumptions GeneratedCollectionWorkCover.completed_run_control_work_is_covered.
Print Assumptions GeneratedCollectionWorkCover.prepend_left_has_the_original_mark.
Print Assumptions GeneratedCollectionWorkCover.prepend_right_has_the_original_mark.
Print Assumptions GeneratedCollectionWorkCover.every_actual_raw_step_has_its_word.
Print Assumptions GeneratedCollectionWorkCover.actual_raw_step_derives_completed_run_grouping.
Print Assumptions GeneratedCollectionWorkCover.sparse_work_append.
Print Assumptions GeneratedCollectionWorkCover.sparse_markers_are_paid_original_occurrences.
Print Assumptions GeneratedCollectionWorkCover.tail_groups_retain_each_paid_copy.
Print Assumptions GeneratedCollectionWorkCover.completed_run_retains_exact_paid_markers.
Print Assumptions GeneratedCollectionWorkCover.completed_blocks_have_the_derived_work_bound.
Print Assumptions GeneratedCollectionWorkCover.completed_blocks_retain_exact_paid_markers.
Print Assumptions GeneratedCollectionWorkCover.grouped_invocation_control_is_covered_by_its_actual_paid_markers.
Print Assumptions GeneratedCollectionWorkCover.every_actual_raw_step_has_a_derived_control_cover.
