(** Control-work accounting for the existing collection comparison core.
    Source: collection_cmp_pda.rs741-802 and its named ControlGroup sites.
    A completed run pays both terminal tail guards, but a final pass breaks
    without another outer guard. Charge lists below describe these source
    blocks, not a second state-transition engine. Scratch allocation and
    disposal retain their separate flat-slot receipt; neither is included in
    the control allowance. Native surcharge is additional to preflight credit.

    This first checkpoint establishes the raw continuation invariants and
    local charge-block arithmetic. Their composition with complete original
    RawMergeStep derivations remains necessary before native work coverage
    may be claimed. Rust pointer validity and the association of each named
    group with its actual policy call remain explicit source boundaries. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
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
End GeneratedCollectionWorkCover.

Print Assumptions GeneratedCollectionWorkCover.successful_copy_preserves_every_exhausted_side.
Print Assumptions GeneratedCollectionWorkCover.every_silent_operation_has_an_allocated_target.
Print Assumptions GeneratedCollectionWorkCover.allocated_target_survives_a_complete_raw_step.
Print Assumptions GeneratedCollectionWorkCover.groups_work_append.
Print Assumptions GeneratedCollectionWorkCover.tail_guard_and_copy_work.
Print Assumptions GeneratedCollectionWorkCover.completed_run_control_work_is_covered.
