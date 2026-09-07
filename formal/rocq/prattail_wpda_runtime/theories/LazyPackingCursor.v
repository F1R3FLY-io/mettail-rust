(* Adapter between Bin's lazy packing/flat cursors and the scheduler's
 * ghost ordered rows. Preparing a packing and resetting an exhausted flat
 * cursor preserve those rows; consuming a row removes exactly its head.
 * Administrative credit counts zero-flat packings too.
 *
 * remaining_rows is a specification only. Calling it at runtime would
 * eagerly evaluate future preparation and could change which fault wins.
 * inspect_cursor evaluates only the next packing when no current rows
 * exist. RowReady allows a caller to suspend/resume its Cartesian cursor
 * without inspecting any later packing. Cartesian output-quota semantics
 * are not replaced by a row-count quota in this adapter.
 *)
From Stdlib Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Section PackingCursor.
  Context {Packing Row Fault : Type}.
  Variable prepare_packing : Packing -> Fault + list Row.

  Record packing_cursor := {
    pending_packings : list Packing;
    current_rows : option (list Row)
  }.

  Fixpoint prepared_rows (packings : list Packing) : Fault + list Row :=
    match packings with
    | [] => inr []
    | packing :: rest => match prepare_packing packing with
        | inl fault => inl fault
        | inr rows => match prepared_rows rest with
            | inl fault => inl fault
            | inr suffix => inr (rows ++ suffix)
            end
        end
    end.

  Definition remaining_rows (cursor : packing_cursor) : Fault + list Row :=
    match current_rows cursor with
    | None => prepared_rows (pending_packings cursor)
    | Some rows => match prepared_rows (pending_packings cursor) with
        | inl fault => inl fault
        | inr suffix => inr (rows ++ suffix)
        end
    end.

  Inductive cursor_observation :=
  | CursorAdvanced : packing_cursor -> cursor_observation
  | RowReady : Row -> cursor_observation
  | CursorExhausted : cursor_observation
  | PreparationFailed : Packing -> Fault -> cursor_observation.

  Definition inspect_cursor (cursor : packing_cursor) : cursor_observation :=
    match current_rows cursor with
    | Some [] => CursorAdvanced
        {| pending_packings := pending_packings cursor; current_rows := None |}
    | Some (first :: _) => RowReady first
    | None => match pending_packings cursor with
        | [] => CursorExhausted
        | packing :: rest => match prepare_packing packing with
            | inl fault => PreparationFailed packing fault
            | inr rows => CursorAdvanced {| pending_packings := rest; current_rows := Some rows |}
            end
        end
    end.

  Definition administrative_credit (cursor : packing_cursor) : nat :=
    2 * length (pending_packings cursor) +
      match current_rows cursor with None => 0 | Some _ => 1 end.

  Theorem administrative_steps_preserve_the_exact_remaining_rows : forall before after,
    inspect_cursor before = CursorAdvanced after -> remaining_rows before = remaining_rows after.
  Proof.
    intros [pending current] after Hstep. destruct current as [[|first rest]|];
      cbn [inspect_cursor current_rows pending_packings] in Hstep; try discriminate.
    - inversion Hstep; subst. cbn [remaining_rows current_rows pending_packings].
      destruct (prepared_rows pending); reflexivity.
    - destruct pending as [|packing rest]; [discriminate|].
      destruct (prepare_packing packing) as [fault|rows] eqn:Hprepare; [discriminate|].
      inversion Hstep; subst. cbn [remaining_rows current_rows pending_packings prepared_rows].
      now rewrite Hprepare.
  Qed.

  Theorem each_administrative_step_consumes_one_credit : forall before after,
    inspect_cursor before = CursorAdvanced after ->
    administrative_credit before = S (administrative_credit after).
  Proof.
    intros [pending current] after Hstep. destruct current as [[|first rest]|];
      cbn [inspect_cursor current_rows pending_packings] in Hstep; try discriminate.
    - inversion Hstep; subst.
      change (2 * length pending + 1 = S (2 * length pending + 0)). lia.
    - destruct pending as [|packing rest]; [discriminate|].
      destruct (prepare_packing packing); [discriminate|].
      inversion Hstep; subst.
      change (2 * S (length rest) + 0 = S (2 * length rest + 1)). lia.
  Qed.

  Theorem consuming_a_ready_row_removes_exactly_one_ordered_occurrence :
    forall pending first rest whole,
    remaining_rows {| pending_packings := pending; current_rows := Some (first :: rest) |} = inr whole ->
    exists suffix, whole = first :: suffix /\
      remaining_rows {| pending_packings := pending; current_rows := Some rest |} = inr suffix.
  Proof.
    intros pending first rest whole Hrows.
    cbn [remaining_rows current_rows pending_packings] in *.
    destruct (prepared_rows pending) as [fault|tail] eqn:Hpending; [discriminate|].
    inversion Hrows; subst. exists (rest ++ tail). split; reflexivity.
  Qed.

  Theorem row_consumption_preserves_administrative_credit : forall pending first rest,
    administrative_credit {| pending_packings := pending; current_rows := Some (first :: rest) |} =
      administrative_credit {| pending_packings := pending; current_rows := Some rest |}.
  Proof. reflexivity. Qed.

  Theorem exhausted_cursor_has_no_unvisited_rows_or_packings : forall cursor,
    inspect_cursor cursor = CursorExhausted ->
    current_rows cursor = None /\ pending_packings cursor = [] /\ remaining_rows cursor = inr [].
  Proof.
    intros [pending current] Hdone. destruct current as [[|first rest]|];
      cbn [inspect_cursor current_rows pending_packings] in Hdone; try discriminate.
    destruct pending as [|packing rest].
    - repeat split; reflexivity.
    - destruct (prepare_packing packing); discriminate.
  Qed.

  Theorem preparation_failure_identifies_the_next_unvisited_packing : forall cursor packing fault,
    inspect_cursor cursor = PreparationFailed packing fault ->
    current_rows cursor = None /\ exists rest,
      pending_packings cursor = packing :: rest /\ prepare_packing packing = inl fault.
  Proof.
    intros [pending current] packing fault Hfailed. destruct current as [[|first rest]|];
      cbn [inspect_cursor current_rows pending_packings] in Hfailed; try discriminate.
    destruct pending as [|next rest]; [discriminate|].
    destruct (prepare_packing next) as [failure|rows] eqn:Hprepare; [|discriminate].
    inversion Hfailed; subst. split; [reflexivity|]. exists rest. split; [reflexivity|exact Hprepare].
  Qed.

  Inductive seek_result :=
  | SeekReady : packing_cursor -> Row -> seek_result
  | SeekExhausted : seek_result
  | SeekPreparationFailed : Packing -> Fault -> seek_result
  | SeekBudgetExhausted : seek_result.

  Fixpoint seek_row (fuel : nat) (cursor : packing_cursor) : seek_result :=
    match fuel with
    | 0 => SeekBudgetExhausted
    | S remaining => match inspect_cursor cursor with
        | CursorAdvanced after => seek_row remaining after
        | RowReady first => SeekReady cursor first
        | CursorExhausted => SeekExhausted
        | PreparationFailed packing fault => SeekPreparationFailed packing fault
        end
    end.

  Theorem bounded_seek_cannot_loop_on_empty_packings : forall fuel cursor,
    administrative_credit cursor < fuel -> seek_row fuel cursor <> SeekBudgetExhausted.
  Proof.
    induction fuel as [|fuel IH]; intros cursor Hcredit; [lia|]. cbn [seek_row].
    destruct (inspect_cursor cursor) as [after|first| |packing fault] eqn:Hinspect;
      try discriminate. apply IH.
    assert (Hdecrease : administrative_credit cursor = S (administrative_credit after)).
    { now apply each_administrative_step_consumes_one_credit. } lia.
  Qed.

  Theorem seeking_a_row_preserves_its_exact_continuation : forall fuel before after first,
    seek_row fuel before = SeekReady after first ->
    remaining_rows before = remaining_rows after /\ inspect_cursor after = RowReady first.
  Proof.
    induction fuel as [|fuel IH]; intros before after first Hseek; [discriminate|].
    cbn [seek_row] in Hseek.
    destruct (inspect_cursor before) as [next|current| |packing fault] eqn:Hinspect;
      try discriminate.
    - destruct (IH next after first Hseek) as [Hrows Hready]. split; [|exact Hready].
      assert (Hsame : remaining_rows before = remaining_rows next).
      { now apply administrative_steps_preserve_the_exact_remaining_rows. }
      now rewrite Hsame.
    - inversion Hseek; subst. split; [reflexivity|exact Hinspect].
  Qed.

  Theorem a_ready_row_does_not_inspect_future_packings : forall pending first rest,
    inspect_cursor {| pending_packings := pending; current_rows := Some (first :: rest) |} =
      RowReady first.
  Proof. reflexivity. Qed.
End PackingCursor.

Section ExecutableWitnesses.
  Definition prepare_example (packing : nat) : nat + list nat :=
    match packing with
    | 0 => inr []
    | 1 => inr [7; 8]
    | _ => inl 99
    end.

  Example zero_flat_packings_are_skipped_with_finite_credit :
    seek_row prepare_example 6 {| pending_packings := [0; 0; 1]; current_rows := None |} =
      SeekReady {| pending_packings := []; current_rows := Some [7; 8] |} 7.
  Proof. vm_compute. reflexivity. Qed.

  Example pending_preparation_failure_does_not_hide_a_ready_row :
    inspect_cursor prepare_example {| pending_packings := [2]; current_rows := Some [7] |} =
      RowReady 7.
  Proof. vm_compute. reflexivity. Qed.

  Example eager_ghost_expansion_would_observe_the_future_failure :
    remaining_rows prepare_example {| pending_packings := [2]; current_rows := Some [7] |} = inl 99.
  Proof. vm_compute. reflexivity. Qed.

  Example future_failure_is_reported_only_after_the_current_rows :
    seek_row prepare_example 2 {| pending_packings := [2]; current_rows := Some [] |} =
      SeekPreparationFailed 2 99.
  Proof. vm_compute. reflexivity. Qed.
End ExecutableWitnesses.

Print Assumptions administrative_steps_preserve_the_exact_remaining_rows.
Print Assumptions each_administrative_step_consumes_one_credit.
Print Assumptions consuming_a_ready_row_removes_exactly_one_ordered_occurrence.
Print Assumptions exhausted_cursor_has_no_unvisited_rows_or_packings.
Print Assumptions preparation_failure_identifies_the_next_unvisited_packing.
Print Assumptions bounded_seek_cannot_loop_on_empty_packings.
Print Assumptions seeking_a_row_preserves_its_exact_continuation.
