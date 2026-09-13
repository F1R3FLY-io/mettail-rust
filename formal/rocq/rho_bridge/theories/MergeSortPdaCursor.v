(** Source projection for runtime/src/collection_cmp_pda.rs.

    MergeSortPda keeps the current-pass source immutable and overwrites flat
    target slots at output. Readiness requests source[left/right]; accept
    copies left for Less/Equal and right for Greater. Tail loops perform
    the same indexed copies without requesting comparisons.

    This model covers indexed replacement, copied prefix, cursor progress and
    reset/saturated-width arithmetic. A run/pass simulation is still required
    for whole-sort correctness. Only the completed target prefix is meaningful
    during a pass; partially overwritten scratch need not be a permutation.
    Allocation, disposal and admission remain in the existing ownership model.

    Natural-number ceilings model usize saturation, with source length bounded
    by the ceiling. Logical list replacement describes indexed overwrite on
    its proved valid domain, not runtime list copying or allocator/CPU cost.
    None outside that domain is a specification sentinel, not a Rust policy. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Module MergeSortPdaCursor.

Section IndexedReplacement.
Context {Entry : Type}.
Fixpoint overwrite (index : nat) (value : Entry) (items : list Entry)
    : option (list Entry) :=
  match index, items with
  | _, [] => None
  | 0, _ :: rest => Some (value :: rest)
  | S smaller, head :: rest => option_map (cons head) (overwrite smaller value rest)
  end.

Theorem bounded_overwrite_preserves_length_and_exact_prefix :
  forall index value items, index < length items ->
  exists next, overwrite index value items = Some next /\
    length next = length items /\
    firstn (S index) next = firstn index items ++ [value] /\
    firstn index next = firstn index items.
Proof.
  induction index as [|index IH]; intros value [|head rest] HB;
    cbn [length] in HB; try lia.
  - exists (value :: rest). repeat split; reflexivity.
  - destruct (IH value rest ltac:(lia)) as [next [HU [HL [HP HK]]]].
    exists (head :: next). split.
    + cbn [overwrite]. now rewrite HU.
    + split.
      * cbn [length]. now rewrite HL.
      * split.
        -- change (head :: firstn (S index) next =
             head :: (firstn index rest ++ [value])). now rewrite HP.
        -- change (head :: firstn index next = head :: firstn index rest).
           now rewrite HK.
Qed.
End IndexedReplacement.

Record Cursor := {
  run_start : nat; run_middle : nat; run_end : nat;
  left_index : nat; right_index : nat; output_index : nat
}.
Definition valid_cursor width cursor :=
  run_start cursor <= left_index cursor /\
  left_index cursor <= run_middle cursor /\
  run_middle cursor <= right_index cursor /\
  right_index cursor <= run_end cursor /\ run_end cursor <= width /\
  output_index cursor = run_start cursor +
    (left_index cursor - run_start cursor) + (right_index cursor - run_middle cursor).
Inductive Side := FromLeft | FromRight.
Definition selected_index side cursor := match side with
  | FromLeft => left_index cursor | FromRight => right_index cursor end.
Definition can_copy side cursor := match side with
  | FromLeft => left_index cursor < run_middle cursor
  | FromRight => right_index cursor < run_end cursor end.
Definition remaining cursor :=
  (run_middle cursor - left_index cursor) + (run_end cursor - right_index cursor).
Definition advance side cursor :=
  {| run_start := run_start cursor; run_middle := run_middle cursor;
     run_end := run_end cursor;
     left_index := match side with FromLeft => S (left_index cursor)
                   | FromRight => left_index cursor end;
     right_index := match side with FromLeft => right_index cursor
                    | FromRight => S (right_index cursor) end;
     output_index := S (output_index cursor) |}.

Theorem enabled_copy_has_valid_source_and_target_indices : forall width cursor side,
  valid_cursor width cursor -> can_copy side cursor ->
  selected_index side cursor < width /\ output_index cursor < width.
Proof.
  intros width cursor side HV HC. unfold valid_cursor in HV.
  destruct side; cbn [can_copy selected_index] in *; lia.
Qed.
Theorem copy_advances_one_record_and_preserves_cursor : forall width cursor side,
  valid_cursor width cursor -> can_copy side cursor ->
  valid_cursor width (advance side cursor) /\
  output_index (advance side cursor) = S (output_index cursor) /\
  remaining cursor = S (remaining (advance side cursor)).
Proof.
  intros width cursor side HV HC. unfold valid_cursor in HV.
  destruct side; unfold can_copy in HC;
    unfold valid_cursor, remaining, advance;
    cbn [run_start run_middle run_end left_index right_index output_index];
    repeat split; lia.
Qed.

Section SourceCopy.
Context {Entry : Type}.
Definition copy_record side cursor (source target : list Entry) :=
  match nth_error source (selected_index side cursor) with
  | None => None
  | Some value => option_map (fun next => (advance side cursor, next))
      (overwrite (output_index cursor) value target)
  end.

Theorem source_indexed_copy_preserves_the_completed_prefix :
  forall width cursor side (source target : list Entry),
  length source = width -> length target = width ->
  valid_cursor width cursor -> can_copy side cursor ->
  exists value next,
    nth_error source (selected_index side cursor) = Some value /\
    copy_record side cursor source target = Some (advance side cursor, next) /\
    length next = width /\
    firstn (output_index cursor) next = firstn (output_index cursor) target /\
    firstn (output_index (advance side cursor)) next =
      firstn (output_index cursor) target ++ [value] /\
    valid_cursor width (advance side cursor) /\
    remaining cursor = S (remaining (advance side cursor)).
Proof.
  intros width cursor side source target LS LT HV HC.
  destruct (enabled_copy_has_valid_source_and_target_indices width cursor side HV HC)
    as [HS HO].
  destruct (nth_error source (selected_index side cursor)) as [value|] eqn:HN.
  - destruct (bounded_overwrite_preserves_length_and_exact_prefix
      (output_index cursor) value target ltac:(lia)) as [next [HU [HL [HP HK]]]].
    destruct (copy_advances_one_record_and_preserves_cursor width cursor side HV HC)
      as [HNEXT [HOUT HREM]].
    exists value, next. split; [reflexivity|]. split.
    + unfold copy_record. rewrite HN, HU. reflexivity.
    + split; [lia|]. split; [exact HK|]. split.
      * rewrite HOUT. exact HP.
      * split; assumption.
  - apply nth_error_None in HN. lia.
Qed.
End SourceCopy.

Definition accept_side ordering := match ordering with
  | Gt => FromRight | Eq | Lt => FromLeft end.
Theorem native_accept_less_and_equal_both_select_left :
  accept_side Lt = FromLeft /\ accept_side Eq = FromLeft /\ accept_side Gt = FromRight.
Proof. repeat split; reflexivity. Qed.

Definition saturated_add maximum lhs rhs := Nat.min (lhs + rhs) maximum.
Definition saturated_double maximum width := Nat.min (2 * width) maximum.
Definition middle_boundary maximum size start width :=
  Nat.min (saturated_add maximum start width) size.
Definition end_boundary maximum size start width :=
  Nat.min (saturated_add maximum start (saturated_double maximum width)) size.

Lemma clipping_to_source_absorbs_saturation : forall maximum size value,
  size <= maximum -> Nat.min (Nat.min value maximum) size = Nat.min value size.
Proof.
  intros maximum size value HB. destruct (Nat.le_ge_cases value maximum) as [HV|HV].
  - now rewrite (Nat.min_l value maximum HV).
  - rewrite (Nat.min_r value maximum HV),
      (Nat.min_r maximum size HB), (Nat.min_r value size ltac:(lia)). reflexivity.
Qed.
Theorem middle_boundary_is_the_exact_clipped_run_boundary : forall maximum size start width,
  size <= maximum -> middle_boundary maximum size start width = Nat.min (start + width) size.
Proof.
  intros. unfold middle_boundary, saturated_add.
  now apply clipping_to_source_absorbs_saturation.
Qed.
Theorem end_boundary_is_the_exact_clipped_double_run_boundary : forall maximum size start width,
  size <= maximum -> end_boundary maximum size start width = Nat.min (start + 2 * width) size.
Proof.
  intros maximum size start width HB. unfold end_boundary, saturated_add, saturated_double.
  rewrite clipping_to_source_absorbs_saturation by exact HB.
  destruct (Nat.le_ge_cases (2 * width) maximum) as [HW|HW].
  - now rewrite (Nat.min_l (2 * width) maximum HW).
  - rewrite (Nat.min_r (2 * width) maximum HW),
      (Nat.min_r (start + maximum) size ltac:(lia)),
      (Nat.min_r (start + 2 * width) size ltac:(lia)). reflexivity.
Qed.

Lemma clipped_run_boundaries_are_ordered : forall size start width,
  start <= size -> start <= Nat.min (start + width) size /\
  Nat.min (start + width) size <= Nat.min (start + 2 * width) size /\
  Nat.min (start + 2 * width) size <= size.
Proof.
  intros size start width HB.
  destruct (Nat.le_ge_cases (start + width) size) as [HM|HM];
    destruct (Nat.le_ge_cases (start + 2 * width) size) as [HE|HE].
  - rewrite (Nat.min_l _ _ HM), (Nat.min_l _ _ HE). lia.
  - rewrite (Nat.min_l _ _ HM), (Nat.min_r (start + 2 * width) size HE). lia.
  - rewrite (Nat.min_r (start + width) size HM), (Nat.min_l (start + 2 * width) size HE). lia.
  - rewrite (Nat.min_r (start + width) size HM), (Nat.min_r (start + 2 * width) size HE). lia.
Qed.
Definition reset_cursor maximum size start width :=
  {| run_start := start; run_middle := middle_boundary maximum size start width;
     run_end := end_boundary maximum size start width; left_index := start;
     right_index := middle_boundary maximum size start width; output_index := start |}.
Theorem reset_initializes_a_valid_empty_output_run : forall maximum size start width,
  size <= maximum -> start <= size -> valid_cursor size (reset_cursor maximum size start width).
Proof.
  intros maximum size start width HB HS.
  pose proof (clipped_run_boundaries_are_ordered size start width HS).
  unfold valid_cursor, reset_cursor.
  cbn [run_start run_middle run_end left_index right_index output_index].
  rewrite middle_boundary_is_the_exact_clipped_run_boundary by exact HB.
  rewrite end_boundary_is_the_exact_clipped_double_run_boundary by exact HB.
  repeat split; lia.
Qed.
Theorem doubled_width_progresses_and_is_exact_before_another_pass :
  forall maximum size width, size <= maximum -> 0 < width -> width < size ->
  width < saturated_double maximum width /\
  (saturated_double maximum width < size -> saturated_double maximum width = 2 * width).
Proof.
  intros maximum size width HB HP HW. unfold saturated_double.
  destruct (Nat.le_ge_cases (2 * width) maximum) as [HD|HD].
  - rewrite (Nat.min_l _ _ HD). lia.
  - rewrite (Nat.min_r (2 * width) maximum HD). lia.
Qed.
Theorem saturated_finish_test_matches_mathematical_doubling : forall maximum size width,
  size <= maximum -> (size <= saturated_double maximum width <-> size <= 2 * width).
Proof.
  intros maximum size width HB. unfold saturated_double.
  destruct (Nat.le_ge_cases (2 * width) maximum) as [HD|HD].
  - now rewrite (Nat.min_l _ _ HD).
  - rewrite (Nat.min_r (2 * width) maximum HD). lia.
Qed.

Print Assumptions bounded_overwrite_preserves_length_and_exact_prefix.
Print Assumptions enabled_copy_has_valid_source_and_target_indices.
Print Assumptions copy_advances_one_record_and_preserves_cursor.
Print Assumptions source_indexed_copy_preserves_the_completed_prefix.
Print Assumptions native_accept_less_and_equal_both_select_left.
Print Assumptions middle_boundary_is_the_exact_clipped_run_boundary.
Print Assumptions end_boundary_is_the_exact_clipped_double_run_boundary.
Print Assumptions reset_initializes_a_valid_empty_output_run.
Print Assumptions doubled_width_progresses_and_is_exact_before_another_pass.
Print Assumptions saturated_finish_test_matches_mathematical_doubling.
End MergeSortPdaCursor.
