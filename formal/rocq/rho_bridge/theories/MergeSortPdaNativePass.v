(** Successful absolute-buffer pass boundaries of the existing PDA.

    Source remains immutable until the outer caller swaps buffers. Each run
    begins at the native reset cursor and recurses at its actual final end,
    passing the exact physical target from one run to the next. The relation
    contains no assumed pass/sort-equivalence premise. Projection proves the
    entire final target equals its original completed prefix plus the sorted
    suffix; the terminal target-length equality closes the full-write boundary.
    Proof fuel measures the remaining source suffix, not a new runtime budget.
    Admission refusal and pending-driver liveness remain separate contracts. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaRun
  MergeSortPdaNativeRun MergeSortPdaPass.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import MergeSortPdaRun.MergeSortPdaRun.
Import MergeSortPdaNativeRun.MergeSortPdaNativeRun.
Import MergeSortPdaPass.MergeSortPdaPass.

Module MergeSortPdaNativePass.
Section NativePass.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Inductive IndexedPassExecution (maximum width : nat) (source : list Entry) :
    nat -> list Entry -> State -> list Entry -> State -> Prop :=
| IndexedPassDone : forall target state,
    IndexedPassExecution maximum width source (length source) target state target state
| IndexedPassMore : forall start target state count final_cursor next next_state final_target last,
    start < length source ->
    IndexedRunExecution compare source count
      (reset_cursor maximum (length source) start width) target state
      final_cursor next next_state ->
    IndexedPassExecution maximum width source (run_end final_cursor)
      next next_state final_target last ->
    IndexedPassExecution maximum width source start target state final_target last.

Lemma positive_run_end_strictly_advances : forall maximum size start width,
  size <= maximum -> start < size -> 0 < width ->
  start < end_boundary maximum size start width /\
  end_boundary maximum size start width <= size.
Proof.
  intros maximum size start width HM HS HW.
  rewrite end_boundary_is_the_exact_clipped_double_run_boundary by exact HM.
  destruct (Nat.le_ge_cases (start + 2 * width) size) as [HE|HE].
  - rewrite (Nat.min_l _ _ HE). split; lia.
  - rewrite (Nat.min_r _ _ HE). split; lia.
Qed.
Lemma strict_start_has_a_nonempty_source_suffix : forall start (source : list Entry),
  start < length source -> skipn start source <> [].
Proof.
  intros start source HS HE.
  pose proof (length_skipn start source) as HL.
  rewrite HE in HL. cbn in HL. lia.
Qed.

Theorem indexed_pass_projects_the_existing_pass_and_exact_global_prefix :
  forall maximum width source,
  length source <= maximum -> 0 < width ->
  forall start target state final_target last,
  IndexedPassExecution maximum width source start target state final_target last ->
  length target = length source ->
  exists suffix,
    PassExecution compare width (skipn start source) state suffix last /\
    final_target = firstn start target ++ suffix /\
    length final_target = length source.
Proof.
  intros maximum width source HMAX HW start target state final_target last HP.
  induction HP as [target state
    |start target state count final_cursor next next_state final_target last HSTART HR HP IH];
    intros LT.
  - exists []. split.
    + rewrite skipn_all. constructor.
    + split; [rewrite <- LT, firstn_all, app_nil_r; reflexivity|exact LT].
  - assert (HV : valid_cursor (length source)
        (reset_cursor maximum (length source) start width)).
    { apply reset_initializes_a_valid_empty_output_run; [exact HMAX|lia]. }
    destruct (@indexed_run_projects_RunExecution_and_preserves_buffers
      Entry State compare source count
      (reset_cursor maximum (length source) start width) target state
      final_cursor next next_state HR (length source) (eq_refl _) LT HV)
      as [RUN [LN [VN [END OUT]]]].
    destruct (@run_execution_strips_its_existing_output_prefix
      Entry State compare _ _ _ _ _ _ _ RUN) as [merged [REL GLOBAL]].
    assert (OUTEND : output_index final_cursor = run_end final_cursor) by congruence.
    rewrite OUTEND in GLOBAL.
    cbn [reset_cursor output_index] in GLOBAL.
    cbn [reset_cursor run_end] in END.
    rewrite (reset_left_is_the_first_source_run maximum source start width HMAX ltac:(lia)),
      (reset_right_is_the_second_source_run maximum source start width HMAX ltac:(lia)) in REL.
    destruct (IH LN) as [suffix [PASS [FINAL LF]]].
    rewrite END, (source_after_run_end_is_the_double_skip_suffix
      maximum source start width HMAX) in PASS.
    exists (merged ++ suffix). split.
    + destruct (skipn start source) as [|head tail] eqn:HSUFF in REL, PASS |- *.
      * exfalso. exact (strict_start_has_a_nonempty_source_suffix start source HSTART HSUFF).
      * eapply PassMore; eassumption.
    + split.
      * rewrite FINAL, GLOBAL, <- app_assoc. reflexivity.
      * exact LF.
Qed.

Corollary actual_start_zero_pass_has_the_exact_physical_output :
  forall maximum width source target state final_target last,
  length source <= maximum -> 0 < width -> length target = length source ->
  IndexedPassExecution maximum width source 0 target state final_target last ->
  PassExecution compare width source state final_target last /\
  length final_target = length source.
Proof.
  intros maximum width source target state final_target last HM HW LT HP.
  destruct (indexed_pass_projects_the_existing_pass_and_exact_global_prefix
    maximum width source HM HW 0 target state final_target last HP LT)
    as [suffix [PASS [FINAL LF]]].
  cbn [skipn firstn] in PASS, FINAL. subst final_target. split; assumption.
Qed.

Lemma responding_driver_constructs_an_indexed_pass_with_sufficient_suffix_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum width source,
  length source <= maximum -> 0 < width ->
  forall fuel start target state,
  start <= length source -> length source - start <= fuel ->
  length target = length source ->
  exists final_target last,
    IndexedPassExecution maximum width source start target state final_target last.
Proof.
  intros TOTAL maximum width source HMAX HW fuel.
  induction fuel as [|fuel IH]; intros start target state HS HF LT.
  - assert (start = length source) by lia. subst start.
    exists target, state. constructor.
  - destruct (Nat.eq_dec start (length source)) as [DONE|MORE].
    + subst start. exists target, state. constructor.
    + assert (HSTART : start < length source) by lia.
      assert (HV : valid_cursor (length source)
          (reset_cursor maximum (length source) start width)).
      { apply reset_initializes_a_valid_empty_output_run; assumption. }
      destruct (@responding_driver_completes_the_actual_indexed_run
        Entry State compare TOTAL (length source) source
        (reset_cursor maximum (length source) start width) target state
        (eq_refl _) LT HV) as [final_cursor [next [next_state HR]]].
      destruct (@indexed_run_projects_RunExecution_and_preserves_buffers
        Entry State compare source
        (remaining (reset_cursor maximum (length source) start width))
        (reset_cursor maximum (length source) start width) target state
        final_cursor next next_state HR (length source) (eq_refl _) LT HV)
        as [RUN [LN [VN [END OUT]]]].
      cbn [reset_cursor run_end] in END.
      destruct (positive_run_end_strictly_advances
        maximum (length source) start width HMAX HSTART HW) as [ADV BOUND].
      destruct (IH (run_end final_cursor) next next_state ltac:(lia) ltac:(lia) LN)
        as [final_target [last HP]].
      exists final_target, last.
      eapply IndexedPassMore; [exact HSTART|exact HR|exact HP].
Qed.
Theorem responding_driver_completes_the_actual_indexed_pass :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum width source start target state,
  length source <= maximum -> 0 < width -> start <= length source ->
  length target = length source ->
  exists final_target last,
    IndexedPassExecution maximum width source start target state final_target last.
Proof.
  intros TOTAL maximum width source start target state HM HW HS LT.
  exact (responding_driver_constructs_an_indexed_pass_with_sufficient_suffix_fuel
    TOTAL maximum width source HM HW (length source - start)
    start target state HS (Nat.le_refl _) LT).
Qed.
End NativePass.

Print Assumptions positive_run_end_strictly_advances.
Print Assumptions strict_start_has_a_nonempty_source_suffix.
Print Assumptions indexed_pass_projects_the_existing_pass_and_exact_global_prefix.
Print Assumptions actual_start_zero_pass_has_the_exact_physical_output.
Print Assumptions responding_driver_constructs_an_indexed_pass_with_sufficient_suffix_fuel.
Print Assumptions responding_driver_completes_the_actual_indexed_pass.
End MergeSortPdaNativePass.
