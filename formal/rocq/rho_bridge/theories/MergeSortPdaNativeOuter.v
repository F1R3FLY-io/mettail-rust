(** Complete successful native buffer lifecycle, refining the existing sort.

    This boundary relation starts at the initial width=1 or immediately after
    a pass swap. Done is tested before obtaining scratch: zero/one inputs keep
    None. A nonfinished first pass uses the existing flat source clone; later
    passes reuse Some(target) verbatim. Each actual indexed pass overwrites
    the entire target, then recursion uses that result as source and retains
    Some(old source) as scratch, exactly as mem::swap.

    The final Done denotes the reached break branch, not an additional native
    step, guard or reset. Only continuing passes reset at start zero through
    IndexedPassExecution. Initial new/reset, admission before scratch cloning,
    waiting/refusal protocol and final release_scratch remain separately
    accounted source operations. No runtime sorter or extra allocation is
    introduced by these proof-only buffer values and transition traces. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaNativePass MergeSortPdaOuter.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import MergeSortPdaNativePass.MergeSortPdaNativePass.
Import MergeSortPdaOuter.MergeSortPdaOuter.

Module MergeSortPdaNativeOuter.
Section Lifecycle.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Definition scratch_valid (source : list Entry) (scratch : option (list Entry)) :=
  match scratch with None => True | Some target => length target = length source end.
Definition scratch_payload (source : list Entry) (scratch : option (list Entry)) :=
  match scratch with None => source | Some target => target end.
Lemma valid_scratch_payload_has_source_width : forall source scratch,
  scratch_valid source scratch -> length (scratch_payload source scratch) = length source.
Proof. intros source [target|] HS; exact HS || reflexivity. Qed.

Inductive NativeOuterExecution (maximum : nat) : nat -> nat -> list Entry ->
    option (list Entry) -> State -> list Entry -> option (list Entry) -> State -> Prop :=
| NativeOuterDone : forall width source scratch state,
    length source <= width ->
    NativeOuterExecution maximum 0 width source scratch state source scratch state
| NativeOuterPass : forall count width source scratch state completed next output final_scratch last,
    width < length source ->
    IndexedPassExecution compare maximum width source 0
      (scratch_payload source scratch) state completed next ->
    NativeOuterExecution maximum count (saturated_double maximum width)
      completed (Some source) next output final_scratch last ->
    NativeOuterExecution maximum (S count) width source scratch state output final_scratch last.

Theorem actual_buffer_lifecycle_projects_to_the_existing_outer_trace :
  forall maximum count width source scratch state output final_scratch last,
  NativeOuterExecution maximum count width source scratch state output final_scratch last ->
  0 < width -> length source <= maximum -> scratch_valid source scratch ->
  OuterExecution compare maximum count width source state output last /\
  length output = length source /\ scratch_valid output final_scratch.
Proof.
  intros maximum count width source scratch state output final_scratch last HE.
  induction HE as [width source scratch state HD
    |count width source scratch state completed next output final_scratch last HL HP HE IH];
    intros HW HM HS.
  - split; [now apply OuterDone|]. split; [reflexivity|exact HS].
  - destruct (@actual_start_zero_pass_has_the_exact_physical_output Entry State compare
      maximum width source (scratch_payload source scratch) state completed next HM HW
      (valid_scratch_payload_has_source_width source scratch HS) HP) as [PASS LEN].
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length source) width HM HW HL) as [GROW _].
    assert (NEXT_SCRATCH : scratch_valid completed (Some source)).
    { unfold scratch_valid. symmetry. exact LEN. }
    destruct (IH ltac:(lia) ltac:(lia) NEXT_SCRATCH) as [OUTER [OUTLEN OUTSCRATCH]].
    split.
    + eapply OuterPass; eassumption.
    + split; [lia|exact OUTSCRATCH].
Qed.

Theorem actual_native_sort_has_the_existing_sort_result :
  forall maximum count source state output final_scratch last,
  length source <= maximum ->
  NativeOuterExecution maximum count 1 source None state output final_scratch last ->
  @SemanticResultMerge.SemanticResultMerge.sort Entry State compare source state = (Some output, last).
Proof.
  intros maximum count source state output final_scratch last HM HE.
  destruct (actual_buffer_lifecycle_projects_to_the_existing_outer_trace
    maximum count 1 source None state output final_scratch last HE ltac:(lia) HM I)
    as [OUTER REST].
  exact (@MergeSortPdaOuter.MergeSortPdaOuter.completed_source_sort_is_the_existing_sort
    Entry State compare maximum count source state output last HM OUTER).
Qed.

Theorem zero_and_one_native_sorts_do_not_create_scratch : forall maximum state (entry : Entry),
  NativeOuterExecution maximum 0 1 [] None state [] None state /\
  NativeOuterExecution maximum 0 1 [entry] None state [entry] None state.
Proof. intros. split; apply NativeOuterDone; cbn [length]; lia. Qed.

Lemma responding_driver_constructs_native_outer_with_sufficient_width_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum fuel width source scratch state,
  0 < width -> length source <= maximum -> scratch_valid source scratch ->
  length source <= width + fuel ->
  exists count output final_scratch last,
    NativeOuterExecution maximum count width source scratch state output final_scratch last.
Proof.
  intros TOTAL maximum fuel. induction fuel as [|fuel IH];
    intros width source scratch state HW HM HS HF;
    destruct (length source <=? width) eqn:HD.
  - apply Nat.leb_le in HD. exists 0, source, scratch, state. now apply NativeOuterDone.
  - apply Nat.leb_gt in HD. lia.
  - apply Nat.leb_le in HD. exists 0, source, scratch, state. now apply NativeOuterDone.
  - apply Nat.leb_gt in HD.
    destruct (@responding_driver_completes_the_actual_indexed_pass Entry State compare TOTAL
      maximum width source 0 (scratch_payload source scratch) state HM HW ltac:(lia)
      (valid_scratch_payload_has_source_width source scratch HS)) as [completed [next PASS]].
    destruct (@actual_start_zero_pass_has_the_exact_physical_output Entry State compare
      maximum width source (scratch_payload source scratch) state completed next HM HW
      (valid_scratch_payload_has_source_width source scratch HS) PASS) as [ABSTRACT LEN].
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length source) width HM HW HD) as [GROW _].
    assert (NEXT_SCRATCH : scratch_valid completed (Some source)).
    { unfold scratch_valid. symmetry. exact LEN. }
    destruct (IH (saturated_double maximum width) completed (Some source) next
      ltac:(lia) ltac:(lia) NEXT_SCRATCH ltac:(lia)) as [count [output [final_scratch [last OUTER]]]].
    exists (S count), output, final_scratch, last.
    eapply NativeOuterPass; eassumption.
Qed.

Theorem responding_driver_completes_the_actual_native_sort :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum source state, length source <= maximum ->
  exists count output final_scratch last,
    NativeOuterExecution maximum count 1 source None state output final_scratch last /\
    count <= length source /\
    @SemanticResultMerge.SemanticResultMerge.sort Entry State compare source state = (Some output, last).
Proof.
  intros TOTAL maximum source state HM.
  destruct (responding_driver_constructs_native_outer_with_sufficient_width_fuel TOTAL
    maximum (length source) 1 source None state ltac:(lia) HM I ltac:(lia))
    as [count [output [final_scratch [last NATIVE]]]].
  destruct (actual_buffer_lifecycle_projects_to_the_existing_outer_trace
    maximum count 1 source None state output final_scratch last NATIVE ltac:(lia) HM I)
    as [OUTER REST].
  exists count, output, final_scratch, last. split; [exact NATIVE|]. split.
  - pose proof (@MergeSortPdaOuter.MergeSortPdaOuter.source_outer_progress_bounds_the_number_of_passes
      Entry State compare maximum count 1 source state output last OUTER ltac:(lia) HM). lia.
  - exact (actual_native_sort_has_the_existing_sort_result
      maximum count source state output final_scratch last HM NATIVE).
Qed.
End Lifecycle.

Print Assumptions valid_scratch_payload_has_source_width.
Print Assumptions actual_buffer_lifecycle_projects_to_the_existing_outer_trace.
Print Assumptions actual_native_sort_has_the_existing_sort_result.
Print Assumptions zero_and_one_native_sorts_do_not_create_scratch.
Print Assumptions responding_driver_constructs_native_outer_with_sufficient_width_fuel.
Print Assumptions responding_driver_completes_the_actual_native_sort.
End MergeSortPdaNativeOuter.
