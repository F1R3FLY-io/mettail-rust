(** Outer-loop projection for the existing MergeSortPda.

    new sets width=1 and done=(len<2); zero/one bypass scratch and all passes.
    A completed pass overwrites every target slot, then mem::swap publishes
    that target as source and retains the old source as scratch. Native width
    uses saturating_mul(2). Before another pass this equals mathematical
    doubling; at completion both widths satisfy the same finish predicate
    because source length is bounded by usize maximum.

    OuterExecution is a proof boundary trace, not an executable replacement
    sorter. OuterDone represents the reached initial/post-swap finish branch;
    it does not add a charged loop test after break. Its PassExecution premise
    must be supplied through the indexed-run and absolute-buffer pass bridge.
    It is not an assumption equating an arbitrary PDA with a sorter.

    Buffer IDs identify storage occurrences. Prepaid ownership and cleanup
    remain in AdmittedCollectionComparisonOwnership. This file adds no credits,
    allocator model or equal-comparator-trace claim for different sorters.
    Logical comparison state is separate from admission accounting. Concrete
    supported-Proc comparison-class factorization remains a separate obligation. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Sorting.Sorted Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaPass.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor MergeSortPdaPass.MergeSortPdaPass.

Module MergeSortPdaOuter.
Section BufferSwap.
Context {Entry : Type}.
Definition publish_pass_swap (source_id target_id : nat) (source output : list Entry) :=
  ((target_id, output), (source_id, source)).
Theorem completed_pass_swap_publishes_only_the_completed_target :
  forall source_id target_id (source output : list Entry),
  snd (fst (publish_pass_swap source_id target_id source output)) = output /\
  snd (snd (publish_pass_swap source_id target_id source output)) = source.
Proof. intros; split; reflexivity. Qed.
Theorem pass_swap_preserves_the_two_storage_occurrences :
  forall source_id target_id (source output : list Entry),
  Permutation [source_id; target_id]
    [fst (fst (publish_pass_swap source_id target_id source output));
     fst (snd (publish_pass_swap source_id target_id source output))].
Proof. intros. cbn [publish_pass_swap]. apply perm_swap. Qed.
Definition initial_scratch_needed (source : list Entry) := 2 <=? length source.
Theorem zero_and_one_need_no_initial_scratch_pass : forall (entry : Entry),
  initial_scratch_needed [] = false /\ initial_scratch_needed [entry] = false.
Proof. intros; split; reflexivity. Qed.
End BufferSwap.

Section OuterProjection.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Lemma existing_passes_agrees_with_saturated_next_width :
  forall maximum fuel width (input : list Entry) state,
  length input <= maximum ->
  @SemanticResultMerge.SemanticResultMerge.passes Entry State compare
    fuel (saturated_double maximum width) input state =
  @SemanticResultMerge.SemanticResultMerge.passes Entry State compare
    fuel (2 * width) input state.
Proof.
  intros maximum fuel width input state HB. unfold saturated_double.
  destruct (Nat.le_ge_cases (2 * width) maximum) as [HD|HD].
  - now rewrite (Nat.min_l _ _ HD).
  - rewrite (Nat.min_r _ _ HD).
    assert (HM : (length input <=? maximum) = true) by (apply Nat.leb_le; exact HB).
    assert (HW : (length input <=? 2 * width) = true) by (apply Nat.leb_le; lia).
    destruct fuel; cbn [SemanticResultMerge.SemanticResultMerge.passes];
      rewrite HM, HW; reflexivity.
Qed.

Inductive OuterExecution (maximum : nat) : nat -> nat -> list Entry -> State ->
    list Entry -> State -> Prop :=
| OuterDone : forall width input state,
    length input <= width -> OuterExecution maximum 0 width input state input state
| OuterPass : forall count width input state intermediate next output last,
    width < length input ->
    @MergeSortPdaPass.MergeSortPdaPass.PassExecution Entry State compare
      width input state intermediate next ->
    OuterExecution maximum count (saturated_double maximum width) intermediate next output last ->
    OuterExecution maximum (S count) width input state output last.

Theorem source_outer_progress_bounds_the_number_of_passes :
  forall maximum count width input state output last,
  OuterExecution maximum count width input state output last ->
  0 < width -> length input <= maximum -> count <= length input - width.
Proof.
  intros maximum count width input state output last HE.
  induction HE as [width input state HD
    |count width input state intermediate next output last HL HP HE IH]; intros HW HB.
  - lia.
  - pose proof (@MergeSortPdaPass.MergeSortPdaPass.completed_source_pass_preserves_the_allocated_width
      Entry State compare width input state intermediate next HW HP) as HLEN.
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length input) width HB HW HL) as [HG _].
    specialize (IH ltac:(lia) ltac:(lia)).
    destruct (Nat.le_ge_cases (saturated_double maximum width) (length input)); lia.
Qed.
Theorem completed_source_outer_loop_is_the_existing_passes :
  forall maximum count width input state output last,
  OuterExecution maximum count width input state output last ->
  forall fuel, 0 < width -> length input <= maximum -> count <= fuel ->
  @SemanticResultMerge.SemanticResultMerge.passes Entry State compare fuel width input state =
    (Some output, last).
Proof.
  intros maximum count width input state output last HE.
  induction HE as [width input state HD
    |count width input state intermediate next output last HL HP HE IH]; intros fuel HW HB HF.
  - assert (HT : (length input <=? width) = true) by (apply Nat.leb_le; exact HD).
    destruct fuel; cbn [SemanticResultMerge.SemanticResultMerge.passes]; now rewrite HT.
  - destruct fuel as [|fuel]; [lia|].
    assert (HT : (length input <=? width) = false) by (apply Nat.leb_gt; exact HL).
    pose proof (@MergeSortPdaPass.MergeSortPdaPass.completed_source_pass_is_the_existing_pass
      Entry State compare width HW input state intermediate next HP (length input) (Nat.le_refl _)) as HM.
    pose proof (@MergeSortPdaPass.MergeSortPdaPass.completed_source_pass_preserves_the_allocated_width
      Entry State compare width input state intermediate next HW HP) as HLEN.
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length input) width HB HW HL) as [HG _].
    cbn [SemanticResultMerge.SemanticResultMerge.passes]. rewrite HT, HM.
    rewrite <- (existing_passes_agrees_with_saturated_next_width
      maximum fuel width intermediate next ltac:(lia)).
    apply IH; lia.
Qed.
Theorem completed_source_sort_is_the_existing_sort :
  forall maximum count input state output last,
  length input <= maximum -> OuterExecution maximum count 1 input state output last ->
  @SemanticResultMerge.SemanticResultMerge.sort Entry State compare input state = (Some output, last).
Proof.
  intros maximum count input state output last HB HE.
  pose proof (source_outer_progress_bounds_the_number_of_passes
    maximum count 1 input state output last HE ltac:(lia) HB) as HC.
  unfold SemanticResultMerge.SemanticResultMerge.sort.
  eapply completed_source_outer_loop_is_the_existing_passes; [exact HE|lia|exact HB|lia].
Qed.
Theorem zero_and_one_source_sorts_bypass_all_passes :
  forall maximum state (entry : Entry),
  OuterExecution maximum 0 1 [] state [] state /\
  OuterExecution maximum 0 1 [entry] state [entry] state.
Proof. intros. split; apply OuterDone; cbn [length]; lia. Qed.

Lemma responding_driver_outer_progress_with_sufficient_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum fuel width input state,
  0 < width -> length input <= maximum -> length input <= width + fuel ->
  exists count output last, OuterExecution maximum count width input state output last.
Proof.
  intros total maximum fuel. induction fuel as [|fuel IH];
    intros width input state HW HB HF;
    destruct (length input <=? width) eqn:HD.
  - apply Nat.leb_le in HD. exists 0, input, state. now apply OuterDone.
  - apply Nat.leb_gt in HD. lia.
  - apply Nat.leb_le in HD. exists 0, input, state. now apply OuterDone.
  - apply Nat.leb_gt in HD.
    destruct (@MergeSortPdaPass.MergeSortPdaPass.responding_driver_completes_the_projected_pass
      Entry State compare total width input state HW) as [intermediate [next HP]].
    pose proof (@MergeSortPdaPass.MergeSortPdaPass.completed_source_pass_preserves_the_allocated_width
      Entry State compare width input state intermediate next HW HP) as HLEN.
    destruct (doubled_width_progresses_and_is_exact_before_another_pass
      maximum (length input) width HB HW HD) as [HG _].
    destruct (IH (saturated_double maximum width) intermediate next
      ltac:(lia) ltac:(lia) ltac:(lia)) as [count [output [last HE]]].
    exists (S count), output, last. eapply OuterPass; eassumption.
Qed.
Theorem responding_driver_completes_source_sort_with_a_bounded_pass_count :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall maximum input state, length input <= maximum ->
  exists count output last,
    OuterExecution maximum count 1 input state output last /\ count <= length input.
Proof.
  intros total maximum input state HB.
  destruct (responding_driver_outer_progress_with_sufficient_fuel total maximum
    (length input) 1 input state ltac:(lia) HB ltac:(lia)) as [count [output [last HE]]].
  exists count, output, last. split; [exact HE|].
  pose proof (source_outer_progress_bounds_the_number_of_passes
    maximum count 1 input state output last HE ltac:(lia) HB). lia.
Qed.
Theorem source_sort_preserves_each_whole_entry_occurrence :
  forall maximum count input state output last,
  length input <= maximum -> OuterExecution maximum count 1 input state output last ->
  Permutation input output.
Proof.
  intros maximum count input state output last HB HE.
  eapply (@SemanticResultMerge.SemanticResultMerge.sort_preserves_occurrences Entry State compare).
  exact (completed_source_sort_is_the_existing_sort maximum count input state output last HB HE).
Qed.
Theorem source_sort_inherits_existing_sortedness : forall (relation : Entry -> Entry -> Prop),
  (forall x y z, relation x y -> relation y z -> relation x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => relation y x | _ => relation x y end) ->
  forall maximum count input state output last,
  length input <= maximum -> OuterExecution maximum count 1 input state output last ->
  StronglySorted relation output.
Proof.
  intros relation trans sound maximum count input state output last HB HE.
  eapply (@SemanticResultMerge.SemanticResultMerge.sort_is_sorted Entry State compare
    relation trans sound).
  exact (completed_source_sort_is_the_existing_sort maximum count input state output last HB HE).
Qed.

(** Key equality can identify distinct source terms. No injectivity of view. *)
Theorem source_sort_inherits_existing_stable_class_subsequences :
  forall (Key : Type) (view : Entry -> Key) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y, order y x = CompOpp (order x y)) ->
  (forall x y z, order x y <> Gt -> order y z <> Gt -> order x z <> Gt) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (view x) (view y) = decision) ->
  forall maximum count input state output last wanted,
  length input <= maximum -> OuterExecution maximum count 1 input state output last ->
  filter (@SemanticResultMerge.SemanticResultMerge.has_key Entry Key view order wanted) output =
    filter (@SemanticResultMerge.SemanticResultMerge.has_key Entry Key view order wanted) input.
Proof.
  intros Key view order key_eq opposite trans faithful maximum count input state output last wanted HB HE.
  exact (@SemanticResultMerge.SemanticResultMerge.sort_preserves_equal_key_subsequence
    Entry State compare Key view order key_eq opposite trans faithful input state output last wanted
    (completed_source_sort_is_the_existing_sort maximum count input state output last HB HE)).
Qed.
End OuterProjection.

Print Assumptions completed_pass_swap_publishes_only_the_completed_target.
Print Assumptions pass_swap_preserves_the_two_storage_occurrences.
Print Assumptions zero_and_one_need_no_initial_scratch_pass.
Print Assumptions source_outer_progress_bounds_the_number_of_passes.
Print Assumptions completed_source_outer_loop_is_the_existing_passes.
Print Assumptions completed_source_sort_is_the_existing_sort.
Print Assumptions zero_and_one_source_sorts_bypass_all_passes.
Print Assumptions responding_driver_completes_source_sort_with_a_bounded_pass_count.
Print Assumptions source_sort_preserves_each_whole_entry_occurrence.
Print Assumptions source_sort_inherits_existing_sortedness.
Print Assumptions source_sort_inherits_existing_stable_class_subsequences.
End MergeSortPdaOuter.
