(** Source reset/run-end/pass assembly for the existing merge-sort PDA.

    reset_run clips start+width and start+2*width to the source length; its
    indexed runs are exactly firstn/skipn of the current unprocessed suffix.
    Each completed run appends whole records to the existing target prefix.
    start=end advances to exactly the double-skip suffix, which strictly
    shrinks for a positive width and nonempty source.

    PassExecution is a proof relation for those source run boundaries, not
    a runtime sorter. Its completed-run premise is the proved source Run
    projection, not an assumed pda_output=sort equation. The assembly proof
    gives the existing SemanticResultMerge.pass equation, enabling reuse of
    its occurrence, aligned-run-growth and stable-class-subsequence laws.
    Actual pass swaps/full-loop termination remain the final projection slice.
    No term Eq/Cmp coherence, admission-state identity or new cost model is used. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaRun.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor MergeSortPdaRun.MergeSortPdaRun.

Module MergeSortPdaPass.

Lemma clipped_offset_is_remaining_width : forall size start width,
  start <= size -> Nat.min (start + width) size - start = Nat.min width (size - start).
Proof.
  intros size start width HB. destruct (Nat.le_ge_cases (start + width) size) as [HW|HW].
  - rewrite (Nat.min_l _ _ HW), (Nat.min_l width (size - start) ltac:(lia)). lia.
  - rewrite (Nat.min_r _ _ HW), (Nat.min_r width (size - start) ltac:(lia)). reflexivity.
Qed.
Lemma clipped_two_run_end : forall size start width,
  Nat.min (Nat.min (start + width) size + width) size = Nat.min (start + 2 * width) size.
Proof.
  intros size start width. destruct (Nat.le_ge_cases (start + width) size) as [HW|HW].
  - rewrite (Nat.min_l _ _ HW). f_equal. lia.
  - rewrite (Nat.min_r _ _ HW),
      (Nat.min_r (size + width) size ltac:(lia)),
      (Nat.min_r (start + 2 * width) size ltac:(lia)). reflexivity.
Qed.

Section ResetSlices.
Context {Entry : Type}.
Lemma clipped_firstn : forall count (source : list Entry),
  firstn (Nat.min count (length source)) source = firstn count source.
Proof.
  intros count source. destruct (Nat.le_ge_cases count (length source)) as [HC|HC].
  - now rewrite (Nat.min_l _ _ HC).
  - rewrite (Nat.min_r _ _ HC), firstn_all, firstn_all2 by exact HC. reflexivity.
Qed.
Lemma clipped_skipn : forall count (source : list Entry),
  skipn (Nat.min count (length source)) source = skipn count source.
Proof.
  intros count source. destruct (Nat.le_ge_cases count (length source)) as [HC|HC].
  - now rewrite (Nat.min_l _ _ HC).
  - rewrite (Nat.min_r _ _ HC), skipn_all, skipn_all2 by exact HC. reflexivity.
Qed.
Lemma window_from_clipped_boundary : forall (source : list Entry) start width,
  start <= length source ->
  source_slice source start (Nat.min (start + width) (length source)) =
    firstn width (skipn start source).
Proof.
  intros source start width HB. unfold source_slice.
  rewrite clipped_offset_is_remaining_width by exact HB.
  rewrite <- (length_skipn start source). apply clipped_firstn.
Qed.
Theorem reset_left_is_the_first_source_run : forall maximum (source : list Entry) start width,
  length source <= maximum -> start <= length source ->
  left_slice source (reset_cursor maximum (length source) start width) =
    firstn width (skipn start source).
Proof.
  intros maximum source start width HB HS. unfold left_slice, reset_cursor.
  cbn [left_index run_middle].
  rewrite middle_boundary_is_the_exact_clipped_run_boundary by exact HB.
  now apply window_from_clipped_boundary.
Qed.
Theorem reset_right_is_the_second_source_run : forall maximum (source : list Entry) start width,
  length source <= maximum -> start <= length source ->
  right_slice source (reset_cursor maximum (length source) start width) =
    firstn width (skipn width (skipn start source)).
Proof.
  intros maximum source start width HB HS.
  destruct (clipped_run_boundaries_are_ordered (length source) start width HS) as [_ [HM HE]].
  unfold right_slice, reset_cursor. cbn [right_index run_end].
  rewrite middle_boundary_is_the_exact_clipped_run_boundary by exact HB.
  rewrite end_boundary_is_the_exact_clipped_double_run_boundary by exact HB.
  rewrite <- (clipped_two_run_end (length source) start width).
  rewrite window_from_clipped_boundary by lia.
  rewrite clipped_skipn, skipn_skipn. f_equal; f_equal; lia.
Qed.
Theorem source_after_run_end_is_the_double_skip_suffix :
  forall maximum (source : list Entry) start width,
  length source <= maximum ->
  skipn (end_boundary maximum (length source) start width) source =
    skipn width (skipn width (skipn start source)).
Proof.
  intros maximum source start width HB.
  rewrite end_boundary_is_the_exact_clipped_double_run_boundary by exact HB.
  rewrite clipped_skipn, !skipn_skipn. f_equal; lia.
Qed.
Theorem a_nonempty_positive_width_run_strictly_advances_the_source_suffix :
  forall width (head : Entry) tail, 0 < width ->
  length (skipn width (skipn width (head :: tail))) < length (head :: tail).
Proof. intros. rewrite !length_skipn. cbn [length]. lia. Qed.
End ResetSlices.

Section PassAssembly.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Theorem completed_run_appends_to_the_existing_pass_prefix :
  forall count prefix lhs rhs state final last,
  @MergeSortPdaRun.MergeSortPdaRun.RunExecution Entry State compare
    count prefix lhs rhs state final last ->
  exists merged,
    @SemanticResultMerge.SemanticResultMerge.merge Entry State compare
      (length lhs + length rhs) lhs rhs state = (Some merged, last) /\
    final = prefix ++ merged.
Proof.
  intros count prefix lhs rhs state final last HR.
  pose proof (@MergeSortPdaRun.MergeSortPdaRun.completed_source_run_is_the_existing_merge
    Entry State compare count prefix lhs rhs state final last HR) as HS.
  unfold run_result in HS.
  destruct (@SemanticResultMerge.SemanticResultMerge.merge Entry State compare
    (length lhs + length rhs) lhs rhs state) as [[merged|] next] eqn:HM;
    cbn [prefix_result] in HS; try discriminate.
  inversion HS; subst. exists merged. split; reflexivity.
Qed.

Theorem one_completed_run_and_suffix_are_the_existing_pass_clause :
  forall width fuel head tail state count merged next suffix last,
  @MergeSortPdaRun.MergeSortPdaRun.RunExecution Entry State compare count []
    (firstn width (head :: tail))
    (firstn width (skipn width (head :: tail))) state merged next ->
  @SemanticResultMerge.SemanticResultMerge.pass Entry State compare fuel width
    (skipn width (skipn width (head :: tail))) next = (Some suffix, last) ->
  @SemanticResultMerge.SemanticResultMerge.pass Entry State compare (S fuel) width
    (head :: tail) state = (Some (merged ++ suffix), last).
Proof.
  intros width fuel head tail state count merged next suffix last HR HT.
  pose proof (@MergeSortPdaRun.MergeSortPdaRun.completed_source_run_is_the_existing_merge
    Entry State compare count [] (firstn width (head :: tail))
    (firstn width (skipn width (head :: tail))) state merged next HR) as HM.
  unfold run_result in HM. rewrite prefix_result_empty in HM.
  cbn [SemanticResultMerge.SemanticResultMerge.pass]. now rewrite HM, HT.
Qed.

(** A boundary trace of the actual two-run resets and completed prefix copies.
    Prefixes here are relative to the current run; the theorem above recovers
    the previously completed global target prefix without reading it as input. *)
Inductive PassExecution (width : nat) : list Entry -> State -> list Entry -> State -> Prop :=
| PassEmpty : forall state, PassExecution width [] state [] state
| PassMore : forall head tail state count merged next suffix last,
    @MergeSortPdaRun.MergeSortPdaRun.RunExecution Entry State compare count []
      (firstn width (head :: tail))
      (firstn width (skipn width (head :: tail))) state merged next ->
    PassExecution width (skipn width (skipn width (head :: tail))) next suffix last ->
    PassExecution width (head :: tail) state (merged ++ suffix) last.

Theorem completed_source_pass_is_the_existing_pass :
  forall width, 0 < width -> forall input state output last,
  PassExecution width input state output last -> forall fuel, length input <= fuel ->
  @SemanticResultMerge.SemanticResultMerge.pass Entry State compare fuel width input state =
    (Some output, last).
Proof.
  intros width HW input state output last HP.
  induction HP as [state|head tail state count merged next suffix last HR HP IH]; intros fuel HF.
  - apply SemanticResultMerge.SemanticResultMerge.pass_nil.
  - destruct fuel as [|fuel]; [cbn [length] in HF; lia|].
    eapply one_completed_run_and_suffix_are_the_existing_pass_clause; [exact HR|].
    apply IH.
    pose proof (a_nonempty_positive_width_run_strictly_advances_the_source_suffix width head tail HW) as HT.
    cbn [length] in HF, HT. lia.
Qed.
Theorem completed_source_pass_preserves_whole_entry_occurrences :
  forall width input state output last,
  0 < width -> PassExecution width input state output last -> Permutation input output.
Proof.
  intros width input state output last HW HP.
  eapply (@SemanticResultMerge.SemanticResultMerge.pass_preserves_occurrences Entry State compare).
  exact (completed_source_pass_is_the_existing_pass width HW input state output last HP
    (length input) (Nat.le_refl _)).
Qed.
Theorem completed_source_pass_preserves_the_allocated_width :
  forall width input state output last,
  0 < width -> PassExecution width input state output last -> length input = length output.
Proof.
  intros width input state output last HW HP. apply Permutation_length.
  exact (completed_source_pass_preserves_whole_entry_occurrences
    width input state output last HW HP).
Qed.

Lemma responding_driver_completes_pass_with_sufficient_suffix_fuel :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall width, 0 < width -> forall fuel input state, length input <= fuel ->
  exists output last, PassExecution width input state output last.
Proof.
  intros total width HW fuel. induction fuel as [|fuel IH];
    intros [|head tail] state HB.
  - exists [], state. constructor.
  - cbn [length] in HB. lia.
  - exists [], state. constructor.
  - destruct (@MergeSortPdaRun.MergeSortPdaRun.responding_driver_completes_the_projected_run
      Entry State compare total [] (firstn width (head :: tail))
      (firstn width (skipn width (head :: tail))) state) as [merged [next HR]].
    assert (HT : length (skipn width (skipn width (head :: tail))) <= fuel).
    { pose proof (a_nonempty_positive_width_run_strictly_advances_the_source_suffix width head tail HW) as HS.
      cbn [length] in HB, HS. lia. }
    destruct (IH (skipn width (skipn width (head :: tail))) next HT) as [suffix [last HP]].
    exists (merged ++ suffix), last. eapply PassMore; eassumption.
Qed.
Theorem responding_driver_completes_the_projected_pass :
  (forall lhs rhs state, exists decision next, compare lhs rhs state = (Some decision, next)) ->
  forall width input state, 0 < width -> exists output last, PassExecution width input state output last.
Proof.
  intros total width input state HW.
  exact (responding_driver_completes_pass_with_sufficient_suffix_fuel total width HW
    (length input) input state (Nat.le_refl _)).
Qed.

Theorem source_pass_inherits_sorted_run_growth : forall (relation : Entry -> Entry -> Prop),
  (forall x y z, relation x y -> relation y z -> relation x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => relation y x | _ => relation x y end) ->
  forall width input state output last,
  0 < width ->
  @SemanticResultMerge.SemanticResultMerge.AlignedRuns Entry relation width input ->
  PassExecution width input state output last ->
  @SemanticResultMerge.SemanticResultMerge.AlignedRuns Entry relation (2 * width) output.
Proof.
  intros relation trans sound width input state output last HW HA HP.
  eapply (@SemanticResultMerge.SemanticResultMerge.pass_doubles_sorted_run_width Entry State compare
    relation trans sound); [exact HW|exact HA|].
  exact (completed_source_pass_is_the_existing_pass width HW input state output last HP
    (length input) (Nat.le_refl _)).
Qed.

(** Equality here is equality of proof class keys, never term equality. *)
Theorem source_pass_inherits_stable_class_subsequences :
  forall (Key : Type) (view : Entry -> Key) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (view x) (view y) = decision) ->
  forall width input state output last wanted,
  0 < width ->
  @SemanticResultMerge.SemanticResultMerge.AlignedRuns Entry
    (fun x y => order (view x) (view y) <> Gt) width input ->
  PassExecution width input state output last ->
  filter (@SemanticResultMerge.SemanticResultMerge.has_key Entry Key view order wanted) output =
    filter (@SemanticResultMerge.SemanticResultMerge.has_key Entry Key view order wanted) input.
Proof.
  intros Key view order key_eq faithful width input state output last wanted HW HA HP.
  exact (@SemanticResultMerge.SemanticResultMerge.pass_preserves_equal_key_subsequence
    Entry State compare Key view order key_eq faithful (length input) width input state output last wanted
    HA (completed_source_pass_is_the_existing_pass width HW input state output last HP
      (length input) (Nat.le_refl _))).
Qed.
End PassAssembly.

Print Assumptions reset_left_is_the_first_source_run.
Print Assumptions reset_right_is_the_second_source_run.
Print Assumptions source_after_run_end_is_the_double_skip_suffix.
Print Assumptions a_nonempty_positive_width_run_strictly_advances_the_source_suffix.
Print Assumptions completed_run_appends_to_the_existing_pass_prefix.
Print Assumptions one_completed_run_and_suffix_are_the_existing_pass_clause.
Print Assumptions completed_source_pass_is_the_existing_pass.
Print Assumptions completed_source_pass_preserves_whole_entry_occurrences.
Print Assumptions completed_source_pass_preserves_the_allocated_width.
Print Assumptions responding_driver_completes_the_projected_pass.
Print Assumptions source_pass_inherits_sorted_run_growth.
Print Assumptions source_pass_inherits_stable_class_subsequences.
End MergeSortPdaPass.
