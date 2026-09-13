(** Canonical comparison classes of the actual native sorted output.

    A class key records exactly what comparison observes, not term identity.
    In particular, identity/pattern digests may identify distinct source
    terms. Antisymmetry is used only on keys. The uniqueness proof generalizes
    SemanticReceiptOrder.sorted_receipt_permutation_is_unique, itself adapted
    from the node's rb_strongly_sorted_perm_eq; no new sorting algorithm is
    defined here.

    The native lifecycle supplies the existing successful sort equation.
    Existing merge laws then supply sortedness and occurrence conservation;
    mapping the complete records gives the unique sorted class roster. The
    same existing sort theorem separately preserves complete equal-class
    subsequences, needed for native hashing. Equality of class rosters alone
    would not establish equality of native hash streams.

    Exact child comparison factorization remains an explicit premise to be
    instantiated by the finite-child source proof. This file does not assume
    an injective term view, successful admission of every roster element, or
    that partially overwritten scratch is a permutation. *)
From Stdlib Require Import List Sorting.Sorted Sorting.Permutation.
From RuntimeGrammar Require Import SemanticComparisonLaws SemanticResultMerge.
From RhoBridge Require Import MergeSortPdaNativeOuter.
Import ListNotations.
Import SemanticComparisonLaws.SemanticComparisonLaws.

Module NativeSortedComparisonClasses.

Section ClassOrder.
Context {Key : Type}.
Variable key_compare : Key -> Key -> comparison.
Hypothesis key_laws : Laws key_compare.
Definition class_le a b := key_compare a b <> Gt.

Lemma class_le_is_antisymmetric : forall a b,
  class_le a b -> class_le b a -> a = b.
Proof.
  intros a b AB BA. unfold class_le in *.
  rewrite (comparison_opposite key_laws a b) in BA.
  destruct (key_compare a b) eqn:E; cbn in BA; try contradiction.
  apply (comparison_eq key_laws). exact E.
Qed.

Theorem sorted_class_permutation_is_unique : forall left right,
  StronglySorted class_le left -> StronglySorted class_le right ->
  Permutation left right -> left = right.
Proof.
  induction left as [|a left IH]; intros right SL SR P.
  - apply Permutation_nil in P. symmetry. exact P.
  - destruct right as [|b right].
    { apply Permutation_sym in P. apply Permutation_nil in P. discriminate. }
    destruct (StronglySorted_inv SL) as [SLT LA].
    destruct (StronglySorted_inv SR) as [SRT LB].
    assert (B : In b (a :: left)).
    { eapply Permutation_in; [apply Permutation_sym; exact P | left; reflexivity]. }
    assert (A : In a (b :: right)).
    { eapply Permutation_in; [exact P | left; reflexivity]. }
    assert (E : a = b).
    { destruct B as [E | B]; [exact E |].
      destruct A as [E | A]; [symmetry; exact E |].
      rewrite Forall_forall in LA, LB. apply class_le_is_antisymmetric;
        [apply LA; exact B | apply LB; exact A]. }
    subst b. apply Permutation_cons_inv in P. f_equal. apply IH; assumption.
Qed.

Section NativeOutput.
Context {Entry State : Type}.
Variable view : Entry -> Key.

(** Class equality does not identify source records. Their per-class ordered
    subsequences supply the missing information, including collisions. *)
Theorem class_roster_and_each_class_subsequence_determine_the_complete_roster :
  forall left right : list Entry,
  map view left = map view right ->
  (forall wanted,
    filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) left =
    filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) right) ->
  left = right.
Proof.
  induction left as [|a left IH]; intros [|b right] KEYS SUBSEQUENCES;
    cbn [map] in KEYS; try discriminate; [reflexivity|].
  injection KEYS as HEAD TAIL.
  pose proof (SUBSEQUENCES (view a)) as SAME_CLASS.
  assert (A : SemanticResultMerge.SemanticResultMerge.has_key view key_compare (view a) a = true).
  { unfold SemanticResultMerge.SemanticResultMerge.has_key.
    rewrite (proj2 (comparison_eq key_laws (view a) (view a)) eq_refl). reflexivity. }
  assert (B : SemanticResultMerge.SemanticResultMerge.has_key view key_compare (view a) b = true).
  { unfold SemanticResultMerge.SemanticResultMerge.has_key. rewrite <- HEAD.
    rewrite (proj2 (comparison_eq key_laws (view a) (view a)) eq_refl). reflexivity. }
  cbn [filter] in SAME_CLASS. rewrite A, B in SAME_CLASS.
  injection SAME_CLASS as RECORD REST. subst b.
  f_equal. apply IH; [exact TAIL|]. intro wanted.
  specialize (SUBSEQUENCES wanted). cbn [filter] in SUBSEQUENCES.
  destruct (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted a).
  - injection SUBSEQUENCES as MATCHED. exact MATCHED.
  - exact SUBSEQUENCES.
Qed.

Variable compare : Entry -> Entry -> State -> option comparison * State.
Hypothesis faithful : forall a b state decision next,
  compare a b state = (Some decision, next) ->
  key_compare (view a) (view b) = decision.

Lemma sorted_records_project_to_sorted_classes : forall records,
  StronglySorted (fun a b => class_le (view a) (view b)) records ->
  StronglySorted class_le (map view records).
Proof.
  intros records HS. induction HS as [|head tail SORT IH BOUND].
  - constructor.
  - cbn [map]. constructor; [exact IH|].
    apply Forall_forall. intros key MEMBER. apply in_map_iff in MEMBER.
    destruct MEMBER as [entry [E MEMBER]]. subst key.
    rewrite Forall_forall in BOUND. exact (BOUND entry MEMBER).
Qed.

Theorem native_output_is_a_sorted_class_permutation :
  forall maximum count source state output scratch last,
  length source <= maximum ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum count 1 source None state output scratch last ->
  StronglySorted class_le (map view output) /\
  Permutation (map view source) (map view output).
Proof.
  intros maximum count source state output scratch last WIDTH NATIVE.
  pose proof (MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.actual_native_sort_has_the_existing_sort_result
    compare maximum count source state output scratch last WIDTH NATIVE) as SORT.
  split.
  - apply sorted_records_project_to_sorted_classes.
    eapply SemanticResultMerge.SemanticResultMerge.sort_is_sorted; [| |exact SORT].
    + intros a b c. unfold class_le.
      apply (not_greater_is_transitive Key key_compare key_laws).
    + exact (SemanticResultMerge.SemanticResultMerge.exact_key_comparison_is_sound
        compare Key view key_compare (comparison_opposite key_laws) faithful).
  - eapply SemanticResultMerge.SemanticResultMerge.sort_preserves_projected_roster.
    exact SORT.
Qed.

Theorem native_output_matches_the_unique_canonical_class_roster :
  forall maximum count source state output scratch last canonical,
  length source <= maximum ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum count 1 source None state output scratch last ->
  StronglySorted class_le canonical -> Permutation (map view source) canonical ->
  map view output = canonical.
Proof.
  intros maximum count source state output scratch last canonical WIDTH NATIVE SC PC.
  destruct (native_output_is_a_sorted_class_permutation
    maximum count source state output scratch last WIDTH NATIVE) as [SO PO].
  apply sorted_class_permutation_is_unique; [exact SO|exact SC|].
  eapply Permutation_trans; [apply Permutation_sym; exact PO|exact PC].
Qed.

Theorem equal_input_class_multisets_give_equal_native_output_class_rosters :
  forall maximum_left count_left left state_left output_left scratch_left last_left
    maximum_right count_right right state_right output_right scratch_right last_right,
  length left <= maximum_left -> length right <= maximum_right ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum_left count_left 1 left None state_left output_left scratch_left last_left ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum_right count_right 1 right None state_right output_right scratch_right last_right ->
  Permutation (map view left) (map view right) ->
  map view output_left = map view output_right.
Proof.
  intros ML CL left SL OL TL FL MR CR right SR OR TR FR WL WR NL NR P.
  destruct (native_output_is_a_sorted_class_permutation MR CR right SR OR TR FR WR NR)
    as [SORT PERM].
  eapply native_output_matches_the_unique_canonical_class_roster;
    [exact WL|exact NL|exact SORT|].
  eapply Permutation_trans; [exact P|exact PERM].
Qed.

Theorem native_output_preserves_complete_equal_class_subsequences :
  forall maximum count source state output scratch last wanted,
  length source <= maximum ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum count 1 source None state output scratch last ->
  filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) output =
    filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) source.
Proof.
  intros maximum count source state output scratch last wanted WIDTH NATIVE.
  pose proof (MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.actual_native_sort_has_the_existing_sort_result
    compare maximum count source state output scratch last WIDTH NATIVE) as SORT.
  eapply SemanticResultMerge.SemanticResultMerge.sort_preserves_equal_key_subsequence;
    [apply (comparison_eq key_laws)|apply (comparison_opposite key_laws)|
     apply (not_greater_is_transitive Key key_compare key_laws)|exact faithful|exact SORT].
Qed.

(** The native output agrees with any ordinary stable sort satisfying its
    sortedness, whole-record permutation, and equal-class stability contract.
    The ordinary sort implementation is not modeled by an extra algorithm.
    Its pinned source/library contract is a separate correspondence boundary. *)
Theorem native_output_matches_any_stable_sorted_roster :
  forall maximum count source state output scratch last reference,
  length source <= maximum ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    compare maximum count 1 source None state output scratch last ->
  StronglySorted (fun a b => class_le (view a) (view b)) reference ->
  Permutation source reference ->
  (forall wanted,
    filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) reference =
    filter (SemanticResultMerge.SemanticResultMerge.has_key view key_compare wanted) source) ->
  output = reference.
Proof.
  intros maximum count source state output scratch last reference WIDTH NATIVE SORT PERM STABLE.
  apply class_roster_and_each_class_subsequence_determine_the_complete_roster.
  - eapply native_output_matches_the_unique_canonical_class_roster;
      [exact WIDTH|exact NATIVE| |].
    + apply sorted_records_project_to_sorted_classes. exact SORT.
    + apply Permutation_map. exact PERM.
  - intro wanted. rewrite STABLE.
    eapply native_output_preserves_complete_equal_class_subsequences; eassumption.
Qed.
End NativeOutput.
End ClassOrder.

Print Assumptions class_le_is_antisymmetric.
Print Assumptions sorted_class_permutation_is_unique.
Print Assumptions sorted_records_project_to_sorted_classes.
Print Assumptions class_roster_and_each_class_subsequence_determine_the_complete_roster.
Print Assumptions native_output_is_a_sorted_class_permutation.
Print Assumptions native_output_matches_the_unique_canonical_class_roster.
Print Assumptions equal_input_class_multisets_give_equal_native_output_class_rosters.
Print Assumptions native_output_preserves_complete_equal_class_subsequences.
Print Assumptions native_output_matches_any_stable_sorted_roster.
End NativeSortedComparisonClasses.
