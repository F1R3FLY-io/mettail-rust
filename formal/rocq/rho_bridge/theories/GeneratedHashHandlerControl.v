(** Shared generated Hash: field and category-Vec control component.

    Source: macros/src/gen/term_ops/iterative_hash.rs, hash_field_eagerly,
    hash_arm_stmts, generate_hash_scoped_arm and hash_collection_stmts;
    collection_walk.rs::for_each_subterm supplies the ordinary Vec walk.
    These lists project existing emitted source groups, not another AST,
    runtime visitor, iterator implementation or execution plan.

    FieldHandoff is the original payload binding/reborrow/handoff (one work).
    OptionalMatch groups as_ref and its selected match arm (one work).
    ChildPointer is present only at an emitted category-pointer extraction.
    Eager leaf reborrows belong to FieldHandoff, not ChildPointer.
    ScopeBody and ScopePattern each group the original inner(), selected
    field and reborrow; with the SINGLE scope-field handoff they total three.
    There are no additional fictitious body/pattern fields.

    VecLength is the original len query. IteratorSetup groups the original
    iter().enumerate().rev()/for adapter initialization. IteratorNext includes
    the terminal attempt; ElementPointer is the yielded reference-to-pointer
    handoff; IteratorRelease is normal teardown. Setup, terminal and release
    reuse RequiredVecBindingReservation's three-work/one-record boundary.
    That record is a logical iterator allowance, not allocated heap capacity.

    Every other group is one NativeWork. Tags, discriminants, payload Hash,
    tasks/pushes, driver/wrapper control and Map/native collection operations
    are EXCLUDED and must be composed separately. A Bag/Map payload's field
    handoff grants no native collection authority. Source correspondence,
    valid borrows, supported branch selection and actual original Vec width
    remain emitter obligations. Metadata inspection must be prepaid BEFORE
    extracting width, calculating a charge, or entering inspection body logic;
    paid BindingCharge accumulation is separate from future native allowance.
    No allocator, arbitrary callback, panic recovery or complete Hash bound
    is asserted here. Existing scheduling laws provide order without redoing
    their work; the new component is additive logical source accounting. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia Sorting.Permutation.
From RhoBridge Require Import GeneratedDummyCleanupReservation
  RequiredVecBindingReservation AdmittedGeneratedHashScheduling.
Import ListNotations.

Module GeneratedHashHandlerControl.
Module D := GeneratedDummyCleanupReservation.
Module V := RequiredVecBindingReservation.
Module S := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.

Inductive Group := FieldHandoff | OptionalMatch | ChildPointer
  | ScopeBody | ScopePattern | VecLength | IteratorSetup | IteratorNext
  | ElementPointer | IteratorRelease.

Definition group_counts group : D.Counts := fun event =>
  D.atom D.NativeWork event +
  match group with IteratorSetup => D.atom D.NativeRecord event | _ => 0 end.
Definition counts groups : D.Counts := fun event =>
  fold_right (fun group total => group_counts group event + total) 0 groups.

Lemma counts_app : forall first second event,
  counts (first ++ second) event = counts first event + counts second event.
Proof.
  induction first as [|group rest IH]; intros second event; [reflexivity|].
  change (group_counts group event + counts (rest ++ second) event =
    (group_counts group event + counts rest event) + counts second event).
  rewrite IH. lia.
Qed.

(** The flags are emitted branch observations, not inferred term properties:
    optional says an option match exists, child says its selected branch
    actually extracts a category pointer. None therefore supplies child=false. *)
Definition field_word (optional child : bool) :=
  [FieldHandoff] ++ (if optional then [OptionalMatch] else []) ++
  (if child then [ChildPointer] else []).
Definition flag (value : bool) := if value then 1 else 0.

Theorem field_control_counts : forall optional child event,
  counts (field_word optional child) event =
    (1 + flag optional + flag child) * D.atom D.NativeWork event.
Proof. intros [] [] event; destruct event; reflexivity. Qed.

Theorem absent_optional_has_no_pointer_or_payload_control :
  field_word true false = [FieldHandoff; OptionalMatch].
Proof. reflexivity. Qed.

Definition scope_word := [FieldHandoff; ScopeBody; ScopePattern].
Theorem scope_extractions_are_one_field_and_two_accesses : forall event,
  counts scope_word event = 3 * D.atom D.NativeWork event.
Proof. intro event; destruct event; reflexivity. Qed.

Definition element_word := [IteratorNext; ElementPointer].
Definition vector_word {A} (original : list A) :=
  [VecLength; IteratorSetup] ++
  concat (map (fun _ => element_word) (rev original)) ++
  [IteratorNext; IteratorRelease].

Lemma element_words_follow_original_occurrences : forall A (items : list A) event,
  counts (concat (map (fun _ => element_word) items)) event =
    2 * length items * D.atom D.NativeWork event.
Proof.
  intros A items. induction items as [|item rest IH]; intro event; [reflexivity|].
  change (counts (element_word ++ concat (map (fun _ => element_word) rest)) event =
    2 * S (length rest) * D.atom D.NativeWork event).
  rewrite counts_app, IH.
  unfold element_word, counts, group_counts. cbn [fold_right]. lia.
Qed.

Theorem vector_control_counts : forall A (original : list A) event,
  counts (vector_word original) event =
    (4 + 2 * length original) * D.atom D.NativeWork event +
    D.atom D.NativeRecord event.
Proof.
  intros A original event. unfold vector_word.
  rewrite !counts_app, element_words_follow_original_occurrences, length_rev.
  unfold counts, group_counts. cbn [fold_right]. lia.
Qed.

Theorem vector_reuses_existing_borrowed_iterator_boundary :
  forall A (original : list A) event,
  counts (vector_word original) event =
    V.borrowed_traversal (length original) event +
    (1 + length original) * D.atom D.NativeWork event.
Proof.
  intros A original event. rewrite vector_control_counts.
  unfold V.borrowed_traversal, V.borrowed_iterator_boundary,
    V.consuming_iterator_boundary. lia.
Qed.

Theorem vector_empty_still_has_setup_terminal_release_and_length : forall event,
  counts (@vector_word nat []) event =
    4 * D.atom D.NativeWork event + D.atom D.NativeRecord event.
Proof. intro event. apply vector_control_counts. Qed.

Definition batch_counts (words : list (list Group)) event :=
  fold_right (fun word total => counts word event + total) 0 words.

Theorem handler_components_compose_additively : forall words event,
  counts (concat words) event = batch_counts words event.
Proof.
  induction words as [|word rest IH]; intro event; [reflexivity|].
  change (counts (word ++ concat rest) event =
    counts word event + batch_counts rest event).
  now rewrite counts_app, IH.
Qed.

Theorem handler_component_order_does_not_change_allowance : forall first second,
  Permutation first second -> forall event,
  counts (concat first) event = counts (concat second) event.
Proof.
  intros first second ORDER event. rewrite !handler_components_compose_additively.
  induction ORDER; unfold batch_counts in *; cbn [fold_right] in *; lia.
Qed.

(** Cost additivity does not justify changing the native Hash stream.
    These corollaries retain the ORIGINAL shared scheduler's exact order. *)
Theorem original_field_batches_keep_their_native_order :
  forall Task (pending : list Task) fields,
  S.pop_order (pending ++ S.deferred_pushes fields) = concat fields ++ S.pop_order pending.
Proof. intros. apply S.reverse_fields_preserve_field_and_element_order. Qed.

Theorem original_vector_prefix_and_elements_keep_their_native_order :
  forall Task (pending : list Task) length_tag original,
  S.pop_order (pending ++ rev original ++ [length_tag]) =
    length_tag :: original ++ S.pop_order pending.
Proof. intros. apply S.vec_prefix_pops_before_elements. Qed.

Theorem original_scope_pattern_and_body_keep_their_native_order :
  forall Task (pending : list Task) prefields pattern body,
  S.pop_order (pending ++ [body; pattern] ++ S.deferred_pushes prefields) =
    concat prefields ++ pattern :: body :: S.pop_order pending.
Proof. intros. apply S.binder_pattern_precedes_body_after_prefields. Qed.

Print Assumptions field_control_counts.
Print Assumptions absent_optional_has_no_pointer_or_payload_control.
Print Assumptions scope_extractions_are_one_field_and_two_accesses.
Print Assumptions vector_control_counts.
Print Assumptions vector_reuses_existing_borrowed_iterator_boundary.
Print Assumptions vector_empty_still_has_setup_terminal_release_and_length.
Print Assumptions handler_components_compose_additively.
Print Assumptions handler_component_order_does_not_change_allowance.
Print Assumptions original_field_batches_keep_their_native_order.
Print Assumptions original_vector_prefix_and_elements_keep_their_native_order.
Print Assumptions original_scope_pattern_and_body_keep_their_native_order.
End GeneratedHashHandlerControl.
