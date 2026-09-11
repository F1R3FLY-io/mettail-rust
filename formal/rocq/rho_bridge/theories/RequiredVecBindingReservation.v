(** Required Vec field accounting for the generated checked binding worker.

    Source: iterative_drop.rs's Regular and scope-prefield Vec arms use
    mem::take followed by one owned DropTask push per stored element. The
    replacement Vec is empty. dummy_receipts.rs::empty_iterator already pays
    construction, terminal next and teardown of a consuming iterator as three
    NativeWork events and one NativeRecord. Successful advances are separate.

    This increment explicitly gives the same three-boundary convention to
    the assembly range iterator and the complete borrowed source iterator.
    collection_walk.rs's Vec ReverseForLifo uses iter().enumerate().rev(),
    without allocating a staging Vec. A logical iterator record does not mean
    a heap allocation or an assertion about compiler-generated instructions.

    Destination header/backing slots are admitted before construction; range
    advances and insertion dispatches are included below. Borrowed traversal
    is paid separately BEFORE the reverse walk. Task-push callbacks, result
    cells and checked takes remain separate. Every Vec element is an owned
    output occurrence in Clone, Open and Close; surrounding Arc/scope Clone
    sharing rules do not change. Child construction, payloads and cleanup are
    already independently paid, not added again to the Vec shell allowance.

    A failed partial Vec drops its header and visits its produced elements;
    those elements retain independent-root cleanup credits. Successful
    assembly transfers those same credits into the parent. Ordered slots and
    prefix equations preserve duplicate occurrences, without a new ownership
    calculus or an identity-uniqueness premise. The emitter still owes exact
    width, admission order, scheduling/readiness and source lifetime facts.
    These are logical normal-error contracts, not physical allocator bounds,
    panic/TLS recovery, arbitrary hashing or a proof of whole Rust execution. *)
From Stdlib Require Import List Arith Lia.
From Trampoline Require Import WorklistFoldEquivalence.
From RhoBridge Require Import GeneratedDummyCleanupReservation
  GeneratedBindingOutputReservation IndexedCopySlots ScalarArcBindingReservation.
Import ListNotations.

Module RequiredVecBindingReservation.
Module D := GeneratedDummyCleanupReservation.
Module O := GeneratedBindingOutputReservation.
Module I := IndexedCopySlots.
Module S := ScalarArcBindingReservation.
Module W := WorklistFoldEquivalence.

Definition consuming_iterator_boundary : D.Counts := fun event =>
  3 * D.atom D.NativeWork event + D.atom D.NativeRecord event.

(** Named new boundaries: one construction, one terminal attempt and one
    teardown; successful advances are charged by the actual width. *)
Definition range_iterator_boundary := consuming_iterator_boundary.
Definition borrowed_iterator_boundary := consuming_iterator_boundary.

Definition destination_storage width : D.Counts := fun event =>
  D.atom D.NativeWork event + (1 + width) * D.atom D.NativeRecord event.

Definition vec_copy width : D.Counts := fun event =>
  destination_storage width event + range_iterator_boundary event +
  width * D.atom D.NativeWork event + width * D.atom D.NativeWork event.

Definition vec_cleanup width : D.Counts := fun event =>
  D.atom D.HandleField event +
  (D.atom D.NativeWork event + D.atom D.NativeRecord event) +
  consuming_iterator_boundary event + width * D.atom D.NativeWork event +
  width * D.atom D.PushDropTask event + D.atom D.NativeWork event.

Definition vec_total width : D.Counts := fun event =>
  vec_copy width event + vec_cleanup width event.

Definition borrowed_traversal width : D.Counts := fun event =>
  borrowed_iterator_boundary event + width * D.atom D.NativeWork event.

Theorem iterator_boundary_projection :
  D.weighted D.base_work_weight consuming_iterator_boundary = 3 /\
  D.weighted D.record_weight consuming_iterator_boundary = 1 /\
  D.weighted D.byte_weight consuming_iterator_boundary = 0.
Proof. repeat split; reflexivity. Qed.

Lemma weighted_scale : forall weight factor counts,
  D.weighted weight (fun event => factor * counts event) =
  factor * D.weighted weight counts.
Proof.
  intros weight factor counts. unfold D.weighted.
  induction D.all_events as [|event rest IH]; cbn [D.weighted_over]; nia.
Qed.

Theorem vec_copy_projection : forall width,
  D.weighted D.base_work_weight (vec_copy width) = 4 + 2 * width /\
  D.weighted D.record_weight (vec_copy width) = 2 + width /\
  D.weighted D.byte_weight (vec_copy width) = 0.
Proof.
  intro width. unfold vec_copy, destination_storage, range_iterator_boundary,
    consuming_iterator_boundary.
  rewrite !S.weighted_add, !weighted_scale.
  change
    (1 + (1 + width) * 0 + (3 * 1 + 0) + width * 1 + width * 1 = 4 + 2 * width /\
     0 + (1 + width) * 1 + (3 * 0 + 1) + width * 0 + width * 0 = 2 + width /\
     0 + (1 + width) * 0 + (3 * 0 + 0) + width * 0 + width * 0 = 0).
  repeat split; lia.
Qed.

Theorem vec_cleanup_projection : forall width,
  D.weighted D.base_work_weight (vec_cleanup width) = 6 + 2 * width /\
  D.weighted D.record_weight (vec_cleanup width) = 2 + width /\
  D.weighted D.byte_weight (vec_cleanup width) = 0.
Proof.
  intro width. unfold vec_cleanup, consuming_iterator_boundary.
  rewrite !S.weighted_add, !weighted_scale.
  change
    (1 + (1 + 0) + (3 * 1 + 0) + width * 1 + width * 1 + 1 = 6 + 2 * width /\
     0 + (0 + 1) + (3 * 0 + 1) + width * 0 + width * 1 + 0 = 2 + width /\
     0 + (0 + 0) + (3 * 0 + 0) + width * 0 + width * 0 + 0 = 0).
  repeat split; lia.
Qed.

Theorem vec_total_projection : forall width,
  D.weighted D.base_work_weight (vec_total width) = 10 + 4 * width /\
  D.weighted D.record_weight (vec_total width) = 4 + 2 * width /\
  D.weighted D.byte_weight (vec_total width) = 0.
Proof.
  intro width. unfold vec_total. rewrite !S.weighted_add.
  destruct (vec_copy_projection width) as [CW [CR CB]].
  destruct (vec_cleanup_projection width) as [DW [DR DB]].
  rewrite CW, CR, CB, DW, DR, DB. repeat split; lia.
Qed.

Theorem borrowed_traversal_projection : forall width,
  D.weighted D.base_work_weight (borrowed_traversal width) = 3 + width /\
  D.weighted D.record_weight (borrowed_traversal width) = 1 /\
  D.weighted D.byte_weight (borrowed_traversal width) = 0.
Proof.
  intro width. unfold borrowed_traversal, borrowed_iterator_boundary,
    consuming_iterator_boundary.
  rewrite !S.weighted_add, !weighted_scale.
  change
    (3 * 1 + 0 + width * 1 = 3 + width /\
     3 * 0 + 1 + width * 0 = 1 /\
     3 * 0 + 0 + width * 0 = 0).
  repeat split; lia.
Qed.

(** Only the direct partial Vec's flat header/element dispatch is counted
    here. Each produced child still has its separately paid root allowance. *)
Definition partial_flat_work produced := 1 + produced.

Theorem partial_vec_flat_cleanup_is_covered : forall produced width,
  produced <= width ->
  partial_flat_work produced <= D.weighted D.base_work_weight (vec_cleanup width).
Proof.
  intros produced width H.
  destruct (vec_cleanup_projection width) as [HW _].
  rewrite HW. unfold partial_flat_work. lia.
Qed.

(** Ordinary list/prefix equations describe the supplied result sequence;
    append is not an implementation proposal for building the Rust Vec. *)
Theorem initial_result_prefix : forall A (supplied : list A), [] ++ supplied = supplied.
Proof. reflexivity. Qed.

Theorem result_push_preserves_ordered_inventory :
  forall A (supplied done : list A) value pending,
  done ++ value :: pending = supplied ->
  (done ++ [value]) ++ pending = supplied.
Proof.
  intros A supplied done value pending H. rewrite <- app_assoc. exact H.
Qed.

Theorem completed_result_prefix_is_exact : forall A (supplied done : list A),
  done ++ [] = supplied -> done = supplied.
Proof. intros A supplied done H. now rewrite app_nil_r in H. Qed.

Theorem ordered_prefix_bounds_partial_cleanup :
  forall A (supplied done pending : list A),
  done ++ pending = supplied ->
  partial_flat_work (length done) <=
    D.weighted D.base_work_weight (vec_cleanup (length supplied)).
Proof.
  intros A supplied done pending H. subst supplied.
  apply partial_vec_flat_cleanup_is_covered. rewrite length_app. lia.
Qed.

Theorem result_inventory_preserves_occurrence_counts :
  forall A (eq_dec : forall left right : A, {left = right} + {left <> right})
    (supplied done pending : list A) occurrence,
  done ++ pending = supplied ->
  count_occ eq_dec supplied occurrence =
    count_occ eq_dec done occurrence + count_occ eq_dec pending occurrence.
Proof.
  intros A eq_dec supplied done pending occurrence H. subst supplied.
  apply count_occ_app.
Qed.

Theorem result_inventory_transfers_existing_credits :
  forall A (credit : A -> D.Counts) supplied done pending event,
  done ++ pending = supplied ->
  O.sum_counts credit supplied event =
    O.sum_counts credit done event + O.sum_counts credit pending event.
Proof.
  intros A credit supplied done pending event H. subst supplied.
  apply O.sum_counts_app.
Qed.

Theorem prepared_slots_return_exact_supplied_sequence :
  forall A prefix expected (supplied : list A) suffix,
  I.take_many (length supplied) (length prefix) expected
    (prefix ++ map (fun value => Some (expected, value)) supplied ++ suffix) =
  Some (supplied, prefix ++ repeat None (length supplied) ++ suffix).
Proof. intros. apply I.prepared_range_ready. Qed.

Theorem reverse_push_then_lifo_preserves_sequence : forall A (supplied : list A),
  rev (rev supplied) = supplied.
Proof. intros. apply rev_involutive. Qed.

Theorem vec_field_instantiates_output_local : forall dc dx dg width tag event,
  O.local_credit dc dx dg (fun _ => [])
    (fun _ => vec_copy width) (fun _ => vec_cleanup width) tag event =
  S.parent_base event + vec_total width event.
Proof.
  intros. unfold O.local_credit, O.local_root, O.replacements, O.sum_counts,
    S.parent_base, vec_total. cbn [fold_right]. lia.
Qed.

(** Algebraic specialization only: the Rust field descriptor must establish
    its actual width and supply all its owned child occurrences. No selected
    category dummy is introduced for a Vec or substituted for those children. *)
Theorem vec_assembly_transfers_existing_child_credits :
  forall dc dx dg width tag children event,
  O.output_credit
    (O.output dc dx dg (fun _ => [])
      (fun _ => vec_copy width) (fun _ => vec_cleanup width)
      (W.Node tag children)) event =
  S.parent_base event + vec_total width event +
  O.sum_counts O.output_credit
    (O.outputs dc dx dg (fun _ => [])
      (fun _ => vec_copy width) (fun _ => vec_cleanup width) children) event.
Proof.
  intros. rewrite O.assembly_transfers_existing_child_credits.
  now rewrite vec_field_instantiates_output_local.
Qed.

Print Assumptions iterator_boundary_projection.
Print Assumptions weighted_scale.
Print Assumptions vec_copy_projection.
Print Assumptions vec_cleanup_projection.
Print Assumptions vec_total_projection.
Print Assumptions borrowed_traversal_projection.
Print Assumptions partial_vec_flat_cleanup_is_covered.
Print Assumptions initial_result_prefix.
Print Assumptions result_push_preserves_ordered_inventory.
Print Assumptions completed_result_prefix_is_exact.
Print Assumptions ordered_prefix_bounds_partial_cleanup.
Print Assumptions result_inventory_preserves_occurrence_counts.
Print Assumptions result_inventory_transfers_existing_credits.
Print Assumptions prepared_slots_return_exact_supplied_sequence.
Print Assumptions reverse_push_then_lifo_preserves_sequence.
Print Assumptions vec_field_instantiates_output_local.
Print Assumptions vec_assembly_transfers_existing_child_credits.
End RequiredVecBindingReservation.
