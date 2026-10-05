(** * Exact optional receipts on the existing owned-value worklist

    This is an incremental annotation of the production value stack, not a
    second lowering machine.  An absent receipt makes no resource claim.  A
    present receipt must describe the very native value carried in that slot.
    Parallel composition carries a receipt only when both operands do.

    The model proves erasure and retained-shape correspondence.  It does not
    establish a Rust allocation bound: source-side admission of clone, metadata,
    temporary-storage and cleanup work is a separate implementation obligation.
*)

From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import RholangTargetConstruction
  RholangWorklistConstruction RholangDeepConstructionSize.
Import ListNotations.

Module AnnotatedValueWorklist.

Record Slot := slot {
  owned_value : NativeValueImage;
  optional_receipt : option NativeReceipt
}.

Definition erase_slot (value : Slot) : Value :=
  erase_native_value (owned_value value).

Definition receipt_exact (value : Slot) : Prop :=
  match optional_receipt value with
  | None => True
  | Some receipt =>
      receipt_outer_bytes receipt = native_outer_bytes (owned_value value) /\
      (forall axis, receipt_owned_count receipt axis =
        native_value_count axis (owned_value value))
  end.

Definition unannotated (value : NativeValueImage) : Slot :=
  slot value None.

Definition annotated (value : NativeValueImage) : Slot :=
  slot value (Some (native_receipt value)).

Definition append_slot (left right : Slot) : Slot :=
  slot (native_append (owned_value left) (owned_value right))
    (match optional_receipt left, optional_receipt right with
     | Some lhs, Some rhs => Some (append_native_receipt lhs rhs)
     | _, _ => None
     end).

Theorem unannotated_is_honest : forall value,
  receipt_exact (unannotated value).
Proof. reflexivity. Qed.

Theorem annotated_is_exact : forall value,
  receipt_exact (annotated value).
Proof. intros; split; reflexivity. Qed.

Theorem append_slot_erases_to_existing_append : forall left right,
  erase_slot (append_slot left right) =
    RholangTargetConstruction.append (erase_slot left) (erase_slot right).
Proof.
  intros; unfold erase_slot, append_slot; cbn.
  apply native_append_erases_to_existing_append.
Qed.

Theorem append_slot_keeps_exact_receipt : forall left right,
  receipt_exact left -> receipt_exact right ->
  receipt_exact (append_slot left right).
Proof.
  intros [lv [lr|]] [rv [rr|]] HL HR; cbn in *; try exact I.
  destruct HL as [HLO HLC].
  destruct HR as [HRO HRC].
  split.
  - cbn. rewrite native_append_receipt_preserves_outer_maximum.
    now rewrite HLO, HRO.
  - intro axis. cbn.
    rewrite native_append_receipt_is_additive.
    now rewrite HLC, HRC.
Qed.

Theorem append_slot_does_not_fabricate_a_receipt : forall left right,
  optional_receipt left = None \/ optional_receipt right = None ->
  optional_receipt (append_slot left right) = None.
Proof.
  intros [lv [lr|]] [rv [rr|]] H; cbn in *; try reflexivity.
  destruct H as [H|H]; discriminate.
Qed.

(** The native append source clones left's head vectors and then clones both
    temporary vectors during concat. Those temporaries and the original left
    are released. This counts owned head visits; root-vector and outer-metadata
    charges are additional finite source-side obligations. *)
Definition append_copy_and_cleanup_count (axis : NativeSizeAxis)
    (left right : NativeValueImage) : nat :=
  native_append_copy_count axis left right +
  native_append_copy_count axis left right.

Theorem append_copy_and_cleanup_count_is_four_left_two_right :
  forall axis left right,
  append_copy_and_cleanup_count axis left right =
    4 * native_value_count axis left + 2 * native_value_count axis right.
Proof.
  intros. unfold append_copy_and_cleanup_count.
  rewrite native_append_copies_twice_left_once_right. lia.
Qed.

Theorem annotated_pair_preserves_ordered_prefix : forall prefix left right,
  reduce_pair (fun lhs rhs => @Built _ unit (append_slot lhs rhs))
    (prefix ++ [left; right]) =
  Completed (prefix ++ [append_slot left right]).
Proof.
  intros. rewrite pair_keeps_left_right_order. reflexivity.
Qed.

Theorem annotated_pair_erases_to_existing_transition : forall prefix left right,
  reduce_pair (fun lhs rhs => @Built _ unit
    (RholangTargetConstruction.append lhs rhs))
    (map erase_slot (prefix ++ [left; right])) =
  map_transition erase_slot
    (reduce_pair (fun lhs rhs => @Built _ unit (append_slot lhs rhs))
      (prefix ++ [left; right])).
Proof.
  intros. rewrite map_app. cbn [map].
  rewrite !pair_keeps_left_right_order. cbn [map_transition map].
  rewrite map_app. cbn [map].
  rewrite append_slot_erases_to_existing_append.
  reflexivity.
Qed.

Definition empty_slot : Slot := annotated (NativeValue [] closed_summary).

Theorem empty_slot_is_exact : receipt_exact empty_slot.
Proof. apply annotated_is_exact. Qed.

Theorem append_fold_preserves_erasure : forall values initial,
  erase_slot (fold_left append_slot values initial) =
    fold_left RholangTargetConstruction.append (map erase_slot values)
      (erase_slot initial).
Proof.
  induction values as [|first rest IH]; intros initial; cbn; [reflexivity|].
  rewrite IH, append_slot_erases_to_existing_append. reflexivity.
Qed.

Theorem append_fold_preserves_exact_receipts : forall values initial,
  receipt_exact initial -> Forall receipt_exact values ->
  receipt_exact (fold_left append_slot values initial).
Proof.
  induction values as [|first rest IH]; intros initial HI HV; cbn; [exact HI|].
  inversion HV; subst. apply IH; [now apply append_slot_keeps_exact_receipt|assumption].
Qed.

Print Assumptions append_slot_erases_to_existing_append.
Print Assumptions append_slot_keeps_exact_receipt.
Print Assumptions append_slot_does_not_fabricate_a_receipt.
Print Assumptions append_copy_and_cleanup_count_is_four_left_two_right.
Print Assumptions annotated_pair_erases_to_existing_transition.
Print Assumptions append_fold_preserves_erasure.
Print Assumptions append_fold_preserves_exact_receipts.

End AnnotatedValueWorklist.
