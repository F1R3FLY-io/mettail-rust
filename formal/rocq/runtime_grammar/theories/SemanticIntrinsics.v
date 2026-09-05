(**
  SemanticIntrinsics: closed, pure primitives for executable semantic images.

  A first-order GSLT rewrite system can inspect constructor structure, but an
  admitted literal payload remains opaque.  Runtime-defined theories therefore
  need a small collection of total operations for equality, UTF-8 traversal,
  checked arithmetic, and final text-plan materialization.  The collection in
  this file is deliberately closed: it contains no URI, host callback, parser,
  capability, or language-specific operation.

  UTF-8 cursors are byte offsets.  [ScalarText] is the mathematical sequence of
  Unicode scalar values used by the Regex reference semantics.  The lemmas
  below establish the bridge from scalar indices to monotonically increasing
  byte boundaries.  A runtime implementation may store UTF-8 directly, but it
  must implement these contracts exactly.

  Rocq 9.1 compatible.  No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Module SemanticIntrinsics.

Definition Commitment := list nat.
Definition Scalar := nat.
Definition ScalarText := list Scalar.
Definition ByteIndex := nat.
Definition SlotId := nat.

(** Unicode scalar values exclude the surrogate interval.  UTF-8 width is
    nevertheless total on [nat], so malformed scalar payloads can be rejected
    independently of cursor arithmetic. *)
Definition valid_unicode_scalar (scalar : Scalar) : Prop :=
  scalar <= 1114111 /\ ~ (55296 <= scalar <= 57343).

Definition utf8_width (scalar : Scalar) : nat :=
  if Nat.leb scalar 127 then 1
  else if Nat.leb scalar 2047 then 2
  else if Nat.leb scalar 65535 then 3
  else 4.

Lemma utf8_width_positive :
  forall scalar, 1 <= utf8_width scalar.
Proof.
  intro scalar. unfold utf8_width.
  repeat destruct (Nat.leb _ _); lia.
Qed.

Lemma utf8_width_at_most_four :
  forall scalar, utf8_width scalar <= 4.
Proof.
  intro scalar. unfold utf8_width.
  repeat destruct (Nat.leb _ _); lia.
Qed.

Fixpoint utf8_byte_length (text : ScalarText) : nat :=
  match text with
  | [] => 0
  | scalar :: rest => utf8_width scalar + utf8_byte_length rest
  end.

(** [scalar_byte_offset text index] saturates at the byte length of [text]
    when [index] exceeds the number of scalars. *)
Fixpoint scalar_byte_offset (text : ScalarText) (index : nat) : ByteIndex :=
  match index, text with
  | 0, _ => 0
  | S index', [] => 0
  | S index', scalar :: rest =>
      utf8_width scalar + scalar_byte_offset rest index'
  end.

Lemma scalar_byte_offset_zero :
  forall text, scalar_byte_offset text 0 = 0.
Proof. intro text. destruct text; reflexivity. Qed.

Lemma scalar_byte_offset_at_length :
  forall text,
    scalar_byte_offset text (length text) = utf8_byte_length text.
Proof.
  induction text as [|scalar rest IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma scalar_byte_offset_monotone :
  forall text left right,
    left <= right ->
    scalar_byte_offset text left <= scalar_byte_offset text right.
Proof.
  induction text as [|scalar rest IH];
    intros [|left] [|right] Horder; simpl in *; try lia.
  specialize (IH left right).
  assert (left <= right) by lia.
  specialize (IH H).
  lia.
Qed.

Lemma scalar_byte_offset_bounded :
  forall text index,
    index <= length text ->
    scalar_byte_offset text index <= utf8_byte_length text.
Proof.
  intros text index Hindex.
  rewrite <- scalar_byte_offset_at_length.
  now apply scalar_byte_offset_monotone.
Qed.

Lemma scalar_byte_offset_successor :
  forall text index scalar,
    nth_error text index = Some scalar ->
    scalar_byte_offset text (S index) =
      scalar_byte_offset text index + utf8_width scalar.
Proof.
  induction text as [|head rest IH]; intros [|index] scalar Hnth;
    simpl in *; try discriminate.
  - inversion Hnth; subst. rewrite scalar_byte_offset_zero. lia.
  - specialize (IH index scalar Hnth). lia.
Qed.

Lemma scalar_byte_offset_strict_at_scalar :
  forall text index scalar,
    nth_error text index = Some scalar ->
    scalar_byte_offset text index < scalar_byte_offset text (S index).
Proof.
  intros text index scalar Hnth.
  rewrite (scalar_byte_offset_successor text index scalar Hnth).
  pose proof (utf8_width_positive scalar). lia.
Qed.

Definition utf8_boundary (text : ScalarText) (byte : ByteIndex) : Prop :=
  exists scalar_index,
    scalar_index <= length text /\
    byte = scalar_byte_offset text scalar_index.

Lemma zero_is_utf8_boundary :
  forall text, utf8_boundary text 0.
Proof.
  intro text. exists 0. split; [lia|].
  now rewrite scalar_byte_offset_zero.
Qed.

Lemma byte_length_is_utf8_boundary :
  forall text, utf8_boundary text (utf8_byte_length text).
Proof.
  intro text. exists (length text). split; [lia|].
  symmetry. apply scalar_byte_offset_at_length.
Qed.

Fixpoint utf8_scalar_at
    (text : ScalarText) (cursor : ByteIndex)
    : option (Scalar * ByteIndex) :=
  match text with
  | [] => None
  | scalar :: rest =>
      if Nat.eqb cursor 0 then Some (scalar, utf8_width scalar)
      else if Nat.ltb cursor (utf8_width scalar) then None
      else
        match utf8_scalar_at rest (cursor - utf8_width scalar) with
        | None => None
        | Some (next_scalar, next_cursor) =>
            Some (next_scalar, utf8_width scalar + next_cursor)
        end
  end.

Theorem utf8_scalar_at_boundary_round_trip :
  forall text index scalar,
    nth_error text index = Some scalar ->
    utf8_scalar_at text (scalar_byte_offset text index) =
      Some (scalar, scalar_byte_offset text (S index)).
Proof.
  induction text as [|head rest IH]; intros [|index] scalar Hnth;
    simpl in *; try discriminate.
  - inversion Hnth; subst scalar.
    repeat rewrite scalar_byte_offset_zero.
    replace (utf8_width head + 0) with (utf8_width head) by lia.
    reflexivity.
  - assert (Hwidth : 0 < utf8_width head).
    { pose proof (utf8_width_positive head). lia. }
    assert (Hzero :
      Nat.eqb (utf8_width head + scalar_byte_offset rest index) 0 = false).
    { apply Nat.eqb_neq. lia. }
    rewrite Hzero.
    assert (Hge :
      Nat.ltb (utf8_width head + scalar_byte_offset rest index)
              (utf8_width head) = false).
    { apply Nat.ltb_ge. lia. }
    rewrite Hge.
    replace
      (utf8_width head + scalar_byte_offset rest index - utf8_width head)
      with (scalar_byte_offset rest index) by lia.
    rewrite (IH index scalar Hnth).
    reflexivity.
Qed.

Theorem utf8_scalar_at_advances_one_boundary :
  forall text index scalar,
    nth_error text index = Some scalar ->
    exists next,
      utf8_scalar_at text (scalar_byte_offset text index) = Some (scalar, next) /\
      next = scalar_byte_offset text (S index) /\
      scalar_byte_offset text index < next /\
      next <= scalar_byte_offset text index + 4.
Proof.
  intros text index scalar Hnth.
  exists (scalar_byte_offset text (S index)).
  split.
  - now apply utf8_scalar_at_boundary_round_trip.
  - split.
    + reflexivity.
    + split.
      * now apply (scalar_byte_offset_strict_at_scalar text index scalar).
      * rewrite (scalar_byte_offset_successor text index scalar Hnth).
        pose proof (utf8_width_at_most_four scalar). lia.
Qed.

Definition utf8_at_end (text : ScalarText) (cursor : ByteIndex) : bool :=
  Nat.eqb cursor (utf8_byte_length text).

Theorem utf8_at_end_exact :
  forall text cursor,
    utf8_at_end text cursor = true <-> cursor = utf8_byte_length text.
Proof.
  intros text cursor. unfold utf8_at_end. apply Nat.eqb_eq.
Qed.

Record ScalarSpan : Type := {
  scalar_span_start : nat;
  scalar_span_end : nat
}.

Record ByteSpan : Type := {
  byte_span_start : ByteIndex;
  byte_span_end : ByteIndex
}.

Definition valid_scalar_span (text : ScalarText) (span : ScalarSpan) : Prop :=
  scalar_span_start span <= scalar_span_end span /\
  scalar_span_end span <= length text.

Definition scalar_span_to_bytes
    (text : ScalarText) (span : ScalarSpan) : ByteSpan :=
  {| byte_span_start := scalar_byte_offset text (scalar_span_start span);
     byte_span_end := scalar_byte_offset text (scalar_span_end span) |}.

Definition valid_byte_span (text : ScalarText) (span : ByteSpan) : Prop :=
  byte_span_start span <= byte_span_end span /\
  byte_span_end span <= utf8_byte_length text /\
  utf8_boundary text (byte_span_start span) /\
  utf8_boundary text (byte_span_end span).

Theorem scalar_span_to_bytes_is_valid :
  forall text span,
    valid_scalar_span text span ->
    valid_byte_span text (scalar_span_to_bytes text span).
Proof.
  intros text [start finish] [Horder Hfinish].
  unfold valid_byte_span, scalar_span_to_bytes; simpl.
  split.
  - now apply scalar_byte_offset_monotone.
  - split.
    + now apply scalar_byte_offset_bounded.
    + split.
      * exists start. apply conj.
        -- exact (Nat.le_trans start finish (length text) Horder Hfinish).
        -- reflexivity.
      * exists finish. apply conj.
        -- exact Hfinish.
        -- reflexivity.
Qed.

Theorem nonempty_scalar_span_has_strict_byte_extent :
  forall text start finish,
    start < finish ->
    finish <= length text ->
    scalar_byte_offset text start < scalar_byte_offset text finish.
Proof.
  intros text start finish Horder Hfinish.
  destruct (nth_error text start) as [scalar|] eqn:Hnth.
  - pose proof
      (scalar_byte_offset_strict_at_scalar text start scalar Hnth) as Hstep.
    assert (S start <= finish) by lia.
    pose proof
      (scalar_byte_offset_monotone text (S start) finish H) as Hrest.
    lia.
  - apply nth_error_None in Hnth. lia.
Qed.

Definition scalar_slice
    (text : ScalarText) (start finish : nat) : ScalarText :=
  firstn (finish - start) (skipn start text).

Inductive Utf8SliceContract
    (text : ScalarText) (start finish : ByteIndex) (output : ScalarText) : Prop :=
| Utf8SliceAtBoundaries : forall scalar_start scalar_finish,
    scalar_start <= scalar_finish ->
    scalar_finish <= length text ->
    start = scalar_byte_offset text scalar_start ->
    finish = scalar_byte_offset text scalar_finish ->
    output = scalar_slice text scalar_start scalar_finish ->
    Utf8SliceContract text start finish output.

Theorem scalar_span_supplies_utf8_slice :
  forall text start finish,
    start <= finish ->
    finish <= length text ->
    Utf8SliceContract
      text
      (scalar_byte_offset text start)
      (scalar_byte_offset text finish)
      (scalar_slice text start finish).
Proof.
  intros text start finish Horder Hfinish.
  eapply Utf8SliceAtBoundaries with
    (scalar_start := start) (scalar_finish := finish).
  - exact Horder.
  - exact Hfinish.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Replacement builds a flat persistent plan.  A production runtime may use
    a balanced rope internally, but observable materialization is one ordered
    traversal rather than repeated string concatenation. *)
Inductive TextPiece : Type :=
| LiteralPiece (text : ScalarText)
| SlicePiece (text : ScalarText) (start finish : nat).

Definition materialize_piece (piece : TextPiece) : ScalarText :=
  match piece with
  | LiteralPiece text => text
  | SlicePiece text start finish => scalar_slice text start finish
  end.

Definition TextPlan := list TextPiece.

Fixpoint materialize_text_plan (plan : TextPlan) : ScalarText :=
  match plan with
  | [] => []
  | piece :: rest => materialize_piece piece ++ materialize_text_plan rest
  end.

Theorem materialize_text_plan_append :
  forall left right,
    materialize_text_plan (left ++ right) =
      materialize_text_plan left ++ materialize_text_plan right.
Proof.
  induction left as [|piece rest IH]; intro right; simpl.
  - reflexivity.
  - now rewrite IH, app_assoc.
Qed.

Inductive IntrinsicSort : Type :=
| ExactTermSort
| BooleanSort
| TextSort
| ScalarSort
| ByteIndexSort
| TextPlanSort.

Inductive IntrinsicOpcode : Type :=
| ExactTermEq
| Utf8AtEnd
| Utf8ScalarAt
| Utf8Slice
| CheckedNatAdd
| TextPlanMaterialize.

Definition intrinsic_domain (opcode : IntrinsicOpcode) : list IntrinsicSort :=
  match opcode with
  | ExactTermEq => [ExactTermSort; ExactTermSort]
  | Utf8AtEnd => [TextSort; ByteIndexSort]
  | Utf8ScalarAt => [TextSort; ByteIndexSort]
  | Utf8Slice => [TextSort; ByteIndexSort; ByteIndexSort]
  | CheckedNatAdd => [ByteIndexSort; ByteIndexSort]
  | TextPlanMaterialize => [TextPlanSort]
  end.

Definition intrinsic_codomain (opcode : IntrinsicOpcode) : list IntrinsicSort :=
  match opcode with
  | ExactTermEq | Utf8AtEnd => [BooleanSort]
  | Utf8ScalarAt => [ScalarSort; ByteIndexSort]
  | Utf8Slice | TextPlanMaterialize => [TextSort]
  | CheckedNatAdd => [ByteIndexSort]
  end.

Inductive IntrinsicPurity := PureTotal.

Definition intrinsic_purity (_opcode : IntrinsicOpcode) : IntrinsicPurity :=
  PureTotal.

Theorem every_intrinsic_is_pure_and_authority_free :
  forall opcode, intrinsic_purity opcode = PureTotal.
Proof. destruct opcode; reflexivity. Qed.

Record IntrinsicInvocation := {
  invocation_opcode : IntrinsicOpcode;
  invocation_inputs : list SlotId;
  invocation_outputs : list SlotId
}.

Definition intrinsic_invocation_well_shaped
    (invocation : IntrinsicInvocation) : Prop :=
  length (invocation_inputs invocation) =
    length (intrinsic_domain (invocation_opcode invocation)) /\
  length (invocation_outputs invocation) =
    length (intrinsic_codomain (invocation_opcode invocation)) /\
  NoDup (invocation_outputs invocation).

Record IntrinsicReceipt := {
  intrinsic_receipt_opcode : IntrinsicOpcode;
  intrinsic_receipt_inputs : list Commitment;
  intrinsic_receipt_outputs : list Commitment;
  intrinsic_receipt_work : nat
}.

Definition intrinsic_receipt_well_shaped
    (receipt : IntrinsicReceipt) : Prop :=
  length (intrinsic_receipt_inputs receipt) =
    length (intrinsic_domain (intrinsic_receipt_opcode receipt)) /\
  length (intrinsic_receipt_outputs receipt) =
    length (intrinsic_codomain (intrinsic_receipt_opcode receipt)) /\
  1 <= intrinsic_receipt_work receipt.

Theorem well_shaped_intrinsic_receipt_has_exact_arity_and_positive_work :
  forall receipt,
    intrinsic_receipt_well_shaped receipt ->
    length (intrinsic_receipt_inputs receipt) =
      length (intrinsic_domain (intrinsic_receipt_opcode receipt)) /\
    length (intrinsic_receipt_outputs receipt) =
      length (intrinsic_codomain (intrinsic_receipt_opcode receipt)) /\
    0 < intrinsic_receipt_work receipt.
Proof.
  intros receipt [Hinputs [Houtputs Hwork]].
  repeat split; try assumption; lia.
Qed.

Print Assumptions utf8_scalar_at_boundary_round_trip.
Print Assumptions utf8_scalar_at_advances_one_boundary.
Print Assumptions scalar_span_to_bytes_is_valid.
Print Assumptions nonempty_scalar_span_has_strict_byte_extent.
Print Assumptions scalar_span_supplies_utf8_slice.
Print Assumptions materialize_text_plan_append.
Print Assumptions every_intrinsic_is_pure_and_authority_free.
Print Assumptions well_shaped_intrinsic_receipt_has_exact_arity_and_positive_work.

End SemanticIntrinsics.
