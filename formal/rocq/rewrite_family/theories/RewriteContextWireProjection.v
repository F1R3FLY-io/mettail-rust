From Stdlib Require Import Bool PeanoNat.
Require Import RewriteFamilyContext.
Import RewriteFamilyContext.RewriteFamilyContext.

Inductive UnaryWireTag :=
| CanonicalUnary (tag : nat)
| CanonicalRewrite
| LegacyCategory
| LegacyBag
| LegacySet
| LegacyList.

Inductive BinaryWireTag :=
| CanonicalBinary (tag : nat)
| CanonicalArrow.

Inductive WireValue :=
| WireText (name : nat)
| WireUnary (tag : UnaryWireTag) (child : WireValue)
| WireBinary (tag : BinaryWireTag) (first second : WireValue)
| WireInvalid.

Fixpoint encode_canonical (value : Syntax) : WireValue :=
  match value with
  | Atom name => WireText name
  | Unary tag child => WireUnary (CanonicalUnary tag) (encode_canonical child)
  | Binary tag first second =>
      WireBinary (CanonicalBinary tag) (encode_canonical first) (encode_canonical second)
  | Arrow domain codomain =>
      WireBinary CanonicalArrow (encode_canonical domain) (encode_canonical codomain)
  | Rewrite result => WireUnary CanonicalRewrite (encode_canonical result)
  | Invalid => WireInvalid
  end.

Fixpoint decode_canonical (value : WireValue) : Syntax :=
  match value with
  | WireText name => Atom name
  | WireUnary (CanonicalUnary tag) child => Unary tag (decode_canonical child)
  | WireUnary CanonicalRewrite child => Rewrite (decode_canonical child)
  | WireBinary (CanonicalBinary tag) first second =>
      Binary tag (decode_canonical first) (decode_canonical second)
  | WireBinary CanonicalArrow first second =>
      Arrow (decode_canonical first) (decode_canonical second)
  | _ => Invalid
  end.

Definition select_wire (value : Syntax) : WireValue :=
  match value with
  | Atom name => WireUnary LegacyCategory (WireText name)
  | Unary 0 (Atom name) => WireUnary LegacyBag (WireText name)
  | Unary 1 (Atom name) => WireUnary LegacySet (WireText name)
  | Unary 2 (Atom name) => WireUnary LegacyList (WireText name)
  | _ => encode_canonical value
  end.

Definition decode_wire (value : WireValue) : Syntax :=
  match value with
  | WireUnary LegacyCategory (WireText name) => Atom name
  | WireUnary LegacyBag (WireText name) => Unary 0 (Atom name)
  | WireUnary LegacySet (WireText name) => Unary 1 (Atom name)
  | WireUnary LegacyList (WireText name) => Unary 2 (Atom name)
  | _ => decode_canonical value
  end.

Theorem canonical_type_wire_preserves_complete_values :
  forall value, decode_canonical (encode_canonical value) = value.
Proof.
  induction value; simpl; congruence.
Qed.

Theorem legacy_context_wire_encodings_are_unchanged :
  forall name,
    select_wire (Atom name) = WireUnary LegacyCategory (WireText name) /\
    select_wire (Unary 0 (Atom name)) = WireUnary LegacyBag (WireText name) /\
    select_wire (Unary 1 (Atom name)) = WireUnary LegacySet (WireText name) /\
    select_wire (Unary 2 (Atom name)) = WireUnary LegacyList (WireText name).
Proof.
  intro name. repeat split; reflexivity.
Qed.

Theorem selected_context_wire_decodes_to_the_original_type :
  forall value, decode_wire (select_wire value) = value.
Proof.
  intro value. destruct value; try reflexivity.
  - destruct tag as [|[|[|tag]]]; destruct value; simpl;
      repeat rewrite canonical_type_wire_preserves_complete_values; reflexivity.
  - simpl. now repeat rewrite canonical_type_wire_preserves_complete_values.
  - simpl. now repeat rewrite canonical_type_wire_preserves_complete_values.
  - simpl. now rewrite canonical_type_wire_preserves_complete_values.
Qed.

Theorem extended_context_children_are_canonical_and_ordered :
  (forall tag first second,
    select_wire (Binary tag first second) =
      WireBinary (CanonicalBinary tag) (encode_canonical first) (encode_canonical second)) /\
  (forall domain codomain,
    select_wire (Arrow domain codomain) =
      WireBinary CanonicalArrow (encode_canonical domain) (encode_canonical codomain)) /\
  (forall result,
    select_wire (Rewrite result) = WireUnary CanonicalRewrite (encode_canonical result)) /\
  (forall tag child,
    encode_canonical (Unary tag child) =
      WireUnary (CanonicalUnary tag) (encode_canonical child)).
Proof.
  repeat split; intros; reflexivity.
Qed.

Theorem legacy_tags_cannot_be_nested_as_canonical_types :
  forall name,
    decode_canonical (WireUnary LegacyCategory (WireText name)) = Invalid /\
    decode_canonical (WireUnary LegacyBag (WireText name)) = Invalid /\
    decode_canonical (WireUnary LegacySet (WireText name)) = Invalid /\
    decode_canonical (WireUnary LegacyList (WireText name)) = Invalid.
Proof.
  intro name. repeat split; reflexivity.
Qed.

Theorem context_wire_preserves_admission_and_refusal :
  forall allow_family value,
    decode_context allow_family (decode_wire (select_wire value)) =
      decode_context allow_family value.
Proof.
  intros. now rewrite selected_context_wire_decodes_to_the_original_type.
Qed.

Print Assumptions canonical_type_wire_preserves_complete_values.
Print Assumptions legacy_context_wire_encodings_are_unchanged.
Print Assumptions selected_context_wire_decodes_to_the_original_type.
Print Assumptions extended_context_children_are_canonical_and_ordered.
Print Assumptions legacy_tags_cannot_be_nested_as_canonical_types.
Print Assumptions context_wire_preserves_admission_and_refusal.
