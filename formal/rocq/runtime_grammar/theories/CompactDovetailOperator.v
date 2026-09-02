(** * Compact encoding of payload-free generated Dovetail operators

    A typed generated backend historically assigns one Rust enum variant to
    every object-language constructor.  Most of those operators carry no
    payload: their identity is already the stable semantic-key discriminant.
    Replacing each payload-free variant by an opaque constructor identifier is
    therefore a representation isomorphism, provided payload variants retain
    their types and the identifier cannot be forged outside the generated
    module.

    This model proves the observations used by the backend: round trips,
    framed-key inputs, report labels, unit-pattern tests, and validity. *)

From Stdlib Require Import List String Arith.PeanoNat.
Import ListNotations.
Set Implicit Arguments.

Module CompactDovetailOperator.

  Section Encoding.
    Context {Payload : Type}.

    Inductive LegacyOp : Type :=
    | LegacyUnit : nat -> LegacyOp
    | LegacyPayload : nat -> Payload -> LegacyOp.

    Record ConstructorId : Type := constructor_id {
      raw_constructor_id : nat
    }.

    Inductive CompactOp : Type :=
    | CompactUnit : ConstructorId -> CompactOp
    | CompactPayload : nat -> Payload -> CompactOp.

    Definition encode (op : LegacyOp) : CompactOp :=
      match op with
      | LegacyUnit discriminant =>
          CompactUnit (constructor_id discriminant)
      | LegacyPayload discriminant payload =>
          CompactPayload discriminant payload
      end.

    Definition decode (op : CompactOp) : LegacyOp :=
      match op with
      | CompactUnit id => LegacyUnit (raw_constructor_id id)
      | CompactPayload discriminant payload =>
          LegacyPayload discriminant payload
      end.

    Theorem decode_encode_round_trip :
      forall op, decode (encode op) = op.
    Proof.
      intros op. destruct op; reflexivity.
    Qed.

    Theorem encode_decode_round_trip :
      forall op, encode (decode op) = op.
    Proof.
      intros op. destruct op as [[discriminant] | discriminant payload]; reflexivity.
    Qed.

    Theorem encode_injective :
      forall left right, encode left = encode right -> left = right.
    Proof.
      intros left right Heq.
      rewrite <- (decode_encode_round_trip left).
      rewrite <- (decode_encode_round_trip right).
      now rewrite Heq.
    Qed.

    (** The semantic hasher frames this pair: the stable discriminant followed
        by the optional typed payload bytes.  Encoding changes neither input. *)
    Definition legacy_key_input (op : LegacyOp) : nat * option Payload :=
      match op with
      | LegacyUnit discriminant => (discriminant, None)
      | LegacyPayload discriminant payload =>
          (discriminant, Some payload)
      end.

    Definition compact_key_input (op : CompactOp) : nat * option Payload :=
      match op with
      | CompactUnit id => (raw_constructor_id id, None)
      | CompactPayload discriminant payload =>
          (discriminant, Some payload)
      end.

    Theorem semantic_key_input_preserved :
      forall op, compact_key_input (encode op) = legacy_key_input op.
    Proof.
      intros op. destruct op; reflexivity.
    Qed.

    Definition legacy_display
        (labels : list string) (op : LegacyOp) : option string :=
      nth_error labels
        (match op with
         | LegacyUnit discriminant => discriminant
         | LegacyPayload discriminant _ => discriminant
         end).

    Definition compact_display
        (labels : list string) (op : CompactOp) : option string :=
      nth_error labels
        (match op with
         | CompactUnit id => raw_constructor_id id
         | CompactPayload discriminant _ => discriminant
         end).

    Theorem display_label_preserved :
      forall labels op,
        compact_display labels (encode op) = legacy_display labels op.
    Proof.
      intros labels op. destruct op; reflexivity.
    Qed.

    Definition legacy_matches_unit (target : nat) (op : LegacyOp) : bool :=
      match op with
      | LegacyUnit discriminant => Nat.eqb discriminant target
      | LegacyPayload _ _ => false
      end.

    Definition compact_matches_unit (target : nat) (op : CompactOp) : bool :=
      match op with
      | CompactUnit id => Nat.eqb (raw_constructor_id id) target
      | CompactPayload _ _ => false
      end.

    Theorem associated_constant_pattern_preserved :
      forall target op,
        compact_matches_unit target (encode op) =
        legacy_matches_unit target op.
    Proof.
      intros target op. destruct op; reflexivity.
    Qed.

    Definition legacy_valid (declared : list nat) (op : LegacyOp) : Prop :=
      match op with
      | LegacyUnit discriminant => In discriminant declared
      | LegacyPayload discriminant _ => In discriminant declared
      end.

    Definition compact_valid (declared : list nat) (op : CompactOp) : Prop :=
      match op with
      | CompactUnit id => In (raw_constructor_id id) declared
      | CompactPayload discriminant _ => In discriminant declared
      end.

    Theorem declared_operator_validity_preserved :
      forall declared op,
        legacy_valid declared op <-> compact_valid declared (encode op).
    Proof.
      intros declared op. destruct op; reflexivity.
    Qed.

  End Encoding.

  Print Assumptions decode_encode_round_trip.
  Print Assumptions encode_decode_round_trip.
  Print Assumptions encode_injective.
  Print Assumptions semantic_key_input_preserved.
  Print Assumptions display_label_preserved.
  Print Assumptions associated_constant_pattern_preserved.
  Print Assumptions declared_operator_validity_preserved.

End CompactDovetailOperator.
