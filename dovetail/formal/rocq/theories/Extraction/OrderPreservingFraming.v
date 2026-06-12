(*
 * OrderPreservingFraming: the derivation child-key framing used by
 * `write_ordered_framed` is prefix-free and preserves lexicographic order.
 *
 * The Rust encoding writes each payload byte as marker/payload (`1, b`) and
 * writes a segment terminator `0`. This differs from e-node identity framing:
 * identity uses length framing for exact structure; derivation ordering uses
 * this ordered framing so embedding child keys in parent keys cannot invert the
 * child-key order.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

Section OrderPreservingFraming.

  Fixpoint ordered_frame (s : list nat) : list nat :=
    match s with
    | [] => [0]
    | b :: bs => 1 :: b :: ordered_frame bs
    end.

  Fixpoint decode_ordered (bytes : list nat) : option (list nat * list nat) :=
    match bytes with
    | [] => None
    | 0 :: rest => Some ([], rest)
    | 1 :: b :: rest =>
        match decode_ordered rest with
        | Some (payload, tail) => Some (b :: payload, tail)
        | None => None
        end
    | _ :: _ => None
    end.

  Lemma decode_ordered_frame : forall s tail,
    decode_ordered (ordered_frame s ++ tail) = Some (s, tail).
  Proof.
    induction s as [| b bs IH]; intros tail; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Theorem ordered_frame_prefix_free : forall a b tail_a tail_b,
    ordered_frame a ++ tail_a = ordered_frame b ++ tail_b ->
    a = b /\ tail_a = tail_b.
  Proof.
    intros a b tail_a tail_b H.
    assert (Ha : decode_ordered (ordered_frame a ++ tail_a) = Some (a, tail_a)).
    { apply decode_ordered_frame. }
    assert (Hb : decode_ordered (ordered_frame b ++ tail_b) = Some (b, tail_b)).
    { apply decode_ordered_frame. }
    rewrite H in Ha. rewrite Hb in Ha.
    injection Ha as Hpayload Htail. split; symmetry; assumption.
  Qed.

  Inductive lex_le : list nat -> list nat -> Prop :=
    | LexNil : forall ys, lex_le [] ys
    | LexConsLt : forall x y xs ys, x < y -> lex_le (x :: xs) (y :: ys)
    | LexConsEq : forall x xs ys, lex_le xs ys -> lex_le (x :: xs) (x :: ys).

  Theorem ordered_frame_preserves_lex : forall a b,
    lex_le a b -> lex_le (ordered_frame a) (ordered_frame b).
  Proof.
    intros a b Hlex. induction Hlex.
    - destruct ys as [| y ys].
      + simpl. apply LexConsEq. apply LexNil.
      + simpl. apply LexConsLt. lia.
    - simpl. apply LexConsEq. apply LexConsLt. exact H.
    - simpl. apply LexConsEq. apply LexConsEq. exact IHHlex.
  Qed.

  Theorem ordered_frame_injective : forall a b,
    ordered_frame a = ordered_frame b -> a = b.
  Proof.
    intros a b H.
    assert (Hframed : ordered_frame a ++ [] = ordered_frame b ++ []).
    { rewrite !app_nil_r. exact H. }
    destruct (ordered_frame_prefix_free a b [] [] Hframed) as [Hab _].
    exact Hab.
  Qed.

End OrderPreservingFraming.
