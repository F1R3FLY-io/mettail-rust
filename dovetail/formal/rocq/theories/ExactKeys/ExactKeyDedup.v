(*
 * ExactKeyDedup: Dovetail's exact content keys only remove byte-identical
 * alternatives, and budget exhaustion is reported explicitly.
 *
 * This file models the proof obligations used by dovetail/src/key.rs and
 * dovetail/src/egraph.rs:
 *   - length framing is injective for composite exact keys;
 *   - ordered child-key framing is prefix-free and preserves lexicographic order;
 *   - dedup is by exact key equality, not by weight or heuristic equality;
 *   - distinct keys cannot be conflated by dedup;
 *   - add-with-budget never overshoots the node budget;
 *   - an overflow result preserves the prior state and reports the refusal.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section ExactKeyDedup.

  Definition Key := nat.

  Definition framed_segment (s : list nat) : list nat :=
    length s :: s.

  Definition decode_framed (bytes : list nat) : option (list nat * list nat) :=
    match bytes with
    | [] => None
    | n :: rest =>
        if n <=? length rest
        then Some (firstn n rest, skipn n rest)
        else None
    end.

  Lemma firstn_length_app : forall (xs tail : list nat),
    firstn (length xs) (xs ++ tail) = xs.
  Proof.
    induction xs as [| x xs IH]; intros tail; simpl.
    - reflexivity.
    - f_equal. apply IH.
  Qed.

  Lemma skipn_length_app : forall (xs tail : list nat),
    skipn (length xs) (xs ++ tail) = tail.
  Proof.
    induction xs as [| x xs IH]; intros tail; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma decode_framed_segment : forall s tail,
    decode_framed (framed_segment s ++ tail) = Some (s, tail).
  Proof.
    intros s tail. unfold framed_segment, decode_framed. simpl.
    destruct (length s <=? length (s ++ tail)) eqn:Hle.
    - rewrite firstn_length_app. rewrite skipn_length_app. reflexivity.
    - apply Nat.leb_gt in Hle. rewrite length_app in Hle. lia.
  Qed.

  Definition framed_pair (a b : list nat) : list nat :=
    framed_segment a ++ framed_segment b.

  Theorem framed_pair_injective : forall a b c d,
    framed_pair a b = framed_pair c d ->
    a = c /\ b = d.
  Proof.
    intros a b c d H.
    assert (Hleft : decode_framed (framed_pair a b) = Some (a, framed_segment b)).
    { unfold framed_pair. apply decode_framed_segment. }
    assert (Hright : decode_framed (framed_pair c d) = Some (c, framed_segment d)).
    { unfold framed_pair. apply decode_framed_segment. }
    rewrite H in Hleft. rewrite Hright in Hleft.
    injection Hleft as Ha _ Hpayload.
    subst c. split.
    - reflexivity.
    - symmetry. exact Hpayload.
  Qed.

  (* Model of `write_ordered_framed`: each payload byte is written as
     marker/payload (`1, b`) and the segment is terminated by `0`. *)
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

  Definition exact_dedup (keys : list Key) : list Key :=
    nodup Nat.eq_dec keys.

  Lemma exact_dedup_complete : forall k keys,
    In k keys -> In k (exact_dedup keys).
  Proof.
    intros k keys Hin. unfold exact_dedup. apply nodup_In. exact Hin.
  Qed.

  Lemma exact_dedup_sound : forall k keys,
    In k (exact_dedup keys) -> In k keys.
  Proof.
    intros k keys Hin. unfold exact_dedup in Hin. apply nodup_In in Hin. exact Hin.
  Qed.

  Lemma exact_dedup_nodup : forall keys,
    NoDup (exact_dedup keys).
  Proof.
    intros keys. unfold exact_dedup. apply NoDup_nodup.
  Qed.

  Theorem distinct_keys_not_conflated : forall k1 k2 keys,
    k1 <> k2 ->
    In k1 keys ->
    In k2 keys ->
    In k1 (exact_dedup keys) /\ In k2 (exact_dedup keys) /\ k1 <> k2.
  Proof.
    intros k1 k2 keys Hneq H1 H2. repeat split.
    - apply exact_dedup_complete. exact H1.
    - apply exact_dedup_complete. exact H2.
    - exact Hneq.
  Qed.

  (* A production index may bucket exact keys by a finite accelerator, but the
     accelerator never decides equality. This models the immutable
     (length,fingerprint) bucket used by ContentKeyMap/ContentKeySet: a bucket
     hit is followed by exact key equality, including on collisions. *)
  Definition accelerated_exact_equal
      (accelerator : Key -> nat) (left right : Key) : bool :=
    Nat.eqb (accelerator left) (accelerator right) && Nat.eqb left right.

  Theorem accelerated_exact_equal_iff : forall accelerator left right,
    accelerated_exact_equal accelerator left right = true <-> left = right.
  Proof.
    intros accelerator left right. unfold accelerated_exact_equal.
    rewrite Bool.andb_true_iff. split.
    - intros [_ Hkey]. now apply Nat.eqb_eq in Hkey.
    - intro Hequal. subst right. split; apply Nat.eqb_refl.
  Qed.

  Theorem accelerator_collision_uses_exact_fallback : forall accelerator left right,
    accelerator left = accelerator right ->
    left <> right ->
    accelerated_exact_equal accelerator left right = false.
  Proof.
    intros accelerator left right Haccelerator Hdistinct.
    unfold accelerated_exact_equal. rewrite Haccelerator, Nat.eqb_refl. simpl.
    now apply Nat.eqb_neq.
  Qed.

  Inductive AddResult : Type :=
    | Added : nat -> AddResult
    | Overflow : nat -> AddResult.

  Definition try_add_with_budget (budget used : nat) : AddResult :=
    if used <? budget then Added (S used) else Overflow used.

  Theorem added_never_overshoots_budget : forall budget used used',
    used <= budget ->
    try_add_with_budget budget used = Added used' ->
    used' <= budget.
  Proof.
    intros budget used used' Hle Hadd.
    unfold try_add_with_budget in Hadd.
    destruct (used <? budget) eqn:Hlt.
    - inversion Hadd. subst used'. apply Nat.ltb_lt in Hlt. lia.
    - discriminate.
  Qed.

  Theorem overflow_preserves_state : forall budget used used',
    try_add_with_budget budget used = Overflow used' ->
    used' = used /\ budget <= used.
  Proof.
    intros budget used used' Hover.
    unfold try_add_with_budget in Hover.
    destruct (used <? budget) eqn:Hlt.
    - discriminate.
    - inversion Hover. subst used'. split.
      + reflexivity.
      + apply Nat.ltb_ge. exact Hlt.
  Qed.

  Print Assumptions accelerated_exact_equal_iff.
  Print Assumptions accelerator_collision_uses_exact_fallback.

End ExactKeyDedup.
