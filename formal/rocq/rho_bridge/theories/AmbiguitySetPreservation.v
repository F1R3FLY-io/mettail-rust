(*
 * AmbiguitySetPreservation: scheduler order must not choose semantic
 * alternatives away.
 *
 * Ambiguity is represented as explicit candidate facts.  RSpace may schedule
 * enabled COMMs in different orders, but the observation is exact-key set
 * membership.  This file proves that emitting the same candidate set in any
 * order yields the same observed ambiguity set.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section AmbiguitySetPreservation.

  Definition Candidate : Type := nat.

  Definition insert_exact (c : Candidate) (seen : list Candidate) : list Candidate :=
    if existsb (Nat.eqb c) seen then seen else c :: seen.

  Lemma existsb_nat_eq_true : forall x xs,
    existsb (Nat.eqb x) xs = true <-> In x xs.
  Proof.
    intros x xs. rewrite existsb_exists.
    split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Theorem insert_exact_membership : forall seen c x,
    In x (insert_exact c seen) <-> x = c \/ In x seen.
  Proof.
    intros seen c x. unfold insert_exact.
    destruct (existsb (Nat.eqb c) seen) eqn:Hex.
    - apply existsb_nat_eq_true in Hex.
      split.
      + intro Hin. right. exact Hin.
      + intros [Heq | Hin].
        * subst x. exact Hex.
        * exact Hin.
    - split.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.

  Fixpoint emit_schedule (schedule seed : list Candidate) : list Candidate :=
    match schedule with
    | [] => seed
    | c :: rest => emit_schedule rest (insert_exact c seed)
    end.

  Theorem emit_schedule_membership : forall schedule seed x,
    In x (emit_schedule schedule seed)
    <-> In x seed \/ In x schedule.
  Proof.
    induction schedule as [| c rest IH]; intros seed x.
    - simpl. split; intro H.
      + left. exact H.
      + destruct H as [H | H]; [exact H | contradiction].
    - simpl. rewrite IH. rewrite insert_exact_membership.
      split.
      + intros [[Heq | Hin] | Hin].
        * right. left. symmetry. exact Heq.
        * left. exact Hin.
        * right. right. exact Hin.
      + intros [Hin | [Heq | Hin]].
        * left. right. exact Hin.
        * left. left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.

  Definition same_candidate_set (left right : list Candidate) : Prop :=
    forall c, In c left <-> In c right.

  Theorem schedule_order_preserves_ambiguity_set : forall left right seed x,
    same_candidate_set left right ->
    (In x (emit_schedule left seed) <-> In x (emit_schedule right seed)).
  Proof.
    intros left right seed x Hsame.
    repeat rewrite emit_schedule_membership.
    specialize (Hsame x). tauto.
  Qed.

End AmbiguitySetPreservation.
