(*
 * RhoObservationFingerprint: exact resting-space observation for RhoNet facts.
 *
 * The runtime oracle observes RSpace by canonical fact keys, not by trace order
 * and not by a lossy hash.  This file models a fingerprint as the characteristic
 * function of exact fact-key membership and proves:
 *   - a fingerprint bit is true exactly when the fact is present;
 *   - fingerprint equivalence is exact set-membership equivalence;
 *   - exact insertion adds only the inserted fact and never hides distinct facts;
 *   - insertion order is irrelevant under fingerprint observation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section RhoObservationFingerprint.

  Definition Fact : Type := nat.

  Definition insert_exact (f : Fact) (facts : list Fact) : list Fact :=
    if existsb (Nat.eqb f) facts then facts else f :: facts.

  Definition fingerprint (facts : list Fact) (x : Fact) : bool :=
    existsb (Nat.eqb x) facts.

  Definition fingerprint_equiv (left right : list Fact) : Prop :=
    forall x, fingerprint left x = fingerprint right x.

  Theorem fingerprint_exact : forall facts x,
    fingerprint facts x = true <-> In x facts.
  Proof.
    intros facts x. unfold fingerprint. rewrite existsb_exists.
    split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Theorem fingerprint_false_exact : forall facts x,
    fingerprint facts x = false <-> ~ In x facts.
  Proof.
    intros facts x.
    destruct (fingerprint facts x) eqn:Hfp.
    - split.
      + intro H. discriminate H.
      + intro Hnot. apply fingerprint_exact in Hfp. contradiction.
    - split.
      + intros _ Hin.
        pose proof (proj2 (fingerprint_exact facts x) Hin) as Htrue.
        rewrite Htrue in Hfp. discriminate Hfp.
      + intros _. reflexivity.
  Qed.

  Theorem fingerprint_equiv_exact : forall left right,
    fingerprint_equiv left right
    <-> (forall x, In x left <-> In x right).
  Proof.
    intros left right. split.
    - intros Heq x. split; intro Hin.
      + apply fingerprint_exact. rewrite <- Heq. apply fingerprint_exact. exact Hin.
      + apply fingerprint_exact. rewrite Heq. apply fingerprint_exact. exact Hin.
    - intros Hset x.
      destruct (fingerprint left x) eqn:Hl.
      + apply fingerprint_exact in Hl. symmetry. apply fingerprint_exact. apply Hset. exact Hl.
      + apply fingerprint_false_exact in Hl. symmetry. apply fingerprint_false_exact.
        intro Hin. apply Hl. apply Hset. exact Hin.
  Qed.

  Theorem insert_exact_membership : forall facts f x,
    In x (insert_exact f facts) <-> x = f \/ In x facts.
  Proof.
    intros facts f x. unfold insert_exact.
    destruct (existsb (Nat.eqb f) facts) eqn:Hex.
    - assert (Hf : In f facts).
      { rewrite existsb_exists in Hex.
        destruct Hex as [y [Hin Heq]]. apply Nat.eqb_eq in Heq.
        subst y. exact Hin. }
      split.
      + intro Hin. right. exact Hin.
      + intros [Heq | Hin].
        * subst x. exact Hf.
        * exact Hin.
    - split.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.

  Theorem fingerprint_insert_exact : forall facts f x,
    fingerprint (insert_exact f facts) x
    = orb (Nat.eqb x f) (fingerprint facts x).
  Proof.
    intros facts f x.
    destruct (Nat.eqb x f) eqn:Hx.
    - apply Nat.eqb_eq in Hx. subst x.
      simpl.
      apply fingerprint_exact. apply insert_exact_membership.
      left. reflexivity.
    - simpl.
      destruct (fingerprint facts x) eqn:Hfacts.
      + apply fingerprint_exact in Hfacts. apply fingerprint_exact.
        apply insert_exact_membership. right. exact Hfacts.
      + apply fingerprint_false_exact in Hfacts. apply fingerprint_false_exact.
        intro Hin. apply insert_exact_membership in Hin.
        destruct Hin as [Heq | Hin].
        * subst x. rewrite Nat.eqb_refl in Hx. discriminate Hx.
        * contradiction.
  Qed.

  Theorem insert_order_fingerprint_equiv : forall facts a b,
    fingerprint_equiv
      (insert_exact a (insert_exact b facts))
      (insert_exact b (insert_exact a facts)).
  Proof.
    intros facts a b x.
    repeat rewrite fingerprint_insert_exact.
    destruct (Nat.eqb x a); destruct (Nat.eqb x b); destruct (fingerprint facts x);
      reflexivity.
  Qed.

End RhoObservationFingerprint.
