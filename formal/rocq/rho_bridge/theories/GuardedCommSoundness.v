(*
 * GuardedCommSoundness: guards commit atomically with COMM.
 *
 * RSpace receive guards and native guard handlers must behave as source
 * Dovetail guards: a false guard observes no rule firing and consumes no facts.
 * This file models a guarded rule attempt and proves the no-commit and
 * no-fabrication obligations.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section GuardedCommSoundness.

  Definition Fact : Type := nat.

  Definition all_present (facts premises : list Fact) : Prop :=
    forall p, In p premises -> In p facts.

  Definition insert_exact (f : Fact) (facts : list Fact) : list Fact :=
    if existsb (Nat.eqb f) facts then facts else f :: facts.

  Lemma existsb_nat_eq_true : forall x xs,
    existsb (Nat.eqb x) xs = true <-> In x xs.
  Proof.
    intros x xs. rewrite existsb_exists.
    split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Theorem insert_exact_membership : forall facts f x,
    In x (insert_exact f facts) <-> x = f \/ In x facts.
  Proof.
    intros facts f x. unfold insert_exact.
    destruct (existsb (Nat.eqb f) facts) eqn:Hex.
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

  Record GuardedRule : Type := {
    guarded_premises : list Fact;
    guarded_guard : bool;
    guarded_output : Fact
  }.

  Inductive guarded_attempt : list Fact -> GuardedRule -> list Fact -> Prop :=
    | guarded_commit : forall facts r,
        all_present facts (guarded_premises r) ->
        guarded_guard r = true ->
        guarded_attempt facts r (insert_exact (guarded_output r) facts)
    | guarded_reject_guard : forall facts r,
        all_present facts (guarded_premises r) ->
        guarded_guard r = false ->
        guarded_attempt facts r facts
    | guarded_reject_missing : forall facts r,
        ~ all_present facts (guarded_premises r) ->
        guarded_attempt facts r facts.

  Theorem failed_guard_no_commit : forall facts r next,
    guarded_guard r = false ->
    guarded_attempt facts r next ->
    next = facts.
  Proof.
    intros facts r next Hfalse Hattempt.
    inversion Hattempt; subst.
    - rewrite Hfalse in H0. discriminate H0.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem missing_premise_no_commit : forall facts r next,
    ~ all_present facts (guarded_premises r) ->
    guarded_attempt facts r next ->
    next = facts.
  Proof.
    intros facts r next Hmissing Hattempt.
    inversion Hattempt; subst.
    - contradiction.
    - contradiction.
    - reflexivity.
  Qed.

  Theorem guarded_attempt_no_fabrication : forall facts r next x,
    guarded_attempt facts r next ->
    In x next ->
    x = guarded_output r \/ In x facts.
  Proof.
    intros facts r next x Hattempt Hin.
    inversion Hattempt; subst.
    - apply insert_exact_membership. exact Hin.
    - right. exact Hin.
    - right. exact Hin.
  Qed.

  Theorem true_guard_enabled_adds_output : forall facts r,
    all_present facts (guarded_premises r) ->
    guarded_guard r = true ->
    exists next,
      guarded_attempt facts r next
      /\ In (guarded_output r) next.
  Proof.
    intros facts r Hpresent Hguard.
    exists (insert_exact (guarded_output r) facts). split.
    - apply guarded_commit; assumption.
    - apply insert_exact_membership. left. reflexivity.
  Qed.

End GuardedCommSoundness.
