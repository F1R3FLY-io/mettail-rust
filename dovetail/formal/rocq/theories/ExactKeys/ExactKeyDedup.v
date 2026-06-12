(*
 * ExactKeyDedup: Dovetail's exact content keys only remove byte-identical
 * alternatives, and budget exhaustion is reported explicitly.
 *
 * This file models the proof obligations used by dovetail/src/key.rs and
 * dovetail/src/egraph.rs:
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

End ExactKeyDedup.
