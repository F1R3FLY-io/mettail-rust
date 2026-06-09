(*
 * EGraphBudgetDedup: exact e-node sharing and budgeted saturation inserts.
 *
 * Models the implementation boundary used by prattail/src/egraph.rs:
 *
 *   - canonical e-node keys are deduplicated by exact key equality;
 *   - deduplication preserves membership of every distinct key;
 *   - budget-aware insertion never exceeds the configured node budget;
 *   - inserting a new distinct key at capacity reports explicit overflow.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

(*  Spec-to-Code Traceability                                             *)
(*  ===================================================================  *)
(*  Rocq Definition          | Rust Implementation                  | Line *)
(*  -------------------------+--------------------------------------+------*)
(*  Key                      | ENode                                | egraph.rs *)
(*  dedup                    | rebuild_exact_indices class-node set | egraph.rs *)
(*  budget_add               | try_add_with_budget                  | egraph.rs *)
(*  overflow flag            | SaturationResult::node_limit_reached | egraph.rs *)
(*  ===================================================================  *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section EGraphBudgetDedup.

  Variable Key : Type.
  Variable key_eq_dec : forall x y : Key, {x = y} + {x <> y}.

  Fixpoint dedup (keys : list Key) : list Key :=
    match keys with
    | [] => []
    | k :: rest =>
        if in_dec key_eq_dec k rest
        then dedup rest
        else k :: dedup rest
    end.

  Definition exact_equiv (xs ys : list Key) : Prop :=
    forall k, In k xs <-> In k ys.

  Lemma in_dedup_iff : forall k keys,
    In k (dedup keys) <-> In k keys.
  Proof.
    intros k keys. induction keys as [| h rest IH].
    - simpl. split; intro H; exact H.
    - simpl. destruct (in_dec key_eq_dec h rest) as [Hin | Hnot].
      + split.
        * intro H. right. apply IH. exact H.
        * intro H. apply IH. destruct H as [Heq | Hrest].
          -- subst. exact Hin.
          -- exact Hrest.
      + simpl. split.
        * intro H. destruct H as [Heq | Hrest].
          -- left. exact Heq.
          -- right. apply IH. exact Hrest.
        * intro H. destruct H as [Heq | Hrest].
          -- left. exact Heq.
          -- right. apply IH. exact Hrest.
  Qed.

  Lemma dedup_exact_equiv : forall keys,
    exact_equiv (dedup keys) keys.
  Proof.
    intros keys k. apply in_dedup_iff.
  Qed.

  Lemma NoDup_dedup : forall keys,
    NoDup (dedup keys).
  Proof.
    induction keys as [| h rest IH].
    - simpl. constructor.
    - simpl. destruct (in_dec key_eq_dec h rest) as [_ | Hnot].
      + exact IH.
      + constructor.
        * intro Hin. apply Hnot. apply in_dedup_iff. exact Hin.
        * exact IH.
  Qed.

  Lemma length_dedup_le : forall keys,
    length (dedup keys) <= length keys.
  Proof.
    induction keys as [| h rest IH].
    - simpl. lia.
    - simpl. destruct (in_dec key_eq_dec h rest); simpl; lia.
  Qed.

  Definition budget_add (max_nodes : nat) (k : Key) (keys : list Key)
    : list Key * bool :=
    if in_dec key_eq_dec k keys then
      (keys, false)
    else if length keys <? max_nodes then
      (k :: keys, false)
    else
      (keys, true).

  Lemma budget_add_preserves_existing : forall max_nodes k keys x,
    In x keys ->
    In x (fst (budget_add max_nodes k keys)).
  Proof.
    intros max_nodes k keys x Hin.
    unfold budget_add. destruct (in_dec key_eq_dec k keys).
    - simpl. exact Hin.
    - destruct (length keys <? max_nodes); simpl.
      + right. exact Hin.
      + exact Hin.
  Qed.

  Lemma budget_add_no_spurious_key : forall max_nodes k keys x,
    In x (fst (budget_add max_nodes k keys)) ->
    x = k \/ In x keys.
  Proof.
    intros max_nodes k keys x Hin.
    unfold budget_add in Hin. destruct (in_dec key_eq_dec k keys).
    - right. exact Hin.
    - destruct (length keys <? max_nodes); simpl in Hin.
      + destruct Hin as [Heq | Htail].
        * left. symmetry. exact Heq.
        * right. exact Htail.
      + right. exact Hin.
  Qed.

  Lemma budget_add_no_overshoot : forall max_nodes k keys,
    length keys <= max_nodes ->
    length (fst (budget_add max_nodes k keys)) <= max_nodes.
  Proof.
    intros max_nodes k keys Hle.
    unfold budget_add. destruct (in_dec key_eq_dec k keys).
    - simpl. exact Hle.
    - destruct (length keys <? max_nodes) eqn:Hlt; simpl.
      + apply Nat.ltb_lt in Hlt. lia.
      + exact Hle.
  Qed.

  Lemma budget_add_success_contains_key : forall max_nodes k keys,
    snd (budget_add max_nodes k keys) = false ->
    In k (fst (budget_add max_nodes k keys)).
  Proof.
    intros max_nodes k keys Hsuccess.
    unfold budget_add in *. destruct (in_dec key_eq_dec k keys) as [Hin | Hnot].
    - simpl. exact Hin.
    - destruct (length keys <? max_nodes) eqn:Hlt.
      + simpl. left. reflexivity.
      + simpl in Hsuccess. discriminate.
  Qed.

  Lemma budget_add_overflow_explicit : forall max_nodes k keys,
    ~ In k keys ->
    length keys >= max_nodes ->
    budget_add max_nodes k keys = (keys, true).
  Proof.
    intros max_nodes k keys Hfresh Hfull.
    unfold budget_add. destruct (in_dec key_eq_dec k keys) as [Hin | _].
    - contradiction.
    - destruct (length keys <? max_nodes) eqn:Hlt.
      + apply Nat.ltb_lt in Hlt. lia.
      + reflexivity.
  Qed.

  Definition canonical_budget_add max_nodes k keys :=
    budget_add max_nodes k (dedup keys).

  Theorem exact_dedup_preserves_distinct_keys : forall keys,
    exact_equiv (dedup keys) keys /\ NoDup (dedup keys).
  Proof.
    intro keys. split.
    - apply dedup_exact_equiv.
    - apply NoDup_dedup.
  Qed.

  Theorem canonical_budget_add_preserves_existing : forall max_nodes k keys x,
    In x keys ->
    In x (fst (canonical_budget_add max_nodes k keys)).
  Proof.
    intros max_nodes k keys x Hin.
    unfold canonical_budget_add.
    apply budget_add_preserves_existing.
    apply in_dedup_iff. exact Hin.
  Qed.

  Theorem canonical_budget_add_no_overshoot : forall max_nodes k keys,
    length (dedup keys) <= max_nodes ->
    length (fst (canonical_budget_add max_nodes k keys)) <= max_nodes.
  Proof.
    intros max_nodes k keys Hle.
    unfold canonical_budget_add.
    apply budget_add_no_overshoot. exact Hle.
  Qed.

  Theorem canonical_budget_add_overflow_is_explicit : forall max_nodes k keys,
    ~ In k keys ->
    length (dedup keys) >= max_nodes ->
    canonical_budget_add max_nodes k keys = (dedup keys, true).
  Proof.
    intros max_nodes k keys Hfresh Hfull.
    unfold canonical_budget_add.
    apply budget_add_overflow_explicit.
    - intro Hin. apply Hfresh. apply in_dedup_iff. exact Hin.
    - exact Hfull.
  Qed.

End EGraphBudgetDedup.
