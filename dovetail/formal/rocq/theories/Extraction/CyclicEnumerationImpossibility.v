(*
 * CyclicEnumerationImpossibility: productive cyclic derivation spaces are not
 * finitely exhaustible.
 *
 * CycleCutBoundary.v proves that Dovetail reports a cycle cut as
 * BoundedByCycleCut, not Complete. This companion proof justifies that boundary:
 * a productive self-cycle has one distinct derivation for every finite unrolling
 * depth, so no finite extraction vector can contain all cyclic derivations.
 *
 * The model is intentionally small. `n : nat` denotes the derivation that goes
 * around the cycle exactly n times before taking the acyclic exit. Distinct n
 * are distinct derivation trees because their recursive depth differs.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Dovetail.Extraction Require Import CycleCutBoundary.

Import ListNotations.

Section CyclicEnumerationImpossibility.

  Definition unrolling_depth : Type := nat.

  Inductive productive_self_cycle_derivation : unrolling_depth -> Prop :=
  | ProductiveExit :
      productive_self_cycle_derivation 0
  | ProductiveLoop : forall depth,
      productive_self_cycle_derivation depth ->
      productive_self_cycle_derivation (S depth).

  Fixpoint max_depth (xs : list unrolling_depth) : nat :=
    match xs with
    | [] => 0
    | x :: rest => Nat.max x (max_depth rest)
    end.

  Lemma member_depth_le_max_depth : forall xs depth,
    In depth xs -> depth <= max_depth xs.
  Proof.
    induction xs as [| x rest IH].
    - intros depth Hin. contradiction.
    - intros depth [Heq | Hin].
      + subst depth. simpl. lia.
      + simpl. specialize (IH depth Hin). lia.
  Qed.

  Lemma successor_of_max_depth_is_fresh : forall xs,
    ~ In (S (max_depth xs)) xs.
  Proof.
    intros xs Hin.
    pose proof (member_depth_le_max_depth xs (S (max_depth xs)) Hin) as Hle.
    lia.
  Qed.

  Theorem productive_self_cycle_has_arbitrarily_deep_derivations : forall depth,
    productive_self_cycle_derivation depth.
  Proof.
    induction depth as [| depth IH].
    - apply ProductiveExit.
    - apply ProductiveLoop. exact IH.
  Qed.

  Theorem no_finite_list_contains_all_cycle_unrollings : forall xs,
    ~ (forall depth,
        productive_self_cycle_derivation depth -> In depth xs).
  Proof.
    intros xs Hall.
    apply (successor_of_max_depth_is_fresh xs).
    apply Hall.
    apply productive_self_cycle_has_arbitrarily_deep_derivations.
  Qed.

  Theorem finite_complete_cyclic_enumeration_impossible : forall xs,
    exists missing_depth,
      productive_self_cycle_derivation missing_depth
      /\ ~ In missing_depth xs.
  Proof.
    intros xs.
    exists (S (max_depth xs)).
    split.
    - apply productive_self_cycle_has_arbitrarily_deep_derivations.
    - apply successor_of_max_depth_is_fresh.
  Qed.

  Definition cyclic_complete_claim
      (outputs : list unrolling_depth)
      (status : CompletenessStatus) : Prop :=
    status = Complete /\
    forall depth,
      productive_self_cycle_derivation depth -> In depth outputs.

  Theorem productive_cycle_cannot_claim_finite_complete : forall outputs,
    ~ cyclic_complete_claim outputs Complete.
  Proof.
    intros outputs [Hstatus Hall].
    apply (no_finite_list_contains_all_cycle_unrollings outputs).
    exact Hall.
  Qed.

  Theorem bounded_by_cycle_cut_is_the_finite_boundary : forall outputs,
    ~ cyclic_complete_claim outputs BoundedByCycleCut.
  Proof.
    intros outputs [Hstatus _].
    discriminate Hstatus.
  Qed.

End CyclicEnumerationImpossibility.
