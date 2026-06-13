(*
 * RhoCostAxisSeparation: refutation and ordering are separate axes.
 *
 * The resource/funding axis can remove a candidate only by explicit refutation.
 * The ordering-cost axis can rank surviving candidates, but ranking must be
 * membership-preserving.  This file proves the exact membership contract for
 * refutation filtering and the no-prune contract for ordering.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section RhoCostAxisSeparation.

  Record Candidate : Type := {
    candidate_id : nat;
    ordering_cost : nat;
    refuted : bool
  }.

  Definition survives_refutation (c : Candidate) : bool :=
    negb (refuted c).

  Definition refutation_filter (candidates : list Candidate) : list Candidate :=
    filter survives_refutation candidates.

  Definition ordering_preserves_membership
      (candidates ranked : list Candidate) : Prop :=
    forall c, In c ranked <-> In c candidates.

  Theorem refutation_filter_sound : forall candidates c,
    In c (refutation_filter candidates) ->
    In c candidates /\ refuted c = false.
  Proof.
    intros candidates c Hin. unfold refutation_filter, survives_refutation in Hin.
    apply filter_In in Hin. destruct Hin as [Hmember Hsurv].
    apply negb_true_iff in Hsurv. split; assumption.
  Qed.

  Theorem refutation_filter_complete : forall candidates c,
    In c candidates ->
    refuted c = false ->
    In c (refutation_filter candidates).
  Proof.
    intros candidates c Hmember Hrefuted.
    unfold refutation_filter, survives_refutation.
    apply filter_In. split.
    - exact Hmember.
    - apply negb_true_iff. exact Hrefuted.
  Qed.

  Theorem ordering_axis_never_refutes : forall candidates ranked c,
    ordering_preserves_membership candidates ranked ->
    In c candidates ->
    In c ranked.
  Proof.
    intros candidates ranked c Hpres Hmember.
    apply Hpres. exact Hmember.
  Qed.

  Theorem ordering_can_change_cost_without_changing_membership :
    forall candidates ranked c,
      ordering_preserves_membership candidates ranked ->
      In c ranked <-> In c candidates.
  Proof.
    intros candidates ranked c Hpres. apply Hpres.
  Qed.

  Theorem only_refutation_removes_candidate : forall candidates c,
    In c candidates ->
    ~ In c (refutation_filter candidates) ->
    refuted c = true.
  Proof.
    intros candidates c Hmember Hremoved.
    destruct (refuted c) eqn:Hrefuted.
    - reflexivity.
    - exfalso. apply Hremoved.
      apply refutation_filter_complete; assumption.
  Qed.

End RhoCostAxisSeparation.
