(*
 * AmbiguityWitnessEnumeration: schedule-independent candidate preservation.
 *
 * Dovetail represents ambiguity as data: each semantic alternative is an
 * explicit candidate fact.  The Rho backend must therefore let RSpace scheduling
 * choose an execution order without choosing away any enabled candidate.  This
 * file models enabled candidate rules and proves that firing all enabled rules
 * yields exactly the initial facts plus the enabled witnesses, independent of
 * rule order whenever the enabled witness set is the same.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section AmbiguityWitnessEnumeration.

  Definition Fact : Type := nat.

  Definition insert_exact (f : Fact) (facts : list Fact) : list Fact :=
    if existsb (Nat.eqb f) facts then facts else f :: facts.

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

  Record CandidateRule : Type := {
    candidate_enabled : bool;
    candidate_fact : Fact
  }.

  Definition enabled_witnesses (rules : list CandidateRule) : list Fact :=
    map candidate_fact (filter candidate_enabled rules).

  Definition fire_rule (r : CandidateRule) (facts : list Fact) : list Fact :=
    if candidate_enabled r
    then insert_exact (candidate_fact r) facts
    else facts.

  Fixpoint fire_all (rules : list CandidateRule) (facts : list Fact) : list Fact :=
    match rules with
    | [] => facts
    | r :: rest => fire_all rest (fire_rule r facts)
    end.

  Theorem fire_all_membership : forall rules facts x,
    In x (fire_all rules facts)
    <-> In x facts \/ In x (enabled_witnesses rules).
  Proof.
    induction rules as [| r rest IH]; intros facts x.
    - simpl. split; intro H.
      + left. exact H.
      + destruct H as [H | H]; [exact H | contradiction].
    - simpl. unfold fire_rule.
      destruct (candidate_enabled r) eqn:Hen.
      + rewrite IH. rewrite insert_exact_membership.
        unfold enabled_witnesses. simpl. rewrite Hen. simpl.
        fold (enabled_witnesses rest). firstorder subst; auto.
      + rewrite IH. unfold enabled_witnesses. simpl. rewrite Hen.
        fold (enabled_witnesses rest). firstorder subst; auto.
  Qed.

  Theorem enabled_witnesses_enumerated : forall rules facts x,
    In x (enabled_witnesses rules) ->
    In x (fire_all rules facts).
  Proof.
    intros rules facts x Hin.
    apply fire_all_membership. right. exact Hin.
  Qed.

  Theorem enumerated_witnesses_sound : forall rules facts x,
    In x (fire_all rules facts) ->
    In x facts \/ In x (enabled_witnesses rules).
  Proof.
    intros rules facts x Hin.
    apply fire_all_membership. exact Hin.
  Qed.

  Definition same_witness_set (left right : list CandidateRule) : Prop :=
    forall x, In x (enabled_witnesses left) <-> In x (enabled_witnesses right).

  Theorem same_witness_set_same_observation : forall left right facts x,
    same_witness_set left right ->
    (In x (fire_all left facts) <-> In x (fire_all right facts)).
  Proof.
    intros left right facts x Hsame.
    repeat rewrite fire_all_membership.
    specialize (Hsame x). tauto.
  Qed.

End AmbiguityWitnessEnumeration.
