(*
 * RhoGroundingAndNames: finite-name obligations for the Rho AST bridge.
 *
 * The M-RHO.1 backend emits normalized Rholang AST directly.  Its generated
 * contracts still rely on Rholang `new` for private result channels and
 * intermediate continuations.  This model proves the obligations needed by
 * that path:
 *   - the allocator chooses a name outside the support of already-ground facts;
 *   - existing grounded fact names cannot be captured by the allocated name;
 *   - alpha-renaming a fresh private name is a no-op on existing public names;
 *   - extending support with a fresh private name preserves groundedness.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section RhoGroundingAndNames.

  Definition Name : Type := nat.

  Record NamedFact : Type := {
    fact_key : nat;
    fact_names : list Name
  }.

  Fixpoint max_name (xs : list Name) : Name :=
    match xs with
    | [] => 0
    | x :: rest => Nat.max x (max_name rest)
    end.

  Definition fresh_name (support : list Name) : Name :=
    S (max_name support).

  Lemma max_name_ge : forall xs x,
    In x xs -> x <= max_name xs.
  Proof.
    induction xs as [| y ys IH]; intros x Hin.
    - contradiction.
    - simpl in *. destruct Hin as [Heq | Hin].
      + subst x. lia.
      + specialize (IH x Hin). lia.
  Qed.

  Theorem fresh_name_not_in_support : forall support,
    ~ In (fresh_name support) support.
  Proof.
    intros support Hin. unfold fresh_name in Hin.
    pose proof (max_name_ge support (S (max_name support)) Hin).
    lia.
  Qed.

  Definition names_of_facts (facts : list NamedFact) : list Name :=
    concat (map fact_names facts).

  Lemma names_of_facts_complete : forall facts f n,
    In f facts ->
    In n (fact_names f) ->
    In n (names_of_facts facts).
  Proof.
    induction facts as [| g rest IH]; intros f n Hf Hn.
    - contradiction.
    - simpl in *. destruct Hf as [Heq | Hf].
      + subst f. apply in_or_app. left. exact Hn.
      + apply in_or_app. right. apply IH with (f := f); assumption.
  Qed.

  Theorem fresh_name_avoids_existing_fact_names : forall facts f n,
    In f facts ->
    In n (fact_names f) ->
    n <> fresh_name (names_of_facts facts).
  Proof.
    intros facts f n Hf Hn Heq.
    pose proof (names_of_facts_complete facts f n Hf Hn) as Hsupport.
    subst n.
    exact (fresh_name_not_in_support (names_of_facts facts) Hsupport).
  Qed.

  Definition rename_name (from to n : Name) : Name :=
    if Nat.eqb n from then to else n.

  Fixpoint rename_names (from to : Name) (xs : list Name) : list Name :=
    match xs with
    | [] => []
    | x :: rest => rename_name from to x :: rename_names from to rest
    end.

  Lemma rename_name_noop : forall from to n,
    n <> from ->
    rename_name from to n = n.
  Proof.
    intros from to n Hneq. unfold rename_name.
    destruct (Nat.eqb n from) eqn:Heq.
    - apply Nat.eqb_eq in Heq. contradiction.
    - reflexivity.
  Qed.

  Theorem rename_fresh_private_name_noop : forall from to names,
    ~ In from names ->
    rename_names from to names = names.
  Proof.
    induction names as [| n rest IH]; intros Hfresh.
    - reflexivity.
    - simpl. f_equal.
      + apply rename_name_noop. intro Heq. subst n. apply Hfresh. left. reflexivity.
      + apply IH. intro Hin. apply Hfresh. right. exact Hin.
  Qed.

  Definition grounded (support names : list Name) : Prop :=
    forall n, In n names -> In n support.

  Theorem fresh_extension_preserves_grounding : forall support names,
    grounded support names ->
    grounded (fresh_name support :: support) names.
  Proof.
    intros support names Hground n Hin.
    right. apply Hground. exact Hin.
  Qed.

  Theorem allocated_private_name_does_not_capture_grounded_names :
    forall support names,
      grounded support names ->
      ~ In (fresh_name support) names.
  Proof.
    intros support names Hground Hin.
    pose proof (Hground (fresh_name support) Hin) as Hsupport.
    exact (fresh_name_not_in_support support Hsupport).
  Qed.

End RhoGroundingAndNames.
