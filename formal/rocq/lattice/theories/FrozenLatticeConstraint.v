(*
 * FrozenLatticeConstraint: semantic separation between constructing a
 * subtype lattice and deciding propositions in an installed lattice.
 *
 * Rust correspondence:
 *   MutableStore / assert_atom  -- LatticeStore / LatticeTheory::propagate
 *   Snapshot / atom_truth       -- FrozenLatticeTheory relation snapshot
 *   Formula / eval              -- TheoryPred<FrozenLatticeTheory>
 *   decide_exact                -- DecidableConstraintTheory::decide_exact
 *
 * A mutable builder accepts a new edge because it extends state.  That fact is
 * not evidence that the edge was already true.  A frozen snapshot instead has
 * a single immutable interpretation; every ground Boolean predicate is
 * therefore decidable by evaluation in that interpretation.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.

Import ListNotations.

Section FrozenLatticeConstraint.

  Variable TypeId : Type.

  Record Atom : Type := atom {
    atom_sub : TypeId;
    atom_sup : TypeId
  }.

  (* A snapshot is the immutable, already-closed subtype observation. *)
  Definition Snapshot : Type := TypeId -> TypeId -> bool.

  Definition atom_truth (snapshot : Snapshot) (constraint : Atom) : bool :=
    snapshot (atom_sub constraint) (atom_sup constraint).

  (* Query returns the same snapshot.  Observation cannot add an edge. *)
  Definition query (snapshot : Snapshot) (constraint : Atom)
      : bool * Snapshot :=
    (atom_truth snapshot constraint, snapshot).

  Theorem query_preserves_snapshot : forall snapshot constraint,
    snd (query snapshot constraint) = snapshot.
  Proof.
    reflexivity.
  Qed.

  Theorem query_reports_exact_atom_truth : forall snapshot constraint,
    fst (query snapshot constraint) = atom_truth snapshot constraint.
  Proof.
    reflexivity.
  Qed.

  (* The construction algebra is deliberately separate.  Successful
     assertion says that a larger store was produced, not that the old frozen
     relation contained the asserted edge. *)
  Definition MutableStore : Type := list Atom.

  Definition assert_atom (store : MutableStore) (constraint : Atom)
      : option MutableStore :=
    Some (constraint :: store).

  Theorem assertion_success_does_not_certify_snapshot_truth :
    forall snapshot store constraint,
      atom_truth snapshot constraint = false ->
      assert_atom store constraint = Some (constraint :: store) /\
      atom_truth snapshot constraint = false.
  Proof.
    intros snapshot store constraint Hfalse.
    split; [reflexivity | exact Hfalse].
  Qed.

  Inductive Formula : Type :=
    | FTrue
    | FFalse
    | FAtom (constraint : Atom)
    | FAnd (left right : Formula)
    | FOr (left right : Formula)
    | FNot (inner : Formula).

  Fixpoint eval (snapshot : Snapshot) (formula : Formula) : bool :=
    match formula with
    | FTrue => true
    | FFalse => false
    | FAtom constraint => atom_truth snapshot constraint
    | FAnd lhs rhs => andb (eval snapshot lhs) (eval snapshot rhs)
    | FOr lhs rhs => orb (eval snapshot lhs) (eval snapshot rhs)
    | FNot inner => negb (eval snapshot inner)
    end.

  (* There is one fixed interpretation.  Unit is the identity witness carried
     by the Rust implementation; predicates contain ground TypeIds. *)
  Definition semantically_satisfiable
      (snapshot : Snapshot) (formula : Formula) : Prop :=
    exists (_ : unit), eval snapshot formula = true.

  Inductive ExactDecision : Type :=
    | Satisfiable
    | Unsatisfiable.

  Definition decide_exact (snapshot : Snapshot) (formula : Formula)
      : ExactDecision :=
    if eval snapshot formula then Satisfiable else Unsatisfiable.

  Theorem exact_satisfiable_sound_complete : forall snapshot formula,
    decide_exact snapshot formula = Satisfiable <->
    semantically_satisfiable snapshot formula.
  Proof.
    intros snapshot formula.
    unfold decide_exact, semantically_satisfiable.
    destruct (eval snapshot formula) eqn:Heval.
    - split.
      + intros _. exists tt. reflexivity.
      + intros _. reflexivity.
    - split.
      + discriminate.
      + intros [_ Htrue]. discriminate.
  Qed.

  Theorem exact_unsatisfiable_sound_complete : forall snapshot formula,
    decide_exact snapshot formula = Unsatisfiable <->
    ~ semantically_satisfiable snapshot formula.
  Proof.
    intros snapshot formula.
    unfold decide_exact, semantically_satisfiable.
    destruct (eval snapshot formula) eqn:Heval.
    - split.
      + discriminate.
      + intros Hnot. exfalso. apply Hnot. exists tt. reflexivity.
    - split.
      + intros _ [_ Htrue]. discriminate.
      + intros _. reflexivity.
  Qed.

  Theorem exact_complement : forall snapshot formula,
    decide_exact snapshot (FNot formula) = Satisfiable <->
    decide_exact snapshot formula = Unsatisfiable.
  Proof.
    intros snapshot formula.
    unfold decide_exact. simpl.
    destruct (eval snapshot formula); cbn.
    - split; discriminate.
    - split; intros _; reflexivity.
  Qed.

  Definition entails (snapshot : Snapshot) (premise conclusion : Formula)
      : Prop :=
    eval snapshot premise = true -> eval snapshot conclusion = true.

  Definition counterexample_free
      (snapshot : Snapshot) (premise conclusion : Formula) : bool :=
    negb (andb (eval snapshot premise) (negb (eval snapshot conclusion))).

  Theorem counterexample_decision_is_entailment :
    forall snapshot premise conclusion,
      counterexample_free snapshot premise conclusion = true <->
      entails snapshot premise conclusion.
  Proof.
    intros snapshot premise conclusion.
    unfold counterexample_free, entails.
    destruct (eval snapshot premise);
      destruct (eval snapshot conclusion);
      simpl; tauto.
  Qed.

  (* A plain base type denotes the constantly true predicate.  Consequently,
     Base <: {x : T | Q} is valid exactly when Q is true in the frozen
     interpretation, not when Q could be added to a mutable store. *)
  Theorem base_to_refined_requires_truth : forall snapshot predicate,
    entails snapshot FTrue predicate <-> eval snapshot predicate = true.
  Proof.
    intros snapshot predicate. unfold entails. simpl.
    split.
    - intros H. apply H. reflexivity.
    - intros H _. exact H.
  Qed.

End FrozenLatticeConstraint.

Print Assumptions query_preserves_snapshot.
Print Assumptions assertion_success_does_not_certify_snapshot_truth.
Print Assumptions exact_satisfiable_sound_complete.
Print Assumptions exact_unsatisfiable_sound_complete.
Print Assumptions exact_complement.
Print Assumptions counterexample_decision_is_entailment.
Print Assumptions base_to_refined_requires_truth.
