(*
 * WorklistFoldEquivalence
 *
 * A continuation-parametric equivalence proof for the explicit work/value
 * stacks used by structural Rust rewrites.  The recursive specification is a
 * fold over mutually recursive trees and forests.  The machine evaluates the
 * same algebra with Visit/Build/Cons tasks and an explicit value stack.
 *
 * The algebra is completely abstract.  Instantiations include:
 *
 *   - receive-node counting (A := nat; algebra := weighted sum),
 *   - constructor-source and rule-summary rendering (A := string),
 *   - structural Clone (A := tree),
 *   - disjunction expansion (A := list (list atom)), and
 *   - ordered visitor observations (A := list event).
 *
 * Thus the proof covers result and source-order equivalence independently of
 * input depth.  LifecyclePdaEquivalence.v separately proves that explicit
 * teardown visits every owned node exactly once.
 *)

From Stdlib Require Import List.

Import ListNotations.

Inductive tree : Type :=
  | Node (tag : nat) (children : forest)
with forest : Type :=
  | FNil
  | FCons (head : tree) (tail : forest).

Section GenericAlgebra.

Variable A : Type.
Variable algebra : nat -> list A -> A.

Fixpoint recursive_fold (input : tree) : A :=
  match input with
  | Node tag children => algebra tag (recursive_folds children)
  end
with recursive_folds (inputs : forest) : list A :=
  match inputs with
  | FNil => []
  | FCons head tail => recursive_fold head :: recursive_folds tail
  end.

Inductive task : Type :=
  | VisitTree (input : tree)
  | VisitForest (inputs : forest)
  | BuildNode (tag : nat)
  | ConsForest.

Inductive value : Type :=
  | TreeValue (result : A)
  | ForestValue (results : list A).

Inductive state : Type :=
  | State (work : list task) (values : list value).

Inductive step : state -> state -> Prop :=
  | StepTree : forall tag children work values,
      step
        (State (VisitTree (Node tag children) :: work) values)
        (State (VisitForest children :: BuildNode tag :: work) values)
  | StepForestNil : forall work values,
      step
        (State (VisitForest FNil :: work) values)
        (State work (ForestValue [] :: values))
  | StepForestCons : forall head tail work values,
      step
        (State (VisitForest (FCons head tail) :: work) values)
        (State
          (VisitTree head :: VisitForest tail :: ConsForest :: work)
          values)
  | StepBuild : forall tag children work values,
      step
        (State (BuildNode tag :: work) (ForestValue children :: values))
        (State work (TreeValue (algebra tag children) :: values))
  | StepCons : forall head tail work values,
      step
        (State
          (ConsForest :: work)
          (ForestValue tail :: TreeValue head :: values))
        (State work (ForestValue (head :: tail) :: values)).

Inductive steps : state -> state -> Prop :=
  | StepsRefl : forall current, steps current current
  | StepsCons : forall first next last,
      step first next -> steps next last -> steps first last.

Lemma steps_trans : forall first middle last,
  steps first middle -> steps middle last -> steps first last.
Proof.
  intros first middle last Hfirst Hlast.
  induction Hfirst.
  - exact Hlast.
  - eapply StepsCons; eauto.
Qed.

Scheme tree_ind_mut := Induction for tree Sort Prop
with forest_ind_mut := Induction for forest Sort Prop.

Combined Scheme tree_forest_ind from tree_ind_mut, forest_ind_mut.

Theorem worklist_fold_equivalence :
  (forall input work values,
    steps
      (State (VisitTree input :: work) values)
      (State work (TreeValue (recursive_fold input) :: values))) /\
  (forall inputs work values,
    steps
      (State (VisitForest inputs :: work) values)
      (State work (ForestValue (recursive_folds inputs) :: values))).
Proof.
  apply tree_forest_ind.
  - intros tag children IHchildren work values. simpl.
    eapply StepsCons.
    + apply StepTree.
    + eapply steps_trans.
      * apply IHchildren.
      * eapply StepsCons.
        -- apply StepBuild.
        -- apply StepsRefl.
  - intros work values. simpl.
    eapply StepsCons.
    + apply StepForestNil.
    + apply StepsRefl.
  - intros head IHhead tail IHtail work values. simpl.
    eapply StepsCons.
    + apply StepForestCons.
    + eapply steps_trans.
      * apply IHhead.
      * eapply steps_trans.
        -- apply IHtail.
        -- eapply StepsCons.
           ++ apply StepCons.
           ++ apply StepsRefl.
Qed.

Corollary worklist_root_equivalence : forall input,
  steps
    (State [VisitTree input] [])
    (State [] [TreeValue (recursive_fold input)]).
Proof.
  intro input.
  destruct worklist_fold_equivalence as [Htree _].
  apply Htree.
Qed.

Section Observer.

Variable observation : Type.
Variable observe : A -> observation.

Corollary worklist_observer_equivalence : forall input,
  exists result,
    steps (State [VisitTree input] []) (State [] [TreeValue result]) /\
    observe result = observe (recursive_fold input).
Proof.
  intro input.
  exists (recursive_fold input).
  split.
  - apply worklist_root_equivalence.
  - reflexivity.
Qed.

End Observer.

End GenericAlgebra.

Print Assumptions worklist_fold_equivalence.
Print Assumptions worklist_root_equivalence.
Print Assumptions worklist_observer_equivalence.
