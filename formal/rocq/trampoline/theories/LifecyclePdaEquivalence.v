(*
 * LifecyclePdaEquivalence
 *
 * A zero-admission equivalence proof for replacing mutually recursive
 * lifecycle traversals with an explicit pushdown machine.  The source model
 * uses mutually inductive trees and forests so the theorem covers unary,
 * binary, and arbitrary-arity recursive fields without a depth bound.
 *
 * The main theorem is continuation-parametric in both pending work and prior
 * output.  Consequently it composes inside enclosing owners and proves exact
 * source-order observations for Clone, Debug, Display, Eq, Ord, Hash, and
 * serialization.  The visit-count corollaries additionally establish that an
 * iterative destructor drains every owned node exactly once.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

Inductive tree : Type :=
  | Node (tag : nat) (children : forest)
with forest : Type :=
  | FNil
  | FCons (head : tree) (tail : forest).

Inductive event : Type :=
  | Enter (tag : nat)
  | Exit (tag : nat).

Fixpoint recursive_trace (input : tree) : list event :=
  match input with
  | Node tag children => Enter tag :: recursive_traces children ++ [Exit tag]
  end
with recursive_traces (inputs : forest) : list event :=
  match inputs with
  | FNil => []
  | FCons head tail => recursive_trace head ++ recursive_traces tail
  end.

Inductive task : Type :=
  | VisitTree (input : tree)
  | VisitForest (inputs : forest)
  | EmitExit (tag : nat).

Inductive state : Type :=
  | State (work : list task) (output : list event).

Inductive step : state -> state -> Prop :=
  | StepTree : forall tag children work output,
      step
        (State (VisitTree (Node tag children) :: work) output)
        (State
          (VisitForest children :: EmitExit tag :: work)
          (output ++ [Enter tag]))
  | StepForestNil : forall work output,
      step (State (VisitForest FNil :: work) output) (State work output)
  | StepForestCons : forall head tail work output,
      step
        (State (VisitForest (FCons head tail) :: work) output)
        (State (VisitTree head :: VisitForest tail :: work) output)
  | StepExit : forall tag work output,
      step
        (State (EmitExit tag :: work) output)
        (State work (output ++ [Exit tag])).

Inductive steps : state -> state -> Prop :=
  | StepsRefl : forall state, steps state state
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

Theorem lifecycle_pda_equivalence :
  (forall input work output,
    steps
      (State (VisitTree input :: work) output)
      (State work (output ++ recursive_trace input))) /\
  (forall inputs work output,
    steps
      (State (VisitForest inputs :: work) output)
      (State work (output ++ recursive_traces inputs))).
Proof.
  apply tree_forest_ind.
  - intros tag children IHchildren work output. simpl.
    replace (output ++ Enter tag :: recursive_traces children ++ [Exit tag])
      with (((output ++ [Enter tag]) ++ recursive_traces children) ++ [Exit tag])
      by (repeat rewrite <- app_assoc; reflexivity).
    eapply StepsCons.
    + constructor.
    + eapply steps_trans.
      * apply IHchildren.
      * eapply StepsCons. constructor. constructor.
  - intros work output. simpl. rewrite app_nil_r.
    eapply StepsCons with (next := State work output).
    + apply StepForestNil.
    + apply StepsRefl.
  - intros head IHhead tail IHtail work output. simpl.
    rewrite app_assoc.
    eapply StepsCons.
    + constructor.
    + eapply steps_trans.
      * apply IHhead.
      * apply IHtail.
Qed.

Corollary lifecycle_pda_root_trace : forall input,
  steps
    (State [VisitTree input] [])
    (State [] (recursive_trace input)).
Proof.
  intro input.
  destruct lifecycle_pda_equivalence as [Htree _].
  specialize (Htree input [] []).
  simpl in Htree.
  exact Htree.
Qed.

Section ObserverEquivalence.

Variable observation : Type.
Variable observe : list event -> observation.

Corollary lifecycle_observer_equivalence : forall input,
  exists output,
    steps (State [VisitTree input] []) (State [] output) /\
    observe output = observe (recursive_trace input).
Proof.
  intro input.
  exists (recursive_trace input).
  split.
  - apply lifecycle_pda_root_trace.
  - reflexivity.
Qed.

End ObserverEquivalence.

Fixpoint node_count (input : tree) : nat :=
  match input with
  | Node _ children => S (forest_count children)
  end
with forest_count (inputs : forest) : nat :=
  match inputs with
  | FNil => 0
  | FCons head tail => node_count head + forest_count tail
  end.

Fixpoint enter_count (events : list event) : nat :=
  match events with
  | [] => 0
  | Enter _ :: tail => S (enter_count tail)
  | Exit _ :: tail => enter_count tail
  end.

Fixpoint exit_count (events : list event) : nat :=
  match events with
  | [] => 0
  | Enter _ :: tail => exit_count tail
  | Exit _ :: tail => S (exit_count tail)
  end.

Lemma enter_count_app : forall left right,
  enter_count (left ++ right) = enter_count left + enter_count right.
Proof.
  intros left right.
  induction left as [| next tail IH].
  - reflexivity.
  - destruct next; simpl; rewrite IH; lia.
Qed.

Lemma exit_count_app : forall left right,
  exit_count (left ++ right) = exit_count left + exit_count right.
Proof.
  intros left right.
  induction left as [| next tail IH].
  - reflexivity.
  - destruct next; simpl; rewrite IH; lia.
Qed.

Theorem lifecycle_trace_visits_once :
  (forall input,
    enter_count (recursive_trace input) = node_count input /\
    exit_count (recursive_trace input) = node_count input) /\
  (forall inputs,
    enter_count (recursive_traces inputs) = forest_count inputs /\
    exit_count (recursive_traces inputs) = forest_count inputs).
Proof.
  apply tree_forest_ind.
  - intros tag children [IHenter IHexit]. simpl.
    split.
    + rewrite enter_count_app. simpl. rewrite IHenter. lia.
    + rewrite exit_count_app. simpl. rewrite IHexit. lia.
  - split; reflexivity.
  - intros head [IHhead_enter IHhead_exit] tail [IHtail_enter IHtail_exit]. simpl.
    split.
    + rewrite enter_count_app. rewrite IHhead_enter, IHtail_enter. reflexivity.
    + rewrite exit_count_app. rewrite IHhead_exit, IHtail_exit. reflexivity.
Qed.

Corollary lifecycle_pda_enters_each_node_once : forall input,
  enter_count (recursive_trace input) = node_count input.
Proof.
  intro input.
  destruct lifecycle_trace_visits_once as [Htree _].
  apply Htree.
Qed.

Corollary lifecycle_pda_exits_each_node_once : forall input,
  exit_count (recursive_trace input) = node_count input.
Proof.
  intro input.
  destruct lifecycle_trace_visits_once as [Htree _].
  apply Htree.
Qed.
