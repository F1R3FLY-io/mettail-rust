(*
 * CartesianSuccessorReachability supplies the coordinate reachability law
 * needed by lazy container products.  The source coordinate is zero-based;
 * family bounds are exact exhausted-family sizes, not temporary cache lengths.
 * A successor increments exactly one occurrence.  No eager materialization of
 * the Cartesian product is needed by the operational traversal.
 *
 * The saturation theorem identifies the required completion invariant: every
 * successor of a processed coordinate has been processed or remains pending.
 * A temporarily unavailable child index must retain an obligation; treating
 * it as an exhausted bound does not satisfy this theorem's premises.
 *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Definition within_bounds (bounds coordinate : list nat) : Prop :=
  Forall2 (fun bound index => index < bound) bounds coordinate.

Definition origin (bounds : list nat) : list nat := map (fun _ => 0) bounds.

Inductive coordinate_step : list nat -> list nat -> list nat -> Prop :=
| IncrementFirst : forall bound bounds index tail,
    S index < bound -> within_bounds bounds tail ->
    coordinate_step (bound :: bounds) (index :: tail) (S index :: tail)
| IncrementLater : forall bound bounds index tail next,
    index < bound -> coordinate_step bounds tail next ->
    coordinate_step (bound :: bounds) (index :: tail) (index :: next).

Inductive coordinate_walk (bounds : list nat) : list nat -> list nat -> Prop :=
| WalkDone : forall coordinate,
    within_bounds bounds coordinate -> coordinate_walk bounds coordinate coordinate
| WalkNext : forall first middle last,
    coordinate_step bounds first middle ->
    coordinate_walk bounds middle last -> coordinate_walk bounds first last.

Lemma step_preserves_exact_bounds : forall bounds first next,
  coordinate_step bounds first next ->
  within_bounds bounds first /\ within_bounds bounds next.
Proof.
  intros bounds first next Hstep. induction Hstep.
  - split; constructor; auto; lia.
  - destruct IHHstep as [Hfirst Hnext]. split; constructor; assumption.
Qed.

Lemma walk_composes : forall bounds first middle last,
  coordinate_walk bounds first middle ->
  coordinate_walk bounds middle last -> coordinate_walk bounds first last.
Proof.
  intros bounds first middle last Hwalk. induction Hwalk; intro Htail.
  - exact Htail.
  - eapply WalkNext; [exact H | now apply IHHwalk].
Qed.

Lemma valid_coordinate_has_valid_origin : forall bounds coordinate,
  within_bounds bounds coordinate -> within_bounds bounds (origin bounds).
Proof.
  intros bounds coordinate Hvalid. induction Hvalid; cbn [origin].
  - constructor.
  - constructor; auto; lia.
Qed.

Lemma increment_head_to_target : forall target bound bounds tail,
  target < bound -> within_bounds bounds tail ->
  coordinate_walk (bound :: bounds) (0 :: tail) (target :: tail).
Proof.
  induction target as [|target IH]; intros bound bounds tail Hbound Htail.
  - apply WalkDone. constructor; assumption.
  - eapply walk_composes with (middle := target :: tail).
    + apply IH; [lia | exact Htail].
    + eapply WalkNext.
      * apply IncrementFirst; assumption.
      * apply WalkDone. constructor; assumption.
Qed.

Lemma walk_under_fixed_head : forall bounds first last,
  coordinate_walk bounds first last ->
  forall bound index, index < bound ->
    coordinate_walk (bound :: bounds) (index :: first) (index :: last).
Proof.
  intros bounds first last Hwalk. induction Hwalk; intros bound index Hbound.
  - apply WalkDone. constructor; assumption.
  - eapply WalkNext.
    + apply IncrementLater; [exact Hbound | exact H].
    + now apply IHHwalk.
Qed.

Theorem every_valid_coordinate_is_reachable : forall bounds coordinate,
  within_bounds bounds coordinate ->
  coordinate_walk bounds (origin bounds) coordinate.
Proof.
  intros bounds coordinate Hvalid. induction Hvalid; cbn [origin].
  - apply WalkDone. constructor.
  - eapply walk_composes with (middle := y :: origin l).
    + apply increment_head_to_target; [exact H |].
      now apply valid_coordinate_has_valid_origin with (coordinate := l').
    + apply walk_under_fixed_head; assumption.
Qed.

Theorem each_successor_makes_strict_progress : forall bounds first next,
  coordinate_step bounds first next ->
  fold_right Nat.add 0 next = S (fold_right Nat.add 0 first).
Proof.
  intros bounds first next Hstep. induction Hstep; cbn; lia.
Qed.

(* [seen] is the set of coordinates whose successor obligations have been
   resolved.  Merely returning a value for a coordinate does not put it here. *)
Definition saturated (bounds : list nat) (seen : list (list nat)) : Prop :=
  forall point next,
    In point seen -> coordinate_step bounds point next -> In next seen.

Lemma saturated_set_contains_walk : forall bounds first last,
  coordinate_walk bounds first last -> forall seen,
    saturated bounds seen -> In first seen -> In last seen.
Proof.
  intros bounds first last Hwalk. induction Hwalk; intros seen Hclosed Hin.
  - exact Hin.
  - apply IHHwalk; [exact Hclosed |].
    eapply Hclosed; eauto.
Qed.

Theorem exhausted_successor_obligations_cover_the_product : forall bounds seen,
  In (origin bounds) seen -> saturated bounds seen ->
  forall coordinate, within_bounds bounds coordinate -> In coordinate seen.
Proof.
  intros bounds seen Horigin Hclosed coordinate Hvalid.
  exact (@saturated_set_contains_walk bounds (origin bounds) coordinate
    (@every_valid_coordinate_is_reachable bounds coordinate Hvalid)
    seen Hclosed Horigin).
Qed.

Example independently_shared_occurrences_are_reachable :
  coordinate_walk [2; 2] [0; 0] [0; 1] /\
  coordinate_walk [2; 2] [0; 0] [1; 0].
Proof.
  split.
  - change (coordinate_walk [2; 2] (origin [2; 2]) [0; 1]).
    apply every_valid_coordinate_is_reachable; repeat constructor; lia.
  - change (coordinate_walk [2; 2] (origin [2; 2]) [1; 0]).
    apply every_valid_coordinate_is_reachable; repeat constructor; lia.
Qed.

Print Assumptions step_preserves_exact_bounds.
Print Assumptions every_valid_coordinate_is_reachable.
Print Assumptions each_successor_makes_strict_progress.
Print Assumptions exhausted_successor_obligations_cover_the_product.
