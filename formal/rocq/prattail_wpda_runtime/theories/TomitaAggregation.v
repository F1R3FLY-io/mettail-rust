(*
 * TomitaAggregation: abstract soundness of one engine.step per frontier.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From PrattailWpdaRuntime Require Import RuntimeModel.

Import ListNotations.

Record frontier_key : Type := {
  fk_control : control;
  fk_pos : nat;
  fk_node : nat
}.

Lemma frontier_key_eq_dec :
  forall x y : frontier_key, {x = y} + {x <> y}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply control_eq_dec.
Defined.

Record arc : Type := {
  arc_key : frontier_key;
  arc_payload : nat
}.

Definition insert_frontier_key
  (k : frontier_key) (ks : list frontier_key) : list frontier_key :=
  if in_dec frontier_key_eq_dec k ks then ks else k :: ks.

Fixpoint frontier_keys (arcs : list arc) : list frontier_key :=
  match arcs with
  | [] => []
  | a :: rest => insert_frontier_key (arc_key a) (frontier_keys rest)
  end.

Lemma in_insert_frontier_key :
  forall k x xs,
    In k (insert_frontier_key x xs) <-> k = x \/ In k xs.
Proof.
  intros k x xs.
  unfold insert_frontier_key.
  destruct (in_dec frontier_key_eq_dec x xs) as [Hin | Hnot].
  - split; intro H.
    + right. exact H.
    + destruct H as [H | H].
      * subst. exact Hin.
      * exact H.
  - simpl. split; intro H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
Qed.

Lemma frontier_keys_spec :
  forall arcs k,
    In k (frontier_keys arcs) <->
    exists a, In a arcs /\ arc_key a = k.
Proof.
  induction arcs as [| a rest IH]; intros k.
  - simpl. split; intro H.
    + contradiction.
    + destruct H as [a [Hin _]]. contradiction.
  - simpl. rewrite in_insert_frontier_key. rewrite IH.
    split; intro H.
    + destruct H as [H | [a' [Hin Hkey]]].
      * exists a. split.
        -- left. reflexivity.
        -- symmetry. exact H.
      * exists a'. split.
        -- right. exact Hin.
        -- exact Hkey.
    + destruct H as [a' [[Hhead | Hin] Hkey]].
      * rewrite <- Hhead in Hkey. left. symmetry. exact Hkey.
      * right. exists a'. split; assumption.
Qed.

Lemma insert_frontier_key_length_le_succ :
  forall k ks,
    length (insert_frontier_key k ks) <= S (length ks).
Proof.
  intros k ks.
  unfold insert_frontier_key.
  destruct (in_dec frontier_key_eq_dec k ks); simpl; lia.
Qed.

Lemma frontier_keys_length_le :
  forall arcs,
    length (frontier_keys arcs) <= length arcs.
Proof.
  induction arcs as [| a rest IH].
  - simpl. lia.
  - simpl.
    eapply Nat.le_trans.
    + apply insert_frontier_key_length_le_succ.
    + lia.
Qed.

Section Aggregation.
  Variable action : Type.
  Variable step_frontier : frontier_key -> list action.

  Definition per_arc_observable (arcs : list arc) (act : action) : Prop :=
    exists a, In a arcs /\ In act (step_frontier (arc_key a)).

  Definition aggregate_observable (arcs : list arc) (act : action) : Prop :=
    exists k, In k (frontier_keys arcs) /\ In act (step_frontier k).

  Theorem tomita_aggregation_sound :
    forall arcs act,
      aggregate_observable arcs act <-> per_arc_observable arcs act.
  Proof.
    intros arcs act.
    unfold aggregate_observable, per_arc_observable.
    split; intro H.
    - destruct H as [k [Hk Hact]].
      apply frontier_keys_spec in Hk.
      destruct Hk as [a [Hin Hkey]].
      exists a. split.
      + exact Hin.
      + rewrite Hkey. exact Hact.
    - destruct H as [a [Hin Hact]].
      exists (arc_key a). split.
      + apply frontier_keys_spec.
        exists a. split; reflexivity || exact Hin.
      + exact Hact.
  Qed.
End Aggregation.

Theorem tomita_frontier_count_bounded :
  forall arcs,
    length (frontier_keys arcs) <= length arcs.
Proof.
  apply frontier_keys_length_le.
Qed.
