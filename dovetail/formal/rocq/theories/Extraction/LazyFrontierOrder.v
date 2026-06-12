(*
 * LazyFrontierOrder: proof obligations for Dovetail's lazy heap frontier.
 *
 * This file models the part not covered by "sort a precomputed list": the
 * extractor pops a current best candidate from a heap and pushes successors
 * formed by bumping one child-rank coordinate. Under MonotoneBestOrder, bumping
 * a coordinate cannot make a candidate strictly better. Therefore a trace whose
 * heap pop is minimal and whose successors satisfy that monotonicity emits a
 * sorted best-first stream.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.

Import ListNotations.

Section LazyFrontierOrder.

  Definition Cand : Type := (nat * nat)%type.

  Definition cleb (a b : Cand) : bool :=
    let (w1, k1) := a in
    let (w2, k2) := b in
    (w1 <? w2) || ((w1 =? w2) && (k1 <=? k2)).

  Lemma cleb_refl : forall a, cleb a a = true.
  Proof.
    intros [w k]. unfold cleb.
    apply orb_true_iff. right. apply andb_true_iff. split.
    - apply Nat.eqb_eq. reflexivity.
    - apply Nat.leb_le. lia.
  Qed.

  Lemma cleb_trans : forall a b c,
    cleb a b = true -> cleb b c = true -> cleb a c = true.
  Proof.
    intros [w1 k1] [w2 k2] [w3 k3]. unfold cleb.
    intros Hab Hbc.
    apply orb_true_iff in Hab. apply orb_true_iff in Hbc. apply orb_true_iff.
    destruct Hab as [Hab | Hab].
    - apply Nat.ltb_lt in Hab.
      destruct Hbc as [Hbc | Hbc].
      + apply Nat.ltb_lt in Hbc. left. apply Nat.ltb_lt. lia.
      + apply andb_true_iff in Hbc. destruct Hbc as [Hbc _].
        apply Nat.eqb_eq in Hbc. left. apply Nat.ltb_lt. lia.
    - apply andb_true_iff in Hab. destruct Hab as [Hab1 Hab2].
      apply Nat.eqb_eq in Hab1. apply Nat.leb_le in Hab2.
      destruct Hbc as [Hbc | Hbc].
      + apply Nat.ltb_lt in Hbc. left. apply Nat.ltb_lt. lia.
      + apply andb_true_iff in Hbc. destruct Hbc as [Hbc1 Hbc2].
        apply Nat.eqb_eq in Hbc1. apply Nat.leb_le in Hbc2.
        right. apply andb_true_iff. split.
        * apply Nat.eqb_eq. lia.
        * apply Nat.leb_le. lia.
  Qed.

  Definition all_ge (pivot : Cand) (xs : list Cand) : Prop :=
    forall x, In x xs -> cleb pivot x = true.

  Fixpoint sorted (xs : list Cand) : Prop :=
    match xs with
    | [] => True
    | x :: rest => all_ge x rest /\ sorted rest
    end.

  Record FrontierStep : Type := {
    popped : Cand;
    fresh_successors : list Cand;
    remaining_after_pop : list Cand
  }.

  Definition step_ok (prev : option Cand) (s : FrontierStep) : Prop :=
    (match prev with
     | None => True
     | Some p => cleb p (popped s) = true
     end) /\
    all_ge (popped s) (fresh_successors s) /\
    all_ge (popped s) (remaining_after_pop s).

  Fixpoint trace_ok (prev : option Cand) (steps : list FrontierStep) : Prop :=
    match steps with
    | [] => True
    | s :: rest => step_ok prev s /\ trace_ok (Some (popped s)) rest
    end.

  Fixpoint emitted (steps : list FrontierStep) : list Cand :=
    match steps with
    | [] => []
    | s :: rest => popped s :: emitted rest
    end.

  Lemma trace_all_ge_prev : forall p steps x,
    trace_ok (Some p) steps ->
    In x (emitted steps) ->
    cleb p x = true.
  Proof.
    intros p steps.
    revert p.
    induction steps as [| s rest IH]; intros p x Hok Hin; simpl in Hin.
    - contradiction.
    - simpl in Hok. destruct Hok as [Hs Hrest].
      unfold step_ok in Hs. destruct Hs as [Hprev _].
      destruct Hin as [Hx | Hin].
      + subst x. exact Hprev.
      + eapply cleb_trans.
        * exact Hprev.
        * apply (IH (popped s)); assumption.
  Qed.

  Lemma trace_sorted_from_prev : forall prev steps,
    trace_ok prev steps ->
    sorted (emitted steps).
  Proof.
    intros prev steps.
    revert prev.
    induction steps as [| s rest IH]; intros prev Hok; simpl.
    - exact I.
    - simpl in Hok. destruct Hok as [Hs Hrest].
      split.
      + intros x Hin. eapply trace_all_ge_prev; eauto.
      + apply (IH (Some (popped s))). exact Hrest.
  Qed.

  Theorem lazy_frontier_trace_sorted : forall steps,
    trace_ok None steps ->
    sorted (emitted steps).
  Proof.
    intros steps Hok.
    apply (trace_sorted_from_prev None). exact Hok.
  Qed.

  Definition next_frontier (s : FrontierStep) : list Cand :=
    remaining_after_pop s ++ fresh_successors s.

  Fixpoint generated_successors (steps : list FrontierStep) : list Cand :=
    match steps with
    | [] => []
    | s :: rest => fresh_successors s ++ generated_successors rest
    end.

  Definition heap_step_ok (frontier : list Cand) (s : FrontierStep) : Prop :=
    Permutation frontier (popped s :: remaining_after_pop s) /\
    all_ge (popped s) (remaining_after_pop s) /\
    all_ge (popped s) (fresh_successors s).

  Fixpoint heap_trace_ok
      (frontier : list Cand)
      (steps : list FrontierStep)
      (final_frontier : list Cand) : Prop :=
    match steps with
    | [] => frontier = final_frontier
    | s :: rest =>
        heap_step_ok frontier s /\
        heap_trace_ok (next_frontier s) rest final_frontier
    end.

  Lemma all_ge_app_intro : forall pivot xs ys,
    all_ge pivot xs ->
    all_ge pivot ys ->
    all_ge pivot (xs ++ ys).
  Proof.
    intros pivot xs ys Hxs Hys x Hin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - apply Hxs. exact Hin.
    - apply Hys. exact Hin.
  Qed.

  Lemma all_ge_perm : forall pivot xs ys,
    Permutation xs ys ->
    all_ge pivot xs ->
    all_ge pivot ys.
  Proof.
    intros pivot xs ys Hperm Hall x Hin.
    apply Hall.
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hin.
  Qed.

  Lemma heap_step_popped_ge_from_frontier : forall pivot frontier s,
    all_ge pivot frontier ->
    heap_step_ok frontier s ->
    cleb pivot (popped s) = true.
  Proof.
    intros pivot frontier s Hfront Hstep.
    unfold heap_step_ok in Hstep. destruct Hstep as [Hperm _].
    apply Hfront.
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - simpl. left. reflexivity.
  Qed.

  Lemma heap_step_next_ge : forall s,
    heap_step_ok (popped s :: remaining_after_pop s) s ->
    all_ge (popped s) (next_frontier s).
  Proof.
    intros s Hstep.
    unfold heap_step_ok in Hstep. destruct Hstep as [_ [Hrem Hfresh]].
    unfold next_frontier.
    apply all_ge_app_intro; assumption.
  Qed.

  Lemma heap_step_next_ge_general : forall frontier s,
    heap_step_ok frontier s ->
    all_ge (popped s) (next_frontier s).
  Proof.
    intros frontier s Hstep.
    unfold heap_step_ok in Hstep. destruct Hstep as [_ [Hrem Hfresh]].
    unfold next_frontier.
    apply all_ge_app_intro; assumption.
  Qed.

  Lemma heap_trace_emitted_ge : forall pivot frontier steps final_frontier,
    all_ge pivot frontier ->
    heap_trace_ok frontier steps final_frontier ->
    all_ge pivot (emitted steps).
  Proof.
    intros pivot frontier steps.
    revert pivot frontier.
    induction steps as [| s rest IH]; intros pivot frontier final_frontier Hfront Htrace x Hin;
      simpl in Hin.
    - contradiction.
    - simpl in Htrace. destruct Htrace as [Hstep Hrest].
      destruct Hin as [Hx | Hin].
      + subst x. eapply heap_step_popped_ge_from_frontier; eauto.
      + apply (IH pivot (next_frontier s) final_frontier).
        * unfold next_frontier.
          unfold heap_step_ok in Hstep. destruct Hstep as [Hperm [Hrem Hfresh]].
          apply all_ge_app_intro.
          -- intros y Hy. apply Hfront.
             eapply Permutation_in.
             ++ apply Permutation_sym. exact Hperm.
             ++ simpl. right. exact Hy.
          -- intros y Hy.
             eapply cleb_trans.
             ++ apply Hfront.
                eapply Permutation_in.
                ** apply Permutation_sym. exact Hperm.
                ** simpl. left. reflexivity.
             ++ apply Hfresh. exact Hy.
        * exact Hrest.
        * exact Hin.
  Qed.

  Theorem lazy_frontier_heap_trace_sorted : forall frontier steps final_frontier,
    heap_trace_ok frontier steps final_frontier ->
    sorted (emitted steps).
  Proof.
    intros frontier steps.
    revert frontier.
    induction steps as [| s rest IH]; intros frontier final_frontier Htrace; simpl.
    - exact I.
    - simpl in Htrace. destruct Htrace as [Hstep Hrest].
      split.
      + intros x Hin.
        eapply (heap_trace_emitted_ge (popped s) (next_frontier s) rest final_frontier).
        * apply (heap_step_next_ge_general frontier s). exact Hstep.
        * exact Hrest.
        * exact Hin.
      + apply (IH (next_frontier s) final_frontier). exact Hrest.
  Qed.

  Theorem lazy_frontier_heap_trace_permutation : forall frontier steps final_frontier,
    heap_trace_ok frontier steps final_frontier ->
    Permutation (frontier ++ generated_successors steps)
      (emitted steps ++ final_frontier).
  Proof.
    intros frontier steps.
    revert frontier.
    induction steps as [| s rest IH]; intros frontier final_frontier Htrace; simpl.
    - simpl in Htrace. subst final_frontier. rewrite app_nil_r. apply Permutation_refl.
    - simpl in Htrace. destruct Htrace as [Hstep Hrest].
      unfold heap_step_ok in Hstep. destruct Hstep as [Hperm _].
      eapply Permutation_trans.
      + apply Permutation_app.
        * exact Hperm.
        * apply Permutation_refl.
      + simpl. apply perm_skip.
        unfold next_frontier in IH.
        rewrite app_assoc.
        apply (IH (remaining_after_pop s ++ fresh_successors s) final_frontier).
        exact Hrest.
  Qed.

  Fixpoint pointwise_le (xs ys : list nat) : Prop :=
    match xs, ys with
    | [], [] => True
    | x :: xs', y :: ys' => x <= y /\ pointwise_le xs' ys'
    | _, _ => False
    end.

  Lemma pointwise_le_refl : forall xs,
    pointwise_le xs xs.
  Proof.
    induction xs as [| x xs IH]; simpl.
    - exact I.
    - split.
      + lia.
      + exact IH.
  Qed.

  Inductive bump_one : list nat -> list nat -> Prop :=
    | BumpHead : forall r tail,
        bump_one (r :: tail) (S r :: tail)
    | BumpTail : forall x xs ys,
        bump_one xs ys ->
        bump_one (x :: xs) (x :: ys).

  Lemma bump_one_pointwise : forall xs ys,
    bump_one xs ys -> pointwise_le xs ys.
  Proof.
    intros xs ys H. induction H; simpl.
    - split.
      + lia.
      + apply pointwise_le_refl.
    - split.
      + lia.
      + exact IHbump_one.
  Qed.

  Definition monotone_weight (weight : list nat -> nat) : Prop :=
    forall xs ys, pointwise_le xs ys -> weight xs <= weight ys.

  Definition rank_cand (weight : list nat -> nat) (ranks : list nat) : Cand :=
    (weight ranks, 0).

  Lemma cleb_of_weight_le : forall w1 w2,
    w1 <= w2 -> cleb (w1, 0) (w2, 0) = true.
  Proof.
    intros w1 w2 Hle. unfold cleb.
    destruct (w1 <? w2) eqn:Hltb.
    - apply orb_true_iff. left. reflexivity.
    - assert (Heq : w1 = w2).
      { apply Nat.ltb_ge in Hltb. lia. }
      subst. rewrite Nat.eqb_refl, Nat.leb_refl. reflexivity.
  Qed.

  Theorem bumped_successor_not_better : forall weight ranks successor,
    monotone_weight weight ->
    bump_one ranks successor ->
    cleb (rank_cand weight ranks) (rank_cand weight successor) = true.
  Proof.
    intros weight ranks successor Hmono Hbump.
    unfold rank_cand.
    apply cleb_of_weight_le.
    apply Hmono.
    apply bump_one_pointwise. exact Hbump.
  Qed.

End LazyFrontierOrder.
