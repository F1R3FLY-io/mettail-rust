(*
 * DeltaOneMinCostJoin: the Δ1 min-cost join contract.
 *
 * Δ1 chooses join matches by first removing refuted candidates, then selecting
 * every remaining candidate with minimal ordering cost.  The ordering axis can
 * rank enabled matches, but it must not remove equal-cost alternatives.
 *
 * Proven here:
 *   - every Δ1-selected candidate is an actual enabled candidate;
 *   - every Δ1-selected candidate is enabled;
 *   - every Δ1-selected candidate has minimal enabled cost;
 *   - every present enabled minimal candidate is selected by the relational
 *     contract;
 *   - a strictly more expensive enabled candidate cannot be selected while a
 *     cheaper enabled candidate exists.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section DeltaOneMinCostJoin.

  Record Candidate : Type := {
    candidate_id : nat;
    candidate_cost : nat;
    candidate_refuted : bool
  }.

  Definition enabled (c : Candidate) : Prop :=
    candidate_refuted c = false.

  Definition min_enabled_cost_value (candidates : list Candidate) (m : nat) : Prop :=
    (exists c, In c candidates /\ enabled c /\ candidate_cost c = m)
    /\ forall c, In c candidates -> enabled c -> m <= candidate_cost c.

  Definition delta1_select (candidates : list Candidate) (c : Candidate) : Prop :=
    In c candidates
    /\ enabled c
    /\ exists m, min_enabled_cost_value candidates m /\ candidate_cost c = m.

  Theorem delta1_selected_member : forall candidates c,
    delta1_select candidates c -> In c candidates.
  Proof.
    intros candidates c H. exact (proj1 H).
  Qed.

  Theorem delta1_selected_enabled : forall candidates c,
    delta1_select candidates c -> enabled c.
  Proof.
    intros candidates c [_ [Henabled _]]. exact Henabled.
  Qed.

  Theorem delta1_selected_minimal : forall candidates c d,
    delta1_select candidates c ->
    In d candidates ->
    enabled d ->
    candidate_cost c <= candidate_cost d.
  Proof.
    intros candidates c d [_ [_ [m [[_ Hmin] Hcost]]]] Hd Hdenabled.
    subst m. apply Hmin; assumption.
  Qed.

  Theorem delta1_complete_for_enabled_minimal : forall candidates c,
    In c candidates ->
    enabled c ->
    (forall d, In d candidates -> enabled d -> candidate_cost c <= candidate_cost d) ->
    delta1_select candidates c.
  Proof.
    intros candidates c Hin Henabled Hmin. split.
    - exact Hin.
    - split.
      + exact Henabled.
      + exists (candidate_cost c). split.
        * split.
          -- exists c. repeat split; try assumption; reflexivity.
          -- exact Hmin.
        * reflexivity.
  Qed.

  Theorem delta1_excludes_strictly_more_expensive : forall candidates cheaper chosen,
    In cheaper candidates ->
    enabled cheaper ->
    delta1_select candidates chosen ->
    candidate_cost cheaper < candidate_cost chosen ->
    False.
  Proof.
    intros candidates cheaper chosen Hcheaper Hcheaper_enabled Hchosen Hlt.
    pose proof (delta1_selected_minimal candidates chosen cheaper Hchosen Hcheaper Hcheaper_enabled) as Hle.
    lia.
  Qed.

  Theorem delta1_refuted_absent : forall candidates c,
    In c candidates ->
    candidate_refuted c = true ->
    ~ delta1_select candidates c.
  Proof.
    intros candidates c _ Hrefuted Hselect.
    pose proof (delta1_selected_enabled candidates c Hselect) as Henabled.
    unfold enabled in Henabled. rewrite Hrefuted in Henabled. discriminate.
  Qed.

End DeltaOneMinCostJoin.
