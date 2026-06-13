(*
 * DeltaOneMinCostMatching: the Δ1 bipartite min-cost matching contract.
 *
 * Δ1 matching chooses assignments for a finite join frontier.  The left side is
 * the set of required join obligations, and the right side is the finite set of
 * admitted message/witness slots considered by the frontier.  A selected
 * matching is left-perfect: it covers every required left obligation while using
 * each right witness at most once.  Extra right witnesses may remain unused, so
 * resting RSpace messages are not accidentally consumed by the model.
 *
 * The contract removes refuted edges before feasibility and cost ordering, then
 * selects every enabled left-perfect matching with minimum total ordering cost.
 * Equal-cost left-perfect matchings remain distinct semantic alternatives.
 *
 * Proven here:
 *   - selected matching edges are actual input edges;
 *   - selected matching edges are enabled and endpoint-valid;
 *   - selected matchings use no duplicate left or right endpoint;
 *   - selected matchings cover every required left endpoint;
 *   - selected matchings are cost-minimal among all enabled left-perfect matchings;
 *   - every present left-perfect matching satisfying the same minimum predicate is
 *     selected by the relational contract;
 *   - equal-cost optimal alternatives are also selected;
 *   - refuted edges cannot appear in a selected matching.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section DeltaOneMinCostMatching.

  Record Edge : Type := {
    edge_id : nat;
    edge_left : nat;
    edge_right : nat;
    edge_cost : nat;
    edge_refuted : bool
  }.

  Definition enabled (e : Edge) : Prop :=
    edge_refuted e = false.

  Definition endpoint_valid (left_count right_count : nat) (e : Edge) : Prop :=
    edge_left e < left_count /\ edge_right e < right_count.

  Definition matching_lefts (matching : list Edge) : list nat :=
    map edge_left matching.

  Definition matching_rights (matching : list Edge) : list nat :=
    map edge_right matching.

  Fixpoint matching_cost (matching : list Edge) : nat :=
    match matching with
    | [] => 0
    | e :: rest => edge_cost e + matching_cost rest
    end.

  Definition covers_lefts (left_count : nat) (matching : list Edge) : Prop :=
    forall left, left < left_count -> In left (matching_lefts matching).

  Definition matching_sound
      (graph : list Edge)
      (left_count right_count : nat)
      (matching : list Edge) : Prop :=
    Forall
      (fun e => In e graph /\ enabled e /\ endpoint_valid left_count right_count e)
      matching
    /\ NoDup (matching_lefts matching)
    /\ NoDup (matching_rights matching).

  Definition left_perfect_matching
      (graph : list Edge)
      (left_count right_count : nat)
      (matching : list Edge) : Prop :=
    matching_sound graph left_count right_count matching
    /\ covers_lefts left_count matching.

  Definition delta1_min_cost_matching
      (graph : list Edge)
      (left_count right_count : nat)
      (matching : list Edge) : Prop :=
    left_perfect_matching graph left_count right_count matching
    /\ forall other,
        left_perfect_matching graph left_count right_count other ->
        matching_cost matching <= matching_cost other.

  Theorem delta1_matching_selected_left_perfect : forall graph left_count right_count matching,
    delta1_min_cost_matching graph left_count right_count matching ->
    left_perfect_matching graph left_count right_count matching.
  Proof.
    intros graph left_count right_count matching Hselected.
    exact (proj1 Hselected).
  Qed.

  Theorem delta1_matching_selected_sound : forall graph left_count right_count matching,
    delta1_min_cost_matching graph left_count right_count matching ->
    matching_sound graph left_count right_count matching.
  Proof.
    intros graph left_count right_count matching Hselected.
    destruct Hselected as [[Hsound _] _].
    exact Hsound.
  Qed.

  Theorem delta1_matching_selected_member : forall graph left_count right_count matching e,
    delta1_min_cost_matching graph left_count right_count matching ->
    In e matching ->
    In e graph.
  Proof.
    intros graph left_count right_count matching e Hselected Hin.
    pose proof (delta1_matching_selected_sound graph left_count right_count matching Hselected)
      as Hsound.
    destruct Hsound as [Hall _].
    apply Forall_forall with (x := e) in Hall.
    - tauto.
    - exact Hin.
  Qed.

  Theorem delta1_matching_selected_enabled : forall graph left_count right_count matching e,
    delta1_min_cost_matching graph left_count right_count matching ->
    In e matching ->
    enabled e.
  Proof.
    intros graph left_count right_count matching e Hselected Hin.
    pose proof (delta1_matching_selected_sound graph left_count right_count matching Hselected)
      as Hsound.
    destruct Hsound as [Hall _].
    apply Forall_forall with (x := e) in Hall.
    - tauto.
    - exact Hin.
  Qed.

  Theorem delta1_matching_selected_endpoint_valid :
    forall graph left_count right_count matching e,
      delta1_min_cost_matching graph left_count right_count matching ->
      In e matching ->
      endpoint_valid left_count right_count e.
  Proof.
    intros graph left_count right_count matching e Hselected Hin.
    pose proof (delta1_matching_selected_sound graph left_count right_count matching Hselected)
      as Hsound.
    destruct Hsound as [Hall _].
    apply Forall_forall with (x := e) in Hall.
    - tauto.
    - exact Hin.
  Qed.

  Theorem delta1_matching_no_duplicate_lefts : forall graph left_count right_count matching,
    delta1_min_cost_matching graph left_count right_count matching ->
    NoDup (matching_lefts matching).
  Proof.
    intros graph left_count right_count matching Hselected.
    pose proof (delta1_matching_selected_sound graph left_count right_count matching Hselected)
      as Hsound.
    destruct Hsound as [_ [Hnodup _]].
    exact Hnodup.
  Qed.

  Theorem delta1_matching_no_duplicate_rights : forall graph left_count right_count matching,
    delta1_min_cost_matching graph left_count right_count matching ->
    NoDup (matching_rights matching).
  Proof.
    intros graph left_count right_count matching Hselected.
    pose proof (delta1_matching_selected_sound graph left_count right_count matching Hselected)
      as Hsound.
    destruct Hsound as [_ [_ Hnodup]].
    exact Hnodup.
  Qed.

  Theorem delta1_matching_covers_lefts : forall graph left_count right_count matching,
    delta1_min_cost_matching graph left_count right_count matching ->
    covers_lefts left_count matching.
  Proof.
    intros graph left_count right_count matching Hselected.
    destruct Hselected as [[_ Hcovers] _].
    exact Hcovers.
  Qed.

  Theorem delta1_matching_selected_minimal_cost : forall graph left_count right_count matching other,
    delta1_min_cost_matching graph left_count right_count matching ->
    left_perfect_matching graph left_count right_count other ->
    matching_cost matching <= matching_cost other.
  Proof.
    intros graph left_count right_count matching other Hselected Hother.
    destruct Hselected as [_ Hminimal].
    apply Hminimal.
    exact Hother.
  Qed.

  Theorem delta1_matching_complete_for_left_perfect_minimal :
    forall graph left_count right_count matching,
      left_perfect_matching graph left_count right_count matching ->
      (forall other,
          left_perfect_matching graph left_count right_count other ->
          matching_cost matching <= matching_cost other) ->
      delta1_min_cost_matching graph left_count right_count matching.
  Proof.
    intros graph left_count right_count matching Hleft_perfect Hminimal.
    split.
    - exact Hleft_perfect.
    - exact Hminimal.
  Qed.

  Theorem delta1_matching_equal_cost_alternative_selected :
    forall graph left_count right_count selected alternative,
      delta1_min_cost_matching graph left_count right_count selected ->
      left_perfect_matching graph left_count right_count alternative ->
      matching_cost alternative = matching_cost selected ->
      delta1_min_cost_matching graph left_count right_count alternative.
  Proof.
    intros graph left_count right_count selected alternative Hselected Halternative Hcost.
    split.
    - exact Halternative.
    - intros other Hother.
      rewrite Hcost.
      apply (delta1_matching_selected_minimal_cost
        graph left_count right_count selected other Hselected Hother).
  Qed.

  Theorem delta1_matching_excludes_strictly_more_expensive :
    forall graph left_count right_count cheaper selected,
      left_perfect_matching graph left_count right_count cheaper ->
      delta1_min_cost_matching graph left_count right_count selected ->
      matching_cost cheaper < matching_cost selected ->
      False.
  Proof.
    intros graph left_count right_count cheaper selected Hcheaper Hselected Hlt.
    pose proof (delta1_matching_selected_minimal_cost
      graph left_count right_count selected cheaper Hselected Hcheaper) as Hle.
    lia.
  Qed.

  Theorem delta1_matching_refuted_edge_absent :
    forall graph left_count right_count matching e,
      delta1_min_cost_matching graph left_count right_count matching ->
      In e matching ->
      edge_refuted e = true ->
      False.
  Proof.
    intros graph left_count right_count matching e Hselected Hin Hrefuted.
    pose proof (delta1_matching_selected_enabled
      graph left_count right_count matching e Hselected Hin) as Henabled.
    unfold enabled in Henabled.
    rewrite Hrefuted in Henabled.
    discriminate.
  Qed.

End DeltaOneMinCostMatching.
