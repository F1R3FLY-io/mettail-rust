(*
 * LazyRelationalAcEdges: D-E4 relational-edge reuse for native AC matching.
 *
 * MaximumBipartiteMatch observes a pure edge predicate after matcher-state
 * isolation. A cacheable row retains the successful edges in an evaluated
 * target prefix and later evaluates only the suffix. This file proves that
 * joining the cached prefix relation with the suffix delta is exactly a full
 * rescan, that no target pair is evaluated twice when the two regions form a
 * NoDup partition, and that replacing the nominal relation by the incremental
 * relation preserves every valid injective multiset assignment.
 *
 * Rocq 9.1 compatible. No Admitted, Axiom, or Assumption.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Arith.Wf_nat.

Import ListNotations.

Section LazyRelationalAcEdges.

  Variable edge : nat -> nat -> bool.

  Definition row (pattern : nat) (targets : list nat) : list nat :=
    filter (edge pattern) targets.

  Definition incremental_row
      (pattern : nat) (cached_prefix delta_suffix : list nat) : list nat :=
    row pattern cached_prefix ++ row pattern delta_suffix.

  Theorem incremental_row_equals_full_scan : forall pattern cached_prefix delta_suffix,
    incremental_row pattern cached_prefix delta_suffix =
    row pattern (cached_prefix ++ delta_suffix).
  Proof.
    intros pattern cached_prefix delta_suffix.
    unfold incremental_row, row.
    symmetry.
    apply filter_app.
  Qed.

  Corollary incremental_membership_iff_full_scan : forall pattern prefix suffix target,
    In target (incremental_row pattern prefix suffix) <->
    In target (row pattern (prefix ++ suffix)).
  Proof.
    intros pattern prefix suffix target.
    rewrite incremental_row_equals_full_scan.
    reflexivity.
  Qed.

  Theorem row_contains_exactly_successful_targets : forall pattern targets target,
    In target (row pattern targets) <->
    In target targets /\ edge pattern target = true.
  Proof.
    intros pattern targets target.
    unfold row.
    apply filter_In.
  Qed.

  (* A target belongs to at most one side of a NoDup prefix/suffix partition.
     Thus the incremental scan never evaluates one pattern-target pair twice. *)
  Theorem prefix_delta_disjoint : forall (prefix suffix : list nat) (target : nat),
    NoDup (prefix ++ suffix) ->
    In target prefix ->
    ~ In target suffix.
  Proof.
    induction prefix as [| head tail IH];
      intros suffix target Hnodup Hin_prefix Hin_suffix.
    - contradiction.
    - simpl in Hnodup.
      inversion Hnodup as [| ? ? Hnotin Htail]; subst.
      simpl in Hin_prefix.
      destruct Hin_prefix as [Heq | Hin_tail].
      + subst target.
        apply Hnotin.
        apply in_or_app.
        right.
        exact Hin_suffix.
      + exact (IH suffix target Htail Hin_tail Hin_suffix).
  Qed.

  Record Assignment := {
    assignment_pattern : nat;
    assignment_target : nat;
  }.

  Definition assignment_valid
      (relation : nat -> list nat) (assignments : list Assignment) : Prop :=
    NoDup (map assignment_pattern assignments) /\
    NoDup (map assignment_target assignments) /\
    Forall
      (fun assignment =>
         In (assignment_target assignment)
            (relation (assignment_pattern assignment)))
      assignments.

  Definition nominal_relation (targets : list nat) : nat -> list nat :=
    fun pattern => row pattern targets.

  Definition incremental_relation
      (prefix suffix : list nat) : nat -> list nat :=
    fun pattern => incremental_row pattern prefix suffix.

  Theorem incremental_assignment_iff_nominal : forall prefix suffix assignments,
    assignment_valid (incremental_relation prefix suffix) assignments <->
    assignment_valid (nominal_relation (prefix ++ suffix)) assignments.
  Proof.
    intros prefix suffix assignments.
    unfold assignment_valid, incremental_relation, nominal_relation.
    split.
    - intros [Hpatterns [Htargets Hedges]].
      repeat split; try assumption.
      clear Hpatterns Htargets.
      induction Hedges as [| assignment remaining Hedge Hremaining IH].
      + constructor.
      + constructor.
        * rewrite <- incremental_row_equals_full_scan.
          exact Hedge.
        * exact IH.
    - intros [Hpatterns [Htargets Hedges]].
      repeat split; try assumption.
      clear Hpatterns Htargets.
      induction Hedges as [| assignment remaining Hedge Hremaining IH].
      + constructor.
      + constructor.
        * rewrite incremental_row_equals_full_scan.
          exact Hedge.
        * exact IH.
  Qed.

  (* The worklist measure used by the Rust row frontier is the unseen suffix
     length. Every evaluation removes its head, so recursive presentations of
     the same loop are well-founded; Rust executes it as a while-loop PDA. *)
  Theorem suffix_length_strictly_decreases : forall (head : nat) (suffix : list nat),
    length suffix < length (head :: suffix).
  Proof.
    intros head suffix.
    simpl.
    apply Nat.lt_succ_diag_r.
  Qed.

  Theorem suffix_length_order_well_founded :
    well_founded (fun left right : list nat => length left < length right).
  Proof.
    exact (well_founded_ltof (list nat) (@length nat)).
  Qed.

End LazyRelationalAcEdges.

Print Assumptions incremental_row_equals_full_scan.
Print Assumptions incremental_membership_iff_full_scan.
Print Assumptions prefix_delta_disjoint.
Print Assumptions incremental_assignment_iff_nominal.
Print Assumptions suffix_length_order_well_founded.
