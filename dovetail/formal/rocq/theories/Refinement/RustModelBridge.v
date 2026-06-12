(*
 * RustModelBridge: bridge obligations between Rust-facing Dovetail concepts and
 * the existing Rocq models.
 *
 * This is not a whole-Rust verifier. It records the concrete correspondence
 * points that the Rust tests/traces exercise: budget results, candidates,
 * rank-vectors, and cycle-cut reports. The theorems compose existing Dovetail
 * model capstones so future trace checkers have stable targets.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

From Dovetail.ExactKeys Require Import ExactKeyDedup.
From Dovetail.Extraction Require Import NBestExtraction.
From Dovetail.Extraction Require Import EnumerationCompleteness.
From Dovetail.Extraction Require Import CycleCutBoundary.
From Dovetail.Saturation Require Import DovetailSaturation.

Import ListNotations.

Section RustModelBridge.

  Record RustCandidate : Type := {
    rust_weight : option nat;
    rust_key : nat
  }.

  Definition to_cand (c : RustCandidate) : Cand :=
    (rust_weight c, rust_key c).

  Definition rust_is_zero (c : RustCandidate) : bool :=
    is_zero (to_cand c).

  Theorem rust_candidate_selection_no_miss : forall c cs,
    In c cs ->
    rust_is_zero c = false ->
    In (to_cand c) (select (map to_cand cs)).
  Proof.
    intros c cs Hin Hnz.
    apply select_complete.
    - apply in_map. exact Hin.
    - exact Hnz.
  Qed.

  Theorem rust_candidate_selection_only_zero_removed : forall c cs,
    In (to_cand c) (select (map to_cand cs)) ->
    rust_is_zero c = false.
  Proof.
    intros c cs Hin. exact (select_only_removes_zero (to_cand c) (map to_cand cs) Hin).
  Qed.

  Inductive RustAddResult : Type :=
    | RustAdded : nat -> RustAddResult
    | RustOverflow : nat -> RustAddResult.

  Definition to_add_result (r : RustAddResult) : AddResult :=
    match r with
    | RustAdded n => Added n
    | RustOverflow n => Overflow n
    end.

  Definition rust_try_add_with_budget (budget used : nat) : RustAddResult :=
    match try_add_with_budget budget used with
    | Added n => RustAdded n
    | Overflow n => RustOverflow n
    end.

  Theorem rust_budget_added_never_overshoots : forall budget used used',
    used <= budget ->
    rust_try_add_with_budget budget used = RustAdded used' ->
    used' <= budget.
  Proof.
    intros budget used used' Hle Hadd.
    unfold rust_try_add_with_budget in Hadd.
    destruct (try_add_with_budget budget used) eqn:Htry; inversion Hadd; subst.
    eapply added_never_overshoots_budget; eauto.
  Qed.

  Theorem rust_budget_overflow_preserves_state : forall budget used used',
    rust_try_add_with_budget budget used = RustOverflow used' ->
    used' = used /\ budget <= used.
  Proof.
    intros budget used used' Hover.
    unfold rust_try_add_with_budget in Hover.
    destruct (try_add_with_budget budget used) eqn:Htry; inversion Hover; subst.
    apply overflow_preserves_state in Htry. exact Htry.
  Qed.

  Inductive RustSaturationOutcome : Type :=
    | RustConverged
    | RustNodeLimit
    | RustIterationLimit.

  Record RustSatStats : Type := {
    rust_sat_iterations : nat;
    rust_sat_total_merges : nat
  }.

  Record RustSatReport : Type := {
    rust_sat_outcome : RustSaturationOutcome;
    rust_sat_stats : RustSatStats
  }.

  Definition to_sat_outcome (o : RustSaturationOutcome) : SaturationOutcome :=
    match o with
    | RustConverged => Converged
    | RustNodeLimit => NodeLimit
    | RustIterationLimit => IterationLimit
    end.

  Definition to_sat_stats (s : RustSatStats) : SatStats :=
    {|
      sat_iterations := rust_sat_iterations s;
      sat_total_merges := rust_sat_total_merges s
    |}.

  Definition to_sat_report (r : RustSatReport) (st : State) : SatReport :=
    {|
      sat_outcome := to_sat_outcome (rust_sat_outcome r);
      sat_stats := to_sat_stats (rust_sat_stats r);
      sat_state := st
    |}.

  Theorem rust_sat_report_outcome_roundtrip : forall r st,
    sat_outcome (to_sat_report r st) = to_sat_outcome (rust_sat_outcome r).
  Proof. intros r st. reflexivity. Qed.

  Theorem rust_node_limit_never_claims_converged : forall stats st,
    sat_outcome
      (to_sat_report {| rust_sat_outcome := RustNodeLimit; rust_sat_stats := stats |} st)
      <> Converged.
  Proof. intros stats st H. discriminate. Qed.

  Theorem rust_iteration_limit_never_claims_converged : forall stats st,
    sat_outcome
      (to_sat_report {| rust_sat_outcome := RustIterationLimit; rust_sat_stats := stats |} st)
      <> Converged.
  Proof. intros stats st H. discriminate. Qed.

  Record RustCycleReport : Type := {
    rust_is_cyclic : bool;
    rust_had_cycle_cut : bool;
    rust_outputs : list nat
  }.

  Definition to_extract_report (r : RustCycleReport) : ExtractReport :=
    {|
      report_shape := if rust_is_cyclic r then Cyclic else Acyclic;
      report_outputs := rust_outputs r;
      had_cycle_cut := rust_had_cycle_cut r
    |}.

  Definition rust_cycle_guarded (r : RustCycleReport) : Prop :=
    rust_is_cyclic r = true -> rust_had_cycle_cut r = true.

  Theorem rust_cycle_cut_never_claims_complete : forall r,
    rust_cycle_guarded r ->
    rust_is_cyclic r = true ->
    status_of (to_extract_report r) <> Complete.
  Proof.
    intros r Hguard Hcyc.
    apply no_silent_cyclic_complete_claim.
    - unfold cycle_guarded, to_extract_report. simpl.
      intros Hshape.
      destruct (rust_is_cyclic r) eqn:Hc; simpl in Hshape.
      + apply Hguard. exact Hc.
      + discriminate.
    - unfold to_extract_report. simpl. rewrite Hcyc. reflexivity.
  Qed.

  Theorem rust_cycle_cut_maps_to_bounded : forall r,
    rust_had_cycle_cut r = true ->
    @extraction_completeness (list nat) (to_extraction (to_extract_report r)) =
      BoundedByCycleCut.
  Proof.
    intros r Hcut. simpl. unfold status_of. simpl. rewrite Hcut. reflexivity.
  Qed.

  Theorem rust_rank_vector_complete : forall bounds v,
    in_bounds bounds v ->
    In v (enum_vectors bounds).
  Proof.
    intros bounds v H. apply enum_vectors_complete. exact H.
  Qed.

  Theorem rust_class_derivation_complete : forall c edge bounds ranks,
    nth_error c edge = Some bounds ->
    in_bounds bounds ranks ->
    In (edge, ranks) (class_enum c).
  Proof.
    intros c edge bounds ranks Hnth Hin.
    eapply class_enum_complete; eauto.
  Qed.

End RustModelBridge.
