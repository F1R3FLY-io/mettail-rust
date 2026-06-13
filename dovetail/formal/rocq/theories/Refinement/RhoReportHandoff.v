(*
 * RhoReportHandoff: Dovetail runtime reports may be handed to a Rho adapter
 * only through the checked completeness boundary.
 *
 * Rust image:
 *   - `dovetail::report::DovetailRunReport::assert_complete()` rejects
 *     `BoundedByCycleCut` before a runtime adapter treats roots as exhaustive
 *     observations.
 *   - a Rho adapter may observe the report roots, in extractor order, only after
 *     that completeness check succeeds.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Dovetail.Extraction Require Import CycleCutBoundary.
From Dovetail.Refinement Require Import RuntimeReportBridge.

Import ListNotations.

Section RhoReportHandoff.

  Inductive HandoffStatus : Type :=
    | HandoffReady
    | HandoffRejectedBounded.

  Record RhoHandoff : Type := {
    handoff_status : HandoffStatus;
    handoff_observations : list nat;
    handoff_terms : list nat
  }.

  Definition handoff_is_ready (h : RhoHandoff) : bool :=
    match handoff_status h with
    | HandoffReady => true
    | HandoffRejectedBounded => false
    end.

  Definition handoff_observes_key (h : RhoHandoff) (key : nat) : bool :=
    existsb (Nat.eqb key) (handoff_observations h).

  Definition handoff_from_report (r : RuntimeReport) : RhoHandoff :=
    match runtime_report_completeness r with
    | Complete =>
        {|
          handoff_status := HandoffReady;
          handoff_observations := runtime_report_roots r;
          handoff_terms := runtime_report_terms r
        |}
    | BoundedByCycleCut =>
        {|
          handoff_status := HandoffRejectedBounded;
          handoff_observations := [];
          handoff_terms := runtime_report_terms r
        |}
    end.

  Definition handoff_from_extraction
      (e : Extraction (list Derivation)) : RhoHandoff :=
    handoff_from_report (report_from_extraction e).

  Theorem complete_report_handoff_is_ready : forall r,
    runtime_report_completeness r = Complete ->
    handoff_is_ready (handoff_from_report r) = true.
  Proof.
    intros [roots terms status] Hcomplete. simpl in *.
    rewrite Hcomplete. reflexivity.
  Qed.

  Theorem ready_handoff_originates_complete_report : forall r,
    handoff_is_ready (handoff_from_report r) = true ->
    runtime_report_completeness r = Complete.
  Proof.
    intros [roots terms status] Hready. simpl in *.
    destruct status.
    - reflexivity.
    - discriminate.
  Qed.

  Theorem complete_report_handoff_preserves_roots : forall r,
    runtime_report_completeness r = Complete ->
    handoff_observations (handoff_from_report r) = runtime_report_roots r.
  Proof.
    intros [roots terms status] Hcomplete. simpl in *.
    rewrite Hcomplete. reflexivity.
  Qed.

  Theorem complete_report_handoff_preserves_terms : forall r,
    runtime_report_completeness r = Complete ->
    handoff_terms (handoff_from_report r) = runtime_report_terms r.
  Proof.
    intros [roots terms status] Hcomplete. simpl in *.
    rewrite Hcomplete. reflexivity.
  Qed.

  Theorem bounded_report_handoff_rejected : forall r,
    runtime_report_completeness r = BoundedByCycleCut ->
    handoff_status (handoff_from_report r) = HandoffRejectedBounded /\
    handoff_is_ready (handoff_from_report r) = false /\
    handoff_observations (handoff_from_report r) = [].
  Proof.
    intros [roots terms status] Hbounded. simpl in *.
    rewrite Hbounded. repeat split; reflexivity.
  Qed.

  Theorem bounded_extraction_handoff_rejected : forall e,
    extraction_completeness e = BoundedByCycleCut ->
    handoff_status (handoff_from_extraction e) = HandoffRejectedBounded /\
    handoff_is_ready (handoff_from_extraction e) = false /\
    handoff_observations (handoff_from_extraction e) = [].
  Proof.
    intros e Hbounded. unfold handoff_from_extraction.
    apply bounded_report_handoff_rejected.
    rewrite report_completeness_matches_extraction.
    exact Hbounded.
  Qed.

  Theorem complete_extraction_handoff_preserves_root_order : forall e,
    extraction_completeness e = Complete ->
    handoff_observations (handoff_from_extraction e) =
      root_keys (extraction_value e).
  Proof.
    intros e Hcomplete. unfold handoff_from_extraction.
    rewrite complete_report_handoff_preserves_roots.
    - apply report_roots_preserve_extractor_order.
    - rewrite report_completeness_matches_extraction. exact Hcomplete.
  Qed.

  Theorem ready_handoff_observations_are_report_roots : forall r,
    handoff_is_ready (handoff_from_report r) = true ->
    handoff_observations (handoff_from_report r) = runtime_report_roots r.
  Proof.
    intros r Hready.
    apply complete_report_handoff_preserves_roots.
    apply ready_handoff_originates_complete_report.
    exact Hready.
  Qed.

  Theorem handoff_observation_membership_exact : forall h key,
    handoff_observes_key h key = true <-> In key (handoff_observations h).
  Proof.
    intros h key. unfold handoff_observes_key.
    rewrite existsb_exists. split.
    - intros [candidate [Hin Heq]].
      apply Nat.eqb_eq in Heq. subst candidate. exact Hin.
    - intros Hin.
      exists key. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Theorem ready_handoff_observed_root_has_term_record : forall e key,
    extraction_completeness e = Complete ->
    handoff_observes_key (handoff_from_extraction e) key = true ->
    In key (runtime_report_terms (report_from_extraction e)).
  Proof.
    intros e key Hcomplete Hobs.
    apply handoff_observation_membership_exact in Hobs.
    unfold handoff_from_extraction in Hobs.
    rewrite complete_report_handoff_preserves_roots in Hobs.
    - apply report_root_keys_have_term_records. exact Hobs.
    - rewrite report_completeness_matches_extraction. exact Hcomplete.
  Qed.

  Theorem ready_handoff_observed_key_came_from_extraction : forall e key,
    extraction_completeness e = Complete ->
    handoff_observes_key (handoff_from_extraction e) key = true ->
    In key (forest_keys (extraction_value e)).
  Proof.
    intros e key Hcomplete Hobs.
    apply report_term_keys_come_from_extraction.
    eapply ready_handoff_observed_root_has_term_record.
    - exact Hcomplete.
    - exact Hobs.
  Qed.

End RhoReportHandoff.
