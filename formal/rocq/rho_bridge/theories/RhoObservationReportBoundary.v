(*
 * RhoObservationReportBoundary: planned Rho execution reports expose typed
 * observations without routing through AscentResults.
 *
 * Rust image:
 *   - `mettail_rholang_runtime::RhoObservationReport<T>` carries the planned
 *     execution boundary, artifact kind, channel, and observed values.
 *   - `membership_fingerprint()` is the order-insensitive set view used by
 *     set-semantics oracle checks.
 *   - `multiplicity_fingerprint()` is the order-insensitive counted view used
 *     when duplicate resting observations are semantically relevant.
 *   - the read-order vector remains diagnostic data.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From RhoBridge Require Import RhoPlannedExecutionBoundary.
From RhoBridge Require Import RhoObservationFingerprint.

Import ListNotations.

Section RhoObservationReportBoundary.

  Record ObservationReport : Type := {
    observation_entry : ExecutionEntry;
    observation_channel : nat;
    observation_values : list Fact
  }.

  Definition planned_observation_report
      (channel : nat)
      (values : list Fact) : ObservationReport :=
    {|
      observation_entry := PlannedDefaultBackend;
      observation_channel := channel;
      observation_values := values
    |}.

  Definition observation_fingerprint (r : ObservationReport) (x : Fact) : bool :=
    fingerprint (observation_values r) x.

  Definition observation_fingerprint_equiv (left right : ObservationReport) : Prop :=
    forall x, observation_fingerprint left x = observation_fingerprint right x.

  Definition observation_multiplicity (r : ObservationReport) (x : Fact) : nat :=
    multiplicity (observation_values r) x.

  Definition observation_multiplicity_equiv
      (left right : ObservationReport) : Prop :=
    forall x, observation_multiplicity left x =
              observation_multiplicity right x.

  Theorem planned_report_boundary_is_planned : forall channel values,
    observation_entry (planned_observation_report channel values) =
      PlannedDefaultBackend.
  Proof. intros channel values. reflexivity. Qed.

  Theorem planned_report_is_not_raw_validated_artifact : forall channel values,
    observation_entry (planned_observation_report channel values) <>
      RawValidatedArtifact.
  Proof.
    intros channel values Hraw. discriminate Hraw.
  Qed.

  Theorem planned_report_preserves_channel : forall channel values,
    observation_channel (planned_observation_report channel values) = channel.
  Proof. intros channel values. reflexivity. Qed.

  Theorem planned_report_preserves_values : forall channel values,
    observation_values (planned_observation_report channel values) = values.
  Proof. intros channel values. reflexivity. Qed.

  Theorem observation_report_fingerprint_exact : forall r x,
    observation_fingerprint r x = true <-> In x (observation_values r).
  Proof.
    intros r x. unfold observation_fingerprint.
    apply fingerprint_exact.
  Qed.

  Theorem observation_report_fingerprint_equiv_exact : forall left right,
    observation_fingerprint_equiv left right
    <-> (forall x, In x (observation_values left) <->
                  In x (observation_values right)).
  Proof.
    intros left right. unfold observation_fingerprint_equiv, observation_fingerprint.
    apply fingerprint_equiv_exact.
  Qed.

  Theorem observation_report_multiplicity_exact : forall r x,
    observation_multiplicity r x = multiplicity (observation_values r) x.
  Proof. intros r x. reflexivity. Qed.

  Theorem observation_report_multiplicity_positive_exact : forall r x,
    observation_multiplicity r x > 0 <-> In x (observation_values r).
  Proof.
    intros r x. unfold observation_multiplicity.
    apply multiplicity_positive_exact.
  Qed.

  Theorem observation_report_permutation_same_multiplicity : forall left right,
    Permutation (observation_values left) (observation_values right) ->
    observation_multiplicity_equiv left right.
  Proof.
    intros left right Hperm x. unfold observation_multiplicity.
    apply multiplicity_permutation_exact. exact Hperm.
  Qed.

  Theorem planned_reports_same_membership_same_fingerprint :
    forall channel_left channel_right values_left values_right,
      (forall x, In x values_left <-> In x values_right) ->
      observation_fingerprint_equiv
        (planned_observation_report channel_left values_left)
        (planned_observation_report channel_right values_right).
  Proof.
    intros channel_left channel_right values_left values_right Hsame.
    apply observation_report_fingerprint_equiv_exact.
    simpl. exact Hsame.
  Qed.

  Theorem planned_reports_same_bag_same_multiplicity :
    forall channel_left channel_right values_left values_right,
      Permutation values_left values_right ->
      observation_multiplicity_equiv
        (planned_observation_report channel_left values_left)
        (planned_observation_report channel_right values_right).
  Proof.
    intros channel_left channel_right values_left values_right Hperm.
    apply observation_report_permutation_same_multiplicity.
    simpl. exact Hperm.
  Qed.

End RhoObservationReportBoundary.
