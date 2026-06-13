(*
 * RhoRuntimeBackendReportBridge: conversion from planned Rho observation
 * reports to the generic runtime backend report preserves the observation
 * boundary and never fabricates an Ascent-shaped result.
 *
 * Rust image:
 *   - `RhoObservationReport<T>::into_runtime_backend_report` maps typed Rho
 *     values into `RuntimeObservationValue`.
 *   - The resulting `RuntimeBackendReport` has backend `RhoMachine`, artifact
 *     `RhoNormalizedAst`, exactly one channel observation, the same read-order
 *     values after payload mapping, and copied evidence references.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From RhoBridge Require Import RhoObservationReportBoundary.

Import ListNotations.

Section RhoRuntimeBackendReportBridge.

  Inductive RuntimeBackend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive RuntimeArtifact : Type :=
  | AscentFixpoint
  | DovetailRunReport
  | RhoNormalizedAst
  | RhoBytecode.

  Inductive RuntimeOutput : Type :=
  | AscentOutput
  | ObservationOutput : nat -> list nat -> RuntimeOutput.

  Record RuntimeBackendReport : Type := {
    runtime_backend : RuntimeBackend;
    runtime_artifact : RuntimeArtifact;
    runtime_output : RuntimeOutput;
    runtime_evidence_refs : list nat
  }.

  Definition rho_report_to_runtime_report
      (evidence_refs : list nat)
      (r : ObservationReport) : RuntimeBackendReport :=
    {|
      runtime_backend := RhoMachine;
      runtime_artifact := RhoNormalizedAst;
      runtime_output :=
        ObservationOutput (observation_channel r) (observation_values r);
      runtime_evidence_refs := evidence_refs
    |}.

  Definition runtime_report_is_ascent_output
      (r : RuntimeBackendReport) : bool :=
    match runtime_output r with
    | AscentOutput => true
    | ObservationOutput _ _ => false
    end.

  Definition runtime_report_observed_count
      (r : RuntimeBackendReport) : nat :=
    match runtime_output r with
    | AscentOutput => 0
    | ObservationOutput _ values => length values
    end.

  Theorem rho_runtime_report_backend_is_rho : forall evidence_refs report,
    runtime_backend (rho_report_to_runtime_report evidence_refs report) =
      RhoMachine.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_artifact_is_normalized_ast :
    forall evidence_refs report,
      runtime_artifact (rho_report_to_runtime_report evidence_refs report) =
        RhoNormalizedAst.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_is_not_ascent_output :
    forall evidence_refs report,
      runtime_report_is_ascent_output
        (rho_report_to_runtime_report evidence_refs report) = false.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_channel : forall evidence_refs report,
    runtime_output (rho_report_to_runtime_report evidence_refs report) =
      ObservationOutput (observation_channel report)
                        (observation_values report).
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_values : forall evidence_refs report,
    match runtime_output (rho_report_to_runtime_report evidence_refs report) with
    | AscentOutput => False
    | ObservationOutput _ values => values = observation_values report
    end.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_observed_count :
    forall evidence_refs report,
      runtime_report_observed_count
        (rho_report_to_runtime_report evidence_refs report) =
      length (observation_values report).
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_evidence_refs :
    forall evidence_refs report,
      runtime_evidence_refs
        (rho_report_to_runtime_report evidence_refs report) = evidence_refs.
  Proof. intros evidence_refs report. reflexivity. Qed.

End RhoRuntimeBackendReportBridge.
