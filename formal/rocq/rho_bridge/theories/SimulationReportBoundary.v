(*
 * SimulationReportBoundary: report-shaped simulation outcomes.
 *
 * The Rust simulation runner consumes RuntimeBackendReport. Ascent-shaped
 * reference reports expose a rewrite graph; complete Dovetail reports expose
 * extracted roots as terminal rewrite-result evidence; Rho observation reports
 * expose runtime observations, not normal-form reachability evidence.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

Section SimulationReportBoundary.

  Inductive DovetailCompleteness : Type :=
  | Complete
  | BoundedByCycleCut.

  Inductive RuntimeReportShape : Type :=
  | AscentGraphReport (normal_form_reachable : bool)
  | DovetailRunReport (completeness : DovetailCompleteness) (root_count : nat)
  | RuntimeObservationReport
  | UnsupportedReport.

  Inductive SimulationOutcome : Type :=
  | NormalFormOutcome
  | StepLimitOutcome
  | RuntimeReportOutcome
  | RuntimeObservationsOutcome
  | ErrorOutcome.

  Definition dovetail_has_terminal_rewrite_result
      (completeness : DovetailCompleteness) (root_count : nat) : bool :=
    match completeness, root_count with
    | Complete, S _ => true
    | _, _ => false
    end.

  Definition normal_form_reachable_evidence
      (report : RuntimeReportShape) : bool :=
    match report with
    | AscentGraphReport reachable => reachable
    | DovetailRunReport completeness roots =>
        dovetail_has_terminal_rewrite_result completeness roots
    | RuntimeObservationReport => false
    | UnsupportedReport => false
    end.

  Definition simulation_outcome (report : RuntimeReportShape) : SimulationOutcome :=
    match report with
    | AscentGraphReport true => NormalFormOutcome
    | AscentGraphReport false => StepLimitOutcome
    | DovetailRunReport _ _ => RuntimeReportOutcome
    | RuntimeObservationReport => RuntimeObservationsOutcome
    | UnsupportedReport => ErrorOutcome
    end.

  Theorem ascent_normal_form_evidence_is_exact : forall reachable,
    normal_form_reachable_evidence (AscentGraphReport reachable) = reachable.
  Proof. intros reachable. destruct reachable; reflexivity. Qed.

  Theorem complete_dovetail_with_root_satisfies_normal_form_reachable :
    forall roots,
      normal_form_reachable_evidence
        (DovetailRunReport Complete (S roots)) = true.
  Proof. intros roots. reflexivity. Qed.

  Theorem complete_dovetail_without_root_has_no_normal_form_evidence :
    normal_form_reachable_evidence
      (DovetailRunReport Complete 0) = false.
  Proof. reflexivity. Qed.

  Theorem bounded_dovetail_never_satisfies_normal_form_reachable :
    forall roots,
      normal_form_reachable_evidence
        (DovetailRunReport BoundedByCycleCut roots) = false.
  Proof. intros roots. destruct roots; reflexivity. Qed.

  Theorem runtime_observations_are_not_normal_form_evidence :
    normal_form_reachable_evidence RuntimeObservationReport = false.
  Proof. reflexivity. Qed.

  Theorem unsupported_reports_are_not_normal_form_evidence :
    normal_form_reachable_evidence UnsupportedReport = false.
  Proof. reflexivity. Qed.

  Theorem dovetail_reports_remain_runtime_report_outcomes :
    forall completeness roots,
      simulation_outcome (DovetailRunReport completeness roots) =
      RuntimeReportOutcome.
  Proof. intros completeness roots. destruct completeness; reflexivity. Qed.

  Theorem runtime_observations_remain_observation_outcomes :
    simulation_outcome RuntimeObservationReport = RuntimeObservationsOutcome.
  Proof. reflexivity. Qed.

End SimulationReportBoundary.
