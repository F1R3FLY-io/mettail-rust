(*
 * ExtractionOutcome: checked stream results expose terminal completeness.
 *
 * Rust exposes `Derivations::next_checked()`, whose terminal `Done` value
 * carries `ExtractionCompleteness`. This module states the small bridge between
 * checked stream steps and the existing cycle-cut boundary model.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Dovetail.Extraction Require Import CycleCutBoundary.

Import ListNotations.

Section ExtractionOutcome.

  Inductive ExtractionStep (A : Type) : Type :=
    | StepItem : A -> ExtractionStep A
    | StepDone : CompletenessStatus -> ExtractionStep A.

  Arguments StepItem {A} _.
  Arguments StepDone {A} _.

  Definition terminal_status {A : Type} (step : ExtractionStep A)
    : option CompletenessStatus :=
    match step with
    | StepItem _ => None
    | StepDone status => Some status
    end.

  Definition done_from_report (r : ExtractReport) : ExtractionStep (list nat) :=
    StepDone (status_of r).

  Theorem done_from_cut_report_is_bounded : forall r,
    had_cycle_cut r = true ->
    terminal_status (done_from_report r) = Some BoundedByCycleCut.
  Proof.
    intros r Hcut. unfold terminal_status, done_from_report.
    rewrite (cut_report_is_bounded r Hcut). reflexivity.
  Qed.

  Theorem done_from_complete_report_is_complete : forall r,
    had_cycle_cut r = false ->
    terminal_status (done_from_report r) = Some Complete.
  Proof.
    intros r Hcut. unfold terminal_status, done_from_report, status_of.
    rewrite Hcut. reflexivity.
  Qed.

  Theorem checked_done_never_loses_cycle_cut : forall r,
    cycle_guarded r ->
    report_shape r = Cyclic ->
    terminal_status (done_from_report r) = Some BoundedByCycleCut.
  Proof.
    intros r Hguard Hcyclic.
    unfold terminal_status, done_from_report.
    rewrite (guarded_cyclic_report_is_bounded r Hguard Hcyclic).
    reflexivity.
  Qed.

End ExtractionOutcome.
