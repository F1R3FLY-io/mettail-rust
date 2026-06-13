(*
 * CycleCutBoundary: Dovetail does not silently claim full cyclic k>=2
 * derivation enumeration.
 *
 * Cyclic inside weights are closed by the SCC/Newton proof. Productive cyclic
 * derivation spaces are not finitely exhaustible in general (proved by
 * CyclicEnumerationImpossibility.v), so k>=2 derivation enumeration across
 * back-edges is intentionally bounded by the extractor cycle guard. The Rust
 * result is `Extraction<T> { value,
 * completeness }`, where `completeness()` is determined directly by the
 * extractor's `cycle_cut` flag. This file proves the abstract reporting
 * contract: a cycle cut is reported as bounded, not as complete.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.

Import ListNotations.

Section CycleCutBoundary.

  Inductive GraphShape : Type :=
    | Acyclic
    | Cyclic.

  Inductive CompletenessStatus : Type :=
    | Complete
    | BoundedByCycleCut.

  Record ExtractReport : Type := {
    report_shape : GraphShape;
    report_outputs : list nat;
    had_cycle_cut : bool
  }.

  Definition status_of (r : ExtractReport) : CompletenessStatus :=
    match had_cycle_cut r with
    | true => BoundedByCycleCut
    | false => Complete
    end.

  Record Extraction (A : Type) : Type := {
    extraction_value : A;
    extraction_completeness : CompletenessStatus
  }.
  Arguments extraction_value {A} _.
  Arguments extraction_completeness {A} _.

  Definition to_extraction (r : ExtractReport) : Extraction (list nat) :=
    {|
      extraction_value := report_outputs r;
      extraction_completeness := status_of r
    |}.

  Definition cycle_guarded (r : ExtractReport) : Prop :=
    report_shape r = Cyclic -> had_cycle_cut r = true.

  Theorem cut_report_is_bounded : forall r,
    had_cycle_cut r = true ->
    status_of r = BoundedByCycleCut.
  Proof.
    intros r Hcut. unfold status_of. rewrite Hcut. reflexivity.
  Qed.

  Theorem complete_report_has_no_cycle_cut : forall r,
    status_of r = Complete ->
    had_cycle_cut r = false.
  Proof.
    intros r Hcomplete. unfold status_of in Hcomplete.
    destruct (had_cycle_cut r); simpl in Hcomplete.
    - discriminate.
    - reflexivity.
  Qed.

  Theorem extraction_completeness_matches_status : forall r,
    extraction_completeness (to_extraction r) = status_of r.
  Proof. intros r. reflexivity. Qed.

  Theorem guarded_cyclic_report_is_bounded : forall r,
    cycle_guarded r ->
    report_shape r = Cyclic ->
    status_of r = BoundedByCycleCut.
  Proof.
    intros r Hguard Hcyc.
    apply cut_report_is_bounded.
    apply Hguard. exact Hcyc.
  Qed.

  Theorem no_silent_cyclic_complete_claim : forall r,
    cycle_guarded r ->
    report_shape r = Cyclic ->
    status_of r <> Complete.
  Proof.
    intros r Hguard Hcyc Hcomplete.
    rewrite (guarded_cyclic_report_is_bounded r Hguard Hcyc) in Hcomplete.
    discriminate.
  Qed.

End CycleCutBoundary.
