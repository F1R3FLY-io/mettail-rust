(*
 * CycleCutBoundary: Dovetail does not silently claim full cyclic k>=2
 * derivation enumeration.
 *
 * Cyclic inside weights are closed by the SCC/Newton proof, but full k>=2
 * derivation enumeration on cyclic hypergraphs is intentionally bounded by the
 * extractor cycle guard. The Rust result carries `had_cycle_cut`; this file
 * proves the abstract reporting contract: cyclic bounded extraction is reported
 * as bounded, not as complete.
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
    match report_shape r, had_cycle_cut r with
    | Acyclic, _ => Complete
    | Cyclic, true => BoundedByCycleCut
    | Cyclic, false => Complete
    end.

  Definition cycle_guarded (r : ExtractReport) : Prop :=
    report_shape r = Cyclic -> had_cycle_cut r = true.

  Theorem guarded_cyclic_report_is_bounded : forall r,
    cycle_guarded r ->
    report_shape r = Cyclic ->
    status_of r = BoundedByCycleCut.
  Proof.
    intros r Hguard Hcyc. unfold status_of.
    destruct r as [shape outputs cut]. simpl in *.
    subst shape. rewrite Hguard.
    - reflexivity.
    - reflexivity.
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
