(*
 * RhoPlannedExecutionBoundary: generated Rho backend execution uses the
 * flip-gated backend plan, not merely a raw validated artifact.
 *
 * Rust image:
 *   - `mettail_rholang_codegen::RhoDefaultBackendPlan` is created only when the
 *     coverage/artifact/deadlock gate accepts.
 *   - `mettail_rholang_runtime::PlannedRhoBackend` is built from that plan and is
 *     the generated-backend execution boundary.
 *   - raw `ValidatedRhoProgram` execution remains available for oracle/debug
 *     code, but it is not the generated-backend entry point.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From RhoBridge Require Import RhoBackendFlipGate.

Section RhoPlannedExecutionBoundary.

  Inductive ExecutionEntry : Type :=
    | RawValidatedArtifact
    | PlannedDefaultBackend.

  Record PlannedExecution : Type := {
    planned_gate_state : GateState;
    planned_has_validated_artifact : bool
  }.

  Definition planned_execution_ready (p : PlannedExecution) : bool :=
    can_flip_to_rho (planned_gate_state p)
    && planned_has_validated_artifact p.

  Definition generated_backend_accepts
      (entry : ExecutionEntry)
      (plan : PlannedExecution) : bool :=
    match entry with
    | RawValidatedArtifact => false
    | PlannedDefaultBackend => planned_execution_ready plan
    end.

  Theorem raw_validated_artifact_is_not_generated_backend_entry : forall p,
    generated_backend_accepts RawValidatedArtifact p = false.
  Proof. intros p. reflexivity. Qed.

  Theorem accepted_execution_is_planned : forall entry p,
    generated_backend_accepts entry p = true ->
    entry = PlannedDefaultBackend.
  Proof.
    intros entry p Haccept.
    destruct entry.
    - discriminate.
    - reflexivity.
  Qed.

  Theorem planned_acceptance_iff_flip_and_validated : forall p,
    generated_backend_accepts PlannedDefaultBackend p = true
    <-> can_flip_to_rho (planned_gate_state p) = true
        /\ planned_has_validated_artifact p = true.
  Proof.
    intros [gate artifact]. simpl.
    apply andb_true_iff.
  Qed.

  Theorem accepted_planned_execution_implies_can_flip : forall p,
    generated_backend_accepts PlannedDefaultBackend p = true ->
    can_flip_to_rho (planned_gate_state p) = true.
  Proof.
    intros p Haccept.
    apply planned_acceptance_iff_flip_and_validated in Haccept.
    destruct Haccept as [Hflip _]. exact Hflip.
  Qed.

  Theorem accepted_planned_execution_implies_validated_artifact : forall p,
    generated_backend_accepts PlannedDefaultBackend p = true ->
    planned_has_validated_artifact p = true.
  Proof.
    intros p Haccept.
    apply planned_acceptance_iff_flip_and_validated in Haccept.
    destruct Haccept as [_ Hvalidated]. exact Hvalidated.
  Qed.

  Theorem accepted_planned_execution_implies_gate_artifact_validated : forall p,
    generated_backend_accepts PlannedDefaultBackend p = true ->
    artifact_validated (planned_gate_state p) = true.
  Proof.
    intros p Haccept.
    apply accepted_planned_execution_implies_can_flip in Haccept.
    apply can_flip_iff_all_gates in Haccept.
    destruct Haccept as [_ [Hartifact _]].
    exact Hartifact.
  Qed.

  Theorem missing_flip_gate_blocks_planned_execution : forall p,
    can_flip_to_rho (planned_gate_state p) = false ->
    generated_backend_accepts PlannedDefaultBackend p = false.
  Proof.
    intros [gate artifact] Hflip.
    simpl in Hflip.
    change ((can_flip_to_rho gate && artifact) = false).
    rewrite Hflip. reflexivity.
  Qed.

  Theorem missing_validated_artifact_blocks_planned_execution : forall gate,
    generated_backend_accepts
      PlannedDefaultBackend
      {| planned_gate_state := gate;
         planned_has_validated_artifact := false |} = false.
  Proof.
    intros gate.
    change ((can_flip_to_rho gate && false) = false).
    destruct (can_flip_to_rho gate); reflexivity.
  Qed.

End RhoPlannedExecutionBoundary.
