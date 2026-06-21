(*
 * RhoArtifactBoundary: generated Rho backends execute validated host artifacts,
 * never Rholang source text.
 *
 * Rust image:
 *   - `rholang-codegen::RhoProgram` currently exposes only
 *     `RhoProgram::Ast(RhoAstProgram)`.
 *   - `ValidatedRhoProgram` validates that AST shape before
 *     `rholang-runtime::PlannedRhoBackend` can execute it.
 *   - Rholang-looking text is an annotation for readers/logs/tests. It is not
 *     parsed to produce the generated backend's executable value.
 *
 * This model deliberately includes a `SourceTextArtifact` constructor that the
 * current Rust API does not expose. The negative theorems prove the boundary
 * explicitly: if such a value appears in the artifact universe, generated
 * backend execution rejects it.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From RhoBridge Require Import RhoBackendFlipGate.
From RhoBridge Require Import RhoParWellFormedness.
From RhoBridge Require Import RhoPlannedExecutionBoundary.

Import ListNotations.

Section RhoArtifactBoundary.

  Inductive ExecutionArtifact : Type :=
    | AstExecutionArtifact : RhoArtifact -> ExecutionArtifact
    | BytecodeArtifact : list nat -> ExecutionArtifact
    | SourceTextArtifact : list nat -> ExecutionArtifact.

  Definition artifact_is_source_text (artifact : ExecutionArtifact) : bool :=
    match artifact with
    | SourceTextArtifact _ => true
    | AstExecutionArtifact _ => false
    | BytecodeArtifact _ => false
    end.

  Definition artifact_is_current_ast (artifact : ExecutionArtifact) : bool :=
    match artifact with
    | AstExecutionArtifact _ => true
    | BytecodeArtifact _ => false
    | SourceTextArtifact _ => false
    end.

  Definition current_generated_artifact_accepts
      (artifact : ExecutionArtifact) : bool :=
    match artifact with
    | AstExecutionArtifact ast =>
        match validate_artifact ast with
        | Some _ => true
        | None => false
        end
    | BytecodeArtifact _ => false
    | SourceTextArtifact _ => false
    end.

  Definition current_lowered_scalar_artifact
      (arities : list nat) : ExecutionArtifact :=
    AstExecutionArtifact (NormalizedAstArtifact (map scalar_contract arities)).

  Theorem source_text_artifact_rejected : forall bytes,
    current_generated_artifact_accepts (SourceTextArtifact bytes) = false.
  Proof. intros bytes. reflexivity. Qed.

  Theorem bytecode_artifact_not_currently_accepted : forall bytes,
    current_generated_artifact_accepts (BytecodeArtifact bytes) = false.
  Proof. intros bytes. reflexivity. Qed.

  Theorem accepted_current_generated_artifact_not_source_text : forall artifact,
    current_generated_artifact_accepts artifact = true ->
    artifact_is_source_text artifact = false.
  Proof.
    intros [ast | bytes | source] Haccept; simpl in *.
    - reflexivity.
    - discriminate Haccept.
    - discriminate Haccept.
  Qed.

  Theorem accepted_current_generated_artifact_is_ast : forall artifact,
    current_generated_artifact_accepts artifact = true ->
    artifact_is_current_ast artifact = true.
  Proof.
    intros [ast | bytes | source] Haccept; simpl in *.
    - reflexivity.
    - discriminate Haccept.
    - discriminate Haccept.
  Qed.

  Theorem accepted_current_generated_artifact_has_validated_ast : forall artifact,
    current_generated_artifact_accepts artifact = true ->
    exists ast validated,
      artifact = AstExecutionArtifact ast /\
      validate_artifact ast = Some validated.
  Proof.
    intros [ast | bytes | source] Haccept; simpl in *.
    - destruct (validate_artifact ast) as [validated |] eqn:Hvalidate.
      + exists ast, validated. repeat split. exact Hvalidate.
      + discriminate Haccept.
    - discriminate Haccept.
    - discriminate Haccept.
  Qed.

  Theorem current_lowered_scalar_artifact_is_ast_not_source_text : forall arities,
    artifact_is_current_ast (current_lowered_scalar_artifact arities) = true
    /\ artifact_is_source_text (current_lowered_scalar_artifact arities) = false.
  Proof.
    intros arities. split; reflexivity.
  Qed.

  Theorem current_lowered_scalar_artifact_accepts : forall arities,
    current_generated_artifact_accepts
      (current_lowered_scalar_artifact arities) = true.
  Proof.
    intros arities. unfold current_lowered_scalar_artifact,
      current_generated_artifact_accepts.
    destruct (lowered_scalar_program_validates arities)
      as [validated [Hvalidate _]].
    rewrite Hvalidate. reflexivity.
  Qed.

  Theorem planned_current_execution_never_uses_source_text : forall plan artifact,
    generated_backend_accepts PlannedDefaultBackend plan = true ->
    current_generated_artifact_accepts artifact = true ->
    artifact_is_source_text artifact = false.
  Proof.
    intros plan artifact _ Hartifact.
    apply accepted_current_generated_artifact_not_source_text.
    exact Hartifact.
  Qed.

  Theorem planned_current_execution_has_validated_ast_artifact : forall plan artifact,
    generated_backend_accepts PlannedDefaultBackend plan = true ->
    current_generated_artifact_accepts artifact = true ->
    exists ast validated,
      artifact = AstExecutionArtifact ast /\
      validate_artifact ast = Some validated /\
      artifact_validated (planned_gate_state plan) = true.
  Proof.
    intros plan artifact Hplan Hartifact.
    destruct (accepted_current_generated_artifact_has_validated_ast artifact Hartifact)
      as [ast [validated [Hast_eq Hvalidate]]].
    exists ast, validated. repeat split.
    - exact Hast_eq.
    - exact Hvalidate.
    - apply accepted_planned_execution_implies_gate_artifact_validated.
      exact Hplan.
  Qed.

End RhoArtifactBoundary.
