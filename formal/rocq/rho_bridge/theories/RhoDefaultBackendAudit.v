(*
 * RhoDefaultBackendAudit: diagnostic planning view before exact coverage.
 *
 * Rust image:
 *   - `mettail_rholang_codegen::audit_rho_default_backend` lowers a structured
 *     `LanguageDef`, classifies rejected rules, collects guard obligations,
 *     validates the generated `rhoapi::Par`, and runs the same flip decision
 *     under the strict assumption that no external coverage has been supplied.
 *   - Advisory rejected-rule classifications are diagnostic output only. They
 *     do not make coverage pass until accepted through
 *     `plan_rho_default_backend` as exact rejected-rule and guard evidence.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat.
From RhoBridge Require Import RhoBackendFlipGate.

Section RhoDefaultBackendAudit.

  Record AuditState : Type := {
    rejected_rule_count : nat;
    suggested_disposition_count : nat;
    guard_obligation_count : nat;
    validation_error_count : nat;
    deadlock_diagnostic_count : nat
  }.

  Definition no_external_coverage_passed (audit : AuditState) : bool :=
    Nat.eqb (rejected_rule_count audit) 0 &&
    Nat.eqb (guard_obligation_count audit) 0.

  Definition artifact_validated_by_audit (audit : AuditState) : bool :=
    Nat.eqb (validation_error_count audit) 0.

  Definition audit_gate_state (audit : AuditState) : GateState :=
    gate_state_from_deadlock_report
      (no_external_coverage_passed audit)
      (artifact_validated_by_audit audit)
      (deadlock_diagnostic_count audit).

  Definition audit_can_plan_without_external_coverage
      (audit : AuditState) : bool :=
    can_flip_to_rho (audit_gate_state audit).

  Theorem audit_can_plan_without_external_coverage_iff :
    forall audit,
      audit_can_plan_without_external_coverage audit = true <->
      rejected_rule_count audit = 0 /\
      guard_obligation_count audit = 0 /\
      validation_error_count audit = 0 /\
      deadlock_diagnostic_count audit = 0.
  Proof.
    intros [rejected suggestions guards validation deadlocks].
    unfold audit_can_plan_without_external_coverage,
      audit_gate_state, no_external_coverage_passed,
      artifact_validated_by_audit, gate_state_from_deadlock_report,
      can_flip_to_rho, deadlock_report_passes.
    simpl.
    repeat rewrite andb_true_iff.
    repeat rewrite Nat.eqb_eq.
    split.
    - intros [[[Hrejected Hguards] Hvalidation] Hdeadlocks].
      repeat split; assumption.
    - intros [Hrejected [Hguards [Hvalidation Hdeadlocks]]].
      repeat split; assumption.
  Qed.

  Theorem advisory_suggestion_count_ignored_by_audit :
    forall rejected suggestions_left suggestions_right guards validation deadlocks,
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions_left;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |} =
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions_right;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |}.
  Proof.
    intros rejected suggestions_left suggestions_right guards validation deadlocks.
    reflexivity.
  Qed.

  Theorem rejected_rules_block_audit_without_external_coverage :
    forall rejected suggestions guards validation deadlocks,
      rejected <> 0 ->
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |} = false.
  Proof.
    intros rejected suggestions guards validation deadlocks Hnonzero.
    unfold audit_can_plan_without_external_coverage,
      audit_gate_state, no_external_coverage_passed,
      artifact_validated_by_audit, gate_state_from_deadlock_report,
      can_flip_to_rho.
    simpl.
    assert (Hrejected : Nat.eqb rejected 0 = false).
    { apply Nat.eqb_neq. exact Hnonzero. }
    rewrite Hrejected. reflexivity.
  Qed.

  Theorem guard_obligations_block_audit_without_external_coverage :
    forall rejected suggestions guards validation deadlocks,
      guards <> 0 ->
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |} = false.
  Proof.
    intros rejected suggestions guards validation deadlocks Hnonzero.
    unfold audit_can_plan_without_external_coverage,
      audit_gate_state, no_external_coverage_passed,
      artifact_validated_by_audit, gate_state_from_deadlock_report,
      can_flip_to_rho.
    simpl.
    assert (Hguards : Nat.eqb guards 0 = false).
    { apply Nat.eqb_neq. exact Hnonzero. }
    rewrite Hguards.
    destruct (Nat.eqb rejected 0); reflexivity.
  Qed.

  Theorem validation_errors_block_audit :
    forall rejected suggestions guards validation deadlocks,
      validation <> 0 ->
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |} = false.
  Proof.
    intros rejected suggestions guards validation deadlocks Hnonzero.
    unfold audit_can_plan_without_external_coverage,
      audit_gate_state, no_external_coverage_passed,
      artifact_validated_by_audit, gate_state_from_deadlock_report,
      can_flip_to_rho.
    simpl.
    assert (Hvalidation : Nat.eqb validation 0 = false).
    { apply Nat.eqb_neq. exact Hnonzero. }
    rewrite Hvalidation.
    destruct (Nat.eqb rejected 0); destruct (Nat.eqb guards 0); reflexivity.
  Qed.

  Theorem deadlock_diagnostics_block_audit :
    forall rejected suggestions guards validation deadlocks,
      deadlocks <> 0 ->
      audit_can_plan_without_external_coverage
        {| rejected_rule_count := rejected;
           suggested_disposition_count := suggestions;
           guard_obligation_count := guards;
           validation_error_count := validation;
           deadlock_diagnostic_count := deadlocks |} = false.
  Proof.
    intros rejected suggestions guards validation deadlocks Hnonzero.
    unfold audit_can_plan_without_external_coverage, audit_gate_state.
    apply deadlock_diagnostic_blocks_flip.
    exact Hnonzero.
  Qed.

End RhoDefaultBackendAudit.
