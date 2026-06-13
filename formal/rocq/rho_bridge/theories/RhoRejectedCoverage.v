(*
 * RhoRejectedCoverage: exact coverage for Rho lowering rejections.
 *
 * Rust image:
 *   - `mettail_rho_codegen::RhoCoverageEvidence::AllRulesLowered` is valid
 *     only when `RhoLowering::rejected` is empty.
 *   - `DelegatedRejectedRules(labels)` is valid only when `labels` names
 *     exactly the rejected rules: no rejected rule is omitted and no stale
 *     delegation names a rule that did not reject.
 *   - `plan_rho_default_backend` turns those two list-level diagnostics into
 *     `uncovered_rejections` and `extraneous_delegations` coverage counters
 *     before calling the flip gate.
 *
 * This file proves the rule-identity/set-level contract underneath those
 * counters. Counts alone are not the specification: exact membership is.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import RhoBackendFlipGate.

Import ListNotations.

Section RhoRejectedCoverage.

  Definition RuleId : Type := nat.

  Definition rule_member (rule : RuleId) (rules : list RuleId) : bool :=
    existsb (Nat.eqb rule) rules.

  Lemma rule_member_iff : forall rule rules,
    rule_member rule rules = true <-> In rule rules.
  Proof.
    intros rule rules. unfold rule_member.
    rewrite existsb_exists. split.
    - intros [candidate [Hin Heq]].
      apply Nat.eqb_eq in Heq. subst candidate. exact Hin.
    - intros Hin.
      exists rule. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma rule_member_false_iff : forall rule rules,
    rule_member rule rules = false <-> ~ In rule rules.
  Proof.
    intros rule rules.
    rewrite <- not_true_iff_false.
    rewrite rule_member_iff.
    reflexivity.
  Qed.

  Definition all_members_of (xs ys : list RuleId) : bool :=
    forallb (fun rule => rule_member rule ys) xs.

  Lemma all_members_of_iff : forall xs ys,
    all_members_of xs ys = true <-> forall rule, In rule xs -> In rule ys.
  Proof.
    intros xs ys. unfold all_members_of.
    rewrite forallb_forall. split.
    - intros Hall rule Hin.
      apply rule_member_iff. apply Hall. exact Hin.
    - intros Hall rule Hin.
      apply rule_member_iff. apply Hall. exact Hin.
  Qed.

  Inductive RejectionCoverageEvidence : Type :=
    | AllRulesLowered
    | DelegatedRejectedRules : list RuleId -> RejectionCoverageEvidence.

  Definition delegated_rule_ids (evidence : RejectionCoverageEvidence)
      : list RuleId :=
    match evidence with
    | AllRulesLowered => []
    | DelegatedRejectedRules delegated => delegated
    end.

  Definition uncovered_rejection_ids
      (rejected delegated : list RuleId) : list RuleId :=
    filter (fun rule => negb (rule_member rule delegated)) rejected.

  Definition extraneous_delegation_ids
      (rejected delegated : list RuleId) : list RuleId :=
    filter (fun rule => negb (rule_member rule rejected)) delegated.

  Definition delegated_rejections_exact
      (rejected delegated : list RuleId) : bool :=
    all_members_of rejected delegated && all_members_of delegated rejected.

  Definition coverage_evidence_exact
      (evidence : RejectionCoverageEvidence)
      (rejected : list RuleId) : bool :=
    match evidence with
    | AllRulesLowered =>
        match rejected with
        | [] => true
        | _ :: _ => false
        end
    | DelegatedRejectedRules delegated =>
        delegated_rejections_exact rejected delegated
    end.

  Definition coverage_state_from_evidence
      (audit : bool)
      (evidence : RejectionCoverageEvidence)
      (rejected : list RuleId) : CoverageState :=
    let delegated := delegated_rule_ids evidence in
    {|
      coverage_audit_passed := audit;
      uncovered_rejections := length (uncovered_rejection_ids rejected delegated);
      extraneous_delegations := length (extraneous_delegation_ids rejected delegated)
    |}.

  Theorem all_rules_lowered_exact_iff_no_rejections : forall rejected,
    coverage_evidence_exact AllRulesLowered rejected = true
    <-> rejected = [].
  Proof.
    intros rejected. destruct rejected as [| r rest]; simpl; split; intro H.
    - reflexivity.
    - reflexivity.
    - discriminate H.
    - discriminate H.
  Qed.

  Theorem delegated_rejections_exact_iff_same_rule_set : forall rejected delegated,
    delegated_rejections_exact rejected delegated = true
    <-> forall rule, In rule rejected <-> In rule delegated.
  Proof.
    intros rejected delegated. unfold delegated_rejections_exact.
    rewrite andb_true_iff.
    repeat rewrite all_members_of_iff.
    split.
    - intros [Hcovered Hstale] rule.
      split.
      + apply Hcovered.
      + apply Hstale.
    - intros Hsame. split.
      + intros rule Hin. apply Hsame. exact Hin.
      + intros rule Hin. apply Hsame. exact Hin.
  Qed.

  Theorem delegated_coverage_omits_no_rejected_rule : forall rejected delegated rule,
    delegated_rejections_exact rejected delegated = true ->
    In rule rejected ->
    In rule delegated.
  Proof.
    intros rejected delegated rule Hexact Hin.
    destruct (delegated_rejections_exact_iff_same_rule_set rejected delegated)
      as [Hto_set _].
    specialize (Hto_set Hexact rule).
    apply Hto_set. exact Hin.
  Qed.

  Theorem delegated_coverage_has_no_stale_rule : forall rejected delegated rule,
    delegated_rejections_exact rejected delegated = true ->
    In rule delegated ->
    In rule rejected.
  Proof.
    intros rejected delegated rule Hexact Hin.
    destruct (delegated_rejections_exact_iff_same_rule_set rejected delegated)
      as [Hto_set _].
    specialize (Hto_set Hexact rule).
    apply Hto_set. exact Hin.
  Qed.

  Theorem omitted_rejected_rule_blocks_exact_delegation : forall rejected delegated rule,
    In rule rejected ->
    ~ In rule delegated ->
    delegated_rejections_exact rejected delegated = false.
  Proof.
    intros rejected delegated rule Hrejected Homitted.
    destruct (delegated_rejections_exact rejected delegated) eqn:Hexact.
    - apply delegated_coverage_omits_no_rejected_rule with
        (rule := rule) in Hexact.
      + contradiction.
      + exact Hrejected.
    - reflexivity.
  Qed.

  Theorem stale_delegated_rule_blocks_exact_delegation : forall rejected delegated rule,
    In rule delegated ->
    ~ In rule rejected ->
    delegated_rejections_exact rejected delegated = false.
  Proof.
    intros rejected delegated rule Hdelegated Hstale.
    destruct (delegated_rejections_exact rejected delegated) eqn:Hexact.
    - apply delegated_coverage_has_no_stale_rule with
        (rule := rule) in Hexact.
      + contradiction.
      + exact Hdelegated.
    - reflexivity.
  Qed.

  Lemma omitted_rule_appears_in_uncovered : forall rejected delegated rule,
    In rule rejected ->
    ~ In rule delegated ->
    In rule (uncovered_rejection_ids rejected delegated).
  Proof.
    intros rejected delegated rule Hrejected Homitted.
    unfold uncovered_rejection_ids.
    apply filter_In. split.
    - exact Hrejected.
    - apply negb_true_iff.
      apply rule_member_false_iff.
      exact Homitted.
  Qed.

  Lemma stale_rule_appears_in_extraneous : forall rejected delegated rule,
    In rule delegated ->
    ~ In rule rejected ->
    In rule (extraneous_delegation_ids rejected delegated).
  Proof.
    intros rejected delegated rule Hdelegated Hstale.
    unfold extraneous_delegation_ids.
    apply filter_In. split.
    - exact Hdelegated.
    - apply negb_true_iff.
      apply rule_member_false_iff.
      exact Hstale.
  Qed.

  Lemma inhabited_list_has_nonzero_length : forall (xs : list RuleId) rule,
    In rule xs -> length xs <> 0.
  Proof.
    intros xs rule Hin Hlen.
    apply length_zero_iff_nil in Hlen.
    subst xs. contradiction.
  Qed.

  Theorem omitted_rejected_rule_blocks_default_backend : forall proofs oracle artifact audit rejected delegated rule diagnostics,
    In rule rejected ->
    ~ In rule delegated ->
    default_backend_gate proofs oracle artifact
      (coverage_state_from_evidence audit (DelegatedRejectedRules delegated) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact audit rejected delegated rule diagnostics
      Hrejected Homitted.
    apply uncovered_rejection_blocks_default_backend.
    apply inhabited_list_has_nonzero_length with (rule := rule).
    apply omitted_rule_appears_in_uncovered; assumption.
  Qed.

  Theorem stale_delegated_rule_blocks_default_backend : forall proofs oracle artifact audit rejected delegated rule diagnostics,
    In rule delegated ->
    ~ In rule rejected ->
    default_backend_gate proofs oracle artifact
      (coverage_state_from_evidence audit (DelegatedRejectedRules delegated) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact audit rejected delegated rule diagnostics
      Hdelegated Hstale.
    assert (Hnonzero :
      length (extraneous_delegation_ids rejected delegated) <> 0).
    {
      apply inhabited_list_has_nonzero_length with (rule := rule).
      apply stale_rule_appears_in_extraneous; assumption.
    }
    unfold default_backend_gate, gate_state_from_deadlock_report,
      coverage_state_from_evidence, exact_coverage_evidence,
      deadlock_report_passes.
    simpl.
    assert (Hextra :
      Nat.eqb (length (extraneous_delegation_ids rejected delegated)) 0 = false).
    { rewrite Nat.eqb_neq. exact Hnonzero. }
    rewrite Hextra.
    destruct proofs; destruct oracle; destruct artifact; destruct audit;
      destruct (Nat.eqb (length (uncovered_rejection_ids rejected delegated)) 0);
      reflexivity.
  Qed.

  Theorem all_rules_lowered_blocks_any_rejection : forall proofs oracle artifact audit rejected rule diagnostics,
    In rule rejected ->
    default_backend_gate proofs oracle artifact
      (coverage_state_from_evidence audit AllRulesLowered rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact audit rejected rule diagnostics Hrejected.
    apply omitted_rejected_rule_blocks_default_backend with
      (rule := rule).
    - exact Hrejected.
    - intros Hempty. inversion Hempty.
  Qed.

End RhoRejectedCoverage.
