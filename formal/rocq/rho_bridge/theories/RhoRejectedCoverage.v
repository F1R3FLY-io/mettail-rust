(*
 * RhoRejectedCoverage: exact coverage for Rho lowering rejections.
 *
 * Rust image:
 *   - `mettail_rho_codegen::RhoCoverageEvidence::AllRulesLowered` is valid
 *     only when `RhoLowering::rejected` is empty.
 *   - `CoveredRejectedRules(dispositions)` is valid only when its disposition
 *     rule ids name exactly the rejected rules: no rejected rule is omitted
 *     and no stale disposition names a rule that did not reject.
 *   - Each disposition must be auditable: the rule id and evidence reference
 *     are present, and no rule has duplicate dispositions.
 *   - `plan_rho_default_backend` turns those diagnostics into
 *     `uncovered_rejections`, `extraneous_dispositions`, and
 *     `invalid_dispositions` coverage counters before calling the flip gate.
 *
 * This file proves the rule-identity/set-level contract and the auditable
 * disposition contract underneath those counters. Counts alone are not the
 * specification: exact membership and valid evidence are.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From RhoBridge Require Import RhoBackendFlipGate.

Import ListNotations.

Section RhoRejectedCoverage.

  Definition RuleId : Type := nat.
  Definition EvidenceId : Type := nat.

  Inductive DispositionKind : Type :=
    | NativeHandler
    | ExternalContract
    | RhoAstContract.

  Record RejectedRuleDisposition : Type := {
    disposition_rule_id : RuleId;
    disposition_kind : DispositionKind;
    disposition_evidence_id : EvidenceId
  }.

  Record RejectedRuleClassification : Type := {
    classification_rule_id : RuleId;
    classification_kind : option DispositionKind
  }.

  Definition classification_to_disposition
      (classification : RejectedRuleClassification)
      (evidence : EvidenceId) : option RejectedRuleDisposition :=
    match classification_kind classification with
    | Some kind =>
        Some {|
          disposition_rule_id := classification_rule_id classification;
          disposition_kind := kind;
          disposition_evidence_id := evidence
        |}
    | None => None
    end.

  (* In this finite model, zero is the missing/blank token for Rust's
     whitespace-only rule ids. *)
  Definition valid_rule_id (rule : RuleId) : bool :=
    negb (Nat.eqb rule 0).

  Definition valid_evidence_id (evidence : EvidenceId) : bool :=
    negb (Nat.eqb evidence 0).

  Definition disposition_valid (disposition : RejectedRuleDisposition) : bool :=
    valid_rule_id (disposition_rule_id disposition)
    && valid_evidence_id (disposition_evidence_id disposition).

  Theorem classification_without_kind_yields_no_disposition :
    forall rule evidence,
    classification_to_disposition
      {| classification_rule_id := rule; classification_kind := None |}
      evidence = None.
  Proof.
    intros rule evidence. reflexivity.
  Qed.

  Theorem classification_to_disposition_preserves_rule_and_evidence :
    forall classification evidence disposition,
    classification_to_disposition classification evidence = Some disposition ->
    disposition_rule_id disposition = classification_rule_id classification
    /\ disposition_evidence_id disposition = evidence.
  Proof.
    intros classification evidence disposition Hconvert.
    unfold classification_to_disposition in Hconvert.
    destruct (classification_kind classification) as [kind |] eqn:Hkind;
      inversion Hconvert; subst; split; reflexivity.
  Qed.

  Theorem classification_with_blank_evidence_yields_invalid_disposition :
    forall classification disposition,
    classification_to_disposition classification 0 = Some disposition ->
    disposition_valid disposition = false.
  Proof.
    intros classification disposition Hconvert.
    unfold classification_to_disposition in Hconvert.
    destruct (classification_kind classification) as [kind |] eqn:Hkind;
      inversion Hconvert; subst.
    unfold disposition_valid, valid_evidence_id. simpl.
    rewrite andb_false_r. reflexivity.
  Qed.

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

  Definition disposition_rule_ids
      (dispositions : list RejectedRuleDisposition) : list RuleId :=
    map disposition_rule_id dispositions.

  Definition invalid_disposition_entries
      (dispositions : list RejectedRuleDisposition)
      : list RejectedRuleDisposition :=
    filter (fun disposition => negb (disposition_valid disposition)) dispositions.

  Fixpoint duplicate_rule_ids
      (dispositions : list RejectedRuleDisposition) : list RuleId :=
    match dispositions with
    | [] => []
    | disposition :: rest =>
        let rule := disposition_rule_id disposition in
        if rule_member rule (disposition_rule_ids rest)
        then rule :: duplicate_rule_ids rest
        else duplicate_rule_ids rest
    end.

  Definition invalid_disposition_count
    (dispositions : list RejectedRuleDisposition) : nat :=
    length (invalid_disposition_entries dispositions)
    + length (duplicate_rule_ids dispositions).

  Inductive RejectionCoverageEvidence : Type :=
    | AllRulesLowered
    | CoveredRejectedRules :
        list RejectedRuleDisposition -> RejectionCoverageEvidence.

  Definition covered_rule_ids (evidence : RejectionCoverageEvidence)
      : list RuleId :=
    match evidence with
    | AllRulesLowered => []
    | CoveredRejectedRules dispositions => disposition_rule_ids dispositions
    end.

  Definition uncovered_rejection_ids
      (rejected covered : list RuleId) : list RuleId :=
    filter (fun rule => negb (rule_member rule covered)) rejected.

  Definition extraneous_disposition_ids
      (rejected covered : list RuleId) : list RuleId :=
    filter (fun rule => negb (rule_member rule rejected)) covered.

  Definition covered_rejections_exact
      (rejected : list RuleId)
      (dispositions : list RejectedRuleDisposition) : bool :=
    let covered := disposition_rule_ids dispositions in
    all_members_of rejected covered && all_members_of covered rejected.

  Definition coverage_evidence_exact
      (evidence : RejectionCoverageEvidence)
      (rejected : list RuleId) : bool :=
    match evidence with
    | AllRulesLowered =>
        match rejected with
        | [] => true
        | _ :: _ => false
        end
    | CoveredRejectedRules dispositions =>
        covered_rejections_exact rejected dispositions
        && Nat.eqb (invalid_disposition_count dispositions) 0
    end.

  Definition coverage_state_from_evidence
      (audit : bool)
      (evidence : RejectionCoverageEvidence)
      (rejected : list RuleId) : CoverageState :=
    let covered := covered_rule_ids evidence in
    let invalid :=
      match evidence with
      | AllRulesLowered => 0
      | CoveredRejectedRules dispositions =>
          invalid_disposition_count dispositions
      end in
    {|
      coverage_audit_passed := audit;
      uncovered_rejections := length (uncovered_rejection_ids rejected covered);
      extraneous_dispositions := length (extraneous_disposition_ids rejected covered);
      invalid_dispositions := invalid;
      uncovered_guard_obligations := 0;
      extraneous_guard_dispositions := 0;
      invalid_guard_dispositions := 0
    |}.

  Lemma inhabited_list_has_nonzero_length : forall (A : Type) (xs : list A) x,
    In x xs -> length xs <> 0.
  Proof.
    intros A xs x Hin Hlen.
    apply length_zero_iff_nil in Hlen.
    subst xs. contradiction.
  Qed.

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

  Theorem covered_rejections_exact_iff_same_rule_set :
    forall rejected dispositions,
    covered_rejections_exact rejected dispositions = true
    <-> forall rule,
      In rule rejected <-> In rule (disposition_rule_ids dispositions).
  Proof.
    intros rejected dispositions. unfold covered_rejections_exact.
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

  Theorem covered_rejection_omits_no_rejected_rule :
    forall rejected dispositions rule,
    covered_rejections_exact rejected dispositions = true ->
    In rule rejected ->
    In rule (disposition_rule_ids dispositions).
  Proof.
    intros rejected dispositions rule Hexact Hin.
    destruct (covered_rejections_exact_iff_same_rule_set rejected dispositions)
      as [Hto_set _].
    specialize (Hto_set Hexact rule).
    apply Hto_set. exact Hin.
  Qed.

  Theorem covered_rejection_has_no_stale_rule :
    forall rejected dispositions rule,
    covered_rejections_exact rejected dispositions = true ->
    In rule (disposition_rule_ids dispositions) ->
    In rule rejected.
  Proof.
    intros rejected dispositions rule Hexact Hin.
    destruct (covered_rejections_exact_iff_same_rule_set rejected dispositions)
      as [Hto_set _].
    specialize (Hto_set Hexact rule).
    apply Hto_set. exact Hin.
  Qed.

  Theorem omitted_rejected_rule_blocks_exact_coverage :
    forall rejected dispositions rule,
    In rule rejected ->
    ~ In rule (disposition_rule_ids dispositions) ->
    covered_rejections_exact rejected dispositions = false.
  Proof.
    intros rejected dispositions rule Hrejected Homitted.
    destruct (covered_rejections_exact rejected dispositions) eqn:Hexact.
    - apply covered_rejection_omits_no_rejected_rule with
        (rule := rule) in Hexact.
      + contradiction.
      + exact Hrejected.
    - reflexivity.
  Qed.

  Theorem stale_disposition_blocks_exact_coverage :
    forall rejected dispositions rule,
    In rule (disposition_rule_ids dispositions) ->
    ~ In rule rejected ->
    covered_rejections_exact rejected dispositions = false.
  Proof.
    intros rejected dispositions rule Hcovered Hstale.
    destruct (covered_rejections_exact rejected dispositions) eqn:Hexact.
    - apply covered_rejection_has_no_stale_rule with
        (rule := rule) in Hexact.
      + contradiction.
      + exact Hcovered.
    - reflexivity.
  Qed.

  Lemma omitted_rule_appears_in_uncovered :
    forall rejected covered rule,
    In rule rejected ->
    ~ In rule covered ->
    In rule (uncovered_rejection_ids rejected covered).
  Proof.
    intros rejected covered rule Hrejected Homitted.
    unfold uncovered_rejection_ids.
    apply filter_In. split.
    - exact Hrejected.
    - apply negb_true_iff.
      apply rule_member_false_iff.
      exact Homitted.
  Qed.

  Lemma stale_rule_appears_in_extraneous :
    forall rejected covered rule,
    In rule covered ->
    ~ In rule rejected ->
    In rule (extraneous_disposition_ids rejected covered).
  Proof.
    intros rejected covered rule Hcovered Hstale.
    unfold extraneous_disposition_ids.
    apply filter_In. split.
    - exact Hcovered.
    - apply negb_true_iff.
      apply rule_member_false_iff.
      exact Hstale.
  Qed.

  Lemma invalid_disposition_appears :
    forall dispositions disposition,
    In disposition dispositions ->
    disposition_valid disposition = false ->
    In disposition (invalid_disposition_entries dispositions).
  Proof.
    intros dispositions disposition Hin Hinvalid.
    unfold invalid_disposition_entries.
    apply filter_In. split.
    - exact Hin.
    - rewrite Hinvalid. reflexivity.
  Qed.

  Lemma invalid_disposition_count_nonzero_if_invalid :
    forall dispositions disposition,
    In disposition dispositions ->
    disposition_valid disposition = false ->
    invalid_disposition_count dispositions <> 0.
  Proof.
    intros dispositions disposition Hin Hinvalid.
    unfold invalid_disposition_count.
    assert (Hlen : length (invalid_disposition_entries dispositions) <> 0).
    {
      apply inhabited_list_has_nonzero_length with
        (x := disposition).
      apply invalid_disposition_appears; assumption.
    }
    lia.
  Qed.

  Lemma duplicate_head_appears_in_duplicate_rule_ids :
    forall disposition rest,
    In (disposition_rule_id disposition) (disposition_rule_ids rest) ->
    In (disposition_rule_id disposition)
      (duplicate_rule_ids (disposition :: rest)).
  Proof.
    intros disposition rest Hdup. simpl.
    apply rule_member_iff in Hdup. rewrite Hdup.
    simpl. left. reflexivity.
  Qed.

  Lemma invalid_disposition_count_nonzero_if_duplicate_head :
    forall disposition rest,
    In (disposition_rule_id disposition) (disposition_rule_ids rest) ->
    invalid_disposition_count (disposition :: rest) <> 0.
  Proof.
    intros disposition rest Hdup.
    unfold invalid_disposition_count.
    assert (Hlen : length (duplicate_rule_ids (disposition :: rest)) <> 0).
    {
      apply inhabited_list_has_nonzero_length with
        (x := disposition_rule_id disposition).
      apply duplicate_head_appears_in_duplicate_rule_ids.
      exact Hdup.
    }
    lia.
  Qed.

  Theorem invalid_disposition_blocks_exact_coverage :
    forall rejected dispositions disposition,
    In disposition dispositions ->
    disposition_valid disposition = false ->
    coverage_evidence_exact (CoveredRejectedRules dispositions) rejected = false.
  Proof.
    intros rejected dispositions disposition Hin Hinvalid.
    unfold coverage_evidence_exact.
    assert (Hnonzero :
      invalid_disposition_count dispositions <> 0).
    {
      apply invalid_disposition_count_nonzero_if_invalid with
        (disposition := disposition); assumption.
    }
    assert (Hcount :
      Nat.eqb (invalid_disposition_count dispositions) 0 = false).
    { rewrite Nat.eqb_neq. exact Hnonzero. }
    rewrite Hcount.
    destruct (covered_rejections_exact rejected dispositions); reflexivity.
  Qed.

  Theorem duplicate_disposition_blocks_exact_coverage :
    forall rejected disposition rest,
    In (disposition_rule_id disposition) (disposition_rule_ids rest) ->
    coverage_evidence_exact
      (CoveredRejectedRules (disposition :: rest)) rejected = false.
  Proof.
    intros rejected disposition rest Hdup.
    unfold coverage_evidence_exact.
    assert (Hnonzero :
      invalid_disposition_count (disposition :: rest) <> 0).
    {
      apply invalid_disposition_count_nonzero_if_duplicate_head.
      exact Hdup.
    }
    assert (Hcount :
      Nat.eqb (invalid_disposition_count (disposition :: rest)) 0 = false).
    { rewrite Nat.eqb_neq. exact Hnonzero. }
    rewrite Hcount.
    destruct (covered_rejections_exact rejected (disposition :: rest));
      reflexivity.
  Qed.

  Theorem omitted_rejected_rule_blocks_default_backend :
    forall proofs oracle artifact fairness audit rejected dispositions rule diagnostics,
    In rule rejected ->
    ~ In rule (disposition_rule_ids dispositions) ->
    default_backend_gate proofs oracle artifact fairness
      (coverage_state_from_evidence audit (CoveredRejectedRules dispositions) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit rejected dispositions rule diagnostics
      Hrejected Homitted.
    unfold coverage_state_from_evidence. simpl.
    apply uncovered_rejection_blocks_default_backend.
    apply inhabited_list_has_nonzero_length with (x := rule).
    apply omitted_rule_appears_in_uncovered; assumption.
  Qed.

  Theorem stale_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit rejected dispositions rule diagnostics,
    In rule (disposition_rule_ids dispositions) ->
    ~ In rule rejected ->
    default_backend_gate proofs oracle artifact fairness
      (coverage_state_from_evidence audit (CoveredRejectedRules dispositions) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit rejected dispositions rule diagnostics
      Hcovered Hstale.
    unfold coverage_state_from_evidence. simpl.
    apply extraneous_delegation_blocks_default_backend.
    apply inhabited_list_has_nonzero_length with (x := rule).
    apply stale_rule_appears_in_extraneous; assumption.
  Qed.

  Theorem inauditable_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit rejected dispositions disposition diagnostics,
    In disposition dispositions ->
    disposition_valid disposition = false ->
    default_backend_gate proofs oracle artifact fairness
      (coverage_state_from_evidence audit (CoveredRejectedRules dispositions) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit rejected dispositions disposition diagnostics
      Hin Hinvalid.
    unfold coverage_state_from_evidence. simpl.
    apply invalid_disposition_blocks_default_backend.
    apply invalid_disposition_count_nonzero_if_invalid with
      (disposition := disposition); assumption.
  Qed.

  Theorem duplicate_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit rejected disposition rest diagnostics,
    In (disposition_rule_id disposition) (disposition_rule_ids rest) ->
    default_backend_gate proofs oracle artifact fairness
      (coverage_state_from_evidence audit
        (CoveredRejectedRules (disposition :: rest)) rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit rejected disposition rest diagnostics Hdup.
    unfold coverage_state_from_evidence. simpl.
    apply invalid_disposition_blocks_default_backend.
    apply invalid_disposition_count_nonzero_if_duplicate_head.
    exact Hdup.
  Qed.

  Theorem all_rules_lowered_blocks_any_rejection :
    forall proofs oracle artifact fairness audit rejected rule diagnostics,
    In rule rejected ->
    default_backend_gate proofs oracle artifact fairness
      (coverage_state_from_evidence audit AllRulesLowered rejected)
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit rejected rule diagnostics Hrejected.
    unfold coverage_state_from_evidence. simpl.
    apply uncovered_rejection_blocks_default_backend.
    apply inhabited_list_has_nonzero_length with (x := rule).
    apply omitted_rule_appears_in_uncovered.
    - exact Hrejected.
    - intros Hempty. inversion Hempty.
  Qed.

End RhoRejectedCoverage.
