(*
 * GeneratedReportCompiler: formal model of the macro-generated
 * LanguageDef -> Dovetail report compiler boundary.
 *
 * This file models the supported fragment implemented by
 * `macros/src/gen/runtime/dovetail_report.rs`:
 *   - structural variables/leaves and constructor applications,
 *   - premise-free equations and rewrites,
 *   - congruence premises supplied by e-graph congruence closure,
 *   - fail-closed rejection for collection/map/zip, binder, substitution,
 *     non-congruence side conditions, and non-converged saturation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List Lia.

From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.

Import ListNotations.

Section GeneratedReportCompiler.

  Inductive GeneratedPatternClass : Type :=
    | GPatStructuralVar
    | GPatStructuralApply
    (* The LOWERED associative-commutative bag apply (Ambient PPar's HashBag,
       lowered to a canonical n-ary ENode). Its identity is an exact content key,
       like any structural apply — distinct from the UNLOWERED collection
       metasyntax `GPatCollectionMeta`, which still fails closed. *)
    | GPatAcStructuralApply
    | GPatCollectionMeta
    | GPatMapMeta
    | GPatZipMeta
    | GPatLambdaMeta
    | GPatMultiLambdaMeta
    | GPatSubstMeta
    | GPatMultiSubstMeta.

  Definition pattern_supported (p : GeneratedPatternClass) : bool :=
    match p with
    | GPatStructuralVar => true
    | GPatStructuralApply => true
    | GPatAcStructuralApply => true
    | GPatCollectionMeta => false
    | GPatMapMeta => false
    | GPatZipMeta => false
    | GPatLambdaMeta => false
    | GPatMultiLambdaMeta => false
    | GPatSubstMeta => false
    | GPatMultiSubstMeta => false
    end.

  Definition pattern_requirements
      (p : GeneratedPatternClass) : list RewriteRequirement :=
    match p with
    | GPatStructuralVar => [ReqExactContentKey]
    | GPatStructuralApply => [ReqExactContentKey]
    | GPatAcStructuralApply => [ReqExactContentKey]
    | GPatCollectionMeta => [ReqCollectionPattern]
    | GPatMapMeta => [ReqMapPattern]
    | GPatZipMeta => [ReqZipPattern]
    | GPatLambdaMeta => [ReqBinderPattern]
    | GPatMultiLambdaMeta => [ReqBinderPattern]
    | GPatSubstMeta => [ReqSubstitutionPattern]
    | GPatMultiSubstMeta => [ReqSubstitutionPattern]
    end.

  Theorem supported_patterns_have_only_exact_key_requirement : forall p r,
    pattern_supported p = true ->
    In r (pattern_requirements p) ->
    r = ReqExactContentKey.
  Proof.
    intros p r Hsupported Hin.
    destruct p; simpl in Hsupported, Hin; try discriminate Hsupported;
      destruct Hin as [<- | []]; reflexivity.
  Qed.

  Inductive GeneratedPremiseClass : Type :=
    | GPremCongruence
    | GPremFreshness
    | GPremRelation
    | GPremForAll
    | GPremBehavioralGuard
    | GPremSyntheticInjectionGuard.

  Definition premise_supported (p : GeneratedPremiseClass) : bool :=
    match p with
    | GPremCongruence => true
    | GPremFreshness => false
    | GPremRelation => false
    | GPremForAll => false
    | GPremBehavioralGuard => false
    | GPremSyntheticInjectionGuard => false
    end.

  Definition premise_requirements
      (p : GeneratedPremiseClass) : list RewriteRequirement :=
    match p with
    | GPremCongruence => [ReqCongruencePremise]
    | GPremFreshness => [ReqFreshnessPremise]
    | GPremRelation => [ReqEnvRelationPremise]
    | GPremForAll => [ReqForAllPremise]
    | GPremBehavioralGuard => [ReqBehavioralGuard]
    | GPremSyntheticInjectionGuard => [ReqSyntheticInjectionGuard]
    end.

  Theorem supported_premises_are_only_congruence : forall p r,
    premise_supported p = true ->
    In r (premise_requirements p) ->
    r = ReqCongruencePremise.
  Proof.
    intros p r Hsupported Hin.
    destruct p; simpl in Hsupported, Hin; try discriminate Hsupported;
      destruct Hin as [<- | []]; reflexivity.
  Qed.

  Inductive GeneratedRuleKind : Type :=
    | GEquation
    | GRewrite
    (* A `fold` term rule (Increment 2/3): its LHS is a structural redex pattern, but its
       RHS is NOT a `Pattern -> Pattern` rewrite — it is a native-computed term added to the
       e-graph through the exact-key path by the generated dispatcher. *)
    | GNativeFold.

  Inductive GeneratedRuleDisposition : Type :=
    | LoweredAsDovetailRule
    | SuppliedByEGraphCongruence
    (* The native-fold disposition: lowered as a `NativeRule` whose computed result is added
       through the exact-key path (hence its single requirement is `ReqExactContentKey`). *)
    | NativeFoldLowered
    | RejectedByGeneratedCompiler.

  Record GeneratedRule : Type := {
    generated_rule_kind : GeneratedRuleKind;
    generated_lhs : GeneratedPatternClass;
    generated_rhs : GeneratedPatternClass;
    generated_premises : list GeneratedPremiseClass;
    generated_is_pure_congruence : bool
  }.

  Definition all_premises_supported
      (rule : GeneratedRule) : bool :=
    forallb premise_supported (generated_premises rule).

  Definition rule_structurally_supported
      (rule : GeneratedRule) : bool :=
    pattern_supported (generated_lhs rule) &&
    pattern_supported (generated_rhs rule) &&
    all_premises_supported rule.

  Definition classify_rule
      (rule : GeneratedRule) : GeneratedRuleDisposition :=
    if rule_structurally_supported rule then
      match generated_rule_kind rule with
      | GNativeFold => NativeFoldLowered
      | _ =>
        if generated_is_pure_congruence rule
        then SuppliedByEGraphCongruence
        else LoweredAsDovetailRule
      end
    else RejectedByGeneratedCompiler.

  Definition disposition_is_lowered
      (d : GeneratedRuleDisposition) : bool :=
    match d with
    | LoweredAsDovetailRule => true
    | _ => false
    end.

  Definition disposition_is_congruence
      (d : GeneratedRuleDisposition) : bool :=
    match d with
    | SuppliedByEGraphCongruence => true
    | _ => false
    end.

  Definition disposition_is_native_fold
      (d : GeneratedRuleDisposition) : bool :=
    match d with
    | NativeFoldLowered => true
    | _ => false
    end.

  Definition disposition_is_rejected
      (d : GeneratedRuleDisposition) : bool :=
    match d with
    | RejectedByGeneratedCompiler => true
    | _ => false
    end.

  Definition lowered_rules (rules : list GeneratedRule) : list GeneratedRule :=
    filter (fun rule => disposition_is_lowered (classify_rule rule)) rules.

  Definition congruence_rules
      (rules : list GeneratedRule) : list GeneratedRule :=
    filter (fun rule => disposition_is_congruence (classify_rule rule)) rules.

  Definition rejected_rules (rules : list GeneratedRule) : list GeneratedRule :=
    filter (fun rule => disposition_is_rejected (classify_rule rule)) rules.

  Definition native_fold_rules
      (rules : list GeneratedRule) : list GeneratedRule :=
    filter (fun rule => disposition_is_native_fold (classify_rule rule)) rules.

  Definition generated_rule_requirements
      (rule : GeneratedRule) : list RewriteRequirement :=
    (match generated_rule_kind rule with
     | GEquation => ReqEquation
     | GRewrite => ReqDirectionalRewrite
     (* A native fold's result is added through the exact-key path (no directional pattern
        rewrite); its kind requirement is the exact content key. *)
     | GNativeFold => ReqExactContentKey
     end)
    :: pattern_requirements (generated_lhs rule)
    ++ pattern_requirements (generated_rhs rule)
    ++ flat_map premise_requirements (generated_premises rule).

  Theorem rule_classification_total : forall rule,
    classify_rule rule = LoweredAsDovetailRule \/
    classify_rule rule = SuppliedByEGraphCongruence \/
    classify_rule rule = NativeFoldLowered \/
    classify_rule rule = RejectedByGeneratedCompiler.
  Proof.
    intros rule. unfold classify_rule.
    destruct (rule_structurally_supported rule),
             (generated_rule_kind rule),
             (generated_is_pure_congruence rule);
      auto.
  Qed.

  Theorem lowered_rule_requires_structural_support : forall rule,
    classify_rule rule = LoweredAsDovetailRule ->
    rule_structurally_supported rule = true /\
    generated_is_pure_congruence rule = false.
  Proof.
    intros rule Hclass. unfold classify_rule in Hclass.
    destruct (rule_structurally_supported rule),
             (generated_rule_kind rule),
             (generated_is_pure_congruence rule);
      try discriminate Hclass; split; reflexivity.
  Qed.

  Theorem congruence_rule_requires_structural_support : forall rule,
    classify_rule rule = SuppliedByEGraphCongruence ->
    rule_structurally_supported rule = true /\
    generated_is_pure_congruence rule = true.
  Proof.
    intros rule Hclass. unfold classify_rule in Hclass.
    destruct (rule_structurally_supported rule),
             (generated_rule_kind rule),
             (generated_is_pure_congruence rule);
      try discriminate Hclass; split; reflexivity.
  Qed.

  (* A native-fold rule is dispositioned `NativeFoldLowered` exactly when it is a
     structurally-supported `GNativeFold` (its LHS redex pattern is exact-key lowerable). *)
  Theorem native_fold_lowered_requires_structural_support : forall rule,
    classify_rule rule = NativeFoldLowered ->
    rule_structurally_supported rule = true /\
    generated_rule_kind rule = GNativeFold.
  Proof.
    intros rule Hclass. unfold classify_rule in Hclass.
    destruct (rule_structurally_supported rule),
             (generated_rule_kind rule),
             (generated_is_pure_congruence rule);
      try discriminate Hclass; split; reflexivity.
  Qed.

  (* Design-doc §6: the `NativeFoldLowered` disposition carries the SINGLE requirement
     `ReqExactContentKey`. A structural native fold (redex LHS, structural result RHS, no
     side-condition premises) has every requirement equal to the exact content key — the
     native result is added through the exact-key path, never via a directional pattern
     rewrite or a side-condition the structural saturation cannot model. *)
  Theorem native_fold_requirements_are_exact_key : forall rule r,
    generated_rule_kind rule = GNativeFold ->
    pattern_supported (generated_lhs rule) = true ->
    pattern_supported (generated_rhs rule) = true ->
    generated_premises rule = nil ->
    In r (generated_rule_requirements rule) ->
    r = ReqExactContentKey.
  Proof.
    intros rule r Hkind Hlhs Hrhs Hprem Hin.
    unfold generated_rule_requirements in Hin.
    rewrite Hkind, Hprem in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin].
    - symmetry. exact Heq.
    - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + exact (supported_patterns_have_only_exact_key_requirement
                 (generated_lhs rule) r Hlhs Hin).
      + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * exact (supported_patterns_have_only_exact_key_requirement
                   (generated_rhs rule) r Hrhs Hin).
        * destruct Hin.
  Qed.

  Theorem unsupported_rule_rejects : forall rule,
    rule_structurally_supported rule = false ->
    classify_rule rule = RejectedByGeneratedCompiler.
  Proof.
    intros rule Hunsupported.
    unfold classify_rule. rewrite Hunsupported. reflexivity.
  Qed.

  Theorem classification_count_exact : forall rules,
    length (lowered_rules rules) +
    length (congruence_rules rules) +
    length (native_fold_rules rules) +
    length (rejected_rules rules) =
    length rules.
  Proof.
    induction rules as [| rule rest IH].
    - reflexivity.
    - unfold lowered_rules, congruence_rules, native_fold_rules, rejected_rules in *.
      simpl.
      destruct (classify_rule rule); simpl; lia.
  Qed.

  Theorem lowered_rules_are_from_input : forall rules rule,
    In rule (lowered_rules rules) -> In rule rules.
  Proof.
    intros rules rule Hin.
    unfold lowered_rules in Hin.
    apply filter_In in Hin. exact (proj1 Hin).
  Qed.

  Theorem congruence_rules_are_from_input : forall rules rule,
    In rule (congruence_rules rules) -> In rule rules.
  Proof.
    intros rules rule Hin.
    unfold congruence_rules in Hin.
    apply filter_In in Hin. exact (proj1 Hin).
  Qed.

  Theorem rejected_rules_are_from_input : forall rules rule,
    In rule (rejected_rules rules) -> In rule rules.
  Proof.
    intros rules rule Hin.
    unfold rejected_rules in Hin.
    apply filter_In in Hin. exact (proj1 Hin).
  Qed.

  Theorem native_fold_rules_are_from_input : forall rules rule,
    In rule (native_fold_rules rules) -> In rule rules.
  Proof.
    intros rules rule Hin.
    unfold native_fold_rules in Hin.
    apply filter_In in Hin. exact (proj1 Hin).
  Qed.

  Theorem input_rule_is_classified : forall rules rule,
    In rule rules ->
    In rule (lowered_rules rules) \/
    In rule (congruence_rules rules) \/
    In rule (native_fold_rules rules) \/
    In rule (rejected_rules rules).
  Proof.
    intros rules rule Hin.
    unfold lowered_rules, congruence_rules, native_fold_rules, rejected_rules.
    destruct (classify_rule rule) eqn:Hclass.
    - left. apply filter_In. split; [exact Hin | rewrite Hclass; reflexivity].
    - right. left. apply filter_In. split; [exact Hin | rewrite Hclass; reflexivity].
    - right. right. left. apply filter_In. split; [exact Hin | rewrite Hclass; reflexivity].
    - right. right. right. apply filter_In. split; [exact Hin | rewrite Hclass; reflexivity].
  Qed.

  Theorem lowered_rule_has_no_unsupported_requirements : forall rule req,
    classify_rule rule = LoweredAsDovetailRule ->
    In req (generated_rule_requirements rule) ->
    req = ReqEquation \/
    req = ReqDirectionalRewrite \/
    req = ReqExactContentKey \/
    req = ReqCongruencePremise.
  Proof.
    intros rule req Hclass Hin.
    apply lowered_rule_requires_structural_support in Hclass
      as [Hstructural _].
    unfold rule_structurally_supported in Hstructural.
    repeat rewrite andb_true_iff in Hstructural.
    destruct Hstructural as [[Hlhs Hrhs] Hpremises].
    unfold generated_rule_requirements in Hin.
    simpl in Hin.
    destruct Hin as [Hkind | Hin].
    - subst req. destruct (generated_rule_kind rule);
        [left | right; left | right; right; left]; reflexivity.
    - apply in_app_iff in Hin as [Hlhs_req | Hin].
      + right. right. left.
        eapply supported_patterns_have_only_exact_key_requirement.
        * exact Hlhs.
        * exact Hlhs_req.
      + apply in_app_iff in Hin as [Hrhs_req | Hprem_req].
        * right. right. left.
          eapply supported_patterns_have_only_exact_key_requirement.
          -- exact Hrhs.
          -- exact Hrhs_req.
        * apply in_flat_map in Hprem_req as
            [premise [Hpremise_in Hreq_in]].
          apply forallb_forall with (x := premise) in Hpremises;
            [| exact Hpremise_in].
          right. right. right.
          eapply supported_premises_are_only_congruence.
          -- exact Hpremises.
          -- exact Hreq_in.
  Qed.

  Theorem lowered_rule_requirements_covered : forall rule req,
    classify_rule rule = LoweredAsDovetailRule ->
    In req (generated_rule_requirements rule) ->
    requirement_covered req.
  Proof.
    intros rule req Hclass Hin.
    apply every_requirement_constructor_is_covered.
  Qed.

  Theorem collection_lhs_is_rejected :
    forall kind rhs premises pure,
      classify_rule
        {| generated_rule_kind := kind;
           generated_lhs := GPatCollectionMeta;
           generated_rhs := rhs;
           generated_premises := premises;
           generated_is_pure_congruence := pure |} =
      RejectedByGeneratedCompiler.
  Proof. reflexivity. Qed.

  Theorem binder_lhs_is_rejected :
    forall kind rhs premises pure,
      classify_rule
        {| generated_rule_kind := kind;
           generated_lhs := GPatLambdaMeta;
           generated_rhs := rhs;
           generated_premises := premises;
           generated_is_pure_congruence := pure |} =
      RejectedByGeneratedCompiler.
  Proof. reflexivity. Qed.

  Theorem substitution_lhs_is_rejected :
    forall kind rhs premises pure,
      classify_rule
        {| generated_rule_kind := kind;
           generated_lhs := GPatSubstMeta;
           generated_rhs := rhs;
           generated_premises := premises;
           generated_is_pure_congruence := pure |} =
      RejectedByGeneratedCompiler.
  Proof. reflexivity. Qed.

  Theorem side_condition_premise_is_rejected :
    forall kind lhs rhs premises pure,
      classify_rule
        {| generated_rule_kind := kind;
           generated_lhs := lhs;
           generated_rhs := rhs;
           generated_premises := GPremBehavioralGuard :: premises;
           generated_is_pure_congruence := pure |} =
      RejectedByGeneratedCompiler.
  Proof.
    intros kind lhs rhs premises pure.
    unfold classify_rule, rule_structurally_supported,
      all_premises_supported.
    simpl. destruct (pattern_supported lhs);
      destruct (pattern_supported rhs); reflexivity.
  Qed.

  (* The LOWERED AC bag apply on the LHS is SUPPORTED: a directional rewrite whose
     LHS is `GPatAcStructuralApply`, with a supported (structural-apply) RHS and a
     non-congruence-but-empty premise set, classifies as a lowered Dovetail rule.
     This is the Ambient OpenRule shape (PPar AC redex ~> positional PPar). *)
  Theorem ac_structural_lhs_is_lowered :
    forall kind, kind <> GNativeFold ->
      classify_rule
        {| generated_rule_kind := kind;
           generated_lhs := GPatAcStructuralApply;
           generated_rhs := GPatAcStructuralApply;
           generated_premises := [];
           generated_is_pure_congruence := false |} =
      LoweredAsDovetailRule.
  Proof.
    intros kind Hk. destruct kind; try reflexivity.
    exfalso. apply Hk. reflexivity.
  Qed.

  (* And the AC bag apply carries ONLY the exact-content-key requirement (its
     identity is exact, like any structural apply — no collection/binder/subst
     requirement leaks in). *)
  Theorem ac_structural_requirements_are_exact_key : forall r,
    In r (pattern_requirements GPatAcStructuralApply) ->
    r = ReqExactContentKey.
  Proof.
    intros r Hin. simpl in Hin. destruct Hin as [<- | []]. reflexivity.
  Qed.

End GeneratedReportCompiler.
