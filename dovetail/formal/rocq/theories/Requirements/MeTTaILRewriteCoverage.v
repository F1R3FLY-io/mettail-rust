(*
 * MeTTaILRewriteCoverage: Dovetail capability coverage for the current
 * MeTTaIL rewrite surface.
 *
 * This proof is deliberately a requirements taxonomy, not a claim that every
 * future DSL extension is already covered. The covered surface is the current
 * LanguageDef rewrite/equation/fold/guard/pattern shape plus the documented
 * M-RHO/Rho handler contracts. Adding a new requirement class must extend this
 * file and the Rust exhaustiveness audit.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.

Import ListNotations.

Section MeTTaILRewriteCoverage.

  Inductive RewriteRequirement : Type :=
    | ReqEquation
    | ReqDirectionalRewrite
    | ReqCongruencePremise
    | ReqFoldNativeHandler
    | ReqFreshnessPremise
    | ReqEnvRelationPremise
    | ReqForAllPremise
    | ReqBehavioralGuard
    | ReqSyntheticInjectionGuard
    | ReqCollectionPattern
    | ReqMapPattern
    | ReqZipPattern
    | ReqBinderPattern
    | ReqSubstitutionPattern
    | ReqExactContentKey
    | ReqBudgetOverflowReport
    | ReqWeightOrdersNeverPrunes
    | ReqDemandEnumeration
    | ReqAmbiguityPreservation
    | ReqCyclicInsideWeights
    | ReqCyclicEnumerationBoundary
    | ReqRhoCommHandlerContract
    | ReqRhoResourceGuardContract.

  Inductive DovetailCapability : Type :=
    | CapExactEGraphEquality
    | CapRulesAsDataSaturation
    | CapExactLazyExtraction
    | CapInsideWeightClosure
    | CapExactKeyDedup
    | CapExplicitBudgetOverflow
    | CapGuardEvidence
    | CapPatternLowering
    | CapNativeHandlerContract
    | CapRhoHandlerContract
    | CapCycleCutReport.

  Definition covering_capability (r : RewriteRequirement) : DovetailCapability :=
    match r with
    | ReqEquation => CapExactEGraphEquality
    | ReqDirectionalRewrite => CapRulesAsDataSaturation
    | ReqCongruencePremise => CapRulesAsDataSaturation
    | ReqFoldNativeHandler => CapNativeHandlerContract
    | ReqFreshnessPremise => CapGuardEvidence
    | ReqEnvRelationPremise => CapGuardEvidence
    | ReqForAllPremise => CapGuardEvidence
    | ReqBehavioralGuard => CapGuardEvidence
    | ReqSyntheticInjectionGuard => CapGuardEvidence
    | ReqCollectionPattern => CapPatternLowering
    | ReqMapPattern => CapPatternLowering
    | ReqZipPattern => CapPatternLowering
    | ReqBinderPattern => CapPatternLowering
    | ReqSubstitutionPattern => CapPatternLowering
    | ReqExactContentKey => CapExactKeyDedup
    | ReqBudgetOverflowReport => CapExplicitBudgetOverflow
    | ReqWeightOrdersNeverPrunes => CapExactLazyExtraction
    | ReqDemandEnumeration => CapExactLazyExtraction
    | ReqAmbiguityPreservation => CapExactLazyExtraction
    | ReqCyclicInsideWeights => CapInsideWeightClosure
    | ReqCyclicEnumerationBoundary => CapCycleCutReport
    | ReqRhoCommHandlerContract => CapRhoHandlerContract
    | ReqRhoResourceGuardContract => CapRhoHandlerContract
    end.

  Inductive covers : DovetailCapability -> RewriteRequirement -> Prop :=
    | CoversEquation :
        covers CapExactEGraphEquality ReqEquation
    | CoversDirectionalRewrite :
        covers CapRulesAsDataSaturation ReqDirectionalRewrite
    | CoversCongruencePremise :
        covers CapRulesAsDataSaturation ReqCongruencePremise
    | CoversFoldNativeHandler :
        covers CapNativeHandlerContract ReqFoldNativeHandler
    | CoversFreshnessPremise :
        covers CapGuardEvidence ReqFreshnessPremise
    | CoversEnvRelationPremise :
        covers CapGuardEvidence ReqEnvRelationPremise
    | CoversForAllPremise :
        covers CapGuardEvidence ReqForAllPremise
    | CoversBehavioralGuard :
        covers CapGuardEvidence ReqBehavioralGuard
    | CoversSyntheticInjectionGuard :
        covers CapGuardEvidence ReqSyntheticInjectionGuard
    | CoversCollectionPattern :
        covers CapPatternLowering ReqCollectionPattern
    | CoversMapPattern :
        covers CapPatternLowering ReqMapPattern
    | CoversZipPattern :
        covers CapPatternLowering ReqZipPattern
    | CoversBinderPattern :
        covers CapPatternLowering ReqBinderPattern
    | CoversSubstitutionPattern :
        covers CapPatternLowering ReqSubstitutionPattern
    | CoversExactContentKey :
        covers CapExactKeyDedup ReqExactContentKey
    | CoversBudgetOverflowReport :
        covers CapExplicitBudgetOverflow ReqBudgetOverflowReport
    | CoversWeightOrdersNeverPrunes :
        covers CapExactLazyExtraction ReqWeightOrdersNeverPrunes
    | CoversDemandEnumeration :
        covers CapExactLazyExtraction ReqDemandEnumeration
    | CoversAmbiguityPreservation :
        covers CapExactLazyExtraction ReqAmbiguityPreservation
    | CoversCyclicInsideWeights :
        covers CapInsideWeightClosure ReqCyclicInsideWeights
    | CoversCyclicEnumerationBoundary :
        covers CapCycleCutReport ReqCyclicEnumerationBoundary
    | CoversRhoCommHandlerContract :
        covers CapRhoHandlerContract ReqRhoCommHandlerContract
    | CoversRhoResourceGuardContract :
        covers CapRhoHandlerContract ReqRhoResourceGuardContract.

  Theorem covering_capability_sound : forall r,
    covers (covering_capability r) r.
  Proof.
    destruct r; simpl; constructor.
  Qed.

  Definition current_mettail_rewrite_requirements : list RewriteRequirement := [
    ReqEquation;
    ReqDirectionalRewrite;
    ReqCongruencePremise;
    ReqFoldNativeHandler;
    ReqFreshnessPremise;
    ReqEnvRelationPremise;
    ReqForAllPremise;
    ReqBehavioralGuard;
    ReqSyntheticInjectionGuard;
    ReqCollectionPattern;
    ReqMapPattern;
    ReqZipPattern;
    ReqBinderPattern;
    ReqSubstitutionPattern;
    ReqExactContentKey;
    ReqBudgetOverflowReport;
    ReqWeightOrdersNeverPrunes;
    ReqDemandEnumeration;
    ReqAmbiguityPreservation;
    ReqCyclicInsideWeights;
    ReqCyclicEnumerationBoundary;
    ReqRhoCommHandlerContract;
    ReqRhoResourceGuardContract
  ].

  Definition requirement_covered (r : RewriteRequirement) : Prop :=
    exists c, covers c r.

  Theorem every_requirement_constructor_is_covered : forall r,
    requirement_covered r.
  Proof.
    intros r. exists (covering_capability r). apply covering_capability_sound.
  Qed.

  Theorem all_current_mettail_rewrite_requirements_covered : forall r,
    In r current_mettail_rewrite_requirements ->
    requirement_covered r.
  Proof.
    intros r _. apply every_requirement_constructor_is_covered.
  Qed.

  Theorem no_silent_requirement_delegation : forall r,
    In r current_mettail_rewrite_requirements ->
    exists c, c = covering_capability r /\ covers c r.
  Proof.
    intros r _. exists (covering_capability r). split.
    - reflexivity.
    - apply covering_capability_sound.
  Qed.

End MeTTaILRewriteCoverage.
