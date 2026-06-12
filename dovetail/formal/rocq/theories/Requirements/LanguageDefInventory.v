(*
 * LanguageDefInventory: proof layer for the executable LanguageDef inventory
 * audit.
 *
 * The companion Rust test parses actual in-repo `language!` macro bodies and
 * classifies their rewrite surfaces. This Rocq file models the checked
 * inventory shape and proves that every inventoried requirement is covered by
 * the Dovetail capability taxonomy.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import String.

From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.

Import ListNotations.
Open Scope string_scope.

Section LanguageDefInventory.

  Record LanguageInventory : Type := {
    inventory_name : string;
    inventory_requirements : list RewriteRequirement
  }.

  Definition arithmetic_rewrite_surface : list RewriteRequirement := [
    ReqDirectionalRewrite;
    ReqCongruencePremise;
    ReqFoldNativeHandler;
    ReqExactContentKey;
    ReqBudgetOverflowReport;
    ReqWeightOrdersNeverPrunes;
    ReqDemandEnumeration;
    ReqAmbiguityPreservation
  ].

  Definition process_rewrite_surface : list RewriteRequirement := [
    ReqEquation;
    ReqDirectionalRewrite;
    ReqCongruencePremise;
    ReqFreshnessPremise;
    ReqEnvRelationPremise;
    ReqBehavioralGuard;
    ReqCollectionPattern;
    ReqBinderPattern;
    ReqRhoCommHandlerContract;
    ReqRhoResourceGuardContract;
    ReqCyclicInsideWeights;
    ReqCyclicEnumerationBoundary
  ].

  Definition collection_rewrite_surface : list RewriteRequirement := [
    ReqCollectionPattern;
    ReqMapPattern;
    ReqZipPattern;
    ReqForAllPremise;
    ReqSyntheticInjectionGuard;
    ReqExactContentKey
  ].

  Definition binder_rewrite_surface : list RewriteRequirement := [
    ReqBinderPattern;
    ReqSubstitutionPattern;
    ReqFreshnessPremise;
    ReqDirectionalRewrite;
    ReqCongruencePremise
  ].

  Definition current_language_inventory : list LanguageInventory := [
    {| inventory_name := "calculator"; inventory_requirements := arithmetic_rewrite_surface ++ collection_rewrite_surface |};
    {| inventory_name := "rhocalc"; inventory_requirements := process_rewrite_surface ++ arithmetic_rewrite_surface |};
    {| inventory_name := "ambient"; inventory_requirements := process_rewrite_surface |};
    {| inventory_name := "lambda"; inventory_requirements := binder_rewrite_surface |};
    {| inventory_name := "ledtest"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "composition"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "refinements"; inventory_requirements := ReqEnvRelationPremise :: ReqFoldNativeHandler :: arithmetic_rewrite_surface |}
  ].

  Definition flat_inventory : list RewriteRequirement :=
    flat_map inventory_requirements current_language_inventory.

  Theorem inventoried_requirement_covered : forall inv r,
    In inv current_language_inventory ->
    In r (inventory_requirements inv) ->
    requirement_covered r.
  Proof.
    intros inv r _ _. apply every_requirement_constructor_is_covered.
  Qed.

  Theorem flat_inventory_covered : forall r,
    In r flat_inventory ->
    requirement_covered r.
  Proof.
    intros r Hin. unfold flat_inventory in Hin.
    apply in_flat_map in Hin.
    destruct Hin as [inv [Hinv Hr]].
    eapply inventoried_requirement_covered; eauto.
  Qed.

  Theorem flat_inventory_has_no_silent_delegation : forall r,
    In r flat_inventory ->
    exists c, c = covering_capability r /\ covers c r.
  Proof.
    intros r Hin. exists (covering_capability r). split.
    - reflexivity.
    - apply covering_capability_sound.
  Qed.

End LanguageDefInventory.
