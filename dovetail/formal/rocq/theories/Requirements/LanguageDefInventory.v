(*
 * LanguageDefInventory: proof layer for the executable LanguageDef inventory
 * audit.
 *
 * The companion Rust test audits actual in-repo `language!` macro bodies and
 * generated Datalog relation families. This Rocq file models the checked
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

  Definition class2_collection_surface : list RewriteRequirement := [
    ReqCollectionPattern
  ].

  Definition class2_map_surface : list RewriteRequirement := [
    ReqCollectionPattern;
    ReqMapPattern
  ].

  Definition class3_binder_collection_surface : list RewriteRequirement := [
    ReqCollectionPattern;
    ReqZipPattern;
    ReqBinderPattern
  ].

  Definition guarded_rho_surface : list RewriteRequirement := [
    ReqBehavioralGuard;
    ReqSyntheticInjectionGuard;
    ReqEnvRelationPremise;
    ReqCollectionPattern;
    ReqBinderPattern;
    ReqRhoCommHandlerContract;
    ReqRhoResourceGuardContract
  ].

  Definition refinement_surface : list RewriteRequirement := [
    ReqEnvRelationPremise
  ].

  Definition current_language_inventory : list LanguageInventory := [
    {| inventory_name := "calculator"; inventory_requirements := arithmetic_rewrite_surface ++ collection_rewrite_surface |};
    {| inventory_name := "rhocalc"; inventory_requirements := process_rewrite_surface ++ arithmetic_rewrite_surface |};
    {| inventory_name := "ambient"; inventory_requirements := process_rewrite_surface |};
    {| inventory_name := "lambda"; inventory_requirements := binder_rewrite_surface |};
    {| inventory_name := "appsubst"; inventory_requirements := binder_rewrite_surface |};
    {| inventory_name := "guardedrho"; inventory_requirements := guarded_rho_surface |};
    {| inventory_name := "ledtest"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "optsmoke"; inventory_requirements := ReqFoldNativeHandler :: class2_collection_surface |};
    {| inventory_name := "class2smoke"; inventory_requirements := class2_collection_surface |};
    {| inventory_name := "class2hashmapsmoke"; inventory_requirements := class2_map_surface |};
    {| inventory_name := "class2multi"; inventory_requirements := class2_collection_surface |};
    {| inventory_name := "class2optsmoke"; inventory_requirements := class2_collection_surface |};
    {| inventory_name := "class3multi"; inventory_requirements := class3_binder_collection_surface |};
    {| inventory_name := "class3opt"; inventory_requirements := class3_binder_collection_surface |};
    {| inventory_name := "basemath"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "extmath"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "importedmath"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "mixedmath"; inventory_requirements := arithmetic_rewrite_surface |};
    {| inventory_name := "refinementsmoke"; inventory_requirements := refinement_surface |};
    (* SwapDemo (Epic 4 R-5 σ-injection demo language): a single directional base
       rewrite `Swap(x, y) ~> Pair(y, x)` — no equations, binders, collections, or
       premises — so it classifies to exactly {DirectionalRewrite}. Its requirement
       is already covered (every arithmetic/process language carries it), so all
       coverage proofs below hold unchanged. *)
    {| inventory_name := "swapdemo"; inventory_requirements := [ ReqDirectionalRewrite ] |}
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

  Theorem every_current_language_has_requirements : forall inv,
    In inv current_language_inventory ->
    inventory_requirements inv <> [].
  Proof.
    intros inv Hinv.
    repeat
      (destruct Hinv as [Hinv | Hinv];
       [subst; simpl; discriminate |]).
    contradiction.
  Qed.

End LanguageDefInventory.
