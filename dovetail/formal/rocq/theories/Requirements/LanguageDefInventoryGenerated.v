(*
 * LanguageDefInventoryGenerated: the MECHANICALLY DERIVED half of the
 * LanguageDef inventory.
 *
 * AUTO-GENERATED — do not edit. Regenerate with:
 *
 *     METTAIL_BLESS=1 cargo test -p dovetail --test language_inventory
 *
 * Produced by `dovetail/tests/language_inventory.rs`, which scans the
 * `language!` declarations under the manifest-declared roots
 * ([package.metadata.mettail] language_roots) and classifies each one into the
 * Dovetail rewrite-requirement taxonomy.
 *
 * This file carries NO proof and NO hand-written judgement; it is data. The formal
 * content that consumes it — the inventory record, the requirement surfaces, and
 * the coverage theorems — stays in LanguageDefInventory.v, which imports this.
 *
 * Its COMPILATION is the load-bearing check: a language carrying a requirement the
 * taxonomy does not yet have emits a constructor name that does not exist, and this
 * file stops compiling until MeTTaILRewriteCoverage.v is extended.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import String.

From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.

Import ListNotations.
Open Scope string_scope.

(* One entry per production `language!` declaration: its inventory name paired with
   the requirements classified from its source. Sorted by name, so the file is a
   function of the declarations alone and never of scan order. *)
Definition generated_language_inventory : list (string * list RewriteRequirement) := [
  ("acbagdemo", [ReqEquation; ReqDirectionalRewrite; ReqCollectionPattern]);
  ("acdemo", [ReqDirectionalRewrite; ReqCollectionPattern]);
  ("additiveinertnesscanary", [ReqDirectionalRewrite]);
  ("ambdemo", [ReqDirectionalRewrite; ReqCollectionPattern]);
  ("ambient", [ReqEquation; ReqDirectionalRewrite; ReqCongruencePremise; ReqFreshnessPremise; ReqCollectionPattern; ReqBinderPattern]);
  ("ambnewdemo", [ReqDirectionalRewrite; ReqCollectionPattern; ReqBinderPattern]);
  ("appsubst", [ReqDirectionalRewrite; ReqCongruencePremise; ReqBinderPattern; ReqSubstitutionPattern]);
  ("basemath", [ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler]);
  ("bicongdemo", [ReqDirectionalRewrite; ReqCongruencePremise]);
  ("binderlawdemo", [ReqEquation; ReqBinderPattern]);
  ("calculator", [ReqEquation; ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler; ReqCollectionPattern; ReqMapPattern; ReqSubstitutionPattern]);
  ("class2hashmapsmoke", [ReqCollectionPattern; ReqMapPattern]);
  ("class2multi", [ReqCollectionPattern]);
  ("class2optsmoke", [ReqCollectionPattern]);
  ("class2smoke", [ReqCollectionPattern]);
  ("class3multi", [ReqCollectionPattern; ReqZipPattern; ReqBinderPattern]);
  ("class3opt", [ReqCollectionPattern; ReqZipPattern; ReqBinderPattern; ReqRhoCommHandlerContract]);
  ("commdemo", [ReqDirectionalRewrite; ReqCollectionPattern; ReqBinderPattern; ReqSubstitutionPattern; ReqRhoCommHandlerContract]);
  ("congruencelanedemo", [ReqDirectionalRewrite; ReqCongruencePremise]);
  ("ctxdemo", [ReqDirectionalRewrite; ReqCongruencePremise]);
  ("discoverycanary", [ReqFoldNativeHandler]);
  ("extmath", [ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler]);
  ("guardedrho", [ReqEnvRelationPremise; ReqBehavioralGuard; ReqSyntheticInjectionGuard; ReqCollectionPattern; ReqBinderPattern; ReqRhoCommHandlerContract; ReqRhoResourceGuardContract]);
  ("guardoptsmoke", [ReqEnvRelationPremise; ReqBehavioralGuard; ReqSyntheticInjectionGuard; ReqCollectionPattern]);
  ("identparamtoy", [ReqFoldNativeHandler; ReqCollectionPattern]);
  ("importedmath", [ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler]);
  ("inoutdemo", [ReqDirectionalRewrite; ReqCollectionPattern]);
  ("json", [ReqCollectionPattern]);
  ("l9flttoy", [ReqFoldNativeHandler; ReqSubstitutionPattern]);
  ("l9modaltoy", [ReqFoldNativeHandler; ReqSubstitutionPattern]);
  ("lambda", [ReqDirectionalRewrite; ReqCongruencePremise; ReqBinderPattern; ReqSubstitutionPattern]);
  ("lambdademo", [ReqDirectionalRewrite; ReqBinderPattern; ReqSubstitutionPattern]);
  ("ledtest", [ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler]);
  ("mapparamrefusaldemo", [ReqFoldNativeHandler; ReqCollectionPattern; ReqMapPattern]);
  ("mixedmath", [ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler]);
  ("monoid", [ReqEquation]);
  ("nativedemo", [ReqFoldNativeHandler]);
  ("nativefolddemo", [ReqFoldNativeHandler]);
  ("nlacdemo", [ReqDirectionalRewrite; ReqCollectionPattern]);
  ("optsmoke", [ReqFoldNativeHandler; ReqCollectionPattern]);
  ("pi", [ReqEquation; ReqDirectionalRewrite; ReqCongruencePremise; ReqFreshnessPremise; ReqCollectionPattern; ReqBinderPattern; ReqSubstitutionPattern]);
  ("refinementsmoke", [ReqEnvRelationPremise]);
  ("rholang", [ReqEquation; ReqDirectionalRewrite; ReqCongruencePremise; ReqFoldNativeHandler; ReqFreshnessPremise; ReqEnvRelationPremise; ReqBehavioralGuard; ReqSyntheticInjectionGuard; ReqCollectionPattern; ReqMapPattern; ReqBinderPattern; ReqSubstitutionPattern; ReqRhoCommHandlerContract; ReqRhoResourceGuardContract]);
  ("seqcarrierdemo", [ReqFoldNativeHandler; ReqCollectionPattern]);
  ("swapdemo", [ReqDirectionalRewrite]);
  ("tokentextleafdemo", [ReqFoldNativeHandler; ReqBinderPattern]);
  ("turing", [ReqDirectionalRewrite; ReqFoldNativeHandler; ReqCollectionPattern]);
  ("turingloop", [ReqDirectionalRewrite; ReqFoldNativeHandler; ReqCollectionPattern]);
  ("typeddropdemo", [ReqEquation; ReqFoldNativeHandler; ReqFreshnessPremise; ReqCollectionPattern; ReqBinderPattern])
].
