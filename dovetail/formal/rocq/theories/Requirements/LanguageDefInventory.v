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

  (* GuardOptSmoke (task #14): a guard-inside-optional-group smoke grammar. The
     `?g:Guard` param (a `TermParam::GuardBody`) contributes BehavioralGuard +
     RhoResourceGuardContract; the `![{ k }]` native fold contributes
     FoldNativeHandler; the `logic { relation ok(Proc) }` contributes
     EnvRelationPremise; ExactContentKey is universal. This is exactly the
     classify_language surface the executable audit computes for it. *)
  Definition guardopt_smoke_surface : list RewriteRequirement := [
    ReqBehavioralGuard;
    ReqRhoResourceGuardContract;
    ReqFoldNativeHandler;
    ReqEnvRelationPremise;
    ReqExactContentKey
  ].

  Definition current_language_inventory : list LanguageInventory := [
    {| inventory_name := "calculator"; inventory_requirements := arithmetic_rewrite_surface ++ collection_rewrite_surface |};
    {| inventory_name := "rholang"; inventory_requirements := process_rewrite_surface ++ arithmetic_rewrite_surface |};
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
    {| inventory_name := "swapdemo"; inventory_requirements := [ ReqDirectionalRewrite ] |};
    {| inventory_name := "guardoptsmoke"; inventory_requirements := guardopt_smoke_surface |};
    (* rho_net Dovetail->Rho firing demo languages (Epic 4). Task #11 (2026-07-26) relocated
       every DEMONSTRATION grammar out of the production tree: they now live in
       `languages/tests/definitions/*demo.rs`, declared `options { hosted_in: ... }`. The
       inventory is UNAFFECTED by the move -- `dovetail/tests/language_inventory.rs` scans
       BOTH `languages/src` and `languages/tests/definitions`, precisely so relocation can
       never drop a language out of the formal requirements coverage.
       Each is a real reduction language, so it is inventoried fail-closed (it is NOT a
       `parse_only` fixture). Requirements mirror the taxonomy that
       `dovetail/tests/language_inventory.rs::classify_source` derives from each
       `language!` source; every constructor is a member of
       `current_mettail_rewrite_requirements` (MeTTaILRewriteCoverage.v) and is discharged
       by `every_requirement_constructor_is_covered` below. *)
    {| inventory_name := "acdemo"; inventory_requirements := [ ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite ] |};
    {| inventory_name := "acbagdemo"; inventory_requirements := [ ReqBehavioralGuard; ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite; ReqEquation; ReqSyntheticInjectionGuard ] |};
    {| inventory_name := "nlacdemo"; inventory_requirements := [ ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite ] |};
    {| inventory_name := "ambdemo"; inventory_requirements := [ ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite ] |};
    {| inventory_name := "ambnewdemo"; inventory_requirements := [ ReqBinderPattern; ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite ] |};
    {| inventory_name := "inoutdemo"; inventory_requirements := [ ReqBehavioralGuard; ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite; ReqSyntheticInjectionGuard ] |};
    {| inventory_name := "commdemo"; inventory_requirements := [ ReqBinderPattern; ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite; ReqRhoCommHandlerContract; ReqSubstitutionPattern ] |};
    {| inventory_name := "ctxdemo"; inventory_requirements := [ ReqBehavioralGuard; ReqCongruencePremise; ReqDirectionalRewrite; ReqSyntheticInjectionGuard ] |};
    {| inventory_name := "bicongdemo"; inventory_requirements := [ ReqCongruencePremise; ReqDirectionalRewrite ] |};
    {| inventory_name := "lambdademo"; inventory_requirements := [ ReqBehavioralGuard; ReqBinderPattern; ReqDirectionalRewrite; ReqSubstitutionPattern; ReqSyntheticInjectionGuard ] |};
    {| inventory_name := "nativedemo"; inventory_requirements := [ ReqBehavioralGuard; ReqDirectionalRewrite; ReqFoldNativeHandler; ReqSyntheticInjectionGuard ] |};
    {| inventory_name := "nativefolddemo"; inventory_requirements := [ ReqBehavioralGuard; ReqDirectionalRewrite; ReqFoldNativeHandler; ReqSyntheticInjectionGuard ] |};
    (* GSLT omnibus conformance specs (2026-07-27). The four theories transcribed
       from the omnibus paper -- Json (L1), Monoid (L2), Turing (L9), Pi (L11) --
       are PRODUCTION specs (USER ruling), so they moved from
       `languages/tests/omnibus_*.rs` to `languages/src/{json,monoid,pi,turing}.rs`.
       That relocation is what brings them into the executable audit's discovery
       roots (`languages/src` + `languages/tests/definitions`): a top-level
       `languages/tests/*.rs` file is NOT scanned, so until now these four real
       reduction languages sat outside the formal requirements coverage entirely.
       Inventorying them here CLOSES that gap; it is not bookkeeping for the move.

       ★ Requirement derivation. Every other entry above was read off
       `dovetail/tests/language_inventory.rs::classify_source`, a TEXTUAL scan of
       the whole source file. These four carry long clause-by-clause conformance
       headers that quote OTHER languages' constructs, and that scan could not tell
       a quotation from a declaration: it reported ReqRhoCommHandlerContract for Json
       (the header cites Rholang's `POutput` idiom at src/json.rs:107), ReqFreshnessPremise
       for all four (their markdown `# ` headings match the `"# "` needle), and
       ReqCongruencePremise for Turing (a markdown table row in its header, plus the
       `map_err(|_| ())` closure in its UInt32 literal action, both match the `"| "`
       needle). Recording those would have been false, so the lists below are the
       STRUCTURAL requirements -- what
       `ast/tests/dovetail_language_inventory.rs::classify_language` derives from the
       parsed `LanguageDef`.

       That textual classifier has since been REPAIRED (commit 9be969a4): it now
       classifies `declarations_only(source)`, with every comment, string and
       character literal blanked, and its congruence and guard needles were made
       precise (a `~>` on the premise side of a statement; a `?<name>:Guard` slot).
       Measured over the corpus, that removed 34 false (language, requirement) pairs
       and no true one, and the six false positives named above are gone: Json,
       Monoid and Turing no longer report a freshness premise, Turing no longer
       reports a congruence premise, and Json no longer reports a Rho COMM handler
       contract or a substitution pattern. Pi's freshness premise SURVIVES, because
       it is real (`| x # ...rest` in ScopeExt). The two classifiers therefore now
       agree on these four modulo the textual side's deliberately coarse carrier
       needles (`Vec<` in a native type declaration counts as a collection).

       No test compares an entry's requirement list against either classifier (both
       check name-set equality, per-language non-emptiness, and constructor
       coverage), and every constructor below is a member of
       `current_mettail_rewrite_requirements`, so the coverage proofs discharge
       unchanged. *)
    (* Json (L1) -- rung one: types + terms only, `equations {}` / `rewrites {}` both
       empty. Its `JArr`/`JObj` arity split carries an ordered `Vec(...)` slot. *)
    {| inventory_name := "json"; inventory_requirements := [ ReqCollectionPattern; ReqExactContentKey ] |};
    (* Monoid (L2) -- rung two: Assoc/UnitL/UnitR and no rewrites. *)
    {| inventory_name := "monoid"; inventory_requirements := [ ReqEquation; ReqExactContentKey ] |};
    (* Pi (L11) -- the pi-calculus: HashBag parallel, `^x.` restriction and input
       binders, the freshness-premised ScopeExt equation, the substituting Comm
       rewrite, and the ParCong/NewCong congruences. *)
    {| inventory_name := "pi"; inventory_requirements := [ ReqBinderPattern; ReqCollectionPattern; ReqCongruencePremise; ReqDirectionalRewrite; ReqEquation; ReqExactContentKey; ReqFreshnessPremise; ReqSubstitutionPattern ] |};
    (* Turing (L9) -- the `Vec(Sym)` zipper tape, the `shift_right` native fold, and
       the two unpremised transition-table rewrites. *)
    {| inventory_name := "turing"; inventory_requirements := [ ReqCollectionPattern; ReqDirectionalRewrite; ReqExactContentKey; ReqFoldNativeHandler ] |};

    (* ── Definitions in a TOP-LEVEL `languages/tests/*.rs` (2026-07-27) ────────────

       The relocation note above says a top-level `languages/tests/*.rs` file is NOT
       scanned. That was a HOLE, not a property: the executable audits enumerated two
       sub-directories, so a `language!` written anywhere else in the package was
       audited by neither and its requirements were recorded nowhere, with every test
       green. Pi and Turing had just been rescued from it by being moved; three more
       definitions were still sitting in it.

       Both audits now root at the `languages` PACKAGE, and each additionally proves
       (`language_declarations_cannot_hide_outside_the_scanned_roots`) that no
       `language!` anywhere in the repository lies outside the files it reads. The
       three entries below are what that widening exposed. Two more of the same shape
       were exposed with it -- X2Base/X2Look/X2Teeth in
       `languages/tests/x2_lookahead_bracket_probe.rs` -- and are NOT inventoried:
       they are lookahead PARSE probes with no equations, rewrites, logic, guards,
       folds, or eval bodies, so they now declare `options { parse_only: true }`,
       which the anti-loophole guard checks mechanically (`has_reduction_semantics`
       must be false for a parse_only language, and is).

       All three below classify identically: a `step` rule whose `![…]` action is a
       native fold, hence DirectionalRewrite + FoldNativeHandler, plus the universal
       ExactContentKey. Every constructor is already in
       `current_mettail_rewrite_requirements`, so the coverage proofs are unaffected. *)

    (* L9FltToy -- the L9-4 gate: the `*flt` guest-body capture (an `FltOpen…` opener
       and an `FltClose…` closer) across three delimiter forms, with
       `AddNum . … ![a + b] step` alongside. Its reduction semantics were outside
       formal coverage until the roots widened. *)
    {| inventory_name := "l9flttoy"; inventory_requirements := [ ReqDirectionalRewrite; ReqFoldNativeHandler; ReqExactContentKey ] |};
    (* L9ModalToy -- the L9-3 gate: token-kind capture (`v@Tok`) mid-rule and leading,
       over the modal (backtick guest mode) lexer path. Same `step` rule, same gap. *)
    {| inventory_name := "l9modaltoy"; inventory_requirements := [ ReqDirectionalRewrite; ReqFoldNativeHandler; ReqExactContentKey ] |};
    (* DiscoveryCanary -- `languages/tests/inventory_discovery_canary.rs`, the standing
       witness that a definition in a top-level test file is discovered. It is
       inventoried like any other reduction language precisely so that a future
       narrowing of the discovery roots fails HERE, loudly, instead of silently
       dropping some real language's coverage. *)
    {| inventory_name := "discoverycanary"; inventory_requirements := [ ReqDirectionalRewrite; ReqFoldNativeHandler; ReqExactContentKey ] |}
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
