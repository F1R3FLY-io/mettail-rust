(*
 * GeneratedLanguageInstallation: production registry contract for generated
 * MeTTaIL languages installed on the Dovetail -> Rho runtime path.
 *
 * Rust image:
 *   - The `language!` macro constructs a `LanguageDef` directly from the
 *     language specification, then applies composition, validation, and
 *     generated rules before runtime-facing code is emitted.
 *   - Human metadata such as display syntax is not a source of compiler truth.
 *     A production Dovetail/Rho installation must be derived from the same
 *     generated definition identity as the wrapped language.
 *   - A registry entry can expose `RuntimeBackend::RhoMachine` and the
 *     non-default `RuntimeBackend::Dovetail` intermediate only after:
 *       * the Rho plan matches the generated definition,
 *       * the Dovetail compiler matches the generated definition,
 *       * the invocation compiler matches the generated definition,
 *       * the Dovetail report is structurally well formed and complete, and
 *       * the invocation compiler emits an AST-first artifact.
 *   - The legacy Ascent runtime is never exposed by the production registry
 *     entry.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List PeanoNat.

Import ListNotations.

Section GeneratedLanguageInstallation.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive ArtifactBoundary : Type :=
  | SourceText
  | RhoAst
  | RhoBytecode.

  Inductive ExtractionCompleteness : Type :=
  | Complete
  | BoundedByCycleCut.

  Inductive ReportShape : Type :=
  | DovetailReportShape
  | ObservationShape.

  Record RuntimeBackendCapability : Type := {
    capability_backend : Backend;
    capability_is_default : bool
  }.

  Record GeneratedLanguage : Type := {
    generated_definition_id : nat
  }.

  Record RhoPlan : Type := {
    rho_plan_definition_id : nat;
    rho_plan_accepted : bool
  }.

  Record DovetailCompiler : Type := {
    dovetail_compiler_definition_id : nat;
    dovetail_report_available : bool;
    dovetail_report_well_formed : bool;
    dovetail_report_completeness : ExtractionCompleteness
  }.

  Record InvocationCompiler : Type := {
    invocation_compiler_definition_id : nat;
    invocation_total : bool;
    invocation_artifact_boundary : ArtifactBoundary
  }.

  Record ProductionInstallation : Type := {
    installed_language : GeneratedLanguage;
    installed_rho_plan : RhoPlan;
    installed_dovetail_compiler : DovetailCompiler;
    installed_invocation_compiler : InvocationCompiler
  }.

  Definition plan_derived_dovetail_compiler
      (plan : RhoPlan)
      (available well_formed : bool)
      (completeness : ExtractionCompleteness) : DovetailCompiler :=
    {| dovetail_compiler_definition_id := rho_plan_definition_id plan;
       dovetail_report_available := available;
       dovetail_report_well_formed := well_formed;
       dovetail_report_completeness := completeness |}.

  Definition plan_derived_invocation_compiler
      (plan : RhoPlan)
      (total : bool)
      (artifact : ArtifactBoundary) : InvocationCompiler :=
    {| invocation_compiler_definition_id := rho_plan_definition_id plan;
       invocation_total := total;
       invocation_artifact_boundary := artifact |}.

  Definition plan_derived_installation
      (lang : GeneratedLanguage)
      (plan : RhoPlan)
      (available well_formed : bool)
      (completeness : ExtractionCompleteness)
      (total : bool)
      (artifact : ArtifactBoundary) : ProductionInstallation :=
    {| installed_language := lang;
       installed_rho_plan := plan;
       installed_dovetail_compiler :=
         plan_derived_dovetail_compiler plan available well_formed completeness;
       installed_invocation_compiler :=
         plan_derived_invocation_compiler plan total artifact |}.

  Definition backend_eqb (left right : Backend) : bool :=
    match left, right with
    | Ascent, Ascent => true
    | Dovetail, Dovetail => true
    | RhoMachine, RhoMachine => true
    | _, _ => false
    end.

  Definition artifact_is_ast_first (artifact : ArtifactBoundary) : bool :=
    match artifact with
    | RhoAst => true
    | RhoBytecode => true
    | SourceText => false
    end.

  Definition completeness_is_complete
      (status : ExtractionCompleteness) : bool :=
    match status with
    | Complete => true
    | BoundedByCycleCut => false
    end.

  Definition language_definition_id (install : ProductionInstallation) : nat :=
    generated_definition_id (installed_language install).

  Definition rho_plan_matches_language
      (install : ProductionInstallation) : bool :=
    Nat.eqb
      (rho_plan_definition_id (installed_rho_plan install))
      (language_definition_id install).

  Definition dovetail_compiler_matches_language
      (install : ProductionInstallation) : bool :=
    Nat.eqb
      (dovetail_compiler_definition_id
         (installed_dovetail_compiler install))
      (language_definition_id install).

  Definition invocation_compiler_matches_language
      (install : ProductionInstallation) : bool :=
    Nat.eqb
      (invocation_compiler_definition_id
         (installed_invocation_compiler install))
      (language_definition_id install).

  Definition dovetail_report_checked
      (compiler : DovetailCompiler) : bool :=
    dovetail_report_available compiler &&
    dovetail_report_well_formed compiler &&
    completeness_is_complete (dovetail_report_completeness compiler).

  Definition production_installation_ok
      (install : ProductionInstallation) : bool :=
    rho_plan_matches_language install &&
    dovetail_compiler_matches_language install &&
    invocation_compiler_matches_language install &&
    rho_plan_accepted (installed_rho_plan install) &&
    dovetail_report_checked (installed_dovetail_compiler install) &&
    invocation_total (installed_invocation_compiler install) &&
    artifact_is_ast_first
      (invocation_artifact_boundary
         (installed_invocation_compiler install)).

  Definition exposed_capabilities
      (install : ProductionInstallation) : list RuntimeBackendCapability :=
    if production_installation_ok install
    then [{| capability_backend := RhoMachine;
             capability_is_default := true |};
          {| capability_backend := Dovetail;
             capability_is_default := false |}]
    else [].

  Definition capabilities_support
      (capabilities : list RuntimeBackendCapability) (backend : Backend) : bool :=
    existsb
      (fun capability =>
         backend_eqb (capability_backend capability) backend)
      capabilities.

  Definition production_supports
      (install : ProductionInstallation) (backend : Backend) : bool :=
    capabilities_support (exposed_capabilities install) backend.

  Definition production_default_backend
      (install : ProductionInstallation) : option Backend :=
    match exposed_capabilities install with
    | [] => None
    | capability :: _ =>
        if capability_is_default capability
        then Some (capability_backend capability)
        else None
    end.

  Definition production_report_shape
      (install : ProductionInstallation) (backend : Backend)
      : option ReportShape :=
    if production_installation_ok install
    then
      match backend with
      | RhoMachine => Some ObservationShape
      | Dovetail => Some DovetailReportShape
      | Ascent => None
      end
    else None.

  Theorem plan_derived_dovetail_match_equals_plan_match :
    forall lang plan available well_formed completeness total artifact,
      dovetail_compiler_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact) =
      rho_plan_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact).
  Proof.
    intros lang plan available well_formed completeness total artifact.
    reflexivity.
  Qed.

  Theorem plan_derived_invocation_match_equals_plan_match :
    forall lang plan available well_formed completeness total artifact,
      invocation_compiler_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact) =
      rho_plan_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact).
  Proof.
    intros lang plan available well_formed completeness total artifact.
    reflexivity.
  Qed.

  Theorem plan_derived_stage_matches_follow_plan_match :
    forall lang plan available well_formed completeness total artifact,
      rho_plan_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact) = true ->
      dovetail_compiler_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact) = true /\
      invocation_compiler_matches_language
        (plan_derived_installation
           lang plan available well_formed completeness total artifact) = true.
  Proof.
    intros lang plan available well_formed completeness total artifact Hplan.
    rewrite plan_derived_dovetail_match_equals_plan_match.
    rewrite plan_derived_invocation_match_equals_plan_match.
    split; exact Hplan.
  Qed.

  Theorem ok_installation_exposes_rho_default : forall install,
    production_installation_ok install = true ->
    production_default_backend install = Some RhoMachine.
  Proof.
    intros install Hok.
    unfold production_default_backend, exposed_capabilities.
    rewrite Hok.
    reflexivity.
  Qed.

  Theorem ok_installation_exposes_dovetail_intermediate : forall install,
    production_installation_ok install = true ->
    production_supports install Dovetail = true.
  Proof.
    intros install Hok.
    unfold production_supports, exposed_capabilities, capabilities_support.
    rewrite Hok.
    reflexivity.
  Qed.

  Theorem ok_installation_never_exposes_ascent : forall install,
    production_supports install Ascent = false.
  Proof.
    intros install.
    unfold production_supports, exposed_capabilities, capabilities_support.
    destruct (production_installation_ok install); reflexivity.
  Qed.

  Theorem rho_report_requires_ok_installation : forall install,
    production_report_shape install RhoMachine = Some ObservationShape ->
    production_installation_ok install = true.
  Proof.
    intros install Hshape.
    unfold production_report_shape in Hshape.
    destruct (production_installation_ok install) eqn:Hok.
    - reflexivity.
    - discriminate Hshape.
  Qed.

  Theorem dovetail_report_requires_ok_installation : forall install,
    production_report_shape install Dovetail = Some DovetailReportShape ->
    production_installation_ok install = true.
  Proof.
    intros install Hshape.
    unfold production_report_shape in Hshape.
    destruct (production_installation_ok install) eqn:Hok.
    - reflexivity.
    - discriminate Hshape.
  Qed.

  Theorem ok_installation_requires_rho_plan_match : forall install,
    production_installation_ok install = true ->
    rho_plan_matches_language install = true.
  Proof.
    intros install Hok.
    unfold production_installation_ok in Hok.
    destruct (rho_plan_matches_language install); simpl in Hok.
    - reflexivity.
    - discriminate Hok.
  Qed.

  Theorem ok_installation_requires_dovetail_compiler_match : forall install,
    production_installation_ok install = true ->
    dovetail_compiler_matches_language install = true.
  Proof.
    intros install Hok.
    unfold production_installation_ok in Hok.
    destruct (rho_plan_matches_language install);
      destruct (dovetail_compiler_matches_language install);
      simpl in Hok;
      try reflexivity;
      discriminate Hok.
  Qed.

  Theorem ok_installation_requires_invocation_compiler_match : forall install,
    production_installation_ok install = true ->
    invocation_compiler_matches_language install = true.
  Proof.
    intros install Hok.
    unfold production_installation_ok in Hok.
    destruct (rho_plan_matches_language install);
      destruct (dovetail_compiler_matches_language install);
      destruct (invocation_compiler_matches_language install);
      simpl in Hok;
      try reflexivity;
      discriminate Hok.
  Qed.

  Theorem ok_installation_requires_checked_dovetail_report : forall install,
    production_installation_ok install = true ->
    dovetail_report_checked (installed_dovetail_compiler install) = true.
  Proof.
    intros install Hok.
    unfold production_installation_ok in Hok.
    destruct (rho_plan_matches_language install);
      destruct (dovetail_compiler_matches_language install);
      destruct (invocation_compiler_matches_language install);
      destruct (rho_plan_accepted (installed_rho_plan install));
      destruct (dovetail_report_checked
                  (installed_dovetail_compiler install));
      simpl in Hok;
      try reflexivity;
      discriminate Hok.
  Qed.

  Theorem ok_installation_requires_ast_first_invocation : forall install,
    production_installation_ok install = true ->
    artifact_is_ast_first
      (invocation_artifact_boundary
         (installed_invocation_compiler install)) = true.
  Proof.
    intros install Hok.
    unfold production_installation_ok in Hok.
    destruct (rho_plan_matches_language install);
      destruct (dovetail_compiler_matches_language install);
      destruct (invocation_compiler_matches_language install);
      destruct (rho_plan_accepted (installed_rho_plan install));
      destruct (dovetail_report_checked
                  (installed_dovetail_compiler install));
      destruct (invocation_total
                  (installed_invocation_compiler install));
      destruct (artifact_is_ast_first
                  (invocation_artifact_boundary
                     (installed_invocation_compiler install)));
      simpl in Hok;
      try reflexivity;
      discriminate Hok.
  Qed.

  Theorem mismatched_rho_plan_blocks_installation : forall lang plan dovetail invoke,
    Nat.eqb
      (rho_plan_definition_id plan)
      (generated_definition_id lang) = false ->
    production_installation_ok
      {| installed_language := lang;
         installed_rho_plan := plan;
         installed_dovetail_compiler := dovetail;
         installed_invocation_compiler := invoke |} = false.
  Proof.
    intros lang plan dovetail invoke Hmismatch.
    unfold production_installation_ok, rho_plan_matches_language,
      language_definition_id.
    simpl.
    rewrite Hmismatch.
    reflexivity.
  Qed.

  Theorem mismatched_dovetail_compiler_blocks_installation :
    forall lang plan dovetail invoke,
      Nat.eqb
        (dovetail_compiler_definition_id dovetail)
        (generated_definition_id lang) = false ->
      production_installation_ok
        {| installed_language := lang;
           installed_rho_plan := plan;
           installed_dovetail_compiler := dovetail;
           installed_invocation_compiler := invoke |} = false.
  Proof.
    intros lang plan dovetail invoke Hmismatch.
    unfold production_installation_ok, rho_plan_matches_language,
      dovetail_compiler_matches_language, invocation_compiler_matches_language,
      language_definition_id.
    simpl.
    destruct (Nat.eqb (rho_plan_definition_id plan)
                     (generated_definition_id lang));
      simpl.
    - rewrite Hmismatch. reflexivity.
    - reflexivity.
  Qed.

  Theorem mismatched_invocation_compiler_blocks_installation :
    forall lang plan dovetail invoke,
      Nat.eqb
        (invocation_compiler_definition_id invoke)
        (generated_definition_id lang) = false ->
      production_installation_ok
        {| installed_language := lang;
           installed_rho_plan := plan;
           installed_dovetail_compiler := dovetail;
           installed_invocation_compiler := invoke |} = false.
  Proof.
    intros lang plan dovetail invoke Hmismatch.
    unfold production_installation_ok, rho_plan_matches_language,
      dovetail_compiler_matches_language, invocation_compiler_matches_language,
      language_definition_id.
    simpl.
    destruct (Nat.eqb (rho_plan_definition_id plan)
                     (generated_definition_id lang));
      destruct (Nat.eqb (dovetail_compiler_definition_id dovetail)
                        (generated_definition_id lang));
      simpl.
    - rewrite Hmismatch. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem bounded_dovetail_report_blocks_installation :
    forall lang plan available well_formed invoke,
      production_installation_ok
        {| installed_language := lang;
           installed_rho_plan := plan;
           installed_dovetail_compiler :=
             {| dovetail_compiler_definition_id :=
                  generated_definition_id lang;
                dovetail_report_available := available;
                dovetail_report_well_formed := well_formed;
                dovetail_report_completeness := BoundedByCycleCut |};
           installed_invocation_compiler := invoke |} = false.
  Proof.
    intros lang plan available well_formed invoke.
    unfold production_installation_ok, dovetail_report_checked,
      rho_plan_matches_language, dovetail_compiler_matches_language,
      invocation_compiler_matches_language, language_definition_id.
    simpl.
    rewrite Nat.eqb_refl.
    destruct (Nat.eqb (rho_plan_definition_id plan)
                     (generated_definition_id lang));
      destruct (Nat.eqb (invocation_compiler_definition_id invoke)
                        (generated_definition_id lang));
      destruct (rho_plan_accepted plan);
      destruct available;
      destruct well_formed;
      reflexivity.
  Qed.

  Theorem source_text_invocation_blocks_installation :
    forall lang plan dovetail invoke_id total,
      production_installation_ok
        {| installed_language := lang;
           installed_rho_plan := plan;
           installed_dovetail_compiler := dovetail;
           installed_invocation_compiler :=
             {| invocation_compiler_definition_id := invoke_id;
                invocation_total := total;
                invocation_artifact_boundary := SourceText |} |} = false.
  Proof.
    intros lang plan dovetail invoke_id total.
    unfold production_installation_ok.
    simpl.
    destruct (rho_plan_matches_language
                {| installed_language := lang;
                   installed_rho_plan := plan;
                   installed_dovetail_compiler := dovetail;
                   installed_invocation_compiler :=
                     {| invocation_compiler_definition_id := invoke_id;
                        invocation_total := total;
                        invocation_artifact_boundary := SourceText |} |});
      destruct (dovetail_compiler_matches_language
                {| installed_language := lang;
                   installed_rho_plan := plan;
                   installed_dovetail_compiler := dovetail;
                   installed_invocation_compiler :=
                     {| invocation_compiler_definition_id := invoke_id;
                        invocation_total := total;
                        invocation_artifact_boundary := SourceText |} |});
      destruct (invocation_compiler_matches_language
                {| installed_language := lang;
                   installed_rho_plan := plan;
                   installed_dovetail_compiler := dovetail;
                   installed_invocation_compiler :=
                     {| invocation_compiler_definition_id := invoke_id;
                        invocation_total := total;
                        invocation_artifact_boundary := SourceText |} |});
      destruct (rho_plan_accepted plan);
      destruct (dovetail_report_checked dovetail);
      destruct total;
      reflexivity.
  Qed.

  Theorem failed_installation_exposes_no_runtime_backend : forall install,
    production_installation_ok install = false ->
    exposed_capabilities install = [].
  Proof.
    intros install Hfail.
    unfold exposed_capabilities.
    rewrite Hfail.
    reflexivity.
  Qed.

End GeneratedLanguageInstallation.
