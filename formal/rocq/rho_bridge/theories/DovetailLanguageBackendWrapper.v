(*
 * DovetailLanguageBackendWrapper: a generated MeTTaIL language can be wrapped
 * with a language-matched Dovetail report producer without changing the generated
 * crate or coupling `dovetail` to `runtime`.
 *
 * Rust image:
 *   - `mettail_dovetail_runtime::DovetailRuntimeBackedLanguage<L, F>`
 *     delegates parsing, environments, type inference, and non-Dovetail,
 *     non-Ascent backend requests to `L`.
 *   - The wrapper selects `RuntimeBackend::Dovetail` as its default backend.
 *   - The legacy Ascent runtime is not exposed through the production
 *     Dovetail-backed value.
 *   - The wrapper installs the default only when the Dovetail report producer
 *     was derived from the same macro-expanded generated `LanguageDef` as the
 *     wrapped language.
 *   - Concrete term execution has additional obligations: the report producer
 *     must return a report, and that report must be structurally well formed
 *     and complete before it can run as the default backend.
 *   - The Dovetail path returns a `DovetailRunReport` shaped
 *     `RuntimeBackendReport`, not `AscentResults` and not Rho observations.
 *   - `BoundedByCycleCut`, malformed reports, and Ascent-shaped seeded facts
 *     are rejected on the Dovetail default path.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List PeanoNat.

Import ListNotations.

Section DovetailLanguageBackendWrapper.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive ReportShape : Type :=
  | AscentShape
  | DovetailReportShape
  | ObservationShape.

  Inductive ExtractionCompleteness : Type :=
  | Complete
  | BoundedByCycleCut.

  Inductive SeedFactsState : Type :=
  | NoSeedFacts
  | SeedFactsPresent.

  Record RuntimeBackendCapability : Type := {
    capability_backend : Backend;
    capability_is_default : bool
  }.

  Record InnerLanguage : Type := {
    inner_supports_ascent : bool;
    inner_supports_rho : bool
  }.

  Record DovetailWrapper : Type := {
    wrapped_inner : InnerLanguage;
    generated_definition_id : nat;
    dovetail_compiler_definition_id : nat;
    dovetail_report_available : bool;
    dovetail_report_completeness : ExtractionCompleteness;
    dovetail_report_well_formed : bool
  }.

  Definition dovetail_compiler_matches_language
      (wrapper : DovetailWrapper) : bool :=
    Nat.eqb
      (dovetail_compiler_definition_id wrapper)
      (generated_definition_id wrapper).

  Definition wrapper_installs_dovetail (wrapper : DovetailWrapper) : bool :=
    dovetail_compiler_matches_language wrapper.

  Definition inner_supports
      (inner : InnerLanguage) (backend : Backend) : bool :=
    match backend with
    | Ascent => false
    | RhoMachine => inner_supports_rho inner
    | Dovetail => false
    end.

  Definition backend_eqb (left right : Backend) : bool :=
    match left, right with
    | Ascent, Ascent => true
    | Dovetail, Dovetail => true
    | RhoMachine, RhoMachine => true
    | _, _ => false
    end.

  Definition completeness_is_complete
      (status : ExtractionCompleteness) : bool :=
    match status with
    | Complete => true
    | BoundedByCycleCut => false
    end.

  Definition demoted_inner_capabilities
      (inner : InnerLanguage) : list RuntimeBackendCapability :=
    (if inner_supports_rho inner
     then [{| capability_backend := RhoMachine;
              capability_is_default := false |}]
     else []).

  Definition wrapper_default_backend (_wrapper : DovetailWrapper) : Backend :=
    Dovetail.

  Definition wrapper_runtime_capabilities
      (wrapper : DovetailWrapper) : list RuntimeBackendCapability :=
    (if wrapper_installs_dovetail wrapper
     then [{| capability_backend := Dovetail;
              capability_is_default := true |}]
     else []) ++
    demoted_inner_capabilities (wrapped_inner wrapper).

  Definition capabilities_support
      (capabilities : list RuntimeBackendCapability) (backend : Backend) : bool :=
    existsb
      (fun capability =>
         backend_eqb (capability_backend capability) backend)
      capabilities.

  Definition wrapper_supports
      (wrapper : DovetailWrapper) (backend : Backend) : bool :=
    match backend with
    | Dovetail => wrapper_installs_dovetail wrapper
    | Ascent => false
    | other => inner_supports (wrapped_inner wrapper) other
    end.

  Definition wrapper_default_report_runs (wrapper : DovetailWrapper) : bool :=
    wrapper_installs_dovetail wrapper &&
    dovetail_report_available wrapper &&
    completeness_is_complete (dovetail_report_completeness wrapper) &&
    dovetail_report_well_formed wrapper.

  Definition wrapper_default_report_shape
      (wrapper : DovetailWrapper) : option ReportShape :=
    if wrapper_default_report_runs wrapper
    then Some DovetailReportShape
    else None.

  Definition wrapper_default_ascent_compat
      (wrapper : DovetailWrapper) : bool :=
    match wrapper_default_report_shape wrapper with
    | Some AscentShape => true
    | Some DovetailReportShape => false
    | Some ObservationShape => false
    | None => false
    end.

  Definition wrapper_report_with_facts
      (wrapper : DovetailWrapper) (facts : SeedFactsState) : bool :=
    match facts with
    | NoSeedFacts => wrapper_default_report_runs wrapper
    | SeedFactsPresent => false
    end.

  Theorem wrapper_default_backend_is_dovetail : forall wrapper,
    wrapper_default_backend wrapper = Dovetail.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_dovetail_iff_installed : forall wrapper,
    wrapper_supports wrapper Dovetail = wrapper_installs_dovetail wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_installs_dovetail_requires_compiler_match : forall wrapper,
    wrapper_installs_dovetail wrapper = true ->
    dovetail_compiler_matches_language wrapper = true.
  Proof. intros wrapper Hinstall. exact Hinstall. Qed.

  Theorem mismatched_compiler_blocks_installation : forall wrapper,
    dovetail_compiler_matches_language wrapper = false ->
    wrapper_installs_dovetail wrapper = false.
  Proof.
    intros wrapper Hmismatch.
    unfold wrapper_installs_dovetail.
    exact Hmismatch.
  Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros [[supports_ascent supports_rho] generated_id compiler_id
              available completeness well_formed] backend.
    simpl.
    unfold wrapper_runtime_capabilities, wrapper_supports, capabilities_support,
      inner_supports, demoted_inner_capabilities, wrapper_installs_dovetail,
      dovetail_compiler_matches_language, backend_eqb.
    simpl.
    destruct backend;
      destruct available;
      destruct supports_ascent;
      destruct supports_rho;
      destruct (compiler_id =? generated_id);
      reflexivity.
  Qed.

  Theorem matched_wrapper_capabilities_start_with_dovetail_default :
    forall inner definition_id available completeness well_formed,
      exists tail,
        wrapper_runtime_capabilities
          {| wrapped_inner := inner;
             generated_definition_id := definition_id;
             dovetail_compiler_definition_id := definition_id;
             dovetail_report_available := available;
             dovetail_report_completeness := completeness;
             dovetail_report_well_formed := well_formed |} =
        {| capability_backend := Dovetail;
           capability_is_default := true |} :: tail.
  Proof.
    intros inner definition_id available completeness well_formed.
    exists (demoted_inner_capabilities inner).
    unfold wrapper_runtime_capabilities, wrapper_installs_dovetail,
      dovetail_compiler_matches_language.
    rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

  Definition no_non_dovetail_default
      (capability : RuntimeBackendCapability) : bool :=
    match capability_backend capability with
    | Dovetail => true
    | _ => negb (capability_is_default capability)
    end.

  Theorem wrapper_capabilities_have_no_inherited_default : forall wrapper,
    Forall
      (fun capability => no_non_dovetail_default capability = true)
      (wrapper_runtime_capabilities wrapper).
  Proof.
    intros [[supports_ascent supports_rho] generated_id compiler_id
              available completeness well_formed].
    simpl.
    unfold wrapper_runtime_capabilities, demoted_inner_capabilities,
      wrapper_installs_dovetail, dovetail_compiler_matches_language.
    simpl.
    destruct available;
      destruct supports_ascent;
      destruct supports_rho;
      destruct (compiler_id =? generated_id);
      repeat constructor;
      reflexivity.
  Qed.

  Theorem wrapper_rejects_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_delegates_rho_support : forall wrapper,
    wrapper_supports wrapper RhoMachine =
      inner_supports_rho (wrapped_inner wrapper).
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_default_report_requires_report_available : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_report_available wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs in Hrun.
    apply andb_true_iff in Hrun as [Hrun _].
    apply andb_true_iff in Hrun as [Hrun _].
    apply andb_true_iff in Hrun as [_ Havailable].
    exact Havailable.
  Qed.

  Theorem wrapper_default_report_requires_complete_report : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_report_completeness wrapper = Complete.
  Proof.
    intros [inner generated_id compiler_id available completeness well_formed]
      Hrun.
    unfold wrapper_default_report_runs in Hrun.
    apply andb_true_iff in Hrun as [Hrun _].
    apply andb_true_iff in Hrun as [_ Hcomplete].
    destruct completeness; simpl in Hcomplete.
    - reflexivity.
    - discriminate Hcomplete.
  Qed.

  Theorem wrapper_default_report_requires_compiler_match : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_compiler_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs in Hrun.
    destruct (wrapper_installs_dovetail wrapper) eqn:Hinstall;
      simpl in Hrun.
    - apply wrapper_installs_dovetail_requires_compiler_match.
      exact Hinstall.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_well_formed_report : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_report_well_formed wrapper = true.
  Proof.
    intros [inner generated_id compiler_id available completeness well_formed]
      Hrun.
    unfold wrapper_default_report_runs in Hrun.
    apply andb_true_iff in Hrun as [_ Hwell_formed].
    exact Hwell_formed.
  Qed.

  Theorem available_complete_well_formed_wrapper_default_report_runs :
    forall inner definition_id,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         generated_definition_id := definition_id;
         dovetail_compiler_definition_id := definition_id;
         dovetail_report_available := true;
         dovetail_report_completeness := Complete;
         dovetail_report_well_formed := true |} = true.
  Proof.
    intros inner definition_id.
    unfold wrapper_default_report_runs, wrapper_installs_dovetail,
      dovetail_compiler_matches_language.
    rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

  Theorem available_bounded_wrapper_default_report_rejects : forall inner,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         generated_definition_id := 0;
         dovetail_compiler_definition_id := 0;
         dovetail_report_available := true;
         dovetail_report_completeness := BoundedByCycleCut;
         dovetail_report_well_formed := true |} = false.
  Proof. intros inner. reflexivity. Qed.

  Theorem unavailable_wrapper_default_report_rejects :
    forall inner completeness well_formed,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         generated_definition_id := 0;
         dovetail_compiler_definition_id := 0;
         dovetail_report_available := false;
         dovetail_report_completeness := completeness;
         dovetail_report_well_formed := well_formed |} = false.
  Proof. intros inner completeness well_formed. reflexivity. Qed.

  Theorem report_availability_does_not_block_capability_exposure :
    forall inner definition_id completeness well_formed,
      wrapper_runtime_capabilities
        {| wrapped_inner := inner;
           generated_definition_id := definition_id;
           dovetail_compiler_definition_id := definition_id;
           dovetail_report_available := false;
           dovetail_report_completeness := completeness;
           dovetail_report_well_formed := well_formed |} =
      wrapper_runtime_capabilities
        {| wrapped_inner := inner;
           generated_definition_id := definition_id;
           dovetail_compiler_definition_id := definition_id;
           dovetail_report_available := true;
           dovetail_report_completeness := completeness;
           dovetail_report_well_formed := well_formed |}.
  Proof.
    intros inner definition_id completeness well_formed.
    reflexivity.
  Qed.

  Theorem available_malformed_wrapper_default_report_rejects :
    forall inner completeness,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         generated_definition_id := 0;
         dovetail_compiler_definition_id := 0;
         dovetail_report_available := true;
         dovetail_report_completeness := completeness;
         dovetail_report_well_formed := false |} = false.
  Proof. intros inner completeness. destruct completeness; reflexivity. Qed.

  Theorem available_mismatched_wrapper_default_report_rejects :
    forall inner generated_id compiler_id completeness well_formed,
    (compiler_id =? generated_id) = false ->
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         generated_definition_id := generated_id;
         dovetail_compiler_definition_id := compiler_id;
         dovetail_report_available := true;
         dovetail_report_completeness := completeness;
         dovetail_report_well_formed := well_formed |} = false.
  Proof.
    intros inner generated_id compiler_id completeness well_formed Hmismatch.
    set (wrapper :=
      {| wrapped_inner := inner;
         generated_definition_id := generated_id;
         dovetail_compiler_definition_id := compiler_id;
         dovetail_report_available := true;
         dovetail_report_completeness := completeness;
         dovetail_report_well_formed := well_formed |}).
    assert (Hinstall : wrapper_installs_dovetail wrapper = false).
    {
      apply mismatched_compiler_blocks_installation.
      unfold dovetail_compiler_matches_language.
      subst wrapper.
      simpl.
      exact Hmismatch.
    }
    unfold wrapper_default_report_runs.
    rewrite Hinstall.
    reflexivity.
  Qed.

  Theorem wrapper_default_report_is_dovetail_report_shaped : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    wrapper_default_report_shape wrapper = Some DovetailReportShape.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_shape.
    rewrite Hrun. reflexivity.
  Qed.

  Theorem wrapper_default_is_not_ascent_compat : forall wrapper,
    wrapper_default_ascent_compat wrapper = false.
  Proof.
    intros wrapper.
    unfold wrapper_default_ascent_compat, wrapper_default_report_shape,
      wrapper_default_report_runs, completeness_is_complete.
    destruct (wrapper_installs_dovetail wrapper);
      destruct (dovetail_report_available wrapper);
      destruct (dovetail_report_completeness wrapper);
      destruct (dovetail_report_well_formed wrapper);
      reflexivity.
  Qed.

  Theorem wrapper_empty_seeded_facts_match_default : forall wrapper,
    wrapper_report_with_facts wrapper NoSeedFacts =
      wrapper_default_report_runs wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_seeded_facts_block_dovetail_default : forall wrapper,
    wrapper_report_with_facts wrapper SeedFactsPresent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_does_not_install_dovetail_in_inner : forall inner,
    inner_supports inner Dovetail = false.
  Proof. intros inner. reflexivity. Qed.

End DovetailLanguageBackendWrapper.
