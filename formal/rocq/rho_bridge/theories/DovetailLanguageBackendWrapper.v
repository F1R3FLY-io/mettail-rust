(*
 * DovetailLanguageBackendWrapper: a generated MeTTaIL language can be wrapped
 * with a complete Dovetail report producer without changing the generated
 * crate or coupling `dovetail` to `mettail-runtime`.
 *
 * Rust image:
 *   - `mettail_dovetail_runtime::DovetailRuntimeBackedLanguage<L, F>`
 *     delegates parsing, environments, type inference, Ascent execution, and
 *     non-Dovetail backend requests to `L`.
 *   - The wrapper selects `RuntimeBackend::Dovetail` as its default backend.
 *   - The Dovetail path returns a `DovetailRunReport` shaped
 *     `RuntimeBackendReport`, not `AscentResults` and not Rho observations.
 *   - `BoundedByCycleCut`, malformed reports, and Ascent-shaped seeded facts
 *     are rejected on the Dovetail default path.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List.

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
    capability_is_default : bool;
    capability_has_evidence : bool
  }.

  Record InnerLanguage : Type := {
    inner_supports_ascent : bool;
    inner_supports_rho : bool
  }.

  Record DovetailWrapper : Type := {
    wrapped_inner : InnerLanguage;
    dovetail_report_available : bool;
    dovetail_report_completeness : ExtractionCompleteness;
    dovetail_report_well_formed : bool
  }.

  Definition inner_supports
      (inner : InnerLanguage) (backend : Backend) : bool :=
    match backend with
    | Ascent => inner_supports_ascent inner
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
    (if inner_supports_ascent inner
     then [{| capability_backend := Ascent;
              capability_is_default := false;
              capability_has_evidence := true |}]
     else []) ++
    (if inner_supports_rho inner
     then [{| capability_backend := RhoMachine;
              capability_is_default := false;
              capability_has_evidence := true |}]
     else []).

  Definition wrapper_default_backend (_wrapper : DovetailWrapper) : Backend :=
    Dovetail.

  Definition wrapper_runtime_capabilities
      (wrapper : DovetailWrapper) : list RuntimeBackendCapability :=
    (if dovetail_report_available wrapper
     then [{| capability_backend := Dovetail;
              capability_is_default := true;
              capability_has_evidence := true |}]
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
    | Dovetail => dovetail_report_available wrapper
    | other => inner_supports (wrapped_inner wrapper) other
    end.

  Definition wrapper_default_report_runs (wrapper : DovetailWrapper) : bool :=
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

  Theorem wrapper_supports_dovetail_iff_report_available : forall wrapper,
    wrapper_supports wrapper Dovetail = dovetail_report_available wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros [[supports_ascent supports_rho] available completeness well_formed] backend.
    destruct backend;
      destruct available;
      destruct well_formed;
      destruct supports_ascent;
      destruct supports_rho;
      reflexivity.
  Qed.

  Theorem available_wrapper_capabilities_start_with_dovetail_default :
    forall inner completeness well_formed,
      exists tail,
        wrapper_runtime_capabilities
          {| wrapped_inner := inner;
             dovetail_report_available := true;
             dovetail_report_completeness := completeness;
             dovetail_report_well_formed := well_formed |} =
        {| capability_backend := Dovetail;
           capability_is_default := true;
           capability_has_evidence := true |} :: tail.
  Proof.
    intros inner completeness well_formed.
    exists (demoted_inner_capabilities inner).
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
    intros [[supports_ascent supports_rho] available completeness well_formed].
    destruct available;
      destruct supports_ascent;
      destruct supports_rho;
      repeat constructor.
  Qed.

  Theorem wrapper_delegates_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent =
      inner_supports_ascent (wrapped_inner wrapper).
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
    destruct (dovetail_report_available wrapper); simpl in Hrun.
    - reflexivity.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_complete_report : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_report_completeness wrapper = Complete.
  Proof.
    intros [inner available completeness well_formed] Hrun.
    unfold wrapper_default_report_runs in Hrun.
    destruct available; simpl in Hrun.
      - destruct completeness; simpl in Hrun.
      + destruct well_formed; simpl in Hrun.
        * reflexivity.
        * discriminate Hrun.
      + discriminate Hrun.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_well_formed_report : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    dovetail_report_well_formed wrapper = true.
  Proof.
    intros [inner available completeness well_formed] Hrun.
    unfold wrapper_default_report_runs in Hrun.
    destruct available; simpl in Hrun.
    - destruct completeness; simpl in Hrun.
      + destruct well_formed; simpl in Hrun.
        * reflexivity.
        * discriminate Hrun.
      + discriminate Hrun.
    - discriminate Hrun.
  Qed.

  Theorem available_complete_well_formed_wrapper_default_report_runs :
    forall inner,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         dovetail_report_available := true;
         dovetail_report_completeness := Complete;
         dovetail_report_well_formed := true |} = true.
  Proof. intros inner. reflexivity. Qed.

  Theorem available_bounded_wrapper_default_report_rejects : forall inner,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         dovetail_report_available := true;
         dovetail_report_completeness := BoundedByCycleCut;
         dovetail_report_well_formed := true |} = false.
  Proof. intros inner. reflexivity. Qed.

  Theorem available_malformed_wrapper_default_report_rejects :
    forall inner completeness,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         dovetail_report_available := true;
         dovetail_report_completeness := completeness;
         dovetail_report_well_formed := false |} = false.
  Proof. intros inner completeness. destruct completeness; reflexivity. Qed.

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
