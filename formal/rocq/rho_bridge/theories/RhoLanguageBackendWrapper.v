(*
 * RhoLanguageBackendWrapper: a generated MeTTaIL language can be wrapped with
 * a flip-gated PlannedRhoBackend without changing the generated crate.
 *
 * Rust image:
 *   - `RhoRuntimeBackedLanguage<L, F>` delegates parsing, environments,
 *     type inference, and non-Rho, non-Ascent backend requests to `L`.
 *   - The wrapper selects `RuntimeBackend::RhoMachine` as its default backend.
 *   - The legacy Ascent runtime is not exposed through the production
 *     Rho-backed value.
 *   - The wrapper installs only a planned backend whose `LanguageDef` identity
 *     matches the generated language being wrapped.
 *   - The Rho path returns an observation-shaped `RuntimeBackendReport`, not
 *     `AscentResults`.
 *   - Ascent-shaped seeded facts are rejected on the Rho path unless the fact
 *     set is empty.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List.

Import ListNotations.

Section RhoLanguageBackendWrapper.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive ReportShape : Type :=
  | AscentShape
  | ObservationShape.

  Inductive SeedFactsState : Type :=
  | NoSeedFacts
  | SeedFactsPresent.

  Record RuntimeBackendCapability : Type := {
    capability_backend : Backend;
    capability_is_default : bool
  }.

  Record InnerLanguage : Type := {
    inner_supports_ascent : bool;
    inner_supports_dovetail : bool
  }.

  Record RhoWrapper : Type := {
    wrapped_inner : InnerLanguage;
    planned_rho_backend : bool;
    plan_matches_language : bool;
    invocation_total : bool
  }.

  Definition wrapper_installs_rho (wrapper : RhoWrapper) : bool :=
    planned_rho_backend wrapper && plan_matches_language wrapper.

  Definition inner_supports
      (inner : InnerLanguage) (backend : Backend) : bool :=
    match backend with
    | Ascent => false
    | Dovetail => inner_supports_dovetail inner
    | RhoMachine => false
    end.

  Definition backend_eqb (left right : Backend) : bool :=
    match left, right with
    | Ascent, Ascent => true
    | Dovetail, Dovetail => true
    | RhoMachine, RhoMachine => true
    | _, _ => false
    end.

  Definition demoted_inner_capabilities
      (inner : InnerLanguage) : list RuntimeBackendCapability :=
    (if inner_supports_dovetail inner
     then [{| capability_backend := Dovetail;
              capability_is_default := false |}]
     else []).

  Definition wrapper_default_backend (_wrapper : RhoWrapper) : Backend :=
    RhoMachine.

  Definition wrapper_runtime_capabilities
      (wrapper : RhoWrapper) : list RuntimeBackendCapability :=
    (if wrapper_installs_rho wrapper
     then [{| capability_backend := RhoMachine;
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
      (wrapper : RhoWrapper) (backend : Backend) : bool :=
    match backend with
    | RhoMachine => wrapper_installs_rho wrapper
    | Ascent => false
    | other => inner_supports (wrapped_inner wrapper) other
    end.

  Definition wrapper_default_report_runs (wrapper : RhoWrapper) : bool :=
    wrapper_installs_rho wrapper && invocation_total wrapper.

  Definition wrapper_default_report_shape
      (wrapper : RhoWrapper) : option ReportShape :=
    if wrapper_default_report_runs wrapper
    then Some ObservationShape
    else None.

  Definition wrapper_default_ascent_compat
      (wrapper : RhoWrapper) : bool :=
    match wrapper_default_report_shape wrapper with
    | Some AscentShape => true
    | Some ObservationShape => false
    | None => false
    end.

  Definition wrapper_report_with_facts
      (wrapper : RhoWrapper) (facts : SeedFactsState) : bool :=
    match facts with
    | NoSeedFacts => wrapper_default_report_runs wrapper
    | SeedFactsPresent => false
    end.

  Theorem wrapper_default_backend_is_rho : forall wrapper,
    wrapper_default_backend wrapper = RhoMachine.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_rho_iff_installed : forall wrapper,
    wrapper_supports wrapper RhoMachine = wrapper_installs_rho wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_installs_rho_requires_planned_backend : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    planned_rho_backend wrapper = true.
  Proof.
    intros wrapper Hinstall.
    unfold wrapper_installs_rho in Hinstall.
    destruct (planned_rho_backend wrapper); simpl in Hinstall.
    - reflexivity.
    - discriminate Hinstall.
  Qed.

  Theorem wrapper_installs_rho_requires_matching_language : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    plan_matches_language wrapper = true.
  Proof.
    intros wrapper Hinstall.
    unfold wrapper_installs_rho in Hinstall.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      simpl in Hinstall;
      try reflexivity;
      discriminate Hinstall.
  Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros [[supports_ascent supports_dovetail] planned same_language invocation] backend.
    destruct backend;
      destruct planned;
      destruct same_language;
      destruct supports_ascent;
      destruct supports_dovetail;
      reflexivity.
  Qed.

  Theorem planned_wrapper_capabilities_start_with_rho_default :
    forall inner invocation,
      exists tail,
        wrapper_runtime_capabilities
          {| wrapped_inner := inner;
             planned_rho_backend := true;
             plan_matches_language := true;
             invocation_total := invocation |} =
        {| capability_backend := RhoMachine;
           capability_is_default := true |} :: tail.
  Proof.
    intros inner invocation.
    exists (demoted_inner_capabilities inner).
    reflexivity.
  Qed.

  Definition no_non_rho_default
      (capability : RuntimeBackendCapability) : bool :=
    match capability_backend capability with
    | RhoMachine => true
    | _ => negb (capability_is_default capability)
    end.

  Theorem wrapper_capabilities_have_no_inherited_default : forall wrapper,
    Forall
      (fun capability => no_non_rho_default capability = true)
      (wrapper_runtime_capabilities wrapper).
  Proof.
    intros [[supports_ascent supports_dovetail] planned same_language invocation].
    destruct planned;
      destruct same_language;
      destruct supports_ascent;
      destruct supports_dovetail;
      repeat constructor.
  Qed.

  Theorem wrapper_rejects_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_delegates_dovetail_support : forall wrapper,
    wrapper_supports wrapper Dovetail =
      inner_supports_dovetail (wrapped_inner wrapper).
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_default_report_requires_planned_backend : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    planned_rho_backend wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs in Hrun.
    unfold wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper); simpl in Hrun.
    - reflexivity.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_matching_language : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    plan_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_total_invocation : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    invocation_total wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs in Hrun.
    destruct (wrapper_installs_rho wrapper); simpl in Hrun.
    - exact Hrun.
    - discriminate Hrun.
  Qed.

  Theorem planned_total_wrapper_default_report_runs : forall inner,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         planned_rho_backend := true;
         plan_matches_language := true;
         invocation_total := true |} = true.
  Proof. intros inner. reflexivity. Qed.

  Theorem mismatched_plan_never_installs_rho : forall inner planned invocation,
    wrapper_supports
      {| wrapped_inner := inner;
         planned_rho_backend := planned;
         plan_matches_language := false;
         invocation_total := invocation |}
      RhoMachine = false /\
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         planned_rho_backend := planned;
         plan_matches_language := false;
         invocation_total := invocation |} = false.
  Proof.
    intros inner planned invocation.
    destruct planned; simpl; split; reflexivity.
  Qed.

  Theorem wrapper_default_report_is_observation_shaped : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    wrapper_default_report_shape wrapper = Some ObservationShape.
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
      wrapper_default_report_runs.
    destruct (wrapper_installs_rho wrapper);
      destruct (invocation_total wrapper);
      reflexivity.
  Qed.

  Theorem wrapper_empty_seeded_facts_match_default : forall wrapper,
    wrapper_report_with_facts wrapper NoSeedFacts =
      wrapper_default_report_runs wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_seeded_facts_block_rho_default : forall wrapper,
    wrapper_report_with_facts wrapper SeedFactsPresent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_does_not_install_rho_in_inner : forall inner,
    inner_supports inner RhoMachine = false.
  Proof. intros inner. reflexivity. Qed.

End RhoLanguageBackendWrapper.
