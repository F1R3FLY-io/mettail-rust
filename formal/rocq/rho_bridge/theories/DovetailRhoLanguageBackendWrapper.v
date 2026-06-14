(*
 * DovetailRhoLanguageBackendWrapper: production wrapper shape for replacing
 * the legacy runtime backend with a Dovetail-checked, Rho-executed path.
 *
 * Rust image:
 *   - `DovetailRhoRuntimeBackedLanguage<L, D, F>` delegates parsing,
 *     environments, and type inference to the generated language `L`.
 *   - The wrapper selects `RuntimeBackend::RhoMachine` as its default backend.
 *   - `RuntimeBackend::Dovetail` is exposed only as the checked intermediate
 *     report for diagnostics/query tooling; it is not the default runtime.
 *   - The default Rho path first builds a Dovetail report, checks structural
 *     well-formedness and `Complete`, then passes that checked report to the
 *     Rho AST invocation builder.
 *   - The legacy Ascent runtime and Ascent-shaped seeded facts are rejected
 *     through the production wrapped value.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List.

Import ListNotations.

Section DovetailRhoLanguageBackendWrapper.

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

  Record DovetailRhoWrapper : Type := {
    planned_rho_backend : bool;
    plan_matches_language : bool;
    dovetail_report_available : bool;
    dovetail_report_completeness : ExtractionCompleteness;
    dovetail_report_well_formed : bool;
    invocation_total_after_dovetail : bool
  }.

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

  Definition wrapper_installs_rho (wrapper : DovetailRhoWrapper) : bool :=
    planned_rho_backend wrapper && plan_matches_language wrapper.

  Definition dovetail_report_checked (wrapper : DovetailRhoWrapper) : bool :=
    dovetail_report_available wrapper &&
    completeness_is_complete (dovetail_report_completeness wrapper) &&
    dovetail_report_well_formed wrapper.

  Definition wrapper_default_backend (_wrapper : DovetailRhoWrapper) : Backend :=
    RhoMachine.

  Definition wrapper_runtime_capabilities
      (_wrapper : DovetailRhoWrapper) : list RuntimeBackendCapability :=
    [{| capability_backend := RhoMachine;
        capability_is_default := true |};
     {| capability_backend := Dovetail;
        capability_is_default := false |}].

  Definition capabilities_support
      (capabilities : list RuntimeBackendCapability) (backend : Backend) : bool :=
    existsb
      (fun capability =>
         backend_eqb (capability_backend capability) backend)
      capabilities.

  Definition wrapper_supports
      (_wrapper : DovetailRhoWrapper) (backend : Backend) : bool :=
    match backend with
    | RhoMachine => true
    | Dovetail => true
    | Ascent => false
    end.

  Definition wrapper_rho_report_runs (wrapper : DovetailRhoWrapper) : bool :=
    wrapper_installs_rho wrapper &&
    dovetail_report_checked wrapper &&
    invocation_total_after_dovetail wrapper.

  Definition wrapper_dovetail_report_runs (wrapper : DovetailRhoWrapper) : bool :=
    dovetail_report_checked wrapper.

  Definition wrapper_report_shape
      (wrapper : DovetailRhoWrapper) (backend : Backend) : option ReportShape :=
    match backend with
    | RhoMachine =>
        if wrapper_rho_report_runs wrapper
        then Some ObservationShape
        else None
    | Dovetail =>
        if wrapper_dovetail_report_runs wrapper
        then Some DovetailReportShape
        else None
    | Ascent => None
    end.

  Definition wrapper_default_ascent_compat
      (wrapper : DovetailRhoWrapper) : bool :=
    match wrapper_report_shape wrapper (wrapper_default_backend wrapper) with
    | Some AscentShape => true
    | Some DovetailReportShape => false
    | Some ObservationShape => false
    | None => false
    end.

  Definition wrapper_report_with_facts
      (wrapper : DovetailRhoWrapper)
      (backend : Backend)
      (facts : SeedFactsState) : bool :=
    match facts with
    | SeedFactsPresent => false
    | NoSeedFacts =>
        match backend with
        | RhoMachine => wrapper_rho_report_runs wrapper
        | Dovetail => wrapper_dovetail_report_runs wrapper
        | Ascent => false
        end
    end.

  Theorem wrapper_default_backend_is_rho : forall wrapper,
    wrapper_default_backend wrapper = RhoMachine.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_rho : forall wrapper,
    wrapper_supports wrapper RhoMachine = true.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_dovetail_intermediate : forall wrapper,
    wrapper_supports wrapper Dovetail = true.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_rejects_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros wrapper backend.
    destruct backend; reflexivity.
  Qed.

  Theorem wrapper_capabilities_are_rho_default_then_dovetail_intermediate :
    forall wrapper,
      wrapper_runtime_capabilities wrapper =
      [{| capability_backend := RhoMachine;
          capability_is_default := true |};
       {| capability_backend := Dovetail;
          capability_is_default := false |}].
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_rho_report_requires_planned_backend : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    planned_rho_backend wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper); simpl in Hrun.
    - reflexivity.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_rho_report_requires_matching_language : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    plan_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  Theorem wrapper_rho_report_requires_dovetail_available : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_available wrapper = true.
  Proof.
    intros [planned same_language available completeness well_formed invocation] Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho,
      dovetail_report_checked in Hrun.
    destruct planned;
      destruct same_language;
      destruct available;
      destruct completeness;
      destruct well_formed;
      destruct invocation;
      simpl in Hrun;
      try discriminate Hrun;
      reflexivity.
  Qed.

  Theorem wrapper_rho_report_requires_complete_dovetail : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_completeness wrapper = Complete.
  Proof.
    intros [planned same_language available completeness well_formed invocation] Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho,
      dovetail_report_checked in Hrun.
    destruct planned;
      destruct same_language;
      destruct available;
      destruct completeness;
      destruct well_formed;
      destruct invocation;
      simpl in Hrun;
      try discriminate Hrun;
      reflexivity.
  Qed.

  Theorem wrapper_rho_report_requires_well_formed_dovetail : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_well_formed wrapper = true.
  Proof.
    intros [planned same_language available completeness well_formed invocation] Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho,
      dovetail_report_checked in Hrun.
    destruct planned;
      destruct same_language;
      destruct available;
      destruct completeness;
      destruct well_formed;
      destruct invocation;
      simpl in Hrun;
      try discriminate Hrun;
      reflexivity.
  Qed.

  Theorem wrapper_rho_report_requires_total_invocation_after_dovetail :
    forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    invocation_total_after_dovetail wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    destruct (wrapper_installs_rho wrapper);
      destruct (dovetail_report_checked wrapper);
      simpl in Hrun;
      try exact Hrun;
      discriminate Hrun.
  Qed.

  Theorem wrapper_rho_report_requires_checked_dovetail : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_checked wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    destruct (wrapper_installs_rho wrapper);
      destruct (dovetail_report_checked wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  Theorem checked_dovetail_report_shape_is_dovetail_report : forall wrapper,
    wrapper_dovetail_report_runs wrapper = true ->
    wrapper_report_shape wrapper Dovetail = Some DovetailReportShape.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_report_shape.
    rewrite Hrun. reflexivity.
  Qed.

  Theorem rho_default_report_shape_is_observation : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    wrapper_report_shape wrapper (wrapper_default_backend wrapper) =
      Some ObservationShape.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_backend, wrapper_report_shape.
    rewrite Hrun. reflexivity.
  Qed.

  Theorem wrapper_default_is_not_ascent_compat : forall wrapper,
    wrapper_default_ascent_compat wrapper = false.
  Proof.
    intros wrapper.
    unfold wrapper_default_ascent_compat, wrapper_default_backend,
      wrapper_report_shape, wrapper_rho_report_runs, wrapper_installs_rho,
      dovetail_report_checked, completeness_is_complete.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      destruct (dovetail_report_available wrapper);
      destruct (dovetail_report_completeness wrapper);
      destruct (dovetail_report_well_formed wrapper);
      destruct (invocation_total_after_dovetail wrapper);
      reflexivity.
  Qed.

  Theorem bounded_dovetail_blocks_dovetail_and_rho :
    forall planned same_language available well_formed invocation,
      let wrapper :=
        {| planned_rho_backend := planned;
           plan_matches_language := same_language;
           dovetail_report_available := available;
           dovetail_report_completeness := BoundedByCycleCut;
           dovetail_report_well_formed := well_formed;
           invocation_total_after_dovetail := invocation |} in
      wrapper_dovetail_report_runs wrapper = false /\
      wrapper_rho_report_runs wrapper = false.
  Proof.
    intros planned same_language available well_formed invocation.
    simpl.
    destruct planned;
      destruct same_language;
      destruct available;
      destruct well_formed;
      destruct invocation;
      split;
      reflexivity.
  Qed.

  Theorem malformed_dovetail_blocks_dovetail_and_rho :
    forall planned same_language available completeness invocation,
      let wrapper :=
        {| planned_rho_backend := planned;
           plan_matches_language := same_language;
           dovetail_report_available := available;
           dovetail_report_completeness := completeness;
           dovetail_report_well_formed := false;
           invocation_total_after_dovetail := invocation |} in
      wrapper_dovetail_report_runs wrapper = false /\
      wrapper_rho_report_runs wrapper = false.
  Proof.
    intros planned same_language available completeness invocation.
    simpl.
    destruct planned;
      destruct same_language;
      destruct available;
      destruct completeness;
      destruct invocation;
      split;
      reflexivity.
  Qed.

  Theorem empty_seeded_facts_match_selected_backend : forall wrapper backend,
    wrapper_report_with_facts wrapper backend NoSeedFacts =
      match backend with
      | RhoMachine => wrapper_rho_report_runs wrapper
      | Dovetail => wrapper_dovetail_report_runs wrapper
      | Ascent => false
      end.
  Proof. intros wrapper backend. destruct backend; reflexivity. Qed.

  Theorem seeded_facts_block_production_backends : forall wrapper backend,
    wrapper_report_with_facts wrapper backend SeedFactsPresent = false.
  Proof. intros wrapper backend. destruct backend; reflexivity. Qed.

End DovetailRhoLanguageBackendWrapper.
