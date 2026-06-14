(*
 * RhoLanguageBackendWrapper: a generated MeTTaIL language can be wrapped with
 * a flip-gated PlannedRhoBackend without changing the generated crate.
 *
 * Rust image:
 *   - `RhoRuntimeBackedLanguage<L, F>` delegates parsing, environments,
 *     type inference, Ascent execution, and non-Rho backend requests to `L`.
 *   - The wrapper selects `RuntimeBackend::RhoMachine` as its default backend.
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
    capability_is_default : bool;
    capability_has_evidence : bool
  }.

  Record InnerLanguage : Type := {
    inner_supports_ascent : bool;
    inner_supports_dovetail : bool
  }.

  Record RhoWrapper : Type := {
    wrapped_inner : InnerLanguage;
    planned_rho_backend : bool;
    invocation_total : bool
  }.

  Definition inner_supports
      (inner : InnerLanguage) (backend : Backend) : bool :=
    match backend with
    | Ascent => inner_supports_ascent inner
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
    (if inner_supports_ascent inner
     then [{| capability_backend := Ascent;
              capability_is_default := false;
              capability_has_evidence := true |}]
     else []) ++
    (if inner_supports_dovetail inner
     then [{| capability_backend := Dovetail;
              capability_is_default := false;
              capability_has_evidence := true |}]
     else []).

  Definition wrapper_default_backend (_wrapper : RhoWrapper) : Backend :=
    RhoMachine.

  Definition wrapper_runtime_capabilities
      (wrapper : RhoWrapper) : list RuntimeBackendCapability :=
    (if planned_rho_backend wrapper
     then [{| capability_backend := RhoMachine;
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
      (wrapper : RhoWrapper) (backend : Backend) : bool :=
    match backend with
    | RhoMachine => planned_rho_backend wrapper
    | other => inner_supports (wrapped_inner wrapper) other
    end.

  Definition wrapper_default_report_runs (wrapper : RhoWrapper) : bool :=
    planned_rho_backend wrapper && invocation_total wrapper.

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

  Theorem wrapper_supports_rho_iff_planned : forall wrapper,
    wrapper_supports wrapper RhoMachine = planned_rho_backend wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros [[supports_ascent supports_dovetail] planned invocation] backend.
    destruct backend;
      destruct planned;
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
             invocation_total := invocation |} =
        {| capability_backend := RhoMachine;
           capability_is_default := true;
           capability_has_evidence := true |} :: tail.
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
    intros [[supports_ascent supports_dovetail] planned invocation].
    destruct planned;
      destruct supports_ascent;
      destruct supports_dovetail;
      repeat constructor.
  Qed.

  Theorem wrapper_delegates_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent =
      inner_supports_ascent (wrapped_inner wrapper).
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
    destruct (planned_rho_backend wrapper); simpl in Hrun.
    - reflexivity.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_default_report_requires_total_invocation : forall wrapper,
    wrapper_default_report_runs wrapper = true ->
    invocation_total wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_report_runs in Hrun.
    destruct (planned_rho_backend wrapper); simpl in Hrun.
    - exact Hrun.
    - discriminate Hrun.
  Qed.

  Theorem planned_total_wrapper_default_report_runs : forall inner,
    wrapper_default_report_runs
      {| wrapped_inner := inner;
         planned_rho_backend := true;
         invocation_total := true |} = true.
  Proof. intros inner. reflexivity. Qed.

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
    destruct (planned_rho_backend wrapper);
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
