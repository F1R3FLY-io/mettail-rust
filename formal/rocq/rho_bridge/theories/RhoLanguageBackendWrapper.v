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

From Stdlib Require Import Bool.

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

  Definition wrapper_default_backend (_wrapper : RhoWrapper) : Backend :=
    RhoMachine.

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
