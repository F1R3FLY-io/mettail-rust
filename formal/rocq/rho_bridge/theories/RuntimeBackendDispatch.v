(*
 * RuntimeBackendDispatch: fail-closed backend selection for generated
 * MeTTaIL languages.
 *
 * The Rust trait `mettail_runtime::Language` exposes an optional selected
 * `RuntimeBackend` query. Generated languages may advertise `Ascent` as the
 * transition oracle default until a Dovetail/Rho flip gate installs a
 * different backend, but a concrete language value with no selected default
 * returns `None` and must not silently fabricate an Ascent fallback.
 * Requested backend selection must also fail closed when the requested backend
 * is absent.
 * A selected non-Ascent backend may run through the report API while still
 * being rejected by the legacy AscentResults compatibility surface.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

Section RuntimeBackendDispatch.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive OutputShape : Type :=
  | AscentResultsShape
  | DovetailReportShape
  | ObservationReportShape.

  Record BackendState : Type := {
    ascent_installed : bool;
    dovetail_installed : bool;
    rho_machine_installed : bool;
    default_selected : bool;
    default_backend : Backend;
    default_output_shape : OutputShape
  }.

  Definition backend_installed (state : BackendState) (backend : Backend) : bool :=
    match backend with
    | Ascent => ascent_installed state
    | Dovetail => dovetail_installed state
    | RhoMachine => rho_machine_installed state
    end.

  Definition selected_default_backend (state : BackendState) : option Backend :=
    if default_selected state
    then Some (default_backend state)
    else None.

  Definition can_run_with_backend (state : BackendState) (backend : Backend) : bool :=
    backend_installed state backend.

  Definition can_run_default_backend (state : BackendState) : bool :=
    default_selected state && can_run_with_backend state (default_backend state).

  Definition output_shape_matches_backend
      (backend : Backend) (shape : OutputShape) : bool :=
    match backend, shape with
    | Ascent, AscentResultsShape => true
    | Dovetail, DovetailReportShape => true
    | RhoMachine, ObservationReportShape => true
    | _, _ => false
    end.

  Definition can_run_default_backend_report (state : BackendState) : bool :=
    can_run_default_backend state &&
    output_shape_matches_backend (default_backend state) (default_output_shape state).

  Definition can_run_default_ascent_compat (state : BackendState) : bool :=
    can_run_default_backend_report state &&
    match default_output_shape state with
    | AscentResultsShape => true
    | DovetailReportShape => false
    | ObservationReportShape => false
    end.

  Definition generated_legacy_state : BackendState :=
    {|
      ascent_installed := true;
      dovetail_installed := false;
      rho_machine_installed := false;
      default_selected := true;
      default_backend := Ascent;
      default_output_shape := AscentResultsShape
    |}.

  Theorem generated_legacy_default_runs :
    can_run_default_backend generated_legacy_state = true.
  Proof. reflexivity. Qed.

  Theorem generated_legacy_default_report_runs :
    can_run_default_backend_report generated_legacy_state = true.
  Proof. reflexivity. Qed.

  Theorem generated_legacy_default_ascent_compat_runs :
    can_run_default_ascent_compat generated_legacy_state = true.
  Proof. reflexivity. Qed.

  Theorem selected_default_query_returns_backend : forall state,
    default_selected state = true ->
    selected_default_backend state = Some (default_backend state).
  Proof.
    intros state Hselected.
    unfold selected_default_backend.
    rewrite Hselected.
    reflexivity.
  Qed.

  Theorem unselected_default_query_returns_none : forall state,
    default_selected state = false ->
    selected_default_backend state = None.
  Proof.
    intros state Hunselected.
    unfold selected_default_backend.
    rewrite Hunselected.
    reflexivity.
  Qed.

  Theorem unselected_default_does_not_fabricate_ascent : forall state,
    default_selected state = false ->
    selected_default_backend state <> Some Ascent.
  Proof.
    intros state Hunselected Hfabricated.
    rewrite (unselected_default_query_returns_none state Hunselected) in Hfabricated.
    discriminate Hfabricated.
  Qed.

  Theorem requested_dovetail_absent_blocks : forall state,
    dovetail_installed state = false ->
    can_run_with_backend state Dovetail = false.
  Proof.
    intros state Habsent. unfold can_run_with_backend, backend_installed.
    exact Habsent.
  Qed.

  Theorem requested_rho_absent_blocks : forall state,
    rho_machine_installed state = false ->
    can_run_with_backend state RhoMachine = false.
  Proof.
    intros state Habsent. unfold can_run_with_backend, backend_installed.
    exact Habsent.
  Qed.

  Theorem default_backend_requires_installation : forall state,
    default_selected state = true ->
    can_run_default_backend state = true <->
    backend_installed state (default_backend state) = true.
  Proof.
    intros state Hselected.
    unfold can_run_default_backend, can_run_with_backend.
    rewrite Hselected.
    simpl.
    split; intro H; exact H.
  Qed.

  Theorem absent_default_blocks : forall state,
    backend_installed state (default_backend state) = false ->
    can_run_default_backend state = false.
  Proof.
    intros state Habsent.
    unfold can_run_default_backend, can_run_with_backend.
    rewrite Habsent.
    destruct (default_selected state); reflexivity.
  Qed.

  Theorem unselected_default_blocks : forall state,
    default_selected state = false ->
    can_run_default_backend state = false.
  Proof.
    intros state Hunselected.
    unfold can_run_default_backend.
    rewrite Hunselected.
    reflexivity.
  Qed.

  Theorem unselected_default_report_blocks : forall state,
    default_selected state = false ->
    can_run_default_backend_report state = false /\
    can_run_default_ascent_compat state = false.
  Proof.
    intros state Hunselected.
    split.
    - unfold can_run_default_backend_report.
      rewrite (unselected_default_blocks state Hunselected).
      reflexivity.
    - unfold can_run_default_ascent_compat, can_run_default_backend_report.
      rewrite (unselected_default_blocks state Hunselected).
      reflexivity.
  Qed.

  Theorem dovetail_default_without_installation_blocks : forall ascent rho,
    can_run_default_backend
      {| ascent_installed := ascent;
         dovetail_installed := false;
         rho_machine_installed := rho;
         default_selected := true;
         default_backend := Dovetail;
         default_output_shape := DovetailReportShape |} = false.
  Proof. reflexivity. Qed.

  Theorem installed_dovetail_default_report_runs :
    can_run_default_backend_report
      {| ascent_installed := true;
         dovetail_installed := true;
         rho_machine_installed := false;
         default_selected := true;
         default_backend := Dovetail;
         default_output_shape := DovetailReportShape |} = true.
  Proof. reflexivity. Qed.

  Theorem installed_dovetail_default_is_not_ascent_compat :
    can_run_default_ascent_compat
      {| ascent_installed := true;
         dovetail_installed := true;
         rho_machine_installed := false;
         default_selected := true;
         default_backend := Dovetail;
         default_output_shape := DovetailReportShape |} = false.
  Proof. reflexivity. Qed.

  Theorem dovetail_default_with_ascent_shape_is_rejected : forall ascent rho,
    can_run_default_backend_report
      {| ascent_installed := ascent;
         dovetail_installed := true;
         rho_machine_installed := rho;
         default_selected := true;
         default_backend := Dovetail;
         default_output_shape := AscentResultsShape |} = false.
  Proof. reflexivity. Qed.

  Theorem dovetail_default_with_observation_shape_is_rejected : forall ascent rho,
    can_run_default_backend_report
      {| ascent_installed := ascent;
         dovetail_installed := true;
         rho_machine_installed := rho;
         default_selected := true;
         default_backend := Dovetail;
         default_output_shape := ObservationReportShape |} = false.
  Proof. reflexivity. Qed.

  Theorem rho_default_without_installation_blocks : forall ascent dovetail,
    can_run_default_backend
      {| ascent_installed := ascent;
         dovetail_installed := dovetail;
         rho_machine_installed := false;
         default_selected := true;
         default_backend := RhoMachine;
         default_output_shape := ObservationReportShape |} = false.
  Proof. reflexivity. Qed.

  Theorem installed_rho_default_report_runs :
    can_run_default_backend_report
      {| ascent_installed := true;
         dovetail_installed := false;
         rho_machine_installed := true;
         default_selected := true;
         default_backend := RhoMachine;
         default_output_shape := ObservationReportShape |} = true.
  Proof. reflexivity. Qed.

  Theorem installed_rho_default_is_not_ascent_compat :
    can_run_default_ascent_compat
      {| ascent_installed := true;
         dovetail_installed := false;
         rho_machine_installed := true;
         default_selected := true;
         default_backend := RhoMachine;
         default_output_shape := ObservationReportShape |} = false.
  Proof. reflexivity. Qed.

  Theorem rho_default_with_ascent_shape_is_rejected : forall ascent dovetail,
    can_run_default_backend_report
      {| ascent_installed := ascent;
         dovetail_installed := dovetail;
         rho_machine_installed := true;
         default_selected := true;
         default_backend := RhoMachine;
         default_output_shape := AscentResultsShape |} = false.
  Proof. reflexivity. Qed.

  Theorem rho_default_with_dovetail_shape_is_rejected : forall ascent dovetail,
    can_run_default_backend_report
      {| ascent_installed := ascent;
         dovetail_installed := dovetail;
         rho_machine_installed := true;
         default_selected := true;
         default_backend := RhoMachine;
         default_output_shape := DovetailReportShape |} = false.
  Proof. reflexivity. Qed.

End RuntimeBackendDispatch.
