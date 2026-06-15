(*
 * RuntimeBackendDispatch: fail-closed backend selection for generated
 * MeTTaIL languages.
 *
 * The Rust trait `mettail_runtime::Language` exposes an optional selected
 * `RuntimeBackend` query. The base metadata trait advertises no backend unless
 * the implementation explicitly returns one. Raw generated languages advertise
 * no production backend by default; Dovetail/Rho production defaults are
 * installed by checked wrappers. The legacy Ascent runner is modeled as an
 * explicit reference-oracle capability, but production report dispatch never
 * selects or executes Ascent.
 * Requested backend selection must also fail closed when the requested backend
 * is absent.
 * A selected backend runs through the report API; the production trait no
 * longer exposes a generic AscentResults-shaped backend/default compatibility
 * surface.
 * The production runtime trait surface also excludes the historical CEK
 * decomposition hook: Dovetail/Rho execution is represented by checked reports
 * and Rho observations, not by language-generated CEK frames.
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

  Definition can_request_backend_report (state : BackendState) (backend : Backend) : bool :=
    match backend with
    | Ascent => false
    | Dovetail | RhoMachine => backend_installed state backend
    end.

  Definition can_select_default_backend (state : BackendState) : bool :=
    default_selected state && can_request_backend_report state (default_backend state).

  Definition output_shape_matches_backend
      (backend : Backend) (shape : OutputShape) : bool :=
    match backend, shape with
    | Ascent, AscentResultsShape => true
    | Dovetail, DovetailReportShape => true
    | RhoMachine, ObservationReportShape => true
    | _, _ => false
    end.

  Definition can_run_default_backend_report (state : BackendState) : bool :=
    can_select_default_backend state &&
    output_shape_matches_backend (default_backend state) (default_output_shape state).

  Definition explicit_ascent_oracle_state : BackendState :=
    {|
      ascent_installed := true;
      dovetail_installed := false;
      rho_machine_installed := false;
      default_selected := true;
      default_backend := Ascent;
      default_output_shape := AscentResultsShape
    |}.

  Theorem explicit_ascent_oracle_not_production_default :
    can_select_default_backend explicit_ascent_oracle_state = false.
  Proof. reflexivity. Qed.

  Theorem explicit_ascent_oracle_report_rejected :
    can_run_default_backend_report explicit_ascent_oracle_state = false.
  Proof. reflexivity. Qed.

  Record GeneratedLanguageBuild : Type := {
    oracle_ascent_feature_enabled : bool
  }.

  Definition generated_ascent_oracle_compiled
      (build : GeneratedLanguageBuild) : bool :=
    oracle_ascent_feature_enabled build.

  Definition generated_ascent_oracle_callable
      (build : GeneratedLanguageBuild) : bool :=
    generated_ascent_oracle_compiled build.

  Definition raw_generated_language_state
      (build : GeneratedLanguageBuild) : BackendState :=
    {|
      ascent_installed := generated_ascent_oracle_compiled build;
      dovetail_installed := false;
      rho_machine_installed := false;
      default_selected := false;
      default_backend := Ascent;
      default_output_shape := AscentResultsShape
    |}.

  Definition no_oracle_generated_build : GeneratedLanguageBuild :=
    {| oracle_ascent_feature_enabled := false |}.

  Definition oracle_generated_build : GeneratedLanguageBuild :=
    {| oracle_ascent_feature_enabled := true |}.

  Theorem no_oracle_build_compiles_no_ascent_oracle :
    generated_ascent_oracle_compiled no_oracle_generated_build = false.
  Proof. reflexivity. Qed.

  Theorem oracle_build_compiles_reference_oracle :
    generated_ascent_oracle_compiled oracle_generated_build = true.
  Proof. reflexivity. Qed.

  Theorem no_oracle_build_has_no_callable_ascent_oracle :
    generated_ascent_oracle_callable no_oracle_generated_build = false.
  Proof. reflexivity. Qed.

  Theorem raw_generated_language_selects_no_default : forall build,
    selected_default_backend (raw_generated_language_state build) = None.
  Proof. intros build. destruct build. reflexivity. Qed.

  Theorem raw_generated_language_runs_no_default_report : forall build,
    can_run_default_backend_report (raw_generated_language_state build) = false.
  Proof. intros build. destruct build. reflexivity. Qed.

  Theorem oracle_feature_does_not_enable_production_ascent_request : forall build,
    can_request_backend_report (raw_generated_language_state build) Ascent = false.
  Proof. intros build. destruct build. reflexivity. Qed.

  Theorem oracle_feature_does_not_change_production_default :
    can_run_default_backend_report
      (raw_generated_language_state no_oracle_generated_build) =
    can_run_default_backend_report
      (raw_generated_language_state oracle_generated_build).
  Proof. reflexivity. Qed.

  Definition empty_metadata_state : BackendState :=
    {|
      ascent_installed := false;
      dovetail_installed := false;
      rho_machine_installed := false;
      default_selected := false;
      default_backend := Ascent;
      default_output_shape := AscentResultsShape
    |}.

  Theorem empty_metadata_selects_no_default :
    selected_default_backend empty_metadata_state = None.
  Proof. reflexivity. Qed.

  Theorem empty_metadata_runs_no_default_report :
    can_run_default_backend_report empty_metadata_state = false.
  Proof. reflexivity. Qed.

  Theorem empty_metadata_does_not_fabricate_ascent :
    selected_default_backend empty_metadata_state <> Some Ascent.
  Proof. discriminate. Qed.

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
    can_request_backend_report state Dovetail = false.
  Proof.
    intros state Habsent. unfold can_request_backend_report, backend_installed.
    exact Habsent.
  Qed.

  Theorem requested_rho_absent_blocks : forall state,
    rho_machine_installed state = false ->
    can_request_backend_report state RhoMachine = false.
  Proof.
    intros state Habsent. unfold can_request_backend_report, backend_installed.
    exact Habsent.
  Qed.

  Theorem requested_ascent_absent_blocks : forall state,
    ascent_installed state = false ->
    can_request_backend_report state Ascent = false.
  Proof. intros state _Habsent. reflexivity. Qed.

  Theorem requested_ascent_always_blocks : forall state,
    can_request_backend_report state Ascent = false.
  Proof. intros state. reflexivity. Qed.

  Theorem default_backend_requires_installation : forall state,
    default_selected state = true ->
    default_backend state <> Ascent ->
    can_select_default_backend state = true <->
    backend_installed state (default_backend state) = true.
  Proof.
    intros state Hselected Hnot_ascent.
    unfold can_select_default_backend, can_request_backend_report.
    rewrite Hselected.
    destruct (default_backend state); try contradiction; simpl;
      split; intro H; exact H.
  Qed.

  Theorem absent_default_blocks : forall state,
    backend_installed state (default_backend state) = false ->
    can_select_default_backend state = false.
  Proof.
    intros state Habsent.
    unfold can_select_default_backend, can_request_backend_report.
    destruct (default_selected state); [| reflexivity].
    destruct (default_backend state) eqn:Hbackend; simpl; [reflexivity | |].
    - simpl in Habsent. exact Habsent.
    - simpl in Habsent. exact Habsent.
  Qed.

  Theorem unselected_default_blocks : forall state,
    default_selected state = false ->
    can_select_default_backend state = false.
  Proof.
    intros state Hunselected.
    unfold can_select_default_backend.
    rewrite Hunselected.
    reflexivity.
  Qed.

  Theorem unselected_default_report_blocks : forall state,
    default_selected state = false ->
    can_run_default_backend_report state = false.
  Proof.
    intros state Hunselected.
    unfold can_run_default_backend_report.
    rewrite (unselected_default_blocks state Hunselected).
    reflexivity.
  Qed.

  Theorem dovetail_default_without_installation_blocks : forall ascent rho,
    can_select_default_backend
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
    can_select_default_backend
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

  Record RuntimeTraitSurface : Type := {
    surface_state : BackendState;
    cek_runtime_hook_exposed : bool
  }.

  Definition report_only_runtime_surface (surface : RuntimeTraitSurface) : bool :=
    negb (cek_runtime_hook_exposed surface).

  Definition dovetail_rho_report_surface : RuntimeTraitSurface :=
    {|
      surface_state :=
        {| ascent_installed := false;
           dovetail_installed := true;
           rho_machine_installed := true;
           default_selected := true;
           default_backend := RhoMachine;
           default_output_shape := ObservationReportShape |};
      cek_runtime_hook_exposed := false
    |}.

  Theorem dovetail_rho_report_surface_exposes_no_cek_hook :
    report_only_runtime_surface dovetail_rho_report_surface = true.
  Proof. reflexivity. Qed.

  Theorem report_only_surface_has_no_cek_runtime_hook : forall surface,
    report_only_runtime_surface surface = true ->
    cek_runtime_hook_exposed surface = false.
  Proof.
    intros surface Hreport_only.
    unfold report_only_runtime_surface in Hreport_only.
    destruct (cek_runtime_hook_exposed surface); simpl in Hreport_only; congruence.
  Qed.

  Theorem dovetail_rho_surface_still_runs_report_backend :
    can_run_default_backend_report (surface_state dovetail_rho_report_surface) = true.
  Proof. reflexivity. Qed.

End RuntimeBackendDispatch.
