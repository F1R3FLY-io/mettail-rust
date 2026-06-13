(*
 * RuntimeBackendDispatch: fail-closed backend selection for generated
 * MeTTaIL languages.
 *
 * The Rust trait `mettail_runtime::Language` exposes an explicit
 * `RuntimeBackend` selector.  Generated languages inherit `Ascent` as the
 * default until a Dovetail/Rho flip gate installs a different backend.  The
 * selector must not silently fall back to Ascent when a requested backend is
 * absent.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

Section RuntimeBackendDispatch.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Record BackendState : Type := {
    ascent_installed : bool;
    dovetail_installed : bool;
    rho_machine_installed : bool;
    default_backend : Backend
  }.

  Definition backend_installed (state : BackendState) (backend : Backend) : bool :=
    match backend with
    | Ascent => ascent_installed state
    | Dovetail => dovetail_installed state
    | RhoMachine => rho_machine_installed state
    end.

  Definition can_run_with_backend (state : BackendState) (backend : Backend) : bool :=
    backend_installed state backend.

  Definition can_run_default_backend (state : BackendState) : bool :=
    can_run_with_backend state (default_backend state).

  Definition generated_legacy_state : BackendState :=
    {|
      ascent_installed := true;
      dovetail_installed := false;
      rho_machine_installed := false;
      default_backend := Ascent
    |}.

  Theorem generated_legacy_default_runs :
    can_run_default_backend generated_legacy_state = true.
  Proof. reflexivity. Qed.

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
    can_run_default_backend state = true <->
    backend_installed state (default_backend state) = true.
  Proof.
    intros state. unfold can_run_default_backend, can_run_with_backend.
    split; intro H; exact H.
  Qed.

  Theorem absent_default_blocks : forall state,
    backend_installed state (default_backend state) = false ->
    can_run_default_backend state = false.
  Proof.
    intros state Habsent.
    unfold can_run_default_backend, can_run_with_backend.
    exact Habsent.
  Qed.

  Theorem dovetail_default_without_installation_blocks : forall ascent rho,
    can_run_default_backend
      {| ascent_installed := ascent;
         dovetail_installed := false;
         rho_machine_installed := rho;
         default_backend := Dovetail |} = false.
  Proof. reflexivity. Qed.

  Theorem rho_default_without_installation_blocks : forall ascent dovetail,
    can_run_default_backend
      {| ascent_installed := ascent;
         dovetail_installed := dovetail;
         rho_machine_installed := false;
         default_backend := RhoMachine |} = false.
  Proof. reflexivity. Qed.

End RuntimeBackendDispatch.
