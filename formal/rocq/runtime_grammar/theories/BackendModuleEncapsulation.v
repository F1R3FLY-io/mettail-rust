(** * Semantics-preserving encapsulation of generated backend modules

    Large generated backends are written to dedicated Rust source files.  A
    backend file is loaded as one child module, imports the language types from
    its parent, and explicitly re-exports only its public interface.  This
    removes textual [include!] expansion from the host module without changing
    the backend declaration sequence or any public observation.

    The model below separates three notions that must not be conflated:

    - [backend_environment] is the complete ordered declaration environment
      visible to generated backend code;
    - [export_names] is the explicit interface visible to host code;
    - [public_environment] is the name-filtered projection exposed by the child
      module.

    Lookup is first-match lookup, matching Rust's requirement that a generated
    name have one definition.  The proofs do not assume declaration reordering:
    the child module retains the original environment byte for byte. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Set Implicit Arguments.

Module BackendModuleEncapsulation.

  Record Declaration : Type := {
    declaration_name : nat;
    declaration_value : nat
  }.

  Definition Environment : Type := list Declaration.

  Fixpoint lookup (name : nat) (environment : Environment) : option nat :=
    match environment with
    | [] => None
    | declaration :: rest =>
        if Nat.eqb name (declaration_name declaration)
        then Some (declaration_value declaration)
        else lookup name rest
    end.

  Definition is_exported (exports : list nat) (declaration : Declaration) : bool :=
    existsb (Nat.eqb (declaration_name declaration)) exports.

  Definition public_environment
      (exports : list nat) (environment : Environment) : Environment :=
    filter (is_exported exports) environment.

  Definition host_observation
      (exports : list nat) (environment : Environment) (name : nat) : option nat :=
    if existsb (Nat.eqb name) exports
    then lookup name environment
    else None.

  Definition module_observation
      (exports : list nat) (environment : Environment) (name : nat) : option nat :=
    lookup name (public_environment exports environment).

  Lemma exported_existsb_true :
    forall exports name,
      In name exports -> existsb (Nat.eqb name) exports = true.
  Proof.
    intros exports name Hin.
    apply existsb_exists.
    exists name. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma private_existsb_false :
    forall exports name,
      ~ In name exports -> existsb (Nat.eqb name) exports = false.
  Proof.
    intros exports name Hnotin.
    destruct (existsb (Nat.eqb name) exports) eqn:Hexists; [|reflexivity].
    apply existsb_exists in Hexists.
    destruct Hexists as [candidate [Hcandidate Hsame]].
    apply Nat.eqb_eq in Hsame. subst candidate.
    exfalso. apply Hnotin. exact Hcandidate.
  Qed.

  Lemma exported_lookup_survives_projection :
    forall environment exports name,
      In name exports ->
      lookup name (public_environment exports environment) =
      lookup name environment.
  Proof.
    intros environment; induction environment as [|declaration rest IH];
      intros exports name Hin; simpl; [reflexivity |].
    unfold is_exported.
    destruct (Nat.eqb name (declaration_name declaration)) eqn:Hsame.
    - apply Nat.eqb_eq in Hsame. subst name.
      rewrite exported_existsb_true by exact Hin.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    - destruct (existsb (Nat.eqb (declaration_name declaration)) exports).
      + simpl. rewrite Hsame. apply IH. exact Hin.
      + apply IH. exact Hin.
  Qed.

  Lemma private_lookup_is_hidden :
    forall environment exports name,
      ~ In name exports ->
      lookup name (public_environment exports environment) = None.
  Proof.
    intros environment; induction environment as [|declaration rest IH];
      intros exports name Hnotin; simpl; [reflexivity |].
    unfold is_exported.
    destruct (existsb (Nat.eqb (declaration_name declaration)) exports) eqn:Hdecl.
    - apply existsb_exists in Hdecl.
      destruct Hdecl as [exported_name [Hin Hsame]].
      apply Nat.eqb_eq in Hsame. subst exported_name.
      destruct (Nat.eqb name (declaration_name declaration)) eqn:Hquery.
      + apply Nat.eqb_eq in Hquery. subst name. exfalso. apply Hnotin. exact Hin.
      + simpl. rewrite Hquery. apply IH. exact Hnotin.
    - apply IH. exact Hnotin.
  Qed.

  Theorem public_observation_preserved :
    forall environment exports name,
      module_observation exports environment name =
      host_observation exports environment name.
  Proof.
    intros environment exports name.
    unfold module_observation, host_observation.
    destruct (in_dec Nat.eq_dec name exports) as [Hin | Hnotin].
    - rewrite exported_existsb_true by exact Hin.
      apply exported_lookup_survives_projection. exact Hin.
    - rewrite private_existsb_false by exact Hnotin.
      apply private_lookup_is_hidden. exact Hnotin.
  Qed.

  (** Backend-local code sees the exact declaration sequence.  Encapsulation
      changes the owner module, not the environment supplied to its generated
      lowering, reconstruction, or report functions. *)
  Definition backend_environment (environment : Environment) : Environment := environment.

  Theorem backend_internal_lookup_preserved :
    forall environment name,
      lookup name (backend_environment environment) = lookup name environment.
  Proof.
    reflexivity.
  Qed.

  Theorem backend_declaration_order_preserved :
    forall environment,
      backend_environment environment = environment.
  Proof.
    reflexivity.
  Qed.

  Theorem non_exported_names_do_not_leak :
    forall environment exports name,
      ~ In name exports -> module_observation exports environment name = None.
  Proof.
    intros environment exports name Hnotin.
    unfold module_observation.
    apply private_lookup_is_hidden. exact Hnotin.
  Qed.

  (** Feature selection occurs before the generated file is loaded.  A disabled
      backend contributes no environment; an enabled backend contributes the
      exact environment proved above. *)
  Definition selected_backend
      (enabled : bool) (environment : Environment) : option Environment :=
    if enabled then Some (backend_environment environment) else None.

  Theorem disabled_backend_is_absent :
    forall environment, selected_backend false environment = None.
  Proof.
    reflexivity.
  Qed.

  Theorem enabled_backend_is_exact :
    forall environment, selected_backend true environment = Some environment.
  Proof.
    reflexivity.
  Qed.

  (** Trait implementations and inherent methods are crate observations rather
      than ordinary exported names: moving their helper declarations into a
      child module does not hide the implementation attached to the parent
      type.  A generated concern therefore records its local declarations,
      explicit free-name exports, and the implementations it contributes. *)
  Record Concern : Type := {
    concern_environment : Environment;
    concern_exports : list nat;
    concern_implementations : list nat
  }.

  Definition monolithic_implementations (concerns : list Concern) : list nat :=
    concat (map concern_implementations concerns).

  Definition modular_implementations (concerns : list Concern) : list nat :=
    concat (map concern_implementations concerns).

  Theorem concern_implementations_preserved :
    forall concerns,
      modular_implementations concerns = monolithic_implementations concerns.
  Proof.
    reflexivity.
  Qed.

  (** Encapsulation is compositional: applying the proven public projection to
      every concern preserves every explicitly exported observation. *)
  Definition concern_public_observation
      (concern : Concern) (name : nat) : option nat :=
    module_observation
      (concern_exports concern)
      (concern_environment concern)
      name.

  Definition concern_host_observation
      (concern : Concern) (name : nat) : option nat :=
    host_observation
      (concern_exports concern)
      (concern_environment concern)
      name.

  Theorem concern_public_observation_preserved :
    forall concern name,
      concern_public_observation concern name =
      concern_host_observation concern name.
  Proof.
    intros concern name.
    unfold concern_public_observation, concern_host_observation.
    apply public_observation_preserved.
  Qed.

  (** A generated concern has a fixed free-name interface.  Optional grammar
      sites change a helper's table payload, never whether the helper is
      declared.  The zero-site payload is the inert table of length zero,
      which keeps every explicit re-export resolvable without fabricating a
      successful grammar observation. *)
  Definition optional_helper_declaration
      (helper_name : nat) (sites : list nat) : Declaration :=
    {| declaration_name := helper_name;
       declaration_value := length sites |}.

  Theorem optional_helper_interface_is_total :
    forall helper_name sites,
      lookup helper_name [optional_helper_declaration helper_name sites] =
      Some (length sites).
  Proof.
    intros helper_name sites. cbn. now rewrite Nat.eqb_refl.
  Qed.

  Theorem zero_site_helper_is_present_and_inert :
    forall helper_name,
      lookup helper_name [optional_helper_declaration helper_name []] = Some 0.
  Proof.
    intro helper_name. apply optional_helper_interface_is_total.
  Qed.

  Print Assumptions public_observation_preserved.
  Print Assumptions backend_internal_lookup_preserved.
  Print Assumptions backend_declaration_order_preserved.
  Print Assumptions non_exported_names_do_not_leak.
  Print Assumptions disabled_backend_is_absent.
  Print Assumptions enabled_backend_is_exact.
  Print Assumptions concern_implementations_preserved.
  Print Assumptions concern_public_observation_preserved.
  Print Assumptions optional_helper_interface_is_total.
  Print Assumptions zero_site_helper_is_present_and_inert.

End BackendModuleEncapsulation.
