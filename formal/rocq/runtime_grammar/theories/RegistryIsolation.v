From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Definition Name := nat.
Definition Fingerprint := nat.
Definition Parser := nat.

Record RegistryEntry : Type := {
  authoritative_spec : Fingerprint;
  cached_image : option Fingerprint
}.

Definition Registry := list (Name * RegistryEntry).
Definition StaticParsers := list (Name * Parser).

Record RuntimeState : Type := {
  static_parsers : StaticParsers;
  registry : Registry
}.

Fixpoint lookup_static (name : Name) (parsers : StaticParsers) : option Parser :=
  match parsers with
  | [] => None
  | (candidate, parser) :: rest =>
      if Nat.eqb name candidate then Some parser else lookup_static name rest
  end.

Definition cache_matches_authority (entry : RegistryEntry) : bool :=
  match cached_image entry with
  | None => false
  | Some fingerprint => Nat.eqb fingerprint (authoritative_spec entry)
  end.

Definition prepared_image (compile : Fingerprint -> Fingerprint) (entry : RegistryEntry)
  : Fingerprint :=
  if cache_matches_authority entry
  then match cached_image entry with
       | Some image => image
       | None => compile (authoritative_spec entry)
       end
  else compile (authoritative_spec entry).

Definition install_registry (state : RuntimeState) (entries : Registry) : RuntimeState :=
  {| static_parsers := static_parsers state;
     registry := entries |}.

Theorem cache_never_changes_authority :
  forall compile entry,
    cached_image entry = None \/
    cached_image entry <> Some (authoritative_spec entry) ->
    prepared_image compile entry = compile (authoritative_spec entry).
Proof.
  intros compile [authority cache] H. simpl in *.
  destruct cache as [image |].
  - destruct H as [H | H]; [discriminate |].
    unfold prepared_image, cache_matches_authority. simpl.
    destruct (Nat.eqb image authority) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst image. exfalso. apply H. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem matching_cache_is_reused :
  forall compile authority,
    prepared_image compile
      {| authoritative_spec := authority; cached_image := Some authority |} = authority.
Proof.
  intros compile authority. unfold prepared_image, cache_matches_authority. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem registry_installation_is_static_backend_inert :
  forall state entries name,
    lookup_static name (static_parsers (install_registry state entries)) =
    lookup_static name (static_parsers state).
Proof. reflexivity. Qed.

Inductive ModuleOrigin : Type := RegistryOrigin | FileSystemOrigin.

Definition origin_available (registry_ready filesystem_ready : bool) (origin : ModuleOrigin)
  : bool :=
  match origin with
  | RegistryOrigin => registry_ready
  | FileSystemOrigin => filesystem_ready
  end.

Theorem registry_origin_does_not_depend_on_filesystem :
  forall registry_ready first_filesystem_state second_filesystem_state,
    origin_available registry_ready first_filesystem_state RegistryOrigin =
    origin_available registry_ready second_filesystem_state RegistryOrigin.
Proof. reflexivity. Qed.

Print Assumptions cache_never_changes_authority.
Print Assumptions registry_installation_is_static_backend_inert.
Print Assumptions registry_origin_does_not_depend_on_filesystem.
