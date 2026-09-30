(** * Checked host-profile admission and publication lifecycle

    This independent boundary model does not implement a language parser,
    projection matcher, hash function, signature verifier, or native codec.
    Generated-definition provenance, publisher authentication, and native codec
    correctness are explicit obligations of supplied trusted checkers. Numeric
    commitments below are abstract identifiers, not cryptographic proofs.

    Exact structured profile identity is checked in addition to digest
    recomputation. Collision resistance on deployed canonical payloads remains
    an external cryptographic obligation; none of the lifecycle theorems infer
    payload equality from equal digests. Seals have an abstract type. Their
    secrecy/unforgeability and atomic registry snapshot access are external
    implementation obligations, not consequences of this model.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Module HostProfileLifecycle.

Inductive FieldRole := ReducibleChild | WithheldChild | OrderedChildren | NativeLeaf.

Record CheckedDefinition := definition {
  language_identity : nat;
  grammar_version : nat;
  definition_digest : nat;
  grammar_digest : nat;
  category_roster : list nat;
  constructor_roster : list nat
}.

Record AdapterLayout := layout {
  layout_definition : nat;
  layout_grammar : nat;
  semantic_key_abi : nat;
  field_roles : list FieldRole
}.

Record CodecIdentity := codec_identity {
  provider_identity : nat;
  provider_code_digest : nat;
  codec_abi : nat;
  provider_epoch : nat
}.

Record CodecProvider := provider {
  provider_contract : CodecIdentity;
  provider_layout : AdapterLayout;
  provider_executable : bool
}.

Record Profile := profile {
  profile_abi : nat;
  profile_definition : CheckedDefinition;
  profile_layout : AdapterLayout;
  profile_codec : CodecIdentity
}.

Record RawDescriptor := raw_descriptor {
  descriptor_payload : Profile;
  descriptor_digest : nat
}.

Inductive Origin := CompiledStartup | RegistryPublisher (publisher : nat).

Definition definition_eq_dec : forall x y : CheckedDefinition, {x = y} + {x <> y}.
Proof. decide equality; apply list_eq_dec || apply Nat.eq_dec; apply Nat.eq_dec. Defined.

Definition layout_eq_dec : forall x y : AdapterLayout, {x = y} + {x <> y}.
Proof. decide equality; try apply Nat.eq_dec. apply list_eq_dec. decide equality. Defined.

Definition codec_identity_eq_dec : forall x y : CodecIdentity, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition provider_eq_dec : forall x y : CodecProvider, {x = y} + {x <> y}.
Proof.
  decide equality; try apply Bool.bool_dec; try apply layout_eq_dec;
    apply codec_identity_eq_dec.
Defined.

Definition profile_eq_dec : forall x y : Profile, {x = y} + {x <> y}.
Proof.
  decide equality; try apply codec_identity_eq_dec; try apply layout_eq_dec;
    try apply definition_eq_dec; apply Nat.eq_dec.
Defined.

Definition equalb {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
           (x y : A) : bool := if dec x y then true else false.

Lemma equalb_true_iff : forall A dec (x y : A),
  equalb dec x y = true <-> x = y.
Proof.
  intros A dec x y. unfold equalb. destruct (dec x y); split;
    intros H; try reflexivity; try assumption; try discriminate; contradiction.
Qed.

Lemma equalb_refl : forall A dec (x : A), equalb dec x x = true.
Proof. intros. apply equalb_true_iff. reflexivity. Qed.

Definition derive_profile (abi : nat) (d : CheckedDefinition)
           (l : AdapterLayout) (p : CodecProvider) : Profile :=
  profile abi d l (provider_contract p).

(** Receiver and argument observations are separate. A codec obligation must
    preserve an inert receiver and the exact ordered argument sequence, not
    merely their cardinality or an unordered collection of children. *)
Record HostValue := host_value {
  withheld_receiver : nat;
  ordered_arguments : list nat;
  remaining_structure : list nat
}.

Section Admission.
Variable digest : Profile -> nat.
Variable generated_check : CheckedDefinition -> AdapterLayout -> bool.
Variable generated_provenance : CheckedDefinition -> AdapterLayout -> Prop.
Hypothesis generated_check_sound : forall d l,
  generated_check d l = true -> generated_provenance d l.

Variable authenticate : Origin -> Profile -> CodecIdentity -> bool.
Variable authenticated_origin : Origin -> Profile -> CodecIdentity -> Prop.
Hypothesis authenticate_sound : forall origin payload codec,
  authenticate origin payload codec = true ->
  authenticated_origin origin payload codec.

Variable encode : CodecProvider -> HostValue -> list nat.
Variable decode : CodecProvider -> list nat -> option HostValue.
Definition codec_correct (p : CodecProvider) : Prop :=
  forall value, decode p (encode p value) = Some value.
Variable codec_check : CodecProvider -> bool.
Hypothesis codec_check_sound : forall p,
  codec_check p = true -> codec_correct p.

(** These checkers are trusted inputs to the installation implementation.
    They are not Boolean assertions that an untrusted descriptor may supply. *)
Definition admission_okb (abi : nat) (d : CheckedDefinition)
           (l : AdapterLayout) (raw : RawDescriptor)
           (p : CodecProvider) (origin : Origin) : bool :=
  generated_check d l &&
  Nat.eqb (layout_definition l) (definition_digest d) &&
  Nat.eqb (layout_grammar l) (grammar_digest d) &&
  equalb layout_eq_dec (provider_layout p) l &&
  equalb profile_eq_dec (descriptor_payload raw) (derive_profile abi d l p) &&
  Nat.eqb (descriptor_digest raw) (digest (descriptor_payload raw)) &&
  provider_executable p && codec_check p &&
  authenticate origin (descriptor_payload raw) (provider_contract p).

Record AdmissionFacts abi d l raw p origin : Prop := admission_facts {
  admitted_provenance : generated_provenance d l;
  admitted_definition : layout_definition l = definition_digest d;
  admitted_grammar : layout_grammar l = grammar_digest d;
  admitted_layout : provider_layout p = l;
  admitted_exact_payload : descriptor_payload raw = derive_profile abi d l p;
  admitted_recomputed_digest : descriptor_digest raw = digest (descriptor_payload raw);
  admitted_executable : provider_executable p = true;
  admitted_codec_correct : codec_correct p;
  admitted_origin : authenticated_origin origin (descriptor_payload raw)
                     (provider_contract p)
}.

Theorem checked_admission_has_generated_provenance : forall abi d l raw p origin,
  admission_okb abi d l raw p origin = true ->
  AdmissionFacts abi d l raw p origin.
Proof.
  intros abi d l raw p origin H. unfold admission_okb in H.
  repeat rewrite andb_true_iff in H.
  constructor.
  - apply generated_check_sound. tauto.
  - apply Nat.eqb_eq. tauto.
  - apply Nat.eqb_eq. tauto.
  - apply (proj1 (equalb_true_iff _ layout_eq_dec _ _)). tauto.
  - apply (proj1 (equalb_true_iff _ profile_eq_dec _ _)). tauto.
  - apply Nat.eqb_eq. tauto.
  - tauto.
  - apply codec_check_sound. tauto.
  - apply authenticate_sound. tauto.
Qed.

Theorem admission_pins_every_identity_dimension : forall abi d l raw p origin,
  admission_okb abi d l raw p origin = true ->
  profile_abi (descriptor_payload raw) = abi /\
  grammar_version (profile_definition (descriptor_payload raw)) = grammar_version d /\
  definition_digest (profile_definition (descriptor_payload raw)) = definition_digest d /\
  grammar_digest (profile_definition (descriptor_payload raw)) = grammar_digest d /\
  field_roles (profile_layout (descriptor_payload raw)) = field_roles l /\
  semantic_key_abi (profile_layout (descriptor_payload raw)) = semantic_key_abi l /\
  profile_codec (descriptor_payload raw) = provider_contract p.
Proof.
  intros abi d l raw p origin H.
  pose proof (admitted_exact_payload _ _ _ _ _ _
    (checked_admission_has_generated_provenance _ _ _ _ _ _ H)) as Exact.
  rewrite Exact. unfold derive_profile. simpl. repeat split; reflexivity.
Qed.

Theorem changed_payload_is_refused_even_with_a_recomputed_digest :
  forall abi d l raw p origin,
  descriptor_payload raw <> derive_profile abi d l p ->
  admission_okb abi d l raw p origin = false.
Proof.
  intros abi d l raw p origin Different.
  destruct (admission_okb abi d l raw p origin) eqn:Checked; [|reflexivity].
  exfalso. apply Different.
  exact (admitted_exact_payload _ _ _ _ _ _
    (checked_admission_has_generated_provenance _ _ _ _ _ _ Checked)).
Qed.

Theorem unauthenticated_content_cannot_be_admitted : forall abi d l raw p origin,
  authenticate origin (descriptor_payload raw) (provider_contract p) = false ->
  admission_okb abi d l raw p origin = false.
Proof.
  intros abi d l raw p origin H. unfold admission_okb. now rewrite H, andb_false_r.
Qed.

Theorem admitted_codec_preserves_withheld_receiver_and_argument_order :
  forall abi d l raw p origin input output,
  admission_okb abi d l raw p origin = true ->
  decode p (encode p input) = Some output ->
  withheld_receiver output = withheld_receiver input /\
  ordered_arguments output = ordered_arguments input /\
  remaining_structure output = remaining_structure input.
Proof.
  intros abi d l raw p origin input output Admitted Decoded.
  pose proof (admitted_codec_correct _ _ _ _ _ _
    (checked_admission_has_generated_provenance _ _ _ _ _ _ Admitted)) as Correct.
  unfold codec_correct in Correct. rewrite Correct in Decoded.
  inversion Decoded; subst. repeat split; reflexivity.
Qed.

End Admission.

(** Collision freedom is stated only as a restricted external obligation.
    It is not proved from [nat] equality or asserted for all possible inputs.
    A real implementation requires canonical encoding and a cryptographic
    argument for its concrete digest, outside this operational model. *)
Definition collision_free_on (digest : Profile -> nat) (admitted : list Profile) : Prop :=
  forall left right, In left admitted -> In right admitted ->
    digest left = digest right -> left = right.

Definition rights_allowedb (requested ceiling : list nat) : bool :=
  forallb (fun right => existsb (Nat.eqb right) ceiling) requested.

Lemma rights_allowedb_sound : forall requested ceiling,
  rights_allowedb requested ceiling = true ->
  forall right, In right requested -> In right ceiling.
Proof.
  intros requested ceiling Allowed right Member.
  unfold rights_allowedb in Allowed. apply forallb_forall with (x := right) in Allowed;
    [|exact Member].
  apply existsb_exists in Allowed as [candidate [Present Equal]].
  apply Nat.eqb_eq in Equal. now subst candidate.
Qed.

Lemma rights_allowedb_refl : forall rights, rights_allowedb rights rights = true.
Proof.
  intros rights. unfold rights_allowedb. apply forallb_forall.
  intros right Member. apply existsb_exists. exists right.
  split; [exact Member|apply Nat.eqb_refl].
Qed.

Section Lifecycle.
Variable Seal : Type.
Variable seal_eq_dec : forall x y : Seal, {x = y} + {x <> y}.

Record Binding := binding {
  binding_payload : Profile;
  binding_digest : nat;
  binding_provider : CodecProvider;
  binding_epoch : nat;
  binding_seal : Seal;
  binding_ceiling : list nat;
  binding_live : bool
}.

Record Handle := handle {
  handle_payload : Profile;
  handle_digest : nat;
  handle_epoch : nat;
  handle_seal : Seal;
  handle_rights : list nat
}.

Definition live_matchb (expected : Profile) (candidate : Binding) : bool :=
  binding_live candidate && equalb profile_eq_dec (binding_payload candidate) expected.

Definition select_unique (expected : Profile) (registry : list Binding)
           : option Binding :=
  match filter (live_matchb expected) registry with
  | [candidate] => Some candidate
  | _ => None
  end.

Lemma unique_selection_exact_roster : forall expected registry selected,
  select_unique expected registry = Some selected ->
  filter (live_matchb expected) registry = [selected].
Proof.
  intros expected registry selected H. unfold select_unique in H.
  destruct (filter (live_matchb expected) registry) as [|first [|second rest]];
    try discriminate. inversion H. reflexivity.
Qed.

Theorem selected_binding_is_live_and_exact : forall expected registry selected,
  select_unique expected registry = Some selected ->
  In selected registry /\ binding_live selected = true /\
  binding_payload selected = expected.
Proof.
  intros expected registry selected H.
  pose proof (unique_selection_exact_roster _ _ _ H) as Roster.
  assert (Member : In selected (filter (live_matchb expected) registry)).
  { rewrite Roster. now left. }
  apply filter_In in Member as [Present Match].
  unfold live_matchb in Match. apply andb_true_iff in Match as [Live Exact].
  apply equalb_true_iff in Exact. auto.
Qed.

Theorem selected_binding_is_the_only_matching_member :
  forall expected registry selected candidate,
  select_unique expected registry = Some selected ->
  In candidate registry -> live_matchb expected candidate = true -> candidate = selected.
Proof.
  intros expected registry selected candidate H Member Match.
  assert (Present : In candidate (filter (live_matchb expected) registry)).
  { apply filter_In. auto. }
  rewrite (unique_selection_exact_roster _ _ _ H) in Present.
  destruct Present as [Equal|Impossible]; [symmetry; exact Equal|contradiction].
Qed.

Theorem duplicate_matching_occurrences_are_refused : forall expected candidate rest,
  live_matchb expected candidate = true ->
  select_unique expected (candidate :: candidate :: rest) = None.
Proof.
  intros expected candidate rest Match. unfold select_unique. simpl.
  rewrite Match. reflexivity.
Qed.

Definition binding_authorizedb (candidate : Binding) (credential : Handle)
           (required : list nat) : bool :=
  binding_live candidate &&
  equalb profile_eq_dec (handle_payload credential) (binding_payload candidate) &&
  Nat.eqb (handle_digest credential) (binding_digest candidate) &&
  Nat.eqb (handle_epoch credential) (binding_epoch candidate) &&
  equalb seal_eq_dec (handle_seal credential) (binding_seal candidate) &&
  rights_allowedb (handle_rights credential) (binding_ceiling candidate) &&
  rights_allowedb required (handle_rights credential).

Record AuthorizationFacts candidate credential required : Prop := authorization_facts {
  authorized_live : binding_live candidate = true;
  authorized_payload : handle_payload credential = binding_payload candidate;
  authorized_digest : handle_digest credential = binding_digest candidate;
  authorized_epoch : handle_epoch credential = binding_epoch candidate;
  authorized_seal : handle_seal credential = binding_seal candidate;
  authorized_attenuation : forall right, In right (handle_rights credential) ->
                            In right (binding_ceiling candidate);
  authorized_requirements : forall right, In right required ->
                             In right (handle_rights credential)
}.

Lemma binding_authorizedb_sound : forall candidate credential required,
  binding_authorizedb candidate credential required = true ->
  AuthorizationFacts candidate credential required.
Proof.
  intros candidate credential required H. unfold binding_authorizedb in H.
  repeat rewrite andb_true_iff in H. constructor.
  - tauto.
  - apply (proj1 (equalb_true_iff _ profile_eq_dec _ _)). tauto.
  - apply Nat.eqb_eq. tauto.
  - apply Nat.eqb_eq. tauto.
  - apply (proj1 (equalb_true_iff _ seal_eq_dec _ _)). tauto.
  - apply rights_allowedb_sound. tauto.
  - apply rights_allowedb_sound. tauto.
Qed.

Theorem successful_use_requires_independent_granted_rights :
  forall candidate credential required right,
  binding_authorizedb candidate credential required = true ->
  In right required -> In right (binding_ceiling candidate).
Proof.
  intros candidate credential required right Checked Required.
  pose proof (binding_authorizedb_sound _ _ _ Checked) as Facts.
  apply (authorized_attenuation _ _ _ Facts).
  apply (authorized_requirements _ _ _ Facts). exact Required.
Qed.

Theorem content_identity_cannot_replace_a_seal : forall candidate credential required,
  handle_payload credential = binding_payload candidate ->
  handle_digest credential = binding_digest candidate ->
  handle_seal credential <> binding_seal candidate ->
  binding_authorizedb candidate credential required = false.
Proof.
  intros candidate credential required _ _ Different.
  destruct (binding_authorizedb candidate credential required) eqn:Checked;
    [|reflexivity].
  exfalso. apply Different.
  exact (authorized_seal _ _ _ (binding_authorizedb_sound _ _ _ Checked)).
Qed.

Definition handle_for (candidate : Binding) : Handle :=
  handle (binding_payload candidate) (binding_digest candidate)
    (binding_epoch candidate) (binding_seal candidate) (binding_ceiling candidate).

(** The installer obtains the two decision bits from independent checked
    admission and installation-authority checks. Raw DDL has no parameters
    corresponding to these internal decisions. An existing live binding is
    never silently replaced, including by an identical duplicate. *)
Definition install (admitted install_authorized : bool) (registry : list Binding)
           (candidate : Binding) : option (list Binding * Handle) :=
  if admitted && install_authorized && binding_live candidate then
    match filter (live_matchb (binding_payload candidate)) registry with
    | [] => Some (candidate :: registry, handle_for candidate)
    | _ => None
    end
  else None.

Theorem installation_cannot_use_admission_as_authority : forall admitted registry candidate,
  install admitted false registry candidate = None.
Proof. intros. unfold install. now rewrite andb_false_r. Qed.

Theorem successful_install_is_atomic_and_unique :
  forall admitted permitted registry candidate next credential,
  install admitted permitted registry candidate = Some (next, credential) ->
  admitted = true /\ permitted = true /\
  next = candidate :: registry /\ credential = handle_for candidate /\
  select_unique (binding_payload candidate) next = Some candidate.
Proof.
  intros admitted permitted registry candidate next credential Installed.
  unfold install in Installed.
  destruct (admitted && permitted && binding_live candidate) eqn:Checks;
    [|discriminate].
  repeat rewrite andb_true_iff in Checks.
  destruct Checks as [[Admitted Permitted] Live].
  destruct (filter (live_matchb (binding_payload candidate)) registry)
    as [|existing rest] eqn:Roster; [|discriminate].
  inversion Installed; subst. repeat split; try assumption; try reflexivity.
  unfold select_unique. simpl. unfold live_matchb at 1.
  rewrite Live, equalb_refl. simpl. now rewrite Roster.
Qed.

Theorem duplicate_installation_is_refused : forall admitted permitted registry candidate,
  filter (live_matchb (binding_payload candidate)) registry <> [] ->
  install admitted permitted registry candidate = None.
Proof.
  intros admitted permitted registry candidate Present. unfold install.
  destruct (admitted && permitted && binding_live candidate); [|reflexivity].
  destruct (filter (live_matchb (binding_payload candidate)) registry);
    [contradiction|reflexivity].
Qed.

(** The public checked path constructs its candidate from the exact descriptor
    and provider passed to admission. The internal [install] helper alone is
    not a provenance theorem about an arbitrary caller-constructed [Binding].
    Fresh epoch allocation and seal issuance belong to the trusted installer;
    revocation/reinstallation laws below require the explicit epoch change. *)
Definition install_generated
    (digest : Profile -> nat)
    (generated_check : CheckedDefinition -> AdapterLayout -> bool)
    (authenticate : Origin -> Profile -> CodecIdentity -> bool)
    (codec_check : CodecProvider -> bool)
    (abi : nat) (d : CheckedDefinition) (l : AdapterLayout)
    (raw : RawDescriptor) (p : CodecProvider) (origin : Origin)
    (permitted : bool) (registry : list Binding)
    (epoch : nat) (seal : Seal) (granted : list nat)
    : option (list Binding * Handle) :=
  install
    (admission_okb digest generated_check authenticate codec_check abi d l raw p origin)
    permitted registry
    (binding (descriptor_payload raw) (descriptor_digest raw) p epoch seal granted true).

Theorem generated_install_binds_the_exact_admitted_candidate :
  forall digest generated_check authenticate codec_check abi d l raw p origin
    permitted registry epoch seal granted next credential,
  install_generated digest generated_check authenticate codec_check
    abi d l raw p origin permitted registry epoch seal granted = Some (next, credential) ->
  admission_okb digest generated_check authenticate codec_check abi d l raw p origin = true /\
  permitted = true /\
  handle_payload credential = descriptor_payload raw /\
  handle_digest credential = descriptor_digest raw /\
  handle_epoch credential = epoch /\
  handle_seal credential = seal /\
  handle_rights credential = granted /\
  select_unique (descriptor_payload raw) next =
    Some (binding (descriptor_payload raw) (descriptor_digest raw) p epoch seal granted true).
Proof.
  intros digest generated_check authenticate codec_check abi d l raw p origin
    permitted registry epoch seal granted next credential Installed.
  unfold install_generated in Installed.
  destruct (successful_install_is_atomic_and_unique _ _ _ _ _ _ Installed)
    as [Admitted [Permitted [_ [Credential Selected]]]].
  subst credential. simpl in *. repeat split; assumption || reflexivity.
Qed.

Definition revoke (candidate : Binding) : Binding :=
  binding (binding_payload candidate) (binding_digest candidate)
    (binding_provider candidate) (S (binding_epoch candidate))
    (binding_seal candidate) [] false.

Definition reinstall (retired : Binding) (fresh_seal : Seal) (ceiling : list nat)
           : Binding :=
  binding (binding_payload retired) (binding_digest retired)
    (binding_provider retired) (S (binding_epoch retired)) fresh_seal ceiling true.

Theorem revocation_changes_epoch_and_removes_authority : forall candidate credential required,
  binding_epoch (revoke candidate) = S (binding_epoch candidate) /\
  binding_authorizedb (revoke candidate) credential required = false.
Proof. intros. split; reflexivity. Qed.

Theorem reinstalling_identical_content_does_not_revive_old_handles :
  forall candidate credential required fresh_seal ceiling,
  binding_authorizedb candidate credential required = true ->
  binding_authorizedb (reinstall (revoke candidate) fresh_seal ceiling)
    credential required = false.
Proof.
  intros candidate credential required fresh_seal ceiling Before.
  pose proof (authorized_epoch _ _ _
    (binding_authorizedb_sound _ _ _ Before)) as OldEpoch.
  destruct (binding_authorizedb (reinstall (revoke candidate) fresh_seal ceiling)
    credential required) eqn:After; [|reflexivity].
  pose proof (authorized_epoch _ _ _
    (binding_authorizedb_sound _ _ _ After)) as NewEpoch.
  unfold reinstall, revoke in NewEpoch. simpl in NewEpoch. lia.
Qed.

Definition retire_matching (expected : Profile) (candidate : Binding) : Binding :=
  if equalb profile_eq_dec (binding_payload candidate) expected
  then revoke candidate else candidate.

Definition revoke_profile (expected : Profile) (registry : list Binding) : list Binding :=
  map (retire_matching expected) registry.

Lemma retired_candidate_never_matches : forall expected candidate,
  live_matchb expected (retire_matching expected candidate) = false.
Proof.
  intros expected candidate. unfold retire_matching.
  destruct (equalb profile_eq_dec (binding_payload candidate) expected) eqn:Equal.
  - reflexivity.
  - unfold live_matchb. now rewrite Equal, andb_false_r.
Qed.

Lemma revoked_profile_has_empty_live_roster : forall expected registry,
  filter (live_matchb expected) (revoke_profile expected registry) = [].
Proof.
  intros expected registry. induction registry as [|candidate rest IH]; [reflexivity|].
  unfold revoke_profile in *. simpl. rewrite retired_candidate_never_matches.
  exact IH.
Qed.

Theorem revoked_profile_cannot_be_selected : forall expected registry,
  select_unique expected (revoke_profile expected registry) = None.
Proof. intros. unfold select_unique. now rewrite revoked_profile_has_empty_live_roster. Qed.

Record PreparedUse := prepared_use {
  prepared_binding : Binding;
  prepared_handle : Handle;
  prepared_rights : list nat
}.

Definition prepare_use (registry : list Binding) (credential : Handle)
           (required : list nat) : option PreparedUse :=
  match select_unique (handle_payload credential) registry with
  | None => None
  | Some candidate =>
      if binding_authorizedb candidate credential required
      then Some (prepared_use candidate credential required)
      else None
  end.

Definition same_execution_bindingb (before after : Binding) : bool :=
  equalb profile_eq_dec (binding_payload before) (binding_payload after) &&
  Nat.eqb (binding_digest before) (binding_digest after) &&
  equalb provider_eq_dec (binding_provider before) (binding_provider after) &&
  Nat.eqb (binding_epoch before) (binding_epoch after) &&
  equalb seal_eq_dec (binding_seal before) (binding_seal after).

Definition publishableb (registry : list Binding) (ticket : PreparedUse) : bool :=
  match select_unique (handle_payload (prepared_handle ticket)) registry with
  | None => false
  | Some current =>
      binding_authorizedb current (prepared_handle ticket) (prepared_rights ticket) &&
      same_execution_bindingb (prepared_binding ticket) current
  end.

Theorem preparation_uses_a_unique_authorized_snapshot :
  forall registry credential required ticket,
  prepare_use registry credential required = Some ticket ->
  prepared_handle ticket = credential /\ prepared_rights ticket = required /\
  select_unique (handle_payload credential) registry = Some (prepared_binding ticket) /\
  binding_authorizedb (prepared_binding ticket) credential required = true.
Proof.
  intros registry credential required ticket H. unfold prepare_use in H.
  destruct (select_unique (handle_payload credential) registry) as [candidate|]
    eqn:Selected; [|discriminate].
  destruct (binding_authorizedb candidate credential required) eqn:Authorized;
    [|discriminate].
  inversion H; subst. simpl. auto.
Qed.

Theorem publication_requires_a_fresh_authorized_snapshot : forall registry ticket,
  publishableb registry ticket = true ->
  exists current,
    select_unique (handle_payload (prepared_handle ticket)) registry = Some current /\
    binding_authorizedb current (prepared_handle ticket) (prepared_rights ticket) = true /\
    binding_payload current = binding_payload (prepared_binding ticket) /\
    binding_provider current = binding_provider (prepared_binding ticket) /\
    binding_epoch current = binding_epoch (prepared_binding ticket).
Proof.
  intros registry ticket H. unfold publishableb in H.
  destruct (select_unique (handle_payload (prepared_handle ticket)) registry)
    as [current|] eqn:Selected; [|discriminate].
  apply andb_true_iff in H as [Authorized Same].
  unfold same_execution_bindingb in Same. repeat rewrite andb_true_iff in Same.
  destruct Same as [[[[Payload Digest] Provider] Epoch] SealEqual].
  apply equalb_true_iff in Payload. apply equalb_true_iff in Provider.
  apply Nat.eqb_eq in Epoch. exists current. auto.
Qed.

Theorem revocation_during_execution_prevents_publication : forall registry ticket,
  publishableb
    (revoke_profile (handle_payload (prepared_handle ticket)) registry) ticket = false.
Proof. intros. unfold publishableb. now rewrite revoked_profile_cannot_be_selected. Qed.

Theorem changed_codec_or_epoch_prevents_publication : forall registry ticket current,
  select_unique (handle_payload (prepared_handle ticket)) registry = Some current ->
  (binding_provider current <> binding_provider (prepared_binding ticket) \/
   binding_epoch current <> binding_epoch (prepared_binding ticket)) ->
  publishableb registry ticket = false.
Proof.
  intros registry ticket current Selected Different.
  destruct (publishableb registry ticket) eqn:Published; [|reflexivity].
  destruct (publication_requires_a_fresh_authorized_snapshot _ _ Published)
    as [actual [SelectedActual [_ [_ [Codec Epoch]]]]].
  rewrite Selected in SelectedActual. inversion SelectedActual; subst actual.
  destruct Different; contradiction.
Qed.

Theorem stale_profile_version_cannot_be_selected : forall expected registry,
  (forall candidate, In candidate registry ->
    grammar_version (profile_definition (binding_payload candidate)) <>
      grammar_version (profile_definition expected)) ->
  select_unique expected registry = None.
Proof.
  intros expected registry Different.
  destruct (select_unique expected registry) as [candidate|] eqn:Selected;
    [|reflexivity].
  destruct (selected_binding_is_live_and_exact _ _ _ Selected)
    as [Present [_ Exact]].
  exfalso. apply (Different candidate Present). now rewrite Exact.
Qed.

(** Host revalidation composes conjunctively with the existing independent
    guest-side authority/commit check. The guest check is an externally
    obtained decision, not inferred from the host profile or result payload. *)
Definition projection_publicationb (guest_revalidated : bool)
           (host_registry : list Binding) (ticket : PreparedUse) : bool :=
  guest_revalidated && publishableb host_registry ticket.

Theorem projection_publication_revalidates_both_endpoints :
  forall guest_revalidated host_registry ticket,
  projection_publicationb guest_revalidated host_registry ticket = true ->
  guest_revalidated = true /\ publishableb host_registry ticket = true.
Proof. intros. now apply andb_true_iff. Qed.

Theorem a_revoked_host_blocks_even_a_revalidated_guest :
  forall guest_revalidated host_registry ticket,
  projection_publicationb guest_revalidated
    (revoke_profile (handle_payload (prepared_handle ticket)) host_registry) ticket = false.
Proof.
  intros. unfold projection_publicationb.
  rewrite revocation_during_execution_prevents_publication. apply andb_false_r.
Qed.

End Lifecycle.
End HostProfileLifecycle.
