From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import CapabilitySeparation.
Import ListNotations.

Definition Commitment := nat.
Definition Generation := nat.
Definition Seal := nat.

Record InstalledEntry : Type := {
  entry_generation : Generation;
  entry_commitment : Commitment;
  entry_ceiling : list LanguageRight;
  entry_seal : Seal;
  entry_live : bool
}.

Record InstalledHandle : Type := {
  handle_generation : Generation;
  handle_commitment : Commitment;
  handle_rights : list LanguageRight;
  handle_seal : Seal
}.

Definition handle_valid (entry : InstalledEntry) (handle : InstalledHandle) : Prop :=
  entry_live entry = true /\
  handle_generation handle = entry_generation entry /\
  handle_commitment handle = entry_commitment entry /\
  handle_seal handle = entry_seal entry /\
  language_attenuates (handle_rights handle) (entry_ceiling entry).

Definition authorize
    (entry : InstalledEntry) (handle : InstalledHandle) (right : LanguageRight) : Prop :=
  handle_valid entry handle /\ In right (handle_rights handle).

(** One parser operation may require several independent rights (for example,
    parsing an FLT pattern requires both Parse and Match).  All rights are
    checked against one immutable authority snapshot. *)
Definition authorize_all
    (entry : InstalledEntry) (handle : InstalledHandle)
    (rights : list LanguageRight) : Prop :=
  handle_valid entry handle /\
  forall right, In right rights -> In right (handle_rights handle).

(** A potentially expensive parser runs outside the registry lock and must
    validate the same handle again before publishing its result.  The two
    snapshots are explicit here so revocation/reinstallation races cannot be
    hidden inside an implementation detail. *)
Definition revalidated_operation
    (before after : InstalledEntry) (handle : InstalledHandle)
    (rights : list LanguageRight) : Prop :=
  authorize_all before handle rights /\ authorize_all after handle rights.

Inductive InstallResult : Type :=
| InstallSucceeded : InstalledEntry -> InstalledHandle -> InstallResult
| InstallConflicted : option InstalledEntry -> InstallResult.

Definition fresh_install
    (generation : Generation) (commitment : Commitment)
    (rights : list LanguageRight) (seal : Seal) : InstallResult :=
  let entry :=
      {| entry_generation := generation;
         entry_commitment := commitment;
         entry_ceiling := rights;
         entry_seal := seal;
         entry_live := true |} in
  let handle :=
      {| handle_generation := generation;
         handle_commitment := commitment;
         handle_rights := rights;
         handle_seal := seal |} in
  InstallSucceeded entry handle.

Definition install
    (current : option InstalledEntry) (initial_generation : Generation)
    (commitment : Commitment) (rights : list LanguageRight) (fresh_seal : Seal)
    : InstallResult :=
  match current with
  | None => fresh_install initial_generation commitment rights fresh_seal
  | Some entry =>
      if entry_live entry then
        if Nat.eqb commitment (entry_commitment entry) then
          let widened := rights ++ entry_ceiling entry in
          InstallSucceeded
            {| entry_generation := entry_generation entry;
               entry_commitment := entry_commitment entry;
               entry_ceiling := widened;
               entry_seal := entry_seal entry;
               entry_live := true |}
            {| handle_generation := entry_generation entry;
               handle_commitment := entry_commitment entry;
               handle_rights := rights;
               handle_seal := entry_seal entry |}
        else InstallConflicted (Some entry)
      else fresh_install (S (entry_generation entry)) commitment rights fresh_seal
  end.

Definition revoke (entry : InstalledEntry) : InstalledEntry :=
  {| entry_generation := S (entry_generation entry);
     entry_commitment := entry_commitment entry;
     entry_ceiling := [];
     entry_seal := entry_seal entry;
     entry_live := false |}.

Lemma prefix_attenuates_append :
  forall requested ceiling,
    language_attenuates requested (requested ++ ceiling).
Proof.
  unfold language_attenuates. intros requested ceiling right Hin.
  apply in_or_app. left. exact Hin.
Qed.

Theorem successful_install_returns_only_authorized_rights :
  forall current initial_generation commitment rights fresh_seal entry handle,
    install current initial_generation commitment rights fresh_seal =
      InstallSucceeded entry handle ->
    handle_valid entry handle /\ handle_rights handle = rights.
Proof.
  intros current initial_generation commitment rights fresh_seal entry handle Hinstall.
  destruct current as [current |].
  - unfold install in Hinstall. simpl in Hinstall.
    destruct (entry_live current) eqn:Hlive.
    + destruct (Nat.eqb commitment (entry_commitment current)) eqn:Hcommit.
      * inversion Hinstall; subst. simpl. split; [| reflexivity].
        repeat split; try reflexivity.
        apply prefix_attenuates_append.
      * discriminate.
    + unfold fresh_install in Hinstall. inversion Hinstall; subst. simpl.
      split; [| reflexivity]. repeat split; try reflexivity.
      apply language_attenuation_reflexive.
  - unfold install, fresh_install in Hinstall. inversion Hinstall; subst. simpl.
    split; [| reflexivity]. repeat split; try reflexivity.
    apply language_attenuation_reflexive.
Qed.

Theorem identical_live_install_is_replay_safe :
  forall entry initial_generation rights fresh_seal,
    entry_live entry = true ->
    install (Some entry) initial_generation (entry_commitment entry) rights fresh_seal =
      InstallSucceeded
        {| entry_generation := entry_generation entry;
           entry_commitment := entry_commitment entry;
           entry_ceiling := rights ++ entry_ceiling entry;
           entry_seal := entry_seal entry;
           entry_live := true |}
        {| handle_generation := entry_generation entry;
           handle_commitment := entry_commitment entry;
           handle_rights := rights;
           handle_seal := entry_seal entry |}.
Proof.
  intros entry initial_generation rights fresh_seal Hlive.
  unfold install. simpl. rewrite Hlive, Nat.eqb_refl. reflexivity.
Qed.

Theorem conflicting_live_install_is_atomic :
  forall entry initial_generation commitment rights fresh_seal,
    entry_live entry = true ->
    commitment <> entry_commitment entry ->
    install (Some entry) initial_generation commitment rights fresh_seal =
      InstallConflicted (Some entry).
Proof.
  intros entry initial_generation commitment rights fresh_seal Hlive Hdifferent.
  unfold install. simpl. rewrite Hlive.
  apply Nat.eqb_neq in Hdifferent. rewrite Hdifferent. reflexivity.
Qed.

Theorem revocation_invalidates_every_preexisting_handle :
  forall entry handle,
    ~ handle_valid (revoke entry) handle.
Proof.
  intros entry handle Hvalid.
  unfold handle_valid, revoke in Hvalid. simpl in Hvalid.
  destruct Hvalid as [Hlive _]. discriminate.
Qed.

Theorem authorize_all_covers_every_requested_right :
  forall entry handle rights right,
    authorize_all entry handle rights ->
    In right rights ->
    authorize entry handle right.
Proof.
  unfold authorize_all, authorize.
  intros entry handle rights right [Hvalid Hall] Hin.
  split; [exact Hvalid | apply Hall; exact Hin].
Qed.

Theorem revoked_completion_fails_revalidation :
  forall entry handle rights,
    ~ revalidated_operation entry (revoke entry) handle rights.
Proof.
  unfold revalidated_operation, authorize_all.
  intros entry handle rights [_ [[Hlive _] _]].
  unfold revoke in Hlive; simpl in Hlive; discriminate.
Qed.

Theorem revocation_between_parse_phases_returns_no_authorized_result :
  forall entry handle rights,
    authorize_all entry handle rights ->
    ~ authorize_all (revoke entry) handle rights.
Proof.
  intros entry handle rights _ [Hvalid _].
  apply (revocation_invalidates_every_preexisting_handle entry handle).
  exact Hvalid.
Qed.

Theorem revoked_entry_reinstalls_with_fresh_generation_and_seal :
  forall entry initial_generation commitment rights fresh_seal,
    entry_live entry = false ->
    install (Some entry) initial_generation commitment rights fresh_seal =
      fresh_install (S (entry_generation entry)) commitment rights fresh_seal.
Proof.
  intros entry initial_generation commitment rights fresh_seal Hrevoked.
  unfold install. simpl. rewrite Hrevoked. reflexivity.
Qed.

Theorem fingerprint_or_commitment_is_not_authority :
  forall entry handle forged_seal,
    handle_valid entry handle ->
    forged_seal <> entry_seal entry ->
    ~ handle_valid entry
        {| handle_generation := handle_generation handle;
           handle_commitment := entry_commitment entry;
           handle_rights := handle_rights handle;
           handle_seal := forged_seal |}.
Proof.
  intros entry handle forged_seal Hvalid Hseal Hforged.
  unfold handle_valid in Hforged. simpl in Hforged.
  destruct Hforged as [_ [_ [_ [Heq _]]]]. contradiction.
Qed.

(* The executable model represents attenuation as list intersection in
   [CapabilitySeparation.grant_requested_language_rights].  Reuse does not
   require a second definition of intersection, so the installed-language
   layer imports and re-exports that proved law. *)
Theorem reused_handle_attenuation_cannot_amplify :
  forall requested granted,
    language_attenuates
      (grant_requested_language_rights requested granted) granted.
Proof. apply requested_language_rights_cannot_amplify_grants. Qed.

(** Runtime languages are prepared as a complete batch before the registry
    lock is taken.  A rejected core or parser image therefore cannot expose a
    prefix of the requested languages.  This list machine is the logical
    counterpart of [install_runtime_batch_with_host] followed by
    [commit_batch]: only [Some] reaches the publication branch. *)
Inductive ParserImageAdmission : Type :=
| ImageAdmitted (commitment : Commitment)
| ImageRejected.

Fixpoint prepare_image_batch
    (images : list ParserImageAdmission) : option (list Commitment) :=
  match images with
  | [] => Some []
  | ImageRejected :: _ => None
  | ImageAdmitted commitment :: rest =>
      match prepare_image_batch rest with
      | Some commitments => Some (commitment :: commitments)
      | None => None
      end
  end.

Definition publish_image_batch
    (installed : list Commitment) (images : list ParserImageAdmission)
    : list Commitment :=
  match prepare_image_batch images with
  | Some commitments => installed ++ commitments
  | None => installed
  end.

Lemma rejected_image_makes_batch_preparation_fail :
  forall images,
    In ImageRejected images ->
    prepare_image_batch images = None.
Proof.
  intros images.
  induction images as [| image rest IH]; intro Hrejected.
  - inversion Hrejected.
  - destruct image as [commitment |].
    + simpl in Hrejected. destruct Hrejected as [Himpossible | Hin].
      * inversion Himpossible.
      * simpl. rewrite (IH Hin). reflexivity.
    + reflexivity.
Qed.

Theorem rejected_image_keeps_the_complete_batch_invisible :
  forall installed images,
    In ImageRejected images ->
    publish_image_batch installed images = installed.
Proof.
  intros installed images Hrejected.
  unfold publish_image_batch.
  rewrite (rejected_image_makes_batch_preparation_fail images Hrejected).
  reflexivity.
Qed.

Theorem admitted_image_batch_publishes_exactly_one_complete_suffix :
  forall installed images commitments,
    prepare_image_batch images = Some commitments ->
    publish_image_batch installed images = installed ++ commitments.
Proof.
  intros installed images commitments Hprepared.
  unfold publish_image_batch. rewrite Hprepared. reflexivity.
Qed.

(** Executable languages refine the parser-only installation model above with
    the complete immutable language identity and both derived artifacts.  The
    idealized full-language fingerprint is a product: sharing a grammar is
    deliberately compatible with parser-image reuse, while changing the
    theory necessarily changes the installed-language key. *)
Definition GrammarFingerprint := nat.
Definition TheoryFingerprint := nat.
Definition ArtifactFingerprint := nat.
Definition AbiVersion := nat.
Definition LimitsFingerprint := nat.
Definition FullLanguageFingerprint :=
  (GrammarFingerprint * TheoryFingerprint)%type.

(** The source schema is projected before either artifact is compiled.  The
    components below deliberately model semantic ownership rather than the
    concrete hash function: syntax and construction determine the parser
    projection, executable theory determines the semantic projection, rights
    remain an attenuated installation request, and authoring metadata is not
    language identity. *)
Inductive SurfaceSchema : Type :=
| Language2Schema
| Language3Schema.

Definition SyntaxProjection := nat.
Definition ConstructionProjection := nat.
Definition SurfaceTheoryProjection := nat.
Definition AuthoringMetadata := nat.
Definition GrammarProjection :=
  (SyntaxProjection * ConstructionProjection)%type.

Record SurfaceLanguageDefinition : Type := {
  surface_schema : SurfaceSchema;
  surface_syntax : SyntaxProjection;
  surface_construction : ConstructionProjection;
  surface_theory : SurfaceTheoryProjection;
  surface_requested_rights : list LanguageRight;
  surface_authoring_metadata : AuthoringMetadata
}.

Definition project_grammar (surface : SurfaceLanguageDefinition)
    : GrammarProjection :=
  (surface_syntax surface, surface_construction surface).

Definition project_theory (surface : SurfaceLanguageDefinition)
    : TheoryFingerprint :=
  match surface_schema surface with
  | Language2Schema => 0
  | Language3Schema => surface_theory surface
  end.

Definition project_installation_rights (surface : SurfaceLanguageDefinition)
    : list LanguageRight :=
  surface_requested_rights surface.

Record ProjectedLanguageDefinition : Type := {
  projected_grammar : GrammarProjection;
  projected_theory : TheoryFingerprint;
  projected_requested_rights : list LanguageRight
}.

Definition lower_surface_language (surface : SurfaceLanguageDefinition)
    : ProjectedLanguageDefinition :=
  {| projected_grammar := project_grammar surface;
     projected_theory := project_theory surface;
     projected_requested_rights := project_installation_rights surface |}.

(** Changing only executable theory, requested rights, or authoring metadata
    cannot perturb the parser-cache key. *)
Theorem grammar_projection_theory_rights_metadata_noninterference :
  forall schema syntax construction theory_left theory_right
         rights_left rights_right metadata_left metadata_right,
    project_grammar
      {| surface_schema := schema;
         surface_syntax := syntax;
         surface_construction := construction;
         surface_theory := theory_left;
         surface_requested_rights := rights_left;
         surface_authoring_metadata := metadata_left |} =
    project_grammar
      {| surface_schema := schema;
         surface_syntax := syntax;
         surface_construction := construction;
         surface_theory := theory_right;
         surface_requested_rights := rights_right;
         surface_authoring_metadata := metadata_right |}.
Proof. reflexivity. Qed.

Theorem grammar_projection_is_syntax_sensitive :
  forall left right,
    surface_syntax left <> surface_syntax right ->
    project_grammar left <> project_grammar right.
Proof.
  intros left right Hsyntax Hprojection.
  unfold project_grammar in Hprojection.
  injection Hprojection as Hsame_syntax _.
  contradiction.
Qed.

Theorem grammar_projection_is_construction_sensitive :
  forall left right,
    surface_construction left <> surface_construction right ->
    project_grammar left <> project_grammar right.
Proof.
  intros left right Hconstruction Hprojection.
  unfold project_grammar in Hprojection.
  injection Hprojection as _ Hsame_construction.
  contradiction.
Qed.

(** The legacy language/2 schema has no executable OSLF projection; its
    compatibility semantics therefore cannot be reinterpreted as authority or
    an executable runtime theory. *)
Theorem language2_projects_to_structural_theory :
  forall syntax construction theory rights metadata,
    project_theory
      {| surface_schema := Language2Schema;
         surface_syntax := syntax;
         surface_construction := construction;
         surface_theory := theory;
         surface_requested_rights := rights;
         surface_authoring_metadata := metadata |} = 0.
Proof. reflexivity. Qed.

Theorem language3_projects_theory_exactly_once :
  forall syntax construction theory rights metadata,
    project_theory
      {| surface_schema := Language3Schema;
         surface_syntax := syntax;
         surface_construction := construction;
         surface_theory := theory;
         surface_requested_rights := rights;
         surface_authoring_metadata := metadata |} = theory.
Proof. reflexivity. Qed.

(** Rights are preserved as a separate request and are not smuggled into
    either the grammar or the semantic identity. *)
Theorem lowering_preserves_rights_only_in_installation_projection :
  forall surface,
    projected_requested_rights (lower_surface_language surface) =
      surface_requested_rights surface /\
    projected_grammar (lower_surface_language surface) =
      project_grammar surface /\
    projected_theory (lower_surface_language surface) =
      project_theory surface.
Proof. intros surface. repeat split; reflexivity. Qed.

(** Artifact compilation is itself gated by the attenuated request.  This is
    deliberately earlier than parser- or semantic-image compilation: a theory
    that asks an action to exercise an unrequested right cannot consume the
    artifact compiler's resource budget. *)
Definition action_rights_authorized
    (requested action : list LanguageRight) : bool :=
  forallb (fun right => has_language_right right requested) action.

Definition theory_actions_authorized
    (requested : list LanguageRight)
    (actions : list (list LanguageRight)) : bool :=
  forallb (action_rights_authorized requested) actions.

Inductive ArtifactPreparationOutcome : Type :=
| AuthorizationRejected
| CompilationRequested.

Definition prepare_artifact_compilation
    (requested : list LanguageRight)
    (actions : list (list LanguageRight)) : ArtifactPreparationOutcome :=
  if theory_actions_authorized requested actions
  then CompilationRequested
  else AuthorizationRejected.

Theorem artifact_compilation_requires_every_action_right_to_be_requested :
  forall requested actions,
    prepare_artifact_compilation requested actions = CompilationRequested ->
    forall action right,
      In action actions -> In right action -> In right requested.
Proof.
  intros requested actions Hprepare action right Haction Hright.
  unfold prepare_artifact_compilation in Hprepare.
  destruct (theory_actions_authorized requested actions) eqn:Hauthorized;
    try discriminate.
  unfold theory_actions_authorized in Hauthorized.
  apply forallb_forall with (x := action) in Hauthorized; [| exact Haction].
  unfold action_rights_authorized in Hauthorized.
  apply forallb_forall with (x := right) in Hauthorized; [| exact Hright].
  now apply has_language_right_sound in Hauthorized.
Qed.

Theorem unauthorized_theory_requests_no_artifact_compilation :
  forall requested actions,
    theory_actions_authorized requested actions = false ->
    prepare_artifact_compilation requested actions = AuthorizationRejected.
Proof.
  intros requested actions Hunauthorized.
  unfold prepare_artifact_compilation. rewrite Hunauthorized. reflexivity.
Qed.

Record ExecutableLanguageIdentity : Type := {
  executable_grammar_fingerprint : GrammarFingerprint;
  executable_theory_fingerprint : TheoryFingerprint
}.

Definition full_language_fingerprint
    (identity : ExecutableLanguageIdentity) : FullLanguageFingerprint :=
  (executable_grammar_fingerprint identity,
   executable_theory_fingerprint identity).

Record ParserImageArtifact : Type := {
  parser_image_grammar_fingerprint : GrammarFingerprint;
  parser_image_artifact_fingerprint : ArtifactFingerprint;
  parser_image_lexer_abi : AbiVersion;
  parser_image_parser_abi : AbiVersion
}.

Record SemanticImageArtifact : Type := {
  semantic_image_language_fingerprint : FullLanguageFingerprint;
  semantic_image_artifact_fingerprint : ArtifactFingerprint;
  semantic_image_compiler_abi : AbiVersion;
  semantic_image_primitive_substrate_abi : AbiVersion
}.

Record ExecutableInstallPolicy : Type := {
  policy_lexer_abi : AbiVersion;
  policy_parser_abi : AbiVersion;
  policy_semantic_compiler_abi : AbiVersion;
  policy_primitive_substrate_abi : AbiVersion;
  policy_parser_limits_fingerprint : LimitsFingerprint;
  policy_semantic_limits_fingerprint : LimitsFingerprint
}.

Record ExecutableLanguageBundle : Type := {
  bundle_language_identity : ExecutableLanguageIdentity;
  bundle_parser_image : ParserImageArtifact;
  bundle_semantic_image : SemanticImageArtifact;
  bundle_policy : ExecutableInstallPolicy
}.

Record ExecutableInstallCommitment : Type := {
  committed_language_fingerprint : FullLanguageFingerprint;
  committed_parser_artifact_fingerprint : ArtifactFingerprint;
  committed_semantic_artifact_fingerprint : ArtifactFingerprint;
  committed_lexer_abi : AbiVersion;
  committed_parser_abi : AbiVersion;
  committed_semantic_compiler_abi : AbiVersion;
  committed_primitive_substrate_abi : AbiVersion;
  committed_parser_limits_fingerprint : LimitsFingerprint;
  committed_semantic_limits_fingerprint : LimitsFingerprint
}.

Definition full_language_fingerprint_eqb
    (left right : FullLanguageFingerprint) : bool :=
  Nat.eqb (fst left) (fst right) && Nat.eqb (snd left) (snd right).

Definition parser_artifact_ok (bundle : ExecutableLanguageBundle) : bool :=
  Nat.eqb
    (parser_image_grammar_fingerprint (bundle_parser_image bundle))
    (executable_grammar_fingerprint (bundle_language_identity bundle)) &&
  Nat.eqb
    (parser_image_lexer_abi (bundle_parser_image bundle))
    (policy_lexer_abi (bundle_policy bundle)) &&
  Nat.eqb
    (parser_image_parser_abi (bundle_parser_image bundle))
    (policy_parser_abi (bundle_policy bundle)).

Definition semantic_artifact_ok (bundle : ExecutableLanguageBundle) : bool :=
  full_language_fingerprint_eqb
    (semantic_image_language_fingerprint (bundle_semantic_image bundle))
    (full_language_fingerprint (bundle_language_identity bundle)) &&
  Nat.eqb
    (semantic_image_compiler_abi (bundle_semantic_image bundle))
    (policy_semantic_compiler_abi (bundle_policy bundle)) &&
  Nat.eqb
    (semantic_image_primitive_substrate_abi (bundle_semantic_image bundle))
    (policy_primitive_substrate_abi (bundle_policy bundle)).

Definition executable_install_commitment
    (bundle : ExecutableLanguageBundle) : ExecutableInstallCommitment :=
  {| committed_language_fingerprint :=
       full_language_fingerprint (bundle_language_identity bundle);
     committed_parser_artifact_fingerprint :=
       parser_image_artifact_fingerprint (bundle_parser_image bundle);
     committed_semantic_artifact_fingerprint :=
       semantic_image_artifact_fingerprint (bundle_semantic_image bundle);
     committed_lexer_abi := policy_lexer_abi (bundle_policy bundle);
     committed_parser_abi := policy_parser_abi (bundle_policy bundle);
     committed_semantic_compiler_abi :=
       policy_semantic_compiler_abi (bundle_policy bundle);
     committed_primitive_substrate_abi :=
       policy_primitive_substrate_abi (bundle_policy bundle);
     committed_parser_limits_fingerprint :=
       policy_parser_limits_fingerprint (bundle_policy bundle);
     committed_semantic_limits_fingerprint :=
       policy_semantic_limits_fingerprint (bundle_policy bundle) |}.

Definition admit_executable_bundle
    (bundle : ExecutableLanguageBundle) : option ExecutableInstallCommitment :=
  if parser_artifact_ok bundle then
    if semantic_artifact_ok bundle then
      Some (executable_install_commitment bundle)
    else None
  else None.

Fixpoint prepare_executable_bundle_batch
    (bundles : list ExecutableLanguageBundle)
    : option (list ExecutableInstallCommitment) :=
  match bundles with
  | [] => Some []
  | bundle :: rest =>
      match admit_executable_bundle bundle,
            prepare_executable_bundle_batch rest with
      | Some commitment, Some commitments =>
          Some (commitment :: commitments)
      | _, _ => None
      end
  end.

Definition publish_executable_bundle_batch
    (installed : list ExecutableInstallCommitment)
    (bundles : list ExecutableLanguageBundle)
    : list ExecutableInstallCommitment :=
  match prepare_executable_bundle_batch bundles with
  | Some commitments => installed ++ commitments
  | None => installed
  end.

Theorem same_grammar_distinct_theories_have_distinct_full_fingerprints :
  forall left right,
    executable_grammar_fingerprint left =
      executable_grammar_fingerprint right ->
    executable_theory_fingerprint left <>
      executable_theory_fingerprint right ->
    full_language_fingerprint left <> full_language_fingerprint right.
Proof.
  intros left right _ Htheory Hfull.
  unfold full_language_fingerprint in Hfull.
  injection Hfull as _ Hsame_theory.
  contradiction.
Qed.

Lemma rejected_executable_bundle_makes_batch_preparation_fail :
  forall bundles rejected,
    In rejected bundles ->
    admit_executable_bundle rejected = None ->
    prepare_executable_bundle_batch bundles = None.
Proof.
  intros bundles.
  induction bundles as [| bundle rest IH]; intros rejected Hin Hrejected.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst bundle. simpl. rewrite Hrejected. reflexivity.
    + simpl. destruct (admit_executable_bundle bundle) as [commitment |].
      * rewrite (IH rejected Hin Hrejected). reflexivity.
      * reflexivity.
Qed.

Theorem rejected_parser_or_semantic_artifact_publishes_no_prefix :
  forall installed bundles rejected,
    In rejected bundles ->
    admit_executable_bundle rejected = None ->
    publish_executable_bundle_batch installed bundles = installed.
Proof.
  intros installed bundles rejected Hin Hrejected.
  unfold publish_executable_bundle_batch.
  rewrite
    (rejected_executable_bundle_makes_batch_preparation_fail
       bundles rejected Hin Hrejected).
  reflexivity.
Qed.

Theorem admitted_executable_bundle_batch_publishes_exactly_once :
  forall installed bundles commitments,
    prepare_executable_bundle_batch bundles = Some commitments ->
    publish_executable_bundle_batch installed bundles =
      installed ++ commitments.
Proof.
  intros installed bundles commitments Hprepared.
  unfold publish_executable_bundle_batch. rewrite Hprepared. reflexivity.
Qed.

Theorem admitted_executable_bundle_binds_both_artifacts :
  forall bundle commitment,
    admit_executable_bundle bundle = Some commitment ->
    parser_artifact_ok bundle = true /\
    semantic_artifact_ok bundle = true /\
    commitment = executable_install_commitment bundle.
Proof.
  intros bundle commitment Hadmitted.
  unfold admit_executable_bundle in Hadmitted.
  destruct (parser_artifact_ok bundle) eqn:Hparser; try discriminate.
  destruct (semantic_artifact_ok bundle) eqn:Hsemantic; try discriminate.
  inversion Hadmitted; subst. auto.
Qed.

(** The public parse boundary deliberately exposes recognition, not reflected
    syntax.  Reflection has its own right, while a parse-only capability may
    learn exactly one of four total, pairwise-distinct dispositions.  The
    executable parser cannot normally return an empty successful forest, but
    classifying it as rejection makes this boundary total and fail closed even
    if an implementation below it regresses. *)
Inductive BoundedParserResult : Type :=
| ParserAlternatives (alternatives : list nat)
| ParserRejected
| ParserExhausted.

Inductive ParseDisposition : Type :=
| ParseAccepted
| ParseRejectedDisposition
| ParseAmbiguous
| ParseExhaustedDisposition.

Definition classify_parse_result (result : BoundedParserResult)
    : ParseDisposition :=
  match result with
  | ParserAlternatives [] => ParseRejectedDisposition
  | ParserAlternatives [_] => ParseAccepted
  | ParserAlternatives (_ :: _ :: _) => ParseAmbiguous
  | ParserRejected => ParseRejectedDisposition
  | ParserExhausted => ParseExhaustedDisposition
  end.

(** Publication is possible only after checking the same opaque handle and
    Parse right both before computation and immediately before observation.
    Parser details cannot change the authority premise or the classification. *)
Inductive publishes_parse_result
    (before after : InstalledEntry) (handle : InstalledHandle)
    (result : BoundedParserResult) : ParseDisposition -> Prop :=
| PublishParseResult :
    revalidated_operation before after handle [Parse] ->
    publishes_parse_result before after handle result
      (classify_parse_result result).

Theorem singleton_parse_is_accepted_exactly :
  forall alternative,
    classify_parse_result (ParserAlternatives [alternative]) = ParseAccepted.
Proof. reflexivity. Qed.

Theorem plural_parse_is_ambiguous_exactly :
  forall first second rest,
    classify_parse_result (ParserAlternatives (first :: second :: rest)) =
      ParseAmbiguous.
Proof. reflexivity. Qed.

Theorem parser_rejection_and_empty_forest_are_rejected_exactly :
  classify_parse_result ParserRejected = ParseRejectedDisposition /\
  classify_parse_result (ParserAlternatives []) = ParseRejectedDisposition.
Proof. split; reflexivity. Qed.

Theorem parser_exhaustion_is_exhausted_exactly :
  classify_parse_result ParserExhausted = ParseExhaustedDisposition.
Proof. reflexivity. Qed.

Theorem parse_publication_is_deterministic :
  forall before after handle result left right,
    publishes_parse_result before after handle result left ->
    publishes_parse_result before after handle result right ->
    left = right.
Proof.
  intros before after handle result left right Hleft Hright.
  inversion Hleft; inversion Hright; reflexivity.
Qed.

Theorem parse_publication_requires_parse_authority_at_both_epochs :
  forall before after handle result disposition,
    publishes_parse_result before after handle result disposition ->
    authorize before handle Parse /\ authorize after handle Parse.
Proof.
  intros before after handle result disposition Hpublished.
  inversion Hpublished as [Hrevalidated].
  destruct Hrevalidated as [Hbefore Hafter].
  split.
  - eapply authorize_all_covers_every_requested_right; eauto. simpl; auto.
  - eapply authorize_all_covers_every_requested_right; eauto. simpl; auto.
Qed.

Theorem revocation_between_parse_and_publication_exposes_no_disposition :
  forall entry handle result disposition,
    ~ publishes_parse_result entry (revoke entry) handle result disposition.
Proof.
  intros entry handle result disposition Hpublished.
  inversion Hpublished as [Hrevalidated].
  eapply revoked_completion_fails_revalidation; eauto.
Qed.

Print Assumptions successful_install_returns_only_authorized_rights.
Print Assumptions identical_live_install_is_replay_safe.
Print Assumptions conflicting_live_install_is_atomic.
Print Assumptions revocation_invalidates_every_preexisting_handle.
Print Assumptions authorize_all_covers_every_requested_right.
Print Assumptions revoked_completion_fails_revalidation.
Print Assumptions revocation_between_parse_phases_returns_no_authorized_result.
Print Assumptions revoked_entry_reinstalls_with_fresh_generation_and_seal.
Print Assumptions fingerprint_or_commitment_is_not_authority.
Print Assumptions reused_handle_attenuation_cannot_amplify.
Print Assumptions rejected_image_keeps_the_complete_batch_invisible.
Print Assumptions admitted_image_batch_publishes_exactly_one_complete_suffix.
Print Assumptions same_grammar_distinct_theories_have_distinct_full_fingerprints.
Print Assumptions rejected_parser_or_semantic_artifact_publishes_no_prefix.
Print Assumptions artifact_compilation_requires_every_action_right_to_be_requested.
Print Assumptions unauthorized_theory_requests_no_artifact_compilation.
Print Assumptions admitted_executable_bundle_batch_publishes_exactly_once.
Print Assumptions admitted_executable_bundle_binds_both_artifacts.
Print Assumptions singleton_parse_is_accepted_exactly.
Print Assumptions plural_parse_is_ambiguous_exactly.
Print Assumptions parser_rejection_and_empty_forest_are_rejected_exactly.
Print Assumptions parser_exhaustion_is_exhausted_exactly.
Print Assumptions parse_publication_is_deterministic.
Print Assumptions parse_publication_requires_parse_authority_at_both_epochs.
Print Assumptions revocation_between_parse_and_publication_exposes_no_disposition.
