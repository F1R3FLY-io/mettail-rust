(** Consuming output protocol for the neutral frontend's owned session.

    Reuses the construction algebra and exact FLT transport records. There is
    no execution API, callback, provider registry, source parser or funding
    certificate in this model. Host services remain declaration requirements.

    A finish input is the result supplied by the existing lowering driver.
    This protocol checks its root-stack shape and reference links; the separate
    worklist refinement must establish that the driver actually finished.
    Checked links do not prove lexical resolution, template validity, semantic
    predicate truth, or canonical node bytes. Those obligations remain explicit.

    Consuming the returned state is a finite-state ownership law, not a proof
    that mathematical values cannot be copied. The Rust interface must enforce
    move-only session ownership and bounded cleanup on error and cancellation. *)

From Stdlib Require Import List String PeanoNat Bool ZArith Lia.
From RhoBridge Require RholangTargetConstruction RholangConstructionProtocol
  RholangFrontendAdmission RholangFltTransport.
Import ListNotations.
Module Algebra := RholangTargetConstruction.
Module Construction := RholangConstructionProtocol.
Module Admission := RholangFrontendAdmission.
Module Foreign := RholangFltTransport.

Inductive ProviderPurpose := LanguageOperations | NativeRule | NativeShift.
Record ProviderRequirement := {
  provider_reference : Admission.Reference;
  provider_purpose : ProviderPurpose;
  declaration_index : nat;
  expected_language_commitment : option string
}.

(** Mirrors FoldSpec's data only. No evaluator or materialized host Definition
    enters the neutral record, and a fingerprint is not an authority handle. *)
Inductive FoldKind := IntFold | UIntFold | FloatFold | FixedFold | BigIntCast | BigRatCast.
Record FoldRequirement := {
  fold_kind : FoldKind;
  fold_width : Z;
  fold_site_index : nat;
  fold_language_commitment : string
}.
Record GuardDescription := {
  condition_reference : nat;
  enclosing_captures : list Algebra.CaptureSlot;
  predicate_references : list nat;
  requested_discharge : bool
}.
Record Diagnostic := {
  diagnostic_code : string;
  diagnostic_occurrence : option nat;
  diagnostic_range : option (nat * nat)
}.
Record SessionPayload := {
  foreign_uses : list Foreign.ForeignUse;
  guard_descriptions : list GuardDescription;
  provider_requirements : list ProviderRequirement;
  fold_requirements : list FoldRequirement;
  diagnostics : list Diagnostic
}.
Definition empty_payload : SessionPayload :=
  {| foreign_uses := []; guard_descriptions := []; provider_requirements := [];
     fold_requirements := []; diagnostics := [] |}.

(** Ordinals in this occurrence vector are source-use identities. Its first
    component is a semantic arena reference; sharing it does not merge uses. *)
Definition Occurrences := list (nat * Admission.Origin).
Record Draft := {
  private_values : list Algebra.Value;
  private_occurrences : Occurrences;
  private_payload : SessionPayload
}.
Inductive Session := Open (draft : Draft) | Consumed.
Definition start : Session := Open
  {| private_values := []; private_occurrences := []; private_payload := empty_payload |}.

Inductive SessionError :=
| SessionAlreadyConsumed
| LoweringFailure (error : Algebra.ConstructionError)
| InvalidResultStack (size : nat)
| DanglingValue (reference : nat)
| DanglingOccurrence (reference : nat)
| DanglingPredicate (reference : nat)
| NonPredicateSite (reference : nat).

Definition replace_values (draft : Draft) (values : list Algebra.Value) : Draft :=
  {| private_values := values; private_occurrences := private_occurrences draft;
     private_payload := private_payload draft |}.
Definition append_foreign_use (payload : SessionPayload) (use : Foreign.ForeignUse) : SessionPayload :=
  {| foreign_uses := foreign_uses payload ++ [use];
     guard_descriptions := guard_descriptions payload;
     provider_requirements := provider_requirements payload;
     fold_requirements := fold_requirements payload; diagnostics := diagnostics payload |}.
Definition replace_payload (draft : Draft) (payload : SessionPayload) : Draft :=
  {| private_values := private_values draft; private_occurrences := private_occurrences draft;
     private_payload := payload |}.

Inductive RegistrationResult :=
| Registered (session : Session) (reference : nat)
| RegistrationRejected (session : Session) (error : SessionError)
    (retained_diagnostics : list Diagnostic).
Definition register_foreign (session : Session) (use : Foreign.ForeignUse) : RegistrationResult :=
  match session with
  | Consumed => RegistrationRejected Consumed SessionAlreadyConsumed []
  | Open draft => Registered
      (Open (replace_payload draft (append_foreign_use (private_payload draft) use)))
      (List.length (foreign_uses (private_payload draft)))
  end.

(** Closed recording vocabulary for the existing producer outputs. Each
    receipt index belongs to the table selected by its event constructor.
    None of these records registers a live provider or executes a guard. *)
Inductive RecordEvent :=
| RecordOccurrence (value_reference : nat) (origin : Admission.Origin)
| RecordForeignUse (use : Foreign.ForeignUse)
| RecordGuard (guard : GuardDescription)
| RecordProvider (requirement : ProviderRequirement)
| RecordFold (requirement : FoldRequirement)
| RecordDiagnostic (diagnostic : Diagnostic).

Definition record_event (session : Session) (event : RecordEvent) : RegistrationResult :=
  match session with
  | Consumed => RegistrationRejected Consumed SessionAlreadyConsumed []
  | Open draft =>
    let payload := private_payload draft in
    match event with
    | RecordOccurrence value origin => Registered (Open
        {| private_values := private_values draft;
           private_occurrences := private_occurrences draft ++ [(value, origin)];
           private_payload := payload |}) (List.length (private_occurrences draft))
    | RecordForeignUse use => register_foreign session use
    | RecordGuard guard => Registered (Open (replace_payload draft
        {| foreign_uses := foreign_uses payload;
           guard_descriptions := guard_descriptions payload ++ [guard];
           provider_requirements := provider_requirements payload;
           fold_requirements := fold_requirements payload; diagnostics := diagnostics payload |}))
        (List.length (guard_descriptions payload))
    | RecordProvider requirement => Registered (Open (replace_payload draft
        {| foreign_uses := foreign_uses payload; guard_descriptions := guard_descriptions payload;
           provider_requirements := provider_requirements payload ++ [requirement];
           fold_requirements := fold_requirements payload; diagnostics := diagnostics payload |}))
        (List.length (provider_requirements payload))
    | RecordFold requirement => Registered (Open (replace_payload draft
        {| foreign_uses := foreign_uses payload; guard_descriptions := guard_descriptions payload;
           provider_requirements := provider_requirements payload;
           fold_requirements := fold_requirements payload ++ [requirement]; diagnostics := diagnostics payload |}))
        (List.length (fold_requirements payload))
    | RecordDiagnostic diagnostic => Registered (Open (replace_payload draft
        {| foreign_uses := foreign_uses payload; guard_descriptions := guard_descriptions payload;
           provider_requirements := provider_requirements payload;
           fold_requirements := fold_requirements payload; diagnostics := diagnostics payload ++ [diagnostic] |}))
        (List.length (diagnostics payload))
    end
  end.

(** This is the same checked construction, now inside an owning session.
    A failed construction consumes the session: its partial descriptor table
    cannot be recovered as a successful output by a subsequent finish. *)
Definition construct_in_session (session : Session) (operation : Construction.ConstructOp)
    (references : list nat) : RegistrationResult :=
  match session with
  | Consumed => RegistrationRejected Consumed SessionAlreadyConsumed []
  | Open draft =>
    match Construction.construction_step (private_values draft) operation references with
    | Construction.ValueAppended values index =>
      Registered (Open (replace_values draft values)) index
    | Construction.StepRejected _ error => RegistrationRejected Consumed (LoweringFailure error)
        (diagnostics (private_payload draft))
    end
  end.

Fixpoint check_value_references (arena : list Algebra.Value) (references : list nat)
    : option SessionError :=
  match references with
  | [] => None
  | index :: rest =>
    match nth_error arena index with
    | Some _ => check_value_references arena rest
    | None => Some (DanglingValue index)
    end
  end.
Fixpoint check_use_occurrences (occurrences : Occurrences) (uses : list Foreign.ForeignUse)
    : option SessionError :=
  match uses with
  | [] => None
  | use :: rest =>
    match nth_error occurrences (Foreign.use_occurrence use) with
    | Some _ => check_use_occurrences occurrences rest
    | None => Some (DanglingOccurrence (Foreign.use_occurrence use))
    end
  end.
Fixpoint check_predicate_references (uses : list Foreign.ForeignUse) (references : list nat)
    : option SessionError :=
  match references with
  | [] => None
  | index :: rest =>
    match nth_error uses index with
    | None => Some (DanglingPredicate index)
    | Some use =>
      match Foreign.use_role use with
      | Foreign.PredicateSite => check_predicate_references uses rest
      | _ => Some (NonPredicateSite index)
      end
    end
  end.
Fixpoint check_guards (arena : list Algebra.Value) (uses : list Foreign.ForeignUse)
    (guards : list GuardDescription) : option SessionError :=
  match guards with
  | [] => None
  | guard :: rest =>
    match nth_error arena (condition_reference guard) with
    | None => Some (DanglingValue (condition_reference guard))
    | Some _ =>
      match check_predicate_references uses (predicate_references guard) with
      | Some error => Some error
      | None => check_guards arena uses rest
      end
    end
  end.
Definition check_links (draft : Draft) : option SessionError :=
  match check_value_references (private_values draft) (map fst (private_occurrences draft)) with
  | Some error => Some error
  | None =>
    match check_use_occurrences (private_occurrences draft) (foreign_uses (private_payload draft)) with
    | Some error => Some error
    | None => check_guards (private_values draft) (foreign_uses (private_payload draft))
        (guard_descriptions (private_payload draft))
    end
  end.

Record OwnedArtifact := {
  artifact_values : list Algebra.Value;
  artifact_root : nat;
  artifact_occurrences : Occurrences;
  artifact_payload : SessionPayload
}.
Definition bundle (draft : Draft) (root : nat) : OwnedArtifact :=
  {| artifact_values := private_values draft; artifact_root := root;
     artifact_occurrences := private_occurrences draft; artifact_payload := private_payload draft |}.

(** Semantic comparison erases diagnostic origins at BOTH levels: outer
    occurrences and nested FLT captures. Checked extents, capture associations,
    guard policy, and every provider/fold requirement remain semantic inputs. *)
Record SemanticPayload := {
  retained_foreign_uses : list Foreign.SemanticUse;
  retained_guards : list GuardDescription;
  retained_providers : list ProviderRequirement;
  retained_folds : list FoldRequirement
}.
Definition erase_payload_diagnostics (payload : SessionPayload) : SemanticPayload :=
  {| retained_foreign_uses := map Foreign.retain_use (foreign_uses payload);
     retained_guards := guard_descriptions payload;
     retained_providers := provider_requirements payload;
     retained_folds := fold_requirements payload |}.
Definition semantic_artifact (artifact : OwnedArtifact) :=
  (artifact_values artifact, artifact_root artifact, map fst (artifact_occurrences artifact),
   erase_payload_diagnostics (artifact_payload artifact)).
Inductive DriverOutcome :=
| DriverValues (result_stack : list nat)
| DriverFailed (error : Algebra.ConstructionError).
Inductive FinishResult :=
| OwnedOutput (artifact : OwnedArtifact)
| NoArtifact (error : SessionError) (retained_diagnostics : list Diagnostic).
Definition finish (session : Session) (outcome : DriverOutcome) : Session * FinishResult :=
  (Consumed,
   match session with
   | Consumed => NoArtifact SessionAlreadyConsumed []
   | Open draft =>
     let reject error := NoArtifact error (diagnostics (private_payload draft)) in
     match outcome with
     | DriverFailed error => reject (LoweringFailure error)
     | DriverValues [root] =>
       match nth_error (private_values draft) root with
       | None => reject (DanglingValue root)
       | Some _ =>
         match check_links draft with
         | Some error => reject error
         | None => OwnedOutput (bundle draft root)
         end
       end
     | DriverValues stack => reject (InvalidResultStack (List.length stack))
     end
   end).

Theorem registration_returns_exact_descriptor : forall draft use,
  let updated := replace_payload draft (append_foreign_use (private_payload draft) use) in
  register_foreign (Open draft) use =
    Registered (Open updated) (List.length (foreign_uses (private_payload draft))) /\
  nth_error (foreign_uses (private_payload updated))
    (List.length (foreign_uses (private_payload draft))) = Some use.
Proof.
  intros; split; [reflexivity|].
  change (nth_error (foreign_uses (private_payload draft) ++ [use])
    (List.length (foreign_uses (private_payload draft))) = Some use).
  rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Theorem registration_preserves_earlier_descriptors : forall draft use index previous,
  nth_error (foreign_uses (private_payload draft)) index = Some previous ->
  nth_error (foreign_uses (append_foreign_use (private_payload draft) use)) index = Some previous.
Proof.
  intros; cbn [append_foreign_use foreign_uses]. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. rewrite H; discriminate.
Qed.

Theorem registration_preserves_other_owned_fields : forall draft use,
  let updated := replace_payload draft (append_foreign_use (private_payload draft) use) in
  private_values updated = private_values draft /\
  private_occurrences updated = private_occurrences draft /\
  guard_descriptions (private_payload updated) = guard_descriptions (private_payload draft) /\
  provider_requirements (private_payload updated) = provider_requirements (private_payload draft) /\
  fold_requirements (private_payload updated) = fold_requirements (private_payload draft) /\
  diagnostics (private_payload updated) = diagnostics (private_payload draft).
Proof. intros; repeat split; reflexivity. Qed.

Theorem construction_failure_consumes_session : forall draft operation references error,
  Construction.construct (private_values draft) operation references = Algebra.ConstructionRejected error ->
  construct_in_session (Open draft) operation references =
    RegistrationRejected Consumed (LoweringFailure error) (diagnostics (private_payload draft)).
Proof.
  intros; unfold construct_in_session.
  rewrite (Construction.failed_step_leaves_arena_unchanged _ _ _ _ H). reflexivity.
Qed.

Theorem success_keeps_whole_owned_bundle : forall draft root value,
  nth_error (private_values draft) root = Some value -> check_links draft = None ->
  finish (Open draft) (DriverValues [root]) = (Consumed, OwnedOutput (bundle draft root)).
Proof. intros; unfold finish; now rewrite H, H0. Qed.

Theorem output_has_actual_root_and_checked_links : forall draft stack artifact,
  snd (finish (Open draft) (DriverValues stack)) = OwnedOutput artifact ->
  exists root value,
    stack = [root] /\ nth_error (private_values draft) root = Some value /\
    check_links draft = None /\ artifact = bundle draft root.
Proof.
  intros draft [|root [|second rest]] artifact H; try discriminate.
  cbn [finish snd] in H.
  destruct (nth_error (private_values draft) root) eqn:E; try discriminate.
  destruct (check_links draft) eqn:C; try discriminate.
  inversion H; subst. exists root, v. repeat split; auto.
Qed.

Theorem failed_driver_has_no_artifact : forall draft error,
  finish (Open draft) (DriverFailed error) =
    (Consumed, NoArtifact (LoweringFailure error) (diagnostics (private_payload draft))).
Proof. reflexivity. Qed.

Theorem finish_always_consumes : forall session outcome, fst (finish session outcome) = Consumed.
Proof. reflexivity. Qed.

Theorem returned_session_cannot_republish : forall session first second,
  finish (fst (finish session first)) second = (Consumed, NoArtifact SessionAlreadyConsumed []).
Proof. reflexivity. Qed.

Theorem consumed_session_cannot_register : forall use,
  register_foreign Consumed use = RegistrationRejected Consumed SessionAlreadyConsumed [].
Proof. reflexivity. Qed.

Theorem fresh_session_has_no_inherited_state :
  start = Open {| private_values := []; private_occurrences := []; private_payload := empty_payload |}.
Proof. reflexivity. Qed.

Theorem origin_erasure_retains_owned_payload : forall draft root,
  (artifact_values (bundle draft root), artifact_root (bundle draft root),
   map fst (artifact_occurrences (bundle draft root)), artifact_payload (bundle draft root)) =
  (private_values draft, root, map fst (private_occurrences draft), private_payload draft).
Proof. reflexivity. Qed.

Theorem semantic_projection_retains_all_owned_requirements : forall draft root,
  semantic_artifact (bundle draft root) =
  (private_values draft, root, map fst (private_occurrences draft),
   {| retained_foreign_uses := map Foreign.retain_use (foreign_uses (private_payload draft));
      retained_guards := guard_descriptions (private_payload draft);
      retained_providers := provider_requirements (private_payload draft);
      retained_folds := fold_requirements (private_payload draft) |}).
Proof. reflexivity. Qed.

Theorem changing_diagnostics_does_not_change_semantics :
  forall values root occurrences uses guards providers folds first second,
  semantic_artifact
    {| artifact_values := values; artifact_root := root; artifact_occurrences := occurrences;
       artifact_payload := {| foreign_uses := uses; guard_descriptions := guards;
         provider_requirements := providers; fold_requirements := folds; diagnostics := first |} |} =
  semantic_artifact
    {| artifact_values := values; artifact_root := root; artifact_occurrences := occurrences;
       artifact_payload := {| foreign_uses := uses; guard_descriptions := guards;
         provider_requirements := providers; fold_requirements := folds; diagnostics := second |} |}.
Proof. reflexivity. Qed.

Theorem changing_occurrence_origins_does_not_change_semantics : forall values root first second payload,
  map fst first = map fst second ->
  semantic_artifact {| artifact_values := values; artifact_root := root;
    artifact_occurrences := first; artifact_payload := payload |} =
  semantic_artifact {| artifact_values := values; artifact_root := root;
    artifact_occurrences := second; artifact_payload := payload |}.
Proof. intros; unfold semantic_artifact; cbn; now rewrite H. Qed.

Theorem predicate_obligations_survive_owned_projection : forall payload index use,
  nth_error (foreign_uses payload) index = Some use ->
  Foreign.use_role use = Foreign.PredicateSite ->
  nth_error (map Foreign.semantic_obligations
    (retained_foreign_uses (erase_payload_diagnostics payload))) index =
  Some (Admission.Supported
    [Admission.ResolveScope; Admission.ValidateStructure; Admission.BindProvider;
     Admission.ConstructGuest; Admission.ObserveGuest; Admission.CheckLiveAuthority;
     Admission.ProjectResources; Admission.FundCommit]).
Proof.
  intros payload index use E R.
  cbn [erase_payload_diagnostics retained_foreign_uses].
  rewrite !nth_error_map, E. cbn [option_map Foreign.retain_use Foreign.semantic_obligations].
  now rewrite R.
Qed.

Example fresh_session_cannot_invent_an_empty_root :
  finish start (DriverValues [0]) = (Consumed, NoArtifact (DanglingValue 0) []).
Proof. reflexivity. Qed.

Example two_results_are_not_silently_elected : forall draft first second,
  finish (Open draft) (DriverValues [first; second]) =
    (Consumed, NoArtifact (InvalidResultStack 2) (diagnostics (private_payload draft))).
Proof. reflexivity. Qed.

Theorem record_event_preserves_constructed_values : forall draft event next index,
  record_event (Open draft) event = Registered (Open next) index ->
  private_values next = private_values draft.
Proof.
  intros draft event next index H; destruct event;
    cbn [record_event register_foreign replace_payload append_foreign_use] in H;
    inversion H; reflexivity.
Qed.

Theorem session_construction_preserves_generated_arena : forall draft operation references next index,
  Construction.GeneratedArena (private_values draft) ->
  construct_in_session (Open draft) operation references = Registered (Open next) index ->
  Construction.GeneratedArena (private_values next).
Proof.
  intros draft operation references next index G H.
  cbn [construct_in_session] in H.
  destruct (Construction.construction_step (private_values draft) operation references) eqn:E;
    try discriminate.
  inversion H; subst. cbn [replace_values private_values].
  eapply Construction.successful_step_retains_generated_image; eauto.
Qed.

(** Reachability excludes forged raw arenas. It is a proof of the concrete
    session transitions, not a supplied validity bit. Producer refinements
    additionally establish the meaning of their descriptors and occurrences. *)
Inductive ReachableDraft : Draft -> Prop :=
| InitialDraft : ReachableDraft
    {| private_values := []; private_occurrences := []; private_payload := empty_payload |}
| RecordedDraft : forall prior event next index,
    ReachableDraft prior -> record_event (Open prior) event = Registered (Open next) index ->
    ReachableDraft next
| ConstructedDraft : forall prior operation references next index,
    ReachableDraft prior ->
    construct_in_session (Open prior) operation references = Registered (Open next) index ->
    ReachableDraft next.

Theorem reachable_drafts_have_constructed_arenas : forall draft,
  ReachableDraft draft -> Construction.GeneratedArena (private_values draft).
Proof.
  intros draft H; induction H.
  - constructor.
  - rewrite (record_event_preserves_constructed_values _ _ _ _ H0); exact IHReachableDraft.
  - eapply session_construction_preserves_generated_arena; eauto.
Qed.

Theorem value_link_check_has_actual_targets : forall arena references,
  check_value_references arena references = None ->
  Forall (fun reference => exists value, nth_error arena reference = Some value) references.
Proof.
  intros arena references; induction references as [|reference rest IH]; intros H; [constructor|].
  cbn in H. destruct (nth_error arena reference) eqn:E; try discriminate.
  constructor; [eexists; exact E|now apply IH].
Qed.

Theorem occurrence_link_check_has_actual_targets : forall occurrences uses,
  check_use_occurrences occurrences uses = None ->
  Forall (fun use => exists occurrence,
    nth_error occurrences (Foreign.use_occurrence use) = Some occurrence) uses.
Proof.
  intros occurrences uses; induction uses as [|use rest IH]; intros H; [constructor|].
  cbn in H. destruct (nth_error occurrences (Foreign.use_occurrence use)) eqn:E; try discriminate.
  constructor; [eexists; exact E|now apply IH].
Qed.

Definition IsPredicateReference (uses : list Foreign.ForeignUse) (reference : nat) : Prop :=
  exists use, nth_error uses reference = Some use /\ Foreign.use_role use = Foreign.PredicateSite.
Theorem predicate_link_check_has_predicate_targets : forall uses references,
  check_predicate_references uses references = None -> Forall (IsPredicateReference uses) references.
Proof.
  intros uses references; induction references as [|reference rest IH]; intros H; [constructor|].
  cbn in H. destruct (nth_error uses reference) as [use|] eqn:E; try discriminate.
  destruct (Foreign.use_role use) eqn:R; try discriminate.
  constructor; [exists use; auto|now apply IH].
Qed.

Definition GuardLinks (arena : list Algebra.Value) (uses : list Foreign.ForeignUse)
    (guard : GuardDescription) : Prop :=
  (exists value, nth_error arena (condition_reference guard) = Some value) /\
  Forall (IsPredicateReference uses) (predicate_references guard).
Theorem guard_link_check_has_condition_and_predicate_targets : forall arena uses guards,
  check_guards arena uses guards = None -> Forall (GuardLinks arena uses) guards.
Proof.
  intros arena uses guards; induction guards as [|guard rest IH]; intros H; [constructor|].
  cbn in H. destruct (nth_error arena (condition_reference guard)) as [value|] eqn:E; try discriminate.
  destruct (check_predicate_references uses (predicate_references guard)) eqn:P; try discriminate.
  constructor; [|now apply IH]. split; [eexists; exact E|].
  now apply predicate_link_check_has_predicate_targets.
Qed.

Theorem checked_bundle_retains_real_reference_targets : forall draft,
  check_links draft = None ->
  Forall (fun reference => exists value, nth_error (private_values draft) reference = Some value)
    (map fst (private_occurrences draft)) /\
  Forall (fun use => exists occurrence,
    nth_error (private_occurrences draft) (Foreign.use_occurrence use) = Some occurrence)
    (foreign_uses (private_payload draft)) /\
  Forall (GuardLinks (private_values draft) (foreign_uses (private_payload draft)))
    (guard_descriptions (private_payload draft)).
Proof.
  intros draft H; unfold check_links in H.
  destruct (check_value_references _ _) eqn:V; try discriminate.
  destruct (check_use_occurrences _ _) eqn:U; try discriminate.
  split; [now apply value_link_check_has_actual_targets|].
  split; [now apply occurrence_link_check_has_actual_targets|].
  now apply guard_link_check_has_condition_and_predicate_targets.
Qed.

Theorem missing_condition_blocks_output : forall draft root value guard rest,
  nth_error (private_values draft) root = Some value ->
  guard_descriptions (private_payload draft) = guard :: rest ->
  nth_error (private_values draft) (condition_reference guard) = None ->
  check_value_references (private_values draft) (map fst (private_occurrences draft)) = None ->
  check_use_occurrences (private_occurrences draft) (foreign_uses (private_payload draft)) = None ->
  finish (Open draft) (DriverValues [root]) =
    (Consumed, NoArtifact (DanglingValue (condition_reference guard)) (diagnostics (private_payload draft))).
Proof.
  intros draft root value guard rest R G C V U.
  unfold finish, check_links. rewrite R, V, U, G. cbn [check_guards]. now rewrite C.
Qed.

Theorem nonpredicate_reference_is_not_observation_evidence : forall uses index use rest,
  nth_error uses index = Some use -> Foreign.use_role use <> Foreign.PredicateSite ->
  check_predicate_references uses (index :: rest) = Some (NonPredicateSite index).
Proof.
  intros uses index use rest E H. cbn [check_predicate_references]. rewrite E.
  destruct (Foreign.use_role use); try reflexivity; contradiction.
Qed.

(** A protocol witness, not an executable Regex application: starting with no
    state, actual construction and recording transitions can produce a bundle
    containing a predicate, its occurrence, its guard and an unresolved provider
    request. Predicate truth, provider binding and funding remain unestablished. *)
Theorem reachable_nonempty_foreign_bundle : forall use origin,
  Foreign.use_occurrence use = 0 -> Foreign.use_role use = Foreign.PredicateSite ->
  exists first second third fourth fifth artifact,
    construct_in_session start (Construction.BooleanOp true) [] = Registered first 0 /\
    record_event first (RecordOccurrence 0 origin) = Registered second 0 /\
    record_event second (RecordForeignUse use) = Registered third 0 /\
    record_event third (RecordGuard
      {| condition_reference := 0; enclosing_captures := []; predicate_references := [0];
         requested_discharge := true |}) = Registered fourth 0 /\
    record_event fourth (RecordProvider
      {| provider_reference := Foreign.lexical_selector (Foreign.use_capture use);
         provider_purpose := LanguageOperations; declaration_index := 0;
         expected_language_commitment := None |}) = Registered fifth 0 /\
    finish fifth (DriverValues [0]) = (Consumed, OwnedOutput artifact) /\
    foreign_uses (artifact_payload artifact) = [use] /\
    map requested_discharge (guard_descriptions (artifact_payload artifact)) = [true].
Proof.
  intros use origin O R.
  do 6 eexists. repeat split; try reflexivity.
  unfold finish, check_links; cbn.
  rewrite O; cbn. rewrite R; reflexivity.
  all: reflexivity.
Qed.

Print Assumptions registration_returns_exact_descriptor.
Print Assumptions registration_preserves_earlier_descriptors.
Print Assumptions registration_preserves_other_owned_fields.
Print Assumptions construction_failure_consumes_session.
Print Assumptions success_keeps_whole_owned_bundle.
Print Assumptions output_has_actual_root_and_checked_links.
Print Assumptions failed_driver_has_no_artifact.
Print Assumptions finish_always_consumes.
Print Assumptions returned_session_cannot_republish.
Print Assumptions consumed_session_cannot_register.
Print Assumptions fresh_session_has_no_inherited_state.
Print Assumptions origin_erasure_retains_owned_payload.
Print Assumptions semantic_projection_retains_all_owned_requirements.
Print Assumptions changing_diagnostics_does_not_change_semantics.
Print Assumptions changing_occurrence_origins_does_not_change_semantics.
Print Assumptions predicate_obligations_survive_owned_projection.
Print Assumptions fresh_session_cannot_invent_an_empty_root.
Print Assumptions two_results_are_not_silently_elected.
Print Assumptions record_event_preserves_constructed_values.
Print Assumptions session_construction_preserves_generated_arena.
Print Assumptions reachable_drafts_have_constructed_arenas.
Print Assumptions value_link_check_has_actual_targets.
Print Assumptions occurrence_link_check_has_actual_targets.
Print Assumptions predicate_link_check_has_predicate_targets.
Print Assumptions guard_link_check_has_condition_and_predicate_targets.
Print Assumptions checked_bundle_retains_real_reference_targets.
Print Assumptions missing_condition_blocks_output.
Print Assumptions nonpredicate_reference_is_not_observation_evidence.
Print Assumptions reachable_nonempty_foreign_bundle.
