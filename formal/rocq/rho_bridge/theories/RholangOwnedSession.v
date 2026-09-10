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
  RholangFrontendAdmission RholangFltTransport RholangSourceScope.
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
  private_host_names : list Algebra.HostNameSlot;
  private_payload : SessionPayload
}.
Inductive Session := Open (draft : Draft) | Consumed.
Definition start : Session := Open
  {| private_values := []; private_occurrences := []; private_host_names := [];
     private_payload := empty_payload |}.

Inductive SessionError :=
| SessionAlreadyConsumed
| LoweringFailure (error : Algebra.ConstructionError)
| InvalidResultStack (size : nat)
| DanglingValue (reference : nat)
| DanglingOccurrence (reference : nat)
| DanglingPredicate (reference : nat)
| NonPredicateSite (reference : nat)
| PredicateInputArity (reference : nat).

Definition replace_values (draft : Draft) (values : list Algebra.Value) : Draft :=
  {| private_values := values; private_occurrences := private_occurrences draft;
     private_host_names := private_host_names draft;
     private_payload := private_payload draft |}.
Definition retain_operation_names (draft : Draft) (operation : Construction.ConstructOp) : Draft :=
  {| private_values := private_values draft; private_occurrences := private_occurrences draft;
     private_host_names := private_host_names draft ++ Construction.operation_host_names operation;
     private_payload := private_payload draft |}.
Definition append_foreign_use (payload : SessionPayload) (use : Foreign.ForeignUse) : SessionPayload :=
  {| foreign_uses := foreign_uses payload ++ [use];
     guard_descriptions := guard_descriptions payload;
     provider_requirements := provider_requirements payload;
     fold_requirements := fold_requirements payload; diagnostics := diagnostics payload |}.
Definition replace_payload (draft : Draft) (payload : SessionPayload) : Draft :=
  {| private_values := private_values draft; private_occurrences := private_occurrences draft;
     private_host_names := private_host_names draft;
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
           private_host_names := private_host_names draft;
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

(** Arity establishes the exact ordered association, not lexical resolution.
    The existing producer must resolve both the selector and every fill under
    its actual scope. This check introduces no second lexical environment. *)
Definition check_operation_context (payload : SessionPayload)
    (operation : Construction.ConstructOp) (references : list nat) : option SessionError :=
  match operation with
  | Construction.PendingPredicateOp index =>
    match nth_error (foreign_uses payload) index with
    | None => Some (DanglingPredicate index)
    | Some use =>
      match Foreign.use_role use with
      | Foreign.PredicateSite =>
        if Nat.eqb (List.length references) (S (List.length (Foreign.construction_bindings use)))
        then None else Some (PredicateInputArity index)
      | _ => Some (NonPredicateSite index)
      end
    end
  | _ => None
  end.

(** This is the same checked construction, now inside an owning session.
    A failed construction consumes the session: its partial descriptor table
    cannot be recovered as a successful output by a subsequent finish. *)
Definition construct_in_session (session : Session) (operation : Construction.ConstructOp)
    (references : list nat) : RegistrationResult :=
  match session with
  | Consumed => RegistrationRejected Consumed SessionAlreadyConsumed []
  | Open draft =>
    match check_operation_context (private_payload draft) operation references with
    | Some error => RegistrationRejected Consumed error (diagnostics (private_payload draft))
    | None =>
      match Construction.construction_step (private_values draft) operation references with
      | Construction.ValueAppended values index =>
        Registered (Open (retain_operation_names (replace_values draft values) operation)) index
      | Construction.StepRejected _ error => RegistrationRejected Consumed (LoweringFailure error)
          (diagnostics (private_payload draft))
      end
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
  artifact_host_names : list Algebra.HostNameSlot;
  artifact_payload : SessionPayload
}.
Definition bundle (draft : Draft) (root : nat) : OwnedArtifact :=
  {| artifact_values := private_values draft; artifact_root := root;
     artifact_host_names := private_host_names draft;
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
   artifact_host_names artifact,
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
  private_host_names updated = private_host_names draft /\
  guard_descriptions (private_payload updated) = guard_descriptions (private_payload draft) /\
  provider_requirements (private_payload updated) = provider_requirements (private_payload draft) /\
  fold_requirements (private_payload updated) = fold_requirements (private_payload draft) /\
  diagnostics (private_payload updated) = diagnostics (private_payload draft).
Proof. intros; repeat split; reflexivity. Qed.

Theorem construction_failure_consumes_session : forall draft operation references error,
  check_operation_context (private_payload draft) operation references = None ->
  Construction.construct (private_values draft) operation references = Algebra.ConstructionRejected error ->
  construct_in_session (Open draft) operation references =
    RegistrationRejected Consumed (LoweringFailure error) (diagnostics (private_payload draft)).
Proof.
  intros draft operation references error Context Failure; unfold construct_in_session.
  rewrite Context, (Construction.failed_step_leaves_arena_unchanged _ _ _ _ Failure). reflexivity.
Qed.

Theorem context_failure_consumes_session : forall draft operation references error,
  check_operation_context (private_payload draft) operation references = Some error ->
  construct_in_session (Open draft) operation references =
    RegistrationRejected Consumed error (diagnostics (private_payload draft)).
Proof. intros; unfold construct_in_session; now rewrite H. Qed.

Definition predicate_input_association (use : Foreign.ForeignUse) (references : list nat) :=
  match references with
  | [] => None
  | selector :: fills =>
    if Nat.eqb (List.length fills) (List.length (Foreign.construction_bindings use)) then
      Some ((Foreign.lexical_selector (Foreign.use_capture use), selector),
        combine (Foreign.construction_bindings use) fills)
    else None
  end.

Lemma equal_length_combine_preserves_both_projections : forall A B (left : list A) (right : list B),
  List.length left = List.length right ->
  map fst (combine left right) = left /\ map snd (combine left right) = right.
Proof.
  intros A B left; induction left as [|first rest IH]; intros [|value values] L;
    try discriminate; [split; reflexivity|].
  cbn in L; injection L as L.
  specialize (IH values L) as [F S]. cbn; now rewrite F, S.
Qed.

Theorem pending_context_preserves_exact_input_association : forall payload index references,
  check_operation_context payload (Construction.PendingPredicateOp index) references = None ->
  exists use selector fills,
    nth_error (foreign_uses payload) index = Some use /\
    Foreign.use_role use = Foreign.PredicateSite /\
    references = selector :: fills /\
    predicate_input_association use references = Some
      ((Foreign.lexical_selector (Foreign.use_capture use), selector),
        combine (Foreign.construction_bindings use) fills) /\
    map fst (combine (Foreign.construction_bindings use) fills) = Foreign.construction_bindings use /\
    map snd (combine (Foreign.construction_bindings use) fills) = fills.
Proof.
  intros payload index references H; cbn [check_operation_context] in H.
  destruct (nth_error (foreign_uses payload) index) as [use|] eqn:U; try discriminate.
  destruct (Foreign.use_role use) eqn:R; try discriminate.
  destruct (Nat.eqb (List.length references) (S (List.length (Foreign.construction_bindings use))))
    eqn:L; try discriminate.
  apply Nat.eqb_eq in L. destruct references as [|selector fills]; [discriminate|].
  cbn in L; injection L as L.
  pose proof (equal_length_combine_preserves_both_projections _ _
    (Foreign.construction_bindings use) fills (eq_sym L)) as [F S].
  exists use, selector, fills. repeat split; auto.
  unfold predicate_input_association. rewrite L, Nat.eqb_refl; reflexivity.
Qed.

Theorem session_success_has_context_and_construction : forall draft operation references next index,
  construct_in_session (Open draft) operation references = Registered (Open next) index ->
  check_operation_context (private_payload draft) operation references = None /\
  exists value,
    Construction.construct (private_values draft) operation references = Algebra.Constructed value /\
    nth_error (private_values next) index = Some value.
Proof.
  intros draft operation references next index H; unfold construct_in_session in H.
  destruct (check_operation_context (private_payload draft) operation references) eqn:C; try discriminate.
  destruct (Construction.construction_step (private_values draft) operation references) eqn:S;
    try discriminate.
  inversion H; subst. split; [reflexivity|].
  apply Construction.successful_step_appends_interpretation in S as [value [V [A [I N]]]].
  exists value; split; [exact V|exact N].
Qed.

(** The graph stores the descriptor index and real ordered input values.
    The association theorem above retains the selector lexical reference and
    each fill's ID/name/lexical reference; neither theorem pretends to prove
    that the source producer resolved those references correctly. *)
Theorem successful_pending_atom_has_real_ordered_inputs : forall draft use_index references next index,
  construct_in_session (Open draft) (Construction.PendingPredicateOp use_index) references =
    Registered (Open next) index ->
  check_operation_context (private_payload draft) (Construction.PendingPredicateOp use_index) references = None /\
  exists selector fills,
    Forall2 (fun reference value => nth_error (private_values draft) reference = Some value)
      references (selector :: fills) /\
    nth_error (private_values next) index =
      Some (Algebra.pending_predicate use_index selector fills).
Proof.
  intros draft use_index references next index H.
  apply session_success_has_context_and_construction in H as [C [value [V N]]].
  split; [exact C|].
  apply Construction.construction_uses_exact_ordered_children in V as [children [R I]].
  destruct children as [|selector fills]; [discriminate|].
  cbn [Construction.interpret] in I. inversion I; subst.
  exists selector, fills; auto.
Qed.

Theorem missing_pending_descriptor_rejects : forall draft index references,
  nth_error (foreign_uses (private_payload draft)) index = None ->
  construct_in_session (Open draft) (Construction.PendingPredicateOp index) references =
    RegistrationRejected Consumed (DanglingPredicate index) (diagnostics (private_payload draft)).
Proof.
  intros; apply context_failure_consumes_session.
  cbn [check_operation_context]; now rewrite H.
Qed.

Theorem wrong_pending_role_rejects : forall draft index references use,
  nth_error (foreign_uses (private_payload draft)) index = Some use ->
  Foreign.use_role use <> Foreign.PredicateSite ->
  construct_in_session (Open draft) (Construction.PendingPredicateOp index) references =
    RegistrationRejected Consumed (NonPredicateSite index) (diagnostics (private_payload draft)).
Proof.
  intros; apply context_failure_consumes_session.
  cbn [check_operation_context]; rewrite H.
  destruct (Foreign.use_role use); try reflexivity; contradiction.
Qed.

Theorem missing_or_extra_pending_input_rejects : forall draft index references use,
  nth_error (foreign_uses (private_payload draft)) index = Some use ->
  Foreign.use_role use = Foreign.PredicateSite ->
  List.length references <> S (List.length (Foreign.construction_bindings use)) ->
  construct_in_session (Open draft) (Construction.PendingPredicateOp index) references =
    RegistrationRejected Consumed (PredicateInputArity index) (diagnostics (private_payload draft)).
Proof.
  intros; apply context_failure_consumes_session.
  cbn [check_operation_context]; rewrite H, H0.
  apply Nat.eqb_neq in H1; now rewrite H1.
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
  start = Open {| private_values := []; private_occurrences := []; private_host_names := [];
    private_payload := empty_payload |}.
Proof. reflexivity. Qed.

Theorem origin_erasure_retains_owned_payload : forall draft root,
  (artifact_values (bundle draft root), artifact_root (bundle draft root),
   map fst (artifact_occurrences (bundle draft root)), artifact_payload (bundle draft root)) =
  (private_values draft, root, map fst (private_occurrences draft), private_payload draft).
Proof. reflexivity. Qed.

Theorem semantic_projection_retains_all_owned_requirements : forall draft root,
  semantic_artifact (bundle draft root) =
  (private_values draft, root, map fst (private_occurrences draft), private_host_names draft,
   {| retained_foreign_uses := map Foreign.retain_use (foreign_uses (private_payload draft));
      retained_guards := guard_descriptions (private_payload draft);
      retained_providers := provider_requirements (private_payload draft);
      retained_folds := fold_requirements (private_payload draft) |}).
Proof. reflexivity. Qed.

Theorem changing_diagnostics_does_not_change_semantics :
  forall values root occurrences names uses guards providers folds first second,
  semantic_artifact
    {| artifact_values := values; artifact_root := root; artifact_occurrences := occurrences;
       artifact_host_names := names;
       artifact_payload := {| foreign_uses := uses; guard_descriptions := guards;
         provider_requirements := providers; fold_requirements := folds; diagnostics := first |} |} =
  semantic_artifact
    {| artifact_values := values; artifact_root := root; artifact_occurrences := occurrences;
       artifact_host_names := names;
       artifact_payload := {| foreign_uses := uses; guard_descriptions := guards;
         provider_requirements := providers; fold_requirements := folds; diagnostics := second |} |}.
Proof. reflexivity. Qed.

Theorem changing_occurrence_origins_does_not_change_semantics : forall values root first second names payload,
  map fst first = map fst second ->
  semantic_artifact {| artifact_values := values; artifact_root := root;
    artifact_host_names := names;
    artifact_occurrences := first; artifact_payload := payload |} =
  semantic_artifact {| artifact_values := values; artifact_root := root;
    artifact_host_names := names;
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
  destruct (check_operation_context (private_payload draft) operation references); try discriminate.
  destruct (Construction.construction_step (private_values draft) operation references) eqn:E;
    try discriminate.
  inversion H; subst. cbn [retain_operation_names replace_values private_values].
  eapply Construction.successful_step_retains_generated_image; eauto.
Qed.

(** Reachability excludes forged raw arenas. It is a proof of the concrete
    session transitions, not a supplied validity bit. Producer refinements
    additionally establish the meaning of their descriptors and occurrences. *)
Inductive ReachableDraft : Draft -> Prop :=
| InitialDraft : ReachableDraft
    {| private_values := []; private_occurrences := []; private_host_names := [];
       private_payload := empty_payload |}
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

(** Requirements are recorded at the successful leaf step, not rediscovered
    by a traversal of the finished graph. Recording unrelated descriptors
    cannot alter them. Target binding validates every retained slot before
    producing a host artifact; the private frontend does not resolve names. *)
Theorem successful_construction_retains_exact_host_requirements :
  forall draft operation references next index,
  construct_in_session (Open draft) operation references = Registered (Open next) index ->
  private_host_names next = private_host_names draft ++ Construction.operation_host_names operation.
Proof.
  intros draft operation references next index H; unfold construct_in_session in H.
  destruct (check_operation_context (private_payload draft) operation references); try discriminate.
  destruct (Construction.construction_step (private_values draft) operation references);
    try discriminate. inversion H; reflexivity.
Qed.

Theorem recording_cannot_change_host_requirements : forall draft event next index,
  record_event (Open draft) event = Registered (Open next) index ->
  private_host_names next = private_host_names draft.
Proof.
  intros draft event next index H; destruct event;
    cbn [record_event register_foreign replace_payload append_foreign_use] in H;
    inversion H; reflexivity.
Qed.

Theorem host_name_leaf_registers_exact_slot : forall draft slot,
  construct_in_session (Open draft) (Construction.HostNameOp slot) [] =
    Registered (Open (retain_operation_names
      (replace_values draft (private_values draft ++ [Algebra.host_name slot]))
      (Construction.HostNameOp slot))) (List.length (private_values draft)).
Proof. reflexivity. Qed.

Theorem bundle_preserves_host_binding_requirements : forall draft root,
  artifact_host_names (bundle draft root) = private_host_names draft.
Proof. reflexivity. Qed.

(** GeneratedArena alone forgets the coupled requirement history. The real
    adapter must use private reachable sessions, not accept a caller-assembled
    Draft merely because its value vector has construction provenance. *)
Theorem successful_step_and_finish_retain_host_requirements :
  forall prior operation references next index stack artifact,
  ReachableDraft prior ->
  construct_in_session (Open prior) operation references = Registered (Open next) index ->
  snd (finish (Open next) (DriverValues stack)) = OwnedOutput artifact ->
  ReachableDraft next /\
  artifact_host_names artifact = private_host_names prior ++ Construction.operation_host_names operation.
Proof.
  intros prior operation references next index stack artifact R C F.
  split; [eapply ConstructedDraft; eauto|].
  apply output_has_actual_root_and_checked_links in F as [root [value [S [V [L B]]]]].
  subst artifact. cbn [bundle artifact_host_names].
  now apply successful_construction_retains_exact_host_requirements in C.
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

(** Unlike the ownership-only Boolean witness above, this path constructs a
    real pending atom and makes it the guard condition. The name is still an
    unresolved host requirement; no predicate result or authority is assumed. *)
Theorem reachable_pending_guard_bundle : forall slot use origin,
  Foreign.use_occurrence use = 0 -> Foreign.use_role use = Foreign.PredicateSite ->
  Foreign.construction_bindings use = [] ->
  exists first second third fourth fifth artifact,
    construct_in_session start (Construction.HostNameOp slot) [] = Registered first 0 /\
    record_event first (RecordOccurrence 1 origin) = Registered second 0 /\
    record_event second (RecordForeignUse use) = Registered third 0 /\
    construct_in_session third (Construction.PendingPredicateOp 0) [0] = Registered fourth 1 /\
    record_event fourth (RecordGuard
      {| condition_reference := 1; enclosing_captures := []; predicate_references := [0];
         requested_discharge := true |}) = Registered fifth 0 /\
    finish fifth (DriverValues [1]) = (Consumed, OwnedOutput artifact) /\
    nth_error (artifact_values artifact) 1 =
      Some (Algebra.pending_predicate 0 (Algebra.host_name slot) []) /\
    foreign_uses (artifact_payload artifact) = [use] /\
    artifact_host_names artifact = [slot].
Proof.
  intros slot use origin O R B.
  do 6 eexists. repeat split; try reflexivity.
  unfold construct_in_session; cbn. rewrite R, B; reflexivity.
  reflexivity.
  unfold finish, check_links; cbn. rewrite O; cbn. rewrite R; reflexivity.
  all: reflexivity.
Qed.

(** Direct specialization: the existing driver supplies one owned root, rather
    than an arena index. FoldRequirement is the same descriptor data used above;
    the report below mirrors the existing observational GuardDischargeReport.
    Nothing constructs a neutral arena, executes a provider, or re-lowers a root.

    The private synchronous bracket must call the SAME drive(Seed::Body, env).
    These finite-state laws specify its entry/exit boundary, not Rust execution,
    panic safety of destructors, allocation bounds, or thread-local borrow safety.
    Rust must establish cleanup before return/resume_unwind, keep the bracket
    private and non-suspending, and retain the actual resolver/options/identities.
    Error and unwind payloads are arbitrary data, not correctness premises. *)
Record DirectGuardReport := {
  direct_discharged : nat;
  direct_refuted : list (nat * string);
  direct_residual : nat;
  direct_disagreements : nat
}.
Definition empty_direct_report : DirectGuardReport :=
  {| direct_discharged := 0; direct_refuted := []; direct_residual := 0;
     direct_disagreements := 0 |}.
Record DirectSideOutputs := {
  direct_folds : list FoldRequirement;
  direct_guards : DirectGuardReport
}.
Definition empty_direct_outputs : DirectSideOutputs :=
  {| direct_folds := fold_requirements empty_payload; direct_guards := empty_direct_report |}.
Record DirectSessionState := {
  direct_active : bool;
  direct_outputs : DirectSideOutputs
}.
Definition direct_idle : DirectSessionState :=
  {| direct_active := false; direct_outputs := empty_direct_outputs |}.
Definition direct_started : DirectSessionState :=
  {| direct_active := true; direct_outputs := empty_direct_outputs |}.
Record DirectArtifact := {
  direct_root : Algebra.Value;
  direct_artifact_outputs : DirectSideOutputs
}.
Inductive DirectDriverExit (Error Unwind : Type) :=
| DirectReturned (root : Algebra.Value) (outputs : DirectSideOutputs)
| DirectFailed (error : Error) (partial : DirectSideOutputs)
| DirectUnwound (panic_payload : Unwind) (partial : DirectSideOutputs).
Arguments DirectReturned {Error Unwind} _ _.
Arguments DirectFailed {Error Unwind} _ _.
Arguments DirectUnwound {Error Unwind} _ _.
Inductive DirectResult (Error Unwind : Type) :=
| DirectOwnedOutput (artifact : DirectArtifact)
| DirectNoArtifact (error : Error)
| DirectResumeUnwind (panic_payload : Unwind)
| DirectReentrant.
Arguments DirectOwnedOutput {Error Unwind} _.
Arguments DirectNoArtifact {Error Unwind} _.
Arguments DirectResumeUnwind {Error Unwind} _.
Arguments DirectReentrant {Error Unwind}.

Definition finish_direct {Error Unwind} (outcome : DirectDriverExit Error Unwind)
    : DirectSessionState * DirectResult Error Unwind :=
  (direct_idle, match outcome with
   | DirectReturned root outputs => DirectOwnedOutput
       {| direct_root := root; direct_artifact_outputs := outputs |}
   | DirectFailed error _ => DirectNoArtifact error
   | DirectUnwound panic_payload _ => DirectResumeUnwind panic_payload
   end).

Section DirectPublicBracket.
Context {Body Options Resolver Imports Error Unwind : Type}.
Definition direct_public_context (context : @RholangSourceScope.SourceContext Options Resolver Imports)
    : @RholangSourceScope.SourceContext Options Resolver Imports :=
  {| RholangSourceScope.context_scope := RholangSourceScope.context_scope context;
     RholangSourceScope.context_options := RholangSourceScope.context_options context;
     RholangSourceScope.context_resolver := RholangSourceScope.context_resolver context;
     RholangSourceScope.context_imports := RholangSourceScope.context_imports context;
     RholangSourceScope.context_mode := RholangSourceScope.PublicSource;
     RholangSourceScope.context_pattern := RholangSourceScope.context_pattern context |}.

(** The active check precedes both clearing stale inactive output and invoking
    the driver. The driver parameter denotes the existing Body entry, not an
    additional parser, evaluator, or assumed-correct transition function. *)
Definition prepare_direct_body (state : DirectSessionState) (body : Body)
    (context : @RholangSourceScope.SourceContext Options Resolver Imports)
    (drive_body : Body -> @RholangSourceScope.SourceContext Options Resolver Imports ->
      DirectSessionState -> DirectDriverExit Error Unwind)
    : DirectSessionState * DirectResult Error Unwind :=
  if direct_active state then (state, DirectReentrant)
  else finish_direct (drive_body body (direct_public_context context) direct_started).

Theorem public_direct_context_retains_all_nonmode_inputs : forall context,
  (RholangSourceScope.context_scope (direct_public_context context),
   RholangSourceScope.context_options (direct_public_context context),
   RholangSourceScope.context_resolver (direct_public_context context),
   RholangSourceScope.context_imports (direct_public_context context),
   RholangSourceScope.context_pattern (direct_public_context context)) =
  (RholangSourceScope.context_scope context, RholangSourceScope.context_options context,
   RholangSourceScope.context_resolver context, RholangSourceScope.context_imports context,
   RholangSourceScope.context_pattern context) /\
  RholangSourceScope.context_mode (direct_public_context context) = RholangSourceScope.PublicSource.
Proof. intro; split; reflexivity. Qed.

Theorem direct_entry_clears_inactive_side_outputs : forall stale body context driver,
  prepare_direct_body {| direct_active := false; direct_outputs := stale |} body context driver =
  finish_direct (driver body (direct_public_context context) direct_started).
Proof. reflexivity. Qed.

Theorem reentrant_direct_entry_preserves_active_payload : forall outputs body context driver,
  prepare_direct_body {| direct_active := true; direct_outputs := outputs |} body context driver =
  ({| direct_active := true; direct_outputs := outputs |}, DirectReentrant).
Proof. reflexivity. Qed.

Theorem reentrant_direct_entry_is_independent_of_driver : forall outputs body context first second,
  prepare_direct_body {| direct_active := true; direct_outputs := outputs |} body context first =
  prepare_direct_body {| direct_active := true; direct_outputs := outputs |} body context second.
Proof. reflexivity. Qed.

Theorem successful_direct_preparation_keeps_exact_driver_payload :
    forall stale body context driver root outputs,
  driver body (direct_public_context context) direct_started = DirectReturned root outputs ->
  prepare_direct_body {| direct_active := false; direct_outputs := stale |} body context driver =
  (direct_idle, DirectOwnedOutput {| direct_root := root; direct_artifact_outputs := outputs |}).
Proof. intros. unfold prepare_direct_body; cbn [direct_active]. now rewrite H. Qed.

Theorem failed_direct_preparation_cleans_before_propagation :
    forall stale body context driver error partial,
  driver body (direct_public_context context) direct_started = DirectFailed error partial ->
  prepare_direct_body {| direct_active := false; direct_outputs := stale |} body context driver =
  (direct_idle, DirectNoArtifact error).
Proof. intros. unfold prepare_direct_body; cbn [direct_active]. now rewrite H. Qed.

Theorem unwound_direct_preparation_cleans_before_resumption :
    forall stale body context driver panic_payload partial,
  driver body (direct_public_context context) direct_started = DirectUnwound panic_payload partial ->
  prepare_direct_body {| direct_active := false; direct_outputs := stale |} body context driver =
  (direct_idle, DirectResumeUnwind panic_payload).
Proof. intros. unfold prepare_direct_body; cbn [direct_active]. now rewrite H. Qed.

Theorem finished_direct_request_cannot_contaminate_next_request :
    forall (outcome : DirectDriverExit Error Unwind) body context driver,
  prepare_direct_body (fst (finish_direct outcome)) body context driver =
  prepare_direct_body direct_idle body context driver.
Proof. reflexivity. Qed.
End DirectPublicBracket.

Theorem direct_start_contains_no_prior_folds_or_guard_report :
  direct_folds (direct_outputs direct_started) = [] /\
  direct_guards (direct_outputs direct_started) = empty_direct_report /\
  direct_active direct_started = true.
Proof. repeat split; reflexivity. Qed.

Theorem every_direct_exit_releases_all_private_outputs : forall Error Unwind
    (outcome : DirectDriverExit Error Unwind), fst (finish_direct outcome) = direct_idle.
Proof. reflexivity. Qed.

(** Legacy operations must not bypass the owned bracket through a resolver or
    reflector callback. Raw lowering has a Result-returning API and rejects
    with the reentrant error. The four legacy accumulator accessors have no
    error result in their existing signatures, so they reject at their API
    boundary by panicking, before borrowing or changing either accumulator.

    The continuation below represents the existing operation AFTER its gate:
    raw driver execution, or the legacy take/clear operation. Its behavior is
    arbitrary. The active branch does not apply it and preserves the complete
    state; the inactive branch retains its exact result and state transition.
    The private owner's clear/take and driver entry are deliberately not legacy
    operations: they remain inside prepare_direct_body and finish_direct.

    Refusal is an observation of this model, not a Rust panic implementation.
    A callback that catches an accessor panic retains the active state. If the
    panic escapes the driver, it is a DirectUnwound exit and the existing
    unwound_direct_preparation_cleans_before_resumption law applies. Concrete
    Rust must establish the gate before callbacks, TLS borrows and driver work;
    these equations do not prove Rust borrow safety or destructor behavior. *)
Inductive DirectLegacyOperation :=
| LegacyRawLowering
| LegacyTakeFolds
| LegacyClearFolds
| LegacyTakeGuardReport
| LegacyClearGuardReport.
Inductive DirectLegacyRefusal :=
| LegacyReentrantError
| LegacyAccessorPanic.
Definition direct_legacy_refusal (operation : DirectLegacyOperation) : DirectLegacyRefusal :=
  match operation with
  | LegacyRawLowering => LegacyReentrantError
  | LegacyTakeFolds | LegacyClearFolds | LegacyTakeGuardReport | LegacyClearGuardReport =>
      LegacyAccessorPanic
  end.
Inductive DirectLegacyResult (A : Type) :=
| LegacyReturned (value : A)
| LegacyRefused (refusal : DirectLegacyRefusal).
Arguments LegacyReturned {A} _.
Arguments LegacyRefused {A} _.

Definition gate_direct_legacy_operation {A} (state : DirectSessionState)
    (operation : DirectLegacyOperation)
    (after_gate : DirectSessionState -> DirectSessionState * A)
    : DirectSessionState * DirectLegacyResult A :=
  if direct_active state then (state, LegacyRefused (direct_legacy_refusal operation))
  else let '(next, value) := after_gate state in (next, LegacyReturned value).

Theorem active_legacy_operation_preserves_exact_owned_state : forall A outputs operation
    (after_gate : DirectSessionState -> DirectSessionState * A),
  gate_direct_legacy_operation
    {| direct_active := true; direct_outputs := outputs |} operation after_gate =
  ({| direct_active := true; direct_outputs := outputs |},
   LegacyRefused (direct_legacy_refusal operation)).
Proof. reflexivity. Qed.

Theorem active_legacy_operation_is_independent_of_continuation : forall A outputs operation
    (first second : DirectSessionState -> DirectSessionState * A),
  gate_direct_legacy_operation
    {| direct_active := true; direct_outputs := outputs |} operation first =
  gate_direct_legacy_operation
    {| direct_active := true; direct_outputs := outputs |} operation second.
Proof. reflexivity. Qed.

Theorem inactive_legacy_operation_retains_exact_behavior : forall A outputs operation
    (after_gate : DirectSessionState -> DirectSessionState * A),
  gate_direct_legacy_operation
    {| direct_active := false; direct_outputs := outputs |} operation after_gate =
  let '(next, value) := after_gate {| direct_active := false; direct_outputs := outputs |} in
  (next, LegacyReturned value).
Proof. reflexivity. Qed.

Theorem active_raw_lowering_returns_reentrant_error : forall A outputs
    (driver : DirectSessionState -> DirectSessionState * A),
  gate_direct_legacy_operation
    {| direct_active := true; direct_outputs := outputs |} LegacyRawLowering driver =
  ({| direct_active := true; direct_outputs := outputs |}, LegacyRefused LegacyReentrantError).
Proof. reflexivity. Qed.

Theorem active_legacy_accessor_panics_without_payload_change : forall A outputs operation
    (accessor : DirectSessionState -> DirectSessionState * A),
  operation <> LegacyRawLowering ->
  gate_direct_legacy_operation
    {| direct_active := true; direct_outputs := outputs |} operation accessor =
  ({| direct_active := true; direct_outputs := outputs |}, LegacyRefused LegacyAccessorPanic).
Proof.
  intros A outputs operation accessor H.
  destruct operation; [exfalso; apply H; reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

(** The current held-fold channel carries an unsigned byte site. Index 255
    is representable; the NEXT request at length 256 is not. The continuation
    stands for the existing fingerprint/channel construction and recording:
    a rejected index never invokes it. No channel identity is fabricated here. *)
Definition checked_direct_fold_site (index : nat) : option nat :=
  if index <=? 255 then Some index else None.
Definition with_checked_direct_fold_site {A} (index : nat) (after_check : nat -> A) : option A :=
  match checked_direct_fold_site index with
  | Some admitted => Some (after_check admitted)
  | None => None
  end.
Definition record_direct_fold (outputs : DirectSideOutputs) (kind : FoldKind)
    (width : Z) (commitment : string) : option DirectSideOutputs :=
  with_checked_direct_fold_site (List.length (direct_folds outputs)) (fun index =>
    {| direct_folds := direct_folds outputs ++
         [{| fold_kind := kind; fold_width := width; fold_site_index := index;
             fold_language_commitment := commitment |}];
       direct_guards := direct_guards outputs |}).

Theorem direct_fold_index_check_is_exact : forall index admitted,
  checked_direct_fold_site index = Some admitted <-> admitted = index /\ index <= 255.
Proof.
  intros index admitted. unfold checked_direct_fold_site.
  destruct (index <=? 255) eqn:H; [apply Nat.leb_le in H|apply Nat.leb_gt in H].
  - split.
    + intro E. split; [congruence|exact H].
    + intros [E _]. subst admitted. reflexivity.
  - split; [discriminate|intros [_ E]; lia].
Qed.

Theorem fold_index_overflow_prevents_followup : forall A index (after_check : nat -> A),
  256 <= index -> with_checked_direct_fold_site index after_check = None.
Proof.
  intros A index after_check H. unfold with_checked_direct_fold_site, checked_direct_fold_site.
  assert ((index <=? 255) = false) as E by (apply Nat.leb_gt; lia). now rewrite E.
Qed.

Theorem checked_fold_recording_retains_exact_index_and_guard_report :
    forall outputs kind width commitment,
  List.length (direct_folds outputs) <= 255 ->
  record_direct_fold outputs kind width commitment = Some
    {| direct_folds := direct_folds outputs ++
         [{| fold_kind := kind; fold_width := width;
             fold_site_index := List.length (direct_folds outputs);
             fold_language_commitment := commitment |}];
       direct_guards := direct_guards outputs |}.
Proof.
  intros outputs kind width commitment H.
  unfold record_direct_fold, with_checked_direct_fold_site, checked_direct_fold_site.
  apply Nat.leb_le in H. now rewrite H.
Qed.

Theorem overflowing_fold_recording_has_no_updated_payload : forall outputs kind width commitment,
  256 <= List.length (direct_folds outputs) ->
  record_direct_fold outputs kind width commitment = None.
Proof. intros. apply fold_index_overflow_prevents_followup. assumption. Qed.

Example direct_fold_byte_boundary_is_inclusive :
  checked_direct_fold_site 0 = Some 0 /\ checked_direct_fold_site 255 = Some 255 /\
  checked_direct_fold_site 256 = None.
Proof. repeat split; reflexivity. Qed.

Print Assumptions public_direct_context_retains_all_nonmode_inputs.
Print Assumptions direct_entry_clears_inactive_side_outputs.
Print Assumptions reentrant_direct_entry_preserves_active_payload.
Print Assumptions reentrant_direct_entry_is_independent_of_driver.
Print Assumptions successful_direct_preparation_keeps_exact_driver_payload.
Print Assumptions failed_direct_preparation_cleans_before_propagation.
Print Assumptions unwound_direct_preparation_cleans_before_resumption.
Print Assumptions finished_direct_request_cannot_contaminate_next_request.
Print Assumptions direct_start_contains_no_prior_folds_or_guard_report.
Print Assumptions every_direct_exit_releases_all_private_outputs.
Print Assumptions active_legacy_operation_preserves_exact_owned_state.
Print Assumptions active_legacy_operation_is_independent_of_continuation.
Print Assumptions inactive_legacy_operation_retains_exact_behavior.
Print Assumptions active_raw_lowering_returns_reentrant_error.
Print Assumptions active_legacy_accessor_panics_without_payload_change.
Print Assumptions direct_fold_index_check_is_exact.
Print Assumptions fold_index_overflow_prevents_followup.
Print Assumptions checked_fold_recording_retains_exact_index_and_guard_report.
Print Assumptions overflowing_fold_recording_has_no_updated_payload.
Print Assumptions direct_fold_byte_boundary_is_inclusive.

Print Assumptions registration_returns_exact_descriptor.
Print Assumptions registration_preserves_earlier_descriptors.
Print Assumptions registration_preserves_other_owned_fields.
Print Assumptions construction_failure_consumes_session.
Print Assumptions context_failure_consumes_session.
Print Assumptions equal_length_combine_preserves_both_projections.
Print Assumptions pending_context_preserves_exact_input_association.
Print Assumptions session_success_has_context_and_construction.
Print Assumptions successful_pending_atom_has_real_ordered_inputs.
Print Assumptions missing_pending_descriptor_rejects.
Print Assumptions wrong_pending_role_rejects.
Print Assumptions missing_or_extra_pending_input_rejects.
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
Print Assumptions reachable_pending_guard_bundle.
Print Assumptions successful_construction_retains_exact_host_requirements.
Print Assumptions recording_cannot_change_host_requirements.
Print Assumptions host_name_leaf_registers_exact_slot.
Print Assumptions bundle_preserves_host_binding_requirements.
Print Assumptions successful_step_and_finish_retain_host_requirements.
