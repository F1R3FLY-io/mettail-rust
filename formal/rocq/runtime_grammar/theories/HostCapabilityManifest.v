From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

(** Runtime grammar data may request host behavior, but it cannot choose or
    grant an implementation.  The installer resolves each request against an
    injected catalog and commits the complete selected manifest. *)
Inductive CapabilityKind : Type :=
| TokenDecoder
| NativeEvaluator
| ForeignBridge.

Inductive RuntimeEffect : Type :=
| Reduce
| Bridge.

Definition capability_kind_eqb (left right : CapabilityKind) : bool :=
  match left, right with
  | TokenDecoder, TokenDecoder
  | NativeEvaluator, NativeEvaluator
  | ForeignBridge, ForeignBridge => true
  | _, _ => false
  end.

Definition runtime_effect_eqb (left right : RuntimeEffect) : bool :=
  match left, right with
  | Reduce, Reduce | Bridge, Bridge => true
  | _, _ => false
  end.

Record CapabilityRequest : Type := {
  request_scope : nat;
  request_kind : CapabilityKind;
  request_name : nat;
  request_effect : RuntimeEffect
}.

Record LogicalCost : Type := {
  cost_base : nat;
  cost_per_input_byte : nat;
  cost_per_value : nat;
  cost_maximum : nat
}.

Record CapabilityManifest : Type := {
  manifest_scope : nat;
  manifest_kind : CapabilityKind;
  manifest_name : nat;
  manifest_code_commitment : nat;
  manifest_abi : nat;
  manifest_effects : list RuntimeEffect;
  manifest_cost : LogicalCost
}.

Definition manifest_matchesb
    (request : CapabilityRequest) (manifest : CapabilityManifest) : bool :=
  Nat.eqb (request_scope request) (manifest_scope manifest) &&
  capability_kind_eqb (request_kind request) (manifest_kind manifest) &&
  Nat.eqb (request_name request) (manifest_name manifest) &&
  existsb
    (runtime_effect_eqb (request_effect request))
    (manifest_effects manifest).

Definition manifest_matches
    (request : CapabilityRequest) (manifest : CapabilityManifest) : Prop :=
  request_scope request = manifest_scope manifest /\
  request_kind request = manifest_kind manifest /\
  request_name request = manifest_name manifest /\
  In (request_effect request) (manifest_effects manifest).

Lemma capability_kind_eqb_sound :
  forall left right,
    capability_kind_eqb left right = true -> left = right.
Proof.
  intros [] []; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma runtime_effect_eqb_sound :
  forall left right,
    runtime_effect_eqb left right = true -> left = right.
Proof.
  intros [] []; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma effect_existsb_sound :
  forall effect effects,
    existsb (runtime_effect_eqb effect) effects = true -> In effect effects.
Proof.
  intros effect effects.
  induction effects as [| candidate rest IH]; simpl; intros H.
  - discriminate.
  - apply orb_true_iff in H. destruct H as [Hcandidate | Hrest].
    + left. symmetry. apply runtime_effect_eqb_sound. exact Hcandidate.
    + right. apply IH. exact Hrest.
Qed.

Lemma manifest_matchesb_sound :
  forall request manifest,
    manifest_matchesb request manifest = true ->
    manifest_matches request manifest.
Proof.
  intros request manifest Hmatches.
  unfold manifest_matchesb in Hmatches.
  repeat rewrite andb_true_iff in Hmatches.
  destruct Hmatches as [[[Hscope Hkind] Hname] Heffect].
  unfold manifest_matches.
  repeat split.
  - apply Nat.eqb_eq. exact Hscope.
  - apply capability_kind_eqb_sound. exact Hkind.
  - apply Nat.eqb_eq. exact Hname.
  - apply effect_existsb_sound. exact Heffect.
Qed.

Definition select_manifest
    (request : CapabilityRequest) (catalog : list CapabilityManifest)
    : option CapabilityManifest :=
  find (manifest_matchesb request) catalog.

(** [bind_worklist] is the functional model of the Rust explicit worklist.
    Failure returns no partial set of bindings. *)
Fixpoint bind_worklist
    (pending : list CapabilityRequest) (catalog : list CapabilityManifest)
    : option (list CapabilityManifest) :=
  match pending with
  | [] => Some []
  | request :: rest =>
      match select_manifest request catalog, bind_worklist rest catalog with
      | Some manifest, Some bound => Some (manifest :: bound)
      | _, _ => None
      end
  end.

Lemma select_manifest_sound :
  forall request catalog manifest,
    select_manifest request catalog = Some manifest ->
    In manifest catalog /\ manifest_matches request manifest.
Proof.
  intros request catalog manifest Hselected.
  unfold select_manifest in Hselected.
  apply find_some in Hselected.
  destruct Hselected as [Hin Hmatches].
  split; [exact Hin |].
  apply manifest_matchesb_sound. exact Hmatches.
Qed.

Theorem iterative_binding_is_total_or_atomic :
  forall pending catalog bound,
    bind_worklist pending catalog = Some bound ->
    Forall2 manifest_matches pending bound /\
    Forall (fun manifest => In manifest catalog) bound.
Proof.
  intros pending.
  induction pending as [| request rest IH]; intros catalog bound Hbound.
  - simpl in Hbound. inversion Hbound; subst. split; constructor.
  - simpl in Hbound.
    destruct (select_manifest request catalog) as [manifest |] eqn:Hselected;
      [| discriminate].
    destruct (bind_worklist rest catalog) as [tail |] eqn:Htail;
      [| discriminate].
    inversion Hbound; subst.
    destruct (select_manifest_sound request catalog manifest Hselected)
      as [Hin Hmatches].
    destruct (IH catalog tail Htail) as [Hpairs Hcatalog].
    split.
    + constructor; assumption.
    + constructor; assumption.
Qed.

Definition effects_authorized
    (authority : list RuntimeEffect) (manifest : CapabilityManifest) : Prop :=
  forall effect, In effect (manifest_effects manifest) -> In effect authority.

Definition invocation_allowed
    (before after : list CapabilityManifest)
    (authority : list RuntimeEffect)
    (request : CapabilityRequest)
    (committed : CapabilityManifest) : Prop :=
  manifest_matches request committed /\
  effects_authorized authority committed /\
  In committed before /\
  In committed after.

Theorem allowed_invocation_authorizes_the_requested_effect :
  forall before after authority request committed,
    invocation_allowed before after authority request committed ->
    In (request_effect request) authority.
Proof.
  intros before after authority request committed
    [Hmatches [Hauthorized [_ _]]].
  destruct Hmatches as [_ [_ [_ Heffect]]].
  apply Hauthorized. exact Heffect.
Qed.

Theorem absent_post_manifest_rejects_completion :
  forall before after authority request committed,
    ~ In committed after ->
    ~ invocation_allowed before after authority request committed.
Proof.
  intros before after authority request committed Habsent
    [_ [_ [_ Hafter]]].
  contradiction.
Qed.

Theorem committed_implementation_fields_are_exact :
  forall before after authority request committed presented,
    invocation_allowed before after authority request committed ->
    presented = committed ->
    manifest_code_commitment presented = manifest_code_commitment committed /\
    manifest_abi presented = manifest_abi committed /\
    manifest_cost presented = manifest_cost committed.
Proof.
  intros before after authority request committed presented _ Hequal.
  subst. repeat split; reflexivity.
Qed.

Theorem binding_is_deterministic :
  forall pending catalog left right,
    bind_worklist pending catalog = Some left ->
    bind_worklist pending catalog = Some right ->
    left = right.
Proof.
  intros pending catalog left right Hleft Hright.
  rewrite Hleft in Hright. inversion Hright. reflexivity.
Qed.

(** Closed built-in operators and carriers are audited interpreter code.  A
    host callback exists only for the explicitly external route. *)
Inductive EvaluationRoute : Type :=
| ClosedBuiltin
| ExternalCapability (request : CapabilityRequest).

Definition invokes_host (route : EvaluationRoute) : bool :=
  match route with
  | ClosedBuiltin => false
  | ExternalCapability _ => true
  end.

Theorem closed_builtin_cannot_dispatch_to_host :
  invokes_host ClosedBuiltin = false.
Proof. reflexivity. Qed.

Theorem every_host_dispatch_is_an_explicit_capability :
  forall route,
    invokes_host route = true ->
    exists request, route = ExternalCapability request.
Proof.
  intros [| request] Hdispatch.
  - discriminate.
  - exists request. reflexivity.
Qed.

Print Assumptions iterative_binding_is_total_or_atomic.
Print Assumptions allowed_invocation_authorizes_the_requested_effect.
Print Assumptions absent_post_manifest_rejects_completion.
Print Assumptions committed_implementation_fields_are_exact.
Print Assumptions binding_is_deterministic.
Print Assumptions closed_builtin_cannot_dispatch_to_host.
Print Assumptions every_host_dispatch_is_an_explicit_capability.
