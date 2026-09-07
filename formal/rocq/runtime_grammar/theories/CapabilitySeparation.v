From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Inductive LanguageRight : Type :=
| Parse
| Construct
| Match
| Observe
| ReflectAst
| Reduce
| Bridge
| Publish
| Introspect
| Check
| SearchProof
| Spend.

Inductive SpaceRight : Type :=
| Gensym
| Produce
| Consume
| InstallContinuation
| Checkpoint
| Replay
| InspectSpace.

Definition language_right_eqb (left right : LanguageRight) : bool :=
  match left, right with
  | Parse, Parse
  | Construct, Construct
  | Match, Match
  | Observe, Observe
  | ReflectAst, ReflectAst
  | Reduce, Reduce
  | Bridge, Bridge
  | Publish, Publish
  | Introspect, Introspect
  | Check, Check
  | SearchProof, SearchProof
  | Spend, Spend => true
  | _, _ => false
  end.

Definition space_right_eqb (left right : SpaceRight) : bool :=
  match left, right with
  | Gensym, Gensym
  | Produce, Produce
  | Consume, Consume
  | InstallContinuation, InstallContinuation
  | Checkpoint, Checkpoint
  | Replay, Replay
  | InspectSpace, InspectSpace => true
  | _, _ => false
  end.

Lemma language_right_eqb_sound :
  forall left right, language_right_eqb left right = true -> left = right.
Proof.
  intros left right. destruct left, right; simpl; intros H;
    try discriminate; reflexivity.
Qed.

Lemma language_right_eqb_complete :
  forall left right, left = right -> language_right_eqb left right = true.
Proof. intros left right ->. destruct right; reflexivity. Qed.

Lemma space_right_eqb_sound :
  forall left right, space_right_eqb left right = true -> left = right.
Proof.
  intros left right. destruct left, right; simpl; intros H;
    try discriminate; reflexivity.
Qed.

Lemma space_right_eqb_complete :
  forall left right, left = right -> space_right_eqb left right = true.
Proof. intros left right ->. destruct right; reflexivity. Qed.

Definition has_language_right
    (right : LanguageRight) (rights : list LanguageRight) : bool :=
  existsb (language_right_eqb right) rights.

Definition has_space_right
    (right : SpaceRight) (rights : list SpaceRight) : bool :=
  existsb (space_right_eqb right) rights.

Lemma has_language_right_sound :
  forall right rights,
    has_language_right right rights = true -> In right rights.
Proof.
  intros right rights H.
  unfold has_language_right in H.
  apply existsb_exists in H as [candidate [Hin Heq]].
  apply language_right_eqb_sound in Heq. subst candidate. exact Hin.
Qed.

Lemma has_language_right_complete :
  forall right rights,
    In right rights -> has_language_right right rights = true.
Proof.
  intros right rights Hin.
  unfold has_language_right. apply existsb_exists.
  exists right. split; [exact Hin |].
  apply language_right_eqb_complete. reflexivity.
Qed.

Lemma has_space_right_sound :
  forall right rights,
    has_space_right right rights = true -> In right rights.
Proof.
  intros right rights H.
  unfold has_space_right in H.
  apply existsb_exists in H as [candidate [Hin Heq]].
  apply space_right_eqb_sound in Heq. subst candidate. exact Hin.
Qed.

Lemma has_space_right_complete :
  forall right rights,
    In right rights -> has_space_right right rights = true.
Proof.
  intros right rights Hin.
  unfold has_space_right. apply existsb_exists.
  exists right. split; [exact Hin |].
  apply space_right_eqb_complete. reflexivity.
Qed.

Definition language_attenuates
    (child parent : list LanguageRight) : Prop :=
  forall right, In right child -> In right parent.

Definition space_attenuates
    (child parent : list SpaceRight) : Prop :=
  forall right, In right child -> In right parent.

Theorem language_attenuation_reflexive :
  forall rights, language_attenuates rights rights.
Proof. unfold language_attenuates. auto. Qed.

Theorem language_attenuation_transitive :
  forall first second third,
    language_attenuates first second ->
    language_attenuates second third ->
    language_attenuates first third.
Proof.
  unfold language_attenuates. intros first second third Hfirst Hsecond right Hin.
  apply Hsecond, Hfirst, Hin.
Qed.

Theorem space_attenuation_reflexive :
  forall rights, space_attenuates rights rights.
Proof. unfold space_attenuates. auto. Qed.

Theorem space_attenuation_transitive :
  forall first second third,
    space_attenuates first second ->
    space_attenuates second third ->
    space_attenuates first third.
Proof.
  unfold space_attenuates. intros first second third Hfirst Hsecond right Hin.
  apply Hsecond, Hfirst, Hin.
Qed.

Definition grant_requested_language_rights
    (requested granted : list LanguageRight) : list LanguageRight :=
  filter (fun right => has_language_right right granted) requested.

Definition grant_requested_space_rights
    (requested granted : list SpaceRight) : list SpaceRight :=
  filter (fun right => has_space_right right granted) requested.

Theorem requested_language_rights_cannot_amplify_grants :
  forall requested granted,
    language_attenuates
      (grant_requested_language_rights requested granted) granted.
Proof.
  unfold language_attenuates, grant_requested_language_rights.
  intros requested granted right Hin.
  apply filter_In in Hin as [_ Hgranted].
  apply has_language_right_sound. exact Hgranted.
Qed.

Theorem requested_language_rights_cannot_invent_requests :
  forall requested granted,
    language_attenuates
      (grant_requested_language_rights requested granted) requested.
Proof.
  unfold language_attenuates, grant_requested_language_rights.
  intros requested granted right Hin.
  apply filter_In in Hin as [Hrequested _]. exact Hrequested.
Qed.

Theorem requested_space_rights_cannot_amplify_grants :
  forall requested granted,
    space_attenuates
      (grant_requested_space_rights requested granted) granted.
Proof.
  unfold space_attenuates, grant_requested_space_rights.
  intros requested granted right Hin.
  apply filter_In in Hin as [_ Hgranted].
  apply has_space_right_sound. exact Hgranted.
Qed.

Theorem requested_space_rights_cannot_invent_requests :
  forall requested granted,
    space_attenuates
      (grant_requested_space_rights requested granted) requested.
Proof.
  unfold space_attenuates, grant_requested_space_rights.
  intros requested granted right Hin.
  apply filter_In in Hin as [Hrequested _]. exact Hrequested.
Qed.

Record Authority : Type := {
  language_rights : list LanguageRight;
  space_rights : list SpaceRight;
  proof_search_right : bool;
  factory_right : bool
}.

Definition authority_attenuates (child parent : Authority) : Prop :=
  language_attenuates (language_rights child) (language_rights parent) /\
  space_attenuates (space_rights child) (space_rights parent) /\
  (proof_search_right child = true -> proof_search_right parent = true) /\
  (factory_right child = true -> factory_right parent = true).

Definition mint_authority (requested granted : Authority) : Authority :=
  {| language_rights :=
       grant_requested_language_rights
         (language_rights requested) (language_rights granted);
     space_rights :=
       grant_requested_space_rights
         (space_rights requested) (space_rights granted);
     proof_search_right :=
       proof_search_right requested && proof_search_right granted;
     factory_right := factory_right requested && factory_right granted |}.

Theorem specification_requests_never_grant_authority :
  forall requested granted,
    authority_attenuates (mint_authority requested granted) granted.
Proof.
  intros requested granted. unfold authority_attenuates, mint_authority. simpl.
  repeat split.
  - apply requested_language_rights_cannot_amplify_grants.
  - apply requested_space_rights_cannot_amplify_grants.
  - intros H. apply andb_true_iff in H as [_ Hgranted]. exact Hgranted.
  - intros H. apply andb_true_iff in H as [_ Hgranted]. exact Hgranted.
Qed.

Theorem minted_authority_contains_only_requested_rights :
  forall requested granted,
    authority_attenuates (mint_authority requested granted) requested.
Proof.
  intros requested granted. unfold authority_attenuates, mint_authority. simpl.
  repeat split.
  - apply requested_language_rights_cannot_invent_requests.
  - apply requested_space_rights_cannot_invent_requests.
  - intros H. apply andb_true_iff in H as [Hrequested _]. exact Hrequested.
  - intros H. apply andb_true_iff in H as [Hrequested _]. exact Hrequested.
Qed.

(** Runtime parsing has an effect row.  Pure recognition requires only
    [Parse]; host token decoding/native evaluation additionally requires
    [Reduce], and foreign-language delegation additionally requires [Bridge].
    Grammar composition combines rows by ordinary list union; authorization
    checks every induced right against one installed-handle snapshot. *)
Inductive RuntimeEffect : Type :=
| HostEvaluation
| ForeignBridge.

Definition runtime_effect_eqb (left right : RuntimeEffect) : bool :=
  match left, right with
  | HostEvaluation, HostEvaluation
  | ForeignBridge, ForeignBridge => true
  | _, _ => false
  end.

Definition required_effect_right (effect : RuntimeEffect) : LanguageRight :=
  match effect with
  | HostEvaluation => Reduce
  | ForeignBridge => Bridge
  end.

Definition runtime_operation_rights
    (effects : list RuntimeEffect) : list LanguageRight :=
  Parse :: map required_effect_right effects.

Definition effects_authorized
    (effects : list RuntimeEffect) (rights : list LanguageRight) : Prop :=
  forall effect, In effect effects -> In (required_effect_right effect) rights.

Theorem runtime_operation_authorization_covers_parse :
  forall effects, In Parse (runtime_operation_rights effects).
Proof. intros effects. unfold runtime_operation_rights. simpl. auto. Qed.

Theorem runtime_operation_authorization_covers_every_effect :
  forall effects,
    effects_authorized effects (runtime_operation_rights effects).
Proof.
  unfold effects_authorized, runtime_operation_rights.
  intros effects effect Heffect. simpl. right.
  apply in_map. exact Heffect.
Qed.

Theorem parse_only_authority_is_inert_for_runtime_effects :
  forall effect, ~ In (required_effect_right effect) [Parse].
Proof.
  intros effect Hin. destruct effect; simpl in Hin.
  - destruct Hin as [Hequal | Himpossible]; [discriminate | contradiction].
  - destruct Hin as [Hequal | Himpossible]; [discriminate | contradiction].
Qed.

Definition compose_runtime_effects
    (left right : list RuntimeEffect) : list RuntimeEffect :=
  left ++ filter
    (fun effect => negb (existsb (runtime_effect_eqb effect) left)) right.

Lemma runtime_effect_eqb_sound :
  forall left right, runtime_effect_eqb left right = true -> left = right.
Proof.
  intros left right. destruct left, right; simpl; intros H;
    try discriminate; reflexivity.
Qed.

Theorem composed_runtime_effect_is_from_an_operand :
  forall left right effect,
    In effect (compose_runtime_effects left right) ->
    In effect left \/ In effect right.
Proof.
  intros left right effect Hcomposed.
  unfold compose_runtime_effects in Hcomposed.
  apply in_app_or in Hcomposed as [Hleft | Hright].
  - left. exact Hleft.
  - apply filter_In in Hright as [Hright _]. right. exact Hright.
Qed.

Theorem composed_runtime_effects_preserve_authorization :
  forall left right rights,
    effects_authorized left rights ->
    effects_authorized right rights ->
    effects_authorized (compose_runtime_effects left right) rights.
Proof.
  unfold effects_authorized.
  intros left right rights Hleft Hright effect Hcomposed.
  apply composed_runtime_effect_is_from_an_operand in Hcomposed as [Hin | Hin].
  - apply Hleft. exact Hin.
  - apply Hright. exact Hin.
Qed.

Record LiveAuthority : Type := {
  authority_epoch : nat;
  live_authority : Authority
}.

Definition language_commit_allowed
    (prepared_epoch : nat) (required : LanguageRight)
    (live : LiveAuthority) : bool :=
  Nat.eqb prepared_epoch (authority_epoch live) &&
  has_language_right required (language_rights (live_authority live)).

Definition space_commit_allowed
    (prepared_epoch : nat) (required : SpaceRight)
    (live : LiveAuthority) : bool :=
  Nat.eqb prepared_epoch (authority_epoch live) &&
  has_space_right required (space_rights (live_authority live)).

Theorem changed_epoch_rejects_language_commit :
  forall prepared_epoch required live,
    prepared_epoch <> authority_epoch live ->
    language_commit_allowed prepared_epoch required live = false.
Proof.
  intros prepared_epoch required live Hstale.
  unfold language_commit_allowed.
  apply Nat.eqb_neq in Hstale. rewrite Hstale. reflexivity.
Qed.

Theorem changed_epoch_rejects_space_commit :
  forall prepared_epoch required live,
    prepared_epoch <> authority_epoch live ->
    space_commit_allowed prepared_epoch required live = false.
Proof.
  intros prepared_epoch required live Hstale.
  unfold space_commit_allowed.
  apply Nat.eqb_neq in Hstale. rewrite Hstale. reflexivity.
Qed.

Print Assumptions specification_requests_never_grant_authority.
Print Assumptions minted_authority_contains_only_requested_rights.
Print Assumptions runtime_operation_authorization_covers_parse.
Print Assumptions runtime_operation_authorization_covers_every_effect.
Print Assumptions parse_only_authority_is_inert_for_runtime_effects.
Print Assumptions composed_runtime_effects_preserve_authorization.
Print Assumptions changed_epoch_rejects_language_commit.
Print Assumptions changed_epoch_rejects_space_commit.
