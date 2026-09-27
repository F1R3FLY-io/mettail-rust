(** The installed runtime adapter boundary, not a new parser model.

    Rust correspondence required before activating this interface:
    - WeightedParse keeps DynamicValue syntax/value and Option<ProductionId>.
      Its weight is a tagged ExactParseCost/DerivationRank pair or the complete
      original rigail::LexicographicWeight. No float conversion, fabricated
      rank, or cross-variant ordering is supplied by this interface.
    - InstalledLanguageTable owns an optional runtime factory. Image/language
      and host-manifest admission precede preparation; every prepared backend
      owns its descriptors before commit_batch can publish any entry.
    - InstalledLanguage retains RuntimeImage metadata and the admitted image.
      Its private capability-bound RuntimeParser produces the lexical session;
      the backend receives that same session, category and effective policy.
      Invocation has no factory parameter and performs no descriptor rebuild.
    - The backend semantic epoch participates in the symbolic-template key.
      Epoch equality promises stable implementation semantics; this file
      proves key separation, not hash collision resistance or that promise.

    Existing InstalledLanguageAuthority supplies admission-batch and sealed
    authority laws. StructuralTemplate supplies the cache soundness theorem.
    Here those models are reused at the new interface. Source correspondence,
    preparation/work/allocation bounds, cancellation and complete enumeration
    remain separate obligations. In particular, a successful bounded walker
    result is not declared exhaustive by this model.

    Weight payloads are universally quantified, unchanged values. Instantiating
    WpdaWeight with the original five-component Rust record retains even its
    primary floating-point representation: we neither model it as a natural
    cost nor claim new semiring or floating-point laws. The observer theorem
    covers each original field, including primary.to_bits(). *)
From Stdlib Require Import List.
From RuntimeGrammar Require Import InstalledLanguageAuthority StructuralTemplate.
Import ListNotations.

Module InstalledRuntimeBackend.

Section WeightTransport.
  Context {ExactCost Rank WpdaWeight Value Production : Type}.

  Inductive ParseWeight : Type :=
  | ExactWeight : ExactCost -> Rank -> ParseWeight
  | SharedWpdaWeight : WpdaWeight -> ParseWeight.

  Record Parse : Type := {
    parse_syntax : Value;
    parse_value : Value;
    parse_weight : ParseWeight;
    parse_production : option Production
  }.

  Definition exact_payload (weight : ParseWeight) : option (ExactCost * Rank) :=
    match weight with
    | ExactWeight cost rank => Some (cost, rank)
    | SharedWpdaWeight _ => None
    end.

  Definition wpda_payload (weight : ParseWeight) : option WpdaWeight :=
    match weight with
    | ExactWeight _ _ => None
    | SharedWpdaWeight original => Some original
    end.

  Definition wrap_wpda (syntax value : Value) (production : option Production)
      (weight : WpdaWeight) : Parse :=
    {| parse_syntax := syntax; parse_value := value;
       parse_weight := SharedWpdaWeight weight;
       parse_production := production |}.

  Theorem exact_payload_roundtrip : forall cost rank,
    exact_payload (ExactWeight cost rank) = Some (cost, rank).
  Proof. reflexivity. Qed.

  Theorem wpda_payload_roundtrip : forall weight,
    wpda_payload (SharedWpdaWeight weight) = Some weight.
  Proof. reflexivity. Qed.

  Theorem wpda_transport_preserves_every_observation :
    forall (Observation : Type) (observe : WpdaWeight -> Observation) weight,
      option_map observe (wpda_payload (SharedWpdaWeight weight)) =
      Some (observe weight).
  Proof. reflexivity. Qed.

  Theorem wrapping_preserves_payload_and_production :
    forall syntax value production weight,
      parse_syntax (wrap_wpda syntax value production weight) = syntax /\
      parse_value (wrap_wpda syntax value production weight) = value /\
      parse_production (wrap_wpda syntax value production weight) = production /\
      wpda_payload (parse_weight (wrap_wpda syntax value production weight)) =
        Some weight.
  Proof. intros. repeat split; reflexivity. Qed.

  Theorem wpda_has_no_fabricated_exact_payload : forall weight,
    exact_payload (SharedWpdaWeight weight) = None.
  Proof. reflexivity. Qed.

  Theorem exact_has_no_fabricated_wpda_payload : forall cost rank,
    wpda_payload (ExactWeight cost rank) = None.
  Proof. reflexivity. Qed.

  Definition wrap_roster
      (readings : list (Value * Value * option Production * WpdaWeight)) :=
    map (fun '(syntax, value, production, weight) =>
      wrap_wpda syntax value production weight) readings.

  Theorem wrapping_preserves_roster_length : forall readings,
    length (wrap_roster readings) = length readings.
  Proof. intro readings. unfold wrap_roster. apply length_map. Qed.

  Theorem wrapping_preserves_weight_roster_in_order : forall readings,
    map (fun parse => wpda_payload (parse_weight parse)) (wrap_roster readings) =
    map (fun '(_, _, _, weight) => Some weight) readings.
  Proof.
    intro readings. unfold wrap_roster. rewrite map_map.
    apply map_ext. intros [[[syntax value] production] weight]. reflexivity.
  Qed.

  (** The functions below are the existing comparators, not assumed ordering
      laws. Same-variant calls delegate verbatim; mixed calls are unavailable.
      A global derived Ord on the Rust enum would violate this contract. *)
  Definition compare_same_variant
      (exact_compare : (ExactCost * Rank) -> (ExactCost * Rank) -> comparison)
      (wpda_compare : WpdaWeight -> WpdaWeight -> comparison)
      (left right : ParseWeight) : option comparison :=
    match left, right with
    | ExactWeight lc lr, ExactWeight rc rr =>
        Some (exact_compare (lc, lr) (rc, rr))
    | SharedWpdaWeight lw, SharedWpdaWeight rw => Some (wpda_compare lw rw)
    | _, _ => None
    end.

  Theorem exact_comparison_is_original : forall exact_compare wpda_compare lc lr rc rr,
    compare_same_variant exact_compare wpda_compare
      (ExactWeight lc lr) (ExactWeight rc rr) =
    Some (exact_compare (lc, lr) (rc, rr)).
  Proof. reflexivity. Qed.

  Theorem wpda_comparison_is_original : forall exact_compare wpda_compare left right,
    compare_same_variant exact_compare wpda_compare
      (SharedWpdaWeight left) (SharedWpdaWeight right) =
    Some (wpda_compare left right).
  Proof. reflexivity. Qed.

  Theorem mixed_comparisons_are_unavailable : forall exact_compare wpda_compare cost rank weight,
    compare_same_variant exact_compare wpda_compare
      (ExactWeight cost rank) (SharedWpdaWeight weight) = None /\
    compare_same_variant exact_compare wpda_compare
      (SharedWpdaWeight weight) (ExactWeight cost rank) = None.
  Proof. intros. split; reflexivity. Qed.
End WeightTransport.

Section FactoryPreparation.
  Context {Inputs Backend EngineEpoch : Type}.

  (** Inputs are the exact immutable grammar/image/preparation-policy bundle.
      Admission is the result of the existing checks, never a caller-supplied
      claim replacing ImageAdmission or host-manifest validation. *)
  Record Request : Type := {
    request_image : ParserImageAdmission;
    request_inputs : Inputs
  }.

  Record Factory : Type := {
    factory_epoch : EngineEpoch;
    prepare_backend : Inputs -> option Backend
  }.

  Record Prepared : Type := {
    prepared_commitment : Commitment;
    prepared_inputs : Inputs;
    prepared_backend : Backend;
    prepared_epoch : EngineEpoch
  }.

  Inductive PreparationError :=
  | RejectedImage
  | MissingRuntimeFactory
  | RejectedBackend.

  Definition prepare_one (factory : option Factory) (request : Request)
      : PreparationError + Prepared :=
    match request_image request with
    | ImageRejected => inl RejectedImage
    | ImageAdmitted commitment =>
      match factory with
      | None => inl MissingRuntimeFactory
      | Some implementation =>
        match prepare_backend implementation (request_inputs request) with
        | None => inl RejectedBackend
        | Some backend => inr
            {| prepared_commitment := commitment;
               prepared_inputs := request_inputs request;
               prepared_backend := backend;
               prepared_epoch := factory_epoch implementation |}
        end
      end
    end.

  Fixpoint prepare_batch (factory : option Factory) (requests : list Request)
      : PreparationError + list Prepared :=
    match requests with
    | [] => inr []
    | request :: rest =>
      match prepare_one factory request with
      | inl error => inl error
      | inr prepared =>
        match prepare_batch factory rest with
        | inl error => inl error
        | inr suffix => inr (prepared :: suffix)
        end
      end
    end.

  Definition publish_batch (installed : list Prepared) (factory : option Factory)
      (requests : list Request) : list Prepared :=
    match prepare_batch factory requests with
    | inl _ => installed
    | inr prepared => installed ++ prepared
    end.

  Theorem missing_factory_is_explicit : forall inputs commitment,
    prepare_one None
      {| request_image := ImageAdmitted commitment; request_inputs := inputs |} =
    inl MissingRuntimeFactory.
  Proof. reflexivity. Qed.

  Theorem rejected_image_cannot_prepare_a_backend : forall factory inputs,
    prepare_one factory
      {| request_image := ImageRejected; request_inputs := inputs |} =
    inl RejectedImage.
  Proof. reflexivity. Qed.

  Theorem prepared_backend_retains_exact_request : forall factory request prepared,
    prepare_one factory request = inr prepared ->
    request_image request = ImageAdmitted (prepared_commitment prepared) /\
    prepared_inputs prepared = request_inputs request.
  Proof.
    intros factory [admission inputs] prepared H.
    destruct admission as [commitment|]; [|discriminate].
    destruct factory as [[epoch worker]|]; [|discriminate].
    cbn in H. destruct (worker inputs) as [backend|]; [|discriminate].
    inversion H; subst. split; reflexivity.
  Qed.

  Theorem prepared_backend_retains_factory_epoch : forall factory request prepared,
    prepare_one (Some factory) request = inr prepared ->
    prepared_epoch prepared = factory_epoch factory.
  Proof.
    intros [epoch worker] [admission inputs] prepared H.
    destruct admission as [commitment|]; [|discriminate].
    cbn in H. destruct (worker inputs) as [backend|]; [|discriminate].
    inversion H; reflexivity.
  Qed.

  (** The new successful batch projects into the existing image-admission
      batch without changing its commitment roster or order. *)
  Theorem successful_backend_batch_refines_image_batch : forall factory requests prepared,
    prepare_batch factory requests = inr prepared ->
    prepare_image_batch (map request_image requests) =
      Some (map prepared_commitment prepared).
  Proof.
    intros factory requests. induction requests as [|request rest IH];
      intros prepared H.
    - cbn in H. inversion H. reflexivity.
    - cbn in H.
      destruct (prepare_one factory request) as [error|head] eqn:Hhead;
        [discriminate|].
      destruct (prepare_batch factory rest) as [error|tail] eqn:Htail;
        [discriminate|].
      inversion H; subst prepared.
      destruct (prepared_backend_retains_exact_request factory request head Hhead)
        as [Himage _].
      cbn. rewrite Himage. cbn. rewrite (IH tail eq_refl). reflexivity.
  Qed.

  Theorem preparation_failure_publishes_no_prefix : forall installed factory requests error,
    prepare_batch factory requests = inl error ->
    publish_batch installed factory requests = installed.
  Proof. intros installed factory requests error H. unfold publish_batch. now rewrite H. Qed.

  Theorem successful_preparation_publishes_exact_complete_suffix :
    forall installed factory requests prepared,
    prepare_batch factory requests = inr prepared ->
    publish_batch installed factory requests = installed ++ prepared.
  Proof. intros installed factory requests prepared H. unfold publish_batch. now rewrite H. Qed.

  Section Invocation.
    Context {Session Category Policy Outcome : Type}.
    Variable run_backend : Backend -> Session -> Category -> Policy -> Outcome.

    (** A borrowed session already contains the private, capability-bound
        RuntimeParser reference. No source/template distinction or decoding
        algorithm is reconstructed at this interface. *)
    Definition invoke (prepared : Prepared) (session : Session)
        (category : Category) (policy : Policy) : Outcome :=
      run_backend (prepared_backend prepared) session category policy.

    Theorem invocation_uses_prepared_backend_and_unchanged_session :
      forall prepared session category policy,
      invoke prepared session category policy =
      run_backend (prepared_backend prepared) session category policy.
    Proof. reflexivity. Qed.
  End Invocation.
End FactoryPreparation.

(** Runtime engine injection does not replace sealed-epoch revalidation. *)
Definition publication_authorized := revalidated_operation.

Theorem revoked_backend_completion_cannot_publish : forall entry handle rights,
  ~ publication_authorized entry (revoke entry) handle rights.
Proof. exact revoked_completion_fails_revalidation. Qed.

Section EngineCacheIdentity.
  Context {Language EngineEpoch Host Result : Type}.
  Variable parse_symbolic : (Language * EngineEpoch) -> Host -> list TemplatePiece -> Result.

  (** Pairing the implementation epoch with the existing language identity
      instantiates StructuralTemplate's cache theorem; no new cache algorithm.
      Rust additionally retains its existing policy/category/hole key fields. *)
  Theorem sound_backend_cache_hit_is_same_backend_parse :
    forall (entry : @SymbolicCacheEntry (Language * EngineEpoch) Host Result)
      language engine host template,
    cache_entry_sound parse_symbolic entry ->
    cache_hit entry (language, engine) host template ->
    cached_parse entry = parse_symbolic (language, engine) host template.
  Proof.
    intros entry language engine host template Hsound Hhit.
    eapply sound_cache_hit_is_uncached_parse; eassumption.
  Qed.

  Theorem different_backend_epoch_cannot_hit :
    forall (entry : @SymbolicCacheEntry (Language * EngineEpoch) Host Result)
      language engine host template,
    snd (cached_language_commitment entry) <> engine ->
    ~ cache_hit entry (language, engine) host template.
  Proof.
    intros entry language engine host template Hdifferent [Hsame _].
    apply Hdifferent. rewrite Hsame. reflexivity.
  Qed.
End EngineCacheIdentity.

Print Assumptions exact_payload_roundtrip.
Print Assumptions wpda_payload_roundtrip.
Print Assumptions wpda_transport_preserves_every_observation.
Print Assumptions wrapping_preserves_payload_and_production.
Print Assumptions wpda_has_no_fabricated_exact_payload.
Print Assumptions exact_has_no_fabricated_wpda_payload.
Print Assumptions wrapping_preserves_roster_length.
Print Assumptions wrapping_preserves_weight_roster_in_order.
Print Assumptions exact_comparison_is_original.
Print Assumptions wpda_comparison_is_original.
Print Assumptions mixed_comparisons_are_unavailable.
Print Assumptions missing_factory_is_explicit.
Print Assumptions rejected_image_cannot_prepare_a_backend.
Print Assumptions prepared_backend_retains_exact_request.
Print Assumptions prepared_backend_retains_factory_epoch.
Print Assumptions successful_backend_batch_refines_image_batch.
Print Assumptions preparation_failure_publishes_no_prefix.
Print Assumptions successful_preparation_publishes_exact_complete_suffix.
Print Assumptions invocation_uses_prepared_backend_and_unchanged_session.
Print Assumptions revoked_backend_completion_cannot_publish.
Print Assumptions sound_backend_cache_hit_is_same_backend_parse.
Print Assumptions different_backend_epoch_cannot_hit.
End InstalledRuntimeBackend.
