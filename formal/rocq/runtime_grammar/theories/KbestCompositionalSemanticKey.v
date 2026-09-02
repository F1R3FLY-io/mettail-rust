(** * Persistent compositional semantic keys for k-best realization

    A realized syntax node has a canonical exact byte stream.  Re-streaming
    every complete subtree for every k-best representative performs triangular
    work on a deep chain even when the parser forest and retained digest table
    are linear.  The repaired interface constructs a persistent key from the
    node's local bytes and already-constructed child keys.  Child keys are
    shared by immutable node identity and an explicit cache; flattening is
    reserved for exact comparison or external encoding.

    This model establishes the implementation obligations without assuming a
    collision-free finite digest:

    - persistent composition flattens to the original exact byte stream;
    - the length-and-fingerprint accelerator composes over concatenation;
    - accelerator equality never replaces exact byte equality;
    - cache insertion preserves the exact-key invariant;
    - bounded insertion reports exhaustion without publishing partial state;
    - a unary chain changes from triangular re-streaming work to linear local
      construction work and linear retained cache witnesses.

    Bytes, fingerprints, and immutable allocation identities are modeled by
    natural numbers.  The additive fingerprint deliberately admits collisions,
    so the exact-fallback theorems cover adversarial finite accelerators rather
    than relying on cryptographic assumptions. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Import ListNotations.

Module KbestCompositionalSemanticKey.

  Definition Byte := nat.
  Definition NodeId := nat.

  (** A tree node stores only its local byte segment and shared references to
      already-built child keys.  [flatten_key] is the authoritative exact
      observation. *)
  Inductive PersistentKey : Type :=
  | FlatKey : list Byte -> PersistentKey
  | ComposedKey : list Byte -> list PersistentKey -> PersistentKey.

  Fixpoint flatten_key (key : PersistentKey) : list Byte :=
    match key with
    | FlatKey bytes => bytes
    | ComposedKey local children =>
        local ++ concat (map flatten_key children)
    end.

  Definition compose_key
      (local : list Byte) (children : list PersistentKey) : PersistentKey :=
    ComposedKey local children.

  Theorem compose_key_exact : forall local children,
      flatten_key (compose_key local children) =
      local ++ concat (map flatten_key children).
  Proof. reflexivity. Qed.

  (** The concrete implementation uses a fixed-width rolling fingerprint and
      exact length.  Addition is used here as a small compositional stand-in:
      it has the same required monoid law and intentionally has many
      collisions. *)
  Definition byte_fingerprint (bytes : list Byte) : nat :=
    fold_right Nat.add 0 bytes.

  Definition Accelerator := (nat * nat)%type.

  Definition accelerator (bytes : list Byte) : Accelerator :=
    (length bytes, byte_fingerprint bytes).

  Definition combine_accelerator
      (left right : Accelerator) : Accelerator :=
    (fst left + fst right, snd left + snd right).

  Lemma byte_fingerprint_app : forall left right,
      byte_fingerprint (left ++ right) =
      byte_fingerprint left + byte_fingerprint right.
  Proof.
    induction left as [|byte left IH]; intros right; simpl.
    - reflexivity.
    - rewrite IH. lia.
  Qed.

  Theorem accelerator_composes : forall left right,
      accelerator (left ++ right) =
      combine_accelerator (accelerator left) (accelerator right).
  Proof.
    intros left right. unfold accelerator, combine_accelerator.
    rewrite length_app, byte_fingerprint_app. reflexivity.
  Qed.

  Definition collision_safe_equal (left right : list Byte) : Prop :=
    accelerator left = accelerator right /\ left = right.

  Theorem collision_safe_equal_iff_exact : forall left right,
      collision_safe_equal left right <-> left = right.
  Proof.
    intros left right. split.
    - intros [_ Hexact]. exact Hexact.
    - intro Hexact. subst right. split; reflexivity.
  Qed.

  Theorem accelerator_collision_cannot_merge : forall left right,
      accelerator left = accelerator right ->
      left <> right ->
      ~ collision_safe_equal left right.
  Proof.
    intros left right _ Hdistinct [_ Hexact]. contradiction.
  Qed.

  Definition Cache := list (NodeId * PersistentKey).

  Fixpoint cache_lookup (node : NodeId) (cache : Cache)
      : option PersistentKey :=
    match cache with
    | [] => None
    | (candidate, key) :: rest =>
        if Nat.eqb node candidate then Some key else cache_lookup node rest
    end.

  Definition CacheSound
      (exact_stream : NodeId -> list Byte) (cache : Cache) : Prop :=
    forall node key,
      cache_lookup node cache = Some key ->
      flatten_key key = exact_stream node.

  Theorem empty_cache_sound : forall exact_stream,
      CacheSound exact_stream [].
  Proof.
    intros exact_stream node key Hlookup. discriminate.
  Qed.

  Theorem inserted_key_is_found : forall node key cache,
      cache_lookup node ((node, key) :: cache) = Some key.
  Proof.
    intros node key cache. simpl. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem sound_cache_insert : forall exact_stream cache node key,
      CacheSound exact_stream cache ->
      flatten_key key = exact_stream node ->
      CacheSound exact_stream ((node, key) :: cache).
  Proof.
    intros exact_stream cache node key Hsound Hkey queried found Hlookup.
    simpl in Hlookup. destruct (Nat.eqb queried node) eqn:Hequal.
    - apply Nat.eqb_eq in Hequal. subst queried.
      inversion Hlookup. subst found. exact Hkey.
    - apply Hsound with (node := queried). exact Hlookup.
  Qed.

  Theorem cache_hit_returns_exact_stream : forall exact_stream cache node key,
      CacheSound exact_stream cache ->
      cache_lookup node cache = Some key ->
      flatten_key key = exact_stream node.
  Proof.
    intros exact_stream cache node key Hsound Hlookup.
    apply Hsound with (node := node). exact Hlookup.
  Qed.

  Inductive CacheInsertResult : Type :=
  | CacheStored : Cache -> CacheInsertResult
  | CacheResourceExhausted : Cache -> CacheInsertResult.

  Definition bounded_cache_insert
      (capacity : nat) (node : NodeId) (key : PersistentKey) (cache : Cache)
      : CacheInsertResult :=
    if length cache <? capacity
    then CacheStored ((node, key) :: cache)
    else CacheResourceExhausted cache.

  Theorem bounded_cache_store_respects_capacity :
      forall capacity node key cache stored,
        length cache <= capacity ->
        bounded_cache_insert capacity node key cache = CacheStored stored ->
        length stored <= capacity.
  Proof.
    intros capacity node key cache stored Hbound Hstored.
    unfold bounded_cache_insert in Hstored.
    destruct (length cache <? capacity) eqn:Hroom.
    - inversion Hstored. subst stored. simpl.
      apply Nat.ltb_lt in Hroom. lia.
    - discriminate.
  Qed.

  Theorem bounded_cache_exhaustion_is_atomic :
      forall capacity node key cache exhausted,
        bounded_cache_insert capacity node key cache =
          CacheResourceExhausted exhausted ->
        exhausted = cache /\ capacity <= length cache.
  Proof.
    intros capacity node key cache exhausted Hexhausted.
    unfold bounded_cache_insert in Hexhausted.
    destruct (length cache <? capacity) eqn:Hroom.
    - discriminate.
    - inversion Hexhausted. subst exhausted. split; [reflexivity |].
      apply Nat.ltb_ge. exact Hroom.
  Qed.

  (** Realization may construct candidate terms before the semantic-key cache
      transaction is committed.  The public boundary is therefore a sum:
      candidates are observable only after a successful commit; exhaustion
      exposes an error and no prefix of the candidate list. *)
  Inductive PublicRealization (Term : Type) : Type :=
  | RealizationSucceeded : list Term -> PublicRealization Term
  | RealizationResourceExhausted : PublicRealization Term.

  Arguments RealizationSucceeded {Term}.
  Arguments RealizationResourceExhausted {Term}.

  Definition finalize_realization {Term : Type}
      (candidates : list Term) (cache_result : CacheInsertResult)
      : PublicRealization Term :=
    match cache_result with
    | CacheStored _ => RealizationSucceeded candidates
    | CacheResourceExhausted _ => RealizationResourceExhausted
    end.

  Definition exposed_terms {Term : Type}
      (result : PublicRealization Term) : list Term :=
    match result with
    | RealizationSucceeded terms => terms
    | RealizationResourceExhausted => []
    end.

  Theorem successful_commit_publishes_all_candidates :
      forall (Term : Type) (candidates : list Term) stored,
        finalize_realization candidates (CacheStored stored) =
          RealizationSucceeded candidates.
  Proof. reflexivity. Qed.

  Theorem exhausted_commit_publishes_no_partial_result :
      forall (Term : Type) (candidates : list Term) retained,
        exposed_terms
          (finalize_realization candidates (CacheResourceExhausted retained)) =
        [].
  Proof. reflexivity. Qed.

  Theorem bounded_exhaustion_preserves_cache_and_hides_candidates :
      forall (Term : Type) capacity node key cache retained
             (candidates : list Term),
        bounded_cache_insert capacity node key cache =
          CacheResourceExhausted retained ->
        retained = cache /\
        exposed_terms
          (finalize_realization candidates (CacheResourceExhausted retained)) =
          [].
  Proof.
    intros Term capacity node key cache retained candidates Hexhausted.
    split.
    - apply (proj1 (bounded_cache_exhaustion_is_atomic
        capacity node key cache retained Hexhausted)).
    - reflexivity.
  Qed.

  (** A cache failure is also a control-state boundary.  In particular, the
      implementation must not fall back to the legacy full-subtree streamer
      after the bounded compositional cache has refused a transaction: doing so
      would reintroduce the triangular work that the bound is meant to avoid. *)
  Inductive DedupControl : Type :=
  | ContinueDedup
  | StopRealization.

  Definition control_after_cache (result : CacheInsertResult) : DedupControl :=
    match result with
    | CacheStored _ => ContinueDedup
    | CacheResourceExhausted _ => StopRealization
    end.

  Definition legacy_fallback_allowed (control : DedupControl) : bool :=
    match control with
    | ContinueDedup => true
    | StopRealization => false
    end.

  Theorem cache_exhaustion_stops_before_legacy_fallback :
      forall retained,
        legacy_fallback_allowed
          (control_after_cache (CacheResourceExhausted retained)) = false.
  Proof. reflexivity. Qed.

  Theorem stopped_realization_is_absorbing :
      forall next,
        match StopRealization with
        | ContinueDedup => next
        | StopRealization => StopRealization
        end = StopRealization.
  Proof. reflexivity. Qed.

  (** Exact keys are also bounded by their logical byte length.  This is a
      distinct resource from the number of cached node witnesses: one leaf may
      contain a large token, and persistent sharing can describe a logical byte
      stream larger than the physical rope.  Construction checks the complete
      logical length before the key becomes observable. *)
  Definition exact_key_bytes (key : PersistentKey) : nat :=
    length (flatten_key key).

  Inductive KeyBuildResult : Type :=
  | KeyBuilt : PersistentKey -> KeyBuildResult
  | KeyBytesExhausted : nat -> KeyBuildResult.

  Definition bounded_compose_key
      (max_bytes : nat) (local : list Byte) (children : list PersistentKey)
      : KeyBuildResult :=
    let key := compose_key local children in
    let requested := exact_key_bytes key in
    if requested <=? max_bytes
    then KeyBuilt key
    else KeyBytesExhausted requested.

  Theorem bounded_key_success_is_exact_and_within_limit :
      forall max_bytes local children key,
        bounded_compose_key max_bytes local children = KeyBuilt key ->
        key = compose_key local children /\
        flatten_key key = local ++ concat (map flatten_key children) /\
        exact_key_bytes key <= max_bytes.
  Proof.
    intros max_bytes local children key Hbuilt.
    unfold bounded_compose_key in Hbuilt.
    destruct (exact_key_bytes (compose_key local children) <=? max_bytes)
      eqn:Hwithin.
    - inversion Hbuilt. subst key. split.
      + reflexivity.
      + split.
        * apply compose_key_exact.
        * apply Nat.leb_le. exact Hwithin.
    - discriminate.
  Qed.

  Theorem bounded_key_exhaustion_reports_exact_request :
      forall max_bytes local children requested,
        bounded_compose_key max_bytes local children =
          KeyBytesExhausted requested ->
        requested = exact_key_bytes (compose_key local children) /\
        max_bytes < requested.
  Proof.
    intros max_bytes local children requested Hexhausted.
    unfold bounded_compose_key in Hexhausted.
    destruct (exact_key_bytes (compose_key local children) <=? max_bytes)
      eqn:Hwithin.
    - discriminate.
    - inversion Hexhausted. subst requested. split.
      + reflexivity.
      + apply Nat.leb_gt. exact Hwithin.
  Qed.

  Definition key_build_exposes_bytes (result : KeyBuildResult) : list Byte :=
    match result with
    | KeyBuilt key => flatten_key key
    | KeyBytesExhausted _ => []
    end.

  Theorem byte_exhaustion_exposes_no_partial_key : forall requested,
      key_build_exposes_bytes (KeyBytesExhausted requested) = [].
  Proof. reflexivity. Qed.

  (** Re-streaming all exact prefixes of a depth-[n] unary chain performs
      [1 + ... + n] byte visits. *)
  Fixpoint chain_restream_work (depth : nat) : nat :=
    match depth with
    | 0 => 0
    | S predecessor => S predecessor + chain_restream_work predecessor
    end.

  (** Compositional construction writes one local segment and one child
      reference per nonempty chain node. *)
  Fixpoint chain_compositional_work (depth : nat) : nat :=
    match depth with
    | 0 => 0
    | S predecessor => 2 + chain_compositional_work predecessor
    end.

  Theorem chain_restream_work_is_triangular : forall depth,
      2 * chain_restream_work depth = depth * (depth + 1).
  Proof.
    induction depth as [|depth IH].
    - reflexivity.
    - change
        (2 * (S depth + chain_restream_work depth) =
         S depth * (S depth + 1)).
      rewrite Nat.mul_add_distr_l, IH. nia.
  Qed.

  Theorem chain_compositional_work_is_linear : forall depth,
      chain_compositional_work depth = 2 * depth.
  Proof.
    induction depth as [|depth IH].
    - reflexivity.
    - simpl. rewrite IH. lia.
  Qed.

  Definition retained_cache_witness_bytes
      (local_width reference_width depth : nat) : nat :=
    depth * (local_width + reference_width).

  Theorem retained_cache_witnesses_are_linear :
      forall local_width reference_width depth,
        retained_cache_witness_bytes local_width reference_width depth =
        depth * (local_width + reference_width).
  Proof. reflexivity. Qed.

  Print Assumptions compose_key_exact.
  Print Assumptions accelerator_composes.
  Print Assumptions collision_safe_equal_iff_exact.
  Print Assumptions accelerator_collision_cannot_merge.
  Print Assumptions empty_cache_sound.
  Print Assumptions inserted_key_is_found.
  Print Assumptions sound_cache_insert.
  Print Assumptions cache_hit_returns_exact_stream.
  Print Assumptions bounded_cache_store_respects_capacity.
  Print Assumptions bounded_cache_exhaustion_is_atomic.
  Print Assumptions successful_commit_publishes_all_candidates.
  Print Assumptions exhausted_commit_publishes_no_partial_result.
  Print Assumptions bounded_exhaustion_preserves_cache_and_hides_candidates.
  Print Assumptions cache_exhaustion_stops_before_legacy_fallback.
  Print Assumptions stopped_realization_is_absorbing.
  Print Assumptions bounded_key_success_is_exact_and_within_limit.
  Print Assumptions bounded_key_exhaustion_reports_exact_request.
  Print Assumptions byte_exhaustion_exposes_no_partial_key.
  Print Assumptions chain_restream_work_is_triangular.
  Print Assumptions chain_compositional_work_is_linear.
  Print Assumptions retained_cache_witnesses_are_linear.

End KbestCompositionalSemanticKey.
