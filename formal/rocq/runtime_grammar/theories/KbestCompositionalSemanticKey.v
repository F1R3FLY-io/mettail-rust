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
    - bounded LRU retention preserves results at every capacity;
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

  Record MemoEntry := {
    memo_node : NodeId;
    memo_owner : nat;
    memo_key : PersistentKey
  }.

  Definition MemoCache := list MemoEntry.
  Definition MemoSound (live : nat -> bool) (exact : NodeId -> list Byte)
      (cache : MemoCache) :=
    forall entry, In entry cache -> live (memo_owner entry) = true ->
      flatten_key (memo_key entry) = exact (memo_node entry).

  Definition remove_node node cache :=
    filter (fun entry => negb (Nat.eqb node (memo_node entry))) cache.

  Definition admit capacity entry cache :=
    firstn capacity (entry :: remove_node (memo_node entry) cache).

  Definition lookup_memo (live : nat -> bool) (node : NodeId) (cache : MemoCache) :=
    match find (fun entry => Nat.eqb node (memo_node entry)) cache with
    | None => (None, cache)
    | Some entry =>
        if live (memo_owner entry)
        then (Some (memo_key entry), entry :: remove_node node cache)
        else (None, remove_node node cache)
    end.

  Definition memoized_key live compute node cache :=
    match fst (lookup_memo live node cache) with
    | Some key => key
    | None => compute node
    end.

  Theorem eviction_preserves_soundness : forall live exact cache retained,
      MemoSound live exact cache ->
      (forall entry, In entry retained -> In entry cache) ->
      MemoSound live exact retained.
  Proof. unfold MemoSound; intros; eauto. Qed.

  Lemma removed_entry_was_present : forall node cache entry,
      In entry (remove_node node cache) -> In entry cache.
  Proof.
    intros; unfold remove_node in H; apply filter_In in H; tauto.
  Qed.

  Theorem admission_preserves_soundness : forall live exact capacity entry cache,
      MemoSound live exact cache ->
      flatten_key (memo_key entry) = exact (memo_node entry) ->
      MemoSound live exact (admit capacity entry cache).
  Proof.
    intros live exact capacity entry cache Hsound Hexact other Hin Hlive.
    unfold admit in Hin.
    assert (In other (entry :: remove_node (memo_node entry) cache)) as Hretained.
    { rewrite <- (firstn_skipn capacity (entry :: remove_node (memo_node entry) cache)).
      apply in_or_app. left. exact Hin. }
    destruct Hretained as [Hequal | HinRest].
    - subst other. exact Hexact.
    - apply Hsound; [eapply removed_entry_was_present; exact HinRest | exact Hlive].
  Qed.

  Theorem admission_bounds_all_entries : forall capacity entry cache,
      length (admit capacity entry cache) <= capacity.
  Proof. intros; unfold admit; rewrite firstn_length; apply Nat.le_min_l. Qed.

  Theorem zero_capacity_retains_nothing : forall entry cache,
      admit 0 entry cache = [].
  Proof. reflexivity. Qed.

  Theorem admission_does_not_inspect_liveness : forall capacity entry cache,
      admit capacity entry cache =
      firstn capacity (entry :: remove_node (memo_node entry) cache).
  Proof. reflexivity. Qed.

  Lemma remove_node_shortens : forall cache entry,
      In entry cache ->
      length (remove_node (memo_node entry) cache) < length cache.
  Proof.
    induction cache as [|head tail IH]; intros entry Hin; [contradiction |].
    simpl in Hin. unfold remove_node; simpl.
    destruct (Nat.eqb (memo_node entry) (memo_node head)) eqn:Hequal; simpl.
    - pose proof (filter_length_le (fun item => negb (Nat.eqb (memo_node entry) (memo_node item))) tail). lia.
    - destruct Hin as [Hin | Hin].
      + subst head. rewrite Nat.eqb_refl in Hequal. discriminate.
      + specialize (IH entry Hin). unfold remove_node in IH. lia.
  Qed.

  Theorem lookup_preserves_entry_bound : forall live node cache,
      length (snd (lookup_memo live node cache)) <= length cache.
  Proof.
    intros live node cache. unfold lookup_memo.
    destruct (find (fun entry => Nat.eqb node (memo_node entry)) cache) as [entry|] eqn:Hfind.
    - apply find_some in Hfind. destruct Hfind as [Hin Hid].
      apply Nat.eqb_eq in Hid. subst node.
      destruct (live (memo_owner entry)); simpl.
      + pose proof (remove_node_shortens cache entry Hin). lia.
      + unfold remove_node. apply filter_length_le.
    - simpl. lia.
  Qed.

  Theorem lookup_preserves_soundness : forall live exact node cache,
      MemoSound live exact cache ->
      MemoSound live exact (snd (lookup_memo live node cache)).
  Proof.
    intros live exact node cache Hsound. unfold lookup_memo.
    destruct (find (fun entry => Nat.eqb node (memo_node entry)) cache) as [entry|] eqn:Hfind.
    - apply find_some in Hfind. destruct Hfind as [Hin _].
      destruct (live (memo_owner entry)); simpl;
        apply (eviction_preserves_soundness live exact cache); try exact Hsound;
        intros other Hother.
      + destruct Hother as [Hother | Hother]; [subst; exact Hin |].
        eapply removed_entry_was_present; eauto.
      + eapply removed_entry_was_present; eauto.
    - exact Hsound.
  Qed.

  Theorem valid_hit_returns_exact_stream : forall live exact node cache key,
      MemoSound live exact cache ->
      fst (lookup_memo live node cache) = Some key ->
      flatten_key key = exact node.
  Proof.
    intros live exact node cache key Hsound Hhit. unfold lookup_memo in Hhit.
    destruct (find (fun entry => Nat.eqb node (memo_node entry)) cache) as [entry|] eqn:Hfind;
      [|discriminate].
    destruct (live (memo_owner entry)) eqn:Hlive; [|discriminate].
    simpl in Hhit. inversion Hhit; subst key.
    apply find_some in Hfind. destruct Hfind as [Hin Hid].
    apply Nat.eqb_eq in Hid. subst node. eapply Hsound; eauto.
  Qed.

  Theorem expired_owner_is_a_miss : forall live node cache entry,
      find (fun candidate => Nat.eqb node (memo_node candidate)) cache = Some entry ->
      live (memo_owner entry) = false ->
      lookup_memo live node cache = (None, remove_node node cache).
  Proof. intros; unfold lookup_memo; now rewrite H, H0. Qed.

  Theorem valid_hit_promotes_to_most_recent : forall live node cache entry,
      find (fun candidate => Nat.eqb node (memo_node candidate)) cache = Some entry ->
      live (memo_owner entry) = true ->
      snd (lookup_memo live node cache) = entry :: remove_node node cache.
  Proof. intros; unfold lookup_memo; now rewrite H, H0. Qed.

  Theorem cache_capacity_cannot_change_key : forall live exact compute node cache,
      MemoSound live exact cache ->
      (forall queried, flatten_key (compute queried) = exact queried) ->
      flatten_key (memoized_key live compute node cache) = exact node.
  Proof.
    intros live exact compute node cache Hsound Hcompute. unfold memoized_key.
    destruct (fst (lookup_memo live node cache)) as [key|] eqn:Hhit.
    - eapply valid_hit_returns_exact_stream; eauto.
    - apply Hcompute.
  Qed.

  Theorem arbitrary_eviction_preserves_observations :
      forall live exact compute nodes left right,
      MemoSound live exact left -> MemoSound live exact right ->
      (forall node, flatten_key (compute node) = exact node) ->
      map (fun node => flatten_key (memoized_key live compute node left)) nodes =
      map (fun node => flatten_key (memoized_key live compute node right)) nodes.
  Proof.
    intros live exact compute nodes left right Hleft Hright Hcompute.
    apply map_ext. intro node.
    rewrite (cache_capacity_cannot_change_key live exact compute node left Hleft Hcompute).
    rewrite (cache_capacity_cannot_change_key live exact compute node right Hright Hcompute).
    reflexivity.
  Qed.

  Definition pending_in cache pending :=
    filter (fun node => existsb (Nat.eqb node) pending) (map memo_node cache).

  Definition abort_memo cache pending :=
    filter (fun entry => negb (existsb (Nat.eqb (memo_node entry)) pending)) cache.

  Theorem provisional_metadata_is_bounded : forall cache pending,
      length (pending_in cache pending) <= length cache.
  Proof.
    intros. unfold pending_in.
    pose proof (filter_length_le (fun node => existsb (Nat.eqb node) pending) (map memo_node cache)).
    rewrite length_map in H. exact H.
  Qed.

  Theorem abort_removes_every_provisional_entry : forall cache pending entry,
      In entry (abort_memo cache pending) -> ~ In (memo_node entry) pending.
  Proof.
    intros cache pending entry Hin Hpending.
    unfold abort_memo in Hin. apply filter_In in Hin. destruct Hin as [_ Hnot].
    apply negb_true_iff in Hnot.
    assert (existsb (Nat.eqb (memo_node entry)) pending = true) as Hyes.
    { apply existsb_exists. exists (memo_node entry). split; [exact Hpending | apply Nat.eqb_refl]. }
    congruence.
  Qed.

  Theorem abort_preserves_soundness : forall live exact cache pending,
      MemoSound live exact cache -> MemoSound live exact (abort_memo cache pending).
  Proof.
    intros. apply (eviction_preserves_soundness live exact cache); [exact H |].
    intros entry Hin. unfold abort_memo in Hin. apply filter_In in Hin. tauto.
  Qed.

  Definition commit_memo (cache : MemoCache) (_pending : list NodeId) := (cache, @nil NodeId).

  Theorem commit_keeps_entries_and_clears_markers : forall cache pending,
      commit_memo cache pending = (cache, []).
  Proof. reflexivity. Qed.

  Inductive PublicRealization (Term : Type) : Type :=
  | RealizationSucceeded : list Term -> PublicRealization Term
  | RealizationConstructionFailed : PublicRealization Term.

  Arguments RealizationSucceeded {Term}.
  Arguments RealizationConstructionFailed {Term}.

  Definition finalize_realization {Term : Type}
      (candidates : list Term) (constructed : bool) : PublicRealization Term :=
    if constructed then RealizationSucceeded candidates else RealizationConstructionFailed.

  Definition exposed_terms {Term : Type} (result : PublicRealization Term) :=
    match result with
    | RealizationSucceeded terms => terms
    | RealizationConstructionFailed => []
    end.

  Theorem construction_success_publishes_all_candidates :
      forall (Term : Type) (candidates : list Term),
      exposed_terms (finalize_realization candidates true) = candidates.
  Proof. reflexivity. Qed.

  Theorem construction_failure_publishes_no_candidates :
      forall (Term : Type) (candidates : list Term),
      exposed_terms (finalize_realization candidates false) = [].
  Proof. reflexivity. Qed.

  Print Assumptions eviction_preserves_soundness.
  Print Assumptions admission_preserves_soundness.
  Print Assumptions admission_bounds_all_entries.
  Print Assumptions zero_capacity_retains_nothing.
  Print Assumptions admission_does_not_inspect_liveness.
  Print Assumptions lookup_preserves_entry_bound.
  Print Assumptions lookup_preserves_soundness.
  Print Assumptions valid_hit_returns_exact_stream.
  Print Assumptions expired_owner_is_a_miss.
  Print Assumptions valid_hit_promotes_to_most_recent.
  Print Assumptions cache_capacity_cannot_change_key.
  Print Assumptions arbitrary_eviction_preserves_observations.
  Print Assumptions provisional_metadata_is_bounded.
  Print Assumptions abort_removes_every_provisional_entry.
  Print Assumptions abort_preserves_soundness.
  Print Assumptions commit_keeps_entries_and_clears_markers.
  Print Assumptions construction_success_publishes_all_candidates.
  Print Assumptions construction_failure_publishes_no_candidates.


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
  Print Assumptions bounded_key_success_is_exact_and_within_limit.
  Print Assumptions bounded_key_exhaustion_reports_exact_request.
  Print Assumptions byte_exhaustion_exposes_no_partial_key.
  Print Assumptions chain_restream_work_is_triangular.
  Print Assumptions chain_compositional_work_is_linear.
  Print Assumptions retained_cache_witnesses_are_linear.

End KbestCompositionalSemanticKey.
