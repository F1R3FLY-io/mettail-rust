(** * Representation-independent canonical semantic arenas

    A semantic forest may arrive in many flat-arena layouts: independent
    siblings may be allocated in either order, equal subterms may be shared or
    duplicated, and unordered collections may be permuted.  None of those
    implementation choices may affect a consensus fingerprint.

    The production algorithm computes node heights, replaces every child by
    its already-canonical lower-height identifier, and encodes the resulting
    local descriptor with an exact collision-free structural code.  Each
    height bucket is then sorted and deduplicated.  Concatenating buckets gives
    a deterministic post-order arena because every child has smaller height.

    In this model a natural number represents that exact structural code.  A
    digest may accelerate comparisons, but equality always checks the exact
    code.  The proofs cover collision safety, representation independence,
    idempotence, Bag multiplicity, Set uniqueness, Map/PathMap key uniqueness,
    backward references, and preservation of ordered root multiplicity. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia Sorting.Permutation.
From Dovetail.ExactKeys Require Import ExactKeyDedup.
Import ListNotations.
Set Implicit Arguments.

Module CanonicalSemanticArena.

  Section BooleanInsertionSort.
    Variable A : Type.
    Variable leb : A -> A -> bool.
    Hypothesis leb_total : forall left right,
        leb left right = true \/ leb right left = true.
    Hypothesis leb_trans : forall left middle right,
        leb left middle = true ->
        leb middle right = true ->
        leb left right = true.

    Lemma leb_refl : forall value, leb value value = true.
    Proof.
      intro value. destruct (leb_total value value); assumption.
    Qed.

    Inductive SSorted : list A -> Prop :=
    | SSortedNil : SSorted []
    | SSortedCons : forall head tail,
        Forall (fun value => leb head value = true) tail ->
        SSorted tail ->
        SSorted (head :: tail).

    Fixpoint insert (value : A) (values : list A) : list A :=
      match values with
      | [] => [value]
      | head :: tail =>
          if leb value head
          then value :: head :: tail
          else head :: insert value tail
      end.

    Definition sort (values : list A) : list A :=
      fold_right insert [] values.

    Lemma insert_permutation : forall value values,
        Permutation (value :: values) (insert value values).
    Proof.
      intros value values. induction values as [|head tail IH]; cbn.
      - reflexivity.
      - destruct (leb value head) eqn:Horder.
        + reflexivity.
        + eapply Permutation_trans.
          * apply perm_swap.
          * apply perm_skip. exact IH.
    Qed.

    Lemma sort_permutation : forall values,
        Permutation values (sort values).
    Proof.
      intro values. induction values as [|head tail IH]; cbn.
      - reflexivity.
      - eapply Permutation_trans.
        + apply perm_skip. exact IH.
        + apply insert_permutation.
    Qed.

    Lemma insert_forall : forall (predicate : A -> Prop) value values,
        predicate value ->
        Forall predicate values ->
        Forall predicate (insert value values).
    Proof.
      intros predicate value values Hvalue Hvalues.
      induction Hvalues as [|head tail Hhead Htail IH]; cbn.
      - constructor; [exact Hvalue | constructor].
      - destruct (leb value head).
        + constructor; [exact Hvalue | constructor; assumption].
        + constructor; [exact Hhead | exact IH].
    Qed.

    Lemma insert_sorted : forall value values,
        SSorted values -> SSorted (insert value values).
    Proof.
      intros value values Hsorted.
      induction Hsorted as [|head tail Hhead Htail IH]; cbn.
      - constructor; constructor.
      - destruct (leb value head) eqn:Horder.
        + constructor.
          * constructor; [exact Horder |].
            eapply Forall_impl; [|exact Hhead].
            cbn. intros candidate Hhead_candidate.
            eapply leb_trans; eauto.
          * constructor; assumption.
        + assert (Hhead_value : leb head value = true).
          { destruct (leb_total value head) as [Hvalue_head | Hhead_value].
            - rewrite Hvalue_head in Horder. discriminate.
            - exact Hhead_value. }
          constructor.
          * apply insert_forall; [exact Hhead_value | exact Hhead].
          * exact IH.
    Qed.

    Theorem sort_sorted : forall values, SSorted (sort values).
    Proof.
      intro values. induction values as [|head tail IH]; cbn.
      - constructor.
      - apply insert_sorted. exact IH.
    Qed.
  End BooleanInsertionSort.

  Definition nat_sort := sort Nat.leb.

  Lemma nat_leb_total : forall left right,
      Nat.leb left right = true \/ Nat.leb right left = true.
  Proof.
    intros left right. destruct (Nat.le_ge_cases left right) as [H | H].
    - left. now apply Nat.leb_le.
    - right. now apply Nat.leb_le.
  Qed.

  Lemma nat_leb_trans : forall left middle right,
      Nat.leb left middle = true ->
      Nat.leb middle right = true ->
      Nat.leb left right = true.
  Proof.
    intros left middle right Hleft Hright.
    apply Nat.leb_le in Hleft. apply Nat.leb_le in Hright.
    apply Nat.leb_le. lia.
  Qed.

  Definition canonical_keys (values : list nat) : list nat :=
    exact_dedup (nat_sort values).

  Lemma nodup_preserves_nat_sorted : forall values,
      SSorted Nat.leb values ->
      SSorted Nat.leb (exact_dedup values).
  Proof.
    intros values Hsorted.
    unfold exact_dedup.
    induction Hsorted as [|head tail Hhead Htail IH]; cbn.
    - constructor.
    - destruct (in_dec Nat.eq_dec head tail) as [Hin | Hnotin].
      + exact IH.
      + constructor.
        * rewrite Forall_forall in *.
          intros candidate Hcandidate.
          apply Hhead.
          apply nodup_In in Hcandidate. exact Hcandidate.
        * exact IH.
  Qed.

  Lemma canonical_keys_sorted : forall values,
      SSorted Nat.leb (canonical_keys values).
  Proof.
    intro values. unfold canonical_keys.
    apply nodup_preserves_nat_sorted.
    apply sort_sorted; [apply nat_leb_total | apply nat_leb_trans].
  Qed.

  Lemma canonical_keys_nodup : forall values,
      NoDup (canonical_keys values).
  Proof.
    intro values. unfold canonical_keys. apply exact_dedup_nodup.
  Qed.

  Lemma canonical_keys_in : forall values key,
      In key (canonical_keys values) <-> In key values.
  Proof.
    intros values key. unfold canonical_keys.
    pose proof (sort_permutation Nat.leb values) as Hpermutation.
    split; intro Hin.
    - apply exact_dedup_sound in Hin.
      eapply Permutation_in; [apply Permutation_sym; exact Hpermutation | exact Hin].
    - apply exact_dedup_complete.
      eapply Permutation_in; [exact Hpermutation | exact Hin].
  Qed.

  Lemma sorted_head_minimum : forall head tail candidate,
      SSorted Nat.leb (head :: tail) ->
      In candidate (head :: tail) ->
      head <= candidate.
  Proof.
    intros head tail candidate Hsorted Hin.
    inversion Hsorted as [|? ? Hhead Htail]; subst.
    destruct Hin as [Hequal | Hin].
    - subst. lia.
    - rewrite Forall_forall in Hhead.
      apply Nat.leb_le. now apply Hhead.
  Qed.

  Lemma sorted_nodup_membership_unique : forall left right,
      SSorted Nat.leb left ->
      NoDup left ->
      SSorted Nat.leb right ->
      NoDup right ->
      (forall key, In key left <-> In key right) ->
      left = right.
  Proof.
    intro left. induction left as [|left_head left_tail IH];
      intros right Hleft_sorted Hleft_nodup Hright_sorted Hright_nodup Hsame.
    - destruct right as [|right_head right_tail]; [reflexivity |].
      specialize (Hsame right_head). cbn in Hsame. tauto.
    - destruct right as [|right_head right_tail].
      + specialize (Hsame left_head). cbn in Hsame. tauto.
      + assert (Hleft_right : left_head <= right_head).
        { apply sorted_head_minimum with (tail := left_tail).
          - exact Hleft_sorted.
          - apply Hsame. cbn. tauto. }
        assert (Hright_left : right_head <= left_head).
        { apply sorted_head_minimum with (tail := right_tail).
          - exact Hright_sorted.
          - apply Hsame. cbn. tauto. }
        assert (Hequal : left_head = right_head) by lia. subst right_head.
        f_equal.
        apply IH.
        * inversion Hleft_sorted; assumption.
        * inversion Hleft_nodup; assumption.
        * inversion Hright_sorted; assumption.
        * inversion Hright_nodup; assumption.
        * intro key. specialize (Hsame key).
          inversion Hleft_nodup as [|? ? Hleft_fresh ?]; subst.
          inversion Hright_nodup as [|? ? Hright_fresh ?]; subst.
          cbn in Hsame. split; intro Hin.
          -- destruct (proj1 Hsame (or_intror Hin)) as [Hequal | Htail].
             ++ subst key. contradiction.
             ++ exact Htail.
          -- destruct (proj2 Hsame (or_intror Hin)) as [Hequal | Htail].
             ++ subst key. contradiction.
             ++ exact Htail.
  Qed.

  Theorem canonical_keys_extensional : forall left right,
      (forall key, In key left <-> In key right) ->
      canonical_keys left = canonical_keys right.
  Proof.
    intros left right Hsame.
    apply sorted_nodup_membership_unique.
    - apply canonical_keys_sorted.
    - apply canonical_keys_nodup.
    - apply canonical_keys_sorted.
    - apply canonical_keys_nodup.
    - intro key. repeat rewrite canonical_keys_in. apply Hsame.
  Qed.

  Theorem canonical_keys_idempotent : forall values,
      canonical_keys (canonical_keys values) = canonical_keys values.
  Proof.
    intro values. apply canonical_keys_extensional.
    intro key. rewrite canonical_keys_in. reflexivity.
  Qed.

  Theorem canonical_keys_ignore_layout_and_sharing : forall left right,
      (forall key, In key left <-> In key right) ->
      canonical_keys left = canonical_keys right.
  Proof. exact canonical_keys_extensional. Qed.

  (** Bags retain multiplicity and differ from sets only by omitting [nodup]. *)
  Definition canonical_bag (entries : list nat) : list nat := nat_sort entries.
  Definition canonical_set (entries : list nat) : list nat := canonical_keys entries.

  Theorem canonical_bag_preserves_multiplicity : forall entries,
      Permutation entries (canonical_bag entries).
  Proof. intro entries. apply sort_permutation. Qed.

  Theorem canonical_set_has_unique_elements : forall entries,
      NoDup (canonical_set entries).
  Proof. exact canonical_keys_nodup. Qed.

  Theorem canonical_set_preserves_membership : forall entries element,
      In element (canonical_set entries) <-> In element entries.
  Proof. exact canonical_keys_in. Qed.

  Definition MapEntry : Type := (nat * nat)%type.
  Definition entry_leb (left right : MapEntry) : bool :=
    Nat.leb (fst left) (fst right).
  Definition canonical_map (entries : list MapEntry) : list MapEntry :=
    sort entry_leb entries.

  Lemma entry_leb_total : forall left right,
      entry_leb left right = true \/ entry_leb right left = true.
  Proof.
    intros [left_key left_value] [right_key right_value].
    unfold entry_leb. cbn. apply nat_leb_total.
  Qed.

  Lemma entry_leb_trans : forall left middle right,
      entry_leb left middle = true ->
      entry_leb middle right = true ->
      entry_leb left right = true.
  Proof.
    intros [left_key left_value] [middle_key middle_value]
      [right_key right_value].
    unfold entry_leb. cbn. apply nat_leb_trans.
  Qed.

  Theorem canonical_map_preserves_entries : forall entries,
      Permutation entries (canonical_map entries).
  Proof. intro entries. apply sort_permutation. Qed.

  Theorem canonical_map_is_key_sorted : forall entries,
      SSorted entry_leb (canonical_map entries).
  Proof.
    intro entries. apply sort_sorted; [apply entry_leb_total | apply entry_leb_trans].
  Qed.

  Theorem canonical_map_preserves_unique_keys : forall entries,
      NoDup (map fst entries) ->
      NoDup (map fst (canonical_map entries)).
  Proof.
    intros entries Hunique.
    apply Permutation_NoDup with (l := map fst entries).
    - apply Permutation_map. apply canonical_map_preserves_entries.
    - exact Hunique.
  Qed.

  (** Map and PathMap admission share this exact duplicate-key predicate. *)
  Definition map_keys_unique (entries : list MapEntry) : Prop :=
    NoDup (map fst entries).

  Theorem duplicate_map_keys_fail_admission : forall entries key left_value right_value,
      In (key, left_value) entries ->
      In (key, right_value) entries ->
      left_value <> right_value ->
      ~ map_keys_unique entries.
  Proof.
    intros entries key left_value right_value Hleft Hright Hdifferent Hunique.
    unfold map_keys_unique in Hunique.
    induction entries as [|[entry_key entry_value] tail IH]; cbn in *.
    - contradiction.
    - inversion Hunique as [|? ? Hfresh Htail_unique]; subst.
      destruct Hleft as [Hleft | Hleft]; destruct Hright as [Hright | Hright].
      + inversion Hleft; inversion Hright; subst. contradiction.
      + inversion Hleft; subst. apply Hfresh.
        apply in_map_iff. exists (key, right_value). split; [reflexivity | exact Hright].
      + inversion Hright; subst. apply Hfresh.
        apply in_map_iff. exists (key, left_value). split; [reflexivity | exact Hleft].
      + eapply IH; eauto.
  Qed.

  (** Digest equality is only a fast precondition.  Exact-code equality is
      always checked, so a digest collision cannot merge distinct terms. *)
  Section DigestAccelerator.
    Variable digest : nat -> nat.

    Definition accelerated_equal (left right : nat) : bool :=
      Nat.eqb (digest left) (digest right) && Nat.eqb left right.

    Theorem accelerated_equal_is_exact : forall left right,
        accelerated_equal left right = true <-> left = right.
    Proof.
      intros left right. unfold accelerated_equal.
      rewrite andb_true_iff. repeat rewrite Nat.eqb_eq.
      split.
      - intros [_ Hequal]. exact Hequal.
      - intro Hequal. subst. auto.
    Qed.

    Theorem digest_collision_cannot_merge_distinct_codes : forall left right,
        digest left = digest right ->
        left <> right ->
        accelerated_equal left right = false.
    Proof.
      intros left right Hdigest Hdistinct.
      unfold accelerated_equal. rewrite Hdigest, Nat.eqb_refl. cbn.
      apply Nat.eqb_neq. exact Hdistinct.
    Qed.
  End DigestAccelerator.

  (** Each list is one height bucket of exact local descriptors. *)
  Definition ArenaBuckets : Type := list (list nat).
  Definition canonical_buckets (buckets : ArenaBuckets) : ArenaBuckets :=
    map canonical_keys buckets.
  Definition canonical_arena (buckets : ArenaBuckets) : list nat :=
    concat (canonical_buckets buckets).

  Inductive SameBucketSemantics : ArenaBuckets -> ArenaBuckets -> Prop :=
  | SameBucketsNil : SameBucketSemantics [] []
  | SameBucketsCons : forall left right left_rest right_rest,
      (forall key, In key left <-> In key right) ->
      SameBucketSemantics left_rest right_rest ->
      SameBucketSemantics (left :: left_rest) (right :: right_rest).

  Theorem canonical_buckets_representation_independent : forall left right,
      SameBucketSemantics left right ->
      canonical_buckets left = canonical_buckets right.
  Proof.
    intros left right Hsame. induction Hsame; cbn.
    - reflexivity.
    - unfold canonical_buckets in IHHsame.
      rewrite (canonical_keys_extensional left right H). now rewrite IHHsame.
  Qed.

  Theorem canonical_arena_representation_independent : forall left right,
      SameBucketSemantics left right ->
      canonical_arena left = canonical_arena right.
  Proof.
    intros left right Hsame. unfold canonical_arena.
    now rewrite (canonical_buckets_representation_independent Hsame).
  Qed.

  Theorem canonical_buckets_idempotent : forall buckets,
      canonical_buckets (canonical_buckets buckets) = canonical_buckets buckets.
  Proof.
    intro buckets. unfold canonical_buckets.
    rewrite map_map. apply map_ext. intro bucket.
    apply canonical_keys_idempotent.
  Qed.

  (** Processing all lower-height buckets before a parent bucket makes every
      remapped child reference backward without recursive execution. *)
  Theorem height_bucket_allocation_makes_references_backward :
    forall child_id parent_id parent_bucket_start,
      child_id < parent_bucket_start ->
      parent_bucket_start <= parent_id ->
      child_id < parent_id.
  Proof. intros. lia. Qed.

  Fixpoint index_of (key : nat) (arena : list nat) : option nat :=
    match arena with
    | [] => None
    | head :: tail =>
        if Nat.eqb key head
        then Some 0
        else option_map S (index_of key tail)
    end.

  Definition canonical_root_indices
      (arena : list nat) (ordered_root_codes : list nat) : list (option nat) :=
    map (fun root => index_of root arena) ordered_root_codes.

  Theorem root_order_and_multiplicity_are_preserved : forall arena roots,
      length (canonical_root_indices arena roots) = length roots.
  Proof.
    intros arena roots. unfold canonical_root_indices. apply length_map.
  Qed.

  Theorem representation_independent_roots : forall left right roots,
      SameBucketSemantics left right ->
      canonical_root_indices (canonical_arena left) roots =
      canonical_root_indices (canonical_arena right) roots.
  Proof.
    intros left right roots Hsame.
    now rewrite (canonical_arena_representation_independent Hsame).
  Qed.

  Print Assumptions accelerated_equal_is_exact.
  Print Assumptions digest_collision_cannot_merge_distinct_codes.
  Print Assumptions canonical_bag_preserves_multiplicity.
  Print Assumptions canonical_set_has_unique_elements.
  Print Assumptions canonical_map_preserves_unique_keys.
  Print Assumptions canonical_arena_representation_independent.
  Print Assumptions canonical_buckets_idempotent.
  Print Assumptions height_bucket_allocation_makes_references_backward.
  Print Assumptions root_order_and_multiplicity_are_preserved.

End CanonicalSemanticArena.
