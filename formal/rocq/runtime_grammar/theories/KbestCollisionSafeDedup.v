(** * Collision-safe bounded deduplication for lazy k-best realization

    A k-best realization session keeps one representative for each exact
    semantic key observed at an SPPF node.  Retaining every complete key is
    sound, but it is not space safe for a deep chain: the keys encode all
    nested suffixes and therefore occupy triangular space.

    The production repair keeps only a fixed-width digest bucket and a
    representative index.  A bucket hit is never an equality decision.  The
    engine first tries a sound structural-equality certificate; success proves
    exact semantic-key equality without serializing either subtree.  A failed
    or unavailable structural comparison is inconclusive and therefore falls
    through to exact, stack-safe semantic-key comparison.  Consequently
    digest collisions and structurally distinct observationally equal terms
    cannot change the accepted equivalence classes.  This file proves
    equivalence with exact-key deduplication, deterministic bounded refusal,
    and the change from triangular retained key bytes to a linear witness
    bound.

    Natural numbers model exact keys, digests, byte counts, and indices.  The
    digest function is deliberately unconstrained, so every theorem includes
    the adversarial collision case. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Import ListNotations.

Module KbestCollisionSafeDedup.

  Definition ExactKey := nat.
  Definition Digest := nat.

  (** [accelerated_member digest key representatives] is the executable
      bucket protocol: the digest narrows the bucket, while exact equality is
      the final and only membership judgment. *)
  Definition accelerated_member
      (digest : ExactKey -> Digest)
      (key : ExactKey)
      (representatives : list ExactKey) : bool :=
    existsb
      (fun representative =>
         Nat.eqb (digest key) (digest representative) &&
         Nat.eqb key representative)
      representatives.

  Theorem accelerated_member_iff : forall digest key representatives,
      accelerated_member digest key representatives = true <->
      In key representatives.
  Proof.
    intros digest key representatives.
    unfold accelerated_member.
    rewrite existsb_exists.
    split.
    - intros [representative [Hin Hsame]].
      apply Bool.andb_true_iff in Hsame as [_ Hexact].
      apply Nat.eqb_eq in Hexact. subst representative. exact Hin.
    - intro Hin. exists key. split; [exact Hin |].
      rewrite !Nat.eqb_refl. reflexivity.
  Qed.

  Theorem digest_collision_cannot_conflate : forall digest left right,
      digest left = digest right ->
      left <> right ->
      accelerated_member digest right [left] = false.
  Proof.
    intros digest left right _ Hdistinct.
    apply Bool.not_true_is_false. intro Hmember.
    apply accelerated_member_iff in Hmember. cbn in Hmember.
    destruct Hmember as [Hequal | Hfalse].
    - apply Hdistinct. exact Hequal.
    - contradiction.
  Qed.

  (** Terms and exact semantic keys are intentionally separate in this model.
      Two structurally different terms may have the same exact key because
      transparent constructors or another declared observation can erase a
      structural distinction. *)
  Definition Term := nat.

  Definition exact_member_by_key
      (key_of : Term -> ExactKey)
      (candidate : Term)
      (representatives : list Term) : bool :=
    existsb
      (fun representative =>
         Nat.eqb (key_of candidate) (key_of representative))
      representatives.

  (** [structural_or_exact] short-circuits only on a positive structural
      certificate.  [false] does not assert semantic inequality: the exact
      key comparison remains authoritative. *)
  Definition structural_or_exact
      (key_of : Term -> ExactKey)
      (structural_equal : Term -> Term -> bool)
      (left right : Term) : bool :=
    if structural_equal left right
    then true
    else Nat.eqb (key_of left) (key_of right).

  Inductive ComparisonRoute : Type :=
  | StructuralShortcut
  | ExactFallback.

  Definition comparison_route
      (structural_equal : Term -> Term -> bool)
      (left right : Term) : ComparisonRoute :=
    if structural_equal left right
    then StructuralShortcut
    else ExactFallback.

  Theorem structural_true_selects_shortcut :
      forall structural_equal left right,
        structural_equal left right = true ->
        comparison_route structural_equal left right = StructuralShortcut.
  Proof.
    intros structural_equal left right Hstructural.
    unfold comparison_route. rewrite Hstructural. reflexivity.
  Qed.

  Theorem structural_false_selects_exact_fallback :
      forall structural_equal left right,
        structural_equal left right = false ->
        comparison_route structural_equal left right = ExactFallback.
  Proof.
    intros structural_equal left right Hstructural.
    unfold comparison_route. rewrite Hstructural. reflexivity.
  Qed.

  Theorem structural_or_exact_is_exact :
      forall key_of structural_equal,
        (forall left right,
            structural_equal left right = true ->
            key_of left = key_of right) ->
        forall left right,
          structural_or_exact key_of structural_equal left right =
          Nat.eqb (key_of left) (key_of right).
  Proof.
    intros key_of structural_equal Hsound left right.
    unfold structural_or_exact.
    destruct (structural_equal left right) eqn:Hstructural.
    - apply Hsound in Hstructural. rewrite Hstructural, Nat.eqb_refl.
      reflexivity.
    - reflexivity.
  Qed.

  Theorem structurally_distinct_observational_equal_falls_back :
      forall key_of structural_equal left right,
        structural_equal left right = false ->
        key_of left = key_of right ->
        comparison_route structural_equal left right = ExactFallback /\
        structural_or_exact key_of structural_equal left right = true.
  Proof.
    intros key_of structural_equal left right Hstructural Hkey.
    split.
    - apply structural_false_selects_exact_fallback. exact Hstructural.
    - unfold structural_or_exact. rewrite Hstructural, Hkey, Nat.eqb_refl.
      reflexivity.
  Qed.

  (** The complete accelerated protocol: the digest selects a bucket, then a
      positive structural certificate or exact key equality establishes
      membership.  The digest is unconstrained and may collide adversarially. *)
  Definition structural_accelerated_member
      (digest : ExactKey -> Digest)
      (key_of : Term -> ExactKey)
      (structural_equal : Term -> Term -> bool)
      (candidate : Term)
      (representatives : list Term) : bool :=
    existsb
      (fun representative =>
         Nat.eqb
           (digest (key_of candidate))
           (digest (key_of representative)) &&
         structural_or_exact
           key_of structural_equal candidate representative)
      representatives.

  Theorem structural_accelerated_member_iff_exact :
      forall digest key_of structural_equal,
        (forall left right,
            structural_equal left right = true ->
            key_of left = key_of right) ->
        forall candidate representatives,
          structural_accelerated_member
            digest key_of structural_equal candidate representatives = true <->
          exact_member_by_key key_of candidate representatives = true.
  Proof.
    intros digest key_of structural_equal Hsound candidate representatives.
    unfold structural_accelerated_member, exact_member_by_key.
    rewrite !existsb_exists. split.
    - intros [representative [Hin Hmember]].
      apply Bool.andb_true_iff in Hmember as [_ Hequal].
      exists representative. split; [exact Hin |].
      rewrite (structural_or_exact_is_exact key_of structural_equal Hsound)
        in Hequal.
      exact Hequal.
    - intros [representative [Hin Hexact]].
      exists representative. split; [exact Hin |].
      apply Bool.andb_true_iff. split.
      + apply Nat.eqb_eq in Hexact. rewrite Hexact, Nat.eqb_refl.
        reflexivity.
      + rewrite (structural_or_exact_is_exact key_of structural_equal Hsound).
        exact Hexact.
  Qed.

  (** Pointer identity is a sound structural shortcut because equal live
      allocation identities denote the same immutable term.  It is not used
      in the converse direction: different pointers may still contain
      structurally or observationally equal terms. *)
  Definition pointer_identical (left right : Term) : bool :=
    Nat.eqb left right.

  Theorem pointer_identity_implies_exact_key_equality :
      forall (key_of : Term -> ExactKey) left right,
        pointer_identical left right = true ->
        key_of left = key_of right.
  Proof.
    intros key_of left right Hsame.
    unfold pointer_identical in Hsame.
    apply Nat.eqb_eq in Hsame. subst right. reflexivity.
  Qed.

  Definition exact_insert
      (key : ExactKey) (representatives : list ExactKey) : list ExactKey :=
    if in_dec Nat.eq_dec key representatives
    then representatives
    else representatives ++ [key].

  Definition accelerated_insert
      (digest : ExactKey -> Digest)
      (key : ExactKey)
      (representatives : list ExactKey) : list ExactKey :=
    if accelerated_member digest key representatives
    then representatives
    else representatives ++ [key].

  Theorem accelerated_insert_is_exact : forall digest key representatives,
      accelerated_insert digest key representatives =
      exact_insert key representatives.
  Proof.
    intros digest key representatives.
    unfold accelerated_insert, exact_insert.
    destruct (accelerated_member digest key representatives) eqn:Hmember.
    - apply accelerated_member_iff in Hmember.
      destruct (in_dec Nat.eq_dec key representatives) as [_ | Habsent].
      + reflexivity.
      + contradiction.
    - assert (Habsent : ~ In key representatives).
      { intro Hin.
        pose proof
          (proj2 (accelerated_member_iff digest key representatives) Hin)
          as Hpresent.
        rewrite Hpresent in Hmember. discriminate. }
      destruct (in_dec Nat.eq_dec key representatives) as [Hin | _].
      + contradiction.
      + reflexivity.
  Qed.

  Inductive InsertResult : Type :=
  | Stored : list ExactKey -> InsertResult
  | ResourceExhausted : list ExactKey -> InsertResult.

  (** Duplicates remain admissible at the distinct-reading limit.  A new
      representative is appended only when capacity remains; otherwise the
      previous state is returned unchanged with explicit exhaustion. *)
  Definition bounded_accelerated_insert
      (digest : ExactKey -> Digest)
      (capacity : nat)
      (key : ExactKey)
      (representatives : list ExactKey) : InsertResult :=
    if accelerated_member digest key representatives
    then Stored representatives
    else if length representatives <? capacity
         then Stored (representatives ++ [key])
         else ResourceExhausted representatives.

  Definition bounded_exact_insert
      (capacity : nat)
      (key : ExactKey)
      (representatives : list ExactKey) : InsertResult :=
    if in_dec Nat.eq_dec key representatives
    then Stored representatives
    else if length representatives <? capacity
         then Stored (representatives ++ [key])
         else ResourceExhausted representatives.

  Theorem bounded_accelerated_insert_is_exact :
      forall digest capacity key representatives,
        bounded_accelerated_insert digest capacity key representatives =
        bounded_exact_insert capacity key representatives.
  Proof.
    intros digest capacity key representatives.
    unfold bounded_accelerated_insert, bounded_exact_insert.
    destruct (accelerated_member digest key representatives) eqn:Hmember.
    - apply accelerated_member_iff in Hmember.
      destruct (in_dec Nat.eq_dec key representatives) as [_ | Habsent].
      + reflexivity.
      + contradiction.
    - assert (Habsent : ~ In key representatives).
      { intro Hin.
        pose proof
          (proj2 (accelerated_member_iff digest key representatives) Hin)
          as Hpresent.
        rewrite Hpresent in Hmember. discriminate. }
      destruct (in_dec Nat.eq_dec key representatives) as [Hin | _].
      + contradiction.
      + reflexivity.
  Qed.

  Theorem stored_never_exceeds_capacity :
      forall digest capacity key representatives stored,
        length representatives <= capacity ->
        bounded_accelerated_insert digest capacity key representatives =
          Stored stored ->
        length stored <= capacity.
  Proof.
    intros digest capacity key representatives stored Hbound Hstored.
    unfold bounded_accelerated_insert in Hstored.
    destruct (accelerated_member digest key representatives).
    - injection Hstored as Hequal. subst stored. exact Hbound.
    - destruct (length representatives <? capacity) eqn:Hroom.
      + inversion Hstored. subst stored. rewrite length_app. cbn.
        apply Nat.ltb_lt in Hroom. lia.
      + discriminate.
  Qed.

  Theorem exhaustion_preserves_state :
      forall digest capacity key representatives exhausted,
        bounded_accelerated_insert digest capacity key representatives =
          ResourceExhausted exhausted ->
        exhausted = representatives /\
        capacity <= length representatives /\
        ~ In key representatives.
  Proof.
    intros digest capacity key representatives exhausted Hexhausted.
    unfold bounded_accelerated_insert in Hexhausted.
    destruct (accelerated_member digest key representatives) eqn:Hmember.
    - discriminate.
    - destruct (length representatives <? capacity) eqn:Hroom.
      + discriminate.
      + inversion Hexhausted. subst exhausted. split; [reflexivity |].
        split.
        * apply Nat.ltb_ge. exact Hroom.
        * intro Hin.
          pose proof
            (proj2 (accelerated_member_iff digest key representatives) Hin)
            as Hpresent.
          rewrite Hpresent in Hmember. discriminate.
  Qed.

  (** Retained-space models.  [exact_key_bytes] is the old sum of complete
      key lengths.  [compact_witness_bytes] charges one fixed-width digest
      and representative index per retained semantic class. *)
  Definition exact_key_bytes
      (key_bytes : ExactKey -> nat)
      (representatives : list ExactKey) : nat :=
    fold_right (fun key total => key_bytes key + total) 0 representatives.

  Definition compact_witness_bytes
      (witness_width : nat)
      (representatives : list ExactKey) : nat :=
    length representatives * witness_width.

  Theorem compact_witness_bound :
      forall witness_width representatives node_count per_node_limit,
        length representatives <= node_count * per_node_limit ->
        compact_witness_bytes witness_width representatives <=
          node_count * per_node_limit * witness_width.
  Proof.
    intros witness_width representatives node_count per_node_limit Hbound.
    unfold compact_witness_bytes. nia.
  Qed.

  (** A depth-[n] unary chain retains keys of sizes [1] through [n]. *)
  Fixpoint chain_exact_key_bytes (n : nat) : nat :=
    match n with
    | 0 => 0
    | S predecessor => S predecessor + chain_exact_key_bytes predecessor
    end.

  Definition chain_compact_witness_bytes
      (witness_width depth : nat) : nat :=
    depth * witness_width.

  Theorem chain_exact_keys_are_triangular : forall depth,
      2 * chain_exact_key_bytes depth = depth * (depth + 1).
  Proof.
    induction depth as [|depth IH].
    - reflexivity.
    - change
        (2 * (S depth + chain_exact_key_bytes depth) =
         S depth * (S depth + 1)).
      rewrite Nat.mul_add_distr_l. rewrite IH. nia.
  Qed.

  Theorem chain_compact_witnesses_are_linear : forall witness_width depth,
      chain_compact_witness_bytes witness_width depth =
      depth * witness_width.
  Proof. reflexivity. Qed.

  Print Assumptions accelerated_member_iff.
  Print Assumptions digest_collision_cannot_conflate.
  Print Assumptions structural_true_selects_shortcut.
  Print Assumptions structural_false_selects_exact_fallback.
  Print Assumptions structural_or_exact_is_exact.
  Print Assumptions structurally_distinct_observational_equal_falls_back.
  Print Assumptions structural_accelerated_member_iff_exact.
  Print Assumptions pointer_identity_implies_exact_key_equality.
  Print Assumptions accelerated_insert_is_exact.
  Print Assumptions bounded_accelerated_insert_is_exact.
  Print Assumptions stored_never_exceeds_capacity.
  Print Assumptions exhaustion_preserves_state.
  Print Assumptions compact_witness_bound.
  Print Assumptions chain_exact_keys_are_triangular.

End KbestCollisionSafeDedup.
