(** * Exact structural semantic keys for recursive collections

    Generated semantic metadata advertises the StructuralV2 key ABI.  A
    collection implementation that first reduces each recursive element to a
    finite digest cannot implement that contract: a digest collision erases
    the element, map-pair, or multiplicity witness before the mandatory exact
    comparison can run.

    This model gives each collection entry an exact, framed structural field.
    The concrete byte encoder represents [WireUnary], [WirePair], and
    [WireCounted] with domain tags and length-framed exact child streams.  The
    model keeps those frames as constructors so that the proof addresses the
    collection algebra independently of the already-proved byte-framing
    codec.  Canonical sorting is a representation concern established by
    [CanonicalSemanticArena]; it never replaces exact entry equality here. *)

From Stdlib Require Import List Arith.PeanoNat.
Import ListNotations.

Module ExactCollectionSemanticKey.

  Definition Byte := nat.
  Definition ExactKey := list Byte.

  (** A deliberately colliding finite accelerator.  It is sufficient to
      exhibit why a digest-only collection carrier cannot establish exact
      identity; production accelerators remain legal only before an exact
      fallback. *)
  Definition legacy_digest (_key : ExactKey) : nat := 0.

  Theorem digest_only_observation_is_not_injective :
      exists left right,
        left <> right /\ legacy_digest left = legacy_digest right.
  Proof.
    exists [0], [1]. split; [discriminate | reflexivity].
  Qed.

  Inductive ExactCollection : Type :=
  | ExactSet : list ExactKey -> ExactCollection
  | ExactMap : list (ExactKey * ExactKey) -> ExactCollection
  | ExactBag : nat -> list (ExactKey * nat) -> ExactCollection
  | ExactPathNeutral : ExactCollection
  | ExactPathSet : list ExactKey -> ExactCollection
  | ExactPathMap : list (ExactKey * ExactKey) -> ExactCollection.

  Inductive WireKind : Type :=
  | WireSet
  | WireMap
  | WireBag
  | WirePathNeutral
  | WirePathSet
  | WirePathMap.

  (** These constructors are the typed form of the runtime's domain-separated
      length-framed child writes.  Pair boundaries and bag multiplicities are
      therefore data, never inferred from a digest or display string. *)
  Inductive WireEntry : Type :=
  | WireUnary : ExactKey -> WireEntry
  | WirePair : ExactKey -> ExactKey -> WireEntry
  | WireCounted : ExactKey -> nat -> WireEntry.

  Definition WireCollection : Type :=
    (nat * WireKind * nat * list WireEntry)%type.

  Definition wire_total (wire : WireCollection) : nat :=
    let '(_, _, total, _) := wire in total.

  Definition wire_entries (wire : WireCollection) : list WireEntry :=
    let '(_, _, _, entries) := wire in entries.

  Definition map_unary (keys : list ExactKey) : list WireEntry :=
    map WireUnary keys.

  Definition map_pair (entries : list (ExactKey * ExactKey))
      : list WireEntry :=
    map (fun entry => WirePair (fst entry) (snd entry)) entries.

  Definition map_counted (entries : list (ExactKey * nat))
      : list WireEntry :=
    map (fun entry => WireCounted (fst entry) (snd entry)) entries.

  Definition encode_collection (collection : ExactCollection)
      : WireCollection :=
    match collection with
    | ExactSet keys => (2, WireSet, length keys, map_unary keys)
    | ExactMap entries => (2, WireMap, length entries, map_pair entries)
    | ExactBag total entries =>
        (2, WireBag, total, map_counted entries)
    | ExactPathNeutral => (2, WirePathNeutral, 0, [])
    | ExactPathSet keys =>
        (2, WirePathSet, length keys, map_unary keys)
    | ExactPathMap entries =>
        (2, WirePathMap, length entries, map_pair entries)
    end.

  Lemma map_unary_injective : forall left right,
      map_unary left = map_unary right -> left = right.
  Proof.
    induction left as [|left_key left IH]; destruct right as [|right_key right];
      simpl; intros Hequal; try discriminate; try reflexivity.
    assert (Hhead : WireUnary left_key = WireUnary right_key).
    { exact (f_equal (hd (WireUnary [])) Hequal). }
    assert (Htail : map_unary left = map_unary right).
    { exact (f_equal (@tl WireEntry) Hequal). }
    inversion Hhead. subst right_key. f_equal. now apply IH.
  Qed.

  Lemma map_pair_injective : forall left right,
      map_pair left = map_pair right -> left = right.
  Proof.
    induction left as [|[left_key left_value] left IH];
      destruct right as [|[right_key right_value] right];
      simpl; intros Hequal; try discriminate; try reflexivity.
    assert (Hhead : WirePair left_key left_value =
                    WirePair right_key right_value).
    { exact (f_equal (hd (WireUnary [])) Hequal). }
    assert (Htail : map_pair left = map_pair right).
    { exact (f_equal (@tl WireEntry) Hequal). }
    inversion Hhead. subst right_key right_value. f_equal. now apply IH.
  Qed.

  Lemma map_counted_injective : forall left right,
      map_counted left = map_counted right -> left = right.
  Proof.
    induction left as [|[left_key left_count] left IH];
      destruct right as [|[right_key right_count] right];
      simpl; intros Hequal; try discriminate; try reflexivity.
    assert (Hhead : WireCounted left_key left_count =
                    WireCounted right_key right_count).
    { exact (f_equal (hd (WireUnary [])) Hequal). }
    assert (Htail : map_counted left = map_counted right).
    { exact (f_equal (@tl WireEntry) Hequal). }
    inversion Hhead. subst right_key right_count. f_equal. now apply IH.
  Qed.

  Theorem encode_collection_injective : forall left right,
      encode_collection left = encode_collection right -> left = right.
  Proof.
    intros left right Hequal.
    destruct left; destruct right; simpl in Hequal; try discriminate.
    - f_equal. apply map_unary_injective.
      exact (f_equal wire_entries Hequal).
    - f_equal. apply map_pair_injective.
      exact (f_equal wire_entries Hequal).
    - assert (Htotal := f_equal wire_total Hequal).
      simpl in Htotal. subst n0. f_equal.
      apply map_counted_injective.
      exact (f_equal wire_entries Hequal).
    - reflexivity.
    - f_equal. apply map_unary_injective.
      exact (f_equal wire_entries Hequal).
    - f_equal. apply map_pair_injective.
      exact (f_equal wire_entries Hequal).
  Qed.

  Theorem digest_collision_cannot_merge_exact_collections :
      forall left right,
        left <> right ->
        legacy_digest (concat (map (fun _ => [0])
          (let '(_, _, _, entries) := encode_collection left in entries))) =
        legacy_digest (concat (map (fun _ => [0])
          (let '(_, _, _, entries) := encode_collection right in entries))) ->
        encode_collection left <> encode_collection right.
  Proof.
    intros left right Hdistinct _ Hequal.
    apply Hdistinct. now apply encode_collection_injective.
  Qed.

  Theorem path_modes_are_domain_separated :
      encode_collection ExactPathNeutral <>
        encode_collection (ExactPathSet []) /\
      encode_collection ExactPathNeutral <>
        encode_collection (ExactPathMap []) /\
      encode_collection (ExactPathSet []) <>
        encode_collection (ExactPathMap []).
  Proof. repeat split; discriminate. Qed.

  Print Assumptions digest_only_observation_is_not_injective.
  Print Assumptions map_unary_injective.
  Print Assumptions map_pair_injective.
  Print Assumptions map_counted_injective.
  Print Assumptions encode_collection_injective.
  Print Assumptions digest_collision_cannot_merge_exact_collections.
  Print Assumptions path_modes_are_domain_separated.

End ExactCollectionSemanticKey.
