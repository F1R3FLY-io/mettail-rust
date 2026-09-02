(** * Generated typed adapters for the canonical semantic image

    A generated language has a statically typed abstract-syntax tree, whereas
    [CanonicalSemanticTermImage] is deliberately source-neutral.  This file
    specifies the generated adapter between those presentations.  The adapter
    is a checked partial isomorphism: every accepted typed value has one
    canonical encoding, every accepted canonical value reconstructs exactly,
    and an unavailable or inexact codec rejects the value.

    The model distinguishes semantic structure from a backend key projection.
    Lists, bags, sets, maps, path maps, scopes, and children remain structural
    fields.  A legacy backend may additionally derive exact operator-payload
    bytes from one such field.  Those bytes are redundant observations, never
    the representation from which the field is reconstructed.  The final
    deforestation theorem permits a generated static backend to fuse

      typed AST -> canonical term -> semantic machine

    without allocating the intermediate term, while remaining observationally
    equal to the materialized composition.

    All recursion below is over flat lists.  The executable design uses the
    corresponding heap worklist and consumes at most one source node per
    transition; it never follows a child reference on the native call stack. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia Sorting.Permutation.
From RuntimeGrammar Require Import
  CanonicalSemanticTermImage StructuralProjectionImage TaggedReconstructionDispatch
  TaggedReconstructionMachine.
Import ListNotations.
Set Implicit Arguments.

Module GeneratedSemanticAdapter.
  Import CanonicalSemanticTermImage StructuralProjectionImage.

  (** An exact codec is a bounded, capability-installed partial isomorphism.
      [nat] abstracts a generated typed value identifier; [list nat] abstracts
      its canonical byte string.  Both laws are conditional because refusing a
      value is valid, but fabricating a value or accepting an ambiguous byte
      string is not. *)
  Record ExactCodec : Type := exact_codec {
    codec_encode : nat -> option (list nat);
    codec_decode : list nat -> option nat;
    codec_decode_encode : forall value bytes,
      codec_encode value = Some bytes ->
      codec_decode bytes = Some value;
    codec_encode_decode : forall bytes value,
      codec_decode bytes = Some value ->
      codec_encode value = Some bytes
  }.

  Definition CodecEnvironment : Type := nat -> option ExactCodec.

  (** Typed fields mirror the generated carriers.  References are already
      post-order arena indices.  Collection entries retain the distinction
      between values and key-value pairs, so Map and PathMap boundaries cannot
      be flattened accidentally. *)
  Inductive TypedField : Type :=
  | TypedChild : nat -> TypedField
  | TypedSequence : list nat -> TypedField
  | TypedCollection : nat -> list CollectionEntry -> TypedField
  | TypedPathMapEmpty : TypedField
  | TypedPathMapSet : list nat -> TypedField
  | TypedPathMapMap : list (nat * nat) -> TypedField
  | TypedOptional : option nat -> TypedField
  | TypedOptionalSequence : option (list nat) -> TypedField
  | TypedOptionalToken : option (list nat) -> TypedField
  | TypedScope : nat -> nat -> nat -> TypedField
  | TypedVariable : TermVariable -> TypedField
  | TypedScalar : Scalar -> TypedField
  | TypedToken : list nat -> TypedField
  | TypedBytes : list nat -> TypedField
  | TypedOpaque : nat -> nat -> TypedField
  | TypedUnit : TypedField.

  (** A field layout is generated once from the language declaration.  Stable
      kind, domain, and codec identifiers make the decoder reject a value that
      belongs to a different constructor shape. *)
  Inductive FieldLayout : Type :=
  | LayoutChild : FieldLayout
  | LayoutSequence : FieldLayout
  | LayoutCollection : nat -> FieldLayout
  | LayoutPathMap : FieldLayout
  | LayoutOptional : FieldLayout
  | LayoutOptionalSequence : FieldLayout
  | LayoutOptionalToken : FieldLayout
  | LayoutScope : nat -> FieldLayout
  | LayoutVariable : FieldLayout
  | LayoutScalar : FieldLayout
  | LayoutToken : FieldLayout
  | LayoutBytes : FieldLayout
  | LayoutOpaque : nat -> FieldLayout
  | LayoutUnit : FieldLayout.

  Fixpoint decode_pathmap_set_entries
      (entries : list PathMapEntry) : option (list nat) :=
    match entries with
    | [] => Some []
    | PathMapKey key :: rest =>
        option_map (cons key) (decode_pathmap_set_entries rest)
    | PathMapKeyValue _ _ :: _ => None
    end.

  Fixpoint decode_pathmap_map_entries
      (entries : list PathMapEntry) : option (list (nat * nat)) :=
    match entries with
    | [] => Some []
    | PathMapKey _ :: _ => None
    | PathMapKeyValue key value :: rest =>
        option_map (cons (key, value)) (decode_pathmap_map_entries rest)
    end.

  Lemma decode_encoded_pathmap_set_entries :
    forall keys,
      decode_pathmap_set_entries (map PathMapKey keys) = Some keys.
  Proof.
    induction keys as [|key rest IH]; cbn; [reflexivity | now rewrite IH].
  Qed.

  Lemma decode_encoded_pathmap_map_entries :
    forall entries,
      decode_pathmap_map_entries
        (map (fun entry => PathMapKeyValue (fst entry) (snd entry)) entries) =
      Some entries.
  Proof.
    induction entries as [|[key value] rest IH]; cbn;
      [reflexivity | now rewrite IH].
  Qed.

  Lemma encoded_decoded_pathmap_set_entries :
    forall entries keys,
      decode_pathmap_set_entries entries = Some keys ->
      map PathMapKey keys = entries.
  Proof.
    induction entries as [|entry rest IH]; intros keys Hdecode; cbn in Hdecode.
    - inversion Hdecode. reflexivity.
    - destruct entry as [key | key value]; try discriminate.
      destruct (decode_pathmap_set_entries rest) as [rest_keys |] eqn:Hrest;
        try discriminate.
      inversion Hdecode; subst. cbn. f_equal. now apply IH.
  Qed.

  Lemma encoded_decoded_pathmap_map_entries :
    forall entries pairs,
      decode_pathmap_map_entries entries = Some pairs ->
      map (fun entry => PathMapKeyValue (fst entry) (snd entry)) pairs = entries.
  Proof.
    induction entries as [|entry rest IH]; intros pairs Hdecode; cbn in Hdecode.
    - inversion Hdecode. reflexivity.
    - destruct entry as [key | key value]; try discriminate.
      destruct (decode_pathmap_map_entries rest) as [rest_pairs |] eqn:Hrest;
        try discriminate.
      inversion Hdecode; subst. cbn. f_equal. now apply IH.
  Qed.

  Definition encode_typed_field
      (codecs : CodecEnvironment) (layout : FieldLayout) (value : TypedField)
      : option Field :=
    match layout, value with
    | LayoutChild, TypedChild reference => Some (ChildRef reference)
    | LayoutSequence, TypedSequence references => Some (SequenceRefs references)
    | LayoutCollection expected_kind, TypedCollection actual_kind entries =>
        if Nat.eqb expected_kind actual_kind
        then Some (CollectionRefs expected_kind entries)
        else None
    | LayoutPathMap, TypedPathMapEmpty =>
        Some (PathMapRefs PathMapNeutralEmpty [])
    | LayoutPathMap, TypedPathMapSet keys =>
        Some (PathMapRefs PathMapSetMode (map PathMapKey keys))
    | LayoutPathMap, TypedPathMapMap entries =>
        Some (PathMapRefs PathMapMapMode
          (map (fun entry => PathMapKeyValue (fst entry) (snd entry)) entries))
    | LayoutOptional, TypedOptional reference => Some (OptionalRef reference)
    | LayoutOptionalSequence, TypedOptionalSequence references =>
        Some (OptionalSequenceRefs references)
    | LayoutOptionalToken, TypedOptionalToken bytes =>
        Some (OptionalTokenText bytes)
    | LayoutScope expected_domain, TypedScope actual_domain arity body =>
        if Nat.eqb expected_domain actual_domain
        then Some (ScopeRef expected_domain arity body)
        else None
    | LayoutVariable, TypedVariable variable => Some (VariableField variable)
    | LayoutScalar, TypedScalar scalar_value => Some (ScalarField scalar_value)
    | LayoutToken, TypedToken bytes => Some (TokenText bytes)
    | LayoutBytes, TypedBytes bytes => Some (ByteString bytes)
    | LayoutOpaque expected_codec, TypedOpaque actual_codec opaque_value =>
        if Nat.eqb expected_codec actual_codec then
          match codecs expected_codec with
          | Some codec =>
              option_map (OpaqueField expected_codec)
                (codec_encode codec opaque_value)
          | None => None
          end
        else None
    | LayoutUnit, TypedUnit => Some UnitField
    | _, _ => None
    end.

  Definition decode_typed_field
      (codecs : CodecEnvironment) (layout : FieldLayout) (value : Field)
      : option TypedField :=
    match layout, value with
    | LayoutChild, ChildRef reference => Some (TypedChild reference)
    | LayoutSequence, SequenceRefs references => Some (TypedSequence references)
    | LayoutCollection expected_kind, CollectionRefs actual_kind entries =>
        if Nat.eqb expected_kind actual_kind
        then Some (TypedCollection expected_kind entries)
        else None
    | LayoutPathMap, PathMapRefs PathMapNeutralEmpty [] =>
        Some TypedPathMapEmpty
    | LayoutPathMap, PathMapRefs PathMapSetMode entries =>
        option_map TypedPathMapSet (decode_pathmap_set_entries entries)
    | LayoutPathMap, PathMapRefs PathMapMapMode entries =>
        option_map TypedPathMapMap (decode_pathmap_map_entries entries)
    | LayoutOptional, OptionalRef reference => Some (TypedOptional reference)
    | LayoutOptionalSequence, OptionalSequenceRefs references =>
        Some (TypedOptionalSequence references)
    | LayoutOptionalToken, OptionalTokenText bytes =>
        Some (TypedOptionalToken bytes)
    | LayoutScope expected_domain, ScopeRef actual_domain arity body =>
        if Nat.eqb expected_domain actual_domain
        then Some (TypedScope expected_domain arity body)
        else None
    | LayoutVariable, VariableField variable => Some (TypedVariable variable)
    | LayoutScalar, ScalarField scalar_value => Some (TypedScalar scalar_value)
    | LayoutToken, TokenText bytes => Some (TypedToken bytes)
    | LayoutBytes, ByteString bytes => Some (TypedBytes bytes)
    | LayoutOpaque expected_codec, OpaqueField actual_codec bytes =>
        if Nat.eqb expected_codec actual_codec then
          match codecs expected_codec with
          | Some codec =>
              option_map (TypedOpaque expected_codec) (codec_decode codec bytes)
          | None => None
          end
        else None
    | LayoutUnit, UnitField => Some TypedUnit
    | _, _ => None
    end.

  Lemma decode_encode_typed_field :
    forall codecs layout typed canonical,
      encode_typed_field codecs layout typed = Some canonical ->
      decode_typed_field codecs layout canonical = Some typed.
  Proof.
    intros codecs layout typed canonical Hencode.
    destruct layout; destruct typed; cbn in Hencode; try discriminate;
      try (inversion Hencode; reflexivity).
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst. inversion Hencode. subst.
      cbn. now rewrite Nat.eqb_refl.
    - inversion Hencode; subst. cbn.
      now rewrite decode_encoded_pathmap_set_entries.
    - inversion Hencode; subst. cbn.
      now rewrite decode_encoded_pathmap_map_entries.
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst. inversion Hencode. subst.
      cbn. now rewrite Nat.eqb_refl.
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst.
      destruct (codecs n0) as [codec |] eqn:Hcodec; try discriminate.
      destruct (codec_encode codec n1) as [bytes |] eqn:Hbytes; try discriminate.
      inversion Hencode; subst. cbn. rewrite Nat.eqb_refl, Hcodec. cbn.
      now rewrite (@codec_decode_encode codec n1 bytes Hbytes).
  Qed.

  Lemma encode_decode_typed_field :
    forall codecs layout canonical typed,
      decode_typed_field codecs layout canonical = Some typed ->
      encode_typed_field codecs layout typed = Some canonical.
  Proof.
    intros codecs layout canonical typed Hdecode.
    destruct layout; destruct canonical; cbn in Hdecode; try discriminate;
      try (inversion Hdecode; reflexivity).
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst. inversion Hdecode. subst.
      cbn. now rewrite Nat.eqb_refl.
    - destruct p; try discriminate.
      + destruct l; try discriminate. inversion Hdecode. reflexivity.
      + destruct (decode_pathmap_set_entries l) as [keys |] eqn:Hentries;
          try discriminate.
        inversion Hdecode; subst. cbn. f_equal.
        now rewrite (@encoded_decoded_pathmap_set_entries l keys Hentries).
      + destruct (decode_pathmap_map_entries l) as [entries |] eqn:Hentries;
          try discriminate.
        inversion Hdecode; subst. cbn. f_equal.
        now rewrite (@encoded_decoded_pathmap_map_entries l entries Hentries).
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst. inversion Hdecode. subst.
      cbn. now rewrite Nat.eqb_refl.
    - destruct (Nat.eqb n n0) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst.
      destruct (codecs n0) as [codec |] eqn:Hcodec; try discriminate.
      destruct (codec_decode codec l) as [opaque_value |] eqn:Hvalue;
        try discriminate.
      inversion Hdecode; subst. cbn. rewrite Nat.eqb_refl, Hcodec. cbn.
      now rewrite (@codec_encode_decode codec l opaque_value Hvalue).
  Qed.

  Theorem missing_opaque_codec_fails_closed :
    forall codecs codec opaque_value,
      codecs codec = None ->
      encode_typed_field codecs (LayoutOpaque codec)
        (TypedOpaque codec opaque_value) = None.
  Proof.
    intros codecs codec opaque_value Hmissing. cbn.
    now rewrite Nat.eqb_refl, Hmissing.
  Qed.

  Theorem collection_pair_boundaries_are_preserved :
    forall codecs kind entries,
      encode_typed_field codecs (LayoutCollection kind)
        (TypedCollection kind entries) = Some (CollectionRefs kind entries).
  Proof. intros. cbn. now rewrite Nat.eqb_refl. Qed.

  (** Human-readable rendering is an observation, not an exact semantic key.
      In particular, deterministic sorting does not repair a non-injective
      element rendering: two unequal singleton collections still collide. *)
  Definition ExactByteObservation (A : Type) (observe : A -> list nat) : Prop :=
    forall left right, observe left = observe right -> left = right.

  Theorem display_only_collection_key_is_not_exact :
    forall (A : Type) (display : A -> list nat) left right,
      left <> right ->
      display left = display right ->
      ~ @ExactByteObservation (list A)
          (fun values => concat (map display values)).
  Proof.
    intros A display left right Hdistinct Hdisplay Hexact.
    apply Hdistinct.
    assert (Hsingleton : [left] = [right]).
    { apply (Hexact [left] [right]). cbn. now rewrite Hdisplay. }
    now inversion Hsingleton.
  Qed.

  (** The structural collection field remains exact even when a reader-facing
      observation collides.  This is the formal reason the generated adapter
      must retain entries and pair boundaries rather than blessing Display or
      Debug text as identity. *)
  Theorem encoded_collection_field_is_injective :
    forall codecs kind left right canonical,
      encode_typed_field codecs (LayoutCollection kind)
        (TypedCollection kind left) = Some canonical ->
      encode_typed_field codecs (LayoutCollection kind)
        (TypedCollection kind right) = Some canonical ->
      left = right.
  Proof.
    intros codecs kind left right canonical Hleft Hright.
    pose proof (@decode_encode_typed_field codecs (LayoutCollection kind)
      (TypedCollection kind left) canonical Hleft) as Hdecode_left.
    pose proof (@decode_encode_typed_field codecs (LayoutCollection kind)
      (TypedCollection kind right) canonical Hright) as Hdecode_right.
    rewrite Hdecode_left in Hdecode_right. inversion Hdecode_right. reflexivity.
  Qed.

  (** The generated lowering PDA carries two deliberately separate values for
      each completed child.  [lower_backend_id] is the transient e-class used
      to construct the backend graph.  [lower_exact_key] is the recursively
      framed structural ContentKey used for semantic ordering.  Confusing the
      former with the latter leaks allocation history into Map and PathMap
      identity: a local e-node key whose children are raw e-class numbers is
      not stable under arena renaming. *)
  Record FusedLowerValue : Type := fused_lower_value {
    lower_backend_id : nat;
    lower_exact_key : nat
  }.

  Definition raw_backend_descriptor
      (operator : nat) (children : list FusedLowerValue)
      : (nat * list nat)%type :=
    (operator, map lower_backend_id children).

  Definition exact_structural_descriptor
      (operator : nat) (children : list FusedLowerValue)
      : (nat * list nat)%type :=
    (operator, map lower_exact_key children).

  Theorem raw_backend_ids_are_not_representation_independent :
    exists left right,
      map lower_exact_key left = map lower_exact_key right /\
      raw_backend_descriptor 7 left <> raw_backend_descriptor 7 right.
  Proof.
    exists [fused_lower_value 0 10; fused_lower_value 1 20].
    exists [fused_lower_value 8 10; fused_lower_value 9 20].
    cbn. split; [reflexivity | discriminate].
  Qed.

  (** [nat] abstracts an exact framed ContentKey.  The encoder law is the
      production framing obligation: equal encodings imply equal operator and
      equal ordered child-key stream.  A finite digest may accelerate this
      function, but it cannot replace the exact result. *)
  Record ExactNodeEncoder : Type := exact_node_encoder {
    encode_exact_node : nat -> list nat -> nat;
    encode_exact_node_injective : forall left_operator left_children
        right_operator right_children,
      encode_exact_node left_operator left_children =
        encode_exact_node right_operator right_children ->
      left_operator = right_operator /\ left_children = right_children
  }.

  Definition fused_assemble
      (encoder : ExactNodeEncoder) (backend_id operator : nat)
      (children : list FusedLowerValue) : FusedLowerValue :=
    fused_lower_value backend_id
      (encode_exact_node encoder operator (map lower_exact_key children)).

  Theorem fused_assembly_erases_transient_backend_ids :
    forall encoder left_backend right_backend operator left right,
      map lower_exact_key left = map lower_exact_key right ->
      lower_exact_key (fused_assemble encoder left_backend operator left) =
      lower_exact_key (fused_assemble encoder right_backend operator right).
  Proof. intros. cbn. now rewrite H. Qed.

  Theorem ordered_fused_assembly_preserves_child_order :
    forall encoder left_backend right_backend operator left right,
      map lower_exact_key left <> map lower_exact_key right ->
      lower_exact_key (fused_assemble encoder left_backend operator left) <>
      lower_exact_key (fused_assemble encoder right_backend operator right).
  Proof.
    intros encoder left_backend right_backend operator left right Hdifferent Hequal.
    apply Hdifferent.
    pose proof (@encode_exact_node_injective encoder operator
      (map lower_exact_key left) operator (map lower_exact_key right) Hequal)
      as [_ Hchildren].
    exact Hchildren.
  Qed.

  (** Unordered assembly sorts the recursively exact child keys.  The
      [canon_iff_permutation] theorem supplies both halves of the contract:
      enumeration permutations collapse to one key, while distinct
      multisets—including distinct bag multiplicities—cannot alias. *)
  Record ExactUnorderedCanonicalizer : Type := exact_unordered_canonicalizer {
    canonicalize_exact_keys : list nat -> list nat;
    canonicalize_exact_keys_iff_permutation : forall left right,
      Permutation left right <->
      canonicalize_exact_keys left = canonicalize_exact_keys right
  }.

  Definition canonical_fused_keys
      (canonicalizer : ExactUnorderedCanonicalizer)
      (children : list FusedLowerValue) : list nat :=
    canonicalize_exact_keys canonicalizer (map lower_exact_key children).

  Definition fused_assemble_unordered
      (encoder : ExactNodeEncoder)
      (canonicalizer : ExactUnorderedCanonicalizer)
      (backend_id operator : nat)
      (children : list FusedLowerValue) : FusedLowerValue :=
    fused_lower_value backend_id
      (encode_exact_node encoder operator
        (canonical_fused_keys canonicalizer children)).

  Theorem unordered_fused_assembly_is_permutation_invariant :
    forall encoder canonicalizer left_backend right_backend operator left right,
      Permutation left right ->
      lower_exact_key
        (fused_assemble_unordered encoder canonicalizer
          left_backend operator left) =
      lower_exact_key
        (fused_assemble_unordered encoder canonicalizer
          right_backend operator right).
  Proof.
    intros encoder canonicalizer left_backend right_backend operator left right Hperm.
    cbn. unfold canonical_fused_keys.
    rewrite (proj1 (canonicalize_exact_keys_iff_permutation canonicalizer
      (map lower_exact_key left) (map lower_exact_key right))).
    - reflexivity.
    - now apply Permutation_map.
  Qed.

  Theorem unordered_fused_assembly_distinguishes_nonpermutations :
    forall encoder canonicalizer left_backend right_backend operator left right,
      ~ Permutation (map lower_exact_key left) (map lower_exact_key right) ->
      lower_exact_key
        (fused_assemble_unordered encoder canonicalizer
          left_backend operator left) <>
      lower_exact_key
        (fused_assemble_unordered encoder canonicalizer
          right_backend operator right).
  Proof.
    intros encoder canonicalizer left_backend right_backend operator left right
      Hdifferent Hequal.
    apply Hdifferent.
    apply (proj2 (canonicalize_exact_keys_iff_permutation canonicalizer _ _)).
    pose proof (@encode_exact_node_injective encoder operator
      (canonical_fused_keys canonicalizer left) operator
      (canonical_fused_keys canonicalizer right) Hequal)
      as [_ Hchildren].
    exact Hchildren.
  Qed.

  (** Map-like entries are first assembled as an ordered pair node.  Therefore
      canonicalizing the outer entry multiset cannot erase the key/value
      boundary or swap the two components. *)
  Definition fused_pair
      (encoder : ExactNodeEncoder) (backend_id pair_operator : nat)
      (key value : FusedLowerValue) : FusedLowerValue :=
    fused_assemble encoder backend_id pair_operator [key; value].

  Theorem fused_pair_key_preserves_key_value_boundary :
    forall encoder left_backend right_backend pair_operator
        left_key left_value right_key right_value,
      lower_exact_key
        (fused_pair encoder left_backend pair_operator left_key left_value) =
      lower_exact_key
        (fused_pair encoder right_backend pair_operator right_key right_value) ->
      lower_exact_key left_key = lower_exact_key right_key /\
      lower_exact_key left_value = lower_exact_key right_value.
  Proof.
    intros encoder left_backend right_backend pair_operator
      left_key left_value right_key right_value Hequal.
    pose proof (@encode_exact_node_injective encoder pair_operator
      [lower_exact_key left_key; lower_exact_key left_value] pair_operator
      [lower_exact_key right_key; lower_exact_key right_value] Hequal)
      as [_ Hchildren].
    now inversion Hchildren.
  Qed.

  (** PathMap retains its mode as the first ordered structural child and sorts
      only the entry suffix.  Consequently the three empty modes stay
      distinct, while permutation of entries is consensus-invisible. *)
  Definition fused_pathmap
      (encoder : ExactNodeEncoder)
      (canonicalizer : ExactUnorderedCanonicalizer)
      (backend_id operator mode_key : nat)
      (entries : list FusedLowerValue) : FusedLowerValue :=
    fused_lower_value backend_id
      (encode_exact_node encoder operator
        (mode_key :: canonical_fused_keys canonicalizer entries)).

  Theorem fused_pathmap_mode_is_injective :
    forall encoder canonicalizer left_backend right_backend operator
        left_mode right_mode left_entries right_entries,
      left_mode <> right_mode ->
      lower_exact_key
        (fused_pathmap encoder canonicalizer
          left_backend operator left_mode left_entries) <>
      lower_exact_key
        (fused_pathmap encoder canonicalizer
          right_backend operator right_mode right_entries).
  Proof.
    intros encoder canonicalizer left_backend right_backend operator
      left_mode right_mode left_entries right_entries Hmode Hequal.
    apply Hmode.
    pose proof (@encode_exact_node_injective encoder operator
      (left_mode :: canonical_fused_keys canonicalizer left_entries) operator
      (right_mode :: canonical_fused_keys canonicalizer right_entries) Hequal)
      as [_ Hchildren].
    now inversion Hchildren.
  Qed.

  Theorem fused_pathmap_entries_are_permutation_invariant :
    forall encoder canonicalizer left_backend right_backend operator mode left right,
      Permutation left right ->
      lower_exact_key
        (fused_pathmap encoder canonicalizer left_backend operator mode left) =
      lower_exact_key
        (fused_pathmap encoder canonicalizer right_backend operator mode right).
  Proof.
    intros encoder canonicalizer left_backend right_backend operator mode left right Hperm.
    cbn. unfold canonical_fused_keys.
    rewrite (proj1 (canonicalize_exact_keys_iff_permutation canonicalizer
      (map lower_exact_key left) (map lower_exact_key right))).
    - reflexivity.
    - now apply Permutation_map.
  Qed.

  (** Recursive native carriers are described by a closed structural algebra;
      they are never inferred from a language/category name.  The first
      admitted product is the zipper topology used by Rholang and available to
      every generated language: one homogeneous PathMap plus one exact focus
      byte string.  Read versus write access belongs to the enclosing typed
      constructor/operator and does not change this structural product. *)
  Inductive NativeCarrierLayout : Type :=
  | LayoutZipper : nat -> nat -> NativeCarrierLayout.

  Inductive TypedNativeCarrier : Type :=
  | TypedZipper : TypedField -> list nat -> TypedNativeCarrier.

  Definition typed_field_is_pathmap (field : TypedField) : bool :=
    match field with
    | TypedPathMapEmpty
    | TypedPathMapSet _
    | TypedPathMapMap _ => true
    | _ => false
    end.

  Definition encode_native_carrier
      (codecs : CodecEnvironment) (layout : NativeCarrierLayout)
      (value : TypedNativeCarrier) : option (list Field) :=
    match layout, value with
    | LayoutZipper _ _, TypedZipper pathmap focus =>
        if typed_field_is_pathmap pathmap then
          match encode_typed_field codecs LayoutPathMap pathmap with
          | Some encoded_pathmap => Some [encoded_pathmap; ByteString focus]
          | None => None
          end
        else None
    end.

  Definition decode_native_carrier
      (codecs : CodecEnvironment) (layout : NativeCarrierLayout)
      (fields : list Field) : option TypedNativeCarrier :=
    match layout, fields with
    | LayoutZipper _ _, [encoded_pathmap; ByteString focus] =>
        match decode_typed_field codecs LayoutPathMap encoded_pathmap with
        | Some pathmap => Some (TypedZipper pathmap focus)
        | None => None
        end
    | _, _ => None
    end.

  Lemma encoded_pathmap_is_typed_pathmap :
    forall codecs typed canonical,
      encode_typed_field codecs LayoutPathMap typed = Some canonical ->
      typed_field_is_pathmap typed = true.
  Proof.
    intros codecs typed canonical Hencode.
    destruct typed; cbn in Hencode; try discriminate; reflexivity.
  Qed.

  Theorem decode_encode_native_carrier :
    forall codecs layout typed canonical,
      encode_native_carrier codecs layout typed = Some canonical ->
      decode_native_carrier codecs layout canonical = Some typed.
  Proof.
    intros codecs [key_category value_category] [pathmap focus]
      canonical Hencode.
    destruct pathmap; cbn in Hencode; try discriminate;
      inversion Hencode; subst; cbn.
    - reflexivity.
    - now rewrite decode_encoded_pathmap_set_entries.
    - now rewrite decode_encoded_pathmap_map_entries.
  Qed.

  Theorem encode_decode_native_carrier :
    forall codecs layout canonical typed,
      decode_native_carrier codecs layout canonical = Some typed ->
      encode_native_carrier codecs layout typed = Some canonical.
  Proof.
    intros codecs [key_category value_category] canonical typed Hdecode.
    destruct canonical as [|first tail]; cbn in Hdecode; try discriminate.
    destruct tail as [|second tail]; cbn in Hdecode; try discriminate.
    destruct tail as [|third rest].
    2: { destruct second; cbn in Hdecode; discriminate. }
    destruct second; cbn in Hdecode; try discriminate.
    fold (decode_typed_field codecs LayoutPathMap first) in Hdecode.
    destruct (decode_typed_field codecs LayoutPathMap first)
      as [pathmap |] eqn:Hfield; try discriminate.
    inversion Hdecode; subst. unfold encode_native_carrier.
    pose proof (@encode_decode_typed_field codecs LayoutPathMap
      first pathmap Hfield) as Hencode.
    pose proof (@encoded_pathmap_is_typed_pathmap codecs pathmap first Hencode)
      as Hpathmap.
    destruct pathmap; cbn in Hpathmap; try discriminate;
      cbn in Hencode |-; inversion Hencode; reflexivity.
  Qed.

  Theorem zipper_focus_is_preserved :
    forall codecs key_category value_category pathmap focus canonical,
      encode_native_carrier codecs
        (LayoutZipper key_category value_category)
        (TypedZipper pathmap focus) = Some canonical ->
      exists encoded_pathmap, canonical = [encoded_pathmap; ByteString focus].
  Proof.
    intros codecs key_category value_category pathmap focus canonical Hencode.
    destruct pathmap; cbn in Hencode; try discriminate;
      inversion Hencode; subst; eexists; reflexivity.
  Qed.

  Theorem zipper_pathmap_topology_is_injective :
    forall codecs key_category value_category
        left_pathmap left_focus right_pathmap right_focus canonical,
      encode_native_carrier codecs
        (LayoutZipper key_category value_category)
        (TypedZipper left_pathmap left_focus) = Some canonical ->
      encode_native_carrier codecs
        (LayoutZipper key_category value_category)
        (TypedZipper right_pathmap right_focus) = Some canonical ->
      left_pathmap = right_pathmap /\ left_focus = right_focus.
  Proof.
    intros codecs key_category value_category left_pathmap left_focus
      right_pathmap right_focus canonical Hleft Hright.
    pose proof (@decode_encode_native_carrier codecs
      (LayoutZipper key_category value_category)
      (TypedZipper left_pathmap left_focus) canonical Hleft) as Hdecode_left.
    pose proof (@decode_encode_native_carrier codecs
      (LayoutZipper key_category value_category)
      (TypedZipper right_pathmap right_focus) canonical Hright) as Hdecode_right.
    rewrite Hdecode_left in Hdecode_right. inversion Hdecode_right. auto.
  Qed.

  Definition native_carrier_transition_consumption
      (pending : list TypedNativeCarrier) : nat :=
    match pending with
    | [] => 0
    | _ :: _ => 1
    end.

  Theorem native_carrier_transition_consumes_at_most_one_value :
    forall pending, native_carrier_transition_consumption pending <= 1.
  Proof. intros [|head tail]; cbn; lia. Qed.

  (** Semantic keys are interpreted in an explicit ABI namespace.  The legacy
      namespace contains rendered collection coefficients; the structural
      namespace contains the checked operator/child tree.  A key crossing a
      cache, bundle, or compatibility boundary is therefore the pair of its ABI
      and its exact byte stream, never the byte stream alone. *)
  Inductive SemanticKeyAbi : Type :=
  | LegacyRenderedV1
  | StructuralV2.

  Definition semantic_key_abi_tag (abi : SemanticKeyAbi) : nat :=
    match abi with
    | LegacyRenderedV1 => 1
    | StructuralV2 => 2
    end.

  Definition VersionedSemanticKey : Type := (nat * list nat)%type.

  Definition version_semantic_key
      (abi : SemanticKeyAbi) (bytes : list nat) : VersionedSemanticKey :=
    (semantic_key_abi_tag abi, bytes).

  Theorem semantic_key_abi_tag_is_injective :
    forall left right,
      semantic_key_abi_tag left = semantic_key_abi_tag right -> left = right.
  Proof.
    intros left right Hequal. destruct left, right; cbn in Hequal;
      try discriminate; reflexivity.
  Qed.

  Theorem versioned_semantic_key_is_injective :
    forall left_abi right_abi left_bytes right_bytes,
      version_semantic_key left_abi left_bytes =
      version_semantic_key right_abi right_bytes ->
      left_abi = right_abi /\ left_bytes = right_bytes.
  Proof.
    intros left_abi right_abi left_bytes right_bytes Hequal.
    inversion Hequal. split.
    - now apply semantic_key_abi_tag_is_injective.
    - reflexivity.
  Qed.

  Theorem semantic_key_abi_namespaces_are_disjoint :
    forall legacy_bytes structural_bytes,
      version_semantic_key LegacyRenderedV1 legacy_bytes <>
      version_semantic_key StructuralV2 structural_bytes.
  Proof. intros legacy_bytes structural_bytes Hequal. discriminate Hequal. Qed.

  (** An equality-preserving migration from a colliding rendered key to an
      exact key is impossible.  Consequently the structural ABI must be an
      explicit compatibility boundary rather than being advertised as
      byte-identical to the legacy rendered stream. *)
  Theorem colliding_legacy_key_cannot_be_preserved_by_exact_migration :
    forall (A : Type) (legacy exact : A -> list nat) left right,
      left <> right ->
      legacy left = legacy right ->
      (forall x y, legacy x = legacy y -> exact x = exact y) ->
      ExactByteObservation exact ->
      False.
  Proof.
    intros A legacy exact left right Hdistinct Hlegacy Hpreserves Hexact.
    apply Hdistinct. apply Hexact. now apply Hpreserves.
  Qed.

  (** PathMap's three typed constructors are part of the structural key.  This
      is stronger than recording the entry list: all three empty values remain
      distinct and a shared canonical field has exactly one typed preimage. *)
  Theorem encoded_pathmap_field_is_injective :
    forall codecs left right canonical,
      encode_typed_field codecs LayoutPathMap left = Some canonical ->
      encode_typed_field codecs LayoutPathMap right = Some canonical ->
      left = right.
  Proof.
    intros codecs left right canonical Hleft Hright.
    pose proof (@decode_encode_typed_field codecs LayoutPathMap
      left canonical Hleft) as Hdecode_left.
    pose proof (@decode_encode_typed_field codecs LayoutPathMap
      right canonical Hright) as Hdecode_right.
    rewrite Hdecode_left in Hdecode_right. inversion Hdecode_right. reflexivity.
  Qed.

  Theorem empty_pathmap_modes_have_distinct_structural_keys :
    forall codecs,
      encode_typed_field codecs LayoutPathMap TypedPathMapEmpty <>
        encode_typed_field codecs LayoutPathMap (TypedPathMapSet []) /\
      encode_typed_field codecs LayoutPathMap TypedPathMapEmpty <>
        encode_typed_field codecs LayoutPathMap (TypedPathMapMap []) /\
      encode_typed_field codecs LayoutPathMap (TypedPathMapSet []) <>
        encode_typed_field codecs LayoutPathMap (TypedPathMapMap []).
  Proof. intros codecs. cbn. repeat split; discriminate. Qed.

  Theorem optional_sequence_presence_is_preserved :
    forall codecs references,
      encode_typed_field codecs LayoutOptionalSequence
        (TypedOptionalSequence references) =
      Some (OptionalSequenceRefs references).
  Proof. reflexivity. Qed.

  Theorem optional_token_presence_is_preserved :
    forall codecs bytes,
      encode_typed_field codecs LayoutOptionalToken
        (TypedOptionalToken bytes) = Some (OptionalTokenText bytes).
  Proof. reflexivity. Qed.

  Theorem scope_domain_arity_and_body_are_preserved :
    forall codecs domain arity body,
      encode_typed_field codecs (LayoutScope domain)
        (TypedScope domain arity body) = Some (ScopeRef domain arity body).
  Proof. intros. cbn. now rewrite Nat.eqb_refl. Qed.

  Fixpoint encode_typed_fields
      (codecs : CodecEnvironment)
      (layouts : list FieldLayout) (values : list TypedField)
      : option (list Field) :=
    match layouts, values with
    | [], [] => Some []
    | layout :: layout_rest, value :: value_rest =>
        match encode_typed_field codecs layout value,
              encode_typed_fields codecs layout_rest value_rest with
        | Some encoded, Some encoded_rest => Some (encoded :: encoded_rest)
        | _, _ => None
        end
    | _, _ => None
    end.

  Fixpoint decode_typed_fields
      (codecs : CodecEnvironment)
      (layouts : list FieldLayout) (values : list Field)
      : option (list TypedField) :=
    match layouts, values with
    | [], [] => Some []
    | layout :: layout_rest, value :: value_rest =>
        match decode_typed_field codecs layout value,
              decode_typed_fields codecs layout_rest value_rest with
        | Some decoded, Some decoded_rest => Some (decoded :: decoded_rest)
        | _, _ => None
        end
    | _, _ => None
    end.

  Lemma decode_encode_typed_fields :
    forall codecs layouts typed canonical,
      encode_typed_fields codecs layouts typed = Some canonical ->
      decode_typed_fields codecs layouts canonical = Some typed.
  Proof.
    intros codecs layouts. induction layouts as [|layout layout_rest IH];
      intros typed canonical Hencode; destruct typed as [|value value_rest];
      cbn in Hencode; try discriminate.
    - inversion Hencode. reflexivity.
    - destruct (encode_typed_field codecs layout value) as [field |] eqn:Hfield;
        try discriminate.
      destruct (encode_typed_fields codecs layout_rest value_rest)
        as [fields |] eqn:Hfields; try discriminate.
      inversion Hencode; subst. cbn.
      rewrite (@decode_encode_typed_field codecs layout value field Hfield),
        (IH _ _ Hfields).
      reflexivity.
  Qed.

  Lemma encode_decode_typed_fields :
    forall codecs layouts canonical typed,
      decode_typed_fields codecs layouts canonical = Some typed ->
      encode_typed_fields codecs layouts typed = Some canonical.
  Proof.
    intros codecs layouts. induction layouts as [|layout layout_rest IH];
      intros canonical typed Hdecode; destruct canonical as [|field field_rest];
      cbn in Hdecode; try discriminate.
    - inversion Hdecode. reflexivity.
    - destruct (decode_typed_field codecs layout field) as [value |] eqn:Hfield;
        try discriminate.
      destruct (decode_typed_fields codecs layout_rest field_rest)
        as [values |] eqn:Hfields; try discriminate.
      inversion Hdecode; subst. cbn.
      rewrite (@encode_decode_typed_field codecs layout field value Hfield),
        (IH _ _ Hfields).
      reflexivity.
  Qed.

  (** Operator payloads are typed coefficients.  The layout fixes their codec;
      the stable category, constructor, and discriminant remain explicit and
      are checked rather than inferred from a textual name. *)
  Record TypedOp : Type := typed_op {
    typed_category : nat;
    typed_constructor : nat;
    typed_discriminant : nat;
    typed_coefficient : option nat
  }.

  Record OperatorLayout : Type := operator_layout {
    layout_category : nat;
    layout_constructor : nat;
    layout_discriminant : nat;
    layout_coefficient_codec : option nat
  }.

  Definition operator_ids_match (layout : OperatorLayout) (op : TypedOp) : bool :=
    Nat.eqb (layout_category layout) (typed_category op) &&
      (Nat.eqb (layout_constructor layout) (typed_constructor op) &&
       Nat.eqb (layout_discriminant layout) (typed_discriminant op)).

  Definition encode_coefficient
      (codecs : CodecEnvironment) (expected_codec : option nat)
      (value : option nat) : option (option Scalar) :=
    match expected_codec, value with
    | None, None => Some None
    | Some codec_id, Some typed_value =>
        match codecs codec_id with
        | Some codec =>
            option_map (fun bytes => Some (scalar codec_id bytes))
              (codec_encode codec typed_value)
        | None => None
        end
    | _, _ => None
    end.

  Definition decode_coefficient
      (codecs : CodecEnvironment) (expected_codec : option nat)
      (value : option Scalar) : option (option nat) :=
    match expected_codec, value with
    | None, None => Some None
    | Some codec_id, Some encoded =>
        if Nat.eqb codec_id (scalar_tag encoded) then
          match codecs codec_id with
          | Some codec => option_map Some (codec_decode codec (scalar_bytes encoded))
          | None => None
          end
        else None
    | _, _ => None
    end.

  Lemma decode_encode_coefficient :
    forall codecs expected typed canonical,
      encode_coefficient codecs expected typed = Some canonical ->
      decode_coefficient codecs expected canonical = Some typed.
  Proof.
    intros codecs [codec_id |] [typed_value |] canonical Hencode;
      cbn in Hencode; try discriminate.
    - destruct (codecs codec_id) as [codec |] eqn:Hcodec; try discriminate.
      destruct (codec_encode codec typed_value) as [bytes |] eqn:Hbytes;
        try discriminate.
      inversion Hencode; subst. cbn. rewrite Nat.eqb_refl, Hcodec. cbn.
      now rewrite (@codec_decode_encode codec typed_value bytes Hbytes).
    - inversion Hencode. reflexivity.
  Qed.

  Lemma encode_decode_coefficient :
    forall codecs expected canonical typed,
      decode_coefficient codecs expected canonical = Some typed ->
      encode_coefficient codecs expected typed = Some canonical.
  Proof.
    intros codecs [codec_id |] [[tag bytes] |] typed Hdecode;
      cbn in Hdecode; try discriminate.
    - destruct (Nat.eqb codec_id tag) eqn:Hequal; try discriminate.
      apply Nat.eqb_eq in Hequal. subst.
      destruct (codecs tag) as [codec |] eqn:Hcodec; try discriminate.
      destruct (codec_decode codec bytes) as [typed_value |] eqn:Hvalue;
        try discriminate.
      inversion Hdecode; subst. cbn. rewrite Hcodec. cbn.
      now rewrite (@codec_encode_decode codec bytes typed_value Hvalue).
    - inversion Hdecode. reflexivity.
  Qed.

  Definition adapt_typed_op
      (codecs : CodecEnvironment) (layout : OperatorLayout) (op : TypedOp)
      : option LegacyOp :=
    if operator_ids_match layout op then
      match encode_coefficient codecs (layout_coefficient_codec layout)
              (typed_coefficient op) with
      | Some payload =>
          Some (legacy_op
            (typed_category op)
            (typed_constructor op)
            (typed_discriminant op)
            payload)
      | None => None
      end
    else None.

  Definition reconstruct_typed_op
      (codecs : CodecEnvironment) (layout : OperatorLayout) (op : LegacyOp)
      : option TypedOp :=
    if Nat.eqb (layout_category layout) (legacy_category op) &&
       (Nat.eqb (layout_constructor layout) (legacy_constructor op) &&
        Nat.eqb (layout_discriminant layout) (legacy_discriminant op)) then
      match decode_coefficient codecs (layout_coefficient_codec layout)
              (legacy_payload op) with
      | Some payload =>
          Some (typed_op
            (legacy_category op)
            (legacy_constructor op)
            (legacy_discriminant op)
            payload)
      | None => None
      end
    else None.

  Lemma operator_ids_match_refl : forall layout,
      operator_ids_match layout
        (typed_op
          (layout_category layout)
          (layout_constructor layout)
          (layout_discriminant layout) None) = true.
  Proof.
    intros []. unfold operator_ids_match. cbn.
    now rewrite !Nat.eqb_refl.
  Qed.

  Lemma operator_ids_match_equalities : forall layout op,
      operator_ids_match layout op = true ->
      layout_category layout = typed_category op /\
      layout_constructor layout = typed_constructor op /\
      layout_discriminant layout = typed_discriminant op.
  Proof.
    intros layout op Hmatch. unfold operator_ids_match in Hmatch.
    apply Bool.andb_true_iff in Hmatch as [Hcategory Hrest].
    apply Bool.andb_true_iff in Hrest as [Hconstructor Hdiscriminant].
    repeat rewrite Nat.eqb_eq in *.
    auto.
  Qed.

  Lemma reconstruct_adapt_typed_op :
    forall codecs layout typed legacy,
      adapt_typed_op codecs layout typed = Some legacy ->
      reconstruct_typed_op codecs layout legacy = Some typed.
  Proof.
    intros codecs layout [category constructor discriminant coefficient]
      legacy Hadapt.
    unfold adapt_typed_op in Hadapt. cbn in Hadapt.
    destruct (operator_ids_match layout
      (typed_op category constructor discriminant coefficient)) eqn:Hids;
      try discriminate.
    destruct (encode_coefficient codecs (layout_coefficient_codec layout) coefficient)
      as [payload |] eqn:Hpayload; try discriminate.
    inversion Hadapt; subst. unfold reconstruct_typed_op. cbn.
    apply operator_ids_match_equalities in Hids as [Hcategory [Hconstructor Hdiscriminant]].
    rewrite Hcategory, Hconstructor, Hdiscriminant, !Nat.eqb_refl. cbn.
    now rewrite (@decode_encode_coefficient codecs
      (layout_coefficient_codec layout) coefficient payload Hpayload).
  Qed.

  Lemma adapt_reconstruct_typed_op :
    forall codecs layout legacy typed,
      reconstruct_typed_op codecs layout legacy = Some typed ->
      adapt_typed_op codecs layout typed = Some legacy.
  Proof.
    intros codecs layout [category constructor discriminant payload]
      typed Hreconstruct.
    unfold reconstruct_typed_op in Hreconstruct. cbn in Hreconstruct.
    destruct (Nat.eqb (layout_category layout) category &&
      (Nat.eqb (layout_constructor layout) constructor &&
       Nat.eqb (layout_discriminant layout) discriminant)) eqn:Hids;
      try discriminate.
    destruct (decode_coefficient codecs (layout_coefficient_codec layout) payload)
      as [coefficient |] eqn:Hpayload; try discriminate.
    inversion Hreconstruct; subst. unfold adapt_typed_op. cbn.
    change
      (operator_ids_match layout
        (typed_op category constructor discriminant coefficient) = true) in Hids.
    rewrite Hids, (@encode_decode_coefficient codecs
      (layout_coefficient_codec layout) payload coefficient Hpayload).
    reflexivity.
  Qed.

  Record SemanticAdapterLayout : Type := semantic_adapter_layout {
    adapter_operator : OperatorLayout;
    adapter_fields : list FieldLayout
  }.

  Record TypedNode : Type := typed_node {
    typed_node_op : TypedOp;
    typed_node_fields : list TypedField
  }.

  Definition adapt_typed_node
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (value : TypedNode) : option (Node LegacyOp) :=
    match adapt_typed_op codecs (adapter_operator layout) (typed_node_op value),
          encode_typed_fields codecs (adapter_fields layout) (typed_node_fields value) with
    | Some op, Some fields => Some (node op fields)
    | _, _ => None
    end.

  Definition reconstruct_typed_node
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (value : Node LegacyOp) : option TypedNode :=
    match reconstruct_typed_op codecs (adapter_operator layout) (node_op value),
          decode_typed_fields codecs (adapter_fields layout) (node_fields value) with
    | Some op, Some fields => Some (typed_node op fields)
    | _, _ => None
    end.

  Definition encode_typed_node
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (value : TypedNode) : option (Node CoreOp) :=
    option_map encode_node (adapt_typed_node codecs layout value).

  Definition decode_typed_node
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (value : Node CoreOp) : option TypedNode :=
    reconstruct_typed_node codecs layout (decode_node value).

  Theorem typed_node_round_trip :
    forall codecs layout typed canonical,
      encode_typed_node codecs layout typed = Some canonical ->
      decode_typed_node codecs layout canonical = Some typed.
  Proof.
    intros codecs layout [op fields] canonical Hencode.
    unfold encode_typed_node, adapt_typed_node in Hencode. cbn in Hencode.
    destruct (adapt_typed_op codecs (adapter_operator layout) op)
      as [legacy_op_value |] eqn:Hop; try discriminate.
    destruct (encode_typed_fields codecs (adapter_fields layout) fields)
      as [legacy_fields |] eqn:Hfields; try discriminate.
    inversion Hencode; subst. unfold decode_typed_node, reconstruct_typed_node.
    cbn. rewrite decode_encode_op.
    rewrite (@reconstruct_adapt_typed_op codecs (adapter_operator layout)
      op legacy_op_value Hop),
      (@decode_encode_typed_fields codecs (adapter_fields layout)
        fields legacy_fields Hfields).
    reflexivity.
  Qed.

  (** The generated Dovetail inverse does not read [Field] values directly.
      Lowering represents recursive, optional, and scope fields with an
      explicit derivation spine.  This projection supplies the category and
      field index retained by the Rust [SemanticAdapterLayout]; those facts are
      intentionally absent from the source-neutral [Field] carrier itself.

      A scope's [body_category] is an independent parameter.  It must be the
      category declared by the binder field, not the enclosing constructor's
      category.  This is the formal seam that rules out casting a body pointer
      to an unrelated generated visit-task type. *)
  Definition typed_field_spine_projection
      (body_category field_index : nat) (field : TypedField)
      : option TaggedReconstructionMachine.CanonicalSpineField :=
    match field with
    | TypedChild reference =>
        Some (TaggedReconstructionMachine.CanonicalChild
          body_category reference)
    | TypedOptional reference =>
        Some (TaggedReconstructionMachine.CanonicalOptional
          body_category field_index reference)
    | TypedScope domain arity body =>
        if Nat.eqb arity 1 then
          Some (TaggedReconstructionMachine.CanonicalBinder
            TaggedReconstructionMachine.SingleBinder domain arity body)
        else
          Some (TaggedReconstructionMachine.CanonicalBinder
            (TaggedReconstructionMachine.MultiBinder arity)
            domain arity body)
    | _ => None
    end.

  Theorem typed_node_round_trip_composes_with_spine :
    forall codecs layout typed canonical body_category field_index field spine,
      encode_typed_node codecs layout typed = Some canonical ->
      In field (typed_node_fields typed) ->
      typed_field_spine_projection body_category field_index field = Some spine ->
      decode_typed_node codecs layout canonical = Some typed /\
      TaggedReconstructionMachine.spine_decode spine
        (TaggedReconstructionMachine.spine_encode spine) = Some spine.
  Proof.
    intros codecs layout typed canonical body_category field_index field spine
      Hencode Hin Hspine.
    split.
    - now eapply typed_node_round_trip.
    - apply TaggedReconstructionMachine.spine_decode_encode.
  Qed.

  Theorem declared_scope_body_category_routes_exactly : forall category,
      TaggedReconstructionMachine.binder_body_route_valid category category = true.
  Proof.
    apply TaggedReconstructionMachine.declared_binder_body_route_is_valid.
  Qed.

  Theorem canonical_node_round_trip :
    forall codecs layout canonical typed,
      decode_typed_node codecs layout canonical = Some typed ->
      encode_typed_node codecs layout typed = Some canonical.
  Proof.
    intros codecs layout [op fields] typed Hdecode.
    unfold decode_typed_node, reconstruct_typed_node in Hdecode. cbn in Hdecode.
    destruct (reconstruct_typed_op codecs (adapter_operator layout) (decode_op op))
      as [typed_op_value |] eqn:Hop; try discriminate.
    destruct (decode_typed_fields codecs (adapter_fields layout) fields)
      as [typed_fields |] eqn:Hfields; try discriminate.
    inversion Hdecode; subst. unfold encode_typed_node, adapt_typed_node. cbn.
    rewrite (@adapt_reconstruct_typed_op codecs (adapter_operator layout)
      (decode_op op) typed_op_value Hop),
      (@encode_decode_typed_fields codecs (adapter_fields layout)
        fields typed_fields Hfields). cbn.
    destruct op. reflexivity.
  Qed.

  (** Exact legacy ContentKey input is preserved before hashing.  This is
      stronger than equality of a digest: a backend receives the same stable
      operator observation and the same structural field sequence. *)
  Theorem exact_legacy_key_input_preserved :
    forall codecs layout typed legacy,
      adapt_typed_node codecs layout typed = Some legacy ->
      core_arena_key_input [encode_node legacy] =
      legacy_arena_key_input [legacy].
  Proof.
    intros.
    change
      (core_arena_key_input (encode_arena [legacy]) =
       legacy_arena_key_input [legacy]).
    apply exact_semantic_key_input_preserved.
  Qed.

  (** A payload projection accounts for old generated operators whose exact key
      included bytes derived from a structural field.  The two naturality laws
      require the typed and canonical views to agree in both directions. *)
  Record FieldPayloadCodec : Type := field_payload_codec {
    typed_payload_bytes : TypedField -> option (list nat);
    canonical_payload_bytes : Field -> option (list nat);
    payload_encode_natural : forall codecs layout typed canonical bytes,
      encode_typed_field codecs layout typed = Some canonical ->
      typed_payload_bytes typed = Some bytes ->
      canonical_payload_bytes canonical = Some bytes;
    payload_decode_natural : forall codecs layout typed canonical bytes,
      decode_typed_field codecs layout canonical = Some typed ->
      canonical_payload_bytes canonical = Some bytes ->
      typed_payload_bytes typed = Some bytes
  }.

  Record PayloadSelection : Type := payload_selection {
    payload_field_index : nat;
    payload_field_codec : FieldPayloadCodec
  }.

  Definition typed_selected_payload
      (selection : PayloadSelection) (fields : list TypedField)
      : option (list nat) :=
    match nth_error fields (payload_field_index selection) with
    | Some field => typed_payload_bytes (payload_field_codec selection) field
    | None => None
    end.

  Definition canonical_selected_payload
      (selection : PayloadSelection) (fields : list Field)
      : option (list nat) :=
    match nth_error fields (payload_field_index selection) with
    | Some field => canonical_payload_bytes (payload_field_codec selection) field
    | None => None
    end.

  Lemma encoded_fields_preserve_nth :
    forall codecs layouts typed canonical index layout field value,
      encode_typed_fields codecs layouts typed = Some canonical ->
      nth_error layouts index = Some layout ->
      nth_error typed index = Some value ->
      nth_error canonical index = Some field ->
      encode_typed_field codecs layout value = Some field.
  Proof.
    intros codecs layouts. induction layouts as [|head_layout tail_layout IH];
      intros typed canonical index layout field value Hencode Hlayout Htyped Hcanonical.
    - destruct typed as [|head_value tail_value].
      + cbn in Hencode. inversion Hencode; subst.
        destruct index; inversion Hlayout.
      + cbn in Hencode. discriminate.
    - destruct typed as [|head_value tail_value]; cbn in Hencode; try discriminate.
      destruct (encode_typed_field codecs head_layout head_value)
        as [head_field |] eqn:Hhead; try discriminate.
      destruct (encode_typed_fields codecs tail_layout tail_value)
        as [tail_fields |] eqn:Htail; try discriminate.
      inversion Hencode; subst. destruct index as [|index]; cbn in *.
      + inversion Hlayout; inversion Htyped; inversion Hcanonical; subst. exact Hhead.
      + eapply IH; eauto.
  Qed.

  Lemma encoded_fields_layout_nth_exists :
    forall codecs layouts typed canonical index value,
      encode_typed_fields codecs layouts typed = Some canonical ->
      nth_error typed index = Some value ->
      exists layout, nth_error layouts index = Some layout.
  Proof.
    intros codecs layouts. induction layouts as [|head_layout tail_layout IH];
      intros typed canonical index value Hencode Htyped.
    - destruct typed.
      + destruct index; inversion Htyped.
      + cbn in Hencode. inversion Hencode.
    - destruct typed as [|head_value tail_value]; cbn in Hencode; try discriminate.
      destruct (encode_typed_field codecs head_layout head_value)
        as [head_field |] eqn:Hhead; try discriminate.
      destruct (encode_typed_fields codecs tail_layout tail_value)
        as [tail_fields |] eqn:Htail; try discriminate.
      inversion Hencode; subst. destruct index as [|index]; cbn in Htyped.
      + exists head_layout. reflexivity.
      + eapply IH; eauto.
  Qed.

  Lemma encoded_fields_canonical_nth_exists :
    forall codecs layouts typed canonical index value,
      encode_typed_fields codecs layouts typed = Some canonical ->
      nth_error typed index = Some value ->
      exists field, nth_error canonical index = Some field.
  Proof.
    intros codecs layouts. induction layouts as [|head_layout tail_layout IH];
      intros typed canonical index value Hencode Htyped.
    - destruct typed.
      + destruct index; inversion Htyped.
      + cbn in Hencode. inversion Hencode.
    - destruct typed as [|head_value tail_value]; cbn in Hencode; try discriminate.
      destruct (encode_typed_field codecs head_layout head_value)
        as [head_field |] eqn:Hhead; try discriminate.
      destruct (encode_typed_fields codecs tail_layout tail_value)
        as [tail_fields |] eqn:Htail; try discriminate.
      inversion Hencode; subst. destruct index as [|index]; cbn in Htyped.
      + exists head_field. reflexivity.
      + destruct (IH tail_value tail_fields index value Htail Htyped)
          as [field Hfield].
        exists field. exact Hfield.
  Qed.

  Lemma encoded_fields_typed_nth_exists :
    forall codecs layouts typed canonical index field,
      encode_typed_fields codecs layouts typed = Some canonical ->
      nth_error canonical index = Some field ->
      exists value, nth_error typed index = Some value.
  Proof.
    intros codecs layouts. induction layouts as [|head_layout tail_layout IH];
      intros typed canonical index field Hencode Hcanonical.
    - destruct typed as [|head_value tail_value].
      + cbn in Hencode. inversion Hencode; subst.
        destruct index; inversion Hcanonical.
      + cbn in Hencode. inversion Hencode.
    - destruct typed as [|head_value tail_value]; cbn in Hencode; try discriminate.
      destruct (encode_typed_field codecs head_layout head_value)
        as [head_field |] eqn:Hhead; try discriminate.
      destruct (encode_typed_fields codecs tail_layout tail_value)
        as [tail_fields |] eqn:Htail; try discriminate.
      inversion Hencode; subst. destruct index as [|index]; cbn in Hcanonical.
      + exists head_value. reflexivity.
      + destruct (IH tail_value tail_fields index field Htail Hcanonical)
          as [value Hvalue].
        exists value. exact Hvalue.
  Qed.

  Theorem selected_payload_projection_is_exact :
    forall codecs layouts typed canonical selection bytes,
      encode_typed_fields codecs layouts typed = Some canonical ->
      typed_selected_payload selection typed = Some bytes ->
      canonical_selected_payload selection canonical = Some bytes.
  Proof.
    intros codecs layouts typed canonical [index payload_codec] bytes
      Hencode Htyped_payload.
    unfold typed_selected_payload, canonical_selected_payload in *; cbn in *.
    destruct (nth_error typed index) as [typed_field |] eqn:Htyped;
      try discriminate.
    destruct (@encoded_fields_layout_nth_exists codecs layouts typed canonical
      index typed_field Hencode Htyped) as [layout Hlayout].
    destruct (@encoded_fields_canonical_nth_exists codecs layouts typed canonical
      index typed_field Hencode Htyped) as [canonical_field Hcanonical].
    rewrite Hcanonical.
    eapply payload_encode_natural; eauto.
    eapply encoded_fields_preserve_nth; eauto.
  Qed.

  Theorem selected_payload_projection_is_reflected :
    forall codecs layouts typed canonical selection bytes,
      encode_typed_fields codecs layouts typed = Some canonical ->
      canonical_selected_payload selection canonical = Some bytes ->
      typed_selected_payload selection typed = Some bytes.
  Proof.
    intros codecs layouts typed canonical [index payload_codec] bytes
      Hencode Hcanonical_payload.
    unfold typed_selected_payload, canonical_selected_payload in *; cbn in *.
    destruct (nth_error canonical index) as [canonical_field |] eqn:Hcanonical;
      try discriminate.
    destruct (@encoded_fields_typed_nth_exists codecs layouts typed canonical
      index canonical_field Hencode Hcanonical) as [typed_field Htyped].
    destruct (@encoded_fields_layout_nth_exists codecs layouts typed canonical
      index typed_field Hencode Htyped) as [layout Hlayout].
    rewrite Htyped.
    eapply payload_decode_natural; eauto.
    apply decode_encode_typed_field.
    eapply encoded_fields_preserve_nth; eauto.
  Qed.

  (** [compile_node_with_payload] is the semantic-machine projection with an
      exact redundant coefficient appended after the canonical operator
      payload.  Field nodes remain the reconstruction authority. *)
  Definition project_main_with_payload
      (template : MachineOp) (op : CoreOp) (payload : list nat) : MachineOp :=
    instantiate template (encode_optional_scalar (core_payload op) ++ payload).

  Definition compile_node_with_payload
      (base : nat) (table : ProjectionTable) (value : Node CoreOp)
      (payload : list nat) : option (list MachineNode * nat)%type :=
    if Nat.eqb
         (machine_discriminant (projection_main_template table))
         (core_discriminant (node_op value)) then
      match compile_fields base (projection_fields table) (node_fields value) with
      | None => None
      | Some (field_nodes, children) =>
          let root := base + length field_nodes in
          Some (
            field_nodes ++
              [machine_node
                (project_main_with_payload
                  (projection_main_template table) (node_op value) payload)
                children
                (projection_canonicalize table)],
            root)
      end
    else None.

  Definition fused_static_projection
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (selection : PayloadSelection) (base : nat) (table : ProjectionTable)
      (typed : TypedNode) : option (list MachineNode * nat)%type :=
    match encode_typed_node codecs layout typed,
          typed_selected_payload selection (typed_node_fields typed) with
    | Some canonical, Some payload =>
        compile_node_with_payload base table canonical payload
    | _, _ => None
    end.

  Definition materialized_static_projection
      (codecs : CodecEnvironment) (layout : SemanticAdapterLayout)
      (selection : PayloadSelection) (base : nat) (table : ProjectionTable)
      (typed : TypedNode) : option (list MachineNode * nat)%type :=
    match encode_typed_node codecs layout typed with
    | Some canonical =>
        match canonical_selected_payload selection (node_fields canonical) with
        | Some payload => compile_node_with_payload base table canonical payload
        | None => None
        end
    | None => None
    end.

  Theorem fused_static_projection_is_deforestation :
    forall codecs layout selection base table typed,
      fused_static_projection codecs layout selection base table typed =
      materialized_static_projection codecs layout selection base table typed.
  Proof.
    intros codecs layout selection base table [op fields].
    unfold fused_static_projection, materialized_static_projection,
      encode_typed_node, adapt_typed_node. cbn.
    destruct (adapt_typed_op codecs (adapter_operator layout) op)
      as [legacy_op_value |] eqn:Hop; cbn; try reflexivity.
    destruct (encode_typed_fields codecs (adapter_fields layout) fields)
      as [canonical_fields |] eqn:Hfields; cbn; try reflexivity.
    destruct (typed_selected_payload selection fields)
      as [payload |] eqn:Hpayload; cbn.
    - rewrite (@selected_payload_projection_is_exact codecs
        (adapter_fields layout) fields canonical_fields selection payload
        Hfields Hpayload).
      reflexivity.
    - destruct (canonical_selected_payload selection canonical_fields)
        as [canonical_payload |] eqn:Hcanonical_payload; try reflexivity.
      pose proof (@selected_payload_projection_is_reflected codecs
        (adapter_fields layout) fields canonical_fields selection canonical_payload
        Hfields Hcanonical_payload) as Hreflected.
      rewrite Hpayload in Hreflected. discriminate.
  Qed.

  Definition AdapterWorkItem : Type :=
    (SemanticAdapterLayout * TypedNode)%type.

  Inductive AdapterRunResult : Type :=
  | AdapterFailed : AdapterRunResult
  | AdapterDone : list (Node CoreOp) -> AdapterRunResult
  | AdapterPending : list AdapterWorkItem -> list (Node CoreOp) -> AdapterRunResult.

  Fixpoint adapter_run
      (fuel : nat) (codecs : CodecEnvironment)
      (pending : list AdapterWorkItem) (emitted_rev : list (Node CoreOp))
      : AdapterRunResult :=
    match fuel, pending with
    | 0, [] => AdapterDone (rev emitted_rev)
    | 0, _ => AdapterPending pending emitted_rev
    | S _, [] => AdapterDone (rev emitted_rev)
    | S remaining, (layout, value) :: rest =>
        match encode_typed_node codecs layout value with
        | Some canonical => adapter_run remaining codecs rest (canonical :: emitted_rev)
        | None => AdapterFailed
        end
    end.

  Fixpoint materialize_adapter_items
      (codecs : CodecEnvironment) (pending : list AdapterWorkItem)
      : option (list (Node CoreOp)) :=
    match pending with
    | [] => Some []
    | (layout, value) :: rest =>
        match encode_typed_node codecs layout value,
              materialize_adapter_items codecs rest with
        | Some canonical, Some later => Some (canonical :: later)
        | _, _ => None
        end
    end.

  Lemma adapter_run_materialized_accumulator :
    forall codecs pending canonical emitted_rev,
      materialize_adapter_items codecs pending = Some canonical ->
      adapter_run (length pending) codecs pending emitted_rev =
      AdapterDone (rev emitted_rev ++ canonical).
  Proof.
    intros codecs pending. induction pending as [|[layout value] rest IH];
      intros canonical emitted_rev Hmaterialize.
    - inversion Hmaterialize; subst. cbn. now rewrite app_nil_r.
    - cbn in Hmaterialize.
      destruct (encode_typed_node codecs layout value)
        as [head |] eqn:Hhead; try discriminate.
      destruct (materialize_adapter_items codecs rest)
        as [tail |] eqn:Htail; try discriminate.
      inversion Hmaterialize; subst. cbn. rewrite Hhead.
      rewrite (IH tail (head :: emitted_rev) eq_refl).
      f_equal. cbn. now rewrite <- app_assoc.
  Qed.

  Theorem adapter_run_equals_materialization :
    forall codecs pending canonical,
      materialize_adapter_items codecs pending = Some canonical ->
      adapter_run (length pending) codecs pending [] = AdapterDone canonical.
  Proof.
    intros codecs pending canonical Hmaterialize.
    rewrite (@adapter_run_materialized_accumulator codecs pending canonical []
      Hmaterialize).
    reflexivity.
  Qed.

  Definition adapter_transition_consumption (pending : list AdapterWorkItem) : nat :=
    match pending with [] => 0 | _ :: _ => 1 end.

  Theorem adapter_transition_consumes_at_most_one_node :
    forall pending, adapter_transition_consumption pending <= 1.
  Proof. intros [|item rest]; simpl; auto. Qed.

  (** Existing pattern, substitution, native-transition, and report theorems are
      inherited after successful typed adaptation.  These corollaries make the
      factorisation explicit at the new seam. *)
  Theorem adapted_pattern_observation_is_preserved :
    forall pattern legacy,
      legacy_pattern_matches_node pattern legacy <->
      core_pattern_matches_node (encode_pattern_atom pattern) (encode_node legacy).
  Proof. apply positional_and_ac_pattern_observation_preserved. Qed.

  Theorem adapted_instantiation_is_preserved :
    forall pattern sigma,
      core_instantiate (encode_pattern_atom pattern) sigma =
      legacy_instantiate pattern sigma.
  Proof. apply structural_instantiation_preserved. Qed.

  Theorem adapted_native_transition_is_natural :
    forall evaluate inputs,
      option_map encode_op (typed_native_evaluate evaluate inputs) =
      evaluate (map encode_op inputs).
  Proof. apply native_transition_naturality. Qed.

  Theorem adapted_report_observation_is_preserved :
    forall report_value,
      core_report_observation (encode_report report_value) =
      legacy_report_observation report_value.
  Proof. apply report_observation_preserved. Qed.

  (** Backend-only structural leaves occupy one checked suffix of the legacy
      operator discriminant space.  Their identity and discriminant are stored
      together: emitters may project this table, but may not independently
      reconstruct its ordering. *)
  Inductive SentinelIdentity : Type :=
  | SentinelBinderArity
  | SentinelFieldNone
  | SentinelFieldOpaque
  | SentinelFieldTokenText
  | SentinelFieldSequence (element_category : nat)
  | SentinelCollectionPair (collection_kind element_category : nat)
  | SentinelPathMapMode (key_category value_category : nat)
  | SentinelPathMapPair (key_category value_category : nat)
  | SentinelFieldWithheld (category : nat)
  | SentinelFieldVariable (category : nat).

  Definition pathmap_mode_tag (mode : PathMapMode) : nat :=
    match mode with
    | PathMapNeutralEmpty => 0
    | PathMapSetMode => 1
    | PathMapMapMode => 2
    end.

  Definition pathmap_mode_template
      (key_category value_category : nat) (mode : PathMapMode)
      : SentinelIdentity * list nat :=
    (SentinelPathMapMode key_category value_category, [pathmap_mode_tag mode]).

  Record SentinelLayout : Type := sentinel_layout {
    sentinel_base : nat;
    sentinel_identities : list SentinelIdentity
  }.

  Definition sentinel_at
      (layout : SentinelLayout) (index : nat)
      : option (SentinelIdentity * nat) :=
    match nth_error (sentinel_identities layout) index with
    | Some identity => Some (identity, sentinel_base layout + index)
    | None => None
    end.

  Definition sentinel_end (layout : SentinelLayout) : nat :=
    sentinel_base layout + length (sentinel_identities layout).

  (** A map-like collection pair leaf is indexed by both the collection kind
      and its homogeneous element category.  Consequently two incompatible
      pair roles cannot be assigned the same structural identity even when
      their surface labels happen to agree. *)
  Theorem collection_pair_sentinel_identity_is_injective :
    forall left_kind left_category right_kind right_category,
      SentinelCollectionPair left_kind left_category =
      SentinelCollectionPair right_kind right_category ->
      left_kind = right_kind /\ left_category = right_category.
  Proof.
    intros left_kind left_category right_kind right_category Hequal.
    now inversion Hequal.
  Qed.

  Theorem pathmap_mode_sentinel_identity_is_injective :
    forall left_key left_value right_key right_value,
      SentinelPathMapMode left_key left_value =
      SentinelPathMapMode right_key right_value ->
      left_key = right_key /\ left_value = right_value.
  Proof.
    intros left_key left_value right_key right_value Hequal.
    now inversion Hequal.
  Qed.

  Theorem pathmap_pair_sentinel_identity_is_injective :
    forall left_key left_value right_key right_value,
      SentinelPathMapPair left_key left_value =
      SentinelPathMapPair right_key right_value ->
      left_key = right_key /\ left_value = right_value.
  Proof.
    intros left_key left_value right_key right_value Hequal.
    now inversion Hequal.
  Qed.

  Theorem pathmap_mode_tag_is_injective :
    forall left right,
      pathmap_mode_tag left = pathmap_mode_tag right -> left = right.
  Proof.
    intros left right Hequal.
    destruct left, right; cbn in Hequal; try discriminate; reflexivity.
  Qed.

  Theorem pathmap_mode_tags_are_pairwise_distinct :
    pathmap_mode_tag PathMapNeutralEmpty <> pathmap_mode_tag PathMapSetMode /\
    pathmap_mode_tag PathMapNeutralEmpty <> pathmap_mode_tag PathMapMapMode /\
    pathmap_mode_tag PathMapSetMode <> pathmap_mode_tag PathMapMapMode.
  Proof. cbn. lia. Qed.

  Theorem pathmap_mode_template_is_injective :
    forall left_key left_value left_mode right_key right_value right_mode,
      pathmap_mode_template left_key left_value left_mode =
      pathmap_mode_template right_key right_value right_mode ->
      left_key = right_key /\ left_value = right_value /\ left_mode = right_mode.
  Proof.
    intros left_key left_value left_mode right_key right_value right_mode Hequal.
    destruct left_mode, right_mode; unfold pathmap_mode_template in Hequal;
      cbn in Hequal; inversion Hequal; subst; try discriminate;
      repeat split; reflexivity.
  Qed.

  Theorem stored_sentinel_identity_and_discriminant_are_exact :
    forall layout index identity,
      nth_error (sentinel_identities layout) index = Some identity ->
      sentinel_at layout index =
        Some (identity, sentinel_base layout + index).
  Proof.
    intros layout index identity Hidentity.
    unfold sentinel_at. now rewrite Hidentity.
  Qed.

  Theorem constructor_and_sentinel_discriminants_are_disjoint :
    forall layout constructor_discriminant index identity,
      constructor_discriminant < sentinel_base layout ->
      sentinel_at layout index = Some (identity, sentinel_base layout + index) ->
      constructor_discriminant <> sentinel_base layout + index.
  Proof.
    intros layout constructor_discriminant index identity Hconstructor _ Hequal.
    subst constructor_discriminant. lia.
  Qed.

  Theorem sentinel_discriminants_are_injective :
    forall layout left_index right_index left_identity right_identity discriminant,
      sentinel_at layout left_index = Some (left_identity, discriminant) ->
      sentinel_at layout right_index = Some (right_identity, discriminant) ->
      left_index = right_index.
  Proof.
    intros [base identities] left_index right_index
      left_identity right_identity discriminant Hleft Hright.
    unfold sentinel_at in *. cbn in *.
    destruct (nth_error identities left_index) as [left |] eqn:Hleft_identity;
      try discriminate.
    destruct (nth_error identities right_index) as [right |] eqn:Hright_identity;
      try discriminate.
    inversion Hleft; inversion Hright; subst. lia.
  Qed.

  Theorem sentinel_discriminant_is_within_reserved_suffix :
    forall layout index identity discriminant,
      sentinel_at layout index = Some (identity, discriminant) ->
      sentinel_base layout <= discriminant < sentinel_end layout.
  Proof.
    intros [base identities] index identity discriminant Hlookup.
    unfold sentinel_at, sentinel_end in *. cbn in *.
    destruct (nth_error identities index) as [found |] eqn:Hidentity;
      try discriminate.
    inversion Hlookup; subst.
    assert (Hsome : nth_error identities index <> None).
    { rewrite Hidentity. discriminate. }
    apply nth_error_Some in Hsome.
    split; lia.
  Qed.

  Print Assumptions decode_encode_typed_field.
  Print Assumptions encode_decode_typed_field.
  Print Assumptions missing_opaque_codec_fails_closed.
  Print Assumptions collection_pair_boundaries_are_preserved.
  Print Assumptions display_only_collection_key_is_not_exact.
  Print Assumptions encoded_collection_field_is_injective.
  Print Assumptions raw_backend_ids_are_not_representation_independent.
  Print Assumptions fused_assembly_erases_transient_backend_ids.
  Print Assumptions ordered_fused_assembly_preserves_child_order.
  Print Assumptions unordered_fused_assembly_is_permutation_invariant.
  Print Assumptions unordered_fused_assembly_distinguishes_nonpermutations.
  Print Assumptions fused_pair_key_preserves_key_value_boundary.
  Print Assumptions fused_pathmap_mode_is_injective.
  Print Assumptions fused_pathmap_entries_are_permutation_invariant.
  Print Assumptions decode_encode_native_carrier.
  Print Assumptions encode_decode_native_carrier.
  Print Assumptions zipper_focus_is_preserved.
  Print Assumptions zipper_pathmap_topology_is_injective.
  Print Assumptions native_carrier_transition_consumes_at_most_one_value.
  Print Assumptions semantic_key_abi_tag_is_injective.
  Print Assumptions versioned_semantic_key_is_injective.
  Print Assumptions semantic_key_abi_namespaces_are_disjoint.
  Print Assumptions colliding_legacy_key_cannot_be_preserved_by_exact_migration.
  Print Assumptions encoded_pathmap_field_is_injective.
  Print Assumptions empty_pathmap_modes_have_distinct_structural_keys.
  Print Assumptions optional_sequence_presence_is_preserved.
  Print Assumptions optional_token_presence_is_preserved.
  Print Assumptions scope_domain_arity_and_body_are_preserved.
  Print Assumptions reconstruct_adapt_typed_op.
  Print Assumptions adapt_reconstruct_typed_op.
  Print Assumptions typed_node_round_trip.
  Print Assumptions typed_node_round_trip_composes_with_spine.
  Print Assumptions declared_scope_body_category_routes_exactly.
  Print Assumptions canonical_node_round_trip.
  Print Assumptions exact_legacy_key_input_preserved.
  Print Assumptions selected_payload_projection_is_exact.
  Print Assumptions selected_payload_projection_is_reflected.
  Print Assumptions fused_static_projection_is_deforestation.
  Print Assumptions adapter_run_equals_materialization.
  Print Assumptions adapter_transition_consumes_at_most_one_node.
  Print Assumptions adapted_pattern_observation_is_preserved.
  Print Assumptions adapted_instantiation_is_preserved.
  Print Assumptions adapted_native_transition_is_natural.
  Print Assumptions adapted_report_observation_is_preserved.
  Print Assumptions stored_sentinel_identity_and_discriminant_are_exact.
  Print Assumptions collection_pair_sentinel_identity_is_injective.
  Print Assumptions pathmap_mode_sentinel_identity_is_injective.
  Print Assumptions pathmap_pair_sentinel_identity_is_injective.
  Print Assumptions pathmap_mode_tag_is_injective.
  Print Assumptions pathmap_mode_tags_are_pairwise_distinct.
  Print Assumptions pathmap_mode_template_is_injective.
  Print Assumptions constructor_and_sentinel_discriminants_are_disjoint.
  Print Assumptions sentinel_discriminants_are_injective.
  Print Assumptions sentinel_discriminant_is_within_reserved_suffix.

End GeneratedSemanticAdapter.
