From Stdlib Require Import Bool PeanoNat Lia List.
Import ListNotations.

(** The structural Rholang ABI contains fixed framing lists and strings around
    two independently recursive sections: the DDL syntax tree and opaque
    canonical values carried by [Data(v)].  Framing consumes resources, but it
    is not a recursive constructor of either semantic section. *)
Inductive WireSection : Type :=
| DdlStructure
| CanonicalData.

Record SectionedDepthBudget : Type := {
  ddl_depth_limit : nat;
  data_depth_limit : nat
}.

Record DepthObservation : Type := {
  observed_section : WireSection;
  observed_depth : nat
}.

Definition observation_withinb
    (budget : SectionedDepthBudget) (observation : DepthObservation) : bool :=
  match observed_section observation with
  | DdlStructure => Nat.leb (observed_depth observation) (ddl_depth_limit budget)
  | CanonicalData => Nat.leb (observed_depth observation) (data_depth_limit budget)
  end.

Definition observation_within
    (budget : SectionedDepthBudget) (observation : DepthObservation) : Prop :=
  match observed_section observation with
  | DdlStructure => observed_depth observation <= ddl_depth_limit budget
  | CanonicalData => observed_depth observation <= data_depth_limit budget
  end.

(** This structurally recursive list function is the logical counterpart of
    the Rust decoder's explicit worklist loop. *)
Fixpoint admit_depth_worklist
    (budget : SectionedDepthBudget) (work : list DepthObservation) : bool :=
  match work with
  | [] => true
  | observation :: rest =>
      observation_withinb budget observation && admit_depth_worklist budget rest
  end.

Lemma observation_withinb_sound :
  forall budget observation,
    observation_withinb budget observation = true ->
    observation_within budget observation.
Proof.
  intros budget [section depth].
  destruct section; simpl; apply Nat.leb_le.
Qed.

Theorem iterative_depth_admission_is_sound :
  forall budget work,
    admit_depth_worklist budget work = true ->
    Forall (observation_within budget) work.
Proof.
  intros budget work.
  induction work as [| observation rest IH]; intros Hadmitted.
  - constructor.
  - simpl in Hadmitted.
    rewrite andb_true_iff in Hadmitted.
    destruct Hadmitted as [Hobservation Hrest].
    constructor.
    + apply observation_withinb_sound. exact Hobservation.
    + apply IH. exact Hrest.
Qed.

Record WireResourceUsage : Type := {
  wire_nodes : nat;
  wire_collection_items : nat;
  wire_string_bytes : nat;
  wire_byte_array_bytes : nat
}.

Definition add_wire_usage
    (left right : WireResourceUsage) : WireResourceUsage :=
  {| wire_nodes := wire_nodes left + wire_nodes right;
     wire_collection_items :=
       wire_collection_items left + wire_collection_items right;
     wire_string_bytes := wire_string_bytes left + wire_string_bytes right;
     wire_byte_array_bytes :=
       wire_byte_array_bytes left + wire_byte_array_bytes right |}.

Definition wire_usage_withinb
    (usage limit : WireResourceUsage) : bool :=
  Nat.leb (wire_nodes usage) (wire_nodes limit) &&
  Nat.leb (wire_collection_items usage) (wire_collection_items limit) &&
  Nat.leb (wire_string_bytes usage) (wire_string_bytes limit) &&
  Nat.leb (wire_byte_array_bytes usage) (wire_byte_array_bytes limit).

Definition wire_usage_within
    (usage limit : WireResourceUsage) : Prop :=
  wire_nodes usage <= wire_nodes limit /\
  wire_collection_items usage <= wire_collection_items limit /\
  wire_string_bytes usage <= wire_string_bytes limit /\
  wire_byte_array_bytes usage <= wire_byte_array_bytes limit.

Lemma wire_usage_withinb_sound :
  forall usage limit,
    wire_usage_withinb usage limit = true ->
    wire_usage_within usage limit.
Proof.
  intros usage limit Hadmitted.
  unfold wire_usage_withinb in Hadmitted.
  repeat rewrite andb_true_iff in Hadmitted.
  destruct Hadmitted as [[[Hnodes Hitems] Hstrings] Hbytes].
  unfold wire_usage_within.
  repeat split; apply Nat.leb_le; assumption.
Qed.

Record WireEnvelope : Type := {
  framing_usage : WireResourceUsage;
  payload_usage : WireResourceUsage;
  ddl_max_depth : nat;
  data_max_depths : list nat
}.

Definition semantic_observations (envelope : WireEnvelope)
    : list DepthObservation :=
  {| observed_section := DdlStructure;
     observed_depth := ddl_max_depth envelope |}
  :: map
       (fun depth =>
          {| observed_section := CanonicalData;
             observed_depth := depth |})
       (data_max_depths envelope).

Definition admit_wire_envelope
    (depth_budget : SectionedDepthBudget)
    (resource_limit : WireResourceUsage)
    (envelope : WireEnvelope) : bool :=
  wire_usage_withinb
    (add_wire_usage (framing_usage envelope) (payload_usage envelope))
    resource_limit &&
  admit_depth_worklist depth_budget (semantic_observations envelope).

Theorem admitted_wire_covers_framing_and_payload_resources :
  forall depth_budget resource_limit envelope,
    admit_wire_envelope depth_budget resource_limit envelope = true ->
    wire_usage_within
      (add_wire_usage (framing_usage envelope) (payload_usage envelope))
      resource_limit.
Proof.
  intros depth_budget resource_limit envelope Hadmitted.
  unfold admit_wire_envelope in Hadmitted.
  rewrite andb_true_iff in Hadmitted.
  destruct Hadmitted as [Hresources _].
  apply wire_usage_withinb_sound. exact Hresources.
Qed.

Theorem admitted_wire_covers_every_semantic_section :
  forall depth_budget resource_limit envelope,
    admit_wire_envelope depth_budget resource_limit envelope = true ->
    Forall
      (observation_within depth_budget)
      (semantic_observations envelope).
Proof.
  intros depth_budget resource_limit envelope Hadmitted.
  unfold admit_wire_envelope in Hadmitted.
  rewrite andb_true_iff in Hadmitted.
  destruct Hadmitted as [_ Hdepth].
  apply iterative_depth_admission_is_sound. exact Hdepth.
Qed.

Lemma mapped_data_depths_at_limit_are_admitted :
  forall count limit,
    admit_depth_worklist
      {| ddl_depth_limit := limit; data_depth_limit := limit |}
      (map
         (fun depth =>
            {| observed_section := CanonicalData; observed_depth := depth |})
         (repeat limit count)) = true.
Proof.
  intros count limit.
  induction count as [| count IH].
  - reflexivity.
  - cbn [repeat map admit_depth_worklist].
    apply andb_true_iff. split.
    + unfold observation_withinb. simpl. apply Nat.leb_refl.
    + exact IH.
Qed.

(** Fixed ABI framing does not spend semantic depth.  In particular, both a
    DDL syntax tree and every [Data(v)] payload may reach the exact shared
    semantic bound regardless of how many already-resource-charged framing
    nodes surround them. *)
Theorem exact_section_depth_limits_are_not_reduced_by_framing :
  forall framing payload count limit,
    admit_depth_worklist
      {| ddl_depth_limit := limit; data_depth_limit := limit |}
      (semantic_observations
         {| framing_usage := framing;
            payload_usage := payload;
            ddl_max_depth := limit;
            data_max_depths := repeat limit count |}) = true.
Proof.
  intros framing payload count limit.
  unfold semantic_observations. cbn [admit_depth_worklist].
  apply andb_true_iff. split.
  - unfold observation_withinb. simpl. apply Nat.leb_refl.
  - apply mapped_data_depths_at_limit_are_admitted.
Qed.

(** Canonical data is transported through ordinary Rholang literal syntax
    before it reaches the structural wire decoder.  Empty braces deliberately
    retain both of Rholang's historical readings: an empty map and the empty
    parallel process (whose canonical data observation is [Nil]).  Therefore a
    canonical renderer must use the unambiguous [Map()] constructor for an
    empty map. *)
Inductive CanonicalLiteralValue : Type :=
| LiteralNil
| LiteralEmptyMap
| LiteralEmptyPathMap
| LiteralNonEmptyMap.

Inductive CanonicalLiteralSurface : Type :=
| SurfaceNil
| SurfaceEmptyBraces
| SurfaceMapConstructor
| SurfacePathMapConstructor
| SurfaceNonEmptyMap.

Inductive literal_surface_parses_as
    : CanonicalLiteralSurface -> CanonicalLiteralValue -> Prop :=
| parse_surface_nil :
    literal_surface_parses_as SurfaceNil LiteralNil
| parse_empty_braces_as_map :
    literal_surface_parses_as SurfaceEmptyBraces LiteralEmptyMap
| parse_empty_braces_as_parallel_zero :
    literal_surface_parses_as SurfaceEmptyBraces LiteralNil
| parse_map_constructor :
    literal_surface_parses_as SurfaceMapConstructor LiteralEmptyMap
| parse_pathmap_constructor :
    literal_surface_parses_as SurfacePathMapConstructor LiteralEmptyPathMap
| parse_nonempty_map :
    literal_surface_parses_as SurfaceNonEmptyMap LiteralNonEmptyMap.

Definition render_canonical_literal
    (value : CanonicalLiteralValue) : CanonicalLiteralSurface :=
  match value with
  | LiteralNil => SurfaceNil
  | LiteralEmptyMap => SurfaceMapConstructor
  | LiteralEmptyPathMap => SurfacePathMapConstructor
  | LiteralNonEmptyMap => SurfaceNonEmptyMap
  end.

Theorem empty_braces_do_not_identify_a_canonical_value :
  literal_surface_parses_as SurfaceEmptyBraces LiteralEmptyMap /\
  literal_surface_parses_as SurfaceEmptyBraces LiteralNil.
Proof.
  split.
  - apply parse_empty_braces_as_map.
  - apply parse_empty_braces_as_parallel_zero.
Qed.

Theorem rendered_canonical_literal_is_unambiguous :
  forall value decoded,
    literal_surface_parses_as (render_canonical_literal value) decoded <->
    decoded = value.
Proof.
  intros value decoded.
  destruct value; split; intro H.
  - inversion H. reflexivity.
  - subst decoded. apply parse_surface_nil.
  - inversion H. reflexivity.
  - subst decoded. apply parse_map_constructor.
  - inversion H. reflexivity.
  - subst decoded. apply parse_pathmap_constructor.
  - inversion H. reflexivity.
  - subst decoded. apply parse_nonempty_map.
Qed.

(** The remaining non-structural carriers whose canonical spellings have an
    explicit frame must retain both their kind and their payload.  In
    particular, byte arrays are not strings, and an integer rendered with the
    [n] frame is not lexed as an integer followed by an identifier.  Payloads
    are abstract here: the executable hexadecimal and decimal transducers are
    checked against this relation by the codec conformance tests. *)
Inductive CanonicalFramedAtom : Type :=
| LiteralBytes (payload : list nat)
| LiteralWideInteger (magnitude : nat) (negative : bool).

Inductive CanonicalFramedSurface : Type :=
| SurfaceByteArray (payload : list nat)
| SurfaceBigInteger (magnitude : nat) (negative : bool)
| SurfaceUnframedString (payload : list nat)
| SurfaceIntegerThenIdentifier (magnitude : nat) (negative : bool).

Inductive framed_surface_parses_as
    : CanonicalFramedSurface -> CanonicalFramedAtom -> Prop :=
| parse_byte_array_frame : forall payload,
    framed_surface_parses_as
      (SurfaceByteArray payload)
      (LiteralBytes payload)
| parse_big_integer_frame : forall magnitude negative,
    framed_surface_parses_as
      (SurfaceBigInteger magnitude negative)
      (LiteralWideInteger magnitude negative).

Definition render_canonical_framed_atom
    (value : CanonicalFramedAtom) : CanonicalFramedSurface :=
  match value with
  | LiteralBytes payload => SurfaceByteArray payload
  | LiteralWideInteger magnitude negative =>
      SurfaceBigInteger magnitude negative
  end.

Theorem rendered_framed_atom_is_kind_and_payload_preserving :
  forall value decoded,
    framed_surface_parses_as (render_canonical_framed_atom value) decoded <->
    decoded = value.
Proof.
  intros value decoded.
  destruct value; split; intro H.
  - inversion H. reflexivity.
  - subst decoded. apply parse_byte_array_frame.
  - inversion H. reflexivity.
  - subst decoded. apply parse_big_integer_frame.
Qed.

Theorem unframed_lookalikes_do_not_decode_as_framed_atoms :
  (forall payload decoded,
      ~ framed_surface_parses_as (SurfaceUnframedString payload) decoded) /\
  (forall magnitude negative decoded,
      ~ framed_surface_parses_as
          (SurfaceIntegerThenIdentifier magnitude negative)
          decoded).
Proof.
  split; intros; intro H; inversion H.
Qed.

Print Assumptions iterative_depth_admission_is_sound.
Print Assumptions admitted_wire_covers_framing_and_payload_resources.
Print Assumptions admitted_wire_covers_every_semantic_section.
Print Assumptions exact_section_depth_limits_are_not_reduced_by_framing.
Print Assumptions empty_braces_do_not_identify_a_canonical_value.
Print Assumptions rendered_canonical_literal_is_unambiguous.
Print Assumptions rendered_framed_atom_is_kind_and_payload_preserving.
Print Assumptions unframed_lookalikes_do_not_decode_as_framed_atoms.
