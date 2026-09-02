(**
  CollectionProjection: preservation of the GrammarCore key/value shape.

  The compile-time frontend and GrammarCore use different names for the same
  five collection kinds.  A projection is admissible exactly when map-like
  collections retain both a key category and the token that separates an
  optional/required value from its key.  In particular, PathMap permits a bare
  key semantically, but still retains its key/value separator so valued entries
  remain parseable.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Module CollectionProjection.

Inductive SourceKind : Type :=
| SourceBag
| SourceSet
| SourceList
| SourceMap
| SourcePathMap.

Inductive CoreKind : Type :=
| CoreBag
| CoreSet
| CoreList
| CoreMap
| CorePathMap.

Definition lower_kind (kind : SourceKind) : CoreKind :=
  match kind with
  | SourceBag => CoreBag
  | SourceSet => CoreSet
  | SourceList => CoreList
  | SourceMap => CoreMap
  | SourcePathMap => CorePathMap
  end.

Definition source_map_like (kind : SourceKind) : bool :=
  match kind with
  | SourceMap | SourcePathMap => true
  | _ => false
  end.

Definition core_map_like (kind : CoreKind) : bool :=
  match kind with
  | CoreMap | CorePathMap => true
  | _ => false
  end.

Theorem lowering_reflects_map_likeness :
  forall kind, core_map_like (lower_kind kind) = source_map_like kind.
Proof.
  intros []; reflexivity.
Qed.

Record SourceCollection := {
  source_kind : SourceKind;
  source_key_category : nat;
  source_value_category : nat;
  source_separator : nat
}.

Record CoreCollection := {
  core_kind : CoreKind;
  core_key_category : option nat;
  core_value_category : nat;
  core_separator : option nat
}.

Definition project_collection (source : SourceCollection) : CoreCollection :=
  if source_map_like (source_kind source) then
    {| core_kind := lower_kind (source_kind source);
       core_key_category := Some (source_key_category source);
       core_value_category := source_value_category source;
       core_separator := Some (source_separator source) |}
  else
    {| core_kind := lower_kind (source_kind source);
       core_key_category := None;
       core_value_category := source_value_category source;
       core_separator := None |}.

Definition option_present {A : Type} (value : option A) : bool :=
  match value with Some _ => true | None => false end.

Definition core_shape_valid (collection : CoreCollection) : bool :=
  Bool.eqb (core_map_like (core_kind collection))
           (option_present (core_key_category collection)) &&
  Bool.eqb (core_map_like (core_kind collection))
           (option_present (core_separator collection)).

Theorem projected_collection_satisfies_key_value_contract :
  forall source, core_shape_valid (project_collection source) = true.
Proof.
  intros [kind key value separator].
  destruct kind; reflexivity.
Qed.

Theorem map_projection_preserves_key_and_value_categories :
  forall key value separator,
    let projected := project_collection
      {| source_kind := SourceMap;
         source_key_category := key;
         source_value_category := value;
         source_separator := separator |} in
    core_key_category projected = Some key /\
    core_value_category projected = value.
Proof.
  intros; split; reflexivity.
Qed.

Theorem pathmap_projection_retains_separator_for_valued_entries :
  forall key value separator,
    core_separator (project_collection
      {| source_kind := SourcePathMap;
         source_key_category := key;
         source_value_category := value;
         source_separator := separator |}) = Some separator.
Proof.
  reflexivity.
Qed.

(** This is the former defective lowering: map-like source kinds collapsed to
    bags while the separator remained present. The GrammarCore validator must
    reject that contradictory shape. *)
Definition legacy_map_collapse (key value separator : nat) : CoreCollection :=
  {| core_kind := CoreBag;
     core_key_category := None;
     core_value_category := value;
     core_separator := Some separator |}.

Theorem legacy_map_collapse_violates_contract :
  forall key value separator,
    core_shape_valid (legacy_map_collapse key value separator) = false.
Proof.
  reflexivity.
Qed.

(** Optional syntax changes presence, not the descriptor of a parameter that is
    present.  Projection therefore resolves collection parameters through the
    leaf relation instead of inspecting only the outer context list. *)
Inductive ParamNode : Type :=
| ScalarParameter (name category : nat)
| CollectionParameter (name category : nat) (kind : SourceKind)
| OptionalParameters (parameters : list ParamNode).

Inductive LeafIn : ParamNode -> list ParamNode -> Prop :=
| LeafHere : forall leaf rest,
    (forall nested, leaf <> OptionalParameters nested) ->
    LeafIn leaf (leaf :: rest)
| LeafThere : forall leaf head rest,
    LeafIn leaf rest -> LeafIn leaf (head :: rest)
| LeafOptional : forall leaf nested rest,
    LeafIn leaf nested -> LeafIn leaf (OptionalParameters nested :: rest).

Theorem optional_context_preserves_collection_descriptor :
  forall name category kind nested rest,
    LeafIn (CollectionParameter name category kind) nested ->
    LeafIn (CollectionParameter name category kind)
           (OptionalParameters nested :: rest).
Proof.
  intros; apply LeafOptional; assumption.
Qed.

Example top_level_only_lookup_is_incomplete :
  LeafIn (CollectionParameter 7 11 SourceList)
         [OptionalParameters [CollectionParameter 7 11 SourceList]].
Proof.
  apply LeafOptional.
  apply LeafHere.
  discriminate.
Qed.

End CollectionProjection.
