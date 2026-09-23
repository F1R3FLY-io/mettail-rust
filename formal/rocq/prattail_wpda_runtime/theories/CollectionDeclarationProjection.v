(** Original collection declaration/element source-observation boundary.

    Sources: ast/src/language/model.rs::collection_element_type_for_category,
    element_ident_from_native_type, CollectionCategory defaults/delimiters;
    macros/src/gen/runtime/wpda_codegen/synthetic.rs::collection.

    Only the ordered selection worker and fixed delimiter constructors are
    modeled here. The existing shallow syn native-element probe remains the operation
    behind native_element; no Rust type parser or native classifier is derived.
    Its duplicate macro helper may delegate to the original AST helper.
    Native None and failed element observation BOTH return immediately for a
    declared collection; neither permits searching terms. Otherwise only the
    FIRST matching term is inspected, and its FIRST Collection item wins.

    Reader projections below are mathematical observations, not eagerly built
    vectors or a replacement syntax IR. Equality callbacks are the original
    Ident equality / checked retained-name equality, not inferred spellings.
    The trace records actual selected comparison/field/item/native sites.
    It does not certify allocation, clone/drop timing, panic recovery, arbitrary
    callback effects, native decoder semantics, or availability of metadata.
    Rust must retain source clones at the selected original sites. Missing
    native-element metadata cannot be reconstructed from HostOpaque strings.

    Defaults below are the exact FIVE existing constructors, not a policy for
    normalizing partial schema declarations. Raw None/Some-empty fields stay
    distinct; notably key/value None must not be blanket-defaulted. Original
    positional Map and dictionary Pathmap forms already differ there.
    SyntheticRuleProjection supplies collection_label, recipe materialization,
    and element/home fallback; those definitions and its ordered synthesis
    driver are not reproduced here.
*)
From Stdlib Require Import List String Bool.
From PrattailWpdaRuntime Require Import SyntheticRuleProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module CollectionDeclarationProjection.
Module S := SyntheticRuleProjection.SyntheticRuleProjection.

Inductive Event := CompareType | ReadCollection | ReadNative | ResolveNative
| CompareRule | ReadItem.
Fixpoint find_trace {A} (test : A -> bool) (event : Event) (values : list A)
    : option A * list Event :=
  match values with
  | [] => (None, [])
  | value :: rest => if test value then (Some value, [event])
      else let '(found, trace) := find_trace test event rest in
           (found, event :: trace)
  end.
Fixpoint find_item {I E} (observe : I -> option E) (items : list I)
    : option E * list Event :=
  match items with
  | [] => (None, [])
  | item :: rest => match observe item with
    | Some element => (Some element, [ReadItem])
    | None => let '(found, trace) := find_item observe rest in
              (found, ReadItem :: trace)
    end
  end.
Definition prepend {A} events (result : A * list Event) :=
  (fst result, events ++ snd result).

Lemma find_trace_projection : forall A B (project : A -> B) test event values,
  find_trace test event (map project values) =
  (option_map project (fst (find_trace (fun value => test (project value)) event values)),
   snd (find_trace (fun value => test (project value)) event values)).
Proof.
  intros A B project test event values; induction values as [|value rest IH]; cbn.
  - reflexivity.
  - destruct (test (project value)); [reflexivity|].
    rewrite IH. destruct (find_trace (fun value => test (project value)) event rest); reflexivity.
Qed.
Lemma find_item_projection : forall I E (observe : I -> option E) items,
  find_item (fun value => value) (map observe items) = find_item observe items.
Proof.
  intros I E observe items; induction items as [|item rest IH]; cbn; [reflexivity|].
  destruct (observe item); [reflexivity|]. now rewrite IH.
Qed.

Section ElementWorker.
Context {Native Element Declaration Rule Item : Type}.
Variable native_element : Native -> option Element.
Record SourceDeclaration := {
  source_type_matches : bool;
  source_collection : bool;
  source_native : option Native
}.
Record SourceRule := {
  source_rule_matches : bool;
  source_items : list (option Element)
}.
Record Reader := {
  type_matches : Declaration -> bool;
  has_collection : Declaration -> bool;
  native : Declaration -> option Native;
  rule_matches : Rule -> bool;
  items : Rule -> list Item;
  item_element : Item -> option Element
}.
Variable reader : Reader.
Definition project_declaration declaration :=
  {| source_type_matches := type_matches reader declaration;
     source_collection := has_collection reader declaration;
     source_native := native reader declaration |}.
Definition project_rule rule :=
  {| source_rule_matches := rule_matches reader rule;
     source_items := map (item_element reader) (items reader rule) |}.
Definition resolve_native value :=
  match value with
  | None => (None, [ReadNative])
  | Some native => (native_element native, [ReadNative; ResolveNative])
  end.
Definition original_terms rules :=
  let '(found, trace) := find_trace source_rule_matches CompareRule rules in
  match found with
  | None => (None, trace)
  | Some rule => prepend trace (find_item (fun value => value) (source_items rule))
  end.
Definition shared_terms rules :=
  let '(found, trace) := find_trace (rule_matches reader) CompareRule rules in
  match found with
  | None => (None, trace)
  | Some rule => prepend trace (find_item (item_element reader) (items reader rule))
  end.
Definition original_element declarations rules :=
  let '(found, trace) := find_trace source_type_matches CompareType declarations in
  match found with
  | None => prepend trace (original_terms rules)
  | Some declaration =>
      if source_collection declaration then
        prepend (trace ++ [ReadCollection]) (resolve_native (source_native declaration))
      else prepend (trace ++ [ReadCollection]) (original_terms rules)
  end.
Definition shared_element declarations rules :=
  let '(found, trace) := find_trace (type_matches reader) CompareType declarations in
  match found with
  | None => prepend trace (shared_terms rules)
  | Some declaration =>
      if has_collection reader declaration then
        prepend (trace ++ [ReadCollection]) (resolve_native (native reader declaration))
      else prepend (trace ++ [ReadCollection]) (shared_terms rules)
  end.

Theorem first_rule_and_item_projection : forall rules,
  original_terms (map project_rule rules) = shared_terms rules.
Proof.
  intros; unfold original_terms, shared_terms.
  rewrite find_trace_projection.
  change (let '(found, trace) :=
      (option_map project_rule (fst (find_trace (rule_matches reader) CompareRule rules)),
       snd (find_trace (rule_matches reader) CompareRule rules)) in
    match found with None => (None, trace)
    | Some rule => prepend trace (find_item (fun value => value) (source_items rule)) end = shared_terms rules).
  unfold shared_terms.
  destruct (find_trace (rule_matches reader) CompareRule rules) as [[rule|] trace]; cbn.
  - now rewrite find_item_projection.
  - reflexivity.
Qed.
Theorem exact_ordered_source_observation_projection : forall declarations rules,
  original_element (map project_declaration declarations) (map project_rule rules) =
  shared_element declarations rules.
Proof.
  intros; unfold original_element, shared_element.
  rewrite find_trace_projection.
  change (let '(found, trace) :=
      (option_map project_declaration (fst (find_trace (type_matches reader) CompareType declarations)),
       snd (find_trace (type_matches reader) CompareType declarations)) in
    match found with
    | None => prepend trace (original_terms (map project_rule rules))
    | Some declaration => if source_collection declaration then
        prepend (trace ++ [ReadCollection]) (resolve_native (source_native declaration))
      else prepend (trace ++ [ReadCollection]) (original_terms (map project_rule rules)) end = shared_element declarations rules).
  unfold shared_element.
  destruct (find_trace (type_matches reader) CompareType declarations) as [[declaration|] trace]; cbn.
  - destruct (has_collection reader declaration); [reflexivity|].
    now rewrite first_rule_and_item_projection.
  - now rewrite first_rule_and_item_projection.
Qed.
Theorem absent_native_stops_without_rule_comparison : forall declaration rest rules,
  type_matches reader declaration = true -> has_collection reader declaration = true ->
  native reader declaration = None ->
  shared_element (declaration :: rest) rules =
    (None, [CompareType; ReadCollection; ReadNative]).
Proof. intros; unfold shared_element; cbn [find_trace]; rewrite H, H0, H1; reflexivity. Qed.
Theorem failed_native_element_stops_without_rule_comparison : forall declaration rest rules value,
  type_matches reader declaration = true -> has_collection reader declaration = true ->
  native reader declaration = Some value -> native_element value = None ->
  shared_element (declaration :: rest) rules =
    (None, [CompareType; ReadCollection; ReadNative; ResolveNative]).
Proof. intros; unfold shared_element; cbn [find_trace]; rewrite H, H0, H1; unfold resolve_native; rewrite H2; reflexivity. Qed.
Theorem first_matching_empty_rule_suppresses_later_rules : forall rule rest,
  rule_matches reader rule = true -> items reader rule = [] ->
  shared_terms (rule :: rest) = (None, [CompareRule]).
Proof. intros; unfold shared_terms; cbn [find_trace]; rewrite H, H0; reflexivity. Qed.
End ElementWorker.

Record Delimiters := {
  open_text : string; close_text : string; separator : string;
  key_value_separator : option string
}.
Definition original_defaults kind :=
  match kind with
  | S.ListKind => {| open_text := "list("; close_text := ")"; separator := ","; key_value_separator := None |}
  | S.BagKind => {| open_text := "bag("; close_text := ")"; separator := ","; key_value_separator := None |}
  | S.MapKind => {| open_text := "map("; close_text := ")"; separator := ","; key_value_separator := Some ":" |}
  | S.SetKind => {| open_text := "Set("; close_text := ")"; separator := ","; key_value_separator := None |}
  | S.PathmapKind => {| open_text := "pathmap("; close_text := ")"; separator := ","; key_value_separator := Some ":" |}
  end.
Definition shared_defaults := original_defaults.
Theorem defaults_relocation_preserves_every_field : forall kind,
  shared_defaults kind = original_defaults kind.
Proof. reflexivity. Qed.
Definition declared_delimiters (_kind : S.CollectionKind) (fields : Delimiters) := fields.
Theorem explicit_empty_and_absent_key_separator_are_not_defaulted : forall kind close,
  declared_delimiters kind
    {| open_text := ""; close_text := close; separator := ""; key_value_separator := None |} =
    {| open_text := ""; close_text := close; separator := ""; key_value_separator := None |}.
Proof. reflexivity. Qed.
Theorem collection_recipe_materialization_is_reused : forall home observation,
  S.materialize_recipe (S.recipe_collection home observation) = S.raw_collection home observation.
Proof. apply S.materialize_collection. Qed.
Theorem missing_element_retains_original_home_fallback : forall home kind opening split closing sep,
  S.element_or_home home
    {| S.collection_kind := kind; S.trimmed_open := opening; S.split_open := split;
       S.close_text := closing; S.separator_text := sep; S.element_name := None |} = home.
Proof. reflexivity. Qed.

Print Assumptions find_trace_projection.
Print Assumptions find_item_projection.
Print Assumptions first_rule_and_item_projection.
Print Assumptions exact_ordered_source_observation_projection.
Print Assumptions absent_native_stops_without_rule_comparison.
Print Assumptions failed_native_element_stops_without_rule_comparison.
Print Assumptions first_matching_empty_rule_suppresses_later_rules.
Print Assumptions defaults_relocation_preserves_every_field.
Print Assumptions explicit_empty_and_absent_key_separator_are_not_defaulted.
Print Assumptions collection_recipe_materialization_is_reused.
Print Assumptions missing_element_retains_original_home_fallback.
End CollectionDeclarationProjection.
