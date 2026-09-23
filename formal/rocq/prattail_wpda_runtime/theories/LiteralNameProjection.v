(** Exact original literal token-name normalization selector.

    Source: ast/src/language/parse.rs, the mapped_name iterator chain in
    LanguageDef::parse. Prior declaration validation, original = ld.name.clone(),
    TokenDef field moves/category Some(original), cross-block duplicate checks,
    and token_defs.extend stay outside this helper and unchanged.

    The selector first compares ORIGINAL category-name equality, not rendered
    spelling (unlike the separate native FIRST family election). Only the first
    equal declaration is inspected for native presence. The existing NativeKind
    standard_token_variant decides whether to construct a standard name using
    original.span() or clone the original name. No alias policy or taxonomy is
    introduced. Reuse NativeKindProjection's checked constant table.

    Names/equality are abstract pure source observations; no equality/spelling
    identity is assumed. The name recipe retains the exact original constructor
    argument, and realize_ast below states the span law explicitly. Production
    core sees no span or syn type: the AST constructor callback performs the
    SAME Ident::new(variant, original.span()), or original.clone(). Runtime
    interpretation/admission/aliases are separate obligations.

    The source/direct-field versus shared/borrowed-handle correspondence includes
    lazy callback order, first-match stop and opaque output construction. It is
    scoped to finite source lists and lawful deterministic callbacks, not parser
    validity, allocation bounds, arbitrary callback effects, or reconstruction.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import NativeKindProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module LiteralNameProjection.
Module K := NativeKindProjection.NativeKindProjection.
Module N := K.N.

Section Selector.
Context {Name : Type}.
Variable names_equal : Name -> Name -> bool.

Record Category := { source_id : nat; source_name : Name; source_native : option K.Kind }.
Inductive Recipe := CloneOriginal (original : Name) | ConstructStandard (variant : string) (original : Name).
Inductive Event :=
| ReadName (category : nat)
| CompareNames (candidate original : Name)
| NativePresence (category : nat)
| ResolveNativeKind (category : nat) (kind : K.Kind)
| StandardVariant (kind : K.Kind)
| CloneName (original : Name)
| ConstructName (variant : string) (original : Name).

Fixpoint source_find original categories : option Category * list Event := match categories with
| [] => (None, [])
| category :: rest =>
  let trace := [ReadName (source_id category); CompareNames (source_name category) original] in
  if names_equal (source_name category) original then (Some category, trace)
  else let '(found, following) := source_find original rest in (found, trace ++ following)
end.

Definition source_select original categories : Recipe * list Event :=
  let '(found, trace) := source_find original categories in
  let clone trace := (CloneOriginal original, trace ++ [CloneName original]) in
  match found with
  | None => clone trace
  | Some category =>
    let checked := trace ++ [NativePresence (source_id category)] in
    match source_native category with
    | None => clone checked
    | Some kind =>
      let resolved := checked ++ [ResolveNativeKind (source_id category) kind; StandardVariant kind] in
      match K.standard_token_variant kind with
      | None => clone resolved
      | Some variant => (ConstructStandard variant original, resolved ++ [ConstructName variant original])
      end
    end
  end.

Record Reader (C : Type) := {
  category_id : C -> nat;
  category_name : C -> Name;
  category_native : C -> option K.Kind
}.
Record Constructors (P : Type) := {
  clone_original : Name -> P;
  construct_standard : string -> Name -> P
}.
Definition interpret {P} (constructors : Constructors P) recipe := match recipe with
| CloneOriginal original => clone_original constructors original
| ConstructStandard variant original => construct_standard constructors variant original end.

Fixpoint shared_find {C} (reader : Reader C) original categories := match categories with
| [] => (None, [])
| category :: rest =>
  let trace := [ReadName (category_id reader category); CompareNames (category_name reader category) original] in
  if names_equal (category_name reader category) original then (Some category, trace)
  else let '(found, following) := shared_find reader original rest in (found, trace ++ following)
end.

Definition shared_select {C P} (reader : Reader C) (constructors : Constructors P) original categories :=
  let '(found, trace) := shared_find reader original categories in
  let clone trace := (clone_original constructors original, trace ++ [CloneName original]) in
  match found with
  | None => clone trace
  | Some category =>
    let checked := trace ++ [NativePresence (category_id reader category)] in
    match category_native reader category with
    | None => clone checked
    | Some kind =>
      let resolved := checked ++ [ResolveNativeKind (category_id reader category) kind; StandardVariant kind] in
      match K.standard_token_variant kind with
      | None => clone resolved
      | Some variant => (construct_standard constructors variant original,
                         resolved ++ [ConstructName variant original])
      end
    end
  end.

Record ReaderLaw {C} (reader : Reader C) (project : Category -> C) : Prop := {
  id_law : forall category, category_id reader (project category) = source_id category;
  name_law : forall category, category_name reader (project category) = source_name category;
  native_law : forall category, category_native reader (project category) = source_native category
}.

Lemma first_equal_declaration_projection : forall C (reader : Reader C) project,
  ReaderLaw reader project -> forall original categories,
  shared_find reader original (map project categories) =
    (option_map project (fst (source_find original categories)), snd (source_find original categories)).
Proof.
  intros C reader project law original categories; induction categories as [|category rest IH]; cbn.
  - reflexivity.
  - rewrite (id_law law), (name_law law).
    destruct (names_equal (source_name category) original); [reflexivity|].
    rewrite IH. destruct (source_find original rest); reflexivity.
Qed.

Theorem exact_literal_name_constructor_and_trace_projection : forall C P (reader : Reader C)
  (constructors : Constructors P) project,
  ReaderLaw reader project -> forall original categories,
  shared_select reader constructors original (map project categories) =
    (interpret constructors (fst (source_select original categories)), snd (source_select original categories)).
Proof.
  intros C P reader constructors project law original categories.
  unfold shared_select, source_select. rewrite (first_equal_declaration_projection law).
  destruct (source_find original categories) as [[category|] trace]; cbn; [|reflexivity].
  rewrite (id_law law), (native_law law).
  destruct (source_native category) as [kind|]; [|reflexivity].
  destruct (K.standard_token_variant kind); reflexivity.
Qed.

Lemma missing_category_clones_original : forall original,
  source_select original [] = (CloneOriginal original, [CloneName original]).
Proof. reflexivity. Qed.

Lemma first_equal_without_native_stops : forall original category rest,
  names_equal (source_name category) original = true -> source_native category = None ->
  source_select original (category :: rest) =
    (CloneOriginal original,
     [ReadName (source_id category); CompareNames (source_name category) original;
      NativePresence (source_id category); CloneName original]).
Proof. intros; unfold source_select; cbn; rewrite H; cbn; rewrite H0; reflexivity. Qed.

Lemma original_name_argument_is_preserved : forall original categories,
  match fst (source_select original categories) with
  | CloneOriginal name => name = original | ConstructStandard _ name => name = original end.
Proof.
  intros; unfold source_select.
  destruct (source_find original categories) as [[category|] trace]; cbn; [|reflexivity].
  destruct (source_native category) as [kind|]; [|reflexivity].
  destruct (K.standard_token_variant kind); reflexivity.
Qed.

(** Concrete AST constructor interpretation: mapped names carry the literal
    occurrence's span, NOT the matched type declaration's name/span. Clones
    retain the entire original opaque name, including its raw spelling. *)
Inductive AstName := Existing (original : Name) | Built (variant : string) (span : nat).
Variable original_span : Name -> nat.
Definition realize_ast recipe := match recipe with
| CloneOriginal original => Existing original
| ConstructStandard variant original => Built variant (original_span original) end.
Definition ast_constructors : Constructors AstName :=
  {| clone_original := Existing;
     construct_standard := fun variant original => Built variant (original_span original) |}.

Lemma original_ast_span_and_clone_constructor_law : forall recipe,
  interpret ast_constructors recipe = realize_ast recipe.
Proof. intros []; reflexivity. Qed.

Theorem ast_selector_reuses_original_constructor_arguments : forall C (reader : Reader C) project,
  ReaderLaw reader project -> forall original categories,
  fst (shared_select reader ast_constructors original (map project categories)) =
    realize_ast (fst (source_select original categories)).
Proof.
  intros C reader project law original categories.
  rewrite (exact_literal_name_constructor_and_trace_projection ast_constructors law).
  cbn. apply original_ast_span_and_clone_constructor_law.
Qed.
End Selector.

(** A source-equality witness deliberately separating spelling and span. *)
Record WitnessName := { equality_class : nat; spelling : string; name_span : nat }.
Definition witness_eq lhs rhs := Nat.eqb (equality_class lhs) (equality_class rhs).
Definition wanted := {| equality_class := 1; spelling := "r#Wanted"; name_span := 90 |}.
Definition spelling_only := {| equality_class := 2; spelling := "r#Wanted"; name_span := 10 |}.
Definition equal_alias := {| equality_class := 1; spelling := "Different"; name_span := 20 |}.
Definition witness_categories : list (@Category WitnessName) :=
  [{| source_id := 0; source_name := spelling_only; source_native := Some N.Float64 |};
   {| source_id := 1; source_name := equal_alias; source_native := Some N.Int32 |}].

Example equality_not_spelling_controls_first_match_and_original_span :
  realize_ast name_span (fst (source_select witness_eq wanted witness_categories)) = Built "Integer" 90.
Proof. reflexivity. Qed.

Example bigint_and_other_clone_instead_of_inventing_a_family_name :
  map (fun kind => fst (source_select witness_eq wanted
    [{| source_id := 0; source_name := wanted; source_native := Some kind |}]))
      [N.CanonicalBigInt; N.CanonicalBigRat; N.CanonicalFixedPoint; N.Other] =
  [CloneOriginal wanted; CloneOriginal wanted; CloneOriginal wanted; CloneOriginal wanted].
Proof. reflexivity. Qed.

Print Assumptions first_equal_declaration_projection.
Print Assumptions exact_literal_name_constructor_and_trace_projection.
Print Assumptions missing_category_clones_original.
Print Assumptions first_equal_without_native_stops.
Print Assumptions original_name_argument_is_preserved.
Print Assumptions original_ast_span_and_clone_constructor_law.
Print Assumptions ast_selector_reuses_original_constructor_arguments.
Print Assumptions equality_not_spelling_controls_first_match_and_original_span.
Print Assumptions bigint_and_other_clone_instead_of_inventing_a_family_name.
End LiteralNameProjection.
