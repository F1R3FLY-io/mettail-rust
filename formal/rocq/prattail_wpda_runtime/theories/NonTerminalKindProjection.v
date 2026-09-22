(** Scoped relocation of the ORIGINAL ast/src/grammar.rs NonTerminalKind.

    Source ledger: the original seven variants occur in the order Var, Integer,
    Boolean, StringLiteral, FloatLiteral, Ident, Category. classify matches the
    first six exact, case-sensitive strings and otherwise returns Category.
    is_literal accepts exactly Integer/Boolean/StringLiteral/FloatLiteral;
    is_builtin is inequality with Category, hence also includes Var and Ident.

    The shared core enum retains this order and these original method bodies.
    ast::grammar::NonTerminalKind re-exports it; core AuthoredNonTerminalKind is
    an alias, eliminating the parallel owned vocabulary. The original authored
    enum's Serde metadata is preserved with rename = "AuthoredNonTerminalKind",
    the same seven variant names and indices. Existing Rust traits are retained;
    Serialize/Deserialize are added at the shared declaration, not to a second
    classifier. There is no new crate, source parser, taxonomy or normalizer.

    This model compares the concrete source and relocated six-branch match,
    seven-value queries, discriminants and serializer arguments. The serde
    implementation itself is outside scope: equality of arguments permits the
    SAME serializer to produce identical results. Rust tests additionally pin
    the actual unit-variant metadata callback and postcard bytes/decoding.
    UTF-8 strings below are the exact source spelling observations, with no
    trimming, case folding, alias substitution or identifier parsing. Rust
    ownership, dependency compilation and ABI layout are not proved here.
*)
From Stdlib Require Import List String Bool Arith.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module NonTerminalKindProjection.
Inductive OriginalKind := OriginalVar | OriginalInteger | OriginalBoolean
  | OriginalStringLiteral | OriginalFloatLiteral | OriginalIdent | OriginalCategory.
Inductive SharedKind := SharedVar | SharedInteger | SharedBoolean
  | SharedStringLiteral | SharedFloatLiteral | SharedIdent | SharedCategory.

Definition relocate kind := match kind with
| OriginalVar => SharedVar | OriginalInteger => SharedInteger
| OriginalBoolean => SharedBoolean | OriginalStringLiteral => SharedStringLiteral
| OriginalFloatLiteral => SharedFloatLiteral | OriginalIdent => SharedIdent
| OriginalCategory => SharedCategory end.

Definition original_classify name :=
  if String.eqb name "Var" then OriginalVar else
  if String.eqb name "Integer" then OriginalInteger else
  if String.eqb name "Boolean" then OriginalBoolean else
  if String.eqb name "StringLiteral" then OriginalStringLiteral else
  if String.eqb name "FloatLiteral" then OriginalFloatLiteral else
  if String.eqb name "Ident" then OriginalIdent else OriginalCategory.
Definition shared_classify name :=
  if String.eqb name "Var" then SharedVar else
  if String.eqb name "Integer" then SharedInteger else
  if String.eqb name "Boolean" then SharedBoolean else
  if String.eqb name "StringLiteral" then SharedStringLiteral else
  if String.eqb name "FloatLiteral" then SharedFloatLiteral else
  if String.eqb name "Ident" then SharedIdent else SharedCategory.

Definition original_is_literal kind := match kind with
| OriginalInteger | OriginalBoolean | OriginalStringLiteral | OriginalFloatLiteral => true
| _ => false end.
Definition shared_is_literal kind := match kind with
| SharedInteger | SharedBoolean | SharedStringLiteral | SharedFloatLiteral => true
| _ => false end.
Definition original_is_builtin kind := match kind with OriginalCategory => false | _ => true end.
Definition shared_is_builtin kind := match kind with SharedCategory => false | _ => true end.

Theorem exact_original_classifier_relocation : forall name,
  shared_classify name = relocate (original_classify name).
Proof.
  intros; unfold shared_classify, original_classify.
  repeat match goal with |- context [if ?condition then _ else _] => destruct condition end;
  reflexivity.
Qed.
Theorem literal_query_preserved : forall kind,
  shared_is_literal (relocate kind) = original_is_literal kind.
Proof. destruct kind; reflexivity. Qed.
Theorem builtin_query_preserved : forall kind,
  shared_is_builtin (relocate kind) = original_is_builtin kind.
Proof. destruct kind; reflexivity. Qed.
Theorem literal_query_after_classification_preserved : forall name,
  shared_is_literal (shared_classify name) = original_is_literal (original_classify name).
Proof. intros; rewrite exact_original_classifier_relocation; apply literal_query_preserved. Qed.
Theorem builtin_query_after_classification_preserved : forall name,
  shared_is_builtin (shared_classify name) = original_is_builtin (original_classify name).
Proof. intros; rewrite exact_original_classifier_relocation; apply builtin_query_preserved. Qed.
Theorem relocation_is_injective : forall left right,
  relocate left = relocate right -> left = right.
Proof. destruct left; destruct right; intros; try discriminate; reflexivity. Qed.
Theorem every_unmatched_string_remains_category : forall name,
  name <> "Var" -> name <> "Integer" -> name <> "Boolean" ->
  name <> "StringLiteral" -> name <> "FloatLiteral" -> name <> "Ident" ->
  shared_classify name = SharedCategory.
Proof.
  intros name V I B S F N; unfold shared_classify.
  apply String.eqb_neq in V; apply String.eqb_neq in I; apply String.eqb_neq in B;
  apply String.eqb_neq in S; apply String.eqb_neq in F; apply String.eqb_neq in N.
  now rewrite V, I, B, S, F, N.
Qed.
Example exact_builtin_roster :
  List.map shared_classify ["Var"; "Integer"; "Boolean"; "StringLiteral"; "FloatLiteral"; "Ident"] =
  [SharedVar; SharedInteger; SharedBoolean; SharedStringLiteral; SharedFloatLiteral; SharedIdent].
Proof. reflexivity. Qed.
Example no_string_normalization :
  List.map shared_classify ["var"; "Ident "; " Ident"; "r#Ident"; "Category"; ""] =
  [SharedCategory; SharedCategory; SharedCategory; SharedCategory; SharedCategory; SharedCategory].
Proof. reflexivity. Qed.

Definition original_discriminant kind := match kind with
| OriginalVar => 0 | OriginalInteger => 1 | OriginalBoolean => 2
| OriginalStringLiteral => 3 | OriginalFloatLiteral => 4 | OriginalIdent => 5 | OriginalCategory => 6 end.
Definition shared_discriminant kind := match kind with
| SharedVar => 0 | SharedInteger => 1 | SharedBoolean => 2
| SharedStringLiteral => 3 | SharedFloatLiteral => 4 | SharedIdent => 5 | SharedCategory => 6 end.
Definition original_variant_name kind := match kind with
| OriginalVar => "Var" | OriginalInteger => "Integer" | OriginalBoolean => "Boolean"
| OriginalStringLiteral => "StringLiteral" | OriginalFloatLiteral => "FloatLiteral"
| OriginalIdent => "Ident" | OriginalCategory => "Category" end.
Definition shared_variant_name kind := match kind with
| SharedVar => "Var" | SharedInteger => "Integer" | SharedBoolean => "Boolean"
| SharedStringLiteral => "StringLiteral" | SharedFloatLiteral => "FloatLiteral"
| SharedIdent => "Ident" | SharedCategory => "Category" end.
Definition original_serde_metadata kind :=
  ("AuthoredNonTerminalKind", original_discriminant kind, original_variant_name kind).
Definition shared_serde_metadata kind :=
  ("AuthoredNonTerminalKind", shared_discriminant kind, shared_variant_name kind).

Theorem original_variant_order_preserved : forall kind,
  shared_discriminant (relocate kind) = original_discriminant kind.
Proof. destruct kind; reflexivity. Qed.
Theorem complete_serde_metadata_preserved : forall kind,
  shared_serde_metadata (relocate kind) = original_serde_metadata kind.
Proof. destruct kind; reflexivity. Qed.
Theorem same_serializer_observes_same_arguments : forall Result
  (serialize : string * nat * string -> Result) kind,
  serialize (shared_serde_metadata (relocate kind)) = serialize (original_serde_metadata kind).
Proof. intros; rewrite complete_serde_metadata_preserved; reflexivity. Qed.

Definition original_decode index := match index with
| 0 => Some OriginalVar | 1 => Some OriginalInteger | 2 => Some OriginalBoolean
| 3 => Some OriginalStringLiteral | 4 => Some OriginalFloatLiteral | 5 => Some OriginalIdent
| 6 => Some OriginalCategory | _ => None end.
Definition shared_decode index := match index with
| 0 => Some SharedVar | 1 => Some SharedInteger | 2 => Some SharedBoolean
| 3 => Some SharedStringLiteral | 4 => Some SharedFloatLiteral | 5 => Some SharedIdent
| 6 => Some SharedCategory | _ => None end.
Theorem decoded_variant_index_preserved : forall index,
  shared_decode index = option_map relocate (original_decode index).
Proof. intros [|[|[|[|[|[|[|index]]]]]]]; reflexivity. Qed.
Theorem shared_index_roundtrip : forall kind,
  shared_decode (shared_discriminant kind) = Some kind.
Proof. destruct kind; reflexivity. Qed.

Print Assumptions exact_original_classifier_relocation.
Print Assumptions literal_query_preserved.
Print Assumptions builtin_query_preserved.
Print Assumptions literal_query_after_classification_preserved.
Print Assumptions builtin_query_after_classification_preserved.
Print Assumptions relocation_is_injective.
Print Assumptions every_unmatched_string_remains_category.
Print Assumptions exact_builtin_roster.
Print Assumptions no_string_normalization.
Print Assumptions original_variant_order_preserved.
Print Assumptions complete_serde_metadata_preserved.
Print Assumptions same_serializer_observes_same_arguments.
Print Assumptions decoded_variant_index_preserved.
Print Assumptions shared_index_roundtrip.
End NonTerminalKindProjection.
