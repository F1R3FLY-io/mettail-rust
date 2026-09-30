(** A per-category [noadmit] declaration refines the existing variable-term
    admission bit. It does not turn an object category into a Data category or
    remove its authored constructors. The canonical type field is the same
    [admits_variables] field consumed by the shared synthetic-rule analysis.

    This is a local elaboration and admission model. Rust correspondence must
    check the generated DDL AST, structural wire decoder, canonical type value,
    GrammarCore projection, and shared rule synthesis. It does not prove the
    lexer, WPDA realization, or theorem-channel implementation. *)
From Stdlib Require Import Bool String.
From RuntimeGrammar Require Import DataCategoryCapabilities.

Module NoAdmitTypeProjection.

Inductive AuthoredType :=
| Plain (name : string)
| NoAdmit (name : string).

Record CategoryDecl := {
  category_name : string;
  category_role : CategoryRole;
  admits_variables : bool
}.

Definition elaborate (declaration : AuthoredType) : CategoryDecl :=
  match declaration with
  | Plain name => {| category_name := name;
                     category_role := Object;
                     admits_variables := true |}
  | NoAdmit name => {| category_name := name;
                       category_role := Object;
                       admits_variables := false |}
  end.

Inductive CanonicalType :=
| Bare (name : string)
| Detailed (name : string) (admits_variables : bool).

Definition encode (category : CategoryDecl) : CanonicalType :=
  if admits_variables category
  then Bare (category_name category)
  else Detailed (category_name category) false.

Definition decode (value : CanonicalType) : CategoryDecl :=
  match value with
  | Bare name => {| category_name := name;
                    category_role := Object;
                    admits_variables := true |}
  | Detailed name admitted => {| category_name := name;
                                  category_role := Object;
                                  admits_variables := admitted |}
  end.

Theorem authored_type_round_trip : forall declaration,
  decode (encode (elaborate declaration)) = elaborate declaration.
Proof. intros [name|name]; reflexivity. Qed.

Theorem plain_keeps_the_existing_default : forall name,
  admits_variables (elaborate (Plain name)) = true /\
  encode (elaborate (Plain name)) = Bare name.
Proof. intros; split; reflexivity. Qed.

Theorem noadmit_projects_exactly_to_the_existing_false_field : forall name,
  admits_variables (elaborate (NoAdmit name)) = false /\
  encode (elaborate (NoAdmit name)) = Detailed name false.
Proof. intros; split; reflexivity. Qed.

Definition synthesize_variable (category : CategoryDecl) : bool :=
  has_capability (category_role category) VariableCarrier &&
  admits_variables category.

Theorem noadmit_disables_only_implicit_variable_synthesis : forall name,
  synthesize_variable (elaborate (Plain name)) = true /\
  synthesize_variable (elaborate (NoAdmit name)) = false /\
  (forall capability,
     has_capability (category_role (elaborate (Plain name))) capability =
     has_capability (category_role (elaborate (NoAdmit name))) capability).
Proof. intros; repeat split; try reflexivity; intros []; reflexivity. Qed.

(** [identifier] represents the already-existing lexical identifier judgment;
    [literal] represents one authored exact literal constructor. The model
    preserves both readings for a plain category and removes only the former
    when [noadmit] is authored. *)
Definition accepts (identifier : string -> bool) (literal source : string)
    (category : CategoryDecl) : bool :=
  String.eqb literal source ||
  (synthesize_variable category && identifier source).

Theorem authored_literal_survives_noadmit : forall identifier name literal,
  accepts identifier literal literal (elaborate (NoAdmit name)) = true.
Proof. intros; unfold accepts; rewrite String.eqb_refl; reflexivity. Qed.

Theorem closed_category_rejects_foreign_identifier :
  forall identifier name literal foreign,
    literal <> foreign ->
    accepts identifier literal foreign (elaborate (NoAdmit name)) = false.
Proof.
  intros identifier name literal foreign distinct.
  unfold accepts, synthesize_variable; simpl.
  apply String.eqb_neq in distinct; rewrite distinct; reflexivity.
Qed.

Theorem plain_category_retains_foreign_variable_reading :
  forall identifier name literal foreign,
    literal <> foreign -> identifier foreign = true ->
    accepts identifier literal foreign (elaborate (Plain name)) = true.
Proof.
  intros identifier name literal foreign distinct recognized.
  unfold accepts, synthesize_variable; simpl.
  apply String.eqb_neq in distinct; rewrite distinct, recognized; reflexivity.
Qed.

(** The Regex GSLT's [Pattern] and [Scalar] are closed object categories.
    Their authored literals and structural FLT holes are independent of the
    implicit object-variable rules. This models the three readings actually
    observed for [a] in [fullMatch(a+, ${text:Text})]: a Pattern variable, a
    [PLiteral] with a Scalar variable, and a [PLiteral] with literal text.
    The template hole is a fourth, separate judgment. *)
Inductive RegexReading :=
| PatternVariable
| ScalarVariable
| ScalarLiteral
| TemplateHole.

Definition regex_reading_allowed (reading : RegexReading) : bool :=
  match reading with
  | PatternVariable => synthesize_variable (elaborate (NoAdmit "Pattern"))
  | ScalarVariable => synthesize_variable (elaborate (NoAdmit "Scalar"))
  | ScalarLiteral | TemplateHole => true
  end.

Theorem closed_regex_retains_exactly_literals_and_holes : forall reading,
  regex_reading_allowed reading = true <->
  reading = ScalarLiteral \/ reading = TemplateHole.
Proof.
  destruct reading; simpl; split; intros H.
  - discriminate.
  - destruct H as [H | H]; discriminate.
  - discriminate.
  - destruct H as [H | H]; discriminate.
  - left; reflexivity.
  - reflexivity.
  - right; reflexivity.
  - reflexivity.
Qed.

End NoAdmitTypeProjection.
