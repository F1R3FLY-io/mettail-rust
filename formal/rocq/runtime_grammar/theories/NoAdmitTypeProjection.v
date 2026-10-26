(** A per-category [noadmit] declaration refines the existing variable-term
    admission bit. It does not turn an object category into a Data category or
    remove its authored constructors. The canonical type field is the same
    [admits_variables] field consumed by the shared synthetic-rule analysis.

    This is a local elaboration and admission model. Rust correspondence must
    check the generated DDL AST, structural wire decoder, canonical type value,
    GrammarCore projection, and shared rule synthesis. It does not prove the
    lexer, WPDA realization, or theorem-channel implementation. *)
From Stdlib Require Import Bool String List Arith.PeanoNat.
From RuntimeGrammar Require Import DataCategoryCapabilities.
Import ListNotations.

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

(** The following is the exact constructor collision at the Cost(Rho) ground
    signature boundary, not a model of the whole WPDA. The generated semantic
    key makes [CostSigGround(Name::NVar x)] transparent to [Name::NVar x],
    while synthetic [CostSig::CVar x] writes the same variable key under the
    CostSig root. No election policy can recover a constructor already merged
    under that key. Disabling only the synthetic variable route leaves the
    authored ground constructor as the sole reading for an identifier. *)
Inductive CostSignatureReading :=
| ImplicitSignatureVariable (name : string)
| DeclaredGroundName (name : string).

Definition cost_signature_readings (category : CategoryDecl) (name : string) :=
  (if synthesize_variable category
   then [ImplicitSignatureVariable name] else []) ++ [DeclaredGroundName name].

Definition variable_semantic_key (reading : CostSignatureReading) : string :=
  match reading with
  | ImplicitSignatureVariable name | DeclaredGroundName name => name
  end.

Theorem admitted_signature_variable_collides_with_transparent_ground : forall name,
  variable_semantic_key (ImplicitSignatureVariable name) =
  variable_semantic_key (DeclaredGroundName name).
Proof. reflexivity. Qed.

Theorem noadmit_preserves_the_declared_ground_without_a_variable_competitor :
  forall name,
    cost_signature_readings (elaborate (NoAdmit "CostSig")) name =
    [DeclaredGroundName name].
Proof. reflexivity. Qed.

Theorem plain_signature_exposes_both_colliding_readings : forall name,
  cost_signature_readings (elaborate (Plain "CostSig")) name =
  [ImplicitSignatureVariable name; DeclaredGroundName name].
Proof. reflexivity. Qed.

(** Iterative destruction replaces a child before queuing that child. A
    variable-admitting category has an immediate finite replacement. A closed
    category, whether parser Data or semantic [noadmit] Object, instead needs
    a declared constructor whose strict scalar dependencies already have
    finite replacements. Optional and collection fields have no strict
    dependency because [None] and the empty collection are finite. *)
Record ConstructorRecipe := {
  recipe_owner : nat;
  strict_dependencies : list nat;
  recipe_supported : bool
}.

Definition recipe_ready (selected : list nat) (recipe : ConstructorRecipe) : bool :=
  recipe_supported recipe &&
  forallb
    (fun dependency =>
       if in_dec Nat.eq_dec dependency selected then true else false)
    (strict_dependencies recipe).

Theorem ready_recipe_has_only_selected_strict_dependencies :
  forall selected recipe dependency,
    recipe_ready selected recipe = true ->
    In dependency (strict_dependencies recipe) ->
    In dependency selected.
Proof.
  intros selected recipe dependency ready present.
  unfold recipe_ready in ready.
  apply andb_true_iff in ready as [_ dependencies_ready].
  apply forallb_forall with (x := dependency) in dependencies_ready; auto.
  destruct (in_dec Nat.eq_dec dependency selected); congruence.
Qed.

Theorem recipe_readiness_is_monotone :
  forall selected extended recipe,
    (forall dependency, In dependency selected -> In dependency extended) ->
    recipe_ready selected recipe = true ->
    recipe_ready extended recipe = true.
Proof.
  intros selected extended recipe included ready.
  unfold recipe_ready in *.
  apply andb_true_iff in ready as [supported dependencies_ready].
  apply andb_true_iff; split; auto.
  apply forallb_forall; intros dependency present.
  apply forallb_forall with (x := dependency) in dependencies_ready; auto.
  destruct (in_dec Nat.eq_dec dependency selected) as [already|missing].
  - destruct (in_dec Nat.eq_dec dependency extended) as [present_extended|absent_extended].
    + reflexivity.
    + exfalso; apply absent_extended; apply included; exact already.
  - discriminate.
Qed.

Definition first_ready_recipe (selected : list nat) (recipes : list ConstructorRecipe) :=
  find (recipe_ready selected) recipes.

Theorem finite_recipe_selection_never_invents_a_constructor :
  forall selected recipes recipe,
    first_ready_recipe selected recipes = Some recipe ->
    In recipe recipes /\ recipe_ready selected recipe = true.
Proof.
  intros selected recipes; induction recipes as [|head tail IH]; intros recipe found.
  - discriminate.
  - simpl in found.
    destruct (recipe_ready selected head) eqn:ready.
    + inversion found; subst; split; auto; left; reflexivity.
    + apply IH in found as [declared selected_ready].
      split; auto; right; exact declared.
Qed.

Definition name_category := 0.
Definition cost_signature_category := 1.
Definition cost_stack_category := 2.
Definition ground_name_recipe :=
  {| recipe_owner := cost_signature_category;
     strict_dependencies := [name_category];
     recipe_supported := true |}.
Definition empty_stack_recipe :=
  {| recipe_owner := cost_stack_category;
     strict_dependencies := [];
     recipe_supported := true |}.

Theorem cost_signature_and_stack_have_finite_declared_replacements :
  recipe_ready [name_category] ground_name_recipe = true /\
  recipe_ready [name_category; cost_signature_category] empty_stack_recipe = true.
Proof. split; reflexivity. Qed.

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

(** A closed semantic category can still contain a variable-admitting child.
    Substitution for the *closed category's own* absent variable sort is the
    identity, while substitution for the child's sort still traverses it.
    This distinguishes [noadmit] from treating the entire term as opaque. *)
Inductive OpenName := NameVariable (id : nat) | NameLiteral (id : nat).
Inductive ClosedSignature :=
| GroundSignature (name : OpenName)
| CompoundSignature (lhs rhs : ClosedSignature).

Fixpoint substitute_closed_sort (term : ClosedSignature) : ClosedSignature :=
  match term with
  | GroundSignature name => GroundSignature name
  | CompoundSignature lhs rhs =>
      CompoundSignature (substitute_closed_sort lhs) (substitute_closed_sort rhs)
  end.

Theorem noadmit_same_sort_substitution_is_identity : forall term,
  substitute_closed_sort term = term.
Proof.
  induction term as [name | lhs lhs_identity rhs rhs_identity]; simpl.
  - reflexivity.
  - rewrite lhs_identity, rhs_identity; reflexivity.
Qed.

Definition substitute_name (needle replacement : nat) (name : OpenName) : OpenName :=
  match name with
  | NameVariable id => if Nat.eqb id needle then NameLiteral replacement else name
  | NameLiteral _ => name
  end.

Fixpoint substitute_name_inside_signature
    (needle replacement : nat) (term : ClosedSignature) : ClosedSignature :=
  match term with
  | GroundSignature name => GroundSignature (substitute_name needle replacement name)
  | CompoundSignature lhs rhs =>
      CompoundSignature
        (substitute_name_inside_signature needle replacement lhs)
        (substitute_name_inside_signature needle replacement rhs)
  end.

Theorem noadmit_preserves_embedded_open_sort_substitution : forall needle replacement,
  substitute_name_inside_signature needle replacement
    (GroundSignature (NameVariable needle)) =
  GroundSignature (NameLiteral replacement).
Proof.
  intros; simpl; rewrite Nat.eqb_refl; reflexivity.
Qed.

(** Collection pattern dispatch is typed by its *element* category.  The
    enclosing constructor's result sort may be closed while an embedded
    element admits object variables, or vice versa.  Structural element
    matching is present in either case.  This is the generator obligation for
    unordered collection matching, not a claim that a closed category can
    contain an implicit variable constructor. *)
Definition collection_variable_case
    (_owner element : CategoryDecl) : bool :=
  synthesize_variable element.

Definition collection_structural_case
    (_owner _element : CategoryDecl) : bool := true.

Theorem closed_owner_keeps_open_element_pattern_variables :
  forall owner element,
    collection_variable_case
      (elaborate (NoAdmit owner)) (elaborate (Plain element)) = true.
Proof. reflexivity. Qed.

Theorem closed_element_emits_no_implicit_pattern_variable_case :
  forall owner element,
    collection_variable_case
      (elaborate (Plain owner)) (elaborate (NoAdmit element)) = false /\
    collection_variable_case
      (elaborate (NoAdmit owner)) (elaborate (NoAdmit element)) = false.
Proof. intros; split; reflexivity. Qed.

Theorem closed_element_still_emits_structural_collection_matching :
  forall owner element,
    collection_structural_case
      (elaborate (NoAdmit owner)) (elaborate (NoAdmit element)) = true.
Proof. reflexivity. Qed.

(** The generated API is [ground.match_pattern(pattern)].  An unordered
    collection's variable element must pass its claimed ground element as the
    receiver; reversing the pair cannot produce the pattern's binding. *)
Definition match_name (ground pattern : OpenName)
    : option (nat * OpenName) :=
  match pattern with
  | NameVariable binder => Some (binder, ground)
  | NameLiteral expected =>
      match ground with
      | NameLiteral actual =>
          if Nat.eqb actual expected then Some (0, ground) else None
      | NameVariable _ => None
      end
  end.

Theorem collection_variable_claim_binds_the_ground_element :
  forall binder value,
    match_name (NameLiteral value) (NameVariable binder) =
      Some (binder, NameLiteral value).
Proof. reflexivity. Qed.

Theorem reversing_collection_match_arguments_loses_the_binding :
  forall binder value,
    match_name (NameVariable binder) (NameLiteral value) = None.
Proof. reflexivity. Qed.

End NoAdmitTypeProjection.
