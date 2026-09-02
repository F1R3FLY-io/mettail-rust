From Stdlib Require Import Bool List.
Import ListNotations.

(** A generated category has one of two semantic roles.  Object categories are
    terms of the specified language.  Data categories are closed structural
    nonterminals used to represent metasyntax inside those terms. *)
Inductive CategoryRole : Type :=
| Object
| Data.

(** Code generation is partitioned by capability rather than by reachability
    accidents.  [StructuralLifecycle] is the complete syntax-tree graph used by
    parsing, display, comparison, hashing, clone, drop, and dedicated structural
    projections.  [SemanticTransit] is the induced object-language graph used by
    substitution, normalization, matching, and executable backends.

    A closed data node is therefore a semantic boundary.  A dedicated
    structural projection may cross that boundary and schedule an explicitly
    embedded object payload, but a generic object-language endomorphism may not
    silently acquire semantics for the metasyntax surrounding that payload. *)
Inductive Capability : Type :=
| ParseRoot
| StructuralLifecycle
| SemanticTransit
| SemanticRoot
| VariableCarrier.

Definition has_capability (role : CategoryRole) (capability : Capability) : bool :=
  match capability with
  | ParseRoot | StructuralLifecycle => true
  | SemanticTransit | SemanticRoot | VariableCarrier =>
      match role with
      | Object => true
      | Data => false
      end
  end.

Record Category : Type := category {
  category_id : nat;
  category_role : CategoryRole
}.

Definition supports (capability : Capability) (entry : Category) : bool :=
  has_capability (category_role entry) capability.

Definition project (capability : Capability) (categories : list Category) : list Category :=
  filter (supports capability) categories.

(** Declared constructor fields form the structural traversal graph. *)
Record FieldEdge : Type := field_edge {
  field_source : Category;
  field_target : Category
}.

Definition structural_edge_is_traversable
    (categories : list Category) (edge : FieldEdge) : Prop :=
  In (field_source edge) (project StructuralLifecycle categories) /\
  In (field_target edge) (project StructuralLifecycle categories).

Definition semantic_edge
    (categories : list Category) (edge : FieldEdge) : Prop :=
  In (field_source edge) (project SemanticTransit categories) /\
  In (field_target edge) (project SemanticTransit categories).

(** An object-to-data constructor field is retained structurally but marks an
    explicit boundary of the generic semantic graph. *)
Definition semantic_boundary_edge
    (categories : list Category) (edge : FieldEdge) : Prop :=
  In (field_source edge) (project SemanticTransit categories) /\
  In (field_target edge) (project StructuralLifecycle categories) /\
  category_role (field_target edge) = Data.

Theorem parse_projection_is_identity :
  forall categories, project ParseRoot categories = categories.
Proof.
  induction categories as [| entry rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Theorem lifecycle_projection_is_identity :
  forall categories, project StructuralLifecycle categories = categories.
Proof.
  induction categories as [| entry rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Theorem object_categories_are_exactly_semantic_transit_nodes :
  forall categories entry,
    In entry (project SemanticTransit categories) <->
    In entry categories /\ category_role entry = Object.
Proof.
  intros categories entry.
  unfold project, supports.
  rewrite filter_In.
  destruct (category_role entry); simpl; intuition discriminate.
Qed.

Theorem every_declared_field_edge_remains_structurally_traversable :
  forall categories edge,
    In (field_source edge) categories ->
    In (field_target edge) categories ->
    structural_edge_is_traversable categories edge.
Proof.
  intros categories edge Hsource Htarget.
  unfold structural_edge_is_traversable.
  rewrite lifecycle_projection_is_identity.
  split; assumption.
Qed.

Theorem object_categories_are_exactly_semantic_roots :
  forall categories entry,
    In entry (project SemanticRoot categories) <->
    In entry categories /\ category_role entry = Object.
Proof.
  intros categories entry.
  unfold project, supports.
  rewrite filter_In.
  destruct (category_role entry); simpl; intuition discriminate.
Qed.

Theorem object_categories_are_exactly_variable_carriers :
  forall categories entry,
    In entry (project VariableCarrier categories) <->
    In entry categories /\ category_role entry = Object.
Proof.
  intros categories entry.
  unfold project, supports.
  rewrite filter_In.
  destruct (category_role entry); simpl; intuition discriminate.
Qed.

Theorem data_is_structural_but_never_semantic_transit :
  forall categories entry,
    In entry categories ->
    category_role entry = Data ->
    In entry (project StructuralLifecycle categories) /\
    ~ In entry (project SemanticTransit categories) /\
    ~ In entry (project SemanticRoot categories).
Proof.
  intros categories entry Hin Hdata.
  split.
  - rewrite lifecycle_projection_is_identity. exact Hin.
  - split.
    + rewrite object_categories_are_exactly_semantic_transit_nodes.
      intros [_ Hobject]. rewrite Hdata in Hobject. discriminate.
    + rewrite object_categories_are_exactly_semantic_roots.
      intros [_ Hobject]. rewrite Hdata in Hobject. discriminate.
Qed.

Theorem semantic_edges_have_only_object_endpoints :
  forall categories edge,
    semantic_edge categories edge ->
    category_role (field_source edge) = Object /\
    category_role (field_target edge) = Object.
Proof.
  intros categories edge [Hsource Htarget].
  rewrite object_categories_are_exactly_semantic_transit_nodes in Hsource.
  rewrite object_categories_are_exactly_semantic_transit_nodes in Htarget.
  intuition.
Qed.

Theorem declared_object_to_data_edge_is_a_semantic_boundary :
  forall categories edge,
    In (field_source edge) categories ->
    In (field_target edge) categories ->
    category_role (field_source edge) = Object ->
    category_role (field_target edge) = Data ->
    semantic_boundary_edge categories edge.
Proof.
  intros categories edge Hsource Htarget Hsource_role Htarget_role.
  unfold semantic_boundary_edge.
  split.
  - rewrite object_categories_are_exactly_semantic_transit_nodes.
    split; assumption.
  - split.
    + rewrite lifecycle_projection_is_identity. exact Htarget.
    + exact Htarget_role.
Qed.

Theorem generic_semantics_cannot_cross_a_data_boundary :
  forall categories edge,
    semantic_boundary_edge categories edge ->
    ~ semantic_edge categories edge.
Proof.
  intros categories edge [_ [_ Hdata]] Hsemantic.
  pose proof (semantic_edges_have_only_object_endpoints categories edge Hsemantic)
    as [_ Htarget].
  rewrite Hdata in Htarget. discriminate.
Qed.

Theorem data_is_never_a_substitution_replacement_axis :
  forall categories entry,
    category_role entry = Data ->
    ~ In entry (project VariableCarrier categories).
Proof.
  intros categories entry Hdata.
  rewrite object_categories_are_exactly_variable_carriers.
  intros [_ Hobject]. rewrite Hdata in Hobject. discriminate.
Qed.

Theorem semantic_root_projection_is_idempotent :
  forall categories,
    project SemanticRoot (project SemanticRoot categories) =
    project SemanticRoot categories.
Proof.
  induction categories as [| entry rest IH]; simpl; [reflexivity |].
  destruct entry as [id role].
  destruct role; simpl; rewrite IH; reflexivity.
Qed.

Theorem variable_projection_equals_semantic_root_projection :
  forall categories,
    project VariableCarrier categories = project SemanticRoot categories.
Proof.
  induction categories as [| entry rest IH]; simpl; [reflexivity |].
  destruct entry as [id role].
  destruct role; simpl; rewrite IH; reflexivity.
Qed.

Theorem semantic_transit_projection_equals_semantic_root_projection :
  forall categories,
    project SemanticTransit categories = project SemanticRoot categories.
Proof.
  induction categories as [| entry rest IH]; simpl; [reflexivity |].
  destruct entry as [id role].
  destruct role; simpl; rewrite IH; reflexivity.
Qed.

(** Object-language endomorphisms act on a constructor with a closed data
    field as the product functor [D * -]: the data coefficient is preserved
    exactly while the object child is transformed.  The pointwise statements
    below avoid any extensionality axiom. *)
Definition coefficient_map {D X Y : Type}
    (f : X -> Y) (value : D * X) : D * Y :=
  let '(coefficient, child) := value in (coefficient, f child).

Theorem coefficient_map_preserves_data :
  forall (D X Y : Type) (f : X -> Y) (value : D * X),
    fst (coefficient_map f value) = fst value.
Proof.
  intros D X Y f [coefficient child]. reflexivity.
Qed.

Theorem coefficient_map_identity :
  forall (D X : Type) (value : D * X),
    coefficient_map (fun child => child) value = value.
Proof.
  intros D X [coefficient child]. reflexivity.
Qed.

Theorem coefficient_map_composition :
  forall (D X Y Z : Type) (f : X -> Y) (g : Y -> Z) (value : D * X),
    coefficient_map g (coefficient_map f value) =
    coefficient_map (fun child => g (f child)) value.
Proof.
  intros D X Y Z f g [coefficient child]. reflexivity.
Qed.

(** Code generation chooses a field plan from the target category role.  Data
    targets are immutable coefficients, never generic semantic work items. *)
Inductive SemanticFieldPlan : Type :=
| RecurseObject
| PreserveCoefficient.

Definition semantic_field_plan (target : Category) : SemanticFieldPlan :=
  match category_role target with
  | Object => RecurseObject
  | Data => PreserveCoefficient
  end.

Theorem data_fields_compile_to_coefficients :
  forall target,
    category_role target = Data ->
    semantic_field_plan target = PreserveCoefficient.
Proof.
  intros [id role] Hdata. simpl in Hdata. subst role. reflexivity.
Qed.

Theorem object_fields_compile_to_recursive_work :
  forall target,
    category_role target = Object ->
    semantic_field_plan target = RecurseObject.
Proof.
  intros [id role] Hobject. simpl in Hobject. subst role. reflexivity.
Qed.

(** Dovetail's generic reconstruction is an inverse to the object-language
    lowering only where every recursively represented field remains in the
    semantic graph.  A data coefficient is deliberately opaque, so accepting
    it as generically reconstructible would claim an inverse that the lowering
    image does not encode. *)
Definition generically_reconstructible (target : Category) : bool :=
  match semantic_field_plan target with
  | RecurseObject => true
  | PreserveCoefficient => false
  end.

Theorem data_boundaries_are_not_generically_reconstructible :
  forall target,
    category_role target = Data ->
    generically_reconstructible target = false.
Proof.
  intros target Hdata.
  unfold generically_reconstructible.
  rewrite data_fields_compile_to_coefficients by exact Hdata.
  reflexivity.
Qed.

(** Prediction automata are an exported tooling projection, not part of the
    recognizer's operational table.  The generated artifact therefore retains
    every declared category in [recognizer_categories] while exporting
    prediction metadata only for object-language roots. *)
Record GeneratedParserArtifact : Type := {
  recognizer_categories : list Category;
  prediction_categories : list Category
}.

Definition parser_artifact (categories : list Category) : GeneratedParserArtifact :=
  {| recognizer_categories := project ParseRoot categories;
     prediction_categories := project SemanticRoot categories |}.

Theorem prediction_export_pruning_preserves_recognizer :
  forall categories,
    recognizer_categories (parser_artifact categories) = categories.
Proof.
  intro categories.
  unfold parser_artifact. simpl.
  apply parse_projection_is_identity.
Qed.

Theorem data_categories_have_no_exported_prediction :
  forall categories category,
    In category categories ->
    category_role category = Data ->
    ~ In category (prediction_categories (parser_artifact categories)).
Proof.
  intros categories category Hin Hdata.
  unfold parser_artifact. simpl.
  intro Hprojected.
  apply object_categories_are_exactly_semantic_roots in Hprojected.
  destruct Hprojected as [_ Hobject].
  rewrite Hdata in Hobject. discriminate.
Qed.

Theorem object_categories_keep_exported_prediction :
  forall categories category,
    In category categories ->
    category_role category = Object ->
    In category (prediction_categories (parser_artifact categories)).
Proof.
  intros categories category Hin Hobject.
  unfold parser_artifact. simpl.
  apply object_categories_are_exactly_semantic_roots.
  split; assumption.
Qed.

Print Assumptions parse_projection_is_identity.
Print Assumptions lifecycle_projection_is_identity.
Print Assumptions object_categories_are_exactly_semantic_transit_nodes.
Print Assumptions every_declared_field_edge_remains_structurally_traversable.
Print Assumptions object_categories_are_exactly_semantic_roots.
Print Assumptions object_categories_are_exactly_variable_carriers.
Print Assumptions data_is_structural_but_never_semantic_transit.
Print Assumptions semantic_edges_have_only_object_endpoints.
Print Assumptions declared_object_to_data_edge_is_a_semantic_boundary.
Print Assumptions generic_semantics_cannot_cross_a_data_boundary.
Print Assumptions data_is_never_a_substitution_replacement_axis.
Print Assumptions semantic_root_projection_is_idempotent.
Print Assumptions variable_projection_equals_semantic_root_projection.
Print Assumptions semantic_transit_projection_equals_semantic_root_projection.
Print Assumptions coefficient_map_preserves_data.
Print Assumptions coefficient_map_identity.
Print Assumptions coefficient_map_composition.
Print Assumptions data_fields_compile_to_coefficients.
Print Assumptions object_fields_compile_to_recursive_work.
Print Assumptions data_boundaries_are_not_generically_reconstructible.
Print Assumptions prediction_export_pruning_preserves_recognizer.
Print Assumptions data_categories_have_no_exported_prediction.
Print Assumptions object_categories_keep_exported_prediction.
