(** Rich resolved source nodes and the existing semantic-image term checks.

    This file models the TERM/VARIABLE slice shared by validate_program and
    validate_judgment_program in grammar-core/src/theory_image.rs.  Its
    expected_form is the constant-depth field projection already performed
    by expected_term_form and compile_term_nodes, not a new production
    compiler, evaluator, or normalizer.  The paired scans express acceptance,
    not diagnostic precedence, allocation cost, or resource completeness.

    The source is AuthoredSourceExecution's rich resolved arena.  Slot,
    Apply, and multi-source Map are the actual image alternatives.  Apply
    REUSES AuthoredTermConstruction.ApplyShape, including exact typed literal
    payloads, function-sort IDs, ordered arguments, binder slots, remainder,
    and PathMap mode.  The old erased MapOperator/Zip proof is not reused as
    evidence for these richer forms.

    Boundary: a caller must supply the exact owner-bound resolved source and
    sort-table projection.  Raw names are not present in this model.  Rust's
    language.validate, CompileContext, ImageSourceContext/index_names and
    validate_sorts/validate_constructors establish declaration membership,
    unique dense name resolution, source typing and the full sort metadata.
    Their implementation-to-model refinement is not proved by assuming a
    resolved arena.  In particular OtherSort erases function internals; we
    preserve the EXACT function-sort ID but do not reconstruct its typing.
    Natural-number IDs model successfully admitted finite Rust indices;
    u32 conversions and admission/resource limits remain concrete guards.

    Successful checks imply exact source fields and bounds, then discharge
    the source lookup/SourceApply premises of the existing construction
    TaskStep.  Map's nonempty-parameter and collection-target runtime guards
    remain explicit: validate_term_references checks nonempty SOURCES, not
    those two guards.  Physical e-class interpretation, canonicalization,
    readback and insertion retain AuthoredTermConstruction's local contracts.
    No whole-builder soundness premise or source-candidate assumption is used.
    Rule owners, roots, ordered premises, fingerprints and costs are checked
    elsewhere; this term-arena check alone is not a complete image validator.
*)

From Stdlib Require Import List Bool PeanoNat ZArith Lia.
From RuntimeGrammar Require Import AuthoredTermConstruction.
Import ListNotations.

Module AuthoredSourceImage.
Module T := AuthoredTermConstruction.
Module S := T.S.
Module Core := T.Core.
Module K := T.K.
Module Canon := T.Canon.

Inductive ImageForm :=
| ImageSlot (variable : Core.VariableId)
| ImageApply (application : T.ApplyShape)
| ImageMap (sources : list Core.TermId) (parameters : list Core.VariableId)
    (body : Core.TermId).

Record ImageNode := { image_sort : Core.SortId; image_form : ImageForm }.
Record ImageVariable := {
  image_variable_id : Core.VariableId;
  image_variable_sort : Core.SortId;
  image_variable_role : Core.VariableRole
}.
Record TermArenaImage := {
  image_variables : list ImageVariable;
  image_terms : list ImageNode
}.

(** Exact equality is the model of the existing Rust PartialEq comparisons.
    It does not replace a typed literal with its printed form or evaluation. *)
Definition literal_eq_dec : forall (left right : S.Literal), {left = right} + {left <> right}.
Proof.
  decide equality; try apply Z.eq_dec; try apply Nat.eq_dec; try apply Bool.bool_dec;
    apply list_eq_dec; apply Nat.eq_dec.
Defined.
Definition collection_kind_eq_dec : forall (left right : K.RuntimeCollectionKind),
    {left = right} + {left <> right}.
Proof. decide equality. Defined.
Definition pathmap_mode_eq_dec : forall (left right : Canon.PathMapMode),
    {left = right} + {left <> right}.
Proof. decide equality. Defined.
Definition variable_role_eq_dec : forall (left right : Core.VariableRole),
    {left = right} + {left <> right}.
Proof. decide equality. Defined.
Definition operator_eq_dec : forall (left right : T.Operator), {left = right} + {left <> right}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply collection_kind_eq_dec;
    apply literal_eq_dec.
Defined.
Definition application_eq_dec : forall (left right : T.ApplyShape), {left = right} + {left <> right}.
Proof.
  decide equality; try apply operator_eq_dec;
    try (apply list_eq_dec; apply Nat.eq_dec);
    decide equality; try apply Nat.eq_dec; apply pathmap_mode_eq_dec.
Defined.
Definition image_form_eq_dec : forall (left right : ImageForm), {left = right} + {left <> right}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply application_eq_dec;
    apply list_eq_dec; apply Nat.eq_dec.
Defined.
Definition image_node_eq_dec : forall (left right : ImageNode), {left = right} + {left <> right}.
Proof. decide equality; [apply image_form_eq_dec|apply Nat.eq_dec]. Defined.
Definition image_variable_eq_dec : forall (left right : ImageVariable), {left = right} + {left <> right}.
Proof. decide equality; try apply Nat.eq_dec; apply variable_role_eq_dec. Defined.

Definition exact_eqb {A : Type} (decide : forall left right : A, {left = right} + {left <> right})
    (left right : A) := if decide left right then true else false.
Lemma exact_eqb_spec : forall (A : Type) decide (left right : A),
    exact_eqb decide left right = true <-> left = right.
Proof. intros. unfold exact_eqb. destruct (decide left right); split; congruence. Qed.

Definition term_sort_resolved (sorts : T.SortTable) arena root :=
  match nth_error (S.terms arena) root with
  | Some node => S.node_sort node <? length sorts
  | None => false
  end.
Definition variable_sort_resolved (sorts : T.SortTable) arena variable :=
  match nth_error (S.variables arena) variable with
  | Some declaration => Core.variable_sort declaration <? length sorts
  | None => false
  end.

Definition expected_form (sorts : T.SortTable) (arena : S.Arena) (node : S.TermNode)
    : option ImageForm :=
  let sort := S.node_sort node in
  match S.node_form node with
  | S.SourceVariable variable => Some (ImageSlot variable)
  | S.SourceConstructor constructor arguments =>
      Some (ImageApply (T.shape (T.ConstructorOperator constructor) arguments [] None None))
  | S.SourceAbstraction binder body =>
      Some (ImageApply (T.shape (T.AbstractionOperator sort) [body] [binder] None None))
  | S.SourceSubstitution abstraction argument =>
      match nth_error (S.terms arena) abstraction with
      | Some function_node =>
          if S.node_sort function_node <? length sorts then
            Some (ImageApply (T.shape
              (T.SubstitutionOperator sort (S.node_sort function_node))
              [abstraction; argument] [] None None))
          else None
      | None => None
      end
  | S.SourceCollection elements remainder mode =>
      match nth_error sorts sort with
      | Some (T.CollectionSort kind key element) =>
          if element <? length sorts then
            Some (ImageApply (T.shape (T.CollectionOperator sort element kind)
              elements [] remainder mode))
          else None
      | _ => None
      end
  | S.SourceMap sources parameters body =>
      if forallb (variable_sort_resolved sorts arena) parameters &&
         forallb (term_sort_resolved sorts arena) sources
      then Some (ImageMap sources parameters body) else None
  | S.SourceProduct factors =>
      Some (ImageApply (T.shape (T.ProductOperator sort) factors [] None None))
  | S.SourceLiteral literal =>
      Some (ImageApply (T.shape (T.LiteralOperator sort literal) [] [] None None))
  end.

Definition expected_node sorts arena node : option ImageNode :=
  if S.node_sort node <? length sorts then
    option_map (fun form => {| image_sort := S.node_sort node; image_form := form |})
      (expected_form sorts arena node)
  else None.

Definition source_references form :=
  match form with
  | S.SourceVariable _ | S.SourceLiteral _ => []
  | S.SourceConstructor _ arguments => arguments
  | S.SourceAbstraction _ body => [body]
  | S.SourceSubstitution abstraction argument => [abstraction; argument]
  | S.SourceCollection elements _ _ => elements
  | S.SourceMap sources _ body => sources ++ [body]
  | S.SourceProduct factors => factors
  end.
Definition source_slots form :=
  match form with
  | S.SourceVariable variable => [variable]
  | S.SourceAbstraction binder _ => [binder]
  | S.SourceCollection _ (Some remainder) _ => [remainder]
  | S.SourceMap _ parameters _ => parameters
  | _ => []
  end.
Definition image_references form :=
  match form with
  | ImageSlot _ => []
  | ImageApply application => T.apply_arguments application
  | ImageMap sources _ body => sources ++ [body]
  end.
Definition image_slots form :=
  match form with
  | ImageSlot variable => [variable]
  | ImageApply application => T.apply_slots application ++
      match T.apply_remainder application with None => [] | Some remainder => [remainder] end
  | ImageMap _ parameters _ => parameters
  end.

Definition nonempty_map_sources form :=
  match form with ImageMap [] _ _ => false | _ => true end.
Definition check_references owner variable_count form :=
  nonempty_map_sources form &&
  (forallb (fun reference => reference <? owner) (image_references form) &&
   forallb (fun variable => variable <? variable_count) (image_slots form)).

Definition check_node sorts arena owner source actual :=
  match expected_node sorts arena source with
  | Some expected => exact_eqb image_node_eq_dec actual expected &&
      check_references owner (length (S.variables arena)) (image_form actual)
  | None => false
  end.

Fixpoint check_nodes_from sorts arena owner (source : list S.TermNode) (actual : list ImageNode) :=
  match source, actual with
  | [], [] => true
  | source_node :: sources, actual_node :: actuals =>
      check_node sorts arena owner source_node actual_node &&
      check_nodes_from sorts arena (S owner) sources actuals
  | _, _ => false
  end.

Definition check_variable (sorts : T.SortTable) owner (source : Core.VariableDecl) actual :=
  exact_eqb image_variable_eq_dec actual
    {| image_variable_id := owner; image_variable_sort := Core.variable_sort source;
       image_variable_role := Core.variable_role source |} &&
  (Core.variable_sort source <? length sorts).

Fixpoint check_variables_from sorts owner (source : list Core.VariableDecl) (actual : list ImageVariable) :=
  match source, actual with
  | [], [] => true
  | source_variable :: sources, actual_variable :: actuals =>
      check_variable sorts owner source_variable actual_variable &&
      check_variables_from sorts (S owner) sources actuals
  | _, _ => false
  end.

Definition check_term_arena sorts source actual :=
  check_variables_from sorts 0 (S.variables source) (image_variables actual) &&
  check_nodes_from sorts source 0 (S.terms source) (image_terms actual).

Lemma expected_node_fields : forall sorts arena source actual,
    expected_node sorts arena source = Some actual ->
    image_sort actual = S.node_sort source /\ S.node_sort source < length sorts /\
    expected_form sorts arena source = Some (image_form actual).
Proof.
  intros sorts arena source actual H. unfold expected_node in H.
  destruct (S.node_sort source <? length sorts) eqn:Hsort; try discriminate.
  destruct (expected_form sorts arena source) eqn:Hform; try discriminate.
  inversion H; subst. simpl. apply Nat.ltb_lt in Hsort. auto.
Qed.

(** Ordered references and slots are preserved, not merely their sets. *)
Theorem expected_form_preserves_ordered_references_and_slots : forall sorts arena source form,
    expected_form sorts arena source = Some form ->
    image_references form = source_references (S.node_form source) /\
    image_slots form = source_slots (S.node_form source).
Proof.
  intros sorts arena [sort source] form H. destruct source; cbn [expected_form S.node_form S.node_sort] in H;
    try (inversion H; subst; split; reflexivity).
  - destruct (nth_error (S.terms arena) abstraction); try discriminate.
    destruct (S.node_sort t <? length sorts); try discriminate.
    inversion H; subst. split; reflexivity.
  - destruct (nth_error sorts sort) as [declaration|]; try discriminate.
    destruct declaration; try discriminate.
    destruct (element <? length sorts); try discriminate.
    inversion H; subst. split; [reflexivity|]. destruct remainder; reflexivity.
  - destruct (forallb (variable_sort_resolved sorts arena) parameters &&
      forallb (term_sort_resolved sorts arena) sources); try discriminate.
    inversion H; subst. split; reflexivity.
Qed.

Definition ConstructionCase sorts arena root source form : Prop :=
  match form with
  | ImageSlot variable => S.node_form source = S.SourceVariable variable
  | ImageApply application => T.SourceApply sorts arena root application
  | ImageMap sources parameters body => S.node_form source = S.SourceMap sources parameters body
  end.

Theorem expected_form_supplies_existing_construction_case : forall sorts arena root source form,
    nth_error (S.terms arena) root = Some source ->
    expected_form sorts arena source = Some form ->
    ConstructionCase sorts arena root source form.
Proof.
  intros sorts arena root [sort source] form Hsource Hform. destruct source;
    cbn [expected_form S.node_form S.node_sort] in Hform.
  - inversion Hform; subst. reflexivity.
  - inversion Hform; subst. simpl. econstructor; eauto.
  - inversion Hform; subst. simpl. econstructor; eauto.
  - destruct (nth_error (S.terms arena) abstraction) eqn:Hfunction; try discriminate.
    destruct (S.node_sort t <? length sorts); try discriminate.
    inversion Hform; subst. simpl. econstructor; eauto.
  - destruct (nth_error sorts sort) as [declaration|] eqn:Hsort; try discriminate.
    destruct declaration; try discriminate.
    destruct (element <? length sorts); try discriminate.
    inversion Hform; subst. simpl. econstructor; eauto.
  - destruct (forallb (variable_sort_resolved sorts arena) parameters &&
      forallb (term_sort_resolved sorts arena) sources); try discriminate.
    inversion Hform; subst. reflexivity.
  - inversion Hform; subst. simpl. econstructor; eauto.
  - inversion Hform; subst. simpl. econstructor; eauto.
Qed.

Lemma check_references_sound : forall owner count form,
    check_references owner count form = true ->
    nonempty_map_sources form = true /\
    Forall (Core.earlier owner) (image_references form) /\
    Forall (fun variable => variable < count) (image_slots form).
Proof.
  intros owner count form H. unfold check_references in H.
  apply andb_true_iff in H as [Hnonempty H]. apply andb_true_iff in H as [Hrefs Hslots].
  split; [exact Hnonempty|]. split; apply Forall_forall; intros reference Hin;
    apply Nat.ltb_lt; [apply (proj1 (forallb_forall _ _) Hrefs)|apply (proj1 (forallb_forall _ _) Hslots)];
    assumption.
Qed.

Lemma check_node_sound : forall sorts arena owner source actual,
    check_node sorts arena owner source actual = true ->
    expected_node sorts arena source = Some actual /\
    check_references owner (length (S.variables arena)) (image_form actual) = true.
Proof.
  intros sorts arena owner source actual H. unfold check_node in H.
  destruct (expected_node sorts arena source) eqn:Hexpect; try discriminate.
  apply andb_true_iff in H as [Heq Hrefs]. apply exact_eqb_spec in Heq. subst. auto.
Qed.

Lemma check_variable_sound : forall sorts owner source actual,
    check_variable sorts owner source actual = true ->
    image_variable_id actual = owner /\
    image_variable_sort actual = Core.variable_sort source /\
    image_variable_role actual = Core.variable_role source /\
    Core.variable_sort source < length sorts.
Proof.
  intros sorts owner source actual H. unfold check_variable in H.
  apply andb_true_iff in H as [Heq Hsort]. apply exact_eqb_spec in Heq. subst.
  apply Nat.ltb_lt in Hsort. simpl. auto.
Qed.

Lemma checked_nodes_have_exact_length : forall sorts arena owner source actual,
    check_nodes_from sorts arena owner source actual = true -> length source = length actual.
Proof.
  intros sorts arena owner source. revert owner.
  induction source; intros owner [|node actual] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ Htail]. simpl. f_equal. eapply IHsource; eauto.
Qed.

Lemma checked_variables_have_exact_length : forall sorts owner source actual,
    check_variables_from sorts owner source actual = true -> length source = length actual.
Proof.
  intros sorts owner source. revert owner.
  induction source; intros owner [|node actual] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ Htail]. simpl. f_equal. eapply IHsource; eauto.
Qed.

Lemma checked_nodes_lookup : forall sorts arena owner source actual,
    check_nodes_from sorts arena owner source actual = true -> forall offset node,
    nth_error actual offset = Some node ->
    exists source_node, nth_error source offset = Some source_node /\
      expected_node sorts arena source_node = Some node /\
      check_references (owner + offset) (length (S.variables arena)) (image_form node) = true.
Proof.
  intros sorts arena owner source. revert owner.
  induction source as [|source_node sources IH]; intros owner [|actual_node actual] Hcheck offset node Hnode;
    simpl in Hcheck; try discriminate.
  - destruct offset; discriminate.
  - apply andb_true_iff in Hcheck as [Hhead Htail].
    destruct offset as [|offset].
    + simpl in Hnode. inversion Hnode; subst. exists source_node. split; [reflexivity|].
      rewrite Nat.add_0_r. now apply check_node_sound.
    + simpl in Hnode. destruct (IH (S owner) actual Htail offset node Hnode)
        as [found [Hfound [Hexpected Hrefs]]].
      exists found. split; [exact Hfound|]. split; [exact Hexpected|].
      replace (owner + S offset) with (S owner + offset) by lia. exact Hrefs.
Qed.

Lemma checked_variables_lookup : forall sorts owner source actual,
    check_variables_from sorts owner source actual = true -> forall offset variable,
    nth_error actual offset = Some variable ->
    exists declaration, nth_error source offset = Some declaration /\
      image_variable_id variable = owner + offset /\
      image_variable_sort variable = Core.variable_sort declaration /\
      image_variable_role variable = Core.variable_role declaration /\
      Core.variable_sort declaration < length sorts.
Proof.
  intros sorts owner source. revert owner.
  induction source as [|declaration sources IH]; intros owner [|actual_variable actual] Hcheck offset variable Hvariable;
    simpl in Hcheck; try discriminate.
  - destruct offset; discriminate.
  - apply andb_true_iff in Hcheck as [Hhead Htail].
    destruct offset as [|offset].
    + simpl in Hvariable. inversion Hvariable; subst. exists declaration. split; [reflexivity|].
      rewrite Nat.add_0_r. now apply check_variable_sound.
    + simpl in Hvariable. destruct (IH (S owner) actual Htail offset variable Hvariable)
        as [found [Hfound [Hid Hfields]]].
      exists found. split; [exact Hfound|]. split; [lia|exact Hfields].
Qed.

Theorem checked_term_arena_has_exact_lengths : forall sorts arena image,
    check_term_arena sorts arena image = true ->
    length (image_variables image) = length (S.variables arena) /\
    length (image_terms image) = length (S.terms arena).
Proof.
  intros sorts arena image H. apply andb_true_iff in H as [Hvars Hterms].
  split; symmetry; [eapply checked_variables_have_exact_length|eapply checked_nodes_have_exact_length]; eauto.
Qed.

Theorem checked_term_arena_has_exact_variables : forall sorts arena image index variable,
    check_term_arena sorts arena image = true ->
    nth_error (image_variables image) index = Some variable ->
    exists declaration, nth_error (S.variables arena) index = Some declaration /\
      image_variable_id variable = index /\
      image_variable_sort variable = Core.variable_sort declaration /\
      image_variable_role variable = Core.variable_role declaration /\
      Core.variable_sort declaration < length sorts.
Proof.
  intros sorts arena image index variable Hcheck Hvariable.
  apply andb_true_iff in Hcheck as [Hvars _].
  exact (checked_variables_lookup sorts 0 _ _ Hvars index variable Hvariable).
Qed.

Theorem checked_term_arena_exposes_exact_construction_view : forall sorts arena image root node,
    check_term_arena sorts arena image = true -> nth_error (image_terms image) root = Some node ->
    exists source,
      nth_error (S.terms arena) root = Some source /\
      image_sort node = S.node_sort source /\ image_sort node < length sorts /\
      ConstructionCase sorts arena root source (image_form node) /\
      image_references (image_form node) = source_references (S.node_form source) /\
      image_slots (image_form node) = source_slots (S.node_form source) /\
      nonempty_map_sources (image_form node) = true /\
      Forall (Core.earlier root) (image_references (image_form node)) /\
      Forall (fun variable => variable < length (image_variables image)) (image_slots (image_form node)).
Proof.
  intros sorts arena image root node Hcheck Hnode.
  pose proof (checked_term_arena_has_exact_lengths _ _ _ Hcheck) as [Hvarslen _].
  apply andb_true_iff in Hcheck as [_ Hterms].
  destruct (checked_nodes_lookup sorts arena 0 _ _ Hterms root node Hnode)
    as [source [Hsource [Hexpected Hrefs]]].
  destruct (expected_node_fields _ _ _ _ Hexpected) as [Hsort [Hbound Hform]].
  pose proof (expected_form_supplies_existing_construction_case _ _ _ _ _ Hsource Hform) as Hcase.
  destruct (expected_form_preserves_ordered_references_and_slots _ _ _ _ Hform) as [Hedges Hslots].
  destruct (check_references_sound _ _ _ Hrefs) as [Hnonempty [Hback Hvariables]].
  exists source. rewrite Hvarslen. simpl in Hback. repeat split; auto; congruence.
Qed.

Theorem checked_term_arena_covers_every_source_node : forall sorts arena image root source,
    check_term_arena sorts arena image = true -> nth_error (S.terms arena) root = Some source ->
    exists node, nth_error (image_terms image) root = Some node /\
      expected_node sorts arena source = Some node.
Proof.
  intros sorts arena image root source Hcheck Hsource.
  pose proof (checked_term_arena_has_exact_lengths _ _ _ Hcheck) as [_ Hlength].
  assert (Hbound : root < length (image_terms image)).
  { rewrite Hlength. apply nth_error_Some. rewrite Hsource. discriminate. }
  destruct (nth_error (image_terms image) root) as [node|] eqn:Hnode.
  - exists node. split; [reflexivity|].
    apply andb_true_iff in Hcheck as [_ Hterms].
    destruct (checked_nodes_lookup sorts arena 0 _ _ Hterms root node Hnode)
      as [found [Hfound [Hexpected _]]]. congruence.
  - apply nth_error_None in Hnode. lia.
Qed.

(** Any unequal field change is refused for the same resolved source.  A
    permutation of IDENTICAL rows is not a different image and is not claimed
    to be detectable.  The theorem needs no hash injectivity premise. *)
Lemma checked_node_is_unique : forall sorts arena owner source left right,
    check_node sorts arena owner source left = true ->
    check_node sorts arena owner source right = true -> left = right.
Proof.
  intros. apply check_node_sound in H as [H _]. apply check_node_sound in H0 as [H0 _]. congruence.
Qed.

Lemma checked_nodes_are_unique : forall sorts arena owner source left right,
    check_nodes_from sorts arena owner source left = true ->
    check_nodes_from sorts arena owner source right = true -> left = right.
Proof.
  intros sorts arena owner source. revert owner.
  induction source; intros owner [|left lefts] [|right rights] Hl Hr; simpl in *; try discriminate;
    [reflexivity|].
  apply andb_true_iff in Hl as [Hl Hls]. apply andb_true_iff in Hr as [Hr Hrs].
  f_equal; [eapply checked_node_is_unique; eauto|eapply IHsource; eauto].
Qed.

Lemma checked_variables_are_unique : forall sorts owner source left right,
    check_variables_from sorts owner source left = true ->
    check_variables_from sorts owner source right = true -> left = right.
Proof.
  intros sorts owner source. revert owner.
  induction source; intros owner [|left lefts] [|right rights] Hl Hr; simpl in *; try discriminate;
    [reflexivity|].
  apply andb_true_iff in Hl as [Hl Hls]. apply andb_true_iff in Hr as [Hr Hrs].
  f_equal; [|eapply IHsource; eauto].
  unfold check_variable in Hl, Hr.
  apply andb_true_iff in Hl as [Hl _]. apply andb_true_iff in Hr as [Hr _].
  apply exact_eqb_spec in Hl. apply exact_eqb_spec in Hr. congruence.
Qed.

Theorem checked_term_arena_is_unique_for_fixed_source : forall sorts arena left right,
    check_term_arena sorts arena left = true -> check_term_arena sorts arena right = true -> left = right.
Proof.
  intros sorts arena [left_variables left_terms] [right_variables right_terms] Hl Hr.
  apply andb_true_iff in Hl as [Hlv Hlt]. apply andb_true_iff in Hr as [Hrv Hrt].
  simpl in *. f_equal; [eapply checked_variables_are_unique|eapply checked_nodes_are_unique]; eauto.
Qed.

Theorem changed_term_arena_is_rejected : forall sorts arena accepted changed,
    check_term_arena sorts arena accepted = true -> accepted <> changed ->
    check_term_arena sorts arena changed = false.
Proof.
  intros sorts arena accepted changed Haccepted Hchanged.
  destruct (check_term_arena sorts arena changed) eqn:Hcheck; [|reflexivity].
  exfalso. apply Hchanged. eapply checked_term_arena_is_unique_for_fixed_source; eauto.
Qed.

(** These are the existing Evaluate branches, not a second term machine.
    FinishApply/FinishMapSources/FinishMapBodies reuse their checked model. *)
Theorem checked_slot_dispatch_is_existing_construction_step :
    forall sorts arena image root sort variable observed activation environment rest values value,
    check_term_arena sorts arena image = true ->
    nth_error (image_terms image) root = Some {| image_sort := sort; image_form := ImageSlot variable |} ->
    S.lookup activation variable environment = Some value ->
    T.TaskStep sorts observed arena activation (T.Evaluate root environment :: rest) values
      rest (values ++ [value]).
Proof.
  intros sorts arena image root sort variable observed activation environment rest values value Hcheck Hnode Hlookup.
  destruct (checked_term_arena_exposes_exact_construction_view _ _ _ _ _ Hcheck Hnode)
    as [[source_sort source_form] [Hsource [Hsort [_ [Hcase _]]]]].
  simpl in *. unfold ConstructionCase in Hcase. simpl in Hcase. subst source_form source_sort.
  econstructor; eauto.
Qed.

Theorem checked_apply_dispatch_is_existing_construction_step :
    forall sorts arena image root sort application observed activation environment rest values,
    check_term_arena sorts arena image = true ->
    nth_error (image_terms image) root = Some {| image_sort := sort; image_form := ImageApply application |} ->
    T.TaskStep sorts observed arena activation (T.Evaluate root environment :: rest) values
      (T.evaluate_requests (T.requests environment (T.apply_arguments application)) ++
        T.FinishApply application environment (length values) :: rest) values.
Proof.
  intros sorts arena image root sort application observed activation environment rest values Hcheck Hnode.
  destruct (checked_term_arena_exposes_exact_construction_view _ _ _ _ _ Hcheck Hnode)
    as [source [_ [_ [_ [Hcase _]]]]].
  apply T.step_expand_apply. exact Hcase.
Qed.

Theorem checked_map_dispatch_is_existing_construction_step :
    forall sorts arena image root target sources parameters body kind key element observed activation environment rest values,
    check_term_arena sorts arena image = true ->
    nth_error (image_terms image) root = Some
      {| image_sort := target; image_form := ImageMap sources parameters body |} ->
    parameters <> [] -> nth_error sorts target = Some (T.CollectionSort kind key element) ->
    T.TaskStep sorts observed arena activation (T.Evaluate root environment :: rest) values
      (T.evaluate_requests (T.requests environment sources) ++
        T.FinishMapSources target sources parameters body environment (length values) :: rest) values.
Proof.
  intros sorts arena image root target sources parameters body kind key element observed activation environment rest values
    Hcheck Hnode Hparameters Htarget.
  destruct (checked_term_arena_exposes_exact_construction_view _ _ _ _ _ Hcheck Hnode)
    as [[source_sort source_form] [Hsource [Hsort [_ [Hcase [_ [_ [Hnonempty _]]]]]]]].
  simpl in Hsort, Hcase. subst source_sort source_form.
  eapply T.step_expand_map; eauto. intro Hempty. subst sources. discriminate.
Qed.

(** One useful end-to-end composition: after an image-driven Apply expansion,
    the ALREADY proved task run suffices.  Physical interpretation remains
    precisely LocalPhysicalRefinement, not an arbitrary full-builder premise. *)
Theorem checked_apply_completion_instantiates_exact_source_root_environment :
    forall sorts arena image root sort application meaning observed activation environment output,
    check_term_arena sorts arena image = true ->
    nth_error (image_terms image) root = Some {| image_sort := sort; image_form := ImageApply application |} ->
    T.LocalPhysicalRefinement meaning observed ->
    T.TaskRun sorts observed arena activation
      (T.evaluate_requests (T.requests environment (T.apply_arguments application)) ++
        [T.FinishApply application environment 0]) [] [] [output] ->
    T.SourceInstantiation sorts meaning arena activation root environment output.
Proof.
  intros sorts arena image root sort application meaning observed activation environment output Hcheck Hnode Hphysical Hrun.
  eapply T.successful_singleton_completion_instantiates_exact_root_environment; [exact Hphysical|].
  eapply T.run_step; [|exact Hrun].
  eapply checked_apply_dispatch_is_existing_construction_step; eauto.
Qed.

(** Concrete controls concern the resolved-node boundary only; these records
    are not presented as complete raw LanguageCoreV1 installation artifacts. *)
Definition unit_source : S.Arena :=
  {| S.variables := [];
     S.terms := [{| S.node_sort := 0; S.node_form := S.SourceLiteral S.UnitLiteral |}];
     S.premises := []; S.premise_roots := [] |}.
Definition unit_image : TermArenaImage :=
  {| image_variables := [];
     image_terms := [{| image_sort := 0;
       image_form := ImageApply (T.shape (T.LiteralOperator 0 S.UnitLiteral) [] [] None None) |}] |}.

Example exact_unit_arena_is_accepted : check_term_arena [T.OtherSort] unit_source unit_image = true.
Proof. reflexivity. Qed.

Example changed_literal_variant_is_rejected :
    check_term_arena [T.OtherSort] unit_source
      {| image_variables := []; image_terms := [{| image_sort := 0;
          image_form := ImageApply (T.shape (T.LiteralOperator 0 (S.BooleanLiteral false)) [] [] None None) |}] |}
    = false.
Proof. reflexivity. Qed.

Example missing_source_node_is_rejected :
    check_term_arena [T.OtherSort] unit_source {| image_variables := []; image_terms := [] |} = false.
Proof. reflexivity. Qed.

Definition function_source : S.Arena :=
  {| S.variables := [];
     S.terms := [{| S.node_sort := 1; S.node_form := S.SourceConstructor 0 [] |};
                 {| S.node_sort := 0; S.node_form := S.SourceLiteral S.UnitLiteral |};
                 {| S.node_sort := 0; S.node_form := S.SourceSubstitution 0 1 |}];
     S.premises := []; S.premise_roots := [] |}.

Example substitution_retains_abstraction_sort_not_result_sort :
    expected_form [T.OtherSort; T.OtherSort] function_source
      {| S.node_sort := 0; S.node_form := S.SourceSubstitution 0 1 |} =
    Some (ImageApply (T.shape (T.SubstitutionOperator 0 1) [0; 1] [] None None)).
Proof. reflexivity. Qed.

Example changed_substitution_function_sort_is_rejected :
    check_node [T.OtherSort; T.OtherSort] function_source 2
      {| S.node_sort := 0; S.node_form := S.SourceSubstitution 0 1 |}
      {| image_sort := 0; image_form := ImageApply
        (T.shape (T.SubstitutionOperator 0 0) [0; 1] [] None None) |} = false.
Proof. reflexivity. Qed.

Example map_forward_body_is_rejected : check_references 3 2 (ImageMap [0; 1] [0; 1] 3) = false.
Proof. reflexivity. Qed.
Example map_ordered_references_are_retained :
    image_references (ImageMap [1; 0; 1] [2; 0; 1] 2) = [1; 0; 1; 2] /\
    image_slots (ImageMap [1; 0; 1] [2; 0; 1] 2) = [2; 0; 1].
Proof. split; reflexivity. Qed.

Print Assumptions expected_form_preserves_ordered_references_and_slots.
Print Assumptions expected_form_supplies_existing_construction_case.
Print Assumptions checked_term_arena_has_exact_lengths.
Print Assumptions checked_term_arena_has_exact_variables.
Print Assumptions checked_term_arena_exposes_exact_construction_view.
Print Assumptions checked_term_arena_covers_every_source_node.
Print Assumptions checked_term_arena_is_unique_for_fixed_source.
Print Assumptions changed_term_arena_is_rejected.
Print Assumptions checked_slot_dispatch_is_existing_construction_step.
Print Assumptions checked_apply_dispatch_is_existing_construction_step.
Print Assumptions checked_map_dispatch_is_existing_construction_step.
Print Assumptions checked_apply_completion_instantiates_exact_source_root_environment.

End AuthoredSourceImage.
