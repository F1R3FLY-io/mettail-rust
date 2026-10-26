(** Finite constructor witnesses: the adapter around the existing tree automaton.

    Source correspondence:
    - capture::field_layout supplies canonical ordered slots. Fixed slots carry
      checked token/native expressions, None, or the empty carrier that
      test_gen/unit_tests.rs `construct_leaf_value` (:417) emits; required
      slots carry category identifiers. Fixed expressions are opaque here:
      their lexical/type checks belong to the existing emitters and the
      CaptureTokenSamplingAdapter model, not to an invented payload algebra.
      HashSet uses HashSetLit. PathMap uses HashBag, as its generated
      payload type requires. Empty carrier expressions encode these
      choices below. The implementation properties check the emitted
      expressions for every carrier and optional field.
    - test_gen/strategies/finite_witness.rs `ordinary_recipe` (:603) admits a
      rule by the classification of term_ops/subst.rs
      `variant_kind_from_term_context` (:3777). The section "Rule admission"
      models both, and the admission before 2026-10-20.
    - sym_tree::SymbolicTreeAutomaton::witness inserts an arena node only after
      every ordered child state has a witness. The arena append and category
      map update below model that insertion, including repeated child indices.
    - materialization follows each occurrence, not each distinct arena index.
      Its finite typed unfolding is proved from strictly earlier references.
    - WorklistFoldEquivalence supplies the already proved explicit work/value
      stack. Its algebra is instantiated for constructor reconstruction and
      postorder emission; no second productivity solver is defined here.

    The model does not prove lexer precedence, Rust ownership/formatting,
    global minimum witness size, or stack safety of existing positive-depth
    tape builders. Tests must connect canonical slots and emitted Rust to
    these operations. TreeAlgebraClosure's binary deterministic model is not
    used as a proof of this arbitrary-arity adapter. No saturation algorithm
    changes in this slice, so its stabilization theorem is not needed either.
*)
From Stdlib Require Import List Arith Lia Bool.
From Trampoline Require Import WorklistFoldEquivalence.
Import ListNotations.

Module FiniteConstructorWitnessAdapter.

Inductive Slot := FixedExpr (expression : nat) | RequiredCategory (category : nat).
Inductive Argument := FixedArgument (expression : nat) | ChildArgument (value : nat).

Fixpoint dependencies (slots : list Slot) : list nat :=
  match slots with
  | [] => []
  | FixedExpr _ :: rest => dependencies rest
  | RequiredCategory category :: rest => category :: dependencies rest
  end.

(** The child cursor advances only for required slots. Both surplus and missing
    children refuse; a fixed slot never consumes or fabricates a child. *)
Fixpoint fill_slots (slots : list Slot) (children : list nat) : option (list Argument) :=
  match slots with
  | [] => match children with [] => Some [] | _ => None end
  | FixedExpr expression :: rest =>
      match fill_slots rest children with
      | Some args => Some (FixedArgument expression :: args) | None => None end
  | RequiredCategory _ :: rest =>
      match children with
      | [] => None
      | child :: tail =>
          match fill_slots rest tail with
          | Some args => Some (ChildArgument child :: args) | None => None end
      end
  end.

Inductive OrderedFill : list Slot -> list nat -> list Argument -> Prop :=
| FillEmpty : OrderedFill [] [] []
| FillFixed : forall expression slots children args,
    OrderedFill slots children args ->
    OrderedFill (FixedExpr expression :: slots) children (FixedArgument expression :: args)
| FillChild : forall category slots child children args,
    OrderedFill slots children args ->
    OrderedFill (RequiredCategory category :: slots) (child :: children)
      (ChildArgument child :: args).

Theorem fill_slots_sound : forall slots children args,
  fill_slots slots children = Some args -> OrderedFill slots children args.
Proof.
  induction slots as [|slot slots IH]; intros children args H.
  - destruct children; simpl in H; inversion H; constructor.
  - destruct slot; simpl in H.
    + destruct (fill_slots slots children) eqn:E; inversion H; subst.
      constructor. eapply IH; exact E.
    + destruct children; [discriminate|].
      destruct (fill_slots slots children) eqn:E; inversion H; subst.
      constructor. eapply IH; exact E.
Qed.

Theorem fill_slots_complete : forall slots children args,
  OrderedFill slots children args -> fill_slots slots children = Some args.
Proof. intros slots children args H; induction H; simpl; rewrite ?IHOrderedFill; reflexivity. Qed.

Definition child_arguments args :=
  flat_map (fun arg => match arg with ChildArgument child => [child] | _ => [] end) args.
Definition fixed_arguments args :=
  flat_map (fun arg => match arg with FixedArgument expression => [expression] | _ => [] end) args.
Definition fixed_slots slots :=
  flat_map (fun slot => match slot with FixedExpr expression => [expression] | _ => [] end) slots.

Theorem ordered_fill_preserves_fields : forall slots children args,
  OrderedFill slots children args ->
  length args = length slots /\ length children = length (dependencies slots) /\
  child_arguments args = children /\ fixed_arguments args = fixed_slots slots.
Proof.
  intros slots children args H; induction H; simpl in *.
  - repeat split; reflexivity.
  - destruct IHOrderedFill as [L [C [A F]]]. repeat split; congruence.
  - destruct IHOrderedFill as [L [C [A F]]]. repeat split; congruence.
Qed.

Theorem exact_arity_has_fill : forall slots children,
  length children = length (dependencies slots) ->
  exists args, fill_slots slots children = Some args.
Proof.
  induction slots as [|slot slots IH]; intros children H.
  - destruct children; [exists []; reflexivity|discriminate].
  - destruct slot; simpl in *.
    + destruct (IH children H) as [args E]. rewrite E. eexists; reflexivity.
    + destruct children as [|child children]; [discriminate|].
      injection H as H. destruct (IH children H) as [args E]. rewrite E.
      eexists; reflexivity.
Qed.

Record Recipe := { constructor_id : nat; result_category : nat; ordered_slots : list Slot }.
Record ArenaNode := { node_recipe : Recipe; child_indices : list nat }.

Definition reference_typed (arena : list ArenaNode) index category :=
  exists node, nth_error arena index = Some node /\
    result_category (node_recipe node) = category.
Definition references_valid arena bound node :=
  Forall2 (fun index category => index < bound /\ reference_typed arena index category)
    (child_indices node) (dependencies (ordered_slots (node_recipe node))).
Definition arena_valid grammar arena :=
  forall index node, nth_error arena index = Some node ->
    In (node_recipe node) grammar /\ references_valid arena index node.

Lemma lookup_append_preserved : forall (A : Type) (prefix suffix : list A) index value,
  nth_error prefix index = Some value -> nth_error (prefix ++ suffix) index = Some value.
Proof.
  intros A prefix suffix index value H.
  rewrite nth_error_app1; [exact H|]. apply nth_error_Some. rewrite H; discriminate.
Qed.

Lemma reference_append_preserved : forall arena suffix index category,
  reference_typed arena index category -> reference_typed (arena ++ suffix) index category.
Proof.
  intros arena suffix index category [node [LOOK CAT]]. exists node; split; auto.
  eapply lookup_append_preserved; exact LOOK.
Qed.

Lemma references_append_preserved : forall arena suffix bound node,
  references_valid arena bound node -> references_valid (arena ++ suffix) bound node.
Proof.
  intros arena suffix bound node H. unfold references_valid in *.
  induction H; constructor; auto.
  destruct H as [EARLIER TYPED]. split; auto. eapply reference_append_preserved; exact TYPED.
Qed.

(** Appending one ready transition is the actual Rust witness insertion step.
    The readiness premise includes exactly its ordered child state witnesses.
    It permits duplicate child indices and requires neither binary arity nor
    determinism. Old nodes continue to refer to the same earlier entries. *)
Theorem arena_insertion_preserves_validity : forall grammar arena recipe indices,
  arena_valid grammar arena -> In recipe grammar ->
  references_valid arena (length arena)
    {| node_recipe := recipe; child_indices := indices |} ->
  arena_valid grammar (arena ++ [{| node_recipe := recipe; child_indices := indices |}]).
Proof.
  intros grammar arena recipe indices VALID MEMBER READY index node LOOK.
  destruct (lt_dec index (length arena)) as [OLD|NEW].
  - rewrite nth_error_app1 in LOOK by exact OLD.
    destruct (VALID index node LOOK) as [M R]. split; [exact M|].
    eapply references_append_preserved; exact R.
  - rewrite nth_error_app2 in LOOK by lia.
    destruct (index - length arena) as [|extra] eqn:E; simpl in LOOK;
      [|destruct extra; discriminate].
    inversion LOOK; subst node. assert (index = length arena) by lia. subst index.
    split; [exact MEMBER|]. eapply references_append_preserved; exact READY.
Qed.

Definition map_valid arena (witnesses : nat -> option nat) :=
  forall category index, witnesses category = Some index -> reference_typed arena index category.
Definition insert_witness (witnesses : nat -> option nat) category index :=
  fun queried => if Nat.eqb queried category then Some index else witnesses queried.

(** This is the ordered map lookup after Rust's all(contains_key) check.
    Failure means some category has not yet acquired a finite witness. *)
Fixpoint gather_children (witnesses : nat -> option nat) (categories : list nat)
    : option (list nat) :=
  match categories with
  | [] => Some []
  | category :: rest =>
      match witnesses category, gather_children witnesses rest with
      | Some index, Some indices => Some (index :: indices)
      | _, _ => None
      end
  end.

Lemma gathered_children_are_earlier_and_typed : forall arena witnesses categories indices,
  map_valid arena witnesses -> gather_children witnesses categories = Some indices ->
  Forall2 (fun index category => index < length arena /\ reference_typed arena index category)
    indices categories.
Proof.
  intros arena witnesses categories; induction categories as [|category rest IH];
    intros indices VALID GATHER; simpl in GATHER.
  - inversion GATHER; constructor.
  - destruct (witnesses category) as [index|] eqn:LOOK; [|discriminate].
    destruct (gather_children witnesses rest) as [children|] eqn:REST;
      inversion GATHER; subst indices.
    constructor.
    + pose proof (VALID category index LOOK) as REF. split; [|exact REF].
      destruct REF as [node [ENTRY _]]. apply nth_error_Some. rewrite ENTRY; discriminate.
    + eapply IH; eauto.
Qed.

Theorem valid_map_supplies_insertion_readiness : forall arena witnesses recipe indices,
  map_valid arena witnesses ->
  gather_children witnesses (dependencies (ordered_slots recipe)) = Some indices ->
  references_valid arena (length arena)
    {| node_recipe := recipe; child_indices := indices |}.
Proof. intros; eapply gathered_children_are_earlier_and_typed; eauto. Qed.

Theorem all_child_categories_present_can_be_gathered : forall witnesses categories,
  Forall (fun category => exists index, witnesses category = Some index) categories ->
  exists indices, gather_children witnesses categories = Some indices.
Proof.
  intros witnesses categories H; induction H.
  - exists []; reflexivity.
  - destruct H as [index LOOK]. destruct IHForall as [indices REST].
    exists (index :: indices); simpl; rewrite LOOK, REST; reflexivity.
Qed.

Theorem witness_map_insertion_preserves_types : forall arena witnesses recipe indices,
  map_valid arena witnesses ->
  map_valid (arena ++ [{| node_recipe := recipe; child_indices := indices |}])
    (insert_witness witnesses (result_category recipe) (length arena)).
Proof.
  intros arena witnesses recipe indices VALID category index LOOK.
  unfold insert_witness in LOOK.
  destruct (Nat.eqb category (result_category recipe)) eqn:E.
  - apply Nat.eqb_eq in E; subst category. inversion LOOK; subst index.
    exists {| node_recipe := recipe; child_indices := indices |}. split; [|reflexivity].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - apply reference_append_preserved. eapply VALID; exact LOOK.
Qed.

Theorem first_witness_not_replaced : forall witnesses category index other previous,
  witnesses category = None -> witnesses other = Some previous ->
  insert_witness witnesses category index other = Some previous.
Proof.
  intros witnesses category index other previous EMPTY OLD. unfold insert_witness.
  destruct (Nat.eqb other category) eqn:E; [|exact OLD].
  apply Nat.eqb_eq in E; subst other. rewrite EMPTY in OLD; discriminate.
Qed.

Fixpoint list_forest (trees : list tree) : forest :=
  match trees with [] => FNil | head :: tail => FCons head (list_forest tail) end.

Inductive TypedTree (grammar : list Recipe) : tree -> nat -> Prop :=
| TypedConstructor : forall recipe children,
    In recipe grammar ->
    Forall2 (TypedTree grammar) children (dependencies (ordered_slots recipe)) ->
    TypedTree grammar (Node (constructor_id recipe) (list_forest children))
      (result_category recipe).

Inductive Unfolds (arena : list ArenaNode) : nat -> tree -> Prop :=
| UnfoldConstructor : forall index node children,
    nth_error arena index = Some node ->
    Forall2 (Unfolds arena) (child_indices node) children ->
    Unfolds arena index (Node (constructor_id (node_recipe node)) (list_forest children)).

Lemma ready_children_unfold : forall grammar arena bound indices categories,
  (forall index category, index < bound -> reference_typed arena index category ->
    exists term, Unfolds arena index term /\ TypedTree grammar term category) ->
  Forall2 (fun index category => index < bound /\ reference_typed arena index category)
    indices categories ->
  exists children, Forall2 (Unfolds arena) indices children /\
    Forall2 (TypedTree grammar) children categories.
Proof.
  intros grammar arena bound indices categories IH READY. induction READY.
  - exists []; split; constructor.
  - destruct H as [EARLIER REF]. destruct (IH x y EARLIER REF) as [term [U T]].
    destruct IHREADY as [children [US TS]]. exists (term :: children).
    split; constructor; auto.
Qed.

(** Strong induction uses arena indices, not a guessed recursion-depth budget.
    Thus a productive cycle's selected finite witness is covered, while an
    unproductive cycle cannot manufacture an arena entry. *)
Theorem valid_arena_has_finite_typed_unfolding : forall grammar arena,
  arena_valid grammar arena -> forall index category,
  reference_typed arena index category ->
  exists term, Unfolds arena index term /\ TypedTree grammar term category.
Proof.
  intros grammar arena VALID index. induction index using lt_wf_ind.
  intros category [node [LOOK CAT]].
  destruct (VALID index node LOOK) as [MEMBER READY].
  destruct (ready_children_unfold grammar arena index (child_indices node)
    (dependencies (ordered_slots (node_recipe node)))) as [children [US TS]].
  - intros child child_category EARLIER REF. eapply H; eauto.
  - exact READY.
  - exists (Node (constructor_id (node_recipe node)) (list_forest children)).
    split.
    + econstructor; eauto.
    + rewrite <- CAT. constructor; auto.
Qed.

(** Reuse the existing worklist theorem with a constructor algebra. The
    separate postorder algebra records every emission occurrence in source
    order. In particular a repeated arena child is visited twice. *)
Definition rebuild_algebra tag children := Node tag (list_forest children).

Lemma rebuild_identity :
  (forall input, recursive_fold tree rebuild_algebra input = input) /\
  (forall inputs, list_forest (recursive_folds tree rebuild_algebra inputs) = inputs).
Proof.
  apply tree_forest_ind.
  - intros tag children IH.
    change (Node tag (list_forest (recursive_folds tree rebuild_algebra children)) =
      Node tag children). rewrite IH. reflexivity.
  - reflexivity.
  - intros head IHhead tail IHtail.
    change (FCons (recursive_fold tree rebuild_algebra head)
      (list_forest (recursive_folds tree rebuild_algebra tail)) = FCons head tail).
    rewrite IHhead, IHtail. reflexivity.
Qed.

Theorem iterative_assembly_reconstructs_typed_witness : forall grammar input category,
  TypedTree grammar input category ->
  exists result,
    steps tree rebuild_algebra
      (State tree [VisitTree input] []) (State tree [] [TreeValue tree result]) /\
    result = input /\ TypedTree grammar result category.
Proof.
  intros grammar input category TYPED. exists input. split; [|split; auto].
  pose proof (worklist_root_equivalence tree rebuild_algebra input) as H.
  rewrite (proj1 rebuild_identity input) in H. exact H.
Qed.

Definition postorder_algebra (tag : nat) (children : list (list nat)) :=
  concat children ++ [tag].
Definition postorder input := recursive_fold (list nat) postorder_algebra input.

Theorem iterative_postorder_emits_all_occurrences : forall input,
  steps (list nat) postorder_algebra
    (State (list nat) [VisitTree input] [])
    (State (list nat) [] [TreeValue (list nat) (postorder input)]).
Proof. intro input; apply worklist_root_equivalence. Qed.

Theorem repeated_child_keeps_both_occurrences : forall tag child,
  postorder (Node tag (FCons child (FCons child FNil))) =
    postorder child ++ postorder child ++ [tag].
Proof.
  intros. change ((postorder child ++ (postorder child ++ [])) ++ [tag] =
    postorder child ++ postorder child ++ [tag]).
  rewrite app_nil_r, app_assoc. reflexivity.
Qed.

(** Direct bases retain their list, order, and multiplicity. A missing witness
    leaves the original empty list for the caller's explicit diagnostic. *)
Definition supply_missing_base (direct : list nat) (witness : option nat) :=
  match direct with
  | [] => match witness with Some base => [base] | None => [] end
  | _ :: _ => direct
  end.

Theorem nonempty_direct_bases_unchanged : forall direct witness,
  direct <> [] -> supply_missing_base direct witness = direct.
Proof. intros [|head tail] witness H; [contradiction|reflexivity]. Qed.

Theorem missing_base_requires_actual_witness : forall witness base,
  In base (supply_missing_base [] witness) <-> witness = Some base.
Proof.
  intros [chosen|] base; simpl; split; intros H; try contradiction; try discriminate.
  - destruct H as [H|H]; [subst; reflexivity|contradiction].
  - inversion H; auto.
Qed.

Example mixed_fields_keep_repeated_child_occurrences :
  fill_slots [FixedExpr 10; RequiredCategory 2; FixedExpr 11; RequiredCategory 2]
    [7; 7] = Some [FixedArgument 10; ChildArgument 7; FixedArgument 11; ChildArgument 7].
Proof. reflexivity. Qed.

(** A capture-free sole `Vec` constructor is the one-slot case of the canonical
    layout: its only slot is the fixed empty carrier. It depends on no child
    state, fills without children, and refuses a surplus child. *)
Example sole_empty_carrier_recipe_needs_no_child :
  dependencies [FixedExpr 12] = []
  /\ fill_slots [FixedExpr 12] [] = Some [FixedArgument 12]
  /\ fill_slots [FixedExpr 12] [3] = None.
Proof. repeat split; reflexivity. Qed.

(** * Rule admission

    A rule's fields after field_layout. A category field is required. A
    non-optional collection field is the empty carrier of its carrier
    (`construct_leaf_value`, unit_tests.rs:440-457). Every other field is one
    fixed expression: a token sample, a predicate, or an optional field, whose
    expression is `None` (unit_tests.rs:432), also when it is a collection.
    The refusals that inspect one field (guest bodies, scopes, runtime-only
    native and undeclared categories, finite_witness.rs:646-696) apply to both
    shapes in the same way, so they are not modeled here. *)
Inductive Carrier :=
  VecCarrier | HashBagCarrier | HashSetCarrier | PathMapCarrier | MapCarrier.

Inductive Field :=
| CategoryField (category : nat)
| CollectionField (carrier : Carrier) (element : nat)
| ExpressionField (expression : nat).

(** subst.rs:3777: a rule whose only field is a non-optional collection is a
    sole collection; a rule without fields is nullary, and the direct bases
    cover it; every other rule is regular. *)
Inductive Shape := NullaryShape | SoleCollectionShape (carrier : Carrier) (element : nat) | RegularShape.

Definition classify (fields : list Field) : Shape :=
  match fields with
  | [] => NullaryShape
  | [CollectionField carrier element] => SoleCollectionShape carrier element
  | _ => RegularShape
  end.

(** HashBag and PathMap share the generated HashBag representation. *)
Definition empty_carrier_expression (carrier : Carrier) : nat :=
  match carrier with
  | VecCarrier => 0 | HashBagCarrier | PathMapCarrier => 1
  | HashSetCarrier => 2 | MapCarrier => 3
  end.

(** finite_witness.rs `field_slot` (:705). *)
Definition field_slot (field : Field) : Slot :=
  match field with
  | CategoryField category => RequiredCategory category
  | CollectionField carrier _ => FixedExpr (empty_carrier_expression carrier)
  | ExpressionField expression => FixedExpr expression
  end.

Definition canonical_slots (fields : list Field) : list Slot := map field_slot fields.

(** The admission before 2026-10-20 (finite_witness.rs:621, kept there as a
    comment): only the regular shape. *)
Definition admission_before (fields : list Field) : option (list Slot) :=
  match classify fields with
  | RegularShape => Some (canonical_slots fields)
  | _ => None
  end.

(** The current admission (finite_witness.rs:622-631): the regular shape, and
    a sole `Vec` collection as the one-slot case of the same canonical layout.
    Other sole carriers keep a named refusal. Correctly typed empty
    expressions do not establish display and parse roundtrip behavior.
    For example, the owner-element bag `PPar` prints `{}`, which Rholang
    also reads as an empty map. *)
Definition admission (fields : list Field) : option (list Slot) :=
  match classify fields with
  | RegularShape | SoleCollectionShape VecCarrier _ => Some (canonical_slots fields)
  | _ => None
  end.

Record Rule := { rule_constructor : nat; rule_category : nat; rule_fields : list Field }.

(** finite_witness.rs `from_language` (:554-572): each admitted rule adds one
    recipe of its category; a refused rule adds none. *)
Definition rule_recipes (admit : list Field -> option (list Slot)) (rule : Rule) : list Recipe :=
  match admit (rule_fields rule) with
  | Some slots =>
      [{| constructor_id := rule_constructor rule; result_category := rule_category rule;
          ordered_slots := slots |}]
  | None => []
  end.

Definition admitted_recipes admit (rules : list Rule) : list Recipe :=
  flat_map (rule_recipes admit) rules.

Lemma classify_sole_collection : forall carrier element,
  classify [CollectionField carrier element] = SoleCollectionShape carrier element.
Proof. reflexivity. Qed.

Lemma canonical_slots_sole_collection : forall carrier element,
  canonical_slots [CollectionField carrier element] =
    [FixedExpr (empty_carrier_expression carrier)].
Proof. reflexivity. Qed.

(** Negative control: the admission before 2026-10-20 refuses a sole `Vec`
    rule, although its canonical layout needs no child. *)
Theorem admission_before_refuses_the_sole_vec_rule : forall element,
  admission_before [CollectionField VecCarrier element] = None
  /\ dependencies (canonical_slots [CollectionField VecCarrier element]) = [].
Proof. split; reflexivity. Qed.

Definition only_sole_vec_rules (rules : list Rule) (category : nat) :=
  forall rule, In rule rules -> rule_category rule = category ->
    exists element, rule_fields rule = [CollectionField VecCarrier element].

(** The root cause of the missing DdlOptionSection and DdlProjectionPremises
    bases, stated for the admission before 2026-10-20: when every rule of a
    category is a sole `Vec` rule, no valid arena types any entry at that
    category, so `base_for` finds no witness. *)
Theorem admission_before_leaves_a_sole_vec_category_without_witness :
  forall rules category arena index,
  only_sole_vec_rules rules category ->
  arena_valid (admitted_recipes admission_before rules) arena ->
  ~ reference_typed arena index category.
Proof.
  intros rules category arena index ONLY VALID [node [LOOK CAT]].
  destruct (VALID index node LOOK) as [MEMBER _].
  unfold admitted_recipes in MEMBER. apply in_flat_map in MEMBER.
  destruct MEMBER as [rule [IN RECIPE]].
  unfold rule_recipes in RECIPE.
  destruct (admission_before (rule_fields rule)) as [slots|] eqn:ADMIT;
    simpl in RECIPE; [|contradiction].
  destruct RECIPE as [EQ|[]].
  rewrite <- EQ in CAT. simpl in CAT.
  destruct (ONLY rule IN CAT) as [element FIELDS].
  rewrite FIELDS in ADMIT.
  rewrite (proj1 (admission_before_refuses_the_sole_vec_rule element)) in ADMIT.
  discriminate.
Qed.

(** The fix: the current admission gives every sole `Vec` rule a recipe with
    no child state. It can be inserted into any valid arena, and the new
    entry types its category, whatever the element category is. *)
Theorem admission_gives_a_sole_vec_rule_a_zero_child_witness :
  forall rules rule element arena,
  In rule rules -> rule_fields rule = [CollectionField VecCarrier element] ->
  arena_valid (admitted_recipes admission rules) arena ->
  exists recipe,
    In recipe (admitted_recipes admission rules) /\
    dependencies (ordered_slots recipe) = [] /\
    arena_valid (admitted_recipes admission rules)
      (arena ++ [{| node_recipe := recipe; child_indices := [] |}]) /\
    reference_typed (arena ++ [{| node_recipe := recipe; child_indices := [] |}])
      (length arena) (rule_category rule).
Proof.
  intros rules rule element arena IN FIELDS VALID.
  exists {| constructor_id := rule_constructor rule; result_category := rule_category rule;
            ordered_slots := [FixedExpr (empty_carrier_expression VecCarrier)] |}.
  assert (MEMBER : In {| constructor_id := rule_constructor rule;
      result_category := rule_category rule;
      ordered_slots := [FixedExpr (empty_carrier_expression VecCarrier)] |}
      (admitted_recipes admission rules)).
  { unfold admitted_recipes. apply in_flat_map. exists rule. split; [exact IN|].
    unfold rule_recipes, admission.
    rewrite FIELDS, classify_sole_collection, canonical_slots_sole_collection.
    simpl. left. reflexivity. }
  split; [exact MEMBER|]. split; [reflexivity|]. split.
  - apply arena_insertion_preserves_validity; [exact VALID|exact MEMBER|].
    unfold references_valid. simpl. constructor.
  - eexists. split.
    + rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + reflexivity.
Qed.

(** Shape independence for `Vec`: the sole rule gets exactly the slot that
    the same collection field gets inside a regular rule. *)
Theorem sole_vec_slot_equals_the_regular_field_slot : forall element,
  admission [CollectionField VecCarrier element] =
    Some [field_slot (CollectionField VecCarrier element)].
Proof. reflexivity. Qed.

(** The other sole carriers stay refused by name (finite_witness.rs:627-631). *)
Theorem admission_refuses_the_other_sole_carriers : forall carrier element,
  carrier <> VecCarrier -> admission [CollectionField carrier element] = None.
Proof. intros [] element H; [exfalso; apply H; reflexivity|reflexivity ..]. Qed.

(** The change does not touch regular rules. *)
Theorem admission_keeps_every_regular_rule : forall fields,
  classify fields = RegularShape ->
  admission fields = admission_before fields /\ admission fields = Some (canonical_slots fields).
Proof. intros fields H. unfold admission, admission_before. rewrite H. split; reflexivity. Qed.

Definition leaf_nullary_before (items_empty context_empty : bool) : bool :=
  items_empty || context_empty.

Definition leaf_nullary (fields : list Field) : bool :=
  match classify fields with NullaryShape => true | _ => false end.

Definition first_nullary_leaf (category : nat) (rules : list Rule) : option Rule :=
  find (fun rule => Nat.eqb category (rule_category rule) && leaf_nullary (rule_fields rule)) rules.

Theorem captured_token_was_a_false_nullary : forall token,
  leaf_nullary_before true true = true /\
  leaf_nullary [ExpressionField token] = false.
Proof. intros; split; reflexivity. Qed.

Theorem leaf_nullary_iff_no_fields : forall fields,
  leaf_nullary fields = true <-> fields = [].
Proof.
  intros [|field tail]; [simpl; tauto|].
  destruct field; destruct tail; simpl; split; intros H; discriminate.
Qed.

Theorem first_nullary_leaf_sound : forall category rules rule,
  first_nullary_leaf category rules = Some rule ->
  In rule rules /\ rule_category rule = category /\ rule_fields rule = [].
Proof.
  intros category rules rule FOUND.
  apply find_some in FOUND. destruct FOUND as [IN TEST].
  apply andb_true_iff in TEST. destruct TEST as [CAT FIELDS].
  apply Nat.eqb_eq in CAT. apply leaf_nullary_iff_no_fields in FIELDS.
  auto.
Qed.

Theorem first_nullary_leaf_complete : forall category rules,
  first_nullary_leaf category rules = None <->
  forall rule, In rule rules -> rule_category rule = category -> rule_fields rule <> [].
Proof.
  intros category rules. split.
  - intros NONE rule IN CAT EMPTY.
    unfold first_nullary_leaf in NONE.
    pose proof (find_none _ _ NONE rule IN) as TEST.
    cbv beta in TEST.
    rewrite CAT, Nat.eqb_refl, EMPTY in TEST. discriminate.
  - intros NONE. destruct (first_nullary_leaf category rules) as [rule|] eqn:FOUND;
      [|reflexivity].
    apply first_nullary_leaf_sound in FOUND.
    destruct FOUND as [IN [CAT EMPTY]].
    exfalso. exact (NONE rule IN CAT EMPTY).
Qed.

Theorem first_nullary_leaf_keeps_declaration_order : forall category head tail,
  rule_category head = category -> rule_fields head = [] ->
  first_nullary_leaf category (head :: tail) = Some head.
Proof.
  intros category head tail CAT EMPTY. unfold first_nullary_leaf. simpl.
  rewrite CAT, Nat.eqb_refl, EMPTY. reflexivity.
Qed.

Theorem empty_carrier_representation :
  empty_carrier_expression VecCarrier = 0 /\
  empty_carrier_expression HashBagCarrier = 1 /\
  empty_carrier_expression HashSetCarrier = 2 /\
  empty_carrier_expression PathMapCarrier = 1 /\
  empty_carrier_expression MapCarrier = 3.
Proof. repeat split; reflexivity. Qed.

Print Assumptions captured_token_was_a_false_nullary.
Print Assumptions leaf_nullary_iff_no_fields.
Print Assumptions first_nullary_leaf_sound.
Print Assumptions first_nullary_leaf_complete.
Print Assumptions first_nullary_leaf_keeps_declaration_order.
Print Assumptions empty_carrier_representation.
Print Assumptions arena_insertion_preserves_validity.
Print Assumptions valid_map_supplies_insertion_readiness.
Print Assumptions valid_arena_has_finite_typed_unfolding.
Print Assumptions iterative_assembly_reconstructs_typed_witness.
Print Assumptions ordered_fill_preserves_fields.
Print Assumptions nonempty_direct_bases_unchanged.
Print Assumptions admission_before_leaves_a_sole_vec_category_without_witness.
Print Assumptions admission_gives_a_sole_vec_rule_a_zero_child_witness.
Print Assumptions admission_refuses_the_other_sole_carriers.
Print Assumptions admission_keeps_every_regular_rule.
End FiniteConstructorWitnessAdapter.
