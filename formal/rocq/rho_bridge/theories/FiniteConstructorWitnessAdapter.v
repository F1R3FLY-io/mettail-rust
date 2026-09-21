(** Finite constructor witnesses: the adapter around the existing tree automaton.

    Source correspondence:
    - capture::field_layout supplies canonical ordered slots. Fixed slots carry
      checked token/native expressions, None, or correctly typed empty carriers;
      required slots carry category identifiers. Fixed expressions are opaque
      here: their lexical/type checks belong to the existing emitters and the
      CaptureTokenSamplingAdapter model, not to an invented payload algebra.
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
From Stdlib Require Import List Arith Lia.
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

Print Assumptions arena_insertion_preserves_validity.
Print Assumptions valid_map_supplies_insertion_readiness.
Print Assumptions valid_arena_has_finite_typed_unfolding.
Print Assumptions iterative_assembly_reconstructs_typed_witness.
Print Assumptions ordered_fill_preserves_fields.
Print Assumptions nonempty_direct_bases_unchanged.
End FiniteConstructorWitnessAdapter.
