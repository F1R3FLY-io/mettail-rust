(** The concrete Visit/Append/Fresh interpreter for construction graphs.

    Values are oldest-first, like the reused Worklist value vector. Work is
    top-first. No source terms are visited here. Integer range admission is
    separate: scalar denotation agrees with the existing checked integer
    constructor on its signed-64-bit domain, rather than truncating integers.

    The bounded execution relation records every intermediate state, allowing
    stack capacities to be established for the actual graph machine, not merely
    inferred from the denotation's tree depth. Resource debits and the actual
    Rust constructor bodies have separate correspondence obligations. Fresh
    execution requires the explicit descriptor-admission and edge-count
    invariant below; this is not a safety theorem for arbitrary forged jobs or
    descriptor-inconsistent graphs. *)
From Stdlib Require Import List Arith Lia Bool String ZArith.
From RhoBridge Require Import RholangInitialGraphInterpretation
  RholangTargetConstruction RholangWorklistConstruction RholangConstructionProtocol
  RholangFreshDescriptor RholangGraphCapacity.
Import ListNotations.

Definition scalar_denotation (scalar : InitialScalar) : Value :=
  match scalar with
  | EmptyScalar => empty
  | IntegerScalar number => singleton (IntegerHead number) [] closed_summary
  | BooleanScalar flag => boolean flag
  | TextScalar payload => text payload
  | BoundScalar _ index => singleton (BoundHead index) [] (bound_summary index)
  | WildcardScalar flag => wildcard flag
  end.

Theorem integer_denotation_reuses_checked_constructor : forall number,
  (-9223372036854775808 <= number <= 9223372036854775807)%Z ->
  integer number = Constructed (scalar_denotation (IntegerScalar number)).
Proof.
  intros number [Hlow Hhigh]. unfold integer, scalar_denotation.
  apply Z.leb_le in Hlow. apply Z.leb_le in Hhigh. now rewrite Hlow, Hhigh.
Qed.

Theorem bound_denotation_reuses_checked_constructor : forall scope index,
  index < scope -> fits_target_index index = true ->
  interpret (BoundOp scope index) [] =
    Constructed (scalar_denotation (BoundScalar scope index)).
Proof.
  intros scope index Hscope Hfits.
  change ((if fits_target_index index && true then bound scope index
    else ConstructionRejected TargetIndexOutOfRange) =
    Constructed (scalar_denotation (BoundScalar scope index))).
  rewrite Hfits. cbn [andb].
  unfold bound. apply Nat.ltb_lt in Hscope. now rewrite Hscope.
Qed.

Theorem wildcard_denotation_retains_its_exact_connective_policy : forall flag,
  interpret (WildcardOp flag) [] = Constructed (scalar_denotation (WildcardScalar flag)).
Proof. reflexivity. Qed.

Definition fresh_denotation (descriptor : FreshDescriptor) (body : Value) (injections : list Value) :=
  singleton (NewHead (shape_width (descriptor_shape descriptor))
    (shape_uris (descriptor_shape descriptor)) (descriptor_keys descriptor))
    (body :: injections) (shifted_summary (shape_width (descriptor_shape descriptor)) (summary_of body)).

Fixpoint tree_denotation (tree : InitialTree) : Value :=
  match tree with
  | ScalarTree scalar => scalar_denotation scalar
  | AppendTree lhs_tree rhs_tree => append (tree_denotation lhs_tree) (tree_denotation rhs_tree)
  | FreshTree descriptor body injections =>
    fresh_denotation descriptor (tree_denotation body) (map tree_denotation injections)
  end.

Inductive GraphJob := Visit (index : nat) | Append (index : nat) | Fresh (index : nat).
Record GraphState := { jobs : list GraphJob; values : list Value }.

Definition graph_step (graph : list InitialNode) (state : GraphState) : option GraphState :=
  match jobs state with
  | [] => None
  | Visit index :: pending =>
    match nth_error graph index with
    | Some (ScalarNode scalar) =>
      Some {| jobs := pending; values := values state ++ [scalar_denotation scalar] |}
    | Some (AppendNode lhs rhs) =>
      if (lhs <? index) && (rhs <? index) then
        Some {| jobs := Visit lhs :: Visit rhs :: Append index :: pending; values := values state |}
      else None
    | Some (FreshNode descriptor body injections) =>
      if forallb (fun child => child <? index) (body :: injections) then
        Some {| jobs := map Visit (body :: injections) ++ Fresh index :: pending;
                values := values state |}
      else None
    | None => None
    end
  | Append _ :: pending =>
    match reduce_pair (fun lhs rhs => @Built _ unit (append lhs rhs)) (values state) with
    | Completed result => Some {| jobs := pending; values := result |}
    | _ => None
    end
  | Fresh index :: pending =>
    match nth_error graph index with
    | Some (FreshNode descriptor _ _) =>
      match reduce_values (S (List.length (descriptor_keys descriptor)))
        (build_fresh descriptor) (values state) with
      | Completed result => Some {| jobs := pending; values := result |}
      | _ => None
      end
    | _ => None
    end
  end.

(** These are concrete field checks of graph nodes, not assumed semantic
    correctness. Checked descriptor construction and edge enrollment must
    establish them before the private graph is emitted. The machine performs
    the same checked Fresh callback; it cannot replace a rejected result. *)
Definition FreshDescriptorsAdmitted (graph : list InitialNode) : Prop :=
  forall index descriptor body injections,
  nth_error graph index = Some (FreshNode descriptor body injections) ->
  admit_fresh_descriptor (descriptor_shape descriptor) (descriptor_keys descriptor) = Some descriptor /\
  List.length (descriptor_keys descriptor) = List.length injections.

Definition fits (job_limit value_limit : nat) (state : GraphState) : Prop :=
  List.length (jobs state) <= job_limit /\ List.length (values state) <= value_limit.

Inductive BoundedSteps (graph : list InitialNode) (job_limit value_limit : nat)
    : GraphState -> GraphState -> Prop :=
| BoundedRefl : forall state,
    fits job_limit value_limit state -> BoundedSteps graph job_limit value_limit state state
| BoundedCons : forall first next last,
    fits job_limit value_limit first -> graph_step graph first = Some next ->
    BoundedSteps graph job_limit value_limit next last ->
    BoundedSteps graph job_limit value_limit first last.

Lemma bounded_steps_trans : forall graph jl vl first middle last,
  BoundedSteps graph jl vl first middle -> BoundedSteps graph jl vl middle last ->
  BoundedSteps graph jl vl first last.
Proof.
  intros graph jl vl first middle last Hfirst Hlast.
  induction Hfirst; [exact Hlast|]. eapply BoundedCons; eauto.
Qed.

Lemma bounded_steps_weaken : forall graph jl vl first last,
  BoundedSteps graph jl vl first last -> forall jl' vl', jl <= jl' -> vl <= vl' ->
  BoundedSteps graph jl' vl' first last.
Proof.
  intros graph jl vl first last H. induction H; intros jl' vl' Hj Hv.
  - apply BoundedRefl. unfold fits in *; lia.
  - eapply BoundedCons; [unfold fits in *; lia|eassumption|]. apply IHBoundedSteps; assumption.
Qed.

Lemma tree_depth_positive : forall tree, 1 <= tree_depth tree.
Proof. destruct tree; cbn; lia. Qed.

Lemma scalar_step : forall graph index scalar pending prefix,
  nth_error graph index = Some (ScalarNode scalar) ->
  graph_step graph {| jobs := Visit index :: pending; values := prefix |} =
  Some {| jobs := pending; values := prefix ++ [scalar_denotation scalar] |}.
Proof. intros. cbn [graph_step jobs values]. now rewrite H. Qed.

Lemma append_enter_step : forall graph index lhs rhs pending prefix,
  nth_error graph index = Some (AppendNode lhs rhs) ->
  ((lhs <? index) && (rhs <? index)) = true ->
  graph_step graph {| jobs := Visit index :: pending; values := prefix |} =
  Some {| jobs := Visit lhs :: Visit rhs :: Append index :: pending; values := prefix |}.
Proof. intros. cbn -[Nat.ltb]. now rewrite H, H0. Qed.

Lemma append_combine_step : forall graph index pending prefix lhs rhs,
  graph_step graph {| jobs := Append index :: pending; values := prefix ++ [lhs; rhs] |} =
  Some {| jobs := pending; values := prefix ++ [append lhs rhs] |}.
Proof.
  intros. unfold graph_step. cbn [jobs values].
  rewrite pair_keeps_left_right_order. reflexivity.
Qed.

Lemma fresh_enter_step : forall graph index descriptor body injections pending prefix,
  nth_error graph index = Some (FreshNode descriptor body injections) ->
  forallb (fun child => child <? index) (body :: injections) = true ->
  graph_step graph {| jobs := Visit index :: pending; values := prefix |} =
  Some {| jobs := map Visit (body :: injections) ++ Fresh index :: pending; values := prefix |}.
Proof. intros. cbn [graph_step jobs values]. now rewrite H, H0. Qed.

Lemma fresh_combine_step : forall graph index descriptor body_ref injection_refs pending prefix body injections,
  nth_error graph index = Some (FreshNode descriptor body_ref injection_refs) ->
  admit_fresh_descriptor (descriptor_shape descriptor) (descriptor_keys descriptor) = Some descriptor ->
  List.length (descriptor_keys descriptor) = List.length injections ->
  graph_step graph {| jobs := Fresh index :: pending; values := prefix ++ body :: injections |} =
  Some {| jobs := pending; values := prefix ++ [fresh_denotation descriptor body injections] |}.
Proof.
  intros graph index descriptor body_ref injection_refs pending prefix body injections Hnode HD HL.
  cbn [graph_step jobs values]. rewrite Hnode.
  rewrite (fresh_transition_retains_prefix_body_and_ordered_injections
    (descriptor_shape descriptor) (descriptor_keys descriptor) descriptor prefix body injections HD HL).
  reflexivity.
Qed.

Definition ChildExecution graph child tree : Prop := forall pending prefix,
  BoundedSteps graph
    (List.length pending + job_allowance (initial_node_arity graph) child)
    (List.length prefix + value_allowance (initial_node_arity graph) child)
    {| jobs := Visit child :: pending; values := prefix |}
    {| jobs := pending; values := prefix ++ [tree_denotation tree] |}.

(** completed contains already-produced siblings, not unique graph nodes.
    Pairwise execution preserves every reference occurrence in source order. *)
Theorem ordered_child_executions_compose : forall graph owner references trees,
  Forall2 (fun child tree => child < owner /\ ChildExecution graph child tree) references trees ->
  forall combine pending prefix completed,
  0 < owner ->
  List.length completed + List.length references = initial_node_arity graph owner ->
  BoundedSteps graph
    (List.length pending + job_allowance (initial_node_arity graph) owner)
    (List.length prefix + value_allowance (initial_node_arity graph) owner)
    {| jobs := map Visit references ++ combine :: pending; values := prefix ++ completed |}
    {| jobs := combine :: pending; values := prefix ++ (completed ++ map tree_denotation trees) |}.
Proof.
  intros graph owner references trees H.
  induction H as [|child tree rest trees [HR HC] Hrest IH];
    intros combine pending prefix completed HO Hcount.
  - cbn [map app]. rewrite app_nil_r. apply BoundedRefl.
    pose proof (single_visit_and_single_result_always_fit (initial_node_arity graph) owner) as [HJ HV].
    pose proof (combining_nonleaf_fits_all_completed_children (initial_node_arity graph) owner HO) as HA.
    unfold fits. cbn [jobs values List.length]. rewrite length_app. cbn [List.length] in Hcount. lia.
  - assert (HP : List.length completed < initial_node_arity graph owner)
      by (cbn [List.length] in Hcount; lia).
    pose proof (child_work_and_pending_siblings_fit_parent_allowance
      (initial_node_arity graph) owner child (List.length completed) HR HP) as HJ.
    pose proof (child_values_and_completed_siblings_fit_parent_allowance
      (initial_node_arity graph) owner child (List.length completed) HR HP) as HV.
    cbn [map app]. eapply bounded_steps_trans.
    + eapply bounded_steps_weaken.
      * exact (HC (map Visit rest ++ combine :: pending) (prefix ++ completed)).
      * rewrite length_app, length_map. cbn [List.length] in Hcount |- *. lia.
      * rewrite length_app. lia.
    + replace ((prefix ++ completed) ++ [tree_denotation tree])
        with (prefix ++ (completed ++ [tree_denotation tree]))
        by (rewrite <- app_assoc; reflexivity).
      replace (prefix ++ (completed ++ tree_denotation tree :: map tree_denotation trees))
        with (prefix ++ ((completed ++ [tree_denotation tree]) ++ map tree_denotation trees))
        by (rewrite <- app_assoc; reflexivity).
      apply IH; [exact HO|]. rewrite length_app. cbn [List.length] in Hcount |- *. lia.
Qed.

(** The suffix-parametric theorem preserves arbitrary pending work and value
    prefixes. The root theorem below is its actual empty-context instance. *)
Lemma ordered_unfolding_supplies_child_executions : forall fuel graph owner references trees,
  Forall (fun child => child < owner) references ->
  unfold_ordered (unfold_graph fuel graph) references = Some trees ->
  (forall child tree, unfold_graph fuel graph child = Some tree -> ChildExecution graph child tree) ->
  Forall2 (fun child tree => child < owner /\ ChildExecution graph child tree) references trees.
Proof.
  intros fuel graph owner references trees HR HU HE.
  pose proof (ordered_unfolding_pairs_each_reference_with_its_result _ _
    (unfold_graph fuel graph) references trees HU) as HP.
  clear HU. revert HR. induction HP; intro HR.
  - constructor.
  - inversion HR; subst. constructor; [split; [assumption|now apply HE]|now apply IHHP].
Qed.

Theorem graph_machine_interprets_unfolding_with_bounded_stacks : forall fuel graph index tree,
  FreshDescriptorsAdmitted graph ->
  unfold_graph fuel graph index = Some tree -> ChildExecution graph index tree.
Proof.
  induction fuel as [|fuel IH]; intros graph index tree HD Htree;
    cbn -[Nat.ltb forallb unfold_ordered] in Htree; [discriminate|].
  unfold ChildExecution. intros pending prefix.
  pose proof (single_visit_and_single_result_always_fit (initial_node_arity graph) index) as [HJ HV].
  destruct (nth_error graph index) as [[scalar|lhs rhs|descriptor body injections]|] eqn:Hnode;
    try discriminate.
  - inversion Htree; subst. cbn [tree_denotation].
    eapply BoundedCons.
    + unfold fits; cbn [jobs values List.length]; lia.
    + apply scalar_step. exact Hnode.
    + apply BoundedRefl. unfold fits; cbn [jobs values]. rewrite length_app. cbn [List.length]; lia.
  - destruct ((lhs <? index) && (rhs <? index)) eqn:Hprior; [|discriminate].
    destruct (unfold_graph fuel graph lhs) as [ltree|] eqn:Hlhs; [|discriminate].
    destruct (unfold_graph fuel graph rhs) as [rtree|] eqn:Hrhs; [|discriminate].
    inversion Htree; subst. cbn [tree_denotation].
    pose proof Hprior as Horder. apply andb_true_iff in Horder as [HL HR].
    apply Nat.ltb_lt in HL. apply Nat.ltb_lt in HR.
    assert (HO : 0 < index) by lia.
    assert (HA : initial_node_arity graph index = 2) by (unfold initial_node_arity; now rewrite Hnode).
    assert (HC : Forall2 (fun child tree => child < index /\ ChildExecution graph child tree)
      [lhs; rhs] [ltree; rtree]).
    { constructor; [split; [exact HL|exact (IH graph lhs ltree HD Hlhs)]|].
      constructor; [split; [exact HR|exact (IH graph rhs rtree HD Hrhs)]|constructor]. }
    pose proof (combining_nonleaf_fits_all_completed_children (initial_node_arity graph) index HO) as Hvalues.
    rewrite HA in Hvalues.
    eapply BoundedCons.
    + unfold fits; cbn [jobs values List.length]; lia.
    + apply append_enter_step; eassumption.
    + eapply bounded_steps_trans.
      * pose proof (ordered_child_executions_compose graph index [lhs; rhs] [ltree; rtree]
          HC (Append index) pending prefix [] HO ltac:(cbn; symmetry; exact HA)) as HE.
        cbn [map app] in HE. rewrite app_nil_r in HE. exact HE.
      * eapply BoundedCons.
        -- unfold fits; cbn [jobs values List.length]. rewrite length_app. cbn [List.length]; lia.
        -- apply append_combine_step.
        -- apply BoundedRefl. unfold fits; cbn [jobs values]. rewrite length_app. cbn [List.length]; lia.
  - destruct (forallb (fun child => child <? index) (body :: injections)) eqn:Hprior; [|discriminate].
    destruct (unfold_graph fuel graph body) as [body_tree|] eqn:HB; [|discriminate].
    destruct (unfold_ordered (unfold_graph fuel graph) injections) as [trees|] eqn:HI; [|discriminate].
    inversion Htree; subst. cbn [tree_denotation].
    assert (HR : Forall (fun child => child < index) (body :: injections)).
    { apply Forall_forall. intros child HC. apply Nat.ltb_lt.
      now apply (proj1 (forallb_forall _ _) Hprior). }
    assert (HO : 0 < index) by (inversion HR; subst; lia).
    assert (HA : initial_node_arity graph index = S (List.length injections))
      by (unfold initial_node_arity; now rewrite Hnode).
    destruct (HD index descriptor body injections Hnode) as [Hadmit Hkeys].
    pose proof (ordered_unfolding_preserves_length _ _ (unfold_graph fuel graph) injections trees HI) as Hlength.
    assert (HC : Forall2 (fun child tree => child < index /\ ChildExecution graph child tree)
      (body :: injections) (body_tree :: trees)).
    { apply (ordered_unfolding_supplies_child_executions fuel graph index); [exact HR| |].
      - cbn [unfold_ordered]. now rewrite HB, HI.
      - intros child result HE. exact (IH graph child result HD HE). }
    pose proof (combining_nonleaf_fits_all_completed_children (initial_node_arity graph) index HO) as Hvalues.
    rewrite HA in Hvalues.
    eapply BoundedCons.
    + unfold fits; cbn [jobs values List.length]; lia.
    + eapply fresh_enter_step; eassumption.
    + eapply bounded_steps_trans.
      * pose proof (ordered_child_executions_compose graph index (body :: injections) (body_tree :: trees)
          HC (Fresh index) pending prefix [] HO ltac:(cbn; symmetry; exact HA)) as HE.
        cbn [map app] in HE. rewrite app_nil_r in HE. exact HE.
      * eapply BoundedCons.
        -- unfold fits; cbn [jobs values List.length]. rewrite length_app. cbn [List.length].
           rewrite length_map. lia.
        -- eapply fresh_combine_step; [exact Hnode|exact Hadmit|]. rewrite length_map. lia.
        -- apply BoundedRefl. unfold fits; cbn [jobs values]. rewrite length_app. cbn [List.length]; lia.
Qed.

Corollary valid_root_has_exact_bounded_machine_execution : forall graph index,
  EarlierReferences graph -> FreshDescriptorsAdmitted graph -> nth_error graph index <> None ->
  exists tree,
    unfold_graph (S index) graph index = Some tree /\
    BoundedSteps graph
      (job_allowance (initial_node_arity graph) index + 1)
      (value_allowance (initial_node_arity graph) index + 1)
      {| jobs := [Visit index]; values := [] |}
      {| jobs := []; values := [tree_denotation tree] |}.
Proof.
  intros graph index Hprior HD Hexists.
  destruct (root_index_bounds_unfolded_depth graph index Hprior Hexists)
    as [tree [Htree Hdepth]]. exists tree. split; [exact Htree|].
  eapply bounded_steps_weaken.
  - exact (graph_machine_interprets_unfolding_with_bounded_stacks
      (S index) graph index tree HD Htree [] []).
  - cbn [List.length]; lia.
  - cbn [List.length]; lia.
Qed.

Corollary binary_root_retains_the_original_machine_capacities : forall graph index,
  EarlierReferences graph -> FreshDescriptorsAdmitted graph -> nth_error graph index <> None ->
  (forall child, child <= index -> initial_node_arity graph child <= 2) ->
  exists tree,
    unfold_graph (S index) graph index = Some tree /\
    BoundedSteps graph (2 * S index + 1) (S index + 1)
      {| jobs := [Visit index]; values := [] |}
      {| jobs := []; values := [tree_denotation tree] |}.
Proof.
  intros graph index HR HD HE HB.
  destruct (valid_root_has_exact_bounded_machine_execution graph index HR HD HE)
    as [tree [HU HS]].
  pose proof (initial_graph_keeps_its_exact_existing_capacity_formula graph index HB) as [HJ HV].
  rewrite HJ, HV in HS. exists tree. auto.
Qed.

Theorem fresh_combine_underflow_never_constructs_a_substitute :
    forall graph index descriptor body references pending supplied,
  nth_error graph index = Some (FreshNode descriptor body references) ->
  List.length supplied < S (List.length (descriptor_keys descriptor)) ->
  graph_step graph {| jobs := Fresh index :: pending; values := supplied |} = None.
Proof.
  intros graph index descriptor body references pending supplied Hnode Hshort.
  cbn [graph_step jobs values]. rewrite Hnode.
  now rewrite fresh_transition_underflow_preserves_the_entire_stack by exact Hshort.
Qed.

(** One body and five injection occurrences all reference the same scalar.
    Descriptor admission checks five distinct keys, not five distinct values. *)
Definition wide_fresh_descriptor : FreshDescriptor :=
  {| descriptor_shape := PlainShape 0; descriptor_keys := ["a"; "b"; "c"; "d"; "e"]%string |}.
Definition wide_fresh_graph : list InitialNode :=
  [ScalarNode (TextScalar "x"); FreshNode wide_fresh_descriptor 0 (repeat 0 5)].

Example wide_fresh_unfolding_keeps_all_six_occurrences :
  unfold_graph 2 wide_fresh_graph 1 =
  Some (FreshTree wide_fresh_descriptor (ScalarTree (TextScalar "x"))
    (repeat (ScalarTree (TextScalar "x")) 5)).
Proof. reflexivity. Qed.

Example wide_fresh_executes_with_the_arity_sensitive_bounds :
  BoundedSteps wide_fresh_graph 9 7
    {| jobs := [Visit 1]; values := [] |}
    {| jobs := []; values := [fresh_denotation wide_fresh_descriptor (text "x") (repeat (text "x") 5)] |}.
Proof.
  assert (HR : EarlierReferences wide_fresh_graph).
  { split.
    - intros [|[|index]] lhs rhs H; cbn in H; try discriminate; destruct index; discriminate.
    - intros [|[|index]] descriptor body injections H; cbn in H; try discriminate;
        try (destruct index; discriminate).
      inversion H; subst. repeat constructor. }
  assert (HD : FreshDescriptorsAdmitted wide_fresh_graph).
  { intros [|[|index]] descriptor body injections H; cbn in H; try discriminate;
      try (destruct index; discriminate).
    inversion H; subst. split; reflexivity. }
  destruct (valid_root_has_exact_bounded_machine_execution wide_fresh_graph 1 HR HD ltac:(discriminate))
    as [tree [HU HS]].
  rewrite wide_fresh_unfolding_keeps_all_six_occurrences in HU. inversion HU; subst. exact HS.
Qed.

Example wide_fresh_expansion_exceeds_the_old_binary_job_capacity :
  graph_step wide_fresh_graph {| jobs := [Visit 1]; values := [] |} =
  Some {| jobs := repeat (Visit 0) 6 ++ [Fresh 1]; values := [] |} /\
  2 * S 1 + 1 < List.length (repeat (Visit 0) 6 ++ [Fresh 1]).
Proof. split; [reflexivity|cbn; lia]. Qed.

Print Assumptions integer_denotation_reuses_checked_constructor.
Print Assumptions bound_denotation_reuses_checked_constructor.
Print Assumptions wildcard_denotation_retains_its_exact_connective_policy.
Print Assumptions bounded_steps_trans.
Print Assumptions bounded_steps_weaken.
Print Assumptions scalar_step.
Print Assumptions append_enter_step.
Print Assumptions append_combine_step.
Print Assumptions fresh_enter_step.
Print Assumptions fresh_combine_step.
Print Assumptions ordered_child_executions_compose.
Print Assumptions ordered_unfolding_supplies_child_executions.
Print Assumptions graph_machine_interprets_unfolding_with_bounded_stacks.
Print Assumptions valid_root_has_exact_bounded_machine_execution.
Print Assumptions binary_root_retains_the_original_machine_capacities.
Print Assumptions fresh_combine_underflow_never_constructs_a_substitute.
Print Assumptions wide_fresh_unfolding_keeps_all_six_occurrences.
Print Assumptions wide_fresh_executes_with_the_arity_sensitive_bounds.
Print Assumptions wide_fresh_expansion_exceeds_the_old_binary_job_capacity.
