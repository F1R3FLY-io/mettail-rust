(** The concrete Visit/Append interpreter for initial construction graphs.

    Values are oldest-first, like the reused Worklist value vector. Work is
    top-first. No source terms are visited here. Integer range admission is
    separate: scalar denotation agrees with the existing checked integer
    constructor on its signed-64-bit domain, rather than truncating integers.

    The bounded execution relation records every intermediate state, allowing
    stack capacities to be established for the actual graph machine, not merely
    inferred from the denotation's tree depth. Resource debits and the actual
    Rust constructor bodies have separate correspondence obligations. *)
From Stdlib Require Import List Arith Lia Bool String ZArith.
From RhoBridge Require Import RholangInitialGraphInterpretation
  RholangTargetConstruction RholangWorklistConstruction RholangConstructionProtocol.
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

Fixpoint tree_denotation (tree : InitialTree) : Value :=
  match tree with
  | ScalarTree scalar => scalar_denotation scalar
  | AppendTree lhs_tree rhs_tree => append (tree_denotation lhs_tree) (tree_denotation rhs_tree)
  end.

Inductive GraphJob := Visit (index : nat) | Append (index : nat).
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
    | None => None
    end
  | Append _ :: pending =>
    match reduce_pair (fun lhs rhs => @Built _ unit (append lhs rhs)) (values state) with
    | Completed result => Some {| jobs := pending; values := result |}
    | _ => None
    end
  end.

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

(** The suffix-parametric theorem preserves arbitrary pending work and value
    prefixes. The root theorem below is its actual empty-context instance. *)
Theorem graph_machine_interprets_unfolding_with_bounded_stacks : forall fuel graph index tree,
  unfold_graph fuel graph index = Some tree -> forall pending prefix,
  BoundedSteps graph
    (List.length pending + 2 * tree_depth tree)
    (List.length prefix + tree_depth tree)
    {| jobs := Visit index :: pending; values := prefix |}
    {| jobs := pending; values := prefix ++ [tree_denotation tree] |}.
Proof.
  induction fuel as [|fuel IH]; intros graph index tree Htree pending prefix;
    cbn -[Nat.ltb] in Htree; [discriminate|].
  destruct (nth_error graph index) as [[scalar|lhs rhs]|] eqn:Hnode; try discriminate.
  - inversion Htree; subst. cbn [tree_depth tree_denotation].
    eapply BoundedCons.
    + unfold fits; cbn; lia.
    + apply scalar_step. exact Hnode.
    + apply BoundedRefl. unfold fits; cbn. rewrite length_app. cbn; lia.
  - destruct ((lhs <? index) && (rhs <? index)) eqn:Hprior; [|discriminate].
    destruct (unfold_graph fuel graph lhs) as [ltree|] eqn:Hlhs; [|discriminate].
    destruct (unfold_graph fuel graph rhs) as [rtree|] eqn:Hrhs; [|discriminate].
    inversion Htree; subst. cbn [tree_depth tree_denotation].
    pose proof (tree_depth_positive ltree) as Hdepthl.
    pose proof (tree_depth_positive rtree) as Hdepthr.
    pose proof (Nat.le_max_l (tree_depth ltree) (tree_depth rtree)) as Hmaxl.
    pose proof (Nat.le_max_r (tree_depth ltree) (tree_depth rtree)) as Hmaxr.
    eapply BoundedCons.
    + unfold fits; cbn; lia.
    + apply append_enter_step; eassumption.
    + eapply bounded_steps_trans.
      * eapply bounded_steps_weaken.
        -- exact (IH graph lhs ltree Hlhs (Visit rhs :: Append index :: pending) prefix).
        -- cbn; lia.
        -- lia.
      * eapply bounded_steps_trans.
        -- eapply bounded_steps_weaken.
           ++ exact (IH graph rhs rtree Hrhs (Append index :: pending)
                (prefix ++ [tree_denotation ltree])).
           ++ cbn; lia.
           ++ rewrite length_app. cbn; lia.
        -- replace ((prefix ++ [tree_denotation ltree]) ++ [tree_denotation rtree])
             with (prefix ++ [tree_denotation ltree; tree_denotation rtree])
             by (rewrite <- app_assoc; reflexivity).
           eapply BoundedCons.
           ++ unfold fits; cbn. rewrite length_app. cbn; lia.
           ++ apply append_combine_step.
           ++ apply BoundedRefl. unfold fits; cbn. rewrite length_app. cbn; lia.
Qed.

Corollary valid_root_has_exact_bounded_machine_execution : forall graph index,
  EarlierReferences graph -> nth_error graph index <> None ->
  exists tree,
    unfold_graph (S index) graph index = Some tree /\
    BoundedSteps graph (2 * S index + 1) (S index + 1)
      {| jobs := [Visit index]; values := [] |}
      {| jobs := []; values := [tree_denotation tree] |}.
Proof.
  intros graph index Hprior Hexists.
  destruct (root_index_bounds_unfolded_depth graph index Hprior Hexists)
    as [tree [Htree Hdepth]]. exists tree. split; [exact Htree|].
  eapply bounded_steps_weaken.
  - exact (graph_machine_interprets_unfolding_with_bounded_stacks
      (S index) graph index tree Htree [] []).
  - cbn; lia.
  - cbn; lia.
Qed.

Print Assumptions integer_denotation_reuses_checked_constructor.
Print Assumptions bound_denotation_reuses_checked_constructor.
Print Assumptions wildcard_denotation_retains_its_exact_connective_policy.
Print Assumptions bounded_steps_trans.
Print Assumptions bounded_steps_weaken.
Print Assumptions scalar_step.
Print Assumptions append_enter_step.
Print Assumptions append_combine_step.
Print Assumptions graph_machine_interprets_unfolding_with_bounded_stacks.
Print Assumptions valid_root_has_exact_bounded_machine_execution.
