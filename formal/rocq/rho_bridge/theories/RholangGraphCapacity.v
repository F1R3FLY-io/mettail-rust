(** Capacity arithmetic for the existing eager, source-ordered graph worker.

    A node at rank r has only earlier children. Entering an n-child node puts
    n visits and one combine on the work stack. While child k runs (zero-based),
    n-k jobs and k completed values remain from this parent. The two inequalities
    below discharge exactly these suffix-parametric induction obligations.

    Surplus counts arity beyond two once per graph index in the root prefix,
    not once per unfolded occurrence. This is sound for peak stacks because
    active ancestors have strictly decreasing ranks. Repeated siblings run in
    sequence; they can still incur repeated execution and clone costs.

    These arithmetic lemmas alone do not establish execution of a Fresh graph
    node. RholangInitialGraphMachine instantiates them at every transition.
    They bound retained work/value slots, not split-off child vectors, metadata,
    node clone/drop workspaces, total allocation volume, or machine-integer
    representability. Those remain distinct preconstruction obligations. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import RholangInitialGraphInterpretation.

(** prefix_surplus arity count includes indices strictly below count. *)
Fixpoint prefix_surplus (arity : nat -> nat) (count : nat) : nat :=
  match count with
  | 0 => 0
  | S previous => prefix_surplus arity previous + (arity previous - 2)
  end.

Definition job_allowance arity rank := 2 * S rank + prefix_surplus arity (S rank).
Definition value_allowance arity rank := S rank + prefix_surplus arity (S rank).

Theorem prefix_surplus_is_monotone : forall arity first last,
  first <= last -> prefix_surplus arity first <= prefix_surplus arity last.
Proof. intros arity first last H. induction H; cbn; lia. Qed.

Theorem child_surplus_fits_before_its_parent : forall arity child parent,
  child < parent -> prefix_surplus arity (S child) <= prefix_surplus arity parent.
Proof. intros. apply prefix_surplus_is_monotone. lia. Qed.

Theorem child_work_and_pending_siblings_fit_parent_allowance :
    forall arity parent child position,
  child < parent -> position < arity parent ->
  (arity parent - position) + job_allowance arity child <= job_allowance arity parent.
Proof.
  intros arity parent child position HR HP.
  pose proof (child_surplus_fits_before_its_parent arity child parent HR) as HB.
  unfold job_allowance. cbn [prefix_surplus] in HB |- *.
  assert (HN : arity parent <= 2 + (arity parent - 2)) by lia.
  lia.
Qed.

Theorem child_values_and_completed_siblings_fit_parent_allowance :
    forall arity parent child position,
  child < parent -> position < arity parent ->
  position + value_allowance arity child <= value_allowance arity parent.
Proof.
  intros arity parent child position HR HP.
  pose proof (child_surplus_fits_before_its_parent arity child parent HR) as HB.
  unfold value_allowance. cbn [prefix_surplus] in HB |- *.
  assert (HK : position <= 1 + (arity parent - 2)) by lia.
  lia.
Qed.

Theorem entering_nonleaf_fits_all_pending_visits_and_combine : forall arity parent,
  0 < parent -> S (arity parent) <= job_allowance arity parent.
Proof. intros. unfold job_allowance. cbn [prefix_surplus]. lia. Qed.

Theorem combining_nonleaf_fits_all_completed_children : forall arity parent,
  0 < parent -> arity parent <= value_allowance arity parent.
Proof. intros. unfold value_allowance. cbn [prefix_surplus]. lia. Qed.

Theorem single_visit_and_single_result_always_fit : forall arity rank,
  1 <= job_allowance arity rank /\ 1 <= value_allowance arity rank.
Proof. intros. unfold job_allowance, value_allowance. lia. Qed.

Theorem only_arities_in_the_root_prefix_affect_capacity : forall arity other count,
  (forall index, index < count -> arity index = other index) ->
  prefix_surplus arity count = prefix_surplus other count.
Proof.
  intros arity other count. induction count as [|count IH]; intro H; [reflexivity|].
  cbn [prefix_surplus]. rewrite IH by (intros; apply H; lia).
  rewrite H by lia. reflexivity.
Qed.

Theorem binary_prefix_has_zero_surplus : forall arity count,
  (forall index, index < count -> arity index <= 2) -> prefix_surplus arity count = 0.
Proof.
  intros arity count. induction count as [|count IH]; intro H; [reflexivity|].
  cbn [prefix_surplus]. rewrite IH by (intros; apply H; lia).
  specialize (H count ltac:(lia)). lia.
Qed.

Definition initial_node_arity (graph : list InitialNode) (index : nat) : nat :=
  match nth_error graph index with
  | Some (AppendNode _ _) => 2
  | Some (FreshNode _ _ injections) => S (length injections)
  | _ => 0
  end.

Theorem initial_graph_keeps_its_exact_existing_capacity_formula : forall graph root,
  (forall index, index <= root -> initial_node_arity graph index <= 2) ->
  job_allowance (initial_node_arity graph) root + 1 = 2 * S root + 1 /\
  value_allowance (initial_node_arity graph) root + 1 = S root + 1.
Proof.
  intros graph root Hbinary.
  assert (HB : prefix_surplus (initial_node_arity graph) (S root) = 0).
  { apply binary_prefix_has_zero_surplus. intros index HI. apply Hbinary. lia. }
  unfold job_allowance, value_allowance. rewrite HB. lia.
Qed.

Theorem later_unreachable_nodes_do_not_change_initial_prefix_surplus :
    forall graph later count,
  count <= length graph ->
  prefix_surplus (initial_node_arity (graph ++ later)) count =
  prefix_surplus (initial_node_arity graph) count.
Proof.
  intros graph later count H. apply only_arities_in_the_root_prefix_affect_capacity.
  intros index HI. unfold initial_node_arity. now rewrite nth_error_app1 by lia.
Qed.

Print Assumptions prefix_surplus_is_monotone.
Print Assumptions child_surplus_fits_before_its_parent.
Print Assumptions child_work_and_pending_siblings_fit_parent_allowance.
Print Assumptions child_values_and_completed_siblings_fit_parent_allowance.
Print Assumptions entering_nonleaf_fits_all_pending_visits_and_combine.
Print Assumptions combining_nonleaf_fits_all_completed_children.
Print Assumptions single_visit_and_single_result_always_fit.
Print Assumptions only_arities_in_the_root_prefix_affect_capacity.
Print Assumptions binary_prefix_has_zero_surplus.
Print Assumptions initial_graph_keeps_its_exact_existing_capacity_formula.
Print Assumptions later_unreachable_nodes_do_not_change_initial_prefix_surplus.
