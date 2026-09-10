(** Initial construction graph interpretation: finite occurrence unfolding.

    The graph is an append-only list, not a tree and not a memoized Par arena.
    Its two append references may coincide. Every reference is smaller than
    its owning index, which provides an actual termination rank independent
    of tree expansion size. Unreachable later nodes do not alter a root.

    This first boundary proves graph shape/unfolding facts. It does not yet
    certify an executable machine, scalar admission, charges or capacity. *)
From Stdlib Require Import List Arith Lia Bool String ZArith.
Import ListNotations.

Inductive InitialScalar :=
| EmptyScalar | IntegerScalar (value : Z) | BooleanScalar (value : bool)
| TextScalar (value : string)
| BoundScalar (scope index : nat)
| WildcardScalar (connective : bool).
Inductive InitialNode :=
| ScalarNode (scalar : InitialScalar)
| AppendNode (lhs rhs : nat).
Inductive InitialTree :=
| ScalarTree (scalar : InitialScalar)
| AppendTree (lhs rhs : InitialTree).

Definition EarlierReferences (graph : list InitialNode) : Prop :=
  forall index lhs rhs,
  nth_error graph index = Some (AppendNode lhs rhs) -> lhs < index /\ rhs < index.

Fixpoint unfold_graph (fuel : nat) (graph : list InitialNode) (index : nat)
    : option InitialTree :=
  match fuel with
  | 0 => None
  | S rest =>
    match nth_error graph index with
    | Some (ScalarNode scalar) => Some (ScalarTree scalar)
    | Some (AppendNode lhs rhs) =>
      if (lhs <? index) && (rhs <? index) then
        match unfold_graph rest graph lhs, unfold_graph rest graph rhs with
        | Some lhs_tree, Some rhs_tree => Some (AppendTree lhs_tree rhs_tree)
        | _, _ => None
        end
      else None
    | None => None
    end
  end.

Fixpoint tree_depth (tree : InitialTree) : nat :=
  match tree with
  | ScalarTree _ => 1
  | AppendTree lhs_tree rhs_tree => S (Nat.max (tree_depth lhs_tree) (tree_depth rhs_tree))
  end.

Theorem valid_graph_unfolding_exists : forall fuel graph index,
  EarlierReferences graph -> index < fuel -> nth_error graph index <> None ->
  exists tree, unfold_graph fuel graph index = Some tree.
Proof.
  induction fuel as [|fuel IH]; intros graph index Hprior Hfuel Hexists; [lia|].
  cbn -[Nat.ltb]. destruct (nth_error graph index) as [node|] eqn:Hnode; [|contradiction].
  destruct node as [scalar|lhs rhs].
  - exists (ScalarTree scalar). reflexivity.
  - pose proof (Hprior index lhs rhs Hnode) as [Hleft Hright].
    assert (Hlength : index < List.length graph) by (apply nth_error_Some; congruence).
    assert (Hlhs : nth_error graph lhs <> None) by (apply nth_error_Some; lia).
    assert (Hrhs : nth_error graph rhs <> None) by (apply nth_error_Some; lia).
    destruct (IH graph lhs Hprior ltac:(lia) Hlhs) as [left Eleft].
    destruct (IH graph rhs Hprior ltac:(lia) Hrhs) as [right Eright].
    assert (El : (lhs <? index) = true) by (apply Nat.ltb_lt; exact Hleft).
    assert (Er : (rhs <? index) = true) by (apply Nat.ltb_lt; exact Hright).
    rewrite El, Er, Eleft, Eright. exists (AppendTree left right). reflexivity.
Qed.

Theorem unfolding_depth_bounded_by_fuel : forall fuel graph index tree,
  unfold_graph fuel graph index = Some tree -> tree_depth tree <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros graph index tree H; cbn -[Nat.ltb] in H; [discriminate|].
  destruct (nth_error graph index) as [[scalar|lhs rhs]|] eqn:Hnode; try discriminate.
  - inversion H; subst; cbn; lia.
  - destruct ((lhs <? index) && (rhs <? index)); [|discriminate].
    destruct (unfold_graph fuel graph lhs) as [left|] eqn:Eleft; [|discriminate].
    destruct (unfold_graph fuel graph rhs) as [right|] eqn:Eright; [|discriminate].
    inversion H; subst; cbn.
    specialize (IH graph lhs left Eleft) as Hl.
    specialize (IH graph rhs right Eright) as Hr.
    apply le_n_S. apply Nat.max_lub; assumption.
Qed.

Corollary root_index_bounds_unfolded_depth : forall graph index,
  EarlierReferences graph -> nth_error graph index <> None ->
  exists tree, unfold_graph (S index) graph index = Some tree /\ tree_depth tree <= S index.
Proof.
  intros graph index Hprior Hexists.
  destruct (valid_graph_unfolding_exists (S index) graph index Hprior ltac:(lia) Hexists)
    as [tree Htree]. exists tree. split; [exact Htree|].
  now apply (unfolding_depth_bounded_by_fuel (S index) graph index).
Qed.

Theorem append_unfolding_preserves_both_ordered_children : forall fuel graph index lhs rhs left right,
  nth_error graph index = Some (AppendNode lhs rhs) -> lhs < index -> rhs < index ->
  unfold_graph fuel graph lhs = Some left -> unfold_graph fuel graph rhs = Some right ->
  unfold_graph (S fuel) graph index = Some (AppendTree left right).
Proof.
  intros fuel graph index lhs rhs left right Hnode Hl Hr El Er. cbn -[Nat.ltb].
  rewrite Hnode. apply Nat.ltb_lt in Hl. apply Nat.ltb_lt in Hr.
  now rewrite Hl, Hr, El, Er.
Qed.

Corollary repeated_reference_is_not_deduplicated : forall fuel graph index child tree,
  nth_error graph index = Some (AppendNode child child) -> child < index ->
  unfold_graph fuel graph child = Some tree ->
  unfold_graph (S fuel) graph index = Some (AppendTree tree tree).
Proof. intros. eapply append_unfolding_preserves_both_ordered_children; eauto. Qed.

Theorem appending_unreachable_nodes_preserves_unfolding : forall fuel graph later index,
  EarlierReferences graph -> index < List.length graph ->
  unfold_graph fuel (graph ++ later) index = unfold_graph fuel graph index.
Proof.
  induction fuel as [|fuel IH]; intros graph later index Hprior Hindex; [reflexivity|].
  cbn -[Nat.ltb]. rewrite nth_error_app1 by exact Hindex.
  destruct (nth_error graph index) as [[scalar|lhs rhs]|] eqn:Hnode; try reflexivity.
  pose proof (Hprior index lhs rhs Hnode) as [Hl Hr].
  rewrite IH by (try assumption; lia).
  rewrite IH by (try assumption; lia). reflexivity.
Qed.

Example shared_graph_has_two_occurrences :
  unfold_graph 2 [ScalarNode (TextScalar "x"); AppendNode 0 0] 1 =
  Some (AppendTree (ScalarTree (TextScalar "x")) (ScalarTree (TextScalar "x"))).
Proof. reflexivity. Qed.

Print Assumptions valid_graph_unfolding_exists.
Print Assumptions unfolding_depth_bounded_by_fuel.
Print Assumptions root_index_bounds_unfolded_depth.
Print Assumptions append_unfolding_preserves_both_ordered_children.
Print Assumptions repeated_reference_is_not_deduplicated.
Print Assumptions appending_unreachable_nodes_preserves_unfolding.
Print Assumptions shared_graph_has_two_occurrences.
