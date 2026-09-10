(** Initial construction graph interpretation: finite occurrence unfolding.

    The graph is an append-only list, not a tree and not a memoized Par arena.
    Its two append references may coincide. Every reference is smaller than
    its owning index, which provides an actual termination rank independent
    of tree expansion size. Unreachable later nodes do not alter a root.

    This first boundary proves graph shape/unfolding facts. It does not yet
    certify an executable machine, scalar admission, charges or capacity. *)
From Stdlib Require Import List Arith Lia Bool String ZArith.
From RhoBridge Require Import RholangFreshDescriptor.
Import ListNotations.

Inductive InitialScalar :=
| EmptyScalar | IntegerScalar (value : Z) | BooleanScalar (value : bool)
| TextScalar (value : string)
| BoundScalar (scope index : nat)
| WildcardScalar (connective : bool).
Inductive InitialNode :=
| ScalarNode (scalar : InitialScalar)
| AppendNode (lhs rhs : nat)
| FreshNode (descriptor : FreshDescriptor) (body : nat) (injections : list nat).
Inductive InitialTree :=
| ScalarTree (scalar : InitialScalar)
| AppendTree (lhs rhs : InitialTree)
| FreshTree (descriptor : FreshDescriptor) (body : InitialTree) (injections : list InitialTree).

Definition EarlierReferences (graph : list InitialNode) : Prop :=
  (forall index lhs rhs,
    nth_error graph index = Some (AppendNode lhs rhs) -> lhs < index /\ rhs < index) /\
  (forall index descriptor body injections,
    nth_error graph index = Some (FreshNode descriptor body injections) ->
    Forall (fun child => child < index) (body :: injections)).

(** Shape unfolding preserves the descriptor unchanged. Its admission and
    key/child-count checks are separate from termination by earlier references,
    just as scalar range admission is separate from scalar shape unfolding. *)
Fixpoint unfold_ordered {A B} (step : A -> option B) (references : list A) : option (list B) :=
  match references with
  | [] => Some []
  | child :: rest =>
    match step child, unfold_ordered step rest with
    | Some value, Some values => Some (value :: values)
    | _, _ => None
    end
  end.

Lemma ordered_unfolding_exists : forall A B (step : A -> option B) references,
  (forall child, In child references -> exists value, step child = Some value) ->
  exists values, unfold_ordered step references = Some values.
Proof.
  intros A B step references. induction references as [|child rest IH]; intro H.
  - exists []. reflexivity.
  - destruct (H child ltac:(now left)) as [value HV].
    destruct (IH ltac:(intros; apply H; now right)) as [values HS].
    cbn. rewrite HV, HS. eauto.
Qed.

Lemma ordered_unfolding_preserves_length : forall A B (step : A -> option B) references values,
  unfold_ordered step references = Some values -> List.length values = List.length references.
Proof.
  intros A B step references. induction references as [|child rest IH]; intros values H; cbn in H.
  - inversion H. reflexivity.
  - destruct (step child); [|discriminate].
    destruct (unfold_ordered step rest) eqn:HS; [|discriminate].
    inversion H; subst. cbn. now rewrite (IH _ eq_refl).
Qed.

Lemma ordered_unfolding_preserves_result_property : forall A B (step : A -> option B)
    (property : B -> Prop) references values,
  (forall child value, step child = Some value -> property value) ->
  unfold_ordered step references = Some values -> Forall property values.
Proof.
  intros A B step property references. induction references as [|child rest IH]; intros values HP H;
    cbn in H.
  - inversion H. constructor.
  - destruct (step child) eqn:HV; [|discriminate].
    destruct (unfold_ordered step rest) eqn:HS; [|discriminate].
    inversion H; subst. constructor; [eapply HP; eauto|eapply IH; eauto].
Qed.

Lemma ordered_unfolding_extensional : forall A B (step other : A -> option B) references,
  (forall child, In child references -> step child = other child) ->
  unfold_ordered step references = unfold_ordered other references.
Proof.
  intros A B step other references. induction references as [|child rest IH]; intro H; [reflexivity|].
  cbn. rewrite H by (now left). rewrite IH by (intros; apply H; now right). reflexivity.
Qed.

Lemma ordered_unfolding_pairs_each_reference_with_its_result : forall A B
    (step : A -> option B) references values,
  unfold_ordered step references = Some values ->
  Forall2 (fun reference value => step reference = Some value) references values.
Proof.
  intros A B step references. induction references as [|child rest IH]; intros values H; cbn in H.
  - inversion H. constructor.
  - destruct (step child) eqn:HC; [|discriminate].
    destruct (unfold_ordered step rest) eqn:HS; [|discriminate].
    inversion H; subst. constructor; [exact HC|now apply IH].
Qed.

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
    | Some (FreshNode descriptor body injections) =>
      if forallb (fun child => child <? index) (body :: injections) then
        match unfold_graph rest graph body, unfold_ordered (unfold_graph rest graph) injections with
        | Some body_tree, Some injection_trees => Some (FreshTree descriptor body_tree injection_trees)
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
  | FreshTree _ body injections =>
    S (Nat.max (tree_depth body)
      (fold_right (fun child depth => Nat.max (tree_depth child) depth) 0 injections))
  end.

Lemma ordered_depths_share_their_upper_bound : forall trees bound,
  Forall (fun tree => tree_depth tree <= bound) trees ->
  fold_right (fun child depth => Nat.max (tree_depth child) depth) 0 trees <= bound.
Proof.
  intros trees bound H. induction H; cbn; [lia|].
  apply Nat.max_lub; assumption.
Qed.

Theorem valid_graph_unfolding_exists : forall fuel graph index,
  EarlierReferences graph -> index < fuel -> nth_error graph index <> None ->
  exists tree, unfold_graph fuel graph index = Some tree.
Proof.
  induction fuel as [|fuel IH]; intros graph index Hprior Hfuel Hexists; [lia|].
  cbn -[Nat.ltb forallb unfold_ordered]. destruct (nth_error graph index) as [node|] eqn:Hnode; [|contradiction].
  destruct node as [scalar|lhs rhs|descriptor body injections].
  - exists (ScalarTree scalar). reflexivity.
  - pose proof (proj1 Hprior index lhs rhs Hnode) as [Hleft Hright].
    assert (Hlength : index < List.length graph) by (apply nth_error_Some; congruence).
    assert (Hlhs : nth_error graph lhs <> None) by (apply nth_error_Some; lia).
    assert (Hrhs : nth_error graph rhs <> None) by (apply nth_error_Some; lia).
    destruct (IH graph lhs Hprior ltac:(lia) Hlhs) as [left Eleft].
    destruct (IH graph rhs Hprior ltac:(lia) Hrhs) as [right Eright].
    assert (El : (lhs <? index) = true) by (apply Nat.ltb_lt; exact Hleft).
    assert (Er : (rhs <? index) = true) by (apply Nat.ltb_lt; exact Hright).
    rewrite El, Er, Eleft, Eright. exists (AppendTree left right). reflexivity.
  - pose proof (proj2 Hprior index descriptor body injections Hnode) as Hchildren.
    assert (Hcheck : forallb (fun child => child <? index) (body :: injections) = true).
    { apply forallb_forall. intros child HI. apply Nat.ltb_lt.
      now apply (proj1 (Forall_forall _ _) Hchildren). }
    rewrite Hcheck.
    inversion Hchildren as [|? ? Hbody Hinjections]; subst.
    assert (Hlength : index < List.length graph) by (apply nth_error_Some; congruence).
    destruct (IH graph body Hprior ltac:(lia)
      ltac:(apply nth_error_Some; lia)) as [body_tree HB].
    destruct (ordered_unfolding_exists _ _ (unfold_graph fuel graph) injections)
      as [injection_trees HI].
    { intros child HC. pose proof (proj1 (Forall_forall _ _) Hinjections child HC) as HR.
      change (child < index) in HR.
      exact (IH graph child Hprior ltac:(lia) ltac:(apply nth_error_Some; lia)). }
    rewrite HB, HI. eauto.
Qed.

Theorem unfolding_depth_bounded_by_fuel : forall fuel graph index tree,
  unfold_graph fuel graph index = Some tree -> tree_depth tree <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros graph index tree H;
    cbn -[Nat.ltb forallb unfold_ordered] in H; [discriminate|].
  destruct (nth_error graph index) as [[scalar|lhs rhs|descriptor body injections]|] eqn:Hnode;
    try discriminate.
  - inversion H; subst; cbn; lia.
  - destruct ((lhs <? index) && (rhs <? index)); [|discriminate].
    destruct (unfold_graph fuel graph lhs) as [left|] eqn:Eleft; [|discriminate].
    destruct (unfold_graph fuel graph rhs) as [right|] eqn:Eright; [|discriminate].
    inversion H; subst; cbn.
    specialize (IH graph lhs left Eleft) as Hl.
    specialize (IH graph rhs right Eright) as Hr.
    apply le_n_S. apply Nat.max_lub; assumption.
  - destruct (forallb (fun child => child <? index) (body :: injections)); [|discriminate].
    destruct (unfold_graph fuel graph body) as [body_tree|] eqn:HB; [|discriminate].
    destruct (unfold_ordered (unfold_graph fuel graph) injections) as [trees|] eqn:HI;
      [|discriminate].
    inversion H; subst. cbn [tree_depth]. apply le_n_S. apply Nat.max_lub.
    + eapply IH; eauto.
    + pose proof (ordered_unfolding_preserves_result_property _ _ (unfold_graph fuel graph)
        (fun tree => tree_depth tree <= fuel) injections trees (IH graph) HI) as HP.
      now apply ordered_depths_share_their_upper_bound.
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
  cbn -[Nat.ltb forallb unfold_ordered]. rewrite nth_error_app1 by exact Hindex.
  destruct (nth_error graph index) as [[scalar|lhs rhs|descriptor body injections]|] eqn:Hnode;
    try reflexivity.
  - pose proof (proj1 Hprior index lhs rhs Hnode) as [Hl Hr].
    rewrite IH by (try assumption; lia).
    rewrite IH by (try assumption; lia). reflexivity.
  - pose proof (proj2 Hprior index descriptor body injections Hnode) as Hchildren.
    inversion Hchildren as [|? ? Hbody Hinjections]; subst.
    rewrite IH by (try assumption; lia).
    rewrite (ordered_unfolding_extensional _ _ (unfold_graph fuel (graph ++ later))
      (unfold_graph fuel graph) injections).
    + reflexivity.
    + intros child HC. apply IH; [exact Hprior|].
      pose proof (proj1 (Forall_forall _ _) Hinjections child HC) as HR.
      change (child < index) in HR. lia.
Qed.

Theorem fresh_unfolding_preserves_body_and_ordered_injections :
    forall fuel graph index descriptor body injections body_tree injection_trees,
  nth_error graph index = Some (FreshNode descriptor body injections) ->
  Forall (fun child => child < index) (body :: injections) ->
  unfold_graph fuel graph body = Some body_tree ->
  unfold_ordered (unfold_graph fuel graph) injections = Some injection_trees ->
  unfold_graph (S fuel) graph index = Some (FreshTree descriptor body_tree injection_trees).
Proof.
  intros fuel graph index descriptor body injections body_tree injection_trees Hnode HR HB HI.
  cbn -[Nat.ltb forallb unfold_ordered]. rewrite Hnode.
  assert (HC : forallb (fun child => child <? index) (body :: injections) = true).
  { apply forallb_forall. intros child HC. apply Nat.ltb_lt.
    now apply (proj1 (Forall_forall _ _) HR). }
  now rewrite HC, HB, HI.
Qed.

Theorem fresh_non_earlier_child_prevents_unfolding :
    forall fuel graph index descriptor body injections child,
  nth_error graph index = Some (FreshNode descriptor body injections) ->
  In child (body :: injections) -> index <= child ->
  unfold_graph (S fuel) graph index = None.
Proof.
  intros fuel graph index descriptor body injections child Hnode HI HR.
  cbn -[Nat.ltb forallb unfold_ordered]. rewrite Hnode.
  destruct (forallb (fun child => child <? index) (body :: injections)) eqn:HC; [|reflexivity].
  pose proof (proj1 (forallb_forall _ _) HC child HI) as Hbefore.
  apply Nat.ltb_lt in Hbefore. exfalso. lia.
Qed.

Example shared_graph_has_two_occurrences :
  unfold_graph 2 [ScalarNode (TextScalar "x"); AppendNode 0 0] 1 =
  Some (AppendTree (ScalarTree (TextScalar "x")) (ScalarTree (TextScalar "x"))).
Proof. reflexivity. Qed.

Print Assumptions valid_graph_unfolding_exists.
Print Assumptions ordered_unfolding_exists.
Print Assumptions ordered_unfolding_preserves_length.
Print Assumptions ordered_unfolding_preserves_result_property.
Print Assumptions ordered_unfolding_extensional.
Print Assumptions ordered_unfolding_pairs_each_reference_with_its_result.
Print Assumptions fresh_unfolding_preserves_body_and_ordered_injections.
Print Assumptions fresh_non_earlier_child_prevents_unfolding.
Print Assumptions unfolding_depth_bounded_by_fuel.
Print Assumptions root_index_bounds_unfolded_depth.
Print Assumptions append_unfolding_preserves_both_ordered_children.
Print Assumptions repeated_reference_is_not_deduplicated.
Print Assumptions appending_unreachable_nodes_preserves_unfolding.
Print Assumptions shared_graph_has_two_occurrences.
