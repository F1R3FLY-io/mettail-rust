(** Inherited binding state for the existing structural worklist fold.

    Each child receives state derived from its parent, never a preceding
    sibling's result. Scope-body edges increment depth; ordinary/pre-field
    edges do not. Clone ignores binding-edge roles.

    The function-valued carrier specifies the semantics, not Rust closure
    allocation. Defunctionalization into Visit(depth)/Assemble result slots
    remains a separate source-correspondence obligation. Tags and edge roles
    must come from the generated field layout. The algebra is universally
    quantified, not a Boolean premise that an engine is correct. Actual
    native/FLT/HashBag reconstruction is not established by this theorem.

    Clone's shallow Arc boundary must be reflected by its source projection
    and algebra; the abstract tree theorem does not prove pointer sharing. *)

From Stdlib Require Import List Arith Lia.
From Trampoline Require Import WorklistFoldEquivalence.
Import ListNotations.

Module InheritedBindingFold.

Inductive Operation := CloneOperation | OpenOperation | CloseOperation.
Inductive EdgeRole := OrdinaryChild | ScopeBodyChild.

(** Keep the ceiling symbolic rather than expanding a huge Peano number. *)
Definition u32_depth_ceiling : nat := Nat.pred (Nat.pow 2 32).

Definition checked_successor (maximum depth : nat) : option nat :=
  if depth <? maximum then Some (S depth) else None.

Definition child_depth maximum operation depth role : option nat :=
  match operation, role with
  | CloneOperation, _ => Some depth
  | _, OrdinaryChild => Some depth
  | _, ScopeBodyChild => checked_successor maximum depth
  end.

Theorem ordinary_child_keeps_parent_depth :
  forall maximum operation depth,
  child_depth maximum operation depth OrdinaryChild = Some depth.
Proof. intros maximum [] depth; reflexivity. Qed.

Theorem clone_ignores_binding_edges :
  forall maximum depth role,
  child_depth maximum CloneOperation depth role = Some depth.
Proof. reflexivity. Qed.

Theorem checked_successor_is_exact :
  forall maximum depth next,
  checked_successor maximum depth = Some next ->
  next = S depth /\ next <= maximum.
Proof.
  intros maximum depth next H. unfold checked_successor in H.
  destruct (depth <? maximum) eqn:HF; [|discriminate].
  apply Nat.ltb_lt in HF. inversion H; subst. split; [reflexivity|lia].
Qed.

Theorem overflowing_depth_is_rejected :
  forall maximum depth,
  maximum <= depth -> checked_successor maximum depth = None.
Proof.
  intros maximum depth H. unfold checked_successor.
  assert (HF : (depth <? maximum) = false) by
    (apply Nat.ltb_ge; exact H).
  now rewrite HF.
Qed.

Theorem binding_scope_body_increments_exactly_once :
  forall maximum operation depth next,
  operation <> CloneOperation ->
  child_depth maximum operation depth ScopeBodyChild = Some next ->
  next = S depth /\ next <= maximum.
Proof.
  intros maximum operation depth next Hnot H.
  destruct operation; [contradiction| |];
    apply checked_successor_is_exact; exact H.
Qed.

Section Fold.

Context {A : Type}.
Variable maximum : nat.
Variable role_of : nat -> nat -> EdgeRole.
Variable clone_algebra : nat -> list A -> A.
Variable binding_algebra : Operation -> nat -> nat -> list A -> option A.

Definition InheritedValue := Operation -> nat -> option A.

(** Indices are source-order child positions. Only the index advances when
    proceeding to a sibling: its parent depth is the original one. *)
Fixpoint evaluate_children
    (tag index : nat) (operation : Operation) (depth : nat)
    (children : list InheritedValue) : option (list A) :=
  match children with
  | [] => Some []
  | child :: rest =>
    match child_depth maximum operation depth (role_of tag index) with
    | None => None
    | Some assigned =>
      match child operation assigned with
      | None => None
      | Some value =>
        match evaluate_children tag (S index) operation depth rest with
        | None => None
        | Some values => Some (value :: values)
        end
      end
    end
  end.

Definition inherited_algebra
    (tag : nat) (children : list InheritedValue) : InheritedValue :=
  fun operation depth =>
    match evaluate_children tag 0 operation depth children with
    | None => None
    | Some values =>
      match operation with
      | CloneOperation => Some (clone_algebra tag values)
      | OpenOperation | CloseOperation =>
        binding_algebra operation depth tag values
      end
    end.

Definition inherited_fold (input : tree) : InheritedValue :=
  recursive_fold InheritedValue inherited_algebra input.

Theorem node_uses_source_order_assigned_children :
  forall tag children operation depth,
  inherited_fold (Node tag children) operation depth =
  inherited_algebra tag
    (recursive_folds InheritedValue inherited_algebra children)
    operation depth.
Proof. reflexivity. Qed.

Theorem siblings_do_not_inherit_each_others_depth :
  forall tag index operation depth first second dfirst dsecond x y,
  child_depth maximum operation depth (role_of tag index) = Some dfirst ->
  child_depth maximum operation depth (role_of tag (S index)) = Some dsecond ->
  first operation dfirst = Some x ->
  second operation dsecond = Some y ->
  evaluate_children tag index operation depth [first; second] = Some [x; y].
Proof.
  intros tag index operation depth first second dfirst dsecond x y
    HF HS HX HY.
  cbn [evaluate_children]. now rewrite HF, HX, HS, HY.
Qed.

Theorem rejected_child_depth_prevents_parent_assembly :
  forall tag index operation depth child rest,
  child_depth maximum operation depth (role_of tag index) = None ->
  evaluate_children tag index operation depth (child :: rest) = None.
Proof.
  intros tag index operation depth child rest H.
  cbn [evaluate_children]. now rewrite H.
Qed.

Lemma clone_children_ignore_initial_depth :
  forall children,
  Forall
    (fun child => forall first second,
       child CloneOperation first = child CloneOperation second)
    children ->
  forall tag index first second,
  evaluate_children tag index CloneOperation first children =
  evaluate_children tag index CloneOperation second children.
Proof.
  intros children H. induction H as [|child rest HC HR IH];
    intros tag index first second.
  - reflexivity.
  - cbn [evaluate_children child_depth].
    rewrite (HC first second).
    destruct (child CloneOperation second); [|reflexivity].
    now rewrite (IH tag (S index) first second).
Qed.

Theorem clone_fold_ignores_initial_depth :
  (forall input first second,
    inherited_fold input CloneOperation first =
    inherited_fold input CloneOperation second) /\
  (forall inputs,
    Forall
      (fun child => forall first second,
         child CloneOperation first = child CloneOperation second)
      (recursive_folds InheritedValue inherited_algebra inputs)).
Proof.
  apply tree_forest_ind.
  - intros tag children IH first second.
    assert (HC :
      evaluate_children tag 0 CloneOperation first
        (recursive_folds InheritedValue inherited_algebra children) =
      evaluate_children tag 0 CloneOperation second
        (recursive_folds InheritedValue inherited_algebra children)).
    { apply clone_children_ignore_initial_depth. exact IH. }
    change
      (option_map (clone_algebra tag)
        (evaluate_children tag 0 CloneOperation first
          (recursive_folds InheritedValue inherited_algebra children)) =
       option_map (clone_algebra tag)
        (evaluate_children tag 0 CloneOperation second
          (recursive_folds InheritedValue inherited_algebra children))).
    now rewrite HC.
  - constructor.
  - intros head IHhead tail IHtail.
    cbn [recursive_folds]. constructor; assumption.
Qed.

(** Reuse the existing complete worklist run. This is not a result-slot
    readiness or defunctionalization theorem for the concrete Rust emitter. *)
Theorem inherited_worklist_root_equivalence :
  forall input,
  @steps InheritedValue inherited_algebra
    (@State InheritedValue [VisitTree input] [])
    (@State InheritedValue []
      [@TreeValue InheritedValue (inherited_fold input)]).
Proof.
  intro input. unfold inherited_fold.
  apply worklist_root_equivalence.
Qed.

Theorem inherited_worklist_observation_equivalence :
  forall input operation depth,
  exists result,
    @steps InheritedValue inherited_algebra
      (@State InheritedValue [VisitTree input] [])
      (@State InheritedValue [] [@TreeValue InheritedValue result]) /\
    result operation depth = inherited_fold input operation depth.
Proof.
  intros input operation depth.
  exists (inherited_fold input). split.
  - apply inherited_worklist_root_equivalence.
  - reflexivity.
Qed.

End Fold.

Print Assumptions ordinary_child_keeps_parent_depth.
Print Assumptions clone_ignores_binding_edges.
Print Assumptions checked_successor_is_exact.
Print Assumptions overflowing_depth_is_rejected.
Print Assumptions binding_scope_body_increments_exactly_once.
Print Assumptions node_uses_source_order_assigned_children.
Print Assumptions siblings_do_not_inherit_each_others_depth.
Print Assumptions rejected_child_depth_prevents_parent_assembly.
Print Assumptions clone_fold_ignores_initial_depth.
Print Assumptions inherited_worklist_root_equivalence.
Print Assumptions inherited_worklist_observation_equivalence.

End InheritedBindingFold.
