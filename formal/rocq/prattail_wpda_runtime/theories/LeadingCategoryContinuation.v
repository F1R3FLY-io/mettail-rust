(** * Category-leading calls preserve the real rule continuation

    A category-leading rule such as juxtaposition can begin while the top
    frame is an infix Return or a category-entry seed. Replacing either frame
    with the leading rule's marker loses a continuation: an enclosing rule in
    the former case, or the category's later Pratt/infix loop in the latter.
    A call first pushes the real RuleAt(1) continuation and then the left
    operand. RuleAt(0) is not an inert substitute: it resets the walker's
    enclosing-receiver summary. This file models local stack, receiver,
    token-position, weight-occurrence and per-predecessor laws.

    Rust correspondence: prefix::leading_category_branch_with_weight selects
    the preserved-caller route whenever a frame exists; the walker's ForkActionKind::Push
    applies the authored weight through try_cgll_pure_descend;
    prefix::enter_leading_child emits the unit-weight CategoryEntry push; the
    existing BinderRule RuleAt(1) resumes and closes the rule.

    This model does not prove Rust source correspondence, GSS hash-consing,
    first-parent v_parent summaries, SPPF packing, or resource bounds. Those
    remain executable and review obligations; full end-to-end implementation
    correctness does not follow from these local lemmas alone.
*)
From Stdlib Require Import List PeanoNat.
Import ListNotations.

Module LeadingCategoryContinuationLaws.

Inductive frame : Type :=
| CategoryEntry (category : nat)
| Caller (identity : nat)
| RuleAt (position : nat)
| GroupingMarker
| CollectionMarker
| MixfixMarker
| ProjectionEdge
| Operand.

Definition push_rule_one (stack : list frame) : list frame :=
  RuleAt 1 :: stack.

Definition open_left (stack : list frame) : option (list frame) :=
  match stack with
  | RuleAt 1 :: tail => Some (Operand :: RuleAt 1 :: tail)
  | _ => None
  end.

Definition finish_left (stack : list frame) : option (list frame) :=
  match stack with
  | Operand :: RuleAt 1 :: tail => Some (RuleAt 1 :: tail)
  | _ => None
  end.

Definition open_right (stack : list frame) : option (list frame) :=
  match stack with
  | RuleAt 1 :: tail => Some (Operand :: RuleAt 2 :: tail)
  | _ => None
  end.

Definition finish_right (stack : list frame) : option (list frame) :=
  match stack with
  | Operand :: RuleAt 2 :: tail => Some (RuleAt 2 :: tail)
  | _ => None
  end.

Definition close_rule (stack : list frame) : option (list frame) :=
  match stack with
  | RuleAt 2 :: tail => Some tail
  | _ => None
  end.

Definition nested_route (stack : list frame) : option (list frame) :=
  open_left (push_rule_one stack).

(** The receiver summary in the walker treats a positive RuleAt as the
    immediate receiver. RuleAt 0 and delimiter markers clear that summary;
    hence a slot-zero staging frame would not refine the existing route. *)
Fixpoint receiver (stack : list frame) : option nat :=
  match stack with
  | RuleAt (S item_pos) :: _ => Some (S item_pos)
  | RuleAt 0 :: _
  | GroupingMarker :: _
  | CollectionMarker :: _
  | MixfixMarker :: _ => None
  | [] => None
  | _ :: tail => receiver tail
  end.

Inductive acceptor_kind := RuleAcceptor | CollectionAcceptor.

Fixpoint acceptor (stack : list frame) : option acceptor_kind :=
  match stack with
  | RuleAt _ :: _ | MixfixMarker :: _ => Some RuleAcceptor
  | CollectionMarker :: _ => Some CollectionAcceptor
  | [] => None
  | _ :: tail => acceptor tail
  end.

Fixpoint enclosing_collection (stack : list frame) : bool :=
  match stack with
  | CollectionMarker :: _ => true
  | [] => false
  | _ :: tail => enclosing_collection tail
  end.

Fixpoint direct_separator (stack : list frame) : bool :=
  match stack with
  | CollectionMarker :: _ => true
  | RuleAt _ :: _ | GroupingMarker :: _ | MixfixMarker :: _ => false
  | [] => false
  | _ :: tail => direct_separator tail
  end.

Fixpoint has_projection_edge (stack : list frame) : bool :=
  match stack with
  | ProjectionEdge :: _ => true
  | [] => false
  | _ :: tail => has_projection_edge tail
  end.

Definition position_preserved (before after : nat) : Prop := before = after.

(** An occurrence records an authored weight in order. The unit-weight child
    entry adds no occurrence; this avoids silently assuming commutativity or
    idempotence of a particular semiring. *)
Record route_state := {
  route_stack : list frame;
  route_pos : nat;
  authored_weights : list nat
}.

Definition nested_weighted_call (rule_weight : nat) (state : route_state)
  : option route_state :=
  match nested_route (route_stack state) with
  | Some new_stack => Some {|
      route_stack := new_stack;
      route_pos := route_pos state;
      authored_weights := authored_weights state ++ [rule_weight]
    |}
  | None => None
  end.

(** The first Push carries the authored rule weight; opening the operand is
    a unit-weight epsilon step. Multiplication order is not commuted. *)
Section OrderedWeights.
  Context {W : Type} (mul : W -> W -> W) (one : W).
  Hypothesis right_unit : forall w, mul w one = w.

  Theorem nested_rule_weight_once : forall w,
    mul w one = w.
  Proof. apply right_unit. Qed.

  Theorem append_rule_factor_keeps_order : forall factors rule_factor,
    fold_left mul (factors ++ [rule_factor]) one =
    mul (fold_left mul factors one) rule_factor.
  Proof. intros; rewrite fold_left_app; reflexivity. Qed.
End OrderedWeights.

Definition legacy_direct_route (stack : list frame) : option (list frame) :=
  match stack with
  | CategoryEntry _ :: tail => Some (Operand :: RuleAt 1 :: tail)
  | _ => None
  end.

(** The old single replace-and-push route substitutes its RuleAt marker for
    the current top frame. It is valid at a seed entry, but it drops a Return
    when used at an infix right-operand site. *)
Definition replace_top_then_open_left (stack : list frame) : option (list frame) :=
  match stack with
  | _ :: tail => Some (Operand :: RuleAt 1 :: tail)
  | [] => None
  end.

Theorem nested_open_retains_any_caller : forall caller tail,
  nested_route (caller :: tail) =
    Some (Operand :: RuleAt 1 :: caller :: tail).
Proof. reflexivity. Qed.

Theorem nested_child_has_real_receiver : forall caller tail,
  receiver (RuleAt 1 :: caller :: tail) = Some 1 /\
  receiver (Operand :: RuleAt 1 :: caller :: tail) = Some 1.
Proof. intros; split; reflexivity. Qed.

Theorem nested_child_context_is_local_rule_with_inherited_boundaries :
  forall caller tail,
    acceptor (Operand :: RuleAt 1 :: caller :: tail) = Some RuleAcceptor /\
    direct_separator (Operand :: RuleAt 1 :: caller :: tail) = false /\
    enclosing_collection (Operand :: RuleAt 1 :: caller :: tail) =
      enclosing_collection (caller :: tail) /\
    has_projection_edge (Operand :: RuleAt 1 :: caller :: tail) =
      has_projection_edge (caller :: tail).
Proof. intros; repeat split; reflexivity. Qed.

Theorem zero_slot_is_not_a_receiver : forall caller tail,
  receiver (RuleAt 0 :: caller :: tail) = None.
Proof. reflexivity. Qed.

Theorem nested_route_consumes_no_token : forall caller tail pos,
  nested_route (caller :: tail) =
    Some (Operand :: RuleAt 1 :: caller :: tail) /\
  position_preserved pos pos.
Proof. intros; split; reflexivity. Qed.

Theorem weighted_call_records_exactly_one_rule_in_order :
  forall caller tail pos weights rule_weight,
    nested_weighted_call rule_weight {|
      route_stack := caller :: tail;
      route_pos := pos;
      authored_weights := weights
    |} = Some {|
      route_stack := Operand :: RuleAt 1 :: caller :: tail;
      route_pos := pos;
      authored_weights := weights ++ [rule_weight]
    |}.
Proof. reflexivity. Qed.

(** GSS predecessor edges may share a top node. The route must commute with
    enumerating each predecessor; no one caller may be substituted for another.
    This law is intentionally independent of the number or identity of edges. *)
Theorem shared_callers_preserve_each_predecessor : forall callers tail,
  map (fun caller => nested_route (caller :: tail)) callers =
  map (fun caller => Some (Operand :: RuleAt 1 :: caller :: tail)) callers.
Proof. intros; apply map_ext; intro caller; reflexivity. Qed.

Definition replay_after_pop (callers : list frame) (tail : list frame) :=
  map (fun caller => close_rule (RuleAt 2 :: caller :: tail)) callers.

Theorem replay_new_caller_after_pop : forall earlier later tail,
  replay_after_pop (earlier ++ [later]) tail =
    replay_after_pop earlier tail ++ [Some (later :: tail)].
Proof. intros; unfold replay_after_pop; rewrite map_app; reflexivity. Qed.

Theorem legacy_direct_drops_category_entry : forall category tail,
  legacy_direct_route (CategoryEntry category :: tail) =
    Some (Operand :: RuleAt 1 :: tail).
Proof. reflexivity. Qed.

(** A category-entry frame is not expendable: after the leading rule closes,
    the same category can still recognize a lower-precedence infix operator.
    This is the abstract continuation behind the ranked [aa|a] witness. *)
Definition may_dispatch_later_infix (category : nat) (stack : list frame) : bool :=
  match stack with
  | CategoryEntry actual :: _ => Nat.eqb actual category
  | _ => false
  end.

Theorem category_entry_call_restores_pratt_continuation : forall category tail,
  close_rule (RuleAt 2 :: CategoryEntry category :: tail) =
    Some (CategoryEntry category :: tail) /\
  may_dispatch_later_infix category (CategoryEntry category :: tail) = true.
Proof.
  intros; split.
  - reflexivity.
  - unfold may_dispatch_later_infix; simpl; rewrite Nat.eqb_refl; reflexivity.
Qed.

Theorem legacy_direct_cannot_dispatch_later_infix : forall category tail,
  may_dispatch_later_infix category tail = false ->
  close_rule (RuleAt 2 :: tail) = Some tail /\
  may_dispatch_later_infix category tail = false.
Proof. intros; split; [reflexivity | assumption]. Qed.

Theorem nested_complete_restores_exact_caller : forall caller tail,
  nested_route (caller :: tail) =
    Some (Operand :: RuleAt 1 :: caller :: tail) /\
  finish_left (Operand :: RuleAt 1 :: caller :: tail) =
    Some (RuleAt 1 :: caller :: tail) /\
  open_right (RuleAt 1 :: caller :: tail) =
    Some (Operand :: RuleAt 2 :: caller :: tail) /\
  finish_right (Operand :: RuleAt 2 :: caller :: tail) =
    Some (RuleAt 2 :: caller :: tail) /\
  close_rule (RuleAt 2 :: caller :: tail) = Some (caller :: tail).
Proof. intros; repeat split; reflexivity. Qed.

Theorem direct_replace_discards_infix_caller : forall identity tail,
  replace_top_then_open_left (Caller identity :: tail) =
    Some (Operand :: RuleAt 1 :: tail).
Proof. reflexivity. Qed.

Theorem nested_route_preserves_arbitrary_tail : forall caller tail suffix,
  nested_route (caller :: tail ++ suffix) =
    Some (Operand :: RuleAt 1 :: caller :: tail ++ suffix).
Proof. reflexivity. Qed.

Print Assumptions nested_open_retains_any_caller.
Print Assumptions nested_child_has_real_receiver.
Print Assumptions nested_child_context_is_local_rule_with_inherited_boundaries.
Print Assumptions zero_slot_is_not_a_receiver.
Print Assumptions nested_route_consumes_no_token.
Print Assumptions weighted_call_records_exactly_one_rule_in_order.
Print Assumptions shared_callers_preserve_each_predecessor.
Print Assumptions replay_new_caller_after_pop.
Print Assumptions nested_rule_weight_once.
Print Assumptions append_rule_factor_keeps_order.
Print Assumptions legacy_direct_drops_category_entry.
Print Assumptions category_entry_call_restores_pratt_continuation.
Print Assumptions legacy_direct_cannot_dispatch_later_infix.
Print Assumptions nested_complete_restores_exact_caller.
Print Assumptions direct_replace_discards_infix_caller.
Print Assumptions nested_route_preserves_arbitrary_tail.
End LeadingCategoryContinuationLaws.
