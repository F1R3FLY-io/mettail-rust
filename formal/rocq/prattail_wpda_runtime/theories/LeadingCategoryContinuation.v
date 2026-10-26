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
From Stdlib Require Import Bool List PeanoNat.
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

(** Source-correspondence ledger for the labelled protocol below:

    - prattail/src/wpda_transitions/prefix.rs:
      singleton_leading_category_with_floor and
      leading_category_branch_with_weight choose the empty-top replacement or
      live-top Fork Push.  The latter pushes the actual rule_at(result,rule,1,
      outer_bp) with lex_w(0,result,rule), preserving the present top.
      enter_leading_child pushes category_entry(source) with lex_one and enters
      PrefixDispatch at the checked child floor and current position.
    - macros/src/gen/runtime/wpda_codegen/prefix.rs emits both singleton and
      fork leading-category calls.  engine_impl.rs dispatches
      EnterLeadingChild.  prattail/src/wpda_owned/engine.rs and
      wpda_transitions/lexical_fork.rs use the same shared transition.
    - prattail/src/wpda_walker.rs applies ForkActionKind::Push with a weighted
      SPPF carrier, applies the later plain Push at unchanged position, and
      funnels both through try_cgll_pure_descend.  The latter records the
      edge-local caller context, the first-parent v_parent summary, and any
      create-after-pop replays.  prattail/src/gss.rs::gll_create/gll_pop are the
      edge/pop operations represented below.
    - macros/src/gen/runtime/wpda_codegen/binder.rs emits the RuleAt(1)
      continuation and its eventual rule_complete arm; the latter uses Pop
      into InfixLoop and fires the semantic action.  Completion of intervening
      positions is an explicit premise here.

    Source inspection supports this mapping, not a machine-checked Rust
    refinement.  FIRST-set membership, explicit-floor admission, child-parser
    acceptance, binder completion, SPPF joins/packing and resource success are
    separate premises.  In particular, first-parent v_parent coherence is not
    established by the current Rust insertion path. *)

(** The local stack laws above intentionally do not identify a GSS node with
    one list stack.  The following labelled protocol keeps the rule identity,
    source category, Pratt floors, selected FIRST token, semiring factors, and
    child span explicit.  The child parse and the rest of the binder rule are
    premises: neither can be inferred from the two epsilon pushes. *)
Module LabelledLeadingCategoryCall.

Inductive frame :=
| CE (category floor : nat)
| RuleAt (category rule slot floor : nat)
| Return (category rule floor : nat)
| CollectionMarker (category rule : nat)
| GroupingMarker
| MixfixMarker (category rule : nat)
| ProjectionEdge
| OtherCaller (identity : nat).

Inductive control :=
| PrefixDispatch (category floor : nat)
| EnterLeadingChild (source floor : nat)
| BinderRule (category rule : nat)
| InfixLoop (floor : nat).

Inductive label :=
| ForkPushRule
| PlainPushChild
| ChildReturn (end_pos : nat)
| ActionThenPop.

Section WeightedProtocol.
  Context {W : Type} (one : W) (times : W -> W -> W).
  Hypothesis right_unit : forall w, times w one = w.

  Record choice := {
    result_category : nat;
    rule_number : nat;
    source_category : nat;
    outer_floor : nat;
    child_floor : nat;
    lookahead : nat;
    first_set : list nat;
    floor_admitted : bool;
    rule_factor : W
  }.

  Definition dispatch_admitted (r : choice) : Prop :=
    In (lookahead r) (first_set r) /\ floor_admitted r = true.

  Record descriptor := {
    current_control : control;
    current_stack : list frame;
    token_position : nat;
    ordered_factors : list W;
    child_spans : list (nat * nat);
    actions_fired : list nat
  }.

  Definition continuation (r : choice) : frame :=
    RuleAt (result_category r) (rule_number r) 1 (outer_floor r).

  Definition initial (r : choice) (caller : frame) (tail : list frame)
      (p : nat) (factors : list W) : descriptor :=
    {| current_control := PrefixDispatch (result_category r) (outer_floor r);
       current_stack := caller :: tail; token_position := p;
       ordered_factors := factors; child_spans := [];
       actions_fired := [] |}.

  Definition after_rule_push (r : choice) (caller : frame) (tail : list frame)
      (p : nat) (factors : list W) : descriptor :=
    {| current_control := EnterLeadingChild (source_category r) (child_floor r);
       current_stack := continuation r :: caller :: tail;
       token_position := p; ordered_factors := factors ++ [rule_factor r];
       child_spans := []; actions_fired := [] |}.

  Definition after_child_push (r : choice) (caller : frame) (tail : list frame)
      (p : nat) (factors : list W) : descriptor :=
    {| current_control := PrefixDispatch (source_category r) (child_floor r);
       current_stack := CE (source_category r) (child_floor r) ::
                        continuation r :: caller :: tail;
       token_position := p; ordered_factors := factors ++ [rule_factor r; one];
       child_spans := []; actions_fired := [] |}.

  Definition after_child_return (r : choice) (caller : frame)
      (tail : list frame) (p q : nat) (factors : list W) : descriptor :=
    {| current_control := BinderRule (result_category r) (rule_number r);
       current_stack := continuation r :: caller :: tail;
       token_position := q; ordered_factors := factors ++ [rule_factor r; one];
       child_spans := [(p, q)]; actions_fired := [] |}.

  Definition after_rule_return (r : choice) (caller : frame)
      (tail : list frame) (p q : nat) (factors : list W) : descriptor :=
    {| current_control := InfixLoop (outer_floor r);
       current_stack := caller :: tail; token_position := q;
       ordered_factors := factors ++ [rule_factor r; one];
       child_spans := [(p, q)]; actions_fired := [rule_number r] |}.

  (** These two premises are supplied by the child parser and the generated
      BinderRule arms.  In particular, RuleAt(1) alone does not imply that all
      later syntax positions have completed or that the semantic action fired. *)
  Variable child_accepted : choice -> nat -> nat -> Prop.
  Variable remaining_rule_items_done : choice -> nat -> Prop.

  Inductive step (r : choice) : label -> descriptor -> descriptor -> Prop :=
  | StepForkPush : forall caller tail p factors,
      dispatch_admitted r ->
      step r ForkPushRule (initial r caller tail p factors)
        (after_rule_push r caller tail p factors)
  | StepPlainPush : forall caller tail p factors,
      step r PlainPushChild (after_rule_push r caller tail p factors)
        (after_child_push r caller tail p factors)
  | StepChildReturn : forall caller tail p q factors,
      child_accepted r p q -> p <= q ->
      step r (ChildReturn q) (after_child_push r caller tail p factors)
        (after_child_return r caller tail p q factors)
  | StepActionPop : forall caller tail p q factors,
      remaining_rule_items_done r q ->
      step r ActionThenPop (after_child_return r caller tail p q factors)
        (after_rule_return r caller tail p q factors).

  Theorem labelled_live_call_and_return : forall r caller tail p q factors,
    dispatch_admitted r -> child_accepted r p q -> p <= q ->
    remaining_rule_items_done r q ->
    step r ForkPushRule (initial r caller tail p factors)
      (after_rule_push r caller tail p factors) /\
    step r PlainPushChild (after_rule_push r caller tail p factors)
      (after_child_push r caller tail p factors) /\
    step r (ChildReturn q) (after_child_push r caller tail p factors)
      (after_child_return r caller tail p q factors) /\
    step r ActionThenPop (after_child_return r caller tail p q factors)
      (after_rule_return r caller tail p q factors).
  Proof.
    intros r caller tail p q factors Hadmit Hchild Hspan Hdone.
    repeat split.
    - apply StepForkPush. exact Hadmit.
    - apply StepPlainPush.
    - apply StepChildReturn; assumption.
    - apply StepActionPop. exact Hdone.
  Qed.

  Theorem call_preserves_caller_position_and_admission : forall r caller tail p factors,
    current_stack (after_child_push r caller tail p factors) =
      CE (source_category r) (child_floor r) ::
      RuleAt (result_category r) (rule_number r) 1 (outer_floor r) ::
      caller :: tail /\
    token_position (after_child_push r caller tail p factors) = p /\
    current_control (after_child_push r caller tail p factors) =
      PrefixDispatch (source_category r) (child_floor r) /\
    ordered_factors (after_child_push r caller tail p factors) =
      factors ++ [rule_factor r; one].
  Proof. intros; repeat split; reflexivity. Qed.

  Theorem returned_child_has_exactly_one_span : forall r caller tail p q factors,
    child_spans (after_child_return r caller tail p q factors) = [(p, q)] /\
    length (child_spans (after_child_return r caller tail p q factors)) = 1 /\
    current_stack (after_child_return r caller tail p q factors) =
      continuation r :: caller :: tail.
  Proof. intros; repeat split; reflexivity. Qed.

  Theorem action_precedes_restored_caller : forall r caller tail p q factors,
    actions_fired (after_rule_return r caller tail p q factors) =
      [rule_number r] /\
    current_stack (after_rule_return r caller tail p q factors) = caller :: tail /\
    current_control (after_rule_return r caller tail p q factors) =
      InfixLoop (outer_floor r).
  Proof. intros; repeat split; reflexivity. Qed.

  Theorem factor_is_applied_once_in_order : forall r factors,
    fold_left times (ordered_factors (after_child_push r (OtherCaller 0) [] 0 factors)) one =
    times (fold_left times factors one) (rule_factor r).
  Proof.
    intros r factors. simpl. rewrite fold_left_app. simpl.
    rewrite right_unit. reflexivity.
  Qed.

  (** The only direct replacement path in current source has no top frame.
      Old and new empty-root actions have the same observable descriptor. *)
  Definition empty_root_fast (r : choice) (p : nat) (factors : list W) : descriptor :=
    {| current_control := PrefixDispatch (source_category r) (child_floor r);
       current_stack := CE (source_category r) (child_floor r) :: continuation r :: [];
       token_position := p; ordered_factors := factors ++ [rule_factor r];
       child_spans := []; actions_fired := [] |}.

  Definition empty_root_original (r : choice) (p : nat) (factors : list W)
      : descriptor :=
    {| current_control := PrefixDispatch (source_category r) (child_floor r);
       current_stack := CE (source_category r) (child_floor r) ::
                        RuleAt (result_category r) (rule_number r) 1 (outer_floor r) :: [];
       token_position := p; ordered_factors := factors ++ [rule_factor r];
       child_spans := []; actions_fired := [] |}.

  Theorem empty_root_fast_path_observational_equivalence : forall r p factors,
    empty_root_original r p factors = empty_root_fast r p factors.
  Proof. reflexivity. Qed.

  (** The historical replace-and-push was *not* equivalent for CE or Return.
      This finite Return witness loses the enclosing rule's continuation. *)
  Definition old_replace_top (r : choice) (stack : list frame) : list frame :=
    match stack with
    | [] => []
    | _ :: tail => CE (source_category r) (child_floor r) :: continuation r :: tail
    end.

  Theorem old_return_overwrite_counterexample : forall r,
    old_replace_top r [Return 7 3 0] =
      [CE (source_category r) (child_floor r); continuation r] /\
    ~ In (Return 7 3 0) (old_replace_top r [Return 7 3 0]).
  Proof.
    intro r. split; [reflexivity |].
    unfold old_replace_top, continuation. simpl.
    intros [H | [H | []]]; discriminate.
  Qed.

  Theorem old_category_entry_overwrite_counterexample : forall r c bp,
    ~ In (CE c bp) (old_replace_top r [CE c bp]) ->
    current_stack (after_rule_return r (CE c bp) [] 0 0 []) = [CE c bp] /\
    old_replace_top r [CE c bp] <> [CE c bp].
  Proof.
    intros r c bp Hlost. split; [reflexivity |].
    intro Heq. apply Hlost. rewrite Heq. simpl. left. reflexivity.
  Qed.

End WeightedProtocol.

(** GSS returns are indexed by an edge, not by a selected list-stack parent.
    A fresh edge is identified by its caller node and operand forest node;
    for each previously recorded pop, creation replays exactly one return for
    that edge.  A duplicate edge emits none, as in gss::gll_create. *)
Record edge := {
  edge_caller : nat;
  edge_operand : nat;
  edge_frames : list frame
}.

Record pop := {
  pop_end : nat;
  pop_result : nat;
  pop_rule : nat
}.

Record returned := {
  returned_caller : nat;
  returned_operand : nat;
  returned_end : nat;
  returned_result : nat;
  returned_rule : nat;
  returned_frames : list frame
}.

Definition return_for (e : edge) (p : pop) : returned :=
  {| returned_caller := edge_caller e;
     returned_operand := edge_operand e;
     returned_end := pop_end p;
     returned_result := pop_result p;
     returned_rule := pop_rule p;
     returned_frames := edge_frames e |}.

Definition replay_for_edge (pops : list pop) (e : edge) : list returned :=
  map (return_for e) pops.

Definition pop_to_all_callers (edges : list edge) (p : pop) : list returned :=
  map (fun e => return_for e p) edges.

Definition prior_pops_to_all_callers (edges : list edge) (pops : list pop)
  : list returned :=
  concat (map (replay_for_edge pops) edges).

Theorem pop_returns_to_every_caller : forall earlier later p,
  pop_to_all_callers (earlier ++ later) p =
    pop_to_all_callers earlier p ++ pop_to_all_callers later p.
Proof. intros; unfold pop_to_all_callers; apply map_app. Qed.

Theorem create_after_pop_replays_each_prior_pop : forall edges pops new_edge,
  prior_pops_to_all_callers (edges ++ [new_edge]) pops =
    prior_pops_to_all_callers edges pops ++ replay_for_edge pops new_edge.
Proof.
  intros. unfold prior_pops_to_all_callers.
  rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem replay_keeps_new_edge_identity : forall pops e returned_value,
  In returned_value (replay_for_edge pops e) ->
  returned_caller returned_value = edge_caller e /\
  returned_operand returned_value = edge_operand e /\
  returned_frames returned_value = edge_frames e.
Proof.
  intros pops e returned_value Hin.
  unfold replay_for_edge in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [p [Heq _]]. subst returned_value.
  repeat split; reflexivity.
Qed.

Definition edge_key (e : edge) : nat * nat :=
  (edge_caller e, edge_operand e).

Definition edge_already_present (edges : list edge) (e : edge) : bool :=
  existsb (fun prior =>
    Nat.eqb (edge_caller prior) (edge_caller e) &&
    Nat.eqb (edge_operand prior) (edge_operand e)) edges.

Definition create_edge (edges : list edge) (pops : list pop) (e : edge)
  : list edge * list returned :=
  if edge_already_present edges e
  then (edges, [])
  else (edges ++ [e], replay_for_edge pops e).

Theorem duplicate_edge_has_no_replay : forall edges pops e,
  edge_already_present edges e = true ->
  create_edge edges pops e = (edges, []).
Proof. intros; unfold create_edge; rewrite H; reflexivity. Qed.

Theorem fresh_edge_replays_all_prior_pops : forall edges pops e,
  edge_already_present edges e = false ->
  create_edge edges pops e = (edges ++ [e], replay_for_edge pops e).
Proof. intros; unfold create_edge; rewrite H; reflexivity. Qed.

(** The summaries used at a rule's child are projections of the caller chain.
    A positive RuleAt is the immediate receiver and rule acceptor.  It blocks
    direct collection separators, while the enclosing collection and any
    projection edge remain inherited from below it. *)
Inductive acceptor_key :=
| RuleAcceptor (category rule : nat)
| CollectionAcceptor (category rule : nat).

Fixpoint receiver_summary (stack : list frame) : option (nat * nat * nat) :=
  match stack with
  | RuleAt c r (S slot) _ :: _ => Some (c, r, S slot)
  | RuleAt _ _ 0 _ :: _
  | CollectionMarker _ _ :: _
  | GroupingMarker :: _
  | MixfixMarker _ _ :: _ => None
  | [] => None
  | _ :: tail => receiver_summary tail
  end.

Fixpoint acceptor_summary (stack : list frame) : option acceptor_key :=
  match stack with
  | RuleAt c r _ _ :: _ | MixfixMarker c r :: _ => Some (RuleAcceptor c r)
  | CollectionMarker c r :: _ => Some (CollectionAcceptor c r)
  | [] => None
  | _ :: tail => acceptor_summary tail
  end.

Fixpoint enclosing_collection_summary (stack : list frame) : option (nat * nat) :=
  match stack with
  | CollectionMarker c r :: _ => Some (c, r)
  | [] => None
  | _ :: tail => enclosing_collection_summary tail
  end.

Fixpoint direct_separator_summary (stack : list frame) : option (nat * nat) :=
  match stack with
  | CollectionMarker c r :: _ => Some (c, r)
  | RuleAt _ _ _ _ :: _ | GroupingMarker :: _ | MixfixMarker _ _ :: _ => None
  | [] => None
  | _ :: tail => direct_separator_summary tail
  end.

Fixpoint projection_summary (stack : list frame) : bool :=
  match stack with
  | ProjectionEdge :: _ => true
  | [] => false
  | _ :: tail => projection_summary tail
  end.

Record caller_summary := {
  summary_receiver : option (nat * nat * nat);
  summary_acceptor : option acceptor_key;
  summary_collection : option (nat * nat);
  summary_direct_separator : option (nat * nat);
  summary_projection : bool
}.

Definition summarize_caller (stack : list frame) : caller_summary :=
  {| summary_receiver := receiver_summary stack;
     summary_acceptor := acceptor_summary stack;
     summary_collection := enclosing_collection_summary stack;
     summary_direct_separator := direct_separator_summary stack;
     summary_projection := projection_summary stack |}.

Theorem rule_one_summary_is_local_and_inherits_boundaries :
  forall c r bp caller tail,
    receiver_summary (CE c bp :: RuleAt c r 1 bp :: caller :: tail) =
      Some (c, r, 1) /\
    acceptor_summary (CE c bp :: RuleAt c r 1 bp :: caller :: tail) =
      Some (RuleAcceptor c r) /\
    direct_separator_summary (CE c bp :: RuleAt c r 1 bp :: caller :: tail) = None /\
    enclosing_collection_summary (CE c bp :: RuleAt c r 1 bp :: caller :: tail) =
      enclosing_collection_summary (caller :: tail) /\
    projection_summary (CE c bp :: RuleAt c r 1 bp :: caller :: tail) =
      projection_summary (caller :: tail).
Proof. intros; repeat split; reflexivity. Qed.

(** First-parent v_parent summaries are a distinct obligation.  The source
    stores the first summary at a hash-consed return node, while edge_ctx and
    GSS returns remain per edge.  This predicate is the missing premise for
    using that first summary as though it described every caller.  The Rust
    code counts divergent insertions; it does not establish this predicate. *)
Definition first_parent_summary_coherent {S : Type}
    (summarize : list frame -> S) (first : edge) (others : list edge) : Prop :=
  Forall (fun e => summarize (edge_frames e) = summarize (edge_frames first)) others.

Theorem first_parent_summary_needs_coherence : forall (S : Type)
    (summarize : list frame -> S) first others e,
  first_parent_summary_coherent summarize first others ->
  In e others ->
  summarize (edge_frames e) = summarize (edge_frames first).
Proof.
  intros S summarize first others e Hcoherent Hin.
  unfold first_parent_summary_coherent in Hcoherent.
  induction Hcoherent as [| current rest Hcurrent Hrest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst current. exact Hcurrent.
    + apply IH. exact Hin.
Qed.

Theorem divergent_first_parent_summary_counterexample :
  summarize_caller [RuleAt 1 2 1 0] <>
  summarize_caller [CollectionMarker 3 4].
Proof.
  intro Heq. apply (f_equal summary_collection) in Heq.
  simpl in Heq. discriminate.
Qed.

Print Assumptions labelled_live_call_and_return.
Print Assumptions factor_is_applied_once_in_order.
Print Assumptions empty_root_fast_path_observational_equivalence.
Print Assumptions old_return_overwrite_counterexample.
Print Assumptions create_after_pop_replays_each_prior_pop.
Print Assumptions rule_one_summary_is_local_and_inherits_boundaries.
Print Assumptions first_parent_summary_needs_coherence.
Print Assumptions divergent_first_parent_summary_counterexample.
End LabelledLeadingCategoryCall.


Module LeadingOperandGoal.

Record entry := {
  entry_source : nat;
  entry_goal : option nat
}.

Definition unrestricted_entry source :=
  {| entry_source := source; entry_goal := None |}.

Definition strict_entry source :=
  {| entry_source := source; entry_goal := Some source |}.

Definition admits (reachable : nat -> nat -> bool) (child : entry) result :=
  match entry_goal child with
  | None => true
  | Some goal => reachable result goal
  end.

Definition enter_strict {Control : Type} source (control : Control) :=
  (strict_entry source, control).

Theorem leading_entry_preserves_source : forall source,
  entry_source (strict_entry source) = entry_source (unrestricted_entry source).
Proof. reflexivity. Qed.

Theorem leading_entry_requires_its_declared_category : forall source,
  entry_goal (strict_entry source) = Some source.
Proof. reflexivity. Qed.

Theorem leading_entry_preserves_control : forall (Control : Type) source (control : Control),
  snd (enter_strict source control) = control.
Proof. reflexivity. Qed.

Theorem leading_goal_admission_is_exact : forall reachable source result,
  admits reachable (strict_entry source) result = reachable result source.
Proof. reflexivity. Qed.

Theorem leading_goal_refuses_unreachable_results : forall reachable source result,
  reachable result source = false ->
  admits reachable (strict_entry source) result = false.
Proof. intros; exact H. Qed.

Theorem leading_goal_retains_reachable_results : forall reachable source result,
  reachable result source = true ->
  admits reachable (strict_entry source) result = true.
Proof. intros; exact H. Qed.

Theorem unrestricted_entry_admission_is_unchanged : forall reachable source result,
  admits reachable (unrestricted_entry source) result = true.
Proof. reflexivity. Qed.

Example unrestricted_child_can_leave_its_declared_category :
  admits Nat.eqb (unrestricted_entry 1) 0 = true /\
  admits Nat.eqb (strict_entry 1) 0 = false.
Proof. split; reflexivity. Qed.

Print Assumptions leading_entry_preserves_source.
Print Assumptions leading_entry_requires_its_declared_category.
Print Assumptions leading_entry_preserves_control.
Print Assumptions leading_goal_admission_is_exact.
Print Assumptions leading_goal_refuses_unreachable_results.
Print Assumptions leading_goal_retains_reachable_results.
Print Assumptions unrestricted_entry_admission_is_unchanged.
Print Assumptions unrestricted_child_can_leave_its_declared_category.

End LeadingOperandGoal.
