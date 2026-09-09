(** Checked construction protocol over the concrete target algebra.

    This module connects operations, ordered arena references, interpretation,
    structural observations, and private append-only construction. It specifies
    results, not a new production traversal. The existing Job/Kont worklist
    remains responsible for scheduling and stack-safe runtime execution.

    Fresh/receive descriptors retain the exact admitted producer image. Full
    staged-producer correspondence and owned FLT session publication remain
    separate obligations in the same interface/worklist handoff. In
    particular, appending a private value here does not publish a process,
    discharge a guard, install a theory, or authorize any node effect. *)

From Stdlib Require Import List String Bool PeanoNat ZArith Lia Structures.OrderedTypeEx.
From RhoBridge Require Import RholangTargetConstruction.
Import ListNotations.

(** Target reference fields use nonnegative signed 32-bit integers. The Rust
    refinement must check these values before allocating a singleton free-bit vector;
    the extensional definition here does not establish strict evaluation order.
    Z is used for the bound, avoiding reduction of a billion Peano successors. *)
Definition fits_target_index (index : nat) : bool :=
  (Z.of_nat index <=? 2147483647)%Z.

Definition within_target_indices (indices : list nat) (result : ConstructionResult)
    : ConstructionResult :=
  if forallb fits_target_index indices then result
  else ConstructionRejected TargetIndexOutOfRange.

(** URI pairs arrive normalized by unbind_uri_scope. This is a linear check of
    that owner's output, NOT another URI parser or sort. Both projections use
    the same pair sequence, so sorting URIs alone cannot change binder identity.
    Source backtick-envelope checking remains the existing producer's job. *)
Inductive FreshPlan :=
| PlainFresh (ordered_binders : list nat)
| UriFresh (ordered_pairs : list (string * nat)).
Definition fresh_binders (plan : FreshPlan) : list nat :=
  match plan with PlainFresh binders => binders | UriFresh pairs => map snd pairs end.
Definition fresh_uris (plan : FreshPlan) : list string :=
  match plan with PlainFresh _ => [] | UriFresh pairs => map fst pairs end.

Fixpoint ordered_uri_tail (previous : string) (uris : list string) : bool :=
  match uris with
  | [] => true
  | uri :: rest => String.ltb previous uri && ordered_uri_tail uri rest
  end.
Definition normalized_uris (uris : list string) : bool :=
  match uris with
  | [] => false
  | first :: rest => negb (String.eqb first EmptyString) && ordered_uri_tail first rest
  end.
Definition fresh_plan_valid (plan : FreshPlan) : bool :=
  match plan with PlainFresh _ => true | UriFresh pairs => normalized_uris (map fst pairs) end.
Definition checked_fresh (plan : FreshPlan) (body : Value) : ConstructionResult :=
  if fresh_plan_valid plan then
    within_target_indices [List.length (fresh_binders plan)]
      (fresh (List.length (fresh_binders plan)) (fresh_uris plan) body)
  else ConstructionRejected InvalidBinderLayout.

(** The caller map can be empty and can contain an empty unused key. Reuse
    the strict string-order check, not normalized_uris' different domain.
    The adapter projects its existing ordered map; this does not sort again. *)
Definition ordered_injection_keys (keys : list string) : bool :=
  match keys with [] => true | first :: rest => ordered_uri_tail first rest end.
Definition checked_injected_fresh (plan : FreshPlan) (keys : list string)
    (children : list Value) : ConstructionResult :=
  match children with
  | [] => ConstructionRejected ChildArityMismatch
  | body :: injections =>
    if fresh_plan_valid plan && ordered_injection_keys keys then
      within_target_indices [List.length (fresh_binders plan)]
        (fresh_with_injections (List.length (fresh_binders plan))
          (fresh_uris plan) keys body injections)
    else ConstructionRejected InvalidBinderLayout
  end.

(** Every admitted receive bind has one outer pattern and no remainder.
    A polyadic payload is inside that pattern's list. Empty input uses a
    wildcard pattern with no captures, NOT a zero-length pattern vector.
    The pattern producer supplies its ordered telescope; this descriptor
    retains its association and does not scan/recount arbitrary pattern trees. *)
Record BindDescriptor := {
  ordered_captures : list CaptureSlot;
  bind_is_persistent : bool
}.
Definition receive_slots (descriptors : list BindDescriptor) : list CaptureSlot :=
  flat_map ordered_captures descriptors.
Definition receive_persistent (descriptors : list BindDescriptor) : bool :=
  existsb bind_is_persistent descriptors.

Fixpoint resolve_bind_roles (descriptors : list BindDescriptor) (children : list Value)
    : option (list BindValue * list Value) :=
  match descriptors with
  | [] => Some ([], children)
  | descriptor :: rest =>
    match children with
    | source :: pattern :: remaining =>
      match resolve_bind_roles rest remaining with
      | Some (binds, suffix) => Some
        ({| bind_source := source; bind_patterns := [pattern];
            bind_free_count := List.length (ordered_captures descriptor);
            bind_remainder := None |} :: binds, suffix)
      | None => None
      end
    | _ => None
    end
  end.

Definition checked_receive (descriptors : list BindDescriptor) (has_condition : bool)
    (children : list Value) : ConstructionResult :=
  match descriptors with
  | [] => ConstructionRejected InvalidBinderLayout
  | _ :: _ =>
    within_target_indices [List.length (receive_slots descriptors)]
      (match resolve_bind_roles descriptors children with
       | Some (binds, [body]) =>
         if has_condition then ConstructionRejected ChildArityMismatch
         else receive binds (receive_slots descriptors) (receive_persistent descriptors) body None
       | Some (binds, [body; condition]) =>
         if has_condition then
           receive binds (receive_slots descriptors) (receive_persistent descriptors) body (Some condition)
         else ConstructionRejected ChildArityMismatch
       | _ => ConstructionRejected ChildArityMismatch
       end)
  end.

(** Single forward decomposition with an exact final continuation slot.
    A request payload is not implicitly packed/unpacked as a Rholang list. *)
Fixpoint resolve_service_reply (payload_count : nat) (children : list Value)
    : option (list Value * Value) :=
  match payload_count, children with
  | 0, [body] => Some ([], body)
  | S remaining, payload :: rest =>
    match resolve_service_reply remaining rest with
    | Some (payloads, body) => Some (payload :: payloads, body)
    | None => None
    end
  | _, _ => None
  end.

Inductive ConstructOp :=
| EmptyOp | AppendOp
| IntegerOp (integer_value : Z) | BooleanOp (boolean_value : bool)
| TextOp (text_value : string)
| HostNameOp (slot : HostNameSlot)
| PendingPredicateOp (use_index : nat)
| BoundOp (scope index : nat) | CaptureOp (width index : nat)
| WildcardOp (connective : bool) | PatternReferenceOp (scope index depth : nat)
| UnaryOp (operator : UnaryOperator) | BinaryOp (operator : BinaryOperator)
| AdditionOp | ImplicationOp
| ListOp | MapOp | MethodOp (name : string) | SendOp (persistent : bool)
| DdlNodeOp (tag : string) | MatchOp | FalseMatchOp
| PatternUnaryOp | PatternBinaryOp (conjunction : bool) | PatternImplicationOp
| FreshOp (plan : FreshPlan) (injection_keys : list string)
| ServiceReplyOp (payload_count : nat)
| ReceiveOp (descriptors : list BindDescriptor) (has_condition : bool).

(** Maps keep an ordered pair vector. Odd input is rejected; a missing value
    is never replaced with empty, and entries are neither sorted nor deduplicated. *)
Fixpoint pair_values (values : list Value) : option (list (Value * Value)) :=
  match values with
  | [] => Some []
  | key :: value :: rest =>
    match pair_values rest with
    | Some pairs => Some ((key, value) :: pairs)
    | None => None
    end
  | [_] => None
  end.

Definition interpret (operation : ConstructOp) (children : list Value)
    : ConstructionResult :=
  match operation, children with
  | EmptyOp, [] => Constructed empty
  | AppendOp, [lhs; rhs] => Constructed (append lhs rhs)
  | IntegerOp value, [] => integer value
  | BooleanOp value, [] => Constructed (boolean value)
  | TextOp value, [] => Constructed (text value)
  | HostNameOp slot, [] => Constructed (host_name slot)
  | PendingPredicateOp use_index, selector :: fills =>
    Constructed (pending_predicate use_index selector fills)
  | BoundOp scope index, [] =>
    within_target_indices [index] (bound scope index)
  | CaptureOp width index, [] =>
    within_target_indices [width; index] (capture width index)
  | WildcardOp flag, [] => Constructed (wildcard flag)
  | PatternReferenceOp scope index depth, [] =>
    within_target_indices [index; depth] (pattern_reference scope index depth)
  | UnaryOp op, [operand] => Constructed (unary op operand)
  | BinaryOp op, operands => checked_binary op operands
  | AdditionOp, [lhs; rhs] => Constructed (addition lhs rhs)
  | ImplicationOp, [lhs; rhs] => Constructed (implication lhs rhs)
  | ListOp, elements => Constructed (list_value elements)
  | MapOp, elements =>
    match pair_values elements with
    | Some pairs => Constructed (map_value pairs)
    | None => ConstructionRejected ChildArityMismatch
    end
  | MethodOp name, receiver :: args => Constructed (method name receiver args)
  | SendOp persistent, channel :: payloads => Constructed (send persistent channel payloads)
  | DdlNodeOp tag, elements => Constructed (ddl_node tag elements)
  | MatchOp, [target; pattern] => Constructed (matches_value target pattern)
  | FalseMatchOp, [target] => Constructed (statically_false_match target)
  | PatternUnaryOp, [operand] => Constructed (pattern_node PatternNot [operand])
  | PatternBinaryOp conjunction, [lhs; rhs] => Constructed
    (pattern_node (if conjunction then PatternAnd else PatternOr) [lhs; rhs])
  | PatternImplicationOp, [lhs; rhs] => Constructed (pattern_implication lhs rhs)
  | FreshOp plan keys, operands => checked_injected_fresh plan keys operands
  | ServiceReplyOp count, channel :: rest =>
    match resolve_service_reply count rest with
    | Some (payloads, body) => Constructed (service_reply channel payloads body)
    | None => ConstructionRejected ChildArityMismatch
    end
  | ReceiveOp descriptors has_condition, operands => checked_receive descriptors has_condition operands
  | _, _ => ConstructionRejected ChildArityMismatch
  end.

(** Incremental requirements of this operation only. Its already-constructed
    children have already registered their own slots. No recursive graph scan
    is necessary when constructing a parent. Repetition is retained. *)
Definition operation_host_names (operation : ConstructOp) : list HostNameSlot :=
  match operation with HostNameOp slot => [slot] | _ => [] end.

Theorem service_reply_resolution_preserves_exact_payload_order : forall count children payloads body,
  resolve_service_reply count children = Some (payloads, body) ->
  List.length payloads = count /\ children = payloads ++ [body].
Proof.
  induction count as [|count IH]; intros children payloads body H.
  - destruct children as [|child [|extra rest]]; try discriminate.
    inversion H; subst; split; reflexivity.
  - destruct children as [|payload rest]; try discriminate.
    cbn in H. destruct (resolve_service_reply count rest) as [[values continuation]|] eqn:E;
      try discriminate. inversion H; subst.
    specialize (IH _ _ _ E) as [L C]. cbn. rewrite L, C; auto.
Qed.

Theorem service_reply_explicit_children_succeed : forall payloads body,
  resolve_service_reply (List.length payloads) (payloads ++ [body]) = Some (payloads, body).
Proof.
  induction payloads as [|payload rest IH]; intros body; cbn; [reflexivity|now rewrite IH].
Qed.

Theorem checked_service_reply_reuses_exact_shell : forall channel payloads body,
  interpret (ServiceReplyOp (List.length payloads)) (channel :: payloads ++ [body]) =
    Constructed (service_reply channel payloads body).
Proof. intros; cbn [interpret]; now rewrite service_reply_explicit_children_succeed. Qed.

Theorem service_reply_bad_arity_rejects : forall count channel children,
  List.length children <> S count ->
  interpret (ServiceReplyOp count) (channel :: children) = ConstructionRejected ChildArityMismatch.
Proof.
  intros count channel children H; cbn [interpret].
  destruct (resolve_service_reply count children) as [[payloads body]|] eqn:E; [|reflexivity].
  apply service_reply_resolution_preserves_exact_payload_order in E as [L C].
  subst children. rewrite length_app, L in H; cbn in H. exfalso; lia.
Qed.

Example installed_flt_one_payload_specialization : forall channel request body,
  interpret (ServiceReplyOp 1) [channel; request; body] =
    Constructed (service_reply channel [request] body).
Proof. reflexivity. Qed.

Example held_fold_two_payload_specialization : forall channel operand body,
  interpret (ServiceReplyOp 2) [channel; operand; service_reply_channel; body] =
    Constructed (service_reply channel [operand; service_reply_channel] body).
Proof. reflexivity. Qed.

Print Assumptions service_reply_resolution_preserves_exact_payload_order.
Print Assumptions service_reply_explicit_children_succeed.
Print Assumptions checked_service_reply_reuses_exact_shell.
Print Assumptions service_reply_bad_arity_rejects.
Print Assumptions installed_flt_one_payload_specialization.
Print Assumptions held_fold_two_payload_specialization.

(** The host-only name carrier is polymorphic so this lookup transports exact
    identity without reconstructing names from strings. The adapter admits
    only closed opaque NAME values into this table; these lookup laws do not
    prove that adapter check, capability rights, or unforgeability. The table
    is an explicit argument, never a process-global provider lookup. *)
Inductive HostNameError := HostNameOwnerMismatch | HostNameSlotMissing.
Inductive HostNameResult (Name : Type) :=
| HostNameResolved (name : Name)
| HostNameRejected (error : HostNameError).
Arguments HostNameResolved {Name} _.
Arguments HostNameRejected {Name} _.
Definition resolve_host_name {Name : Type} (owner : nat) (names : list Name)
    (slot : HostNameSlot) : HostNameResult Name :=
  if Nat.eqb owner (host_name_owner slot) then
    match nth_error names (host_name_index slot) with
    | Some name => HostNameResolved name
    | None => HostNameRejected HostNameSlotMissing
    end
  else HostNameRejected HostNameOwnerMismatch.

Theorem host_resolution_preserves_exact_identity : forall Name owner names slot (name : Name),
  resolve_host_name owner names slot = HostNameResolved name ->
  owner = host_name_owner slot /\ nth_error names (host_name_index slot) = Some name.
Proof.
  intros Name owner names slot name H; unfold resolve_host_name in H.
  destruct (Nat.eqb owner (host_name_owner slot)) eqn:E; try discriminate.
  destruct (nth_error names (host_name_index slot)) eqn:N; try discriminate.
  inversion H; subst. split; [now apply Nat.eqb_eq|reflexivity].
Qed.

Theorem host_owner_mismatch_cannot_resolve : forall Name owner (names : list Name) slot,
  owner <> host_name_owner slot ->
  resolve_host_name owner names slot = HostNameRejected HostNameOwnerMismatch.
Proof. intros; unfold resolve_host_name. apply Nat.eqb_neq in H; now rewrite H. Qed.

Theorem missing_host_slot_cannot_resolve : forall Name owner (names : list Name) index,
  nth_error names index = None ->
  resolve_host_name owner names {| host_name_owner := owner; host_name_index := index |} =
    HostNameRejected HostNameSlotMissing.
Proof. intros; unfold resolve_host_name; cbn; now rewrite Nat.eqb_refl, H. Qed.

Theorem host_name_operation_requires_no_children : forall slot first rest,
  interpret (HostNameOp slot) (first :: rest) = ConstructionRejected ChildArityMismatch.
Proof. reflexivity. Qed.

Inductive ChildrenResult :=
| ChildrenResolved (values : list Value)
| ChildrenRejected (error : ConstructionError).

(** Fail at the first missing ordered reference. The error retains its actual
    index. These reads are private: neither success nor failure mutates arena. *)
Fixpoint resolve_checked (arena : list Value) (references : list nat) : ChildrenResult :=
  match references with
  | [] => ChildrenResolved []
  | index :: rest =>
    match nth_error arena index with
    | None => ChildrenRejected (MissingReference index)
    | Some value =>
      match resolve_checked arena rest with
      | ChildrenResolved values => ChildrenResolved (value :: values)
      | ChildrenRejected error => ChildrenRejected error
      end
    end
  end.

Definition construct (arena : list Value) (operation : ConstructOp) (references : list nat)
    : ConstructionResult :=
  match resolve_checked arena references with
  | ChildrenRejected error => ConstructionRejected error
  | ChildrenResolved children => interpret operation children
  end.

Record StructuralObservation := {
  observed_single_string : bool;
  observed_summary : Summary
}.
Definition observation_of (value : Value) : StructuralObservation :=
  {| observed_single_string := single_string value;
     observed_summary := summary_of value |}.
Inductive ObservationResult :=
| Observed (observation : StructuralObservation)
| ObservationRejected (error : ConstructionError).
Definition observe (arena : list Value) (index : nat) : ObservationResult :=
  match nth_error arena index with
  | Some value => Observed (observation_of value)
  | None => ObservationRejected (MissingReference index)
  end.

(** Quote, drop and name parentheses reuse their child's constructed value.
    They do not introduce a wrapper or append a new semantic arena node. The
    existing source driver still records each source occurrence separately. *)
Inductive ForwardResult := Forwarded (reference : nat)
  | ForwardRejected (error : ConstructionError).
Definition forward_reference (arena : list Value) (reference : nat) : ForwardResult :=
  match nth_error arena reference with
  | Some _ => Forwarded reference
  | None => ForwardRejected (MissingReference reference)
  end.

Theorem quote_drop_forward_exact_reference : forall arena reference value,
  nth_error arena reference = Some value -> forward_reference arena reference = Forwarded reference.
Proof. intros; unfold forward_reference; now rewrite H. Qed.

Theorem quote_drop_forward_preserves_observation : forall arena reference forwarded,
  forward_reference arena reference = Forwarded forwarded ->
  forwarded = reference /\ observe arena forwarded = observe arena reference.
Proof.
  intros arena reference forwarded H; unfold forward_reference in H.
  destruct (nth_error arena reference); try discriminate. inversion H; subst; auto.
Qed.

Theorem quote_drop_cannot_forward_missing_value : forall arena reference,
  nth_error arena reference = None ->
  forward_reference arena reference = ForwardRejected (MissingReference reference).
Proof. intros; unfold forward_reference; now rewrite H. Qed.

(** Each step is a private transaction. A failed step returns the unchanged
    arena; successful construction appends one actual interpreted value and
    returns precisely its new reference. There is no public-root field here. *)
Inductive StepResult :=
| ValueAppended (arena : list Value) (reference : nat)
| StepRejected (arena : list Value) (error : ConstructionError).
Definition construction_step (arena : list Value) (operation : ConstructOp)
    (references : list nat) : StepResult :=
  match construct arena operation references with
  | Constructed value => ValueAppended (arena ++ [value]) (List.length arena)
  | ConstructionRejected error => StepRejected arena error
  end.

(** This image relation is generated by successful concrete steps from empty.
    It is not an assumed validity flag and admits no raw Value insertion. A
    later runtime adapter must establish this relation for its private arena. *)
Inductive GeneratedArena : list Value -> Prop :=
| GeneratedEmpty : GeneratedArena []
| GeneratedAppend : forall arena operation references value,
    GeneratedArena arena -> construct arena operation references = Constructed value ->
    GeneratedArena (arena ++ [value]).

Theorem target_index_check_exact : forall index,
  fits_target_index index = true <-> (Z.of_nat index <= 2147483647)%Z.
Proof. intros; unfold fits_target_index; apply Z.leb_le. Qed.

Theorem checked_indices_success_bounded : forall indices result value,
  within_target_indices indices result = Constructed value ->
  Forall (fun index => (Z.of_nat index <= 2147483647)%Z) indices /\
  result = Constructed value.
Proof.
  intros indices result value H; unfold within_target_indices in H.
  destruct (forallb fits_target_index indices) eqn:E; try discriminate.
  split; [|exact H]. apply Forall_forall. intros index Hin.
  apply forallb_forall with (x := index) in E; auto.
  now apply target_index_check_exact.
Qed.

Theorem pair_values_preserves_every_child : forall values pairs,
  pair_values values = Some pairs -> pair_children pairs = values.
Proof.
  fix IH 1. intros [|key [|value rest]] pairs H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (pair_values rest) eqn:E; try discriminate.
    inversion H; subst.
    change (key :: value :: pair_children l = key :: value :: rest).
    now rewrite (IH rest l E).
Qed.

Theorem checked_resolution_matches_algebra : forall arena references values,
  resolve_checked arena references = ChildrenResolved values <->
  resolve_children arena references = Some values.
Proof.
  intros arena references; induction references as [|index rest IH]; intros values.
  - cbn; split; intros H; inversion H; reflexivity.
  - cbn. destruct (nth_error arena index) eqn:E; [|split; discriminate].
    destruct (resolve_checked arena rest) as [resolved|error] eqn:R.
    + pose proof (proj1 (IH resolved) eq_refl) as C.
      rewrite C. split; intros H; inversion H; reflexivity.
    + destruct (resolve_children arena rest) as [resolved|] eqn:C.
      * pose proof (proj2 (IH resolved) eq_refl) as Impossible. discriminate.
      * split; discriminate.
Qed.

Theorem construction_uses_exact_ordered_children : forall arena operation references value,
  construct arena operation references = Constructed value ->
  exists children,
    Forall2 (fun index child => nth_error arena index = Some child) references children /\
    interpret operation children = Constructed value.
Proof.
  intros arena operation references value H; unfold construct in H.
  destruct (resolve_checked arena references) eqn:R; try discriminate.
  exists values; split; [|exact H].
  apply checked_reference_order. now apply checked_resolution_matches_algebra.
Qed.

Theorem missing_first_reference_is_exact_error : forall arena operation index rest,
  nth_error arena index = None ->
  construct arena operation (index :: rest) =
    ConstructionRejected (MissingReference index).
Proof. intros; unfold construct; cbn [resolve_checked]; now rewrite H. Qed.

Theorem repeated_children_remain_repeated : forall arena index value,
  nth_error arena index = Some value ->
  construct arena AppendOp [index; index] = Constructed (append value value).
Proof. intros; unfold construct; cbn [resolve_checked]; now rewrite H. Qed.

Theorem failed_step_leaves_arena_unchanged : forall arena operation references error,
  construct arena operation references = ConstructionRejected error ->
  construction_step arena operation references = StepRejected arena error.
Proof. intros; unfold construction_step; now rewrite H. Qed.

Theorem successful_step_appends_interpretation : forall arena operation references result index,
  construction_step arena operation references = ValueAppended result index ->
  exists value, construct arena operation references = Constructed value /\
    result = arena ++ [value] /\ index = List.length arena /\
    nth_error result index = Some value.
Proof.
  intros arena operation references result index H; unfold construction_step in H.
  destruct (construct arena operation references) eqn:C; try discriminate.
  inversion H; subst. exists value. repeat split; auto.
  rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Theorem successful_step_preserves_old_references :
  forall arena operation references result index old value,
  construction_step arena operation references = ValueAppended result index ->
  nth_error arena old = Some value -> nth_error result old = Some value.
Proof.
  intros arena operation references result index old value H Hlookup.
  apply successful_step_appends_interpretation in H as [new [C [E _]]]. subst result.
  rewrite nth_error_app1; [exact Hlookup|].
  apply nth_error_Some. rewrite Hlookup; discriminate.
Qed.

Theorem observe_returned_reference_is_actual_value :
  forall arena operation references result index,
  construction_step arena operation references = ValueAppended result index ->
  exists value, construct arena operation references = Constructed value /\
    observe result index = Observed (observation_of value).
Proof.
  intros arena operation references result index H.
  apply successful_step_appends_interpretation in H as [value [C [E [I N]]]].
  exists value; split; [exact C|]. unfold observe; now rewrite N.
Qed.

Theorem observe_missing_reference_rejects : forall arena index,
  nth_error arena index = None -> observe arena index = ObservationRejected (MissingReference index).
Proof. intros; unfold observe; now rewrite H. Qed.

Theorem checked_addition_observes_constructed_values : forall arena lhs rhs left_value right_value,
  nth_error arena lhs = Some left_value -> nth_error arena rhs = Some right_value ->
  construct arena AdditionOp [lhs; rhs] = Constructed (addition left_value right_value).
Proof. intros; unfold construct; cbn [resolve_checked]; now rewrite H, H0. Qed.

Theorem successful_step_retains_generated_image : forall arena operation references result index,
  GeneratedArena arena ->
  construction_step arena operation references = ValueAppended result index ->
  GeneratedArena result.
Proof.
  intros arena operation references result index G H.
  apply successful_step_appends_interpretation in H as [value [C [E _]]]. subst result.
  eapply GeneratedAppend; eauto.
Qed.

Theorem generated_member_has_concrete_construction : forall arena value,
  GeneratedArena arena -> In value arena ->
  exists prefix operation references,
    GeneratedArena prefix /\ construct prefix operation references = Constructed value.
Proof.
  intros arena value G; induction G as [|arena operation references new G IH C]; intros Hin.
  - inversion Hin.
  - apply in_app_or in Hin as [Hbefore|Hnew]; [now apply IH|].
    destruct Hnew as [E|Hfalse]; [subst new|contradiction].
    exists arena, operation, references; auto.
Qed.

Example append_then_observe_text :
  construction_step [empty; text "a"] AppendOp [0; 1] =
    ValueAppended [empty; text "a"; text "a"] 2 /\
  observe [empty; text "a"; text "a"] 2 = Observed (observation_of (text "a")).
Proof. split; reflexivity. Qed.

Example invalid_arity_does_not_append :
  construction_step [text "a"] AdditionOp [0] =
    StepRejected [text "a"] ChildArityMismatch.
Proof. reflexivity. Qed.

Example missing_operand_never_becomes_empty :
  construction_step [text "a"] AdditionOp [0; 1] =
    StepRejected [text "a"] (MissingReference 1).
Proof. reflexivity. Qed.

Example map_missing_value_rejected :
  construct [text "key"] MapOp [0] = ConstructionRejected ChildArityMismatch.
Proof. reflexivity. Qed.

Lemma string_ltb_has_closed_order : forall first second,
  String.ltb first second = true -> String_as_OT.lt first second.
Proof.
  intros first second H; unfold String.ltb in H.
  apply String_as_OT.cmp_lt.
  unfold String_as_OT.cmp.
  destruct (String.compare first second); try discriminate; reflexivity.
Qed.

Lemma ordered_uri_tail_all_larger : forall uris previous,
  ordered_uri_tail previous uris = true -> Forall (String_as_OT.lt previous) uris.
Proof.
  induction uris as [|uri rest IH]; intros previous H; [constructor|].
  cbn in H. apply andb_true_iff in H as [Hnext Hrest].
  apply string_ltb_has_closed_order in Hnext.
  constructor; [exact Hnext|]. specialize (IH uri Hrest).
  apply Forall_forall; intros later Hin.
  apply Forall_forall with (x := later) in IH; auto.
  eapply String_as_OT.lt_trans; eauto.
Qed.

Theorem ordered_uri_check_excludes_duplicates : forall uris previous,
  ordered_uri_tail previous uris = true -> NoDup (previous :: uris).
Proof.
  induction uris as [|uri rest IH]; intros previous H.
  - constructor; [intro Hfalse; inversion Hfalse|constructor].
  - pose proof (ordered_uri_tail_all_larger (uri :: rest) previous H) as Hall.
    cbn in H. apply andb_true_iff in H as [Hnext Hrest].
    constructor; [|now apply IH]. intros Hin.
    apply Forall_forall with (x := previous) in Hall; auto.
    exact (String_as_OT.lt_not_eq previous previous Hall eq_refl).
Qed.

Theorem normalized_uri_check_retains_nonempty_unique_sequence : forall uris,
  normalized_uris uris = true ->
  uris <> [] /\ NoDup uris /\ Forall (fun uri => uri <> EmptyString) uris.
Proof.
  intros [|first rest] H; [discriminate|].
  unfold normalized_uris in H. apply andb_true_iff in H as [Hfirst Hrest].
  apply negb_true_iff in Hfirst. apply String.eqb_neq in Hfirst.
  split; [discriminate|]. split; [now apply ordered_uri_check_excludes_duplicates|].
  constructor; [exact Hfirst|].
  pose proof (ordered_uri_tail_all_larger rest first Hrest) as Hall.
  apply Forall_forall. intros uri Hin E; subst uri.
  apply Forall_forall with (x := EmptyString) in Hall; auto. inversion Hall.
Qed.

Theorem injection_key_check_excludes_duplicates : forall keys,
  ordered_injection_keys keys = true -> NoDup keys.
Proof.
  intros [|first rest] H; [constructor|].
  now apply ordered_uri_check_excludes_duplicates.
Qed.

Theorem empty_injection_operation_reuses_fresh : forall plan body,
  interpret (FreshOp plan []) [body] = checked_fresh plan body.
Proof.
  intros. cbn [interpret checked_injected_fresh ordered_injection_keys].
  rewrite andb_true_r. unfold checked_fresh.
  now rewrite empty_injections_specialize_fresh.
Qed.

Theorem injected_fresh_success_has_exact_layout : forall plan keys body injections value,
  interpret (FreshOp plan keys) (body :: injections) = Constructed value ->
  fresh_plan_valid plan = true /\ ordered_injection_keys keys = true /\
  (Z.of_nat (List.length (fresh_binders plan)) <= 2147483647)%Z /\
  List.length keys = List.length injections /\
  heads_of value = [MakeHead
    (NewHead (List.length (fresh_binders plan)) (fresh_uris plan) keys) (body :: injections)] /\
  summary_of value = shifted_summary (List.length (fresh_binders plan)) (summary_of body).
Proof.
  intros plan keys body injections value H.
  cbn [interpret checked_injected_fresh] in H.
  destruct (fresh_plan_valid plan && ordered_injection_keys keys) eqn:E; try discriminate.
  apply andb_true_iff in E as [P K].
  apply checked_indices_success_bounded in H as [B F]. inversion B; subst.
  apply injected_fresh_preserves_all_entries in F as [L [U [C S]]].
  repeat split; auto.
Qed.

Example unused_empty_injection_key_is_retained :
  interpret (FreshOp (PlainFresh []) [EmptyString]) [empty; text "value"] =
    Constructed (singleton (NewHead 0 [] [EmptyString]) [empty; text "value"] closed_summary).
Proof. reflexivity. Qed.

Example duplicate_injection_keys_reject :
  interpret (FreshOp (PlainFresh []) ["key"%string; "key"%string]) [empty; text "a"; text "b"] =
    ConstructionRejected InvalidBinderLayout.
Proof. reflexivity. Qed.

Example missing_injection_value_rejects :
  interpret (FreshOp (PlainFresh []) ["key"%string]) [empty] =
    ConstructionRejected ChildArityMismatch.
Proof. reflexivity. Qed.

Example repeated_injection_values_remain_associated : forall body value,
  interpret (FreshOp (PlainFresh []) ["a"%string; "b"%string]) [body; value; value] =
    Constructed (singleton (NewHead 0 [] ["a"%string; "b"%string]) [body; value; value]
      (shifted_summary 0 (summary_of body))).
Proof. reflexivity. Qed.

Theorem fresh_uri_and_binder_projection_remain_associated : forall pairs,
  combine (fresh_uris (UriFresh pairs)) (fresh_binders (UriFresh pairs)) = pairs.
Proof. induction pairs as [|[uri binder] rest IH]; cbn in *; [reflexivity|now rewrite IH]. Qed.

Theorem checked_fresh_success_has_exact_layout : forall plan body value,
  checked_fresh plan body = Constructed value ->
  fresh_plan_valid plan = true /\
  (Z.of_nat (List.length (fresh_binders plan)) <= 2147483647)%Z /\
  heads_of value = [MakeHead (NewHead (List.length (fresh_binders plan)) (fresh_uris plan) []) [body]] /\
  summary_of value = shifted_summary (List.length (fresh_binders plan)) (summary_of body).
Proof.
  intros plan body value H; unfold checked_fresh in H.
  destruct (fresh_plan_valid plan) eqn:E; try discriminate.
  apply checked_indices_success_bounded in H as [Hbounds Hfresh].
  inversion Hbounds; subst.
  apply fresh_success_retains_body_and_local_layout in Hfresh as [Hcount [Hheads Hsummary]].
  repeat split; auto.
Qed.

Definition descriptor_shape (descriptor : BindDescriptor) : BindShape :=
  {| pattern_count := 1; free_count := List.length (ordered_captures descriptor);
     remainder_index := None |}.

Theorem receive_role_resolution_preserves_layout : forall descriptors children binds suffix,
  resolve_bind_roles descriptors children = Some (binds, suffix) ->
  map bind_shape binds = map descriptor_shape descriptors /\
  bind_width binds = List.length (receive_slots descriptors) /\
  children = flat_map bind_children binds ++ suffix.
Proof.
  induction descriptors as [|descriptor rest IH]; intros children binds suffix H.
  - cbn in H. inversion H; subst; repeat split; reflexivity.
  - destruct children as [|source [|pattern children]]; try discriminate.
    cbn [resolve_bind_roles] in H.
    destruct (resolve_bind_roles rest children) as [[remaining tail]|] eqn:E; try discriminate.
    inversion H; subst.
    specialize (IH children remaining suffix E) as [Hshapes [Hwidth Hchildren]].
    split.
    + cbn. now rewrite Hshapes.
    + split.
      * change (List.length (ordered_captures descriptor) + bind_width remaining =
          List.length (ordered_captures descriptor ++ receive_slots rest)).
        now rewrite length_app, Hwidth.
      * cbn [flat_map bind_children]. now rewrite Hchildren.
Qed.

Theorem receive_has_no_empty_join_constructor : forall has_condition children,
  checked_receive [] has_condition children = ConstructionRejected InvalidBinderLayout.
Proof. reflexivity. Qed.

Theorem receive_roster_keeps_order_and_duplicates : forall first rest,
  receive_slots (first :: rest) = ordered_captures first ++ receive_slots rest.
Proof. reflexivity. Qed.

Theorem receive_persistence_keeps_mixed_binds : forall first rest,
  receive_persistent (first :: rest) = bind_is_persistent first || receive_persistent rest.
Proof. reflexivity. Qed.

(** Scope size itself is not an emitted i32 field: nested valid binders can
    have a larger total environment. Bounds constrain the actual index/depth,
    not that unencoded total. Resource limits belong to session admission. *)
Theorem bound_zero_does_not_restrict_total_scope : forall scope,
  0 < scope -> interpret (BoundOp scope 0) [] =
    Constructed (singleton (BoundHead 0) [] (bound_summary 0)).
Proof.
  intros scope H. cbn [interpret within_target_indices forallb fits_target_index].
  unfold bound. assert (E : (0 <? scope) = true) by (apply Nat.ltb_lt; exact H).
  now rewrite E.
Qed.

Theorem scoped_pattern_reference_does_not_restrict_total_scope : forall scope,
  0 < scope -> interpret (PatternReferenceOp scope 0 1) [] =
    Constructed (singleton (PatternReferenceHead 0 1) []
      (with_connective true (bound_summary 0))).
Proof.
  intros scope H. cbn [interpret within_target_indices forallb fits_target_index].
  unfold pattern_reference. assert (E : (0 <? scope) = true) by (apply Nat.ltb_lt; exact H).
  now rewrite E.
Qed.

Definition condition_present (condition : option Value) : bool :=
  match condition with None => false | Some _ => true end.

Theorem checked_receive_constructs_exact_descriptor_image :
  forall descriptors children binds body condition,
  descriptors <> [] ->
  fits_target_index (List.length (receive_slots descriptors)) = true ->
  resolve_bind_roles descriptors children = Some (binds, body :: option_values condition) ->
  checked_receive descriptors (condition_present condition) children = Constructed
    (singleton (ReceiveHead (map descriptor_shape descriptors) (receive_slots descriptors)
      (receive_persistent descriptors) (condition_present condition))
      (receive_children binds body condition) (receive_summary binds body condition)).
Proof.
  intros descriptors children binds body condition Hnonempty Hfits Hroles.
  pose proof (receive_role_resolution_preserves_layout _ _ _ _ Hroles)
    as [Hshapes [Hwidth Hchildren]].
  unfold checked_receive. destruct descriptors as [|descriptor rest]; [contradiction|].
  unfold within_target_indices. cbn [forallb]. rewrite Hfits. cbn [andb].
  rewrite Hroles. destruct condition; cbn [option_values condition_present].
  all: unfold receive; rewrite Hwidth, Nat.eqb_refl, Hshapes; reflexivity.
Qed.

Theorem excessive_receive_count_returns_no_value : forall first rest condition children,
  fits_target_index (List.length (receive_slots (first :: rest))) = false ->
  checked_receive (first :: rest) condition children = ConstructionRejected TargetIndexOutOfRange.
Proof.
  intros first rest condition children H.
  unfold checked_receive, within_target_indices. cbn [forallb]. now rewrite H.
Qed.

Example plain_fresh_zero_preserved :
  checked_fresh (PlainFresh []) empty = Constructed
    (singleton (NewHead 0 [] []) [empty] closed_summary).
Proof. reflexivity. Qed.

Local Open Scope string_scope.

Example normalized_uri_pairs_keep_binders :
  combine (fresh_uris (UriFresh [("a", 9); ("z", 2)]))
    (fresh_binders (UriFresh [("a", 9); ("z", 2)])) = [("a", 9); ("z", 2)].
Proof. reflexivity. Qed.

Example duplicate_uri_rejected :
  checked_fresh (UriFresh [("a", 9); ("a", 2)]) empty =
    ConstructionRejected InvalidBinderLayout.
Proof. reflexivity. Qed.

Example empty_uri_rejected :
  checked_fresh (UriFresh [(EmptyString, 9)]) empty =
    ConstructionRejected InvalidBinderLayout.
Proof. reflexivity. Qed.

Example unsorted_normalized_descriptor_rejected :
  checked_fresh (UriFresh [("z", 2); ("a", 9)]) empty =
    ConstructionRejected InvalidBinderLayout.
Proof. reflexivity. Qed.

Definition no_capture_bind : BindDescriptor :=
  {| ordered_captures := []; bind_is_persistent := false |}.

Example empty_bind_retains_one_wildcard :
  resolve_bind_roles [no_capture_bind] [text "channel"; wildcard false; empty] = Some
    ([{| bind_source := text "channel"; bind_patterns := [wildcard false];
         bind_free_count := 0; bind_remainder := None |}], [empty]).
Proof. reflexivity. Qed.

Example polyadic_bind_retains_one_list :
  resolve_bind_roles [no_capture_bind] [text "channel"; list_value [text "a"; text "b"]; empty] = Some
    ([{| bind_source := text "channel"; bind_patterns := [list_value [text "a"; text "b"]];
         bind_free_count := 0; bind_remainder := None |}], [empty]).
Proof. reflexivity. Qed.

Example receive_descriptor_constructs_actual_receive :
  interpret (ReceiveOp [no_capture_bind] false) [text "channel"; wildcard false; empty] =
    receive [{| bind_source := text "channel"; bind_patterns := [wildcard false];
                bind_free_count := 0; bind_remainder := None |}] [] false empty None.
Proof. reflexivity. Qed.

Example repeated_capture_names_retained :
  receive_slots
    [{| ordered_captures := [OrdinarySlot 4; GuestSlot "capture"];
        bind_is_persistent := false |};
     {| ordered_captures := [GuestSlot "capture"]; bind_is_persistent := true |}] =
  [OrdinarySlot 4; GuestSlot "capture"; GuestSlot "capture"].
Proof. reflexivity. Qed.

Print Assumptions target_index_check_exact.
Print Assumptions checked_indices_success_bounded.
Print Assumptions pair_values_preserves_every_child.
Print Assumptions checked_resolution_matches_algebra.
Print Assumptions construction_uses_exact_ordered_children.
Print Assumptions missing_first_reference_is_exact_error.
Print Assumptions repeated_children_remain_repeated.
Print Assumptions failed_step_leaves_arena_unchanged.
Print Assumptions successful_step_appends_interpretation.
Print Assumptions successful_step_preserves_old_references.
Print Assumptions observe_returned_reference_is_actual_value.
Print Assumptions observe_missing_reference_rejects.
Print Assumptions quote_drop_forward_exact_reference.
Print Assumptions quote_drop_forward_preserves_observation.
Print Assumptions quote_drop_cannot_forward_missing_value.
Print Assumptions checked_addition_observes_constructed_values.
Print Assumptions successful_step_retains_generated_image.
Print Assumptions generated_member_has_concrete_construction.
Print Assumptions append_then_observe_text.
Print Assumptions invalid_arity_does_not_append.
Print Assumptions missing_operand_never_becomes_empty.
Print Assumptions map_missing_value_rejected.
Print Assumptions string_ltb_has_closed_order.
Print Assumptions ordered_uri_tail_all_larger.
Print Assumptions ordered_uri_check_excludes_duplicates.
Print Assumptions normalized_uri_check_retains_nonempty_unique_sequence.
Print Assumptions fresh_uri_and_binder_projection_remain_associated.
Print Assumptions checked_fresh_success_has_exact_layout.
Print Assumptions host_resolution_preserves_exact_identity.
Print Assumptions host_owner_mismatch_cannot_resolve.
Print Assumptions missing_host_slot_cannot_resolve.
Print Assumptions host_name_operation_requires_no_children.
Print Assumptions injection_key_check_excludes_duplicates.
Print Assumptions empty_injection_operation_reuses_fresh.
Print Assumptions injected_fresh_success_has_exact_layout.
Print Assumptions unused_empty_injection_key_is_retained.
Print Assumptions duplicate_injection_keys_reject.
Print Assumptions missing_injection_value_rejects.
Print Assumptions repeated_injection_values_remain_associated.
Print Assumptions receive_role_resolution_preserves_layout.
Print Assumptions receive_has_no_empty_join_constructor.
Print Assumptions receive_roster_keeps_order_and_duplicates.
Print Assumptions receive_persistence_keeps_mixed_binds.
Print Assumptions bound_zero_does_not_restrict_total_scope.
Print Assumptions scoped_pattern_reference_does_not_restrict_total_scope.
Print Assumptions checked_receive_constructs_exact_descriptor_image.
Print Assumptions excessive_receive_count_returns_no_value.
Print Assumptions plain_fresh_zero_preserved.
Print Assumptions normalized_uri_pairs_keep_binders.
Print Assumptions duplicate_uri_rejected.
Print Assumptions empty_uri_rejected.
Print Assumptions unsorted_normalized_descriptor_rejected.
Print Assumptions empty_bind_retains_one_wildcard.
Print Assumptions polyadic_bind_retains_one_list.
Print Assumptions receive_descriptor_constructs_actual_receive.
Print Assumptions repeated_capture_names_retained.
