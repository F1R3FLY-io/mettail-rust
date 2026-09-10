(** Compact observations for the initial neutral construction target.

    A flat append node retains its two references. It does not copy or flatten
    either child's heads. This module proves that a three-case cached head
    classification and the exact existing Summary suffice for the observations
    consumed by the lowerer. The cache describes constructed values, never
    source node tags, parse ranking, or semantic execution.

    Checked references/private append are supplied by RholangConstructionProtocol.
    These facts complement that protocol; they do not certify Rust ownership,
    allocator behavior, or arbitrary untrusted serialized graphs. *)
From Stdlib Require Import List String Bool ZArith.
From RhoBridge Require Import RholangTargetConstruction RholangConstructionProtocol.
Import ListNotations.

Inductive HeadShape := NoHeads | OneText | OtherHeads.
Definition text_head (head : Head) : bool :=
  match head with MakeHead (TextHead _) [] => true | _ => false end.
Definition shape_of_heads (heads : list Head) : HeadShape :=
  match heads with
  | [] => NoHeads
  | [head] => if text_head head then OneText else OtherHeads
  | _ => OtherHeads
  end.
Definition append_shape (left right : HeadShape) : HeadShape :=
  match left, right with
  | NoHeads, shape | shape, NoHeads => shape
  | _, _ => OtherHeads
  end.

Theorem append_shape_is_exact : forall left right,
  shape_of_heads (left ++ right) =
  append_shape (shape_of_heads left) (shape_of_heads right).
Proof.
  intros [|left [|next rest]] [|right [|next' rest']]; cbn;
    repeat match goal with
    | |- context [text_head ?head] => destruct (text_head head)
    end; reflexivity.
Qed.

Definition shape_is_text (shape : HeadShape) : bool :=
  match shape with OneText => true | _ => false end.

Theorem cached_text_observation_exact : forall value,
  shape_is_text (shape_of_heads (heads_of value)) = single_string value.
Proof.
  intros [heads summary]. destruct heads as [|[kind children] [|next rest]];
    cbn; try reflexivity.
  all: destruct kind; destruct children; reflexivity.
Qed.

Record ConstructionFact := { head_shape : HeadShape; structural_summary : Summary }.
Definition fact_of (value : Value) : ConstructionFact :=
  {| head_shape := shape_of_heads (heads_of value);
     structural_summary := summary_of value |}.
Definition append_fact (left right : ConstructionFact) : ConstructionFact :=
  {| head_shape := append_shape (head_shape left) (head_shape right);
     structural_summary := join_summary (structural_summary left) (structural_summary right) |}.
Definition fact_observation (fact : ConstructionFact) : StructuralObservation :=
  {| observed_single_string := shape_is_text (head_shape fact);
     observed_summary := structural_summary fact |}.

Theorem append_fact_is_exact : forall left right,
  append_fact (fact_of left) (fact_of right) = fact_of (append left right).
Proof.
  intros [left summary_left] [right summary_right].
  unfold append_fact, fact_of, append; cbn.
  now rewrite append_shape_is_exact.
Qed.

Theorem fact_observation_is_exact : forall value,
  fact_observation (fact_of value) = observation_of value.
Proof.
  intro value. unfold fact_observation, fact_of, observation_of; cbn.
  now rewrite cached_text_observation_exact.
Qed.

(** Fresh's observation is not the ordinary union of all children. The source
    body determines both the shifted free bits and the connective flag; ordered
    injection values remain children but never contribute to this summary. *)
Definition fresh_fact (width : nat) (body : ConstructionFact) : ConstructionFact :=
  {| head_shape := OtherHeads;
     structural_summary := shifted_summary width (structural_summary body) |}.

Theorem fresh_fact_is_exact : forall width uris keys body injections value,
  fresh_with_injections width uris keys body injections = Constructed value ->
  fresh_fact width (fact_of body) = fact_of value.
Proof.
  intros width uris keys body injections value H.
  apply injected_fresh_preserves_all_entries in H as [_ [_ [HH HS]]].
  unfold fresh_fact, fact_of. rewrite HH, HS. reflexivity.
Qed.

(** This is the first fully implemented family, not a permissive operation
    enum whose remaining variants silently fail. Wider families retain their
    separate construction and source-admission obligations. *)
Inductive Primitive :=
| EmptyPrimitive | IntegerPrimitive (number : Z) | BooleanPrimitive (flag : bool)
| TextPrimitive (payload : string) | AppendPrimitive
| BoundPrimitive (scope index : nat) | WildcardPrimitive (connective : bool).
Definition primitive_operation (primitive : Primitive) : ConstructOp :=
  match primitive with
  | EmptyPrimitive => EmptyOp | IntegerPrimitive number => IntegerOp number
  | BooleanPrimitive flag => BooleanOp flag | TextPrimitive payload => TextOp payload
  | AppendPrimitive => AppendOp
  | BoundPrimitive scope index => BoundOp scope index
  | WildcardPrimitive flag => WildcardOp flag
  end.
Definition primitive_fact (primitive : Primitive) (children : list ConstructionFact)
    : option ConstructionFact :=
  match primitive, children with
  | EmptyPrimitive, [] => Some (fact_of empty)
  | IntegerPrimitive number, [] =>
    match integer number with Constructed value => Some (fact_of value) | _ => None end
  | BooleanPrimitive flag, [] => Some (fact_of (boolean flag))
  | TextPrimitive payload, [] => Some (fact_of (text payload))
  | AppendPrimitive, [lhs; rhs] => Some (append_fact lhs rhs)
  | BoundPrimitive scope index, [] =>
    match within_target_indices [index] (bound scope index) with
    | Constructed value => Some (fact_of value) | _ => None end
  | WildcardPrimitive flag, [] => Some (fact_of (wildcard flag))
  | _, _ => None
  end.

Theorem primitive_cache_commutes : forall primitive children,
  primitive_fact primitive (map fact_of children) =
  match interpret (primitive_operation primitive) children with
  | Constructed value => Some (fact_of value)
  | ConstructionRejected _ => None
  end.
Proof.
  intros primitive children.
  destruct primitive; destruct children as [|left [|right [|extra rest]]];
    cbn [primitive_fact primitive_operation interpret map]; try reflexivity.
  now rewrite append_fact_is_exact.
Qed.

(** Generic ordered lookup: the same loop can borrow values or cached facts.
    This law does not allow a cache mismatch or a missing index to be hidden. *)
Inductive LookupResult (A : Type) := Found (values : list A) | Missing (index : nat).
Arguments Found {A} _.
Arguments Missing {A} _.
Fixpoint lookup_ordered {A} (arena : list A) (references : list nat) : LookupResult A :=
  match references with
  | [] => Found []
  | index :: rest =>
    match nth_error arena index with
    | None => Missing index
    | Some value =>
      match lookup_ordered arena rest with
      | Found values => Found (value :: values)
      | Missing first => Missing first
      end
    end
  end.
Definition map_lookup {A B} (f : A -> B) (result : LookupResult A) : LookupResult B :=
  match result with Found values => Found (map f values) | Missing index => Missing index end.

Theorem lookup_mapping_commutes : forall A B (f : A -> B) arena references,
  lookup_ordered (map f arena) references = map_lookup f (lookup_ordered arena references).
Proof.
  intros A B f arena references. induction references as [|index rest IH]; cbn; auto.
  rewrite nth_error_map. destruct (nth_error arena index); cbn; auto.
  rewrite IH. destruct (lookup_ordered arena rest); reflexivity.
Qed.

Theorem ordered_lookup_reuses_checked_protocol : forall arena references,
  resolve_checked arena references =
  match lookup_ordered arena references with
  | Found values => ChildrenResolved values
  | Missing index => ChildrenRejected (MissingReference index)
  end.
Proof.
  intros arena references. induction references as [|index rest IH]; cbn; auto.
  destruct (nth_error arena index); cbn; auto.
  rewrite IH. destruct (lookup_ordered arena rest); reflexivity.
Qed.

Theorem mapped_cache_preserves_first_missing_reference : forall arena references index,
  lookup_ordered arena references = Missing index ->
  lookup_ordered (map fact_of arena) references = Missing index.
Proof. intros. rewrite lookup_mapping_commutes, H. reflexivity. Qed.

Theorem mapped_cache_preserves_ordered_constructed_children : forall arena references children,
  resolve_checked arena references = ChildrenResolved children ->
  lookup_ordered (map fact_of arena) references = Found (map fact_of children).
Proof.
  intros arena references children H. rewrite ordered_lookup_reuses_checked_protocol in H.
  rewrite lookup_mapping_commutes.
  destruct (lookup_ordered arena references); inversion H; subst; reflexivity.
Qed.

Example shared_child_retains_both_edges_and_is_not_single_text : forall payload,
  primitive_fact AppendPrimitive [fact_of (text payload); fact_of (text payload)] =
  Some {| head_shape := OtherHeads; structural_summary := closed_summary |}.
Proof. reflexivity. Qed.

Example empty_append_text_is_still_single_text : forall payload,
  primitive_fact AppendPrimitive [fact_of empty; fact_of (text payload)] =
  Some {| head_shape := OneText; structural_summary := closed_summary |}.
Proof. reflexivity. Qed.

Print Assumptions append_shape_is_exact.
Print Assumptions cached_text_observation_exact.
Print Assumptions append_fact_is_exact.
Print Assumptions fact_observation_is_exact.
Print Assumptions fresh_fact_is_exact.
Print Assumptions primitive_cache_commutes.
Print Assumptions lookup_mapping_commutes.
Print Assumptions ordered_lookup_reuses_checked_protocol.
Print Assumptions mapped_cache_preserves_first_missing_reference.
Print Assumptions mapped_cache_preserves_ordered_constructed_children.
Print Assumptions shared_child_retains_both_edges_and_is_not_single_text.
Print Assumptions empty_append_text_is_still_single_text.
