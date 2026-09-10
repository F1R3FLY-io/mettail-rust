(** FltNode selector-only binding, matching runtime/src/flt_node.rs.

    Five strings, ordered holes/pieces, bounds and position are preserved.
    Only the selector uses the existing known-roster operation. Strings model
    byte strings, so String.length counts bytes, not Unicode scalar values.
    Payload measures exclude the separately charged selector. Records are
    logical retention units, not allocator bytes. Declared bounds are not
    trusted for either measure. Concrete index/depth representability retains
    the restrictions documented in MonikerLeafOperations.

    This proves structural composition, not parsing, freshening, validation,
    a complete reservation schedule, or whole-graph correctness. *)
From Stdlib Require Import List String Arith.
From RhoBridge Require Import MonikerLeafOperations.
Import ListNotations KnownRosterLeaves.

Module SelectorPayloadComposition.
Record Hole := {
  hole_id : nat; hole_name : string; hole_category : option string;
  hole_range : nat * nat
}.
Inductive Piece :=
| TextPiece (text : string) (range : nat * nat)
| HolePiece (id : nat) (range : nat * nat).
Record Payload := {
  selector_spelling : string; result_category : string;
  opener : string; body_source : string; closer : string;
  holes : list Hole; pieces : list Piece;
  declared_bounds : (nat * nat * nat * nat * nat)%type;
  source_position : nat
}.
Record Node := { selector : @LeafVariable string; payload : Payload }.

Definition replace_selector (node : Node) (value : @LeafVariable string) :=
  {| selector := value; payload := payload node |}.
Definition checked_node operation maximum depth roster node : option Node :=
  option_map (replace_selector node)
    (checked_operation operation maximum depth roster (selector node)).
Definition reference_close_node depth roster node : Node :=
  replace_selector node (reference_close depth roster (selector node)).

Theorem successful_node_has_exact_selector_and_unchanged_payload :
  forall operation maximum depth roster node result,
  checked_node operation maximum depth roster node = Some result ->
  checked_operation operation maximum depth roster (selector node) =
    Some (selector result) /\ payload result = payload node.
Proof.
  intros operation maximum depth roster node result H.
  unfold checked_node in H.
  destruct (checked_operation operation maximum depth roster (selector node))
    as [value|] eqn:HS; cbn in H; [|discriminate].
  inversion H; subst. split; reflexivity.
Qed.

Theorem successful_close_is_reference_close :
  forall maximum depth roster node result,
  checked_node CloseLeaf maximum depth roster node = Some result ->
  result = reference_close_node depth roster node.
Proof.
  intros maximum depth roster node result H.
  unfold checked_node, checked_operation in H.
  destruct (checked_close maximum depth roster (selector node))
    as [value|] eqn:HS; cbn in H; [|discriminate].
  inversion H; subst.
  apply checked_close_success_matches_reference in HS.
  unfold reference_close_node. now rewrite HS.
Qed.

Theorem representable_close_lifts_reference :
  forall maximum depth roster node,
  List.length roster <= S maximum ->
  checked_node CloseLeaf maximum depth roster node =
    Some (reference_close_node depth roster node).
Proof.
  intros maximum depth roster node H. unfold checked_node, checked_operation.
  rewrite bounded_roster_close_is_total_and_matches_reference by exact H.
  reflexivity.
Qed.

Theorem missing_open_selector_has_no_node :
  forall maximum depth roster index pretty retained,
  nth_error roster index = None ->
  checked_node OpenLeaf maximum depth roster
    {| selector := Bound depth index pretty; payload := retained |} = None.
Proof.
  intros maximum depth roster index pretty retained H.
  unfold checked_node. cbn [selector].
  rewrite missing_matching_depth_index_refuses by exact H. reflexivity.
Qed.

Theorem clone_lifts_without_changing_node :
  forall maximum depth roster node,
  checked_node CloneLeaf maximum depth roster node = Some node.
Proof. intros maximum depth roster [value retained]; reflexivity. Qed.

Definition optional_bytes value :=
  match value with None => 0 | Some text => String.length text end.
Definition hole_bytes hole :=
  String.length (hole_name hole) + optional_bytes (hole_category hole).
Definition piece_bytes piece :=
  match piece with TextPiece text _ => String.length text | HolePiece _ _ => 0 end.
Definition payload_bytes retained :=
  String.length (selector_spelling retained) + String.length (result_category retained) +
  String.length (opener retained) + String.length (body_source retained) +
  String.length (closer retained) +
  fold_right (fun hole rest => hole_bytes hole + rest) 0 (holes retained) +
  fold_right (fun piece rest => piece_bytes piece + rest) 0 (pieces retained).
Definition hole_records hole :=
  2 + match hole_category hole with None => 0 | Some _ => 1 end.
Definition piece_records piece :=
  match piece with TextPiece _ _ => 2 | HolePiece _ _ => 1 end.
(** One node, five string headers and two vector headers, plus entry records
    and their string headers. Strings' allocated bytes are measured above. *)
Definition payload_records retained :=
  8 + fold_right (fun hole rest => hole_records hole + rest) 0 (holes retained) +
  fold_right (fun piece rest => piece_records piece + rest) 0 (pieces retained).

Theorem successful_binding_preserves_payload_copy_measures :
  forall operation maximum depth roster node result,
  checked_node operation maximum depth roster node = Some result ->
  payload_bytes (payload result) = payload_bytes (payload node) /\
  payload_records (payload result) = payload_records (payload node).
Proof.
  intros operation maximum depth roster node result H.
  apply successful_node_has_exact_selector_and_unchanged_payload in H.
  destruct H as [_ HP]. now rewrite HP.
Qed.

Definition with_bounds p bounds :=
  {| selector_spelling := selector_spelling p; result_category := result_category p;
     opener := opener p; body_source := body_source p; closer := closer p;
     holes := holes p; pieces := pieces p; declared_bounds := bounds;
     source_position := source_position p |}.
Theorem declared_bounds_cannot_change_copy_measures :
  forall p bounds,
  payload_bytes (with_bounds p bounds) = payload_bytes p /\
  payload_records (with_bounds p bounds) = payload_records p.
Proof. intros; split; reflexivity. Qed.

Print Assumptions successful_node_has_exact_selector_and_unchanged_payload.
Print Assumptions successful_close_is_reference_close.
Print Assumptions representable_close_lifts_reference.
Print Assumptions missing_open_selector_has_no_node.
Print Assumptions clone_lifts_without_changing_node.
Print Assumptions successful_binding_preserves_payload_copy_measures.
Print Assumptions declared_bounds_cannot_change_copy_measures.
End SelectorPayloadComposition.
