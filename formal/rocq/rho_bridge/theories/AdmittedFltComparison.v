(** Original native FltNode and Arc<FltNode> Eq/Ne/Cmp admission.

    Source fields: runtime/src/flt_node.rs 14,21,42,53,72,204. All ten
    node fields participate, including diagnostic Strings, hole declarations,
    piece payloads/ranges, bounds and position. Actual String/vector lengths
    are inspected; declared bounds are NOT substituted for source contents.
    Reuse AdmittedNativeLeafComparison's logical String operand-byte envelope
    and AdmittedIdentityComparison's distinct identity Eq/Cmp schedules.
    Neither Eq iff cmp==Equal nor hash injectivity is assumed.

    The same trusted prebuilt x86_64/64-bit compiler/core profile applies.
    Generic slice Eq costs header7 and, at equal lengths, 3+item Eq per pair:
    address/control2 plus item default-Ne (Eq+1). Unequal lengths skip items.
    Native generic slice Ord (core/slice/cmp.rs 214,285) costs header11:
    Vec forwarding1, slice forwarding1, closure1, min/range initialization1,
    two prefix slices2, terminal1, length closure1, usize comparison2,
    outer AlwaysBreak extraction1. Each visited pair adds index/control1,
    element-result routing1, Try routing1, increment1, plus item Cmp.
    Reserve the full possible paired prefix, even if native comparison stops
    earlier. These are logical source groups, NOT machine loads/instructions,
    memcmp internals, allocator costs, or a compiler-expansion proof.

    Option costs5 except Some/Some6+String. Hole costs16+name+category;
    Piece costs5 across variants,14+text for Text/Text,18 for Hole/Hole.
    Canonical struct groups give node29+selector+fiveStrings+twoVectors.
    Node Ne is node Eq+1, not independently negated field comparisons.
    Arc Eq/Ne (alloc/sync.rs 3717,3722,3747,3768) has the actual shared
    pointer shortcut3, otherwise4+nodeEq /5+nodeEq. Arc Cmp (3877) always
    compares payload, even at the same pointer:2+nodeCmp.

    Metadata: pay one root group BEFORE pointer/variant/length projection,
    then one group BEFORE each paired next, including terminal. Unequal Eq
    vectors have NO iterator pass. No equality/hash/String comparison occurs
    during metadata. Checked arithmetic failure/refusal prevents the whole
    original native operation; prior metadata charges stay spent. The reused
    folds describe mathematical paired source projections, not allocated
    vectors, copied operands, replacement comparators or runtime plans.
    Matching on these projections is not speculative runtime inspection.
    Concrete Rust must project metadata only inside the admitted action.
    Source implementation/profile correspondence remains separately audited;
    theorems below close the arithmetic and admission composition, not that
    compiler boundary or arbitrary callback/asynchronous cancellation. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedNativeLeafComparison AdmittedIdentityComparison
  AdmittedStructuralKeyHash RholangSourceScope RholangInitialGraphResources
  GeneratedDummyCleanupReservation.
Import ListNotations.

Module AdmittedFltComparison.
Module L := AdmittedNativeLeafComparison.AdmittedNativeLeafComparison.
Module I := AdmittedIdentityComparison.AdmittedIdentityComparison.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module D := GeneratedDummyCleanupReservation.

Definition payload_operation operation := match operation with
  | L.OpCmp => L.OpCmp | _ => L.OpEq end.
Definition ne_extra operation := match operation with L.OpNe => 1 | _ => 0 end.
Definition string_work operation (lhs rhs : S.ByteString) :=
  L.string_work (payload_operation operation) (length lhs) (length rhs).
Definition option_work operation (lhs rhs : option S.ByteString) :=
  match lhs, rhs with
  | Some a, Some b => S.enum_work [string_work operation a b]
  | _, _ => S.enum_work []
  end.
Definition hole_work operation (lhs rhs : S.FltHole) := S.struct_work
  [S.identity_work; string_work operation (S.hole_name lhs) (S.hole_name rhs);
   option_work operation (S.hole_category lhs) (S.hole_category rhs); S.range_work].
Definition piece_work operation (lhs rhs : S.FltPiece) := match lhs, rhs with
  | S.TextPiece a _, S.TextPiece b _ => S.enum_work [string_work operation a b; S.range_work]
  | S.HolePiece _ _, S.HolePiece _ _ => S.enum_work [S.identity_work; S.range_work]
  | _, _ => S.enum_work []
  end.
Definition vector_header operation := match operation with L.OpCmp => 11 | _ => 7 end.
Definition vector_step operation := match operation with L.OpCmp => 4 | _ => 3 end.
Definition vector_enabled {A} operation (lhs rhs : list A) :=
  match operation with L.OpCmp => true | _ => length lhs =? length rhs end.
Definition vector_pairs {A} operation (lhs rhs : list A) :=
  if vector_enabled operation lhs rhs then combine lhs rhs else [].
Definition pair_work {A} operation (item_work : A -> A -> nat) (pair : A * A) :=
  vector_step operation + item_work (fst pair) (snd pair).
Definition vector_work {A} operation (item_work : A -> A -> nat) lhs rhs :=
  vector_header operation + S.items_work (pair_work operation item_work)
    (vector_pairs operation lhs rhs).
Definition hole_item operation := pair_work operation (hole_work operation).
Definition piece_item operation := pair_work operation (piece_work operation).
Definition node_fields operation (lhs rhs : S.FltNode) :=
  [I.ordvar_work (payload_operation operation) (S.selector lhs) (S.selector rhs);
   string_work operation (S.selector_name lhs) (S.selector_name rhs);
   string_work operation (S.category lhs) (S.category rhs);
   string_work operation (S.open_src lhs) (S.open_src rhs);
   string_work operation (S.body_src lhs) (S.body_src rhs);
   vector_work operation (hole_work operation) (S.holes lhs) (S.holes rhs);
   vector_work operation (piece_work operation) (S.pieces lhs) (S.pieces rhs);
   string_work operation (S.close_src lhs) (S.close_src rhs); S.bounds_work; S.scalar_work].
Definition node_work operation lhs rhs := ne_extra operation + S.struct_work (node_fields operation lhs rhs).
Definition fixed_payload_work operation lhs rhs :=
  I.ordvar_work (payload_operation operation) (S.selector lhs) (S.selector rhs) +
  string_work operation (S.selector_name lhs) (S.selector_name rhs) +
  string_work operation (S.category lhs) (S.category rhs) +
  string_work operation (S.open_src lhs) (S.open_src rhs) +
  string_work operation (S.body_src lhs) (S.body_src rhs) +
  string_work operation (S.close_src lhs) (S.close_src rhs).

Theorem nested_field_groups : forall operation hole other a b identity range,
  hole_work operation hole other = 16 + string_work operation (S.hole_name hole) (S.hole_name other) +
    option_work operation (S.hole_category hole) (S.hole_category other) /\
  option_work operation (Some a) (Some b) = 6 + string_work operation a b /\
  piece_work operation (S.TextPiece a range) (S.TextPiece b range) = 14 + string_work operation a b /\
  piece_work operation (S.HolePiece identity range) (S.HolePiece identity range) = 18 /\
  piece_work operation (S.TextPiece a range) (S.HolePiece identity range) = 5.
Proof.
  intros. unfold hole_work, option_work, piece_work, S.struct_work, S.enum_work, S.field_sum.
  cbn [fold_right]. change S.identity_work with 4. change S.range_work with 7.
  repeat split; lia.
Qed.
Theorem node_native_groups : forall operation lhs rhs,
  node_work operation lhs rhs = ne_extra operation + 29 + fixed_payload_work operation lhs rhs +
    vector_work operation (hole_work operation) (S.holes lhs) (S.holes rhs) +
    vector_work operation (piece_work operation) (S.pieces lhs) (S.pieces rhs).
Proof.
  intros. unfold node_work, node_fields, S.struct_work, S.field_sum, fixed_payload_work.
  cbn [fold_right]. change S.bounds_work with 16. change S.scalar_work with 2. lia.
Qed.
Theorem node_ne_uses_eq_payload : forall lhs rhs,
  node_work L.OpNe lhs rhs = 1 + node_work L.OpEq lhs rhs.
Proof. reflexivity. Qed.
Theorem paired_length_is_minimum : forall A (lhs rhs : list A),
  length (combine lhs rhs) = Nat.min (length lhs) (length rhs).
Proof.
  intros A lhs. induction lhs as [|a rest IH]; intros [|b tail]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IH.
Qed.
Theorem native_visited_prefix_is_covered : forall A (work : A -> nat) prefix suffix,
  S.items_work work prefix <= S.items_work work (prefix ++ suffix).
Proof.
  intros A work prefix. induction prefix as [|item rest IH]; intro suffix;
    cbn [S.items_work fold_right app]; [lia|]. specialize (IH suffix). lia.
Qed.

(** Reuse the paid flat fold. Each item is a mathematical pair of borrowed
    source items; one constant group pays both next/projection operations. *)
Definition vector_steps {A} operation (lhs rhs : list A) :=
  if vector_enabled operation lhs rhs then 1 + length (combine lhs rhs) else 0.
Definition inspect_vector {A} (item : A * A -> nat) operation lhs rhs maximum available accumulated :=
  if vector_enabled operation lhs rhs then
    S.inspect_items item maximum (combine lhs rhs) available accumulated
  else Accepted available accumulated.
Theorem successful_vector_inspection : forall A (item : A * A -> nat) operation lhs rhs
  maximum available accumulated paid total,
  accumulated <= maximum ->
  inspect_vector item operation lhs rhs maximum available accumulated = Accepted paid total ->
  total = accumulated + S.items_work item (vector_pairs operation lhs rhs) /\
  total <= maximum /\ work_left paid + vector_steps operation lhs rhs = work_left available /\
  units_left paid = units_left available.
Proof.
  intros A item operation lhs rhs maximum available accumulated paid total HB HI.
  unfold inspect_vector in HI. unfold vector_pairs, vector_steps.
  destruct (vector_enabled operation lhs rhs) eqn:HE.
  - apply S.successful_metadata_fold_is_exact in HI. exact HI.
  - inversion HI; subst. cbn [S.items_work fold_right]. repeat split; lia.
Qed.
Theorem vector_metadata_counts : forall A (lhs rhs : list A),
  vector_steps L.OpCmp lhs rhs = 1 + Nat.min (length lhs) (length rhs) /\
  vector_steps L.OpEq lhs rhs =
    (if length lhs =? length rhs then 1 + length lhs else 0).
Proof.
  intros A lhs rhs. unfold vector_steps, vector_enabled. rewrite paired_length_is_minimum.
  split; [reflexivity|]. destruct (length lhs =? length rhs) eqn:HE; [|reflexivity].
  apply Nat.eqb_eq in HE. rewrite HE, Nat.min_id. reflexivity.
Qed.
Definition inspection_base forwarding operation lhs rhs :=
  forwarding + ne_extra operation + (29 + 2 * vector_header operation) + fixed_payload_work operation lhs rhs.
Definition node_steps operation lhs rhs :=
  1 + vector_steps operation (S.holes lhs) (S.holes rhs) +
      vector_steps operation (S.pieces lhs) (S.pieces rhs).
Theorem inspection_sum_is_native_work : forall forwarding operation lhs rhs,
  inspection_base forwarding operation lhs rhs +
    S.items_work (hole_item operation) (vector_pairs operation (S.holes lhs) (S.holes rhs)) +
    S.items_work (piece_item operation) (vector_pairs operation (S.pieces lhs) (S.pieces rhs)) =
  forwarding + node_work operation lhs rhs.
Proof.
  intros. rewrite node_native_groups.
  unfold inspection_base, vector_work, hole_item, piece_item. lia.
Qed.
Definition inspect_node maximum forwarding operation lhs rhs available :=
  match precharged_action false available 1 0
    (fun _ => checked_sum maximum 0 (inspection_base forwarding operation lhs rhs)) with
  | Refused remaining => Refused remaining
  | Accepted remaining accumulated =>
    match inspect_vector (hole_item operation) operation (S.holes lhs) (S.holes rhs)
      maximum remaining accumulated with
    | Refused remaining => Refused remaining
    | Accepted remaining accumulated =>
      inspect_vector (piece_item operation) operation (S.pieces lhs) (S.pieces rhs)
        maximum remaining accumulated
    end
  end.
Theorem successful_node_inspection : forall maximum forwarding operation lhs rhs available paid work,
  inspect_node maximum forwarding operation lhs rhs available = Accepted paid work ->
  work = forwarding + node_work operation lhs rhs /\ work <= maximum /\
  work_left paid + node_steps operation lhs rhs = work_left available /\
  units_left paid = units_left available.
Proof.
  intros maximum forwarding operation lhs rhs available paid work HI. unfold inspect_node in HI.
  destruct (precharged_action false available 1 0
    (fun _ => checked_sum maximum 0 (inspection_base forwarding operation lhs rhs)))
    as [remaining|remaining accumulated] eqn:HR; [discriminate|].
  destruct (inspect_vector (hole_item operation) operation (S.holes lhs) (S.holes rhs)
    maximum remaining accumulated) as [after_holes|after_holes hole_total] eqn:HH; [discriminate|].
  apply successful_action_constructs_only_the_paid_result in HR.
  destruct HR as [_ [HB [HW HU]]]. apply checked_sum_success_is_exact_and_bounded in HB.
  apply successful_vector_inspection in HH; [|lia].
  apply successful_vector_inspection in HI; [|lia].
  pose proof (inspection_sum_is_native_work forwarding operation lhs rhs) as HE.
  unfold node_steps. lia.
Qed.

Inductive Request := NodePair (lhs rhs : S.FltNode) | ArcPair (shared : bool) (lhs rhs : S.FltNode).
Definition left_node request := match request with NodePair a _ | ArcPair _ a _ => a end.
Definition right_node request := match request with NodePair _ b | ArcPair _ _ b => b end.
(** shared projects actual Arc::ptr_eq, never a user-supplied receipt. *)
Definition shortcut operation request := match request with
  | NodePair _ _ => false
  | ArcPair shared _ _ => match operation with L.OpCmp => false | _ => shared end
  end.
Definition forwarding operation request := match request with
  | NodePair _ _ => 0
  | ArcPair _ _ _ => match operation with L.OpCmp => 2 | _ => 4 end
  end.
Definition request_work operation request :=
  if shortcut operation request then 3 else
    forwarding operation request + node_work operation (left_node request) (right_node request).
Definition metadata_work operation request :=
  if shortcut operation request then 1 else node_steps operation (left_node request) (right_node request).
Definition inspect_shared maximum available :=
  precharged_action false available 1 0 (fun _ => checked_sum maximum 0 3).
Definition inspect_request maximum operation request available :=
  if shortcut operation request then inspect_shared maximum available else
    inspect_node maximum (forwarding operation request) operation (left_node request) (right_node request) available.
Theorem arc_native_branches : forall lhs rhs shared,
  request_work L.OpEq (ArcPair true lhs rhs) = 3 /\
  request_work L.OpNe (ArcPair true lhs rhs) = 3 /\
  request_work L.OpEq (ArcPair false lhs rhs) = 4 + node_work L.OpEq lhs rhs /\
  request_work L.OpNe (ArcPair false lhs rhs) = 5 + node_work L.OpEq lhs rhs /\
  request_work L.OpCmp (ArcPair shared lhs rhs) = 2 + node_work L.OpCmp lhs rhs.
Proof. repeat split; reflexivity. Qed.
Theorem successful_request_inspection : forall maximum operation request available paid work,
  inspect_request maximum operation request available = Accepted paid work ->
  work = request_work operation request /\ work <= maximum /\
  work_left paid + metadata_work operation request = work_left available /\
  units_left paid = units_left available.
Proof.
  intros maximum operation request available paid work HI.
  unfold inspect_request in HI. unfold request_work, metadata_work.
  destruct (shortcut operation request).
  - unfold inspect_shared in HI. apply successful_action_constructs_only_the_paid_result in HI.
    destruct HI as [_ [HB [HW HU]]]. apply checked_sum_success_is_exact_and_bounded in HB. lia.
  - now apply successful_node_inspection in HI.
Qed.
Theorem root_refusal_precedes_metadata : forall maximum operation request available,
  reserve available 1 0 = None -> inspect_request maximum operation request available = Refused available.
Proof.
  intros maximum operation request available HR. unfold inspect_request.
  destruct (shortcut operation request); [unfold inspect_shared|unfold inspect_node];
    rewrite (failed_precharge_is_independent_of_constructor _ _ _ _ _ HR); reflexivity.
Qed.
Theorem overflowing_request_cannot_execute : forall maximum operation request available,
  maximum < request_work operation request ->
  exists remaining, inspect_request maximum operation request available = Refused remaining.
Proof.
  intros maximum operation request available HO.
  destruct (inspect_request maximum operation request available) as [remaining|remaining work] eqn:HI.
  - exists remaining. reflexivity.
  - apply successful_request_inspection in HI. lia.
Qed.
Theorem execution_has_no_owned_payload : forall operation request,
  D.weighted D.base_work_weight (S.work_counts (request_work operation request)) = request_work operation request /\
  D.weighted D.record_weight (S.work_counts (request_work operation request)) = 0 /\
  D.weighted D.byte_weight (S.work_counts (request_work operation request)) = 0.
Proof. intros. apply S.work_counts_projection. Qed.

Section OriginalExecution.
Variable execute_native : forall operation, Request -> L.ResultType operation.
(** The ignored initial result is only a typed mathematical slot needed by
    the existing execution combinator. No preliminary native call is made. *)
Definition initial_result operation : L.ResultType operation := match operation with
  | L.OpEq | L.OpNe => false | L.OpCmp => Eq end.
Definition admitted_comparison (supported : bool) maximum operation request available :=
  S.execute_original (fun request (_ : L.ResultType operation) => execute_native operation request)
    (fun request available => if supported then inspect_request maximum operation request available
       else Refused available) request (initial_result operation) available.
Theorem successful_comparison_is_original_and_paid : forall supported maximum operation request available paid result,
  admitted_comparison supported maximum operation request available = Accepted paid result ->
  supported = true /\ result = execute_native operation request /\ request_work operation request <= maximum /\
  work_left paid + metadata_work operation request + request_work operation request = work_left available /\
  units_left paid = units_left available.
Proof.
  intros supported maximum operation request available paid result HC.
  unfold admitted_comparison, S.execute_original in HC. destruct supported; [|discriminate].
  destruct (inspect_request maximum operation request available)
    as [remaining|remaining work] eqn:HI; [discriminate|].
  apply successful_request_inspection in HI.
  apply successful_action_constructs_only_the_paid_result in HC.
  destruct HC as [_ [HR [HW HU]]]. inversion HR; subst.
  repeat split; try reflexivity; lia.
Qed.
Theorem metadata_refusal_prevents_native_call : forall maximum operation request available remaining,
  inspect_request maximum operation request available = Refused remaining ->
  admitted_comparison true maximum operation request available = Refused remaining.
Proof.
  intros maximum operation request available remaining HI.
  unfold admitted_comparison, S.execute_original. now rewrite HI.
Qed.
Theorem execution_refusal_keeps_metadata_charge : forall maximum operation request available remaining work,
  inspect_request maximum operation request available = Accepted remaining work -> reserve remaining work 0 = None ->
  admitted_comparison true maximum operation request available = Refused remaining.
Proof.
  intros maximum operation request available remaining work HI HR.
  unfold admitted_comparison, S.execute_original. rewrite HI.
  now apply failed_precharge_is_independent_of_constructor.
Qed.
Theorem cancelled_execution_stage_keeps_metadata_charge : forall operation request remaining work,
  precharged_action true remaining work 0 (fun _ => Some (execute_native operation request)) = Refused remaining.
Proof. reflexivity. Qed.
End OriginalExecution.
Theorem cancelled_pair_stage_precedes_next : forall A (item : A * A -> nat) pair maximum accumulated available,
  precharged_action true available 1 0
    (fun _ => checked_sum maximum accumulated (item pair)) = Refused available.
Proof. reflexivity. Qed.

Print Assumptions nested_field_groups.
Print Assumptions node_native_groups.
Print Assumptions node_ne_uses_eq_payload.
Print Assumptions paired_length_is_minimum.
Print Assumptions native_visited_prefix_is_covered.
Print Assumptions successful_vector_inspection.
Print Assumptions vector_metadata_counts.
Print Assumptions inspection_sum_is_native_work.
Print Assumptions successful_node_inspection.
Print Assumptions arc_native_branches.
Print Assumptions successful_request_inspection.
Print Assumptions root_refusal_precedes_metadata.
Print Assumptions overflowing_request_cannot_execute.
Print Assumptions execution_has_no_owned_payload.
Print Assumptions successful_comparison_is_original_and_paid.
Print Assumptions metadata_refusal_prevents_native_call.
Print Assumptions execution_refusal_keeps_metadata_charge.
Print Assumptions cancelled_execution_stage_keeps_metadata_charge.
Print Assumptions cancelled_pair_stage_precedes_next.
End AdmittedFltComparison.
