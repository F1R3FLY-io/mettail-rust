(** Required structural native leaves following AdmittedKeyHashExecution.

    Source inventory: runtime/src/binding.rs OrdVar, moniker 0.5.0
    {unique_id,free_var,bound_var,var,binder}.rs, and runtime/src/flt_node.rs.
    FreeVar hashes only UniqueId; BoundVar hashes scope then binder index.
    Neither hashes pretty_name. FltNode's derived Hash DOES hash diagnostic
    Strings, every hole/piece/range, all five bounds, and position. The bounds
    values do not replace traversing the actual vectors and String extents.

    This is a source-group envelope, not a different hash algorithm. Struct
    and wrapper D(fields)=1+sum(1+field); enum E(active)=5+sum(1+field);
    vector V(items)=7+sum(2+item); Arc=2+payload. The enum header allows entry,
    discriminant/match, and at most three groups for native signed tag hashing.
    The Vec header allows Vec/slice/hash_slice entry, length-prefix/accumulator,
    iterator initialization and final next; each element pays next/handoff.
    Concrete compiler-derived tag calls must be checked against the audited
    compiler profile. These equations alone do not prove compiler expansion.

    Metadata admission is separate from this native-execution allowance.
    One paid constant-size root group covers fixed metadata and iterator setup.
    Every metadata next, including the terminal next, is paid before its
    action. A yielded-item group includes its fixed-shape projections and
    checked arithmetic; nested vectors use their own paid folds. This is
    constant-size per item for the concrete holes and pieces below. No String
    contents are scanned during metadata inspection. The existing Fx envelope
    pays the byte scan during the final native Hash call.

    Lists/records below are mathematical source projections, not runtime
    allocations or a cached execution plan. Rust borrows original values and
    keeps the original hasher. A metadata refusal or arithmetic overflow
    prevents the WHOLE native Hash call. No theorem refunds earlier metadata
    charges, attests a custom sysroot, bounds arbitrary Hasher implementations,
    or establishes Eq/Ord, generated task lifecycle, or HashBag admission. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedKeyHashExecution RholangSourceScope
  RholangInitialGraphResources GeneratedDummyCleanupReservation
  RequiredVecBindingReservation.
Import ListNotations.

Module AdmittedStructuralKeyHash.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module D := GeneratedDummyCleanupReservation.
Module V := RequiredVecBindingReservation.

Definition ByteString := list nat.
Definition string_work (bytes : ByteString) := H.fx_string_envelope (length bytes).
Definition field_sum := fold_right (fun work rest => 1 + work + rest) 0.
Definition struct_work fields := 1 + field_sum fields.
Definition enum_work fields := 5 + field_sum fields.
Definition vector_work {A} (item_work : A -> nat) (items : list A) :=
  7 + fold_right (fun item rest => 2 + item_work item + rest) 0 items.
Definition arc_work payload_work := 2 + payload_work.

Definition scalar_work := 2.
Definition identity_work := struct_work [scalar_work].
Definition free_work := struct_work [identity_work].
Definition binder_work := struct_work [free_work].
Definition bound_work := struct_work [identity_work; identity_work].

Inductive MonikerVar :=
| Free (identity : nat) (pretty_name : option ByteString)
| Bound (scope index : nat) (pretty_name : option ByteString).
Inductive MonikerIdentity :=
| FreeIdentity (identity : nat)
| BoundIdentity (scope index : nat).
Definition hash_identity value := match value with
  | Free identity _ => FreeIdentity identity
  | Bound scope index _ => BoundIdentity scope index
  end.
Definition ordvar_work value := struct_work
  [match value with Free _ _ => enum_work [free_work]
                   | Bound _ _ _ => enum_work [bound_work] end].
Record Binder := { binder_identity : nat; binder_pretty : option ByteString }.
Definition binders_work := @vector_work Binder (fun _ => binder_work).

Theorem moniker_native_groups :
  identity_work = 4 /\ free_work = 6 /\ binder_work = 8 /\ bound_work = 11.
Proof. repeat split; reflexivity. Qed.
Theorem ordvar_native_groups : forall identity scope index pretty,
  ordvar_work (Free identity pretty) = 14 /\
  ordvar_work (Bound scope index pretty) = 19.
Proof. repeat split; reflexivity. Qed.
Theorem moniker_pretty_names_are_not_hashed : forall identity scope index a b,
  hash_identity (Free identity a) = hash_identity (Free identity b) /\
  hash_identity (Bound scope index a) = hash_identity (Bound scope index b) /\
  ordvar_work (Free identity a) = ordvar_work (Free identity b) /\
  ordvar_work (Bound scope index a) = ordvar_work (Bound scope index b).
Proof. repeat split; reflexivity. Qed.
Theorem binder_vector_native_groups : forall binders,
  binders_work binders = 7 + 10 * length binders.
Proof.
  intro binders. unfold binders_work, vector_work.
  assert (HF : fold_right (fun (_ : Binder) rest => 2 + binder_work + rest) 0
    binders = 10 * length binders).
  { induction binders; cbn [fold_right length] in *; [reflexivity|].
    change (10 + fold_right (fun (_ : Binder) rest => 2 + binder_work + rest) 0
      binders = 10 * S (length binders)). lia. }
  now rewrite HF.
Qed.

Record FltRange := { range_start : nat; range_end : nat }.
Record FltBounds := {
  source_bytes : nat; body_bytes : nat; piece_count : nat;
  hole_declarations : nat; hole_occurrences : nat
}.
Record FltHole := {
  hole_id : nat; hole_name : ByteString; hole_category : option ByteString;
  hole_first_occurrence : FltRange
}.
Inductive FltPiece :=
| TextPiece (text : ByteString) (range : FltRange)
| HolePiece (identity : nat) (range : FltRange).
Record FltNode := {
  selector : MonikerVar; selector_name : ByteString; category : ByteString;
  open_src : ByteString; body_src : ByteString;
  holes : list FltHole; pieces : list FltPiece; close_src : ByteString;
  bounds : FltBounds; position : nat
}.

Definition range_work := struct_work [scalar_work; scalar_work].
Definition bounds_work := struct_work
  [scalar_work; scalar_work; scalar_work; scalar_work; scalar_work].
Definition optional_string_work value := match value with
  | None => enum_work [] | Some bytes => enum_work [string_work bytes] end.
Definition hole_work hole := struct_work
  [identity_work; string_work (hole_name hole);
   optional_string_work (hole_category hole); range_work].
Definition piece_work piece := match piece with
  | TextPiece bytes _ => enum_work [string_work bytes; range_work]
  | HolePiece _ _ => enum_work [identity_work; range_work]
  end.
(** Ten native fields, in declaration/hash order, including close_src AFTER
    the vectors. The five top-level Strings are not interchangeable with the
    bounds' declared source_bytes/body_bytes values. *)
Definition node_field_work node :=
  [ordvar_work (selector node); string_work (selector_name node);
   string_work (category node); string_work (open_src node);
   string_work (body_src node); vector_work hole_work (holes node);
   vector_work piece_work (pieces node); string_work (close_src node);
   bounds_work; scalar_work].
Definition node_work node := struct_work (node_field_work node).

Theorem flt_fixed_field_groups : range_work = 7 /\ bounds_work = 16.
Proof. split; reflexivity. Qed.
Theorem option_string_groups : forall bytes,
  optional_string_work None = 5 /\
  optional_string_work (Some bytes) = 6 + string_work bytes.
Proof. intro bytes. unfold optional_string_work, enum_work, field_sum.
  cbn [fold_right]. split; lia. Qed.
Theorem hole_native_groups : forall hole,
  hole_work hole = 16 + string_work (hole_name hole) +
    optional_string_work (hole_category hole).
Proof.
  intro hole. unfold hole_work, struct_work, field_sum.
  cbn [fold_right]. change identity_work with 4. change range_work with 7.
  lia.
Qed.
Theorem piece_native_groups : forall bytes identity range,
  piece_work (TextPiece bytes range) = 14 + string_work bytes /\
  piece_work (HolePiece identity range) = 18.
Proof.
  intros. unfold piece_work, enum_work, field_sum.
  cbn [fold_right]. change
    (5 + (1 + string_work bytes + (1 + 7 + 0)) = 14 + string_work bytes /\
     18 = 18). split; lia.
Qed.
Theorem node_native_groups : forall node,
  node_work node = 29 + ordvar_work (selector node) +
    string_work (selector_name node) + string_work (category node) +
    string_work (open_src node) + string_work (body_src node) +
    string_work (close_src node) + vector_work hole_work (holes node) +
    vector_work piece_work (pieces node).
Proof.
  intro node. unfold node_work, node_field_work, struct_work, field_sum.
  cbn [fold_right]. change bounds_work with 16. change scalar_work with 2.
  lia.
Qed.
Theorem arc_node_adds_only_borrowed_forwarding : forall node,
  arc_work (node_work node) = 2 + node_work node.
Proof. reflexivity. Qed.

(** Reuse the existing finite checked_sum and precharged_action. A successful
    item inspection supplies its exact mathematical work; None represents
    checked arithmetic failure. It is NOT silently substituted by zero. *)
Definition work_counts work : D.Counts := fun event => work * D.atom D.NativeWork event.
Theorem work_counts_projection : forall work,
  D.weighted D.base_work_weight (work_counts work) = work /\
  D.weighted D.record_weight (work_counts work) = 0 /\
  D.weighted D.byte_weight (work_counts work) = 0.
Proof.
  intro work. unfold work_counts. rewrite !V.weighted_scale.
  change (work * 1 = work /\ work * 0 = 0 /\ work * 0 = 0).
  repeat split; lia.
Qed.

Section MetadataFold.
Context {Item : Type}.
Variable item_work : Item -> nat.
Definition checked_item maximum accumulated item :=
  checked_sum maximum accumulated (item_work item).

(** Structural recursion describes the source iterator. In Rust the next
    action AND item projection occur only after the corresponding reservation;
    the proof's list constructor is not a speculative runtime next. The nil
    branch deliberately includes a paid terminal next, even for an empty Vec. *)
Fixpoint inspect_items maximum (items : list Item) available accumulated :=
  match items with
  | [] => precharged_action false available 1 0
      (fun _ => checked_sum maximum accumulated 0)
  | item :: rest =>
    match precharged_action false available 1 0
      (fun _ => checked_item maximum accumulated item) with
    | Refused remaining => Refused remaining
    | Accepted remaining next => inspect_items maximum rest remaining next
    end
  end.
Definition items_work := fold_right (fun item rest => item_work item + rest) 0.

Theorem successful_metadata_fold_is_exact : forall items maximum available accumulated paid total,
  inspect_items maximum items available accumulated = Accepted paid total ->
  total = accumulated + items_work items /\ total <= maximum /\
  work_left paid + S (length items) = work_left available /\
  units_left paid = units_left available.
Proof.
  induction items as [|item rest IH]; intros maximum available accumulated paid total HI.
  - cbn [inspect_items] in HI.
    apply successful_action_constructs_only_the_paid_result in HI.
    destruct HI as [_ [HS [HW HU]]].
    apply checked_sum_success_is_exact_and_bounded in HS.
    cbn [items_work fold_right length]. lia.
  - cbn [inspect_items] in HI.
    destruct (precharged_action false available 1 0
      (fun _ => checked_item maximum accumulated item)) as [remaining|remaining next]
      eqn:HP; [discriminate|].
    apply successful_action_constructs_only_the_paid_result in HP.
    destruct HP as [_ [HS [HW HU]]].
    unfold checked_item in HS. apply checked_sum_success_is_exact_and_bounded in HS.
    specialize (IH maximum remaining next paid total HI).
    cbn [items_work fold_right length]. lia.
Qed.

Theorem metadata_reservation_refusal_precedes_next : forall items maximum available accumulated,
  reserve available 1 0 = None ->
  inspect_items maximum items available accumulated = Refused available.
Proof.
  intros items maximum available accumulated HR. destruct items; cbn [inspect_items];
    rewrite (failed_precharge_is_independent_of_constructor _ _ _ _ _ HR); reflexivity.
Qed.
Theorem item_overflow_retains_paid_inspection : forall item rest maximum available accumulated paid,
  reserve available 1 0 = Some paid -> maximum < accumulated + item_work item ->
  inspect_items maximum (item :: rest) available accumulated = Refused paid.
Proof.
  intros item rest maximum available accumulated paid HR HO.
  cbn [inspect_items].
  assert (HC : checked_item maximum accumulated item = None).
  { unfold checked_item. now apply overflowing_sum_produces_no_index. }
  rewrite (callback_failure_does_not_refund _ _ _ _ _ _ HR HC). reflexivity.
Qed.
End MetadataFold.

(** The two vector headers contribute 14 to the fixed node coefficient 29.
    The forwarding parameter is 0 for FltNode, 2 for Arc<FltNode>. It is
    determined by the sealed Rust leaf type, not by untrusted source metadata. *)
Definition node_inspection_base forwarding node :=
  forwarding + 43 + ordvar_work (selector node) +
  string_work (selector_name node) + string_work (category node) +
  string_work (open_src node) + string_work (body_src node) +
  string_work (close_src node).
Definition hole_item_work hole := 2 + hole_work hole.
Definition piece_item_work piece := 2 + piece_work piece.
Theorem node_inspection_sum_is_native_work : forall forwarding node,
  node_inspection_base forwarding node + items_work hole_item_work (holes node) +
  items_work piece_item_work (pieces node) = forwarding + node_work node.
Proof.
  intros. rewrite node_native_groups.
  unfold node_inspection_base, items_work, vector_work, hole_item_work, piece_item_work.
  lia.
Qed.

Definition inspect_node maximum forwarding node available :=
  match precharged_action false available 1 0
    (fun _ => checked_sum maximum 0 (node_inspection_base forwarding node)) with
  | Refused remaining => Refused remaining
  | Accepted remaining accumulated =>
    match inspect_items hole_item_work maximum (holes node) remaining accumulated with
    | Refused remaining => Refused remaining
    | Accepted remaining accumulated =>
      inspect_items piece_item_work maximum (pieces node) remaining accumulated
    end
  end.

Theorem successful_node_inspection_is_exact :
  forall maximum forwarding node available paid work,
  inspect_node maximum forwarding node available = Accepted paid work ->
  work = forwarding + node_work node /\ work <= maximum /\
  work_left paid + (3 + length (holes node) + length (pieces node)) =
    work_left available /\ units_left paid = units_left available.
Proof.
  intros maximum forwarding node available paid work HI.
  unfold inspect_node in HI.
  destruct (precharged_action false available 1 0
    (fun _ => checked_sum maximum 0 (node_inspection_base forwarding node)))
    as [remaining|remaining accumulated] eqn:HR; [discriminate|].
  destruct (inspect_items hole_item_work maximum (holes node) remaining accumulated)
    as [after_holes|after_holes hole_total] eqn:HH; [discriminate|].
  apply successful_action_constructs_only_the_paid_result in HR.
  destruct HR as [_ [HB [HW HU]]].
  apply checked_sum_success_is_exact_and_bounded in HB.
  apply successful_metadata_fold_is_exact in HH, HI.
  pose proof (node_inspection_sum_is_native_work forwarding node) as HE.
  lia.
Qed.

(** Binder metadata is length-only. Its native Hash still visits EVERY binder,
    already covered by 7+10*n; pretty-name Strings are not scanned at all. *)
Definition inspect_binders maximum (binders : list Binder) available :=
  precharged_action false available 1 0
    (fun _ => checked_sum maximum 0 (7 + 10 * length binders)).
Theorem successful_binder_inspection_is_exact : forall maximum binders available paid work,
  inspect_binders maximum binders available = Accepted paid work ->
  work = binders_work binders /\ work <= maximum /\
  work_left paid + 1 = work_left available /\ units_left paid = units_left available.
Proof.
  intros maximum binders available paid work HI.
  unfold inspect_binders in HI.
  apply successful_action_constructs_only_the_paid_result in HI.
  destruct HI as [_ [HS [HW HU]]].
  apply checked_sum_success_is_exact_and_bounded in HS.
  rewrite binder_vector_native_groups. lia.
Qed.

(** Whole original native call after metadata succeeds. The source and hasher
    are transported unchanged; no field-by-field replacement hash is executed.
    The inspection function may compose fixed projections and several paid
    folds (holes then pieces). This law does not assume its numeric receipt is
    correct: that separate source-specific obligation is supplied above/by the
    concrete checked-arithmetic implementation and its correspondence tests. *)
Section WholeNativeExecution.
Context {Source State : Type}.
Variable native_hash : Source -> State -> State.
Variable inspect : Source -> Allowance -> ActionResult nat.
Definition execute_original source state available :=
  match inspect source available with
  | Refused remaining => Refused remaining
  | Accepted remaining work => precharged_action false remaining work 0
      (fun _ => Some (native_hash source state))
  end.
Theorem successful_execution_is_the_original_call : forall source state available paid output,
  execute_original source state available = Accepted paid output ->
  output = native_hash source state.
Proof.
  intros source state available paid output HE. unfold execute_original in HE.
  destruct (inspect source available); [discriminate|].
  apply successful_action_constructs_only_the_paid_result in HE.
  destruct HE as [_ [HE _]]. now inversion HE.
Qed.
Theorem metadata_refusal_prevents_whole_native_hash : forall source state available remaining,
  inspect source available = Refused remaining ->
  execute_original source state available = Refused remaining.
Proof.
  intros source state available remaining HI.
  unfold execute_original. now rewrite HI.
Qed.
Theorem execution_refusal_does_not_refund_metadata : forall source state available remaining work,
  inspect source available = Accepted remaining work ->
  reserve remaining work 0 = None ->
  execute_original source state available = Refused remaining.
Proof.
  intros source state available remaining work HI HR.
  unfold execute_original. rewrite HI.
  now apply failed_precharge_is_independent_of_constructor.
Qed.
End WholeNativeExecution.

Print Assumptions moniker_native_groups.
Print Assumptions ordvar_native_groups.
Print Assumptions moniker_pretty_names_are_not_hashed.
Print Assumptions binder_vector_native_groups.
Print Assumptions flt_fixed_field_groups.
Print Assumptions option_string_groups.
Print Assumptions hole_native_groups.
Print Assumptions piece_native_groups.
Print Assumptions node_native_groups.
Print Assumptions arc_node_adds_only_borrowed_forwarding.
Print Assumptions work_counts_projection.
Print Assumptions successful_metadata_fold_is_exact.
Print Assumptions metadata_reservation_refusal_precedes_next.
Print Assumptions item_overflow_retains_paid_inspection.
Print Assumptions node_inspection_sum_is_native_work.
Print Assumptions successful_node_inspection_is_exact.
Print Assumptions successful_binder_inspection_is_exact.
Print Assumptions successful_execution_is_the_original_call.
Print Assumptions metadata_refusal_prevents_whole_native_hash.
Print Assumptions execution_refusal_does_not_refund_metadata.
End AdmittedStructuralKeyHash.
