(** Exact structural size receipts for scalar/append/Fresh construction.

    Each axis is a separate natural-number measurement, not a native byte-size
    estimate or a gas grade. Equalities are pointwise, avoiding any functional
    extensionality axiom. Current outer Par metadata is measured separately by
    metadata_length; NestedMetadata counts inner New metadata and descendants'
    outer metadata. ImmediateNewRoots counts driven Par clone entry points when
    directly copying top-level New heads, not all descendant Par occurrences.

    This mathematical fold is a specification of the cached receipt. It does
    not prescribe another runtime subtree walk. Clone/drop control, transient
    buffers, map sorting and allocation allowances need separate owner proofs
    before this receipt can justify a production resource debit. *)
From Stdlib Require Import List String Arith Lia Sorting.Permutation.
From RhoBridge Require Import RholangTargetConstruction RholangFreshDescriptor
  RholangInitialGraphInterpretation RholangInitialGraphMachine RholangBoundMetadata.
From RhoBridge Require Import RholangCanonicalMetadata RholangInitialGraphResources.
Import ListNotations.

Inductive SizeAxis :=
| HeadEntries | TextPayloadBytes | UriEntries | UriPayloadBytes
| InjectionEntries | KeyPayloadBytes | NewEntries
| NestedMetadata | DescendantPars | ImmediateNewRoots.

Definition sum_sizes {A} (measure : A -> nat) (items : list A) : nat :=
  fold_right (fun item total => measure item + total) 0 items.

Lemma sum_sizes_with_base : forall A (measure : A -> nat) items base,
  fold_right (fun item total => measure item + total) base items = sum_sizes measure items + base.
Proof.
  intros A measure items. induction items; intro base; cbn [fold_right sum_sizes]; [lia|].
  rewrite IHitems. unfold sum_sizes. lia.
Qed.

Lemma sum_sizes_app : forall A (measure : A -> nat) left right,
  sum_sizes measure (left ++ right) = sum_sizes measure left + sum_sizes measure right.
Proof. intros. unfold sum_sizes at 1. rewrite fold_right_app. apply sum_sizes_with_base. Qed.

Lemma sum_sizes_map : forall A B (measure : B -> nat) (mapping : A -> B) items,
  sum_sizes measure (map mapping items) = sum_sizes (fun item => measure (mapping item)) items.
Proof.
  intros A B measure mapping items. induction items; cbn [sum_sizes map fold_right]; [reflexivity|].
  f_equal. exact IHitems.
Qed.

Lemma sum_sizes_extensional : forall A (left right : A -> nat) items,
  (forall item, In item items -> left item = right item) -> sum_sizes left items = sum_sizes right items.
Proof.
  intros A left right items. induction items as [|item rest IH]; intro H; [reflexivity|].
  cbn [sum_sizes fold_right]. rewrite H by (now left).
  change (right item + sum_sizes left rest = right item + sum_sizes right rest).
  rewrite IH by (intros; apply H; now right). reflexivity.
Qed.

Definition fresh_owned_count (axis : SizeAxis) (uris keys : list string)
    (arity shifted_bytes : nat) : nat :=
  match axis with
  | HeadEntries | NewEntries => 1
  | TextPayloadBytes | DescendantPars => 0
  | UriEntries => List.length uris
  | UriPayloadBytes => sum_sizes String.length uris
  | InjectionEntries => List.length keys
  | KeyPayloadBytes => sum_sizes String.length keys
  | NestedMetadata => shifted_bytes
  | ImmediateNewRoots => arity
  end.

Definition head_owned_count (axis : SizeAxis) (kind : HeadKind) (children : list Value) : nat :=
  match kind with
  | NewHead width uris keys =>
    let inner_metadata := match children with
      | [] => 0
      | body :: _ => List.length (free_bits (shifted_summary width (summary_of body)))
      end in
    fresh_owned_count axis uris keys (List.length children) inner_metadata
  | _ => match axis, kind with
    | HeadEntries, _ => 1
    | TextPayloadBytes, TextHead payload => String.length payload
    | _, _ => 0
    end
  end.

Definition embed_count (axis : SizeAxis) (outer_bytes owned_count : nat) : nat :=
  match axis with
  | NestedMetadata => outer_bytes + owned_count
  | DescendantPars => S owned_count
  | ImmediateNewRoots => 0
  | _ => owned_count
  end.

Fixpoint value_owned_count (axis : SizeAxis) (value : Value) : nat :=
  match value with
  | MakeValue heads _ => sum_sizes (head_deep_count axis) heads
  end
with head_deep_count (axis : SizeAxis) (head : Head) : nat :=
  match head with
  | MakeHead kind children =>
    head_owned_count axis kind children +
      sum_sizes (fun child => embed_count axis (metadata_length child) (value_owned_count axis child)) children
  end.

Theorem append_owned_receipt_is_additive : forall axis left right,
  value_owned_count axis (append left right) = value_owned_count axis left + value_owned_count axis right.
Proof. intros axis [left LS] [right RS]. apply sum_sizes_app. Qed.

Theorem fresh_owned_receipt_is_exact : forall axis descriptor body injections,
  value_owned_count axis (fresh_denotation descriptor body injections) =
  fresh_owned_count axis (shape_uris (descriptor_shape descriptor)) (descriptor_keys descriptor)
    (S (List.length injections))
    (List.length (free_bits (shifted_summary (shape_width (descriptor_shape descriptor)) (summary_of body)))) +
  sum_sizes (fun child => embed_count axis (metadata_length child) (value_owned_count axis child))
    (body :: injections).
Proof.
  intros. cbn [fresh_denotation singleton value_owned_count sum_sizes fold_right head_deep_count
    head_owned_count List.length]. lia.
Qed.

(** Unlike the standard generated induction principle, this rule supplies an
    induction fact for EVERY injection, including repeated occurrences. *)
Lemma construction_tree_deep_induction : forall (property : InitialTree -> Prop),
  (forall scalar, property (ScalarTree scalar)) ->
  (forall left right, property left -> property right -> property (AppendTree left right)) ->
  (forall descriptor body injections, property body -> Forall property injections ->
    property (FreshTree descriptor body injections)) ->
  forall tree, property tree.
Proof.
  intros property HS HA HF. fix IH 1. intro tree.
  destruct tree as [scalar|left right|descriptor body injections].
  - apply HS.
  - apply HA; apply IH.
  - apply HF; [apply IH|]. induction injections; constructor; [apply IH|assumption].
Qed.

Definition scalar_owned_count (axis : SizeAxis) (scalar : InitialScalar) : nat :=
  match axis, scalar with
  | HeadEntries, EmptyScalar => 0
  | HeadEntries, _ => 1
  | TextPayloadBytes, TextScalar payload => String.length payload
  | _, _ => 0
  end.

Fixpoint tree_owned_count (axis : SizeAxis) (tree : InitialTree) : nat :=
  match tree with
  | ScalarTree scalar => scalar_owned_count axis scalar
  | AppendTree lhs rhs => tree_owned_count axis lhs + tree_owned_count axis rhs
  | FreshTree descriptor body injections =>
    fresh_owned_count axis (shape_uris (descriptor_shape descriptor)) (descriptor_keys descriptor)
      (S (List.length injections)) (tree_metadata_length body - shape_width (descriptor_shape descriptor)) +
    sum_sizes (fun child => embed_count axis (tree_metadata_length child) (tree_owned_count axis child))
      (body :: injections)
  end.

Theorem cached_deep_receipt_is_exact : forall tree axis,
  tree_owned_count axis tree = value_owned_count axis (tree_denotation tree).
Proof.
  refine (construction_tree_deep_induction
    (fun tree => forall axis,
      tree_owned_count axis tree = value_owned_count axis (tree_denotation tree)) _ _ _).
  - intros scalar axis. destruct scalar, axis;
      cbn [tree_owned_count scalar_owned_count tree_denotation scalar_denotation
        empty boolean text wildcard singleton value_owned_count head_deep_count
        head_owned_count sum_sizes fold_right]; lia.
  - intros left right HL HR axis. cbn [tree_owned_count tree_denotation].
    rewrite append_owned_receipt_is_additive, HL, HR. reflexivity.
  - intros descriptor body injections HB HI axis. cbn [tree_owned_count tree_denotation].
    rewrite fresh_owned_receipt_is_exact, length_map.
    assert (Hshift :
      List.length (free_bits (shifted_summary (shape_width (descriptor_shape descriptor))
        (summary_of (tree_denotation body)))) =
      tree_metadata_length body - shape_width (descriptor_shape descriptor)).
    { cbn [shifted_summary free_bits].
      rewrite canonical_shift_has_exact_saturating_length
        by apply graph_denotation_has_canonical_outer_metadata.
      rewrite cached_metadata_length_is_exact. reflexivity. }
    rewrite Hshift. f_equal.
    rewrite <- map_cons, sum_sizes_map.
    apply sum_sizes_extensional. intros child HC.
    rewrite cached_metadata_length_is_exact.
    destruct HC as [HC|HC].
    + subst child. rewrite HB. reflexivity.
    + rewrite (proj1 (Forall_forall _ _) HI child HC). reflexivity.
Qed.

Theorem flat_owned_receipt_refines_existing_footprint : forall tree,
  flat_reference_tree tree = true ->
  tree_owned_count HeadEntries tree = entry_count (tree_footprint tree) /\
  tree_owned_count TextPayloadBytes tree = text_bytes (tree_footprint tree).
Proof.
  induction tree as [scalar|lhs HL rhs HR|descriptor body HB injections]; intro Hflat.
  - destruct scalar; split; reflexivity.
  - apply Bool.andb_true_iff in Hflat as [Hleft Hright].
    destruct (HL Hleft), (HR Hright).
    cbn [tree_owned_count tree_footprint plus entry_count text_bytes]. split; lia.
  - discriminate.
Qed.

(** This measures the three head-copy sequences performed by the pinned
    append constructor. It is not its retained output and does not include
    either outer metadata copies or clone/drop control workspaces. *)
Definition append_head_copy_count (axis : SizeAxis) (lhs rhs : Value) : nat :=
  sum_sizes (head_deep_count axis) (heads_of lhs ++ (heads_of lhs ++ heads_of rhs)).

Theorem append_head_copy_receipt_is_exact : forall axis lhs rhs,
  append_head_copy_count axis lhs rhs =
    2 * value_owned_count axis lhs + value_owned_count axis rhs.
Proof.
  intros axis [lhs LS] [rhs RS]. unfold append_head_copy_count.
  cbn [heads_of value_owned_count]. rewrite !sum_sizes_app. lia.
Qed.

Theorem append_head_copy_receipt_covers_retained_output : forall axis lhs rhs,
  value_owned_count axis (append lhs rhs) <= append_head_copy_count axis lhs rhs.
Proof.
  intros. rewrite append_owned_receipt_is_additive, append_head_copy_receipt_is_exact. lia.
Qed.

(** Fresh retains the shifted body metadata twice: once on the enclosing Par,
    once on New. Every body's/injection's outer metadata remains its own. *)
Theorem fresh_total_metadata_conserves_both_shifted_copies : forall descriptor body injections,
  metadata_length (fresh_denotation descriptor body injections) +
    value_owned_count NestedMetadata (fresh_denotation descriptor body injections) =
  2 * List.length (free_bits (shifted_summary (shape_width (descriptor_shape descriptor))
      (summary_of body))) +
    sum_sizes (fun child => metadata_length child + value_owned_count NestedMetadata child)
      (body :: injections).
Proof.
  intros. rewrite fresh_owned_receipt_is_exact.
  cbn [fresh_owned_count embed_count].
  unfold metadata_length at 1. cbn [fresh_denotation singleton summary_of]. lia.
Qed.

Example repeated_injection_occurrences_are_not_deduplicated :
  let tree := FreshTree wide_fresh_descriptor (ScalarTree (TextScalar "x"))
    (repeat (ScalarTree (TextScalar "x")) 5) in
  tree_owned_count HeadEntries tree = 7 /\
  tree_owned_count TextPayloadBytes tree = 6 /\
  tree_owned_count DescendantPars tree = 6 /\
  tree_owned_count ImmediateNewRoots tree = 6 /\
  tree_owned_count KeyPayloadBytes tree = 5.
Proof. repeat split; reflexivity. Qed.

Definition one_binder_descriptor : FreshDescriptor :=
  {| descriptor_shape := PlainShape 1; descriptor_keys := [] |}.
Definition nested_metadata_example : InitialTree :=
  FreshTree one_binder_descriptor
    (FreshTree one_binder_descriptor (ScalarTree (BoundScalar 3 2)) []) [].

Example nested_metadata_and_clone_entries_are_distinct :
  tree_metadata_length nested_metadata_example = 1 /\
  tree_owned_count NestedMetadata nested_metadata_example = 8 /\
  tree_owned_count DescendantPars nested_metadata_example = 2 /\
  tree_owned_count ImmediateNewRoots nested_metadata_example = 1 /\
  tree_owned_count NewEntries nested_metadata_example = 2.
Proof. repeat split; reflexivity. Qed.

Example appended_outer_metadata_does_not_change_inner_new_metadata :
  let tree := AppendTree
    (FreshTree one_binder_descriptor (ScalarTree (BoundScalar 3 2)) [])
    (ScalarTree (BoundScalar 10 9)) in
  metadata_length (tree_denotation tree) = 10 /\
  value_owned_count NestedMetadata (tree_denotation tree) = 5.
Proof. split; reflexivity. Qed.

Print Assumptions append_owned_receipt_is_additive.
Print Assumptions fresh_owned_receipt_is_exact.
Print Assumptions construction_tree_deep_induction.
Print Assumptions cached_deep_receipt_is_exact.
Print Assumptions flat_owned_receipt_refines_existing_footprint.
Print Assumptions append_head_copy_receipt_is_exact.
Print Assumptions append_head_copy_receipt_covers_retained_output.
Print Assumptions fresh_total_metadata_conserves_both_shifted_copies.
Print Assumptions repeated_injection_occurrences_are_not_deduplicated.
Print Assumptions nested_metadata_and_clone_entries_are_distinct.
Print Assumptions appended_outer_metadata_does_not_change_inner_new_metadata.

(** Mixed native heads retain fields which the semantic Value algebra erases.
    In particular, an ordinary EList and a DDL EList have different inner
    metadata policies even with identical children. Append cannot recover a
    head's inner metadata from the enclosing Par's joined summary. The proof
    annotation below records the constructor's actual retained local fields;
    erasure still yields the existing Value algebra. It is not another runtime
    representation, a traversal proposal, or a native allocation-size model.

    Source correspondence: models/src/main/protobuf/RhoTypes.proto and
    models/src/rust/utils.rs in the isolated node define EList/EMap/EMethod,
    Send/Receive/New inner metadata; EMethod owns methodName; New owns URI and
    injection-key strings; Receive owns ReceiveBind records; EMap owns
    KeyValuePair records. Optional list/map and bind remainder Vars are counted
    separately. Host-name payload bytes must come from the admitted name owner,
    not from HostNameSlot's abstract identifier. Other fixed-size fields are
    bounded by the head/child/record counts, not mistaken for variable bytes.

    This model specifies retained shape. Native helper clones, sorting,
    temporary vectors, constructor metadata passes and control stacks remain
    separately prepaid operations. Native EMap construction sorts and collapses
    duplicate keys: input receipts are upper bounds unless the producer carries
    the actual retained selection. The thinning law below does not assert that
    native sorting has already been verified against that selection. *)

Inductive NativeSizeAxis :=
| NativeHeads | NativePayloadBytes | NativeNameEntries | NativeMetadataBytes
| NativeDescendantPars | NativeReceiveBinds | NativeMapPairs | NativeRemainderVars.

Record NativeHeadFields := {
  native_kind : HeadKind;
  native_inner_metadata_bytes : nat;
  native_host_payload_bytes : nat;
  native_collection_remainder : bool
}.

(** These constructors keep a second copy of the output metadata on their
    native head. Unary/binary expressions and connective wrappers do not.
    Calling this at construction time, before any append, preserves the DDL
    closed-summary policy as well as the ordinary child-derived policy. *)
Definition native_fields (kind : HeadKind) (summary : Summary)
    (host_payload : nat) (collection_remainder : bool) : NativeHeadFields :=
  {| native_kind := kind;
     native_inner_metadata_bytes := match kind with
       | ListHead | MapHead | MethodHead _ | SendHead _ | NewHead _ _ _
       | ReceiveHead _ _ _ _ => List.length (free_bits summary)
       | _ => 0
       end;
     native_host_payload_bytes := match kind with HostNameHead _ => host_payload | _ => 0 end;
     native_collection_remainder := match kind with ListHead | MapHead => collection_remainder | _ => false end |}.

Definition remainder_count (present : bool) : nat := if present then 1 else 0.
Definition bind_remainder_count (bind : BindShape) : nat :=
  match remainder_index bind with None => 0 | Some _ => 1 end.

Definition native_local_count (axis : NativeSizeAxis) (fields : NativeHeadFields)
    (child_count : nat) : nat :=
  match axis with
  | NativeHeads => 1
  | NativePayloadBytes =>
    match native_kind fields with
    | TextHead payload | MethodHead payload => String.length payload
    | NewHead _ uris keys => sum_sizes String.length uris + sum_sizes String.length keys
    | HostNameHead _ => native_host_payload_bytes fields
    | _ => 0
    end
  | NativeNameEntries =>
    match native_kind fields with
    | NewHead _ uris keys => List.length uris + List.length keys
    | _ => 0
    end
  | NativeMetadataBytes => native_inner_metadata_bytes fields
  | NativeDescendantPars => 0
  | NativeReceiveBinds =>
    match native_kind fields with ReceiveHead binds _ _ _ => List.length binds | _ => 0 end
  | NativeMapPairs => match native_kind fields with MapHead => child_count / 2 | _ => 0 end
  | NativeRemainderVars =>
    match native_kind fields with
    | ListHead | MapHead => remainder_count (native_collection_remainder fields)
    | ReceiveHead binds _ _ _ => sum_sizes bind_remainder_count binds
    | _ => 0
    end
  end.

Inductive NativeValueImage :=
| NativeValue (heads : list NativeHeadImage) (summary : Summary)
with NativeHeadImage :=
| NativeHead (fields : NativeHeadFields) (children : list NativeValueImage).

Fixpoint erase_native_value (value : NativeValueImage) : Value :=
  match value with NativeValue heads summary => MakeValue (map erase_native_head heads) summary end
with erase_native_head (head : NativeHeadImage) : Head :=
  match head with NativeHead fields children =>
    MakeHead (native_kind fields) (map erase_native_value children)
  end.

Definition native_outer_bytes (value : NativeValueImage) : nat :=
  match value with NativeValue _ summary => List.length (free_bits summary) end.

Definition native_embed_count (axis : NativeSizeAxis) (outer owned : nat) : nat :=
  match axis with
  | NativeMetadataBytes => outer + owned
  | NativeDescendantPars => S owned
  | _ => owned
  end.

Fixpoint native_value_count (axis : NativeSizeAxis) (value : NativeValueImage) : nat :=
  match value with NativeValue heads _ => sum_sizes (native_head_count axis) heads end
with native_head_count (axis : NativeSizeAxis) (head : NativeHeadImage) : nat :=
  match head with NativeHead fields children =>
    native_local_count axis fields (List.length children) +
    sum_sizes (fun child => native_embed_count axis (native_outer_bytes child)
      (native_value_count axis child)) children
  end.

(** A Rust receipt is a finite record of these components, carried beside its
    owned Par. Functions here avoid choosing a Rust layout. Child receipts are
    supplied in the existing constructor order, including repeated occurrences.
    Arithmetic in Rust must reject overflow before allocation or publication. *)
Record NativeReceipt := {
  receipt_outer_bytes : nat;
  receipt_owned_count : NativeSizeAxis -> nat
}.
Definition native_receipt (value : NativeValueImage) : NativeReceipt :=
  {| receipt_outer_bytes := native_outer_bytes value;
     receipt_owned_count := fun axis => native_value_count axis value |}.
Definition receipt_children_count (axis : NativeSizeAxis) (children : list NativeReceipt) : nat :=
  sum_sizes (fun child => native_embed_count axis (receipt_outer_bytes child)
    (receipt_owned_count child axis)) children.
Definition construct_native_receipt (fields : NativeHeadFields) (outer : nat)
    (children : list NativeReceipt) : NativeReceipt :=
  {| receipt_outer_bytes := outer;
     receipt_owned_count := fun axis => native_local_count axis fields (List.length children) +
       receipt_children_count axis children |}.

Theorem native_constructor_receipt_is_exact : forall fields summary children axis,
  receipt_owned_count
    (construct_native_receipt fields (List.length (free_bits summary)) (map native_receipt children)) axis =
  native_value_count axis (NativeValue [NativeHead fields children] summary).
Proof.
  intros. cbn [construct_native_receipt receipt_owned_count native_value_count
    native_head_count sum_sizes fold_right].
  unfold receipt_children_count. rewrite length_map, sum_sizes_map.
  cbn [native_receipt receipt_outer_bytes receipt_owned_count]. lia.
Qed.

Theorem native_constructor_erasure_keeps_ordered_children : forall fields summary children,
  erase_native_value (NativeValue [NativeHead fields children] summary) =
  singleton (native_kind fields) (map erase_native_value children) summary.
Proof. reflexivity. Qed.

Definition native_append (left right : NativeValueImage) : NativeValueImage :=
  match left, right with NativeValue lhs ls, NativeValue rhs rs =>
    NativeValue (lhs ++ rhs) (join_summary ls rs)
  end.
Definition append_native_receipt (left right : NativeReceipt) : NativeReceipt :=
  {| receipt_outer_bytes := Nat.max (receipt_outer_bytes left) (receipt_outer_bytes right);
     receipt_owned_count := fun axis => receipt_owned_count left axis + receipt_owned_count right axis |}.

Theorem native_append_erases_to_existing_append : forall left right,
  erase_native_value (native_append left right) = append (erase_native_value left) (erase_native_value right).
Proof. intros [lh ls] [rh rs]. cbn [native_append erase_native_value append]. now rewrite map_app. Qed.

Theorem native_append_receipt_is_additive : forall axis left right,
  native_value_count axis (native_append left right) = native_value_count axis left + native_value_count axis right.
Proof. intros axis [lh ls] [rh rs]. apply sum_sizes_app. Qed.

Theorem native_append_receipt_preserves_outer_maximum : forall left right,
  native_outer_bytes (native_append left right) = Nat.max (native_outer_bytes left) (native_outer_bytes right).
Proof.
  intros [lh [lb lc]] [rh [rb rc]]. cbn [native_append native_outer_bytes join_summary free_bits].
  apply union_metadata_length_is_maximum.
Qed.

Definition native_append_copy_count (axis : NativeSizeAxis) (left right : NativeValueImage) : nat :=
  match left, right with NativeValue lhs _, NativeValue rhs _ =>
    sum_sizes (native_head_count axis) (lhs ++ lhs ++ rhs)
  end.
Theorem native_append_copies_twice_left_once_right : forall axis left right,
  native_append_copy_count axis left right = 2 * native_value_count axis left + native_value_count axis right.
Proof.
  intros axis [lh ls] [rh rs]. cbn [native_append_copy_count native_value_count].
  rewrite !sum_sizes_app. lia.
Qed.

Theorem native_append_accepts_conservative_child_receipts : forall axis left right left_bound right_bound,
  native_value_count axis left <= left_bound -> native_value_count axis right <= right_bound ->
  native_value_count axis (native_append left right) <= left_bound + right_bound /\
  native_append_copy_count axis left right <= 2 * left_bound + right_bound.
Proof.
  intros. rewrite native_append_receipt_is_additive, native_append_copies_twice_left_once_right. lia.
Qed.

Theorem native_embedded_child_keeps_outer_metadata : forall fields summary children,
  native_value_count NativeMetadataBytes (NativeValue [NativeHead fields children] summary) =
  native_inner_metadata_bytes fields + sum_sizes
    (fun child => native_outer_bytes child + native_value_count NativeMetadataBytes child) children.
Proof. intros. cbn [native_value_count native_head_count native_local_count native_embed_count sum_sizes fold_right]. lia. Qed.

Theorem native_child_occurrences_are_exact : forall fields summary children,
  native_value_count NativeDescendantPars (NativeValue [NativeHead fields children] summary) =
  sum_sizes (fun child => S (native_value_count NativeDescendantPars child)) children.
Proof. intros. cbn [native_value_count native_head_count native_local_count native_embed_count sum_sizes fold_right]. lia. Qed.

Theorem native_new_local_metadata_preserves_existing_fresh_policy : forall width uris keys summary arity,
  native_local_count NativeMetadataBytes (native_fields (NewHead width uris keys) summary 0 false) arity =
  fresh_owned_count NestedMetadata uris keys arity (List.length (free_bits summary)).
Proof. reflexivity. Qed.

Theorem native_new_local_payload_keeps_all_uri_and_key_bytes : forall width uris keys summary arity,
  native_local_count NativePayloadBytes (native_fields (NewHead width uris keys) summary 0 false) arity =
  fresh_owned_count UriPayloadBytes uris keys arity (List.length (free_bits summary)) +
  fresh_owned_count KeyPayloadBytes uris keys arity (List.length (free_bits summary)).
Proof. reflexivity. Qed.

Theorem native_map_pair_records_match_complete_pairs : forall count summary,
  native_local_count NativeMapPairs (native_fields MapHead summary 0 false) (2 * count) = count.
Proof. intros. cbn [native_local_count native_fields native_kind]. rewrite Nat.mul_comm. apply Nat.div_mul. discriminate. Qed.

Inductive ReceiptSelection {A : Type} : list A -> list A -> Prop :=
| SelectNil : ReceiptSelection [] []
| SelectKeep : forall item retained input, ReceiptSelection retained input ->
    ReceiptSelection (item :: retained) (item :: input)
| SelectDrop : forall item retained input, ReceiptSelection retained input ->
    ReceiptSelection retained (item :: input).

Theorem selected_receipts_do_not_increase_counts : forall A (measure : A -> nat) retained input,
  ReceiptSelection retained input -> sum_sizes measure retained <= sum_sizes measure input.
Proof.
  intros A measure retained input selected.
  induction selected as [|item retained input selection IH|item retained input selection IH].
  - apply Nat.le_refl.
  - change (measure item + sum_sizes measure retained <= measure item + sum_sizes measure input).
    now apply Nat.add_le_mono_l.
  - change (sum_sizes measure retained <= measure item + sum_sizes measure input).
    eapply Nat.le_trans; [exact IH|apply Nat.le_add_l].
Qed.

Theorem reordered_receipts_preserve_counts : forall A (measure : A -> nat) left right,
  Permutation left right -> sum_sizes measure left = sum_sizes measure right.
Proof.
  intros A measure left right order.
  induction order as [|item left right order IH|first second rest|left middle right one IHone two IHtwo].
  - reflexivity.
  - change (measure item + sum_sizes measure left = measure item + sum_sizes measure right).
    now rewrite IH.
  - change (measure second + (measure first + sum_sizes measure rest) =
      measure first + (measure second + sum_sizes measure rest)). lia.
  - now rewrite IHone, IHtwo.
Qed.

Theorem reordered_selected_receipts_are_bounded : forall A (measure : A -> nat) output retained input,
  ReceiptSelection retained input -> Permutation output retained ->
  sum_sizes measure output <= sum_sizes measure input.
Proof.
  intros A measure output retained input selection order.
  rewrite (reordered_receipts_preserve_counts A measure output retained order).
  now apply selected_receipts_do_not_increase_counts.
Qed.

Definition example_child : NativeValueImage := NativeValue [] (bound_summary 2).
Definition ordinary_list_fields : NativeHeadFields :=
  native_fields ListHead (bound_summary 2) 0 false.
Definition ddl_list_fields : NativeHeadFields :=
  native_fields ListHead closed_summary 0 false.

Example ddl_and_ordinary_inner_metadata_remain_distinct_after_append :
  let ordinary := NativeValue [NativeHead ordinary_list_fields [example_child]] (bound_summary 2) in
  let ddl := NativeValue [NativeHead ddl_list_fields [example_child]] closed_summary in
  native_value_count NativeMetadataBytes ordinary = 6 /\
  native_value_count NativeMetadataBytes ddl = 3 /\
  native_value_count NativeMetadataBytes (native_append ordinary ddl) = 9 /\
  native_outer_bytes (native_append ordinary ddl) = 3.
Proof. repeat split; reflexivity. Qed.

Example method_payload_and_repeated_child_occurrences_are_retained :
  let fields := native_fields (MethodHead "get") (bound_summary 2) 0 false in
  let value := NativeValue [NativeHead fields [example_child; example_child]] (bound_summary 2) in
  native_value_count NativePayloadBytes value = 3 /\
  native_value_count NativeDescendantPars value = 2 /\
  native_value_count NativeMetadataBytes value = 9.
Proof. repeat split; reflexivity. Qed.

Example receive_counts_bind_records_without_counting_lexical_slot_names :
  let binds := [{| pattern_count := 2; free_count := 1; remainder_index := Some 0 |};
                {| pattern_count := 1; free_count := 1; remainder_index := None |}] in
  let fields := native_fields (ReceiveHead binds [GuestSlot "not a native payload"] false true)
    (bound_summary 2) 0 false in
  native_local_count NativeReceiveBinds fields 7 = 2 /\
  native_local_count NativeRemainderVars fields 7 = 1 /\
  native_local_count NativePayloadBytes fields 7 = 0 /\
  native_local_count NativeMetadataBytes fields 7 = 3.
Proof. repeat split; reflexivity. Qed.

Print Assumptions native_constructor_receipt_is_exact.
Print Assumptions native_constructor_erasure_keeps_ordered_children.
Print Assumptions native_append_erases_to_existing_append.
Print Assumptions native_append_receipt_is_additive.
Print Assumptions native_append_receipt_preserves_outer_maximum.
Print Assumptions native_append_copies_twice_left_once_right.
Print Assumptions native_append_accepts_conservative_child_receipts.
Print Assumptions native_embedded_child_keeps_outer_metadata.
Print Assumptions native_child_occurrences_are_exact.
Print Assumptions native_new_local_metadata_preserves_existing_fresh_policy.
Print Assumptions native_new_local_payload_keeps_all_uri_and_key_bytes.
Print Assumptions native_map_pair_records_match_complete_pairs.
Print Assumptions selected_receipts_do_not_increase_counts.
Print Assumptions reordered_receipts_preserve_counts.
Print Assumptions reordered_selected_receipts_are_bounded.
Print Assumptions ddl_and_ordinary_inner_metadata_remain_distinct_after_append.
Print Assumptions method_payload_and_repeated_child_occurrences_are_retained.
Print Assumptions receive_counts_bind_records_without_counting_lexical_slot_names.
