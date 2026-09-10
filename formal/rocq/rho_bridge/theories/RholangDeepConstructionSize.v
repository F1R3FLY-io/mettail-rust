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
From Stdlib Require Import List String Arith Lia.
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
