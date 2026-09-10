(** Exact outer-metadata sizes and explicit pass debits for flat construction.

    Each Boolean in free_bits denotes one node byte (0 or 1), not a packed
    bit. Bound construction initializes i+1 bytes and with_exprs clones them.
    Append clones left metadata, takes right, then union initializes and fills
    max(left,right) bytes. The final observation comparison scans at most the
    output length. These are declared logical byte passes, not CPU cycles,
    allocator RSS, encoded protobuf size, or a whole-program resource bound.

    Expression/text copy charges remain RholangInitialGraphResources' existing
    charges. Metadata passes are additional and must be combined into the same
    atomic reservation BEFORE node helpers run. The graph scheduling/capacity
    proof remains the same: Bound and Wildcard are nullary leaves. *)
From Stdlib Require Import List Arith Lia Bool.
From RhoBridge Require Import RholangTargetConstruction RholangInitialGraphInterpretation
  RholangInitialGraphMachine RholangInitialGraphResources.
Import ListNotations.

Definition metadata_length (value : Value) : nat :=
  List.length (free_bits (summary_of value)).

Theorem union_metadata_length_is_maximum : forall lhs rhs,
  List.length (union_bits lhs rhs) = Nat.max (List.length lhs) (List.length rhs).
Proof.
  induction lhs as [|a lhs IH]; intros [|b rhs]; cbn; try lia.
  now rewrite IH.
Qed.
Theorem singleton_bound_metadata_has_one_byte_per_index : forall scope index,
  metadata_length (scalar_denotation (BoundScalar scope index)) = S index.
Proof.
  intros. unfold metadata_length, scalar_denotation, singleton, bound_summary.
  cbn [summary_of free_bits]. rewrite length_app, repeat_length. cbn; lia.
Qed.
Theorem append_metadata_is_not_additive : forall lhs rhs,
  metadata_length (append lhs rhs) = Nat.max (metadata_length lhs) (metadata_length rhs).
Proof. intros; unfold metadata_length, append; cbn. apply union_metadata_length_is_maximum. Qed.

Definition scalar_metadata_length (scalar : InitialScalar) : nat :=
  match scalar with BoundScalar _ index => S index | _ => 0 end.
Fixpoint tree_metadata_length (tree : InitialTree) : nat :=
  match tree with
  | ScalarTree scalar => scalar_metadata_length scalar
  | AppendTree lhs rhs => Nat.max (tree_metadata_length lhs) (tree_metadata_length rhs)
  end.
Theorem cached_metadata_length_is_exact : forall tree,
  tree_metadata_length tree = metadata_length (tree_denotation tree).
Proof.
  induction tree as [scalar|lhs HL rhs HR]; cbn [tree_metadata_length tree_denotation].
  - destruct scalar; try reflexivity. symmetry. apply singleton_bound_metadata_has_one_byte_per_index.
  - now rewrite append_metadata_is_not_additive, HL, HR.
Qed.

Inductive MetadataPass :=
| AllocateInitialized (bytes : nat)
| CopyAllocated (bytes : nat)
| FillExisting (bytes : nat)
| CompareExisting (bytes : nat).
Definition pass_work (pass : MetadataPass) : nat :=
  match pass with
  | AllocateInitialized n | CopyAllocated n | FillExisting n | CompareExisting n => n
  end.
Definition pass_units (pass : MetadataPass) : nat :=
  match pass with AllocateInitialized n | CopyAllocated n => n | _ => 0 end.
Definition passes_work (passes : list MetadataPass) := fold_right (fun p n => pass_work p + n) 0 passes.
Definition passes_units (passes : list MetadataPass) := fold_right (fun p n => pass_units p + n) 0 passes.
Definition bound_passes (index : nat) :=
  [AllocateInitialized (S index); CopyAllocated (S index); CompareExisting (S index)].
Definition append_passes (left_bytes right_bytes : nat) :=
  let result_bytes := Nat.max left_bytes right_bytes in
  [CopyAllocated left_bytes; AllocateInitialized result_bytes;
   FillExisting result_bytes; CompareExisting result_bytes].

Theorem bound_pass_debits_cover_both_allocations_and_comparison : forall index,
  passes_work (bound_passes index) = 3 * S index /\
  passes_units (bound_passes index) = 2 * S index.
Proof. intros; unfold bound_passes, passes_work, passes_units; cbn; lia. Qed.
Theorem append_pass_debits_cover_copy_initialization_fill_and_comparison : forall lhs rhs,
  passes_work (append_passes lhs rhs) = lhs + 3 * Nat.max lhs rhs /\
  passes_units (append_passes lhs rhs) = lhs + Nat.max lhs rhs.
Proof. intros; unfold append_passes, passes_work, passes_units; cbn; lia. Qed.

Definition reserve_with_metadata available payload passes :=
  reserve available (payload_work payload + passes_work passes)
    (payload_units payload + passes_units passes).
Theorem combined_payload_and_metadata_reservation_is_exact : forall available payload passes next,
  reserve_with_metadata available payload passes = Some next ->
  work_left next + payload_work payload + passes_work passes = work_left available /\
  units_left next + payload_units payload + passes_units passes = units_left available.
Proof. intros; apply successful_reservation_is_exact in H; lia. Qed.
Theorem combined_reservation_requires_both_complete_dimensions : forall available payload passes,
  (exists next, reserve_with_metadata available payload passes = Some next) <->
  payload_work payload + passes_work passes <= work_left available /\
  payload_units payload + passes_units passes <= units_left available.
Proof. intros; apply reservation_succeeds_exactly_when_both_dimensions_fit. Qed.

Example reused_bound_metadata_does_not_double_the_retained_length : forall scope index,
  let value := scalar_denotation (BoundScalar scope index) in
  metadata_length (append value value) = S index.
Proof.
  intros scope index.
  change (metadata_length (append (scalar_denotation (BoundScalar scope index))
    (scalar_denotation (BoundScalar scope index))) = S index).
  rewrite append_metadata_is_not_additive, singleton_bound_metadata_has_one_byte_per_index.
  apply Nat.max_id.
Qed.

Print Assumptions union_metadata_length_is_maximum.
Print Assumptions singleton_bound_metadata_has_one_byte_per_index.
Print Assumptions append_metadata_is_not_additive.
Print Assumptions cached_metadata_length_is_exact.
Print Assumptions bound_pass_debits_cover_both_allocations_and_comparison.
Print Assumptions append_pass_debits_cover_copy_initialization_fill_and_comparison.
Print Assumptions combined_payload_and_metadata_reservation_is_exact.
Print Assumptions combined_reservation_requires_both_complete_dimensions.
Print Assumptions reused_bound_metadata_does_not_double_the_retained_length.
