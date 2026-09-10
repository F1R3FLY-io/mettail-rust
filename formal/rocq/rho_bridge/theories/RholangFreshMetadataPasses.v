(** Fresh metadata's concrete logical pass schedule.

    Source owners: filter_and_adjust_bitset and bitvec_from_indices in
    rholang-runtime/src/rholang_ast.rs, DirectNodeTarget::fresh, and the pinned
    node's new_new_par/Par::with_news. The source scans every input byte, collects
    surviving indices, finds their maximum, initializes the shifted bytes,
    sets the surviving positions, clones the New metadata, clones the outer
    receiver metadata, and finally compares the constructed observation.

    Byte operations reuse MetadataPass. Index entries use the existing four
    logical units per entry convention. These are logical work/payload-volume
    bounds, not physical Vec capacity, allocator growth, RSS or semantic gas.
    Pool/control allocation, map construction and failure cleanup are separate
    obligations. Exact input bytes must satisfy the admitted Boolean metadata
    image; canonicality is required when the receipt supplies output length.
    The mathematical survivor count does not require a new runtime scan: its
    bound by the cached shifted length permits precharge before the helper. *)
From Stdlib Require Import List Arith Lia Bool.
From RhoBridge Require Import RholangTargetConstruction RholangCanonicalMetadata
  RholangBoundMetadata RholangInitialGraphResources.
Import ListNotations.

Fixpoint surviving_scan_count (width : nat) (bits : list bool) : nat :=
  match bits with
  | [] => 0
  | bit :: rest => match width with
    | S remaining => surviving_scan_count remaining rest
    | 0 => (if bit then 1 else 0) + surviving_scan_count 0 rest
    end
  end.

Theorem concrete_survivor_count_matches_existing_bit_count : forall bits width,
  surviving_scan_count width bits = set_bit_count (skipn width bits).
Proof.
  induction bits as [|bit rest IH]; intro width; destruct width;
    cbn [surviving_scan_count skipn set_bit_count]; auto.
Qed.

Theorem survivor_count_is_bounded_before_scanning : forall bits width,
  surviving_scan_count width bits <= List.length bits - width.
Proof.
  intros. rewrite concrete_survivor_count_matches_existing_bit_count.
  apply surviving_index_count_fits_shifted_allowance.
Qed.

Inductive FreshMetadataPass :=
| BytePass (pass : MetadataPass)
| CollectIndexEntries (entries : nat)
| ReadIndexEntries (entries : nat)
(** One logical indexed assignment includes reading its index and setting the
    existing metadata byte; it is not a count of primitive machine accesses. *)
| SetIndexedBits (entries : nat).

Definition fresh_pass_work (pass : FreshMetadataPass) : nat :=
  match pass with
  | BytePass bytes => pass_work bytes
  | CollectIndexEntries n | ReadIndexEntries n | SetIndexedBits n => n
  end.
Definition fresh_pass_units (pass : FreshMetadataPass) : nat :=
  match pass with
  | BytePass bytes => pass_units bytes
  | CollectIndexEntries n => 4 * n
  | ReadIndexEntries _ | SetIndexedBits _ => 0
  end.
Definition fresh_passes_work (passes : list FreshMetadataPass) : nat :=
  fold_right (fun pass total => fresh_pass_work pass + total) 0 passes.
Definition fresh_passes_units (passes : list FreshMetadataPass) : nat :=
  fold_right (fun pass total => fresh_pass_units pass + total) 0 passes.

Definition fresh_metadata_passes (input_bytes survivors shifted_bytes : nat) :=
  [BytePass (CompareExisting input_bytes);
   CollectIndexEntries survivors;
   ReadIndexEntries survivors;
   BytePass (AllocateInitialized shifted_bytes);
   SetIndexedBits survivors;
   BytePass (CopyAllocated shifted_bytes);
   BytePass (CopyAllocated shifted_bytes);
   BytePass (CompareExisting shifted_bytes)].

Theorem fresh_metadata_schedule_has_exact_logical_charge : forall input survivors shifted,
  fresh_passes_work (fresh_metadata_passes input survivors shifted) =
    input + 3 * survivors + 4 * shifted /\
  fresh_passes_units (fresh_metadata_passes input survivors shifted) =
    4 * survivors + 3 * shifted.
Proof.
  intros. unfold fresh_metadata_passes, fresh_passes_work, fresh_passes_units.
  cbn [fold_right fresh_pass_work fresh_pass_units pass_work pass_units]. split; lia.
Qed.

Theorem canonical_fresh_metadata_precharge_covers_actual_passes : forall bits width,
  canonical_bits bits = true ->
  let input := List.length bits in
  let shifted := input - width in
  let actual := fresh_metadata_passes input (surviving_scan_count width bits)
    (List.length (shift_bits width bits)) in
  fresh_passes_work actual <= input + 7 * shifted /\
  fresh_passes_units actual <= 7 * shifted.
Proof.
  intros bits width HC. cbn zeta.
  rewrite canonical_shift_has_exact_saturating_length by exact HC.
  destruct (fresh_metadata_schedule_has_exact_logical_charge
    (List.length bits) (surviving_scan_count width bits) (List.length bits - width)) as [HW HU].
  rewrite HW, HU.
  pose proof (survivor_count_is_bounded_before_scanning bits width). split; lia.
Qed.

Definition reserve_fresh_metadata available payload input shifted :=
  reserve available (payload_work payload + input + 7 * shifted)
    (payload_units payload + 7 * shifted).

Theorem fresh_metadata_reservation_is_atomic_and_exact : forall available payload input shifted next,
  reserve_fresh_metadata available payload input shifted = Some next ->
  work_left next + payload_work payload + input + 7 * shifted = work_left available /\
  units_left next + payload_units payload + 7 * shifted = units_left available.
Proof.
  intros. apply successful_reservation_is_exact in H. lia.
Qed.

Example sparse_metadata_precharge_does_not_assume_every_bit_is_set :
  surviving_scan_count 1 [true; false; false; true] = 1 /\
  List.length (shift_bits 1 [true; false; false; true]) = 3 /\
  fresh_passes_work (fresh_metadata_passes 4 1 3) = 19 /\
  fresh_passes_units (fresh_metadata_passes 4 1 3) = 13.
Proof. repeat split; reflexivity. Qed.

Example entirely_bound_metadata_still_requires_the_input_scan :
  fresh_passes_work (fresh_metadata_passes 4 0 0) = 4 /\
  fresh_passes_units (fresh_metadata_passes 4 0 0) = 0.
Proof. split; reflexivity. Qed.

Print Assumptions concrete_survivor_count_matches_existing_bit_count.
Print Assumptions survivor_count_is_bounded_before_scanning.
Print Assumptions fresh_metadata_schedule_has_exact_logical_charge.
Print Assumptions canonical_fresh_metadata_precharge_covers_actual_passes.
Print Assumptions fresh_metadata_reservation_is_atomic_and_exact.
Print Assumptions sparse_metadata_precharge_does_not_assume_every_bit_is_set.
Print Assumptions entirely_bound_metadata_still_requires_the_input_scan.
