(** Exact native counts-table geometry through the existing Layout interface.
    On the pinned 64-bit profile, a (T, usize) tuple has power-of-two alignment
    at least eight and positive size divisible by that alignment. Allocated
    bucket counts are powers of two at least four. These parameters describe
    those type/layout facts, not a second allocator or table implementation.

    raw.rs:216 rounds data bytes to max(tuple alignment,16), then adds B+16
    control bytes. core/alloc/layout.rs:500 Layout::extend rounds its first
    size to the NEXT layout's alignment and returns an UNPADDED combined size.
    Using Layout::array<(T,usize)>(B) and a control layout of size B+16 and
    alignment16 gives the same offset, size and alignment, as shown below.
    The rounded-offset formula is the natural-number meaning of these native
    power-of-two alignment operations, not a proof of compiler bit lowering.

    Accepted geometry bounds native arithmetic BEFORE insertion. It does not
    pay for key Hash/Eq, table scans, allocation work or physical RSS. Local
    probe arithmetic retains its reached-stride premise: this file does not
    establish that a whole lookup stops before exhausting its probe sequence. *)
From Stdlib Require Import Arith.PeanoNat Lia.

Module NativeHashBagLayout.

Definition tuple_alignment exponent := 2 ^ (exponent + 3).
Definition tuple_size exponent words := tuple_alignment exponent * S words.
Definition allocated_buckets exponent := 2 ^ (exponent + 2).
Definition control_alignment exponent := Nat.max (tuple_alignment exponent) 16.
Definition data_bytes alignment_exponent words bucket_exponent :=
  tuple_size alignment_exponent words * allocated_buckets bucket_exponent.
Definition round_up bytes alignment := (bytes + alignment - 1) / alignment * alignment.

Lemma type_geometry_has_positive_minimums : forall alignment_exponent words bucket_exponent,
  8 <= tuple_alignment alignment_exponent /\
  8 <= tuple_size alignment_exponent words /\
  4 <= allocated_buckets bucket_exponent /\
  16 <= control_alignment alignment_exponent.
Proof.
  intros alignment_exponent words bucket_exponent.
  pose proof (Nat.pow_nonzero 2 alignment_exponent ltac:(lia)) as ALIGN.
  pose proof (Nat.pow_nonzero 2 bucket_exponent ltac:(lia)) as BUCKETS.
  unfold tuple_size, tuple_alignment, allocated_buckets, control_alignment.
  rewrite !Nat.pow_add_r. cbn [Nat.pow]. repeat split; nia.
Qed.

Lemma data_bytes_are_control_aligned : forall alignment_exponent words bucket_exponent,
  exists multiple, data_bytes alignment_exponent words bucket_exponent =
    control_alignment alignment_exponent * multiple.
Proof.
  intros [|alignment_exponent] words bucket_exponent.
  - exists (2 * S words * 2 ^ bucket_exponent).
    unfold data_bytes, tuple_size, control_alignment, tuple_alignment, allocated_buckets.
    rewrite !Nat.pow_add_r. cbn [Nat.pow Nat.max]. nia.
  - exists (S words * allocated_buckets bucket_exponent).
    assert (LARGE : 16 <= tuple_alignment (S alignment_exponent)).
    { unfold tuple_alignment. replace (S alignment_exponent + 3)
        with (alignment_exponent + 4) by lia.
      rewrite Nat.pow_add_r. cbn [Nat.pow].
      pose proof (Nat.pow_nonzero 2 alignment_exponent ltac:(lia)). nia. }
    unfold control_alignment. rewrite Nat.max_l by exact LARGE.
    unfold data_bytes, tuple_size. nia.
Qed.

Lemma data_bytes_are_group_aligned : forall alignment_exponent words bucket_exponent,
  exists multiple, data_bytes alignment_exponent words bucket_exponent = 16 * multiple.
Proof.
  intros alignment_exponent words bucket_exponent.
  exists (2 * 2 ^ alignment_exponent * S words * 2 ^ bucket_exponent).
  unfold data_bytes, tuple_size, tuple_alignment, allocated_buckets.
  rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

Lemma rounding_an_aligned_size_is_identity : forall alignment multiple,
  0 < alignment -> round_up (alignment * multiple) alignment = alignment * multiple.
Proof.
  intros alignment multiple POSITIVE. unfold round_up.
  assert (QUOTIENT : (alignment * multiple + alignment - 1) / alignment = multiple).
  { symmetry. apply Nat.div_unique with (r := alignment - 1); nia. }
  rewrite QUOTIENT. nia.
Qed.

Theorem standard_extend_and_native_offsets_are_identical :
  forall alignment_exponent words bucket_exponent,
  round_up (data_bytes alignment_exponent words bucket_exponent)
    (control_alignment alignment_exponent) =
      data_bytes alignment_exponent words bucket_exponent /\
  round_up (data_bytes alignment_exponent words bucket_exponent) 16 =
      data_bytes alignment_exponent words bucket_exponent.
Proof.
  intros alignment_exponent words bucket_exponent.
  destruct (type_geometry_has_positive_minimums alignment_exponent words bucket_exponent)
    as [ALIGN [SIZE [BUCKETS CONTROL]]]. split.
  - destruct (data_bytes_are_control_aligned alignment_exponent words bucket_exponent)
      as [multiple BYTES]. rewrite BYTES.
    apply rounding_an_aligned_size_is_identity. lia.
  - destruct (data_bytes_are_group_aligned alignment_exponent words bucket_exponent)
      as [multiple BYTES]. rewrite BYTES.
    apply rounding_an_aligned_size_is_identity. lia.
Qed.

Definition allocation_bytes alignment_exponent words bucket_exponent :=
  data_bytes alignment_exponent words bucket_exponent +
    allocated_buckets bucket_exponent + 16.
Definition accepted_layout signed_limit alignment_exponent words bucket_exponent :=
  allocation_bytes alignment_exponent words bucket_exponent +
    (control_alignment alignment_exponent - 1) <= signed_limit.

Theorem accepted_layout_has_the_native_size_ceiling :
  forall signed_limit alignment_exponent words bucket_exponent,
  accepted_layout signed_limit alignment_exponent words bucket_exponent <->
  control_alignment alignment_exponent <= S signed_limit /\
  allocation_bytes alignment_exponent words bucket_exponent <=
    S signed_limit - control_alignment alignment_exponent.
Proof.
  intros signed_limit alignment_exponent words bucket_exponent.
  destruct (type_geometry_has_positive_minimums alignment_exponent words bucket_exponent)
    as [ALIGN [SIZE [BUCKETS CONTROL]]].
  unfold accepted_layout. lia.
Qed.

(** The two input Layout constructors must accept too: using extend must not
    introduce an extra rejection for otherwise valid native geometry. *)
Theorem accepted_layout_validates_both_standard_components :
  forall signed_limit alignment_exponent words bucket_exponent,
  accepted_layout signed_limit alignment_exponent words bucket_exponent ->
  data_bytes alignment_exponent words bucket_exponent +
    (tuple_alignment alignment_exponent - 1) <= signed_limit /\
  allocated_buckets bucket_exponent + 16 + 15 <= signed_limit.
Proof.
  intros signed_limit alignment_exponent words bucket_exponent ACCEPTED.
  destruct (type_geometry_has_positive_minimums alignment_exponent words bucket_exponent)
    as [ALIGN [SIZE [BUCKETS CONTROL]]].
  assert (ALIGNMENT : tuple_alignment alignment_exponent <=
    control_alignment alignment_exponent).
  { unfold control_alignment. apply Nat.le_max_l. }
  unfold accepted_layout, allocation_bytes in ACCEPTED. split; lia.
Qed.

Theorem accepted_layout_covers_native_intermediate_arithmetic :
  forall signed_limit alignment_exponent words bucket_exponent,
  accepted_layout signed_limit alignment_exponent words bucket_exponent ->
  data_bytes alignment_exponent words bucket_exponent <= signed_limit /\
  data_bytes alignment_exponent words bucket_exponent +
    (control_alignment alignment_exponent - 1) <= signed_limit /\
  allocated_buckets bucket_exponent + 16 <= signed_limit /\
  allocation_bytes alignment_exponent words bucket_exponent <= signed_limit /\
  2 * allocated_buckets bucket_exponent + 14 <= signed_limit.
Proof.
  intros signed_limit alignment_exponent words bucket_exponent ACCEPTED.
  destruct (type_geometry_has_positive_minimums alignment_exponent words bucket_exponent)
    as [ALIGN [SIZE [BUCKETS CONTROL]]].
  unfold accepted_layout, allocation_bytes, data_bytes in *.
  repeat split; nia.
Qed.

Theorem reached_probe_step_additions_fit_before_masking :
  forall signed_limit word_limit alignment_exponent words bucket_exponent position stride,
  accepted_layout signed_limit alignment_exponent words bucket_exponent ->
  signed_limit <= word_limit ->
  position < allocated_buckets bucket_exponent ->
  stride < allocated_buckets bucket_exponent ->
  stride + 16 <= word_limit /\ position + (stride + 16) <= word_limit.
Proof.
  intros signed_limit word_limit alignment_exponent words bucket_exponent position stride
    ACCEPTED WORD POSITION STRIDE.
  pose proof (accepted_layout_covers_native_intermediate_arithmetic
    _ _ _ _ ACCEPTED) as [_ [_ [_ [_ BOUND]]]]. split; lia.
Qed.

End NativeHashBagLayout.

Print Assumptions NativeHashBagLayout.standard_extend_and_native_offsets_are_identical.
Print Assumptions NativeHashBagLayout.accepted_layout_has_the_native_size_ceiling.
Print Assumptions NativeHashBagLayout.accepted_layout_validates_both_standard_components.
Print Assumptions NativeHashBagLayout.accepted_layout_covers_native_intermediate_arithmetic.
Print Assumptions NativeHashBagLayout.reached_probe_step_additions_fit_before_masking.
