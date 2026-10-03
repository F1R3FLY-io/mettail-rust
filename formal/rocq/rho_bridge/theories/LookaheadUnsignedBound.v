(** The value-level contract for the FIPS's unsigned 64-bit lookahead bound.

    Rholang's existing small integer carries a signed 64-bit value. Its existing
    big-integer literal and protobuf value carry the upper half of the unsigned
    range without converting the number to text. The wire constructors below
    abstract those two *decoded values*: canonical signed-byte encoding of the
    big-integer datum is a separate Rust codec obligation, not a theorem here.

    The public source gate must reject values outside [0, unsigned_max]. The
    old signed-integer wire remains unchanged for its whole nonnegative range;
    larger valid values use the versioned big-integer request. Decoding checks
    the range again because callers can send directly to the system channel. *)
From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.

Definition signed_max : Z := 9223372036854775807.
Definition unsigned_max : Z := 18446744073709551615.

Inductive BoundDatum := SmallInteger (value : Z) | BigInteger (value : Z).

Definition in_unsigned_range (value : Z) : bool :=
  Z.leb 0 value && Z.leb value unsigned_max.

Definition encode_bound (value : Z) : BoundDatum :=
  if Z.leb value signed_max then SmallInteger value else BigInteger value.

Definition decode_bound (datum : BoundDatum) : option Z :=
  match datum with
  | SmallInteger value =>
      if Z.leb 0 value && Z.leb value signed_max then Some value else None
  | BigInteger value =>
      if in_unsigned_range value then Some value else None
  end.

Definition admit_source_bound (value : Z) : option BoundDatum :=
  if in_unsigned_range value then Some (encode_bound value) else None.

Lemma signed_max_below_unsigned_max : signed_max < unsigned_max.
Proof. unfold signed_max, unsigned_max; lia. Qed.

Theorem admitted_bound_round_trips : forall value,
  0 <= value <= unsigned_max -> decode_bound (encode_bound value) = Some value.
Proof.
  intros value Hrange.
  unfold encode_bound, decode_bound.
  assert (Hnonnegative : Z.leb 0 value = true) by (apply Z.leb_le; lia).
  assert (Hunsigned : Z.leb value unsigned_max = true) by (apply Z.leb_le; lia).
  destruct (Z.leb value signed_max) eqn:Hsmall; cbn.
  - now rewrite Hnonnegative, Hsmall.
  - unfold in_unsigned_range. now rewrite Hnonnegative, Hunsigned.
Qed.

Theorem admitted_source_bound_round_trips : forall value datum,
  admit_source_bound value = Some datum -> decode_bound datum = Some value.
Proof.
  intros value datum Hadmitted.
  unfold admit_source_bound in Hadmitted.
  destruct (in_unsigned_range value) eqn:Hrange; try discriminate.
  inversion Hadmitted; subst datum.
  unfold in_unsigned_range in Hrange.
  apply andb_true_iff in Hrange as [Hnonnegative Hmaximum].
  apply Z.leb_le in Hnonnegative.
  apply Z.leb_le in Hmaximum.
  apply admitted_bound_round_trips. lia.
Qed.

Theorem decoded_bound_is_unsigned : forall datum value,
  decode_bound datum = Some value -> 0 <= value <= unsigned_max.
Proof.
  intros [candidate | candidate] value Hdecoded; cbn in Hdecoded.
  - destruct (Z.leb 0 candidate && Z.leb candidate signed_max) eqn:Hrange;
      try discriminate.
    inversion Hdecoded; subst value.
    apply andb_true_iff in Hrange as [Hnonnegative Hmaximum].
    apply Z.leb_le in Hnonnegative.
    apply Z.leb_le in Hmaximum.
    pose proof signed_max_below_unsigned_max; lia.
  - unfold in_unsigned_range in Hdecoded.
    destruct (Z.leb 0 candidate && Z.leb candidate unsigned_max) eqn:Hrange;
      try discriminate.
    inversion Hdecoded; subst value.
    apply andb_true_iff in Hrange as [Hnonnegative Hmaximum].
    apply Z.leb_le in Hnonnegative.
    apply Z.leb_le in Hmaximum.
    lia.
Qed.

Theorem negative_source_bound_is_refused : forall value,
  value < 0 -> admit_source_bound value = None.
Proof.
  intros value Hnegative.
  unfold admit_source_bound, in_unsigned_range.
  assert (Hcheck : Z.leb 0 value = false) by (apply Z.leb_gt; lia).
  now rewrite Hcheck.
Qed.

Theorem overflowing_source_bound_is_refused : forall value,
  unsigned_max < value -> admit_source_bound value = None.
Proof.
  intros value Hoverflow.
  unfold admit_source_bound, in_unsigned_range.
  assert (Hcheck : Z.leb value unsigned_max = false) by (apply Z.leb_gt; lia).
  rewrite Hcheck. now destruct (Z.leb 0 value).
Qed.

Theorem old_wire_is_preserved : forall value,
  0 <= value <= signed_max -> encode_bound value = SmallInteger value.
Proof.
  intros value Hrange. unfold encode_bound.
  assert (Hcheck : Z.leb value signed_max = true) by (apply Z.leb_le; lia).
  now rewrite Hcheck.
Qed.

Theorem upper_unsigned_half_uses_big_integer : forall value,
  signed_max < value <= unsigned_max -> encode_bound value = BigInteger value.
Proof.
  intros value Hrange. unfold encode_bound.
  assert (Hcheck : Z.leb value signed_max = false) by (apply Z.leb_gt; lia).
  now rewrite Hcheck.
Qed.

Example first_big_integer_bound_round_trips :
  decode_bound (encode_bound 9223372036854775808) = Some 9223372036854775808.
Proof. reflexivity. Qed.

Example maximum_unsigned_bound_round_trips :
  decode_bound (encode_bound unsigned_max) = Some unsigned_max.
Proof. reflexivity. Qed.

Print Assumptions admitted_bound_round_trips.
Print Assumptions admitted_source_bound_round_trips.
Print Assumptions decoded_bound_is_unsigned.
Print Assumptions negative_source_bound_is_refused.
Print Assumptions overflowing_source_bound_is_refused.
Print Assumptions old_wire_is_preserved.
Print Assumptions upper_unsigned_half_uses_big_integer.
