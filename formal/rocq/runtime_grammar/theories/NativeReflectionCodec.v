(** * Exact native payloads at the structural FLT boundary

    Dynamic reflection represents text as two lowercase hexadecimal digits per
    UTF-8 byte, integers as canonical signed decimal i128 values, and Booleans
    as [true] or [false].  These are payload codecs, not guest-language parsers.
    The constructor/tag envelope and the semantic image's operator framing are
    separate boundaries; this file does not assume or prove their correctness.

    The byte-string theorem is deliberately stronger than a Unicode-only
    theorem: hexadecimal conversion preserves every byte.  Production still
    checks UTF-8 before constructing a Rust String.  Integer decimal conversion
    reuses the standard library's proved decimal conversion, then checks the
    same bounds and canonical-render equality as the Rust admission helper.
    This model does not certify the Rust standard library or protobuf codec.

    This model proves payload partial inverses.  Caller-enforced input/work
    limits and iterative Rust execution are separate refinement obligations;
    an i128 value bound alone does not bound decimal input length. *)

From Stdlib Require Import Strings.Ascii Strings.String Numbers.DecimalString
  Numbers.DecimalZ ZArith Bool.Bool.

Local Open Scope string_scope.
Local Open Scope char_scope.

Module NativeReflectionCodec.

Record Nibble := nibble {
  bit0 : bool;
  bit1 : bool;
  bit2 : bool;
  bit3 : bool
}.

Definition hex_digit (n : Nibble) : ascii :=
  match n with
  | nibble false false false false => "0"
  | nibble true  false false false => "1"
  | nibble false true  false false => "2"
  | nibble true  true  false false => "3"
  | nibble false false true  false => "4"
  | nibble true  false true  false => "5"
  | nibble false true  true  false => "6"
  | nibble true  true  true  false => "7"
  | nibble false false false true  => "8"
  | nibble true  false false true  => "9"
  | nibble false true  false true  => "a"
  | nibble true  true  false true  => "b"
  | nibble false false true  true  => "c"
  | nibble true  false true  true  => "d"
  | nibble false true  true  true  => "e"
  | nibble true  true  true  true  => "f"
  end.

Definition decode_digit (c : ascii) : option Nibble :=
  match c with
  | "0" => Some (nibble false false false false)
  | "1" => Some (nibble true  false false false)
  | "2" => Some (nibble false true  false false)
  | "3" => Some (nibble true  true  false false)
  | "4" => Some (nibble false false true  false)
  | "5" => Some (nibble true  false true  false)
  | "6" => Some (nibble false true  true  false)
  | "7" => Some (nibble true  true  true  false)
  | "8" => Some (nibble false false false true)
  | "9" => Some (nibble true  false false true)
  | "a" => Some (nibble false true  false true)
  | "b" => Some (nibble true  true  false true)
  | "c" => Some (nibble false false true  true)
  | "d" => Some (nibble true  false true  true)
  | "e" => Some (nibble false true  true  true)
  | "f" => Some (nibble true  true  true  true)
  | _ => None
  end.

Lemma decode_encoded_digit : forall n, decode_digit (hex_digit n) = Some n.
Proof.
  intros [a b c d]. destruct a, b, c, d; reflexivity.
Qed.

Lemma encode_decoded_digit : forall c n,
  decode_digit c = Some n -> hex_digit n = c.
Proof.
  intros [a b c d e f g h] n.
  destruct a, b, c, d, e, f, g, h;
    cbn; intros H; inversion H; reflexivity.
Qed.

Definition join_nibbles (high low : Nibble) : ascii :=
  Ascii (bit0 low) (bit1 low) (bit2 low) (bit3 low)
    (bit0 high) (bit1 high) (bit2 high) (bit3 high).

Fixpoint encode_hex (bytes : string) : string :=
  match bytes with
  | EmptyString => EmptyString
  | String (Ascii a b c d e f g h) rest =>
      String (hex_digit (nibble e f g h))
        (String (hex_digit (nibble a b c d)) (encode_hex rest))
  end.

Fixpoint decode_hex (text : string) : option string :=
  match text with
  | EmptyString => Some EmptyString
  | String high (String low rest) =>
      match decode_digit high, decode_digit low, decode_hex rest with
      | Some hi, Some lo, Some tail => Some (String (join_nibbles hi lo) tail)
      | _, _, _ => None
      end
  | _ => None
  end.

Theorem decode_encoded_bytes : forall bytes,
  decode_hex (encode_hex bytes) = Some bytes.
Proof.
  induction bytes as [|[a b c d e f g h] rest IH].
  - reflexivity.
  - cbn [encode_hex decode_hex].
    rewrite !decode_encoded_digit, IH. reflexivity.
Qed.

Theorem encode_decoded_bytes : forall text bytes,
  decode_hex text = Some bytes -> encode_hex bytes = text.
Proof.
  fix IH 1.
  intros [|high [|low rest]] bytes H.
  - inversion H. reflexivity.
  - discriminate.
  - cbn [decode_hex] in H.
    destruct (decode_digit high) as [hi|] eqn:Hhigh; try discriminate.
    destruct (decode_digit low) as [lo|] eqn:Hlow; try discriminate.
    destruct (decode_hex rest) as [tail|] eqn:Hrest; try discriminate.
    inversion H; subst bytes.
    pose proof (encode_decoded_digit high hi Hhigh) as Ehigh.
    pose proof (encode_decoded_digit low lo Hlow) as Elow.
    destruct hi as [a b c d], lo as [e f g h].
    (* Preserve the digit abstraction for rewriting.  [cbn] here unfolded its
       match and hid the exact subterm supplied by [encode_decoded_digit]. *)
    change (String (hex_digit (nibble a b c d))
      (String (hex_digit (nibble e f g h)) (encode_hex tail)) =
      String high (String low rest)).
    rewrite Ehigh, Elow, (IH rest tail Hrest). reflexivity.
Qed.

Corollary hex_encoding_injective : forall first second,
  encode_hex first = encode_hex second -> first = second.
Proof.
  intros first second H.
  pose proof (decode_encoded_bytes first) as E.
  rewrite H, decode_encoded_bytes in E. now inversion E.
Qed.

(** Byte identity also preserves any byte-defined validity property, including
    UTF-8 validity.  No proposition about the implementation of a UTF-8 checker
    is assumed by this transport theorem. *)
Corollary round_trip_preserves_byte_property : forall (P : string -> Prop) bytes result,
  P bytes -> decode_hex (encode_hex bytes) = Some result -> P result.
Proof.
  intros P bytes result HP H.
  rewrite decode_encoded_bytes in H. now inversion H; subst.
Qed.

Definition encode_integer (value : Z) : string :=
  DecimalString.NilEmpty.string_of_int (Z.to_int value).

Definition in_i128 (value : Z) : bool :=
  (Z.leb (-(2 ^ 127)) value && Z.ltb value (2 ^ 127))%Z.

Definition decode_integer (text : string) : option Z :=
  match DecimalString.NilEmpty.int_of_string text with
  | None => None
  | Some decimal =>
      let value := Z.of_int decimal in
      if in_i128 value && String.eqb (encode_integer value) text
      then Some value else None
  end.

Theorem decode_encoded_integer : forall value,
  in_i128 value = true -> decode_integer (encode_integer value) = Some value.
Proof.
  intros value Hbound. unfold decode_integer, encode_integer.
  rewrite DecimalString.NilEmpty.isi, DecimalZ.of_to, Hbound, String.eqb_refl.
  reflexivity.
Qed.

Theorem encode_decoded_integer : forall text value,
  decode_integer text = Some value ->
  encode_integer value = text /\ in_i128 value = true.
Proof.
  intros text value H. unfold decode_integer in H.
  destruct (DecimalString.NilEmpty.int_of_string text) as [decimal|]; try discriminate.
  destruct (in_i128 (Z.of_int decimal) &&
    String.eqb (encode_integer (Z.of_int decimal)) text) eqn:E; try discriminate.
  inversion H; subst value. apply andb_true_iff in E.
  destruct E as [Hbound Hcanonical]. apply String.eqb_eq in Hcanonical.
  auto.
Qed.

Corollary integer_encoding_injective : forall first second,
  in_i128 first = true -> in_i128 second = true ->
  encode_integer first = encode_integer second -> first = second.
Proof.
  intros first second Hfirst Hsecond Heq.
  pose proof (decode_encoded_integer first Hfirst) as H.
  rewrite Heq, (decode_encoded_integer second Hsecond) in H. now inversion H.
Qed.

Definition encode_boolean (value : bool) : string :=
  if value then "true"%string else "false"%string.

Definition decode_boolean (text : string) : option bool :=
  if String.eqb text "true"%string then Some true
  else if String.eqb text "false"%string then Some false
  else None.

Theorem decode_encoded_boolean : forall value,
  decode_boolean (encode_boolean value) = Some value.
Proof. intros []; reflexivity. Qed.

Theorem encode_decoded_boolean : forall text value,
  decode_boolean text = Some value -> encode_boolean value = text.
Proof.
  intros text value H. unfold decode_boolean in H.
  destruct (String.eqb text "true"%string) eqn:Etrue.
  - apply String.eqb_eq in Etrue. inversion H; subst. reflexivity.
  - destruct (String.eqb text "false"%string) eqn:Efalse; try discriminate.
    apply String.eqb_eq in Efalse. inversion H; subst. reflexivity.
Qed.

Example noncanonical_hex_rejected : decode_hex "4A"%string = None.
Proof. reflexivity. Qed.

Example odd_hex_rejected : decode_hex "a"%string = None.
Proof. reflexivity. Qed.

Example noncanonical_zero_rejected : decode_integer "-0"%string = None.
Proof. reflexivity. Qed.

Example leading_zero_rejected : decode_integer "01"%string = None.
Proof. reflexivity. Qed.

End NativeReflectionCodec.

Print Assumptions NativeReflectionCodec.decode_encoded_bytes.
Print Assumptions NativeReflectionCodec.encode_decoded_bytes.
Print Assumptions NativeReflectionCodec.decode_encoded_integer.
Print Assumptions NativeReflectionCodec.encode_decoded_integer.
Print Assumptions NativeReflectionCodec.decode_encoded_boolean.
Print Assumptions NativeReflectionCodec.encode_decoded_boolean.
