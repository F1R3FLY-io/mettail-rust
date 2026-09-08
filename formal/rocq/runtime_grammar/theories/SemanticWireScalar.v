(** Full unsigned-64 transport through signed Rholang scalar representations.

    The fixed-width codec and induction follow encode_fixed_be,
    decode_fixed_be and decode_encode_fixed_be in the sibling project's
    vinary-syntax/formal/rocq/SourceSnapshotIdentitySpec.v. Binary N replaces
    unary nat for scalar arithmetic so checking the 64-bit endpoints cannot
    allocate unary representations of those endpoints. Width remains nat.

    Small is a signed integer. Large carries signed big-endian bytes: this
    interface accepts only a zero sign byte followed by exactly eight bytes,
    and only values above the Small range. Negative, redundant, truncated,
    trailing and overflow representations cannot produce a canonical value.
    The inverse in BOTH directions establishes representation uniqueness.
    Rust library/Par-envelope correspondence and resource charging are tested
    separately; this model neither calls nor assumes correctness of BigInt. *)
From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.
Open Scope N_scope.

Module SemanticWireScalar.

Fixpoint width_bound (width : nat) : N :=
  match width with O => 1 | S smaller => 256 * width_bound smaller end.

Fixpoint encode_be (width : nat) (value : N) : list N :=
  match width with O => []
  | S smaller => encode_be smaller (value / 256) ++ [value mod 256] end.

Fixpoint decode_be (width : nat) (input : list N) : option (N * list N) :=
  match width with
  | O => Some (0, input)
  | S smaller =>
      match decode_be smaller input with
      | Some (prefix, current :: rest) =>
          if current <? 256 then Some (prefix * 256 + current, rest) else None
      | _ => None end
  end.

Lemma encoded_width : forall width value,
  length (encode_be width value) = width.
Proof.
  induction width; intros; cbn [encode_be]; [reflexivity |].
  rewrite length_app, IHwidth. cbn. lia.
Qed.

Lemma decode_encode_be : forall width value suffix,
  value < width_bound width ->
  decode_be width (encode_be width value ++ suffix) = Some (value, suffix).
Proof.
  induction width as [|width IH]; intros value suffix Hbound.
  - cbn [width_bound] in Hbound. assert (value = 0) by lia. now subst.
  - change (value < 256 * width_bound width) in Hbound.
    assert (Hquotient : value / 256 < width_bound width) by
      (apply N.Div0.div_lt_upper_bound; lia).
    cbn [encode_be decode_be]. rewrite <- app_assoc, IH by exact Hquotient.
    change ((if value mod 256 <? 256 then
      Some ((value / 256) * 256 + value mod 256, suffix) else None) = Some (value, suffix)).
    assert (Hremainder : value mod 256 < 256) by (apply N.mod_upper_bound; discriminate).
    assert (Hcheck : (value mod 256 <? 256) = true) by (apply N.ltb_lt; exact Hremainder).
    rewrite Hcheck. f_equal. f_equal.
    pose proof (N.div_mod value 256 ltac:(discriminate)). nia.
Qed.

Lemma encode_decode_be : forall width input value suffix,
  decode_be width input = Some (value, suffix) ->
  value < width_bound width /\ encode_be width value ++ suffix = input.
Proof.
  induction width as [|width IH]; intros input value suffix Hdecode.
  - cbn [decode_be] in Hdecode. inversion Hdecode; subst. split; [reflexivity | reflexivity].
  - cbn [decode_be] in Hdecode.
    destruct (decode_be width input) as [[prefix rest]|] eqn:E; try discriminate.
    destruct rest as [|current rest]; try discriminate.
    destruct (current <? 256) eqn:C; try discriminate.
    apply N.ltb_lt in C. inversion Hdecode; subst.
    destruct (IH input prefix (current :: suffix) E) as [B R].
    assert (D : (prefix * 256 + current) / 256 = prefix).
    { symmetry. apply N.div_unique with (r := current); [exact C | nia]. }
    assert (M : (prefix * 256 + current) mod 256 = current).
    { symmetry. apply N.mod_unique with (q := prefix); [exact C | nia]. }
    split.
    + change (prefix * 256 + current < 256 * width_bound width). nia.
    + cbn [encode_be]. rewrite D, M, <- app_assoc. exact R.
Qed.

Definition small_bound : N := 9223372036854775808.
Definition full_bound : N := width_bound 8.

Inductive Scalar := Small (value : Z) | Large (bytes : list N).

Definition encode_uint value :=
  if value <? small_bound then Small (Z.of_N value)
  else Large (0 :: encode_be 8 value).

Definition decode_uint scalar := match scalar with
  | Small value =>
      if (0 <=? value)%Z then
        let unsigned := Z.to_N value in
        if unsigned <? small_bound then Some unsigned else None
      else None
  | Large (0 :: bytes) =>
      match decode_be 8 bytes with
      | Some (value, []) =>
          if small_bound <=? value then Some value else None
      | _ => None end
  | _ => None end.

Theorem uint_round_trip : forall value,
  value < full_bound -> decode_uint (encode_uint value) = Some value.
Proof.
  intros value B. unfold encode_uint.
  destruct (value <? small_bound) eqn:C.
  - cbn [decode_uint]. rewrite N2Z.id.
    assert (ZC : (0 <=? Z.of_N value)%Z = true) by (apply Z.leb_le; lia).
    now rewrite ZC, C.
  - change (match decode_be 8 (encode_be 8 value) with
      | Some (decoded, []) => if small_bound <=? decoded then Some decoded else None
      | _ => None end = Some value).
    replace (encode_be 8 value) with (encode_be 8 value ++ []) by apply app_nil_r.
    rewrite decode_encode_be by exact B.
    apply N.ltb_ge in C.
    assert (NC : (small_bound <=? value) = true) by (apply N.leb_le; exact C).
    now rewrite NC.
Qed.

Theorem accepted_scalar_is_canonical : forall scalar value,
  decode_uint scalar = Some value ->
  value < full_bound /\ encode_uint value = scalar.
Proof.
  intros [signed|bytes] value H.
  - cbn [decode_uint] in H.
    destruct (0 <=? signed)%Z eqn:ZC; try discriminate.
    destruct (Z.to_N signed <? small_bound) eqn:NC; try discriminate.
    inversion H; subst. apply Z.leb_le in ZC.
    split.
    + apply N.ltb_lt in NC.
      assert (small_bound < full_bound) by reflexivity. lia.
    + unfold encode_uint. rewrite NC, Z2N.id by exact ZC. reflexivity.
  - destruct bytes as [|sign rest]; try discriminate.
    destruct sign; try discriminate.
    change (match decode_be 8 rest with
      | Some (decoded, []) => if small_bound <=? decoded then Some decoded else None
      | _ => None end = Some value) in H.
    destruct (decode_be 8 rest) as [[decoded suffix]|] eqn:E; try discriminate.
    destruct suffix; try discriminate.
    destruct (small_bound <=? decoded) eqn:C; try discriminate.
    inversion H; subst. apply N.leb_le in C.
    destruct (encode_decode_be 8 rest value [] E) as [B R].
    split; [exact B |]. unfold encode_uint.
    assert (NC : (value <? small_bound) = false) by (apply N.ltb_ge; exact C).
    rewrite NC. rewrite app_nil_r in R. now rewrite R.
Qed.

Theorem uint_encoding_is_injective : forall a b,
  a < full_bound -> b < full_bound -> encode_uint a = encode_uint b -> a = b.
Proof.
  intros a b A B E. apply (f_equal decode_uint) in E.
  rewrite !uint_round_trip in E by assumption. now inversion E.
Qed.

Theorem large_encoding_has_nine_bytes : forall value,
  small_bound <= value -> exists bytes,
    encode_uint value = Large bytes /\ length bytes = 9%nat.
Proof.
  intros value H. unfold encode_uint.
  assert (C : (value <? small_bound) = false) by (apply N.ltb_ge; exact H).
  rewrite C. exists (0 :: encode_be 8 value). split; [reflexivity |].
  cbn [length]. now rewrite encoded_width.
Qed.

Theorem negative_small_is_refused : forall value,
  (value < 0)%Z -> decode_uint (Small value) = None.
Proof.
  intros value H. cbn [decode_uint].
  assert (C : (0 <=? value)%Z = false) by (apply Z.leb_gt; exact H).
  now rewrite C.
Qed.

End SemanticWireScalar.

Print Assumptions SemanticWireScalar.encoded_width.
Print Assumptions SemanticWireScalar.decode_encode_be.
Print Assumptions SemanticWireScalar.encode_decode_be.
Print Assumptions SemanticWireScalar.uint_round_trip.
Print Assumptions SemanticWireScalar.accepted_scalar_is_canonical.
Print Assumptions SemanticWireScalar.uint_encoding_is_injective.
Print Assumptions SemanticWireScalar.large_encoding_has_nine_bytes.
Print Assumptions SemanticWireScalar.negative_small_is_refused.
