(** Native admission used by the declared Regex continuation machines.

    Scalar inputs are read at byte zero and compared with the returned
    singleton text before either the surface or derivative continuation runs.
    This file reuses the scalar-sequence UTF-8 model; it does not certify Rust
    String/char encoding. Concrete codec and kernel tests supply that boundary.

    Integer operands arrive through the existing i128 codec. The checked
    nonnegative addition below makes its admission explicit, then connects
    add-zero and add-one to the already proved repetition endpoint invariant.
    No counter-sized computation is evaluated by these proofs. *)

From Stdlib Require Import List Bool PeanoNat ZArith Lia.
From RuntimeGrammar Require Import SemanticIntrinsics NativeReflectionCodec
  RegexGsltMatch RegexGsltSmartMachine RegexGsltRepeatMachine.
Import ListNotations SemanticIntrinsics.SemanticIntrinsics
  NativeReflectionCodec.NativeReflectionCodec.

Definition admit_scalar_text (text : ScalarText) : option Scalar :=
  match utf8_scalar_at text 0 with
  | None => None
  | Some (scalar, _) =>
      if list_eq_dec Nat.eq_dec text [scalar] then Some scalar else None
  end.

Theorem scalar_admission_is_exact : forall text scalar,
  admit_scalar_text text = Some scalar <-> text = [scalar].
Proof.
  intros [|head tail] scalar; unfold admit_scalar_text; cbn [utf8_scalar_at Nat.eqb].
  - split; discriminate.
  - destruct (list_eq_dec Nat.eq_dec (head :: tail) [head]) as [E|E].
    + inversion E; subst tail. split; intro H; inversion H; reflexivity.
    + split; [discriminate|]. intro H. inversion H; subst. contradiction.
Qed.

Corollary empty_scalar_is_not_admitted : admit_scalar_text [] = None.
Proof. reflexivity. Qed.

Corollary multiple_scalars_are_not_admitted : forall first second rest,
  admit_scalar_text (first :: second :: rest) = None.
Proof.
  intros. unfold admit_scalar_text; cbn [utf8_scalar_at Nat.eqb].
  destruct (list_eq_dec Nat.eq_dec (first :: second :: rest) [first]);
    [discriminate|reflexivity].
Qed.

(** These are the common read/decide phases of EReadScalar and
    DerivativeReadScalar, independent of the continuation they guard. *)
Inductive ScalarAdmissionState :=
| ScalarRead (text : ScalarText)
| ScalarDecide (text : ScalarText) (scalar : Scalar) (equal : bool)
| ScalarAdmitted (scalar : Scalar).

Definition scalar_admission_step (state : ScalarAdmissionState)
    : option ScalarAdmissionState :=
  match state with
  | ScalarRead text =>
      match utf8_scalar_at text 0 with
      | None => None
      | Some (scalar, _) => Some (ScalarDecide text scalar
          (if list_eq_dec Nat.eq_dec text [scalar] then true else false))
      end
  | ScalarDecide _ scalar true => Some (ScalarAdmitted scalar)
  | _ => None
  end.

Definition scalar_phase (state : ScalarAdmissionState) : nat :=
  match state with ScalarRead _ => 2 | ScalarDecide _ _ _ => 1 | ScalarAdmitted _ => 0 end.

Theorem scalar_administration_strictly_decreases : forall source target,
  scalar_admission_step source = Some target -> scalar_phase target < scalar_phase source.
Proof.
  intros source target H. destruct source as [text|text scalar equal|scalar].
  - cbn [scalar_admission_step] in H.
    destruct (utf8_scalar_at text 0) as [[scalar next]|]; [|discriminate].
    inversion H; subst. cbn [scalar_phase]. lia.
  - destruct equal; inversion H; subst; cbn [scalar_phase]; lia.
  - discriminate.
Qed.

Theorem scalar_read_decide_admits_exactly_singletons : forall text scalar,
  (exists decision,
    scalar_admission_step (ScalarRead text) = Some decision /\
    scalar_admission_step decision = Some (ScalarAdmitted scalar)) <-> text = [scalar].
Proof.
  intros text scalar. split.
  - intros [decision [Hread Hdone]]. destruct text as [|head tail]; [discriminate|].
    cbn [scalar_admission_step utf8_scalar_at Nat.eqb] in Hread.
    destruct (list_eq_dec Nat.eq_dec (head :: tail) [head]) as [E|E];
      inversion Hread; subst decision.
    + cbn [scalar_admission_step] in Hdone. inversion Hdone; subst. exact E.
    + discriminate.
  - intro E; subst text. exists (ScalarDecide [scalar] scalar true). split; [|reflexivity].
    cbn [scalar_admission_step utf8_scalar_at Nat.eqb].
    destruct (list_eq_dec Nat.eq_dec [scalar] [scalar]); [reflexivity|contradiction].
Qed.

Definition native_nat (value : Z) : bool := in_i128 value && (0 <=? value)%Z.

Lemma native_nat_exact : forall value,
  native_nat value = true <-> (0 <= value < 2 ^ 127)%Z.
Proof.
  intro value. unfold native_nat, in_i128.
  repeat rewrite andb_true_iff. rewrite Z.leb_le, Z.ltb_lt, Z.leb_le.
  assert (Hpositive : (0 < 2 ^ 127)%Z) by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

Definition checked_native_nat_add (first second : Z) : option Z :=
  if native_nat first && native_nat second && native_nat (first + second)%Z
  then Some (first + second)%Z else None.

Theorem checked_add_zero_admits_exactly_native_naturals : forall value,
  checked_native_nat_add value 0 = Some value <-> native_nat value = true.
Proof.
  intro value. unfold checked_native_nat_add. rewrite Z.add_0_r.
  assert (Hzero : native_nat 0 = true) by (apply native_nat_exact; split; [lia|apply Z.pow_pos_nonneg; lia]).
  rewrite Hzero, andb_true_r, andb_diag.
  destruct (native_nat value); split; intro H; try reflexivity; discriminate.
Qed.

Theorem checked_add_one_is_nat_successor : forall cursor,
  (Z.of_nat (S cursor) < 2 ^ 127)%Z ->
  checked_native_nat_add (Z.of_nat cursor) 1 = Some (Z.of_nat (S cursor)).
Proof.
  intros cursor Hbound. rewrite Nat2Z.inj_succ in *.
  assert (Hcursor : native_nat (Z.of_nat cursor) = true) by
    (apply native_nat_exact; pose proof (Nat2Z.is_nonneg cursor); lia).
  assert (Hone : native_nat 1 = true) by (apply native_nat_exact; split; [lia|vm_compute; reflexivity]).
  assert (Hsum : native_nat (Z.of_nat cursor + 1) = true) by
    (apply native_nat_exact; pose proof (Nat2Z.is_nonneg cursor); lia).
  unfold checked_native_nat_add. rewrite Hcursor, Hone, Hsum.
  change (Some (Z.of_nat cursor + 1)%Z = Some (Z.succ (Z.of_nat cursor))).
  now f_equal.
Qed.

Theorem required_native_increment_fits : forall pattern lower upper cursor result,
  repeat_control_valid (RepeatAppendRequired pattern lower upper cursor (SmartDone result)) ->
  (Z.of_nat upper < 2 ^ 127)%Z ->
  checked_native_nat_add (Z.of_nat cursor) 1 = Some (Z.of_nat (S cursor)).
Proof.
  intros pattern lower upper cursor result Hvalid Hbound.
  pose proof (required_increment_fits_admitted_endpoint _ _ _ _ _ upper Hvalid (Nat.le_refl upper)).
  apply checked_add_one_is_nat_successor. lia.
Qed.

Theorem optional_native_increment_fits : forall pattern upper cursor required result,
  repeat_control_valid (RepeatOptionalAlternative pattern upper cursor required (SmartDone result)) ->
  (Z.of_nat upper < 2 ^ 127)%Z ->
  checked_native_nat_add (Z.of_nat cursor) 1 = Some (Z.of_nat (S cursor)).
Proof.
  intros pattern upper cursor required result Hvalid Hbound.
  pose proof (optional_increment_fits_admitted_endpoint _ _ _ _ _ upper Hvalid (Nat.le_refl upper)).
  apply checked_add_one_is_nat_successor. lia.
Qed.

Print Assumptions scalar_admission_is_exact.
Print Assumptions empty_scalar_is_not_admitted.
Print Assumptions multiple_scalars_are_not_admitted.
Print Assumptions scalar_administration_strictly_decreases.
Print Assumptions scalar_read_decide_admits_exactly_singletons.
Print Assumptions native_nat_exact.
Print Assumptions checked_add_zero_admits_exactly_native_naturals.
Print Assumptions checked_add_one_is_nat_successor.
Print Assumptions required_native_increment_fits.
Print Assumptions optional_native_increment_fits.
