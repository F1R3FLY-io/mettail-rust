(*
 * ChainAbsorb: abstract obligations for IterativeChainAbsorb.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From PrattailWpdaRuntime Require Import RuntimeModel.

Import ListNotations.

Inductive assoc : Type :=
  | LeftAssoc
  | RightAssoc
  | MixfixAssoc.

Record span : Type := {
  span_lo : nat;
  span_hi : nat
}.

Definition strictly_inside (sp : span) (pos : nat) : Prop :=
  span_lo sp < pos /\ pos < span_hi sp.

Record chain_spec : Type := {
  op_cat_src_idx : nat;
  op_rule_idx : nat;
  chain_assoc : assoc;
  step_weight : nat
}.

Fixpoint iter_weight (n step : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => step + iter_weight n' step
  end.

Lemma iter_weight_mul :
  forall n step,
    iter_weight n step = n * step.
Proof.
  induction n as [| n IH]; intros step.
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Inductive ordinary_chain (spec : chain_spec) : nat -> nat -> Prop :=
  | ordinary_zero :
      ordinary_chain spec 0 0
  | ordinary_step :
      forall n w,
        ordinary_chain spec n w ->
        ordinary_chain spec (S n) (step_weight spec + w).

Record absorb_result : Type := {
  ar_span : span;
  ar_weight : nat;
  ar_state : control
}.

Definition absorb_chain (spec : chain_spec) (start len : nat) : absorb_result :=
  {| ar_span := {| span_lo := start; span_hi := start + len |};
     ar_weight := iter_weight len (step_weight spec);
     ar_state := Unwinding |}.

Theorem absorb_chain_matches_ordinary_weight :
  forall spec start len,
    ordinary_chain spec len (ar_weight (absorb_chain spec start len)).
Proof.
  intros spec start len.
  induction len as [| len IH].
  - constructor.
  - simpl. constructor. exact IH.
Qed.

Theorem absorb_chain_records_span :
  forall spec start len,
    span_lo (ar_span (absorb_chain spec start len)) = start /\
    span_hi (ar_span (absorb_chain spec start len)) = start + len.
Proof.
  intros. split; reflexivity.
Qed.

Theorem absorb_chain_enters_unwinding :
  forall spec start len,
    ar_state (absorb_chain spec start len) = Unwinding.
Proof.
  intros. reflexivity.
Qed.

Definition cross_cat_allowed (intervals : list span) (pos : nat) : Prop :=
  forall sp, In sp intervals -> ~ strictly_inside sp pos.

Lemma absorbed_interval_suppresses_strict_interior :
  forall sp pos,
    strictly_inside sp pos ->
    ~ cross_cat_allowed [sp] pos.
Proof.
  intros sp pos Hinside Hallowed.
  specialize (Hallowed sp).
  assert (Hin : In sp [sp]) by (left; reflexivity).
  specialize (Hallowed Hin).
  contradiction.
Qed.

Lemma absorbed_interval_allows_left_boundary :
  forall sp,
    ~ strictly_inside sp (span_lo sp).
Proof.
  intros sp [Hlt _].
  lia.
Qed.

Lemma absorbed_interval_allows_right_boundary :
  forall sp,
    ~ strictly_inside sp (span_hi sp).
Proof.
  intros sp [_ Hlt].
  lia.
Qed.

Record interval_key : Type := {
  ik_category : nat;
  ik_rule : nat
}.

Record keyed_span : Type := {
  ks_key : interval_key;
  ks_span : span
}.

Definition keyed_cross_cat_allowed
    (intervals : list keyed_span)
    (key : interval_key)
    (pos : nat) : Prop :=
  forall entry,
    In entry intervals ->
    ks_key entry = key ->
    ~ strictly_inside (ks_span entry) pos.

Lemma keyed_absorbed_interval_suppresses_matching_strict_interior :
  forall key sp pos,
    strictly_inside sp pos ->
    ~ keyed_cross_cat_allowed
        [{| ks_key := key; ks_span := sp |}]
        key
        pos.
Proof.
  intros key sp pos Hinside Hallowed.
  specialize
    (Hallowed {| ks_key := key; ks_span := sp |}).
  assert (Hin :
    In {| ks_key := key; ks_span := sp |}
      [{| ks_key := key; ks_span := sp |}])
    by (left; reflexivity).
  specialize (Hallowed Hin eq_refl).
  contradiction.
Qed.

Lemma keyed_absorbed_interval_allows_unrelated_key :
  forall stored query sp pos,
    stored <> query ->
    keyed_cross_cat_allowed
      [{| ks_key := stored; ks_span := sp |}]
      query
      pos.
Proof.
  intros stored query sp pos Hneq entry Hin Hkey Hinside.
  destruct Hin as [Heq | []].
  subst entry.
  simpl in Hkey.
  apply Hneq.
  exact Hkey.
Qed.
