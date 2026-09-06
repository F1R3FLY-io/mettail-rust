(** * Binary juxtaposition uses the existing category-indexed Pratt contract

    Adjacent homogeneous operands do not require an operator token to have
    declared associativity. Recognition may retain both associations; this
    evidence filter checks their child production powers, without changing
    token selection, payloads, parse costs, or ranks. It does not establish
    general forest completeness or alter generated token-trigger dispatch.

    [Other] stands for every non-category syntax item. The exact two-category
    shape deliberately excludes binders, collections and cross-category
    application: their binding contracts are not inferred here. *)
From Stdlib Require Import List Arith Bool Lia.
From RuntimeGrammar Require Import CategoricalPrattFloor.
Import ListNotations.
Set Implicit Arguments.

Inductive ShapeItem := Operand (category : nat) | Other.

Definition juxtaposition (result : nat) (items : list ShapeItem) : bool :=
  match items with
  | [Operand lhs; Operand rhs] => (lhs =? result) && (rhs =? result)
  | _ => false
  end.

Theorem juxtaposition_is_exact : forall result items,
  juxtaposition result items = true <->
  items = [Operand result; Operand result].
Proof.
  intros result items; split; intro H.
  - destruct items as [|first [|second [|third rest]]];
      repeat match goal with item : ShapeItem |- _ => destruct item end;
      cbn in H; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hl Hr]; apply Nat.eqb_eq in Hl; apply Nat.eqb_eq in Hr.
    subst; reflexivity.
  - subst; simpl; rewrite Nat.eqb_refl; reflexivity.
Qed.

(** This is the existing runtime comparison. It uses strict comparison, not
    bounded-integer increment, so the largest representable power is safe. *)
Definition tighter (parent : nat) (allow_equal : bool) (child : option nat) :=
  match child with
  | None => true
  | Some power => (parent <? power) || (allow_equal && (power =? parent))
  end.

Definition operand_floor (parent : nat) (allow_equal : bool) :
    PrattFloor (OtherCategory 0) :=
  {| minimum_power := if allow_equal then parent else S parent |}.

Definition child_operator (power : nat) : InfixOperator (OtherCategory 0) :=
  {| left_power := power; right_power := power |}.

Theorem tighter_refines_existing_pratt_admission : forall parent allow power,
  tighter parent allow (Some power) =
  admits_infix (operand_floor parent allow) (child_operator power).
Proof.
  intros parent allow power.
  unfold tighter, admits_infix, operand_floor, child_operator; simpl.
  apply eq_true_iff_eq.
  rewrite orb_true_iff, andb_true_iff, Nat.ltb_lt, Nat.eqb_eq, Nat.leb_le.
  destruct allow; simpl; lia.
Qed.

Inductive Associativity := Left | Right | NonAssociative.

Definition binary_admission (assoc : Associativity) (parent : nat)
    (left right : option nat) : bool :=
  match assoc with
  | Left => tighter parent true left && tighter parent false right
  | Right => tighter parent false left && tighter parent true right
  | NonAssociative => tighter parent false left && tighter parent false right
  end.

Theorem equal_power_follows_declared_direction : forall power,
  binary_admission Left power (Some power) None = true /\
  binary_admission Left power None (Some power) = false /\
  binary_admission Right power (Some power) None = false /\
  binary_admission Right power None (Some power) = true /\
  binary_admission NonAssociative power (Some power) None = false /\
  binary_admission NonAssociative power None (Some power) = false.
Proof.
  intro power; unfold binary_admission, tighter.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl; repeat split; reflexivity.
Qed.

Theorem atomic_operands_remain_admitted : forall assoc power,
  binary_admission assoc power None None = true.
Proof. intros assoc power; destruct assoc; reflexivity. Qed.

Theorem lower_power_operand_is_rejected : forall assoc parent child,
  child < parent ->
  binary_admission assoc parent (Some child) None = false /\
  binary_admission assoc parent None (Some child) = false.
Proof.
  intros assoc parent child H.
  assert (Hlt : (parent <? child) = false) by (apply Nat.ltb_ge; lia).
  assert (Heq : (child =? parent) = false) by (apply Nat.eqb_neq; lia).
  destruct assoc; unfold binary_admission, tighter; rewrite Hlt, Heq;
    split; reflexivity.
Qed.

(** The entire candidate is retained, including its independently computed
    syntax, semantic value, cost and rank. No preferred lexical reading is
    substituted for a surviving candidate. *)
Section Preservation.
  Context {Candidate : Type}.
  Variable declared_evidence : Candidate -> bool.

  Definition admitted := filter declared_evidence.

  Theorem admission_preserves_exact_candidate : forall candidates candidate,
    In candidate (admitted candidates) <->
    In candidate candidates /\ declared_evidence candidate = true.
  Proof. intros; apply filter_In. Qed.

  Theorem already_admitted_family_is_unchanged : forall candidates,
    Forall (fun candidate => declared_evidence candidate = true) candidates ->
    admitted candidates = candidates.
  Proof.
    intros candidates H; induction H; simpl; auto.
    unfold admitted in *; simpl; rewrite H, IHForall; reflexivity.
  Qed.
End Preservation.

Print Assumptions juxtaposition_is_exact.
Print Assumptions tighter_refines_existing_pratt_admission.
Print Assumptions equal_power_follows_declared_direction.
Print Assumptions atomic_operands_remain_admitted.
Print Assumptions lower_power_operand_is_rejected.
Print Assumptions admission_preserves_exact_candidate.
Print Assumptions already_admitted_family_is_unchanged.
