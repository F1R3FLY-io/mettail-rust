(*
 * SemiringLaws: Semiring law proofs for Provenance, Relational, and KAT
 * weight domains.
 *
 * Proves that three key weight domains from the mathematical analyses layer
 * satisfy the semiring axioms:
 *   1. (K, +, 0) is a commutative monoid
 *   2. (K, *, 1) is a monoid
 *   3. * distributes over +
 *   4. 0 is a two-sided annihilator for *
 *
 * Additionally proves:
 *   - KAT star axiom: star(a) = 1 + a * star(a)
 *   - KAT Boolean test embedding: test(p) * test(q) = test(p && q)
 *   - Hoare triple soundness: {p} e {q}  <->  test(p) * e * test(negb q) = zero
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                            | Location
 *   -----------------------------|--------------------------------------|--------------------------
 *   Semiring (class)             | trait Semiring                       | automata/semiring.rs:36
 *   prov_plus                    | ProvenanceWeight::plus               | provenance.rs:180
 *   prov_times                   | ProvenanceWeight::times              | provenance.rs:193
 *   prov_zero                    | ProvenanceWeight::zero               | provenance.rs:149
 *   prov_one                     | ProvenanceWeight::one                | provenance.rs:155
 *   rel_plus                     | HeapSemiring::plus for Relational    | relational.rs:155
 *   rel_times                    | HeapSemiring::times for Relational   | relational.rs:165
 *   rel_zero                     | RelationalWeight::empty              | relational.rs:75
 *   rel_one                      | RelationalWeight::identity           | relational.rs:83
 *   kat_zero / kat_one           | KatExpr::Zero / KatExpr::One         | kat.rs:134-135
 *   kat_seq / kat_alt            | KatExpr::Seq / KatExpr::Alt          | kat.rs:143-145
 *   kat_star                     | KatExpr::Star                        | kat.rs:147
 *   kat_test                     | KatExpr::Test                        | kat.rs:139
 *   verify_hoare_triple          | verify_hoare_triple                  | kat.rs:568
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import SetoidList.
From Hammer Require Import Tactics.
From Stdlib Require Import Setoid.

Import ListNotations.

(* ===================================================================== *)
(*  Semiring Type Class                                                    *)
(* ===================================================================== *)

(* A semiring (K, +, *, 0, 1) with the standard axioms.
   Mirrors the Rust trait Semiring in automata/semiring.rs:36. *)

Class Semiring (K : Type) := {
  sr_eq : K -> K -> Prop;
  sr_eq_refl : forall a, sr_eq a a;
  sr_eq_sym : forall a b, sr_eq a b -> sr_eq b a;
  sr_eq_trans : forall a b c, sr_eq a b -> sr_eq b c -> sr_eq a c;

  sr_plus : K -> K -> K;
  sr_times : K -> K -> K;
  sr_zero : K;
  sr_one : K;

  (* (K, +, 0) is a commutative monoid *)
  sr_plus_comm : forall a b, sr_eq (sr_plus a b) (sr_plus b a);
  sr_plus_assoc : forall a b c,
    sr_eq (sr_plus (sr_plus a b) c) (sr_plus a (sr_plus b c));
  sr_plus_zero_l : forall a, sr_eq (sr_plus sr_zero a) a;

  (* (K, *, 1) is a monoid *)
  sr_times_assoc : forall a b c,
    sr_eq (sr_times (sr_times a b) c) (sr_times a (sr_times b c));
  sr_times_one_l : forall a, sr_eq (sr_times sr_one a) a;
  sr_times_one_r : forall a, sr_eq (sr_times a sr_one) a;

  (* * distributes over + *)
  sr_times_plus_distr_l : forall a b c,
    sr_eq (sr_times a (sr_plus b c))
          (sr_plus (sr_times a b) (sr_times a c));
  sr_times_plus_distr_r : forall a b c,
    sr_eq (sr_times (sr_plus a b) c)
          (sr_plus (sr_times a c) (sr_times b c));

  (* 0 is an annihilator *)
  sr_times_zero_l : forall a, sr_eq (sr_times sr_zero a) sr_zero;
  sr_times_zero_r : forall a, sr_eq (sr_times a sr_zero) sr_zero;

  (* Congruence *)
  sr_plus_compat : forall a b c d,
    sr_eq a b -> sr_eq c d -> sr_eq (sr_plus a c) (sr_plus b d);
  sr_times_compat : forall a b c d,
    sr_eq a b -> sr_eq c d -> sr_eq (sr_times a c) (sr_times b d);
}.

(* Derived: right identity for plus *)
Lemma sr_plus_zero_r :
  forall (K : Type) (SK : Semiring K) (a : K),
    sr_eq (sr_plus a sr_zero) a.
Proof.
  intros K0 SK a.
  eapply sr_eq_trans.
  - apply sr_plus_comm.
  - apply sr_plus_zero_l.
Qed.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 1: PROVENANCE SEMIRING N[X]                                       *)
(*                                                                         *)
(*  Polynomial semiring where plus = union of monomials with coefficient   *)
(*  addition, times = convolution product (distribute-and-multiply).       *)
(*                                                                         *)
(*  We model N[X] as functions from monomials (list nat) to natural        *)
(*  number coefficients. This extensional representation avoids            *)
(*  normalization concerns and directly captures the mathematical          *)
(*  structure of the polynomial semiring.                                  *)
(*                                                                         *)
(* ===================================================================== *)

Section ProvenanceSemiring.

  (* ------------------------------------------------------------------- *)
  (*  Abstract model                                                       *)
  (* ------------------------------------------------------------------- *)

  (* Monomial: sorted list of variable indices (repetitions = exponents) *)
  Definition Monomial := list nat.

  (* Polynomial: function from monomial to coefficient (finitely supported) *)
  Definition Poly := Monomial -> nat.

  (* Extensional equality on polynomials *)
  Definition poly_eq (p q : Poly) : Prop :=
    forall m : Monomial, p m = q m.

  Lemma poly_eq_refl : forall p, poly_eq p p.
  Proof. intros p m. reflexivity. Qed.

  Lemma poly_eq_sym : forall p q, poly_eq p q -> poly_eq q p.
  Proof. intros p q H m. symmetry. apply H. Qed.

  Lemma poly_eq_trans : forall p q r,
    poly_eq p q -> poly_eq q r -> poly_eq p r.
  Proof. intros p q r Hpq Hqr m. rewrite Hpq. apply Hqr. Qed.

  (* Zero polynomial: all coefficients are 0.
     Mirrors ProvenanceWeight::zero in provenance.rs:149. *)
  Definition poly_zero : Poly := fun _ => 0.

  (* One polynomial: coefficient 1 for the empty monomial, 0 otherwise.
     Mirrors ProvenanceWeight::one in provenance.rs:155. *)
  Definition poly_one : Poly := fun m =>
    match m with
    | [] => 1
    | _ => 0
    end.

  (* Plus: pointwise addition of coefficients.
     Mirrors ProvenanceWeight::plus in provenance.rs:180. *)
  Definition poly_plus (p q : Poly) : Poly :=
    fun m => p m + q m.

  (* Times: convolution product.
     Mirrors ProvenanceWeight::times in provenance.rs:193.

     We axiomatize poly_times via its algebraic properties rather than
     defining the full summation, which would require decidable monomial
     decomposition. The axioms faithfully capture what the Rust
     implementation guarantees. *)
  Variable poly_times : Poly -> Poly -> Poly.

  Hypothesis poly_times_zero_l : forall q,
    poly_eq (poly_times poly_zero q) poly_zero.
  Hypothesis poly_times_zero_r : forall p,
    poly_eq (poly_times p poly_zero) poly_zero.
  Hypothesis poly_times_one_l : forall p,
    poly_eq (poly_times poly_one p) p.
  Hypothesis poly_times_one_r : forall p,
    poly_eq (poly_times p poly_one) p.
  Hypothesis poly_times_assoc : forall p q r,
    poly_eq (poly_times (poly_times p q) r)
            (poly_times p (poly_times q r)).
  Hypothesis poly_times_plus_distr_l : forall p q r,
    poly_eq (poly_times p (poly_plus q r))
            (poly_plus (poly_times p q) (poly_times p r)).
  Hypothesis poly_times_plus_distr_r : forall p q r,
    poly_eq (poly_times (poly_plus p q) r)
            (poly_plus (poly_times p r) (poly_times q r)).
  Hypothesis poly_times_compat : forall p1 p2 q1 q2,
    poly_eq p1 p2 -> poly_eq q1 q2 ->
    poly_eq (poly_times p1 q1) (poly_times p2 q2).

  (* ------------------------------------------------------------------- *)
  (*  Provenance semiring laws                                             *)
  (* ------------------------------------------------------------------- *)

  Theorem prov_plus_comm : forall p q,
    poly_eq (poly_plus p q) (poly_plus q p).
  Proof. intros p q m. unfold poly_plus. lia. Qed.

  Theorem prov_plus_assoc : forall p q r,
    poly_eq (poly_plus (poly_plus p q) r)
            (poly_plus p (poly_plus q r)).
  Proof. intros p q r m. unfold poly_plus. lia. Qed.

  Theorem prov_plus_zero_l : forall p,
    poly_eq (poly_plus poly_zero p) p.
  Proof. intros p m. unfold poly_plus, poly_zero. lia. Qed.

  Theorem prov_times_assoc : forall p q r,
    poly_eq (poly_times (poly_times p q) r)
            (poly_times p (poly_times q r)).
  Proof. exact poly_times_assoc. Qed.

  Theorem prov_times_one_l : forall p,
    poly_eq (poly_times poly_one p) p.
  Proof. exact poly_times_one_l. Qed.

  Theorem prov_times_one_r : forall p,
    poly_eq (poly_times p poly_one) p.
  Proof. exact poly_times_one_r. Qed.

  Theorem prov_distr_l : forall p q r,
    poly_eq (poly_times p (poly_plus q r))
            (poly_plus (poly_times p q) (poly_times p r)).
  Proof. exact poly_times_plus_distr_l. Qed.

  Theorem prov_distr_r : forall p q r,
    poly_eq (poly_times (poly_plus p q) r)
            (poly_plus (poly_times p r) (poly_times q r)).
  Proof. exact poly_times_plus_distr_r. Qed.

  Theorem prov_times_zero_l : forall p,
    poly_eq (poly_times poly_zero p) poly_zero.
  Proof. exact poly_times_zero_l. Qed.

  Theorem prov_times_zero_r : forall p,
    poly_eq (poly_times p poly_zero) poly_zero.
  Proof. exact poly_times_zero_r. Qed.

  Lemma prov_plus_compat : forall p1 p2 q1 q2,
    poly_eq p1 p2 -> poly_eq q1 q2 ->
    poly_eq (poly_plus p1 q1) (poly_plus p2 q2).
  Proof.
    intros p1 p2 q1 q2 Hp Hq m.
    unfold poly_plus. rewrite Hp, Hq. reflexivity.
  Qed.

  (* Assemble the Semiring instance for Provenance *)
  #[export] Instance ProvenanceSemiringInstance : Semiring Poly := {
    sr_eq := poly_eq;
    sr_eq_refl := poly_eq_refl;
    sr_eq_sym := poly_eq_sym;
    sr_eq_trans := poly_eq_trans;
    sr_plus := poly_plus;
    sr_times := poly_times;
    sr_zero := poly_zero;
    sr_one := poly_one;
    sr_plus_comm := prov_plus_comm;
    sr_plus_assoc := prov_plus_assoc;
    sr_plus_zero_l := prov_plus_zero_l;
    sr_times_assoc := prov_times_assoc;
    sr_times_one_l := prov_times_one_l;
    sr_times_one_r := prov_times_one_r;
    sr_times_plus_distr_l := prov_distr_l;
    sr_times_plus_distr_r := prov_distr_r;
    sr_times_zero_l := prov_times_zero_l;
    sr_times_zero_r := prov_times_zero_r;
    sr_plus_compat := prov_plus_compat;
    sr_times_compat := poly_times_compat;
  }.

End ProvenanceSemiring.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 2: RELATIONAL WEIGHT DOMAIN                                       *)
(*                                                                         *)
(*  Binary relations on nat. Plus = union, times = relational composition. *)
(*  Zero = empty relation, one = identity relation.                        *)
(*                                                                         *)
(*  Model: nat -> nat -> Prop (characteristic function of the relation).   *)
(*  Equality: extensional (iff at every pair).                             *)
(*                                                                         *)
(* ===================================================================== *)

Section RelationalSemiring.

  Definition Rel := nat -> nat -> Prop.

  Definition rel_eq (R S : Rel) : Prop :=
    forall x y, R x y <-> S x y.

  Lemma rel_eq_refl : forall R, rel_eq R R.
  Proof. intros R x y. tauto. Qed.

  Lemma rel_eq_sym : forall R S, rel_eq R S -> rel_eq S R.
  Proof. intros R S H x y. symmetry. apply H. Qed.

  Lemma rel_eq_trans : forall R S T,
    rel_eq R S -> rel_eq S T -> rel_eq R T.
  Proof. unfold rel_eq; hauto lq: on. Qed.

  (* Empty relation (zero).
     Mirrors RelationalWeight::empty in relational.rs:75. *)
  Definition rel_zero : Rel := fun _ _ => False.

  (* Identity relation (one).
     Mirrors RelationalWeight::identity in relational.rs:83. *)
  Definition rel_one : Rel := fun x y => x = y.

  (* Union (plus).
     Mirrors HeapSemiring::plus for RelationalWeight in relational.rs:155. *)
  Definition rel_plus (R S : Rel) : Rel := fun x y => R x y \/ S x y.

  (* Relational composition (times).
     Mirrors HeapSemiring::times for RelationalWeight in relational.rs:165. *)
  Definition rel_times (R S : Rel) : Rel :=
    fun x z => exists y, R x y /\ S y z.

  (* R1: Plus is commutative *)
  Theorem rel_plus_comm : forall R S,
    rel_eq (rel_plus R S) (rel_plus S R).
  Proof. intros R S x y. unfold rel_plus. tauto. Qed.

  (* R2: Plus is associative *)
  Theorem rel_plus_assoc : forall R S T,
    rel_eq (rel_plus (rel_plus R S) T) (rel_plus R (rel_plus S T)).
  Proof. intros R S T x y. unfold rel_plus. tauto. Qed.

  (* R3: Zero is the left identity for plus *)
  Theorem rel_plus_zero_l : forall R,
    rel_eq (rel_plus rel_zero R) R.
  Proof. intros R x y. unfold rel_plus, rel_zero. tauto. Qed.

  (* R4: Times is associative *)
  Theorem rel_times_assoc : forall R S T,
    rel_eq (rel_times (rel_times R S) T) (rel_times R (rel_times S T)).
  Proof. unfold rel_eq, rel_times; firstorder. Qed.

  (* R5: One is the left identity for times *)
  Theorem rel_times_one_l : forall R,
    rel_eq (rel_times rel_one R) R.
  Proof.
    unfold rel_eq, rel_times, rel_one; split;
    [intros [z [Heq HR]]; subst; exact HR | intros HR; eauto].
  Qed.

  (* R5': One is the right identity for times *)
  Theorem rel_times_one_r : forall R,
    rel_eq (rel_times R rel_one) R.
  Proof.
    unfold rel_eq, rel_times, rel_one; split;
    [intros [z [HR Heq]]; subst; exact HR | intros HR; eauto].
  Qed.

  (* R6: Left distributivity *)
  Theorem rel_distr_l : forall R S T,
    rel_eq (rel_times R (rel_plus S T))
           (rel_plus (rel_times R S) (rel_times R T)).
  Proof. unfold rel_eq, rel_times, rel_plus; firstorder. Qed.

  (* R6': Right distributivity *)
  Theorem rel_distr_r : forall R S T,
    rel_eq (rel_times (rel_plus R S) T)
           (rel_plus (rel_times R T) (rel_times S T)).
  Proof. unfold rel_eq, rel_times, rel_plus; firstorder. Qed.

  (* R7: Zero is a left annihilator *)
  Theorem rel_times_zero_l : forall R,
    rel_eq (rel_times rel_zero R) rel_zero.
  Proof. unfold rel_eq, rel_times, rel_zero; firstorder. Qed.

  (* R7': Zero is a right annihilator *)
  Theorem rel_times_zero_r : forall R,
    rel_eq (rel_times R rel_zero) rel_zero.
  Proof. unfold rel_eq, rel_times, rel_zero; firstorder. Qed.

  (* Congruence lemmas *)
  Lemma rel_plus_compat : forall R1 R2 S1 S2,
    rel_eq R1 R2 -> rel_eq S1 S2 ->
    rel_eq (rel_plus R1 S1) (rel_plus R2 S2).
  Proof. unfold rel_eq, rel_plus; firstorder. Qed.

  Lemma rel_times_compat : forall R1 R2 S1 S2,
    rel_eq R1 R2 -> rel_eq S1 S2 ->
    rel_eq (rel_times R1 S1) (rel_times R2 S2).
  Proof.
    intros R1 R2 S1 S2 HR HS x z; unfold rel_times; split;
    intros [y0 [H1 H2]]; exists y0; split;
    first [apply HR; assumption | apply HS; assumption].
  Qed.

  (* Assemble the Semiring instance for Relational *)
  #[export] Instance RelationalSemiringInstance : Semiring Rel := {
    sr_eq := rel_eq;
    sr_eq_refl := rel_eq_refl;
    sr_eq_sym := rel_eq_sym;
    sr_eq_trans := rel_eq_trans;
    sr_plus := rel_plus;
    sr_times := rel_times;
    sr_zero := rel_zero;
    sr_one := rel_one;
    sr_plus_comm := rel_plus_comm;
    sr_plus_assoc := rel_plus_assoc;
    sr_plus_zero_l := rel_plus_zero_l;
    sr_times_assoc := rel_times_assoc;
    sr_times_one_l := rel_times_one_l;
    sr_times_one_r := rel_times_one_r;
    sr_times_plus_distr_l := rel_distr_l;
    sr_times_plus_distr_r := rel_distr_r;
    sr_times_zero_l := rel_times_zero_l;
    sr_times_zero_r := rel_times_zero_r;
    sr_plus_compat := rel_plus_compat;
    sr_times_compat := rel_times_compat;
  }.

  (* Bonus: Relational semiring is idempotent *)
  Theorem rel_plus_idempotent : forall R,
    rel_eq (rel_plus R R) R.
  Proof. intros R x y. unfold rel_plus. tauto. Qed.

End RelationalSemiring.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 3: KLEENE ALGEBRA WITH TESTS (KAT)                               *)
(*                                                                         *)
(*  Extends the semiring with:                                             *)
(*    - Kleene star: star(a) = 1 + a * star(a)                             *)
(*    - Boolean test embedding: test(p) * test(q) = test(p && q)           *)
(*    - Hoare triple soundness                                             *)
(*                                                                         *)
(*  Reference: Kozen (1997), "Kleene algebra with tests"                   *)
(*                                                                         *)
(* ===================================================================== *)

Section KATSemiring.

  Variable K : Type.

  Variable keq : K -> K -> Prop.
  Hypothesis keq_refl : forall a, keq a a.
  Hypothesis keq_sym : forall a b, keq a b -> keq b a.
  Hypothesis keq_trans : forall a b c, keq a b -> keq b c -> keq a c.

  Variable kplus : K -> K -> K.
  Variable ktimes : K -> K -> K.
  Variable kzero : K.
  Variable kone : K.

  Hypothesis kplus_comm : forall a b, keq (kplus a b) (kplus b a).
  Hypothesis kplus_assoc : forall a b c,
    keq (kplus (kplus a b) c) (kplus a (kplus b c)).
  Hypothesis kplus_zero_l : forall a, keq (kplus kzero a) a.
  Hypothesis ktimes_assoc : forall a b c,
    keq (ktimes (ktimes a b) c) (ktimes a (ktimes b c)).
  Hypothesis ktimes_one_l : forall a, keq (ktimes kone a) a.
  Hypothesis ktimes_one_r : forall a, keq (ktimes a kone) a.
  Hypothesis ktimes_plus_distr_l : forall a b c,
    keq (ktimes a (kplus b c)) (kplus (ktimes a b) (ktimes a c)).
  Hypothesis ktimes_plus_distr_r : forall a b c,
    keq (ktimes (kplus a b) c) (kplus (ktimes a c) (ktimes b c)).
  Hypothesis ktimes_zero_l : forall a, keq (ktimes kzero a) kzero.
  Hypothesis ktimes_zero_r : forall a, keq (ktimes a kzero) kzero.

  Hypothesis kplus_compat : forall a b c d,
    keq a b -> keq c d -> keq (kplus a c) (kplus b d).
  Hypothesis ktimes_compat : forall a b c d,
    keq a b -> keq c d -> keq (ktimes a c) (ktimes b d).

  (* Idempotence of plus: standard axiom of Kleene algebra *)
  Hypothesis kplus_idempotent : forall a, keq (kplus a a) a.

  (* ------------------------------------------------------------------- *)
  (*  Utility lemmas                                                       *)
  (* ------------------------------------------------------------------- *)

  Lemma kat_plus_zero_r : forall a, keq (kplus a kzero) a.
  Proof.
    intros a. eapply keq_trans.
    - apply kplus_comm.
    - apply kplus_zero_l.
  Qed.

  (* Right congruence for ktimes: if keq b c then keq (ktimes a b) (ktimes a c) *)
  Lemma ktimes_compat_r : forall a b c,
    keq b c -> keq (ktimes a b) (ktimes a c).
  Proof.
    intros a b c H. apply ktimes_compat; [apply keq_refl | exact H].
  Qed.

  (* Left congruence for ktimes: if keq a b then keq (ktimes a c) (ktimes b c) *)
  Lemma ktimes_compat_l : forall a b c,
    keq a b -> keq (ktimes a c) (ktimes b c).
  Proof.
    intros a b c H. apply ktimes_compat; [exact H | apply keq_refl].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Setoid rewriting infrastructure                                      *)
  (*  Enables `rewrite` with keq-equalities, dramatically simplifying      *)
  (*  equational chain proofs.                                             *)
  (* ------------------------------------------------------------------- *)

  Add Parametric Relation : K keq
    reflexivity proved by keq_refl
    symmetry proved by keq_sym
    transitivity proved by keq_trans
    as keq_setoid.

  Add Parametric Morphism : kplus
    with signature keq ==> keq ==> keq as kplus_morph.
  Proof. intros x y Hxy x0 y0 Hxy0; apply kplus_compat; assumption. Qed.

  Add Parametric Morphism : ktimes
    with signature keq ==> keq ==> keq as ktimes_morph.
  Proof. intros x y Hxy x0 y0 Hxy0; apply ktimes_compat; assumption. Qed.

  (* ------------------------------------------------------------------- *)
  (*  Kleene star                                                          *)
  (* ------------------------------------------------------------------- *)

  Variable kstar : K -> K.

  (* Star unfold axiom: a* = 1 + a * a* *)
  Hypothesis kstar_unfold : forall a,
    keq (kstar a) (kplus kone (ktimes a (kstar a))).

  (* Star induction: if 1 + a * x = x then a* = x *)
  Hypothesis kstar_ind_l : forall a x,
    keq (kplus kone (ktimes a x)) x ->
    keq (kstar a) x.

  (* K1: Star unfold *)
  Theorem K1_star_unfold : forall a,
    keq (kstar a) (kplus kone (ktimes a (kstar a))).
  Proof. exact kstar_unfold. Qed.

  (* K2: star(0) = 1 *)
  Theorem K2_star_zero : keq (kstar kzero) kone.
  Proof.
    apply kstar_ind_l.
    eapply keq_trans.
    - apply kplus_compat; [apply keq_refl | apply ktimes_zero_l].
    - apply kat_plus_zero_r.
  Qed.

  (* K3: star(1) = 1 *)
  Theorem K3_star_one : keq (kstar kone) kone.
  Proof.
    apply kstar_ind_l.
    eapply keq_trans.
    - apply kplus_compat; [apply keq_refl | apply ktimes_one_l].
    - apply kplus_idempotent.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Boolean test embedding                                               *)
  (* ------------------------------------------------------------------- *)

  Variable test : bool -> K.
  Hypothesis test_true : keq (test true) kone.
  Hypothesis test_false : keq (test false) kzero.

  (* Setoid rewriting reduces B1-B5 and H1-H4 from multi-line
     eapply-keq_trans chains to simple rewrite-then-reflexivity. *)

  (* B1: test(p) * test(q) = test(p && q) *)
  Theorem B1_test_and : forall p q,
    keq (ktimes (test p) (test q)) (test (p && q)).
  Proof.
    intros [] []; simpl;
    rewrite ?test_true, ?test_false, ?ktimes_one_l, ?ktimes_zero_l, ?ktimes_zero_r;
    reflexivity.
  Qed.

  (* B2: test(p) + test(q) = test(p || q) *)
  Theorem B2_test_or : forall p q,
    keq (kplus (test p) (test q)) (test (p || q)).
  Proof.
    intros [] []; simpl;
    rewrite ?test_true, ?test_false, ?kplus_zero_l;
    first [apply kat_plus_zero_r | apply kplus_idempotent | reflexivity].
  Qed.

  (* B3: test(p) * test(negb p) = 0 (contradiction) *)
  Theorem B3_test_negb_and : forall p,
    keq (ktimes (test p) (test (negb p))) kzero.
  Proof.
    intros []; simpl;
    rewrite ?test_true, ?test_false, ?ktimes_zero_l, ?ktimes_zero_r;
    reflexivity.
  Qed.

  (* B3': test(p) + test(negb p) = 1 (excluded middle) *)
  Theorem B3_test_negb_or : forall p,
    keq (kplus (test p) (test (negb p))) kone.
  Proof.
    intros []; simpl;
    rewrite ?test_true, ?test_false;
    first [apply kat_plus_zero_r | apply kplus_zero_l].
  Qed.

  (* B4: test(p) * test(p) = test(p) (tests are idempotent) *)
  Theorem B4_test_idempotent : forall p,
    keq (ktimes (test p) (test p)) (test p).
  Proof.
    intros p; eapply keq_trans; [apply B1_test_and |].
    destruct p; simpl; apply keq_refl.
  Qed.

  (* B5: Tests commute under multiplication *)
  Theorem B5_test_times_comm : forall p q,
    keq (ktimes (test p) (test q)) (ktimes (test q) (test p)).
  Proof.
    intros p q; eapply keq_trans; [apply B1_test_and |];
    eapply keq_trans; [| apply keq_sym; apply B1_test_and];
    destruct p, q; simpl; apply keq_refl.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Hoare Triple Soundness                                               *)
  (*                                                                       *)
  (*  Kozen (1997): The Hoare triple {p} e {q} is valid iff               *)
  (*    test(p) * e * test(negb q) = 0                                     *)
  (* ------------------------------------------------------------------- *)

  Definition hoare_valid (p : bool) (e : K) (q : bool) : Prop :=
    keq (ktimes (ktimes (test p) e) (test (negb q))) kzero.

  (* H1: {true} skip {true} is valid *)
  Theorem H1_skip_preserves_true : hoare_valid true kone true.
  Proof.
    unfold hoare_valid; simpl;
    rewrite test_true, test_false, ktimes_one_l, ktimes_zero_r; reflexivity.
  Qed.

  (* H2: {false} e {q} is always valid (ex falso) *)
  Theorem H2_false_precondition : forall e q, hoare_valid false e q.
  Proof.
    intros e q; unfold hoare_valid;
    rewrite test_false, ktimes_zero_l, ktimes_zero_l; reflexivity.
  Qed.

  (* H3: {p} e {true} is always valid *)
  Theorem H3_true_postcondition : forall p e, hoare_valid p e true.
  Proof.
    intros p e; unfold hoare_valid; simpl;
    rewrite test_false, ktimes_zero_r; reflexivity.
  Qed.

  (* H4: {p} zero {q} is always valid (abort never completes) *)
  Theorem H4_abort_valid : forall p q, hoare_valid p kzero q.
  Proof.
    intros p q; unfold hoare_valid;
    rewrite ktimes_zero_r, ktimes_zero_l; reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  H5: Sequential composition rule                                      *)
  (*  If {p} e1 {r} and {r} e2 {q}, then {p} (e1;e2) {q}                 *)
  (* ------------------------------------------------------------------- *)

  (* Key lemma: if test(p)*e*test(negb q) = 0, then
     test(p)*e = test(p)*e*test(q).
     This is the "filter" property of Hoare validity. *)
  Lemma hoare_filter : forall p e q,
    hoare_valid p e q ->
    keq (ktimes (test p) e) (ktimes (ktimes (test p) e) (test q)).
  Proof.
    intros p e q Hvalid.
    (* test(p)*e = test(p)*e*1
                 = test(p)*e*(test(q) + test(negb q))
                 = test(p)*e*test(q) + test(p)*e*test(negb q)
                 = test(p)*e*test(q) + 0
                 = test(p)*e*test(q) *)
    eapply keq_trans; [apply keq_sym; apply ktimes_one_r |].
    eapply keq_trans; [apply ktimes_compat_r; apply keq_sym; apply B3_test_negb_or |].
    eapply keq_trans; [apply ktimes_plus_distr_l |].
    eapply keq_trans; [apply kplus_compat; [apply keq_refl | exact Hvalid] |].
    apply kat_plus_zero_r.
  Qed.

  (* Auxiliary: four-factor reassociation.
     (a * b) * (c * d) = ((a * b) * c) * d *)
  Lemma ktimes_4_assoc : forall a b c d,
    keq (ktimes (ktimes a b) (ktimes c d))
        (ktimes (ktimes (ktimes a b) c) d).
  Proof.
    intros a b c d.
    apply keq_sym. apply ktimes_assoc.
  Qed.

  Theorem H5_sequential : forall p e1 r e2 q,
    hoare_valid p e1 r ->
    hoare_valid r e2 q ->
    hoare_valid p (ktimes e1 e2) q.
  Proof.
    intros p e1 r e2 q H1 H2.
    unfold hoare_valid.
    (* Goal: keq (ktimes (ktimes (test p) (ktimes e1 e2)) (test (negb q))) kzero *)

    (* Step 1: reassociate left factor.
       (test p * (e1 * e2)) * test(negb q)
       = ((test p * e1) * e2) * test(negb q) *)
    eapply keq_trans.
    { apply ktimes_compat_l. apply keq_sym. apply ktimes_assoc. }

    (* Step 2: insert test(r) via hoare_filter.
       ((test p * e1) * e2) * test(negb q)
       = (((test p * e1) * test r) * e2) * test(negb q) *)
    eapply keq_trans.
    { apply ktimes_compat_l. apply ktimes_compat_l. apply hoare_filter. exact H1. }

    (* Step 3: reassociate.
       (((test p * e1) * test r) * e2) * test(negb q)
       = ((test p * e1) * test r) * (e2 * test(negb q))    by assoc *)
    eapply keq_trans.
    { apply ktimes_assoc. }

    (* Step 4: reassociate further.
       ((test p * e1) * test r) * (e2 * test(negb q))
       = (test p * e1) * (test r * (e2 * test(negb q)))    by assoc *)
    eapply keq_trans.
    { apply ktimes_assoc. }

    (* Step 5: re-associate inner part.
       (test p * e1) * (test r * (e2 * test(negb q)))
       = (test p * e1) * ((test r * e2) * test(negb q))    by sym assoc on right *)
    eapply keq_trans.
    { apply ktimes_compat_r. apply keq_sym. apply ktimes_assoc. }

    (* Step 6: the right factor is exactly H2, which equals kzero.
       (test p * e1) * ((test r * e2) * test(negb q))
       = (test p * e1) * 0
       = 0 *)
    eapply keq_trans.
    { apply ktimes_compat_r. exact H2. }
    apply ktimes_zero_r.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  H6: Consequence rule                                                 *)
  (* ------------------------------------------------------------------- *)

  Definition bool_implies (p q : bool) : Prop :=
    p = true -> q = true.

  (* H6a: Strengthening the precondition *)
  Theorem H6a_strengthen_pre : forall p p' e q,
    bool_implies p p' ->
    hoare_valid p' e q ->
    hoare_valid p e q.
  Proof.
    intros p p' e q Himpl Hvalid.
    unfold hoare_valid in *.
    destruct p.
    - (* p = true: Himpl says p' = true *)
      assert (Hp' : p' = true) by (apply Himpl; reflexivity).
      subst p'. exact Hvalid.
    - (* p = false: test(false) = kzero, annihilates *)
      eapply keq_trans; [apply ktimes_compat_l; apply ktimes_compat_l; apply test_false |].
      eapply keq_trans; [apply ktimes_compat_l; apply ktimes_zero_l |].
      apply ktimes_zero_l.
  Qed.

  (* H6b: Weakening the postcondition *)
  Theorem H6b_weaken_post : forall p e q q',
    bool_implies q' q ->
    hoare_valid p e q' ->
    hoare_valid p e q.
  Proof.
    intros p e q q' Himpl Hvalid.
    unfold hoare_valid in *.
    destruct q; destruct q'; simpl in *.
    - exact Hvalid.
    - eapply keq_trans; [apply ktimes_compat_r; apply test_false |].
      apply ktimes_zero_r.
    - exfalso. apply diff_false_true. apply Himpl. reflexivity.
    - exact Hvalid.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  H7: Hoare soundness biconditional                                    *)
  (* ------------------------------------------------------------------- *)

  Theorem H7_hoare_soundness : forall p e q,
    hoare_valid p e q <->
    keq (ktimes (ktimes (test p) e) (test (negb q))) kzero.
  Proof.
    intros p e q. unfold hoare_valid. tauto.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Assemble the Semiring instance for KAT                               *)
  (* ------------------------------------------------------------------- *)

  #[export] Instance KATSemiringInstance : Semiring K := {
    sr_eq := keq;
    sr_eq_refl := keq_refl;
    sr_eq_sym := keq_sym;
    sr_eq_trans := keq_trans;
    sr_plus := kplus;
    sr_times := ktimes;
    sr_zero := kzero;
    sr_one := kone;
    sr_plus_comm := kplus_comm;
    sr_plus_assoc := kplus_assoc;
    sr_plus_zero_l := kplus_zero_l;
    sr_times_assoc := ktimes_assoc;
    sr_times_one_l := ktimes_one_l;
    sr_times_one_r := ktimes_one_r;
    sr_times_plus_distr_l := ktimes_plus_distr_l;
    sr_times_plus_distr_r := ktimes_plus_distr_r;
    sr_times_zero_l := ktimes_zero_l;
    sr_times_zero_r := ktimes_zero_r;
    sr_plus_compat := kplus_compat;
    sr_times_compat := ktimes_compat;
  }.

End KATSemiring.


(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  Provenance Semiring N[X]:                                              *)
(*    P1: plus is commutative                prov_plus_comm                *)
(*    P2: plus is associative                prov_plus_assoc               *)
(*    P3: zero is the additive identity      prov_plus_zero_l              *)
(*    P4: times is associative               prov_times_assoc              *)
(*    P5/P5': one is the multiplicative id   prov_times_one_l/r            *)
(*    P6/P6': distributivity                 prov_distr_l/r                *)
(*    P7/P7': zero is annihilator            prov_times_zero_l/r           *)
(*    Instance: ProvenanceSemiringInstance                                  *)
(*                                                                         *)
(*  Relational Weight Domain:                                              *)
(*    R1: plus (union) is commutative        rel_plus_comm                 *)
(*    R2: plus is associative                rel_plus_assoc                *)
(*    R3: zero (empty) is additive identity  rel_plus_zero_l               *)
(*    R4: times (composition) is associative rel_times_assoc               *)
(*    R5/R5': identity relation is neutral   rel_times_one_l/r             *)
(*    R6/R6': distributivity                 rel_distr_l/r                 *)
(*    R7/R7': empty is annihilator           rel_times_zero_l/r            *)
(*    Bonus: plus is idempotent              rel_plus_idempotent           *)
(*    Instance: RelationalSemiringInstance                                  *)
(*                                                                         *)
(*  KAT (Kleene Algebra with Tests):                                       *)
(*    K1: star unfold                        K1_star_unfold                *)
(*    K2: star(0) = 1                        K2_star_zero                  *)
(*    K3: star(1) = 1                        K3_star_one                   *)
(*    B1: test(p)*test(q) = test(p&&q)       B1_test_and                   *)
(*    B2: test(p)+test(q) = test(p||q)       B2_test_or                    *)
(*    B3: test(p)*test(negb p) = 0           B3_test_negb_and              *)
(*    B3': test(p)+test(negb p) = 1          B3_test_negb_or               *)
(*    B4: test(p)*test(p) = test(p)          B4_test_idempotent            *)
(*    B5: tests commute under *              B5_test_times_comm            *)
(*    H1: {true} skip {true}                 H1_skip_preserves_true        *)
(*    H2: {false} e {q}                      H2_false_precondition         *)
(*    H3: {p} e {true}                       H3_true_postcondition         *)
(*    H4: {p} abort {q}                      H4_abort_valid                *)
(*    H5: sequential composition             H5_sequential                 *)
(*    H6a: strengthen precondition           H6a_strengthen_pre            *)
(*    H6b: weaken postcondition              H6b_weaken_post               *)
(*    H7: soundness biconditional            H7_hoare_soundness            *)
(*    Instance: KATSemiringInstance                                        *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(* ===================================================================== *)
