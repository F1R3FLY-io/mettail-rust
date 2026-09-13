(** Comparison classes for the existing generated native comparator.

    Identity and binder comparisons use deterministic hash results, so distinct
    terms can occupy the same ordering class. A proof-only view maps terms to
    class keys; it need not be injective. Laws of key comparison transfer to
    the term comparison only through its exact factorization equation.
    They never identify term Eq with a comparison result of Equal.

    The existing SemanticComparisonLaws supplies numeric, product, sum and
    list ordering. These adapters reuse those definitions and proofs rather
    than introducing another runtime comparator, allocated key or rank table.
    Actual constructor/field factorization and nested Map induction remain
    separate source obligations. These conditional composition lemmas alone
    do not certify all Proc constructors or arbitrary native callbacks. *)
From Stdlib Require Import List Arith.PeanoNat.
From RuntimeGrammar Require Import SemanticComparisonLaws.

Module AdmittedComparisonClasses.

Section ClassView.
Context {Term Key : Type}.
Variable compare : Term -> Term -> comparison.
Variable key_compare : Key -> Key -> comparison.
Variable view : Term -> Key.
Hypothesis key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws key_compare.
Hypothesis factor : forall x y, compare x y = key_compare (view x) (view y).

Theorem class_equality : forall x y, compare x y = Eq <-> view x = view y.
Proof.
  intros x y. rewrite factor.
  apply (SemanticComparisonLaws.SemanticComparisonLaws.comparison_eq key_laws).
Qed.
Theorem class_reflexivity : forall x, compare x x = Eq.
Proof. intro x. apply class_equality. reflexivity. Qed.
Theorem class_opposite : forall x y, compare y x = CompOpp (compare x y).
Proof.
  intros x y. rewrite !factor.
  apply (SemanticComparisonLaws.SemanticComparisonLaws.comparison_opposite key_laws).
Qed.
Theorem class_congruence_left : forall x y z,
  compare x y = Eq -> compare x z = compare y z.
Proof. intros x y z E. apply class_equality in E. rewrite !factor. now rewrite E. Qed.
Theorem class_congruence_right : forall x y z,
  compare y z = Eq -> compare x y = compare x z.
Proof. intros x y z E. apply class_equality in E. rewrite !factor. now rewrite E. Qed.
Theorem class_transitivity : forall x y z c,
  compare x y = c -> compare y z = c -> compare x z = c.
Proof.
  intros x y z c H1 H2. rewrite factor in H1, H2 |- *.
  exact (SemanticComparisonLaws.SemanticComparisonLaws.comparison_transitive
    key_laws _ _ _ c H1 H2).
Qed.
Theorem class_not_greater_transitivity : forall x y z,
  compare x y <> Gt -> compare y z <> Gt -> compare x z <> Gt.
Proof.
  intros x y z H1 H2. rewrite factor in H1, H2 |- *.
  exact (SemanticComparisonLaws.SemanticComparisonLaws.not_greater_is_transitive
    Key key_compare key_laws _ _ _ H1 H2).
Qed.
Theorem class_not_greater_totality : forall x y,
  compare x y <> Gt \/ compare y x <> Gt.
Proof.
  intros x y. rewrite !factor.
  exact (SemanticComparisonLaws.SemanticComparisonLaws.not_greater_is_total
    Key key_compare key_laws _ _).
Qed.
End ClassView.

Theorem pair_factor : forall (A B K J : Type)
  (ca : A -> A -> comparison) (cb : B -> B -> comparison)
  (ck : K -> K -> comparison) (cj : J -> J -> comparison)
  (va : A -> K) (vb : B -> J),
  (forall x y, ca x y = ck (va x) (va y)) ->
  (forall x y, cb x y = cj (vb x) (vb y)) ->
  forall x y,
  SemanticComparisonLaws.SemanticComparisonLaws.pair_compare ca cb x y =
  SemanticComparisonLaws.SemanticComparisonLaws.pair_compare ck cj
    (va (fst x), vb (snd x)) (va (fst y), vb (snd y)).
Proof.
  intros A B K J ca cb ck cj va vb FA FB [a b] [c d].
  unfold SemanticComparisonLaws.SemanticComparisonLaws.pair_compare; cbn.
  now rewrite FA, FB.
Qed.
Theorem list_factor : forall (A K : Type)
  (ca : A -> A -> comparison) (ck : K -> K -> comparison)
  (view : A -> K),
  (forall x y, ca x y = ck (view x) (view y)) ->
  forall xs ys,
  list_compare ca xs ys = list_compare ck (map view xs) (map view ys).
Proof.
  intros A K ca ck view F xs. induction xs as [|x xs IH];
    intros [|y ys]; cbn; try reflexivity.
  rewrite F, IH. reflexivity.
Qed.
Definition sum_view {A B K J : Type} (va : A -> K) (vb : B -> J)
  (x : A + B) : K + J :=
  match x with inl a => inl (va a) | inr b => inr (vb b) end.
Theorem sum_factor : forall (A B K J : Type)
  (ca : A -> A -> comparison) (cb : B -> B -> comparison)
  (ck : K -> K -> comparison) (cj : J -> J -> comparison)
  (va : A -> K) (vb : B -> J),
  (forall x y, ca x y = ck (va x) (va y)) ->
  (forall x y, cb x y = cj (vb x) (vb y)) ->
  forall x y, SemanticComparisonLaws.SemanticComparisonLaws.sum_compare ca cb x y =
  SemanticComparisonLaws.SemanticComparisonLaws.sum_compare ck cj
    (sum_view va vb x) (sum_view va vb y).
Proof.
  intros A B K J ca cb ck cj va vb FA FB [a|b] [c|d];
    cbn [SemanticComparisonLaws.SemanticComparisonLaws.sum_compare sum_view]; auto.
Qed.

(** This logical witness demonstrates non-injectivity is permitted. It is not
    a claim to have constructed a collision in the runtime's native hasher. *)
Theorem equal_class_keys_need_not_identify_source_values :
  (fun _ : nat => 0) 1 = (fun _ : nat => 0) 2 /\ 1 <> 2.
Proof. split; [reflexivity|discriminate]. Qed.

Print Assumptions class_equality.
Print Assumptions class_reflexivity.
Print Assumptions class_opposite.
Print Assumptions class_congruence_left.
Print Assumptions class_congruence_right.
Print Assumptions class_transitivity.
Print Assumptions class_not_greater_transitivity.
Print Assumptions class_not_greater_totality.
Print Assumptions pair_factor.
Print Assumptions list_factor.
Print Assumptions sum_factor.
Print Assumptions equal_class_keys_need_not_identify_source_values.
End AdmittedComparisonClasses.
