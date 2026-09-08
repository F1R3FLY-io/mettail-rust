(** Small composition adapters for the fixed neutral-receipt schema.

    List ordering and all its laws are reused from Stdlib.List. Products use
    the same first-field-then-second-field comparison as PairOrderedType, with
    ordinary tuple equality rather than its componentwise setoid interface.
    The lexicographic transitivity proof is adapted from the isolated node's
    RuntimeBudgetRefinement.v, lexc_trans, rather than expanded per receipt.

    Tagged sums model the finite premise/resource alternatives. These are
    proof-only typed views; the runtime compares borrowed fields directly.
    No generic recursive Value comparator or allocated comparison key is added. *)
From Stdlib Require Import List Arith.PeanoNat Lia.

Module SemanticComparisonLaws.

Record Laws {A : Type} (compare : A -> A -> comparison) : Prop := {
  comparison_eq : forall x y, compare x y = Eq <-> x = y;
  comparison_opposite : forall x y, compare y x = CompOpp (compare x y);
  comparison_transitive : forall x y z c,
    compare x y = c -> compare y z = c -> compare x z = c
}.
Arguments comparison_eq {A compare} _ _ _.
Arguments comparison_opposite {A compare} _ _ _.
Arguments comparison_transitive {A compare} _ _ _ _ _ _ _.

Theorem natural_laws : Laws Nat.compare.
Proof.
  constructor; [apply Nat.compare_eq_iff | apply Nat.compare_antisym |].
  intros x y z c H1 H2. destruct c.
  - apply Nat.compare_eq_iff in H1, H2. apply Nat.compare_eq_iff. congruence.
  - apply Nat.compare_lt_iff in H1, H2. apply Nat.compare_lt_iff. lia.
  - apply Nat.compare_gt_iff in H1, H2. apply Nat.compare_gt_iff. lia.
Qed.

Theorem list_laws : forall (A : Type) (compare : A -> A -> comparison),
  Laws compare -> Laws (list_compare compare).
Proof.
  intros A compare laws. constructor.
  - apply list_compare_refl. apply (comparison_eq laws).
  - intros x y. apply list_compare_antisym;
      [apply (comparison_eq laws) | apply (comparison_opposite laws)].
  - intros x y z c. apply list_compare_trans;
      [apply (comparison_eq laws) | apply (comparison_transitive laws) |
       apply (comparison_opposite laws)].
Qed.

Definition lex first second := match first with Eq => second | _ => first end.

Lemma lex_transitive : forall (T : Type) (f g : T -> T -> comparison),
  (forall c x y z, f x y = c -> f y z = c -> f x z = c) ->
  (forall x y z, f x y = Eq -> f x z = f y z) ->
  (forall x y z, f y z = Eq -> f x z = f x y) ->
  (forall c x y z, g x y = c -> g y z = c -> g x z = c) ->
  forall c x y z,
    lex (f x y) (g x y) = c -> lex (f y z) (g y z) = c ->
    lex (f x z) (g x z) = c.
Proof.
  intros T f g f_trans f_cong_l f_cong_r g_trans c x y z H1 H2.
  unfold lex in *.
  destruct (f x y) eqn:Hxy; destruct (f y z) eqn:Hyz.
  - rewrite (f_trans Eq x y z Hxy Hyz). apply (g_trans c x y z H1 H2).
  - rewrite (f_cong_l x y z Hxy), Hyz. exact H2.
  - rewrite (f_cong_l x y z Hxy), Hyz. exact H2.
  - rewrite (f_cong_r x y z Hyz), Hxy. exact H1.
  - rewrite (f_trans Lt x y z Hxy Hyz). exact H1.
  - subst c; discriminate.
  - rewrite (f_cong_r x y z Hyz), Hxy. exact H1.
  - subst c; discriminate.
  - rewrite (f_trans Gt x y z Hxy Hyz). exact H1.
Qed.

Definition pair_compare {A B : Type} (first : A -> A -> comparison)
    (second : B -> B -> comparison) (x y : A * B) :=
  lex (first (fst x) (fst y)) (second (snd x) (snd y)).

Theorem pair_laws : forall (A B : Type) first second,
  @Laws A first -> @Laws B second -> Laws (pair_compare first second).
Proof.
  intros A B first second F S. constructor.
  - intros [a b] [c d]. unfold pair_compare; cbn. split.
    + unfold lex. destruct (first a c) eqn:E; try discriminate.
      intro H. apply (comparison_eq F) in E. apply (comparison_eq S) in H.
      congruence.
    + intro E. inversion E; subst.
      rewrite (proj2 (comparison_eq F c c) eq_refl).
      apply (proj2 (comparison_eq S d d) eq_refl).
  - intros [a b] [c d]. unfold pair_compare; cbn.
    rewrite (comparison_opposite F a c), (comparison_opposite S b d).
    unfold lex. destruct (first a c); reflexivity.
  - intros x y z c. unfold pair_compare.
    eapply (lex_transitive (A * B) (fun a b => first (fst a) (fst b))
      (fun a b => second (snd a) (snd b))).
    + intros decision a b d. apply (comparison_transitive F).
    + intros a b d E. apply (comparison_eq F) in E. now rewrite E.
    + intros a b d E. apply (comparison_eq F) in E. now rewrite E.
    + intros decision a b d. apply (comparison_transitive S).
Qed.

Definition sum_compare {A B : Type} (first : A -> A -> comparison)
    (second : B -> B -> comparison) (x y : A + B) :=
  match x, y with
  | inl a, inl b => first a b
  | inl _, inr _ => Lt
  | inr _, inl _ => Gt
  | inr a, inr b => second a b
  end.

Theorem sum_laws : forall (A B : Type) first second,
  @Laws A first -> @Laws B second -> Laws (sum_compare first second).
Proof.
  intros A B first second F S. constructor.
  - intros [a|b] [c|d]; cbn [sum_compare]; split; intro H; try discriminate.
    + apply (comparison_eq F) in H. now subst.
    + inversion H; subst. apply (comparison_eq F). reflexivity.
    + apply (comparison_eq S) in H. now subst.
    + inversion H; subst. apply (comparison_eq S). reflexivity.
  - intros [a|b] [c|d]; cbn [sum_compare];
      try reflexivity; [apply (comparison_opposite F) | apply (comparison_opposite S)].
  - intros [a|b] [c|d] [e|f] decision H1 H2; cbn [sum_compare] in *; try congruence.
    + eapply comparison_transitive; [exact F | exact H1 | exact H2].
    + eapply comparison_transitive; [exact S | exact H1 | exact H2].
Qed.

Theorem injective_view_laws : forall (A B : Type) (view : A -> B) compare,
  Laws compare -> (forall x y, view x = view y -> x = y) ->
  Laws (fun x y => compare (view x) (view y)).
Proof.
  intros A B view compare laws injective. constructor.
  - intros x y. rewrite (comparison_eq laws). split;
      [apply injective | intro E; now subst].
  - intros x y. apply (comparison_opposite laws).
  - intros x y z c. apply (comparison_transitive laws).
Qed.

Theorem not_greater_is_transitive : forall (A : Type) compare,
  @Laws A compare -> forall x y z,
    compare x y <> Gt -> compare y z <> Gt -> compare x z <> Gt.
Proof.
  intros A compare laws x y z H1 H2.
  destruct (compare x y) eqn:E; [| | contradiction].
  - apply (comparison_eq laws) in E. now subst.
  - destruct (compare y z) eqn:F; [| | contradiction].
    + apply (comparison_eq laws) in F. subst z. rewrite E. discriminate.
    + rewrite (comparison_transitive laws x y z Lt E F). discriminate.
Qed.

Theorem not_greater_is_total : forall (A : Type) compare,
  @Laws A compare -> forall x y, compare x y <> Gt \/ compare y x <> Gt.
Proof.
  intros A compare laws x y. destruct (compare x y) eqn:E;
    try (left; discriminate).
  right. rewrite (comparison_opposite laws x y), E. discriminate.
Qed.

End SemanticComparisonLaws.

Print Assumptions SemanticComparisonLaws.natural_laws.
Print Assumptions SemanticComparisonLaws.list_laws.
Print Assumptions SemanticComparisonLaws.pair_laws.
Print Assumptions SemanticComparisonLaws.sum_laws.
Print Assumptions SemanticComparisonLaws.injective_view_laws.
Print Assumptions SemanticComparisonLaws.not_greater_is_transitive.
Print Assumptions SemanticComparisonLaws.not_greater_is_total.
