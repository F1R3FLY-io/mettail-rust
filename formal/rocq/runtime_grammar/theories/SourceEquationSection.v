(** The section of the exact ten authored collapse equations.

    This is a mathematical reference proof, NOT another runtime normalizer.
    Production reuse is CompiledRuleSet, saturation, selected extraction, and
    a final irreducibility check.  The accepted-output theorem below needs
    equation membership and irreducibility, not extraction optimality or
    exact floating-point arithmetic.

    We reuse SemanticTransitionKernel.LogicTerm as the structural term view.
    Its five distinguished operator LABELS are local mathematical tags, not
    hardcoded source constructor IDs or Regex names.  The source reader below
    resolves those tags from an explicit role record and retains actual
    RuleArena nodes, sorts, input-variable IDs, orientation and premises.
    Every other operator and its ordered children remain uninterpreted.
    In particular Plus, Optional and Repeat have no expansion equation here.
    Arbitrarily deep substitutions and arbitrary surrounding contexts are
    allowed; depth three limits ONLY recognition of authored schemas.

    Exact encoding of typed operators/payloads into LogicTerm labels, source
    owner authentication, the physical e-graph equivalence invariant, and
    exhaustive matching of an extracted tree are implementation refinement
    boundaries.  No encoding may identify distinct opaque payloads, confuse
    a distinguished role with another operator, or erase ordered children.
    Numeric labels alone do not prove that refinement.  Existing rich source
    and canonical-image models remain the relevant representation contracts.
    This file neither changes cost grades nor supplies a continued cut.
*)

From Stdlib Require Import List Bool PeanoNat Lia Arith.Wf_nat.
From RuntimeGrammar Require Import ExecutableTheoryCore SemanticTransitionKernel.
From Dovetail.Saturation Require Import DovetailSaturation.
Import ListNotations.

Module SourceEquationSection.
Module Core := ExecutableTheoryCore.
Module K := SemanticTransitionKernel.
Module Sat := DovetailSaturation.
Import K.

Definition Term := LogicTerm.
Definition zero : Term := LogicApplication 0 [].
Definition unit : Term := LogicApplication 1 [].
Definition alternative a b : Term := LogicApplication 2 [a; b].
Definition product a b : Term := LogicApplication 3 [a; b].
Definition closure a : Term := LogicApplication 4 [a].

Definition scoped_eq_dec : forall (x y : ScopedVariable), {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint term_eq_dec (x y : Term) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply scoped_eq_dec.
  apply list_eq_dec. exact term_eq_dec.
Defined.

Definition term_eqb x y := if term_eq_dec x y then true else false.
Lemma term_eqb_spec : forall x y, term_eqb x y = true <-> x = y.
Proof. intros. unfold term_eqb. destruct (term_eq_dec x y); split; congruence. Qed.

(** The nested-list induction principle supplies hypotheses for EVERY child,
    not just the outer constructor. *)
Lemma term_induction : forall P : Term -> Prop,
  (forall variable, P (LogicVariable variable)) ->
  (forall operator children, Forall P children -> P (LogicApplication operator children)) ->
  forall term, P term.
Proof.
  intros P V A. fix IH 1. intros [variable|operator children].
  - apply V.
  - apply A. induction children as [|child rest Hrest]; constructor; auto.
Qed.

Inductive RootStep : Term -> Term -> Prop :=
| alternative_zero_left : forall x, RootStep (alternative zero x) x
| alternative_zero_right : forall x, RootStep (alternative x zero) x
| alternative_idempotent : forall x, RootStep (alternative x x) x
| product_zero_left : forall x, RootStep (product zero x) zero
| product_zero_right : forall x, RootStep (product x zero) zero
| product_unit_left : forall x, RootStep (product unit x) x
| product_unit_right : forall x, RootStep (product x unit) x
| closure_zero : RootStep (closure zero) unit
| closure_unit : RootStep (closure unit) unit
| closure_nested : forall x, RootStep (closure (closure x)) (closure x).

Inductive Step : Term -> Term -> Prop :=
| step_root : forall x y, RootStep x y -> Step x y
| step_context : forall operator before after x y,
    Step x y ->
    Step (LogicApplication operator (before ++ x :: after))
         (LogicApplication operator (before ++ y :: after)).

Inductive Reaches : Term -> Term -> Prop :=
| reaches_refl : forall x, Reaches x x
| reaches_step : forall x y, Step x y -> Reaches x y
| reaches_trans : forall x y z, Reaches x y -> Reaches y z -> Reaches x z.

Inductive Congruence : Term -> Term -> Prop :=
| congruence_refl : forall x, Congruence x x
| congruence_sym : forall x y, Congruence x y -> Congruence y x
| congruence_trans : forall x y z, Congruence x y -> Congruence y z -> Congruence x z
| congruence_root : forall x y, RootStep x y -> Congruence x y
| congruence_context : forall operator before after x y,
    Congruence x y ->
    Congruence (LogicApplication operator (before ++ x :: after))
               (LogicApplication operator (before ++ y :: after)).

Lemma step_in_congruence : forall x y, Step x y -> Congruence x y.
Proof. intros x y H. induction H; eauto using congruence_root, congruence_context. Qed.
Lemma reaches_in_congruence : forall x y, Reaches x y -> Congruence x y.
Proof.
  intros x y H. induction H; eauto using congruence_refl, step_in_congruence,
    congruence_trans.
Qed.

Fixpoint occurrences (term : Term) : nat :=
  match term with
  | LogicVariable _ => 1
  | LogicApplication _ children =>
      S (fold_right (fun child total => occurrences child + total) 0 children)
  end.
Definition child_occurrences children :=
  fold_right (fun child total => occurrences child + total) 0 children.

Lemma occurrences_positive : forall term, 0 < occurrences term.
Proof. destruct term; simpl; lia. Qed.
Lemma child_occurrences_app : forall first second,
  child_occurrences (first ++ second) =
  child_occurrences first + child_occurrences second.
Proof. induction first; intros; simpl in *; [reflexivity|rewrite IHfirst; lia]. Qed.
Lemma occurrences_context : forall operator before after term,
  occurrences (LogicApplication operator (before ++ term :: after)) =
  S (child_occurrences before + occurrences term + child_occurrences after).
Proof.
  intros. change (S (child_occurrences (before ++ term :: after)) =
    S (child_occurrences before + occurrences term + child_occurrences after)).
  rewrite child_occurrences_app.
  change (S (child_occurrences before + (occurrences term + child_occurrences after)) =
    S (child_occurrences before + occurrences term + child_occurrences after)).
  f_equal. lia.
Qed.

Theorem every_contextual_collapse_strictly_decreases_occurrences :
  forall x y, Step x y -> occurrences y < occurrences x.
Proof.
  intros x y H. induction H.
  - destruct H; simpl; try pose proof (occurrences_positive x); lia.
  - rewrite !occurrences_context. lia.
Qed.

Theorem collapse_reduction_terminates : well_founded (fun y x => Step x y).
Proof.
  apply (well_founded_lt_compat Term occurrences).
  intros y x H. now apply every_contextual_collapse_strictly_decreases_occurrences.
Qed.

(** Smart constructors are a reference definition used to prove existence
    and uniqueness.  They are not an additional production execution path. *)
Definition smart_alternative a b :=
  if term_eq_dec a zero then b else
  if term_eq_dec b zero then a else
  if term_eq_dec a b then a else alternative a b.
Definition smart_product a b :=
  if term_eq_dec a zero then zero else
  if term_eq_dec b zero then zero else
  if term_eq_dec a unit then b else
  if term_eq_dec b unit then a else product a b.
Definition closure_child term : option Term :=
  match term with
  | LogicApplication operator [child] =>
      if Nat.eq_dec operator 4 then Some child else None
  | _ => None
  end.
Definition smart_closure a :=
  if term_eq_dec a zero then unit else
  if term_eq_dec a unit then unit else
  match closure_child a with Some _ => a | None => closure a end.

Lemma closure_child_sound : forall term child,
  closure_child term = Some child -> term = closure child.
Proof.
  intros [v|op children] child H; [discriminate|].
  destruct children as [|a rest]; [discriminate|].
  destruct rest; [|discriminate]. unfold closure_child in H.
  destruct (Nat.eq_dec op 4); [|discriminate]. inversion H. now subst.
Qed.
Lemma closure_child_closure : forall a, closure_child (closure a) = Some a.
Proof. intros. unfold closure_child, closure. destruct (Nat.eq_dec 4 4); congruence. Qed.

Definition smart_node operator children :=
  match operator, children with
  | 2, [a; b] => smart_alternative a b
  | 3, [a; b] => smart_product a b
  | 4, [a] => smart_closure a
  | _, _ => LogicApplication operator children
  end.

Fixpoint normalize (term : Term) : Term :=
  match term with
  | LogicVariable variable => LogicVariable variable
  | LogicApplication operator children => smart_node operator (map normalize children)
  end.

Lemma normalize_zero : normalize zero = zero. Proof. reflexivity. Qed.
Lemma normalize_unit : normalize unit = unit. Proof. reflexivity. Qed.
Lemma normalize_alternative : forall a b,
  normalize (alternative a b) = smart_alternative (normalize a) (normalize b).
Proof. reflexivity. Qed.
Lemma normalize_product : forall a b,
  normalize (product a b) = smart_product (normalize a) (normalize b).
Proof. reflexivity. Qed.
Lemma normalize_closure : forall a,
  normalize (closure a) = smart_closure (normalize a).
Proof. reflexivity. Qed.

Lemma smart_alternative_zero_left : forall a, smart_alternative zero a = a.
Proof. intros. unfold smart_alternative. destruct (term_eq_dec zero zero); congruence. Qed.
Lemma smart_alternative_zero_right : forall a, smart_alternative a zero = a.
Proof.
  intros. unfold smart_alternative. destruct (term_eq_dec a zero); [now subst|].
  destruct (term_eq_dec zero zero); congruence.
Qed.
Lemma smart_alternative_idempotent : forall a, smart_alternative a a = a.
Proof.
  intros. unfold smart_alternative. destruct (term_eq_dec a zero); [reflexivity|].
  destruct (term_eq_dec a a); congruence.
Qed.
Lemma smart_product_zero_left : forall a, smart_product zero a = zero.
Proof. intros. unfold smart_product. destruct (term_eq_dec zero zero); congruence. Qed.
Lemma smart_product_zero_right : forall a, smart_product a zero = zero.
Proof.
  intros. unfold smart_product. destruct (term_eq_dec a zero); [reflexivity|].
  destruct (term_eq_dec zero zero); congruence.
Qed.
Lemma smart_product_unit_left : forall a, smart_product unit a = a.
Proof.
  intros. unfold smart_product. destruct (term_eq_dec unit zero); [discriminate|].
  destruct (term_eq_dec a zero); [now subst|].
  destruct (term_eq_dec unit unit); congruence.
Qed.
Lemma smart_product_unit_right : forall a, smart_product a unit = a.
Proof.
  intros. unfold smart_product. destruct (term_eq_dec a zero); [now subst|].
  destruct (term_eq_dec unit zero); [discriminate|].
  destruct (term_eq_dec a unit); [now subst|].
  destruct (term_eq_dec unit unit); congruence.
Qed.
Lemma smart_closure_zero : smart_closure zero = unit.
Proof. unfold smart_closure. destruct (term_eq_dec zero zero); congruence. Qed.
Lemma smart_closure_unit : smart_closure unit = unit.
Proof.
  unfold smart_closure. destruct (term_eq_dec unit zero); [discriminate|].
  destruct (term_eq_dec unit unit); congruence.
Qed.
Lemma smart_closure_closed : forall a, smart_closure (closure a) = closure a.
Proof.
  intros. unfold smart_closure.
  destruct (term_eq_dec (closure a) zero); [discriminate|].
  destruct (term_eq_dec (closure a) unit); [discriminate|].
  now rewrite closure_child_closure.
Qed.
Lemma smart_closure_idempotent : forall a,
  smart_closure (smart_closure a) = smart_closure a.
Proof.
  intros a. unfold smart_closure at 2 3.
  destruct (term_eq_dec a zero); [apply smart_closure_unit|].
  destruct (term_eq_dec a unit); [apply smart_closure_unit|].
  destruct (closure_child a) as [child|] eqn:H.
  - apply closure_child_sound in H. subst. apply smart_closure_closed.
  - apply smart_closure_closed.
Qed.

Theorem every_root_equation_has_the_same_reference_normal_form :
  forall x y, RootStep x y -> normalize x = normalize y.
Proof.
  intros x y H. destruct H;
    rewrite ?normalize_alternative, ?normalize_product, ?normalize_closure,
      ?normalize_zero, ?normalize_unit;
    auto using smart_alternative_zero_left, smart_alternative_zero_right,
      smart_alternative_idempotent, smart_product_zero_left,
      smart_product_zero_right, smart_product_unit_left, smart_product_unit_right,
      smart_closure_zero, smart_closure_unit, smart_closure_idempotent.
Qed.

Lemma normalized_context : forall operator before after x y,
  normalize x = normalize y ->
  normalize (LogicApplication operator (before ++ x :: after)) =
  normalize (LogicApplication operator (before ++ y :: after)).
Proof.
  intros operator before after x y H. change
    (smart_node operator (map normalize (before ++ x :: after)) =
     smart_node operator (map normalize (before ++ y :: after))).
  rewrite !map_app. simpl. now rewrite H.
Qed.

Theorem source_congruence_preserves_reference_normal_form :
  forall x y, Congruence x y -> normalize x = normalize y.
Proof.
  intros x y H. induction H; eauto using
    every_root_equation_has_the_same_reference_normal_form, normalized_context;
    congruence.
Qed.

Lemma smart_alternative_reduces : forall a b,
  smart_alternative a b = alternative a b \/
  RootStep (alternative a b) (smart_alternative a b).
Proof.
  intros. unfold smart_alternative.
  destruct (term_eq_dec a zero); [subst; right; constructor|].
  destruct (term_eq_dec b zero); [subst; right; constructor|].
  destruct (term_eq_dec a b); [subst; right; constructor|left; reflexivity].
Qed.
Lemma smart_product_reduces : forall a b,
  smart_product a b = product a b \/ RootStep (product a b) (smart_product a b).
Proof.
  intros. unfold smart_product.
  destruct (term_eq_dec a zero); [subst; right; constructor|].
  destruct (term_eq_dec b zero); [subst; right; constructor|].
  destruct (term_eq_dec a unit); [subst; right; constructor|].
  destruct (term_eq_dec b unit); [subst; right; constructor|left; reflexivity].
Qed.
Lemma smart_closure_reduces : forall a,
  smart_closure a = closure a \/ RootStep (closure a) (smart_closure a).
Proof.
  intros. unfold smart_closure.
  destruct (term_eq_dec a zero); [subst; right; constructor|].
  destruct (term_eq_dec a unit); [subst; right; constructor|].
  destruct (closure_child a) as [child|] eqn:H; [|left; reflexivity].
  apply closure_child_sound in H. subst. right. constructor.
Qed.

Lemma smart_node_reduces : forall operator children,
  smart_node operator children = LogicApplication operator children \/
  RootStep (LogicApplication operator children) (smart_node operator children).
Proof.
  intros operator children.
  destruct operator as [|[|[|[|[|operator]]]]]; try (left; reflexivity).
  - destruct children as [|a [|b [|c rest]]]; try (left; reflexivity).
    apply smart_alternative_reduces.
  - destruct children as [|a [|b [|c rest]]]; try (left; reflexivity).
    apply smart_product_reduces.
  - destruct children as [|a [|b rest]]; try (left; reflexivity).
    apply smart_closure_reduces.
Qed.

Inductive Normal : Term -> Prop :=
| normal_variable : forall variable, Normal (LogicVariable variable)
| normal_application : forall operator children,
    Forall Normal children ->
    (forall other, ~ RootStep (LogicApplication operator children) other) ->
    Normal (LogicApplication operator children).

Lemma normal_zero : Normal zero.
Proof. constructor; [constructor|intros other H; inversion H]. Qed.
Lemma normal_unit : Normal unit.
Proof. constructor; [constructor|intros other H; inversion H]. Qed.

Lemma alternative_root_cases : forall a b other,
  RootStep (alternative a b) other -> a = zero \/ b = zero \/ a = b.
Proof. intros a b other H. inversion H; subst; auto. Qed.
Lemma product_root_cases : forall a b other,
  RootStep (product a b) other ->
  a = zero \/ b = zero \/ a = unit \/ b = unit.
Proof. intros a b other H. inversion H; subst; auto. Qed.
Lemma closure_root_cases : forall a other,
  RootStep (closure a) other -> a = zero \/ a = unit \/ exists b, a = closure b.
Proof. intros a other H. inversion H; subst; eauto. Qed.

Lemma smart_alternative_normal : forall a b,
  Normal a -> Normal b -> Normal (smart_alternative a b).
Proof.
  intros a b A B. unfold smart_alternative.
  destruct (term_eq_dec a zero); [exact B|].
  destruct (term_eq_dec b zero); [exact A|].
  destruct (term_eq_dec a b); [exact A|].
  constructor; [repeat constructor; assumption|].
  intros other H. apply alternative_root_cases in H. tauto.
Qed.
Lemma smart_product_normal : forall a b,
  Normal a -> Normal b -> Normal (smart_product a b).
Proof.
  intros a b A B. unfold smart_product.
  destruct (term_eq_dec a zero); [exact normal_zero|].
  destruct (term_eq_dec b zero); [exact normal_zero|].
  destruct (term_eq_dec a unit); [exact B|].
  destruct (term_eq_dec b unit); [exact A|].
  constructor; [repeat constructor; assumption|].
  intros other H. apply product_root_cases in H. tauto.
Qed.
Lemma smart_closure_normal : forall a, Normal a -> Normal (smart_closure a).
Proof.
  intros a A. unfold smart_closure.
  destruct (term_eq_dec a zero); [exact normal_unit|].
  destruct (term_eq_dec a unit); [exact normal_unit|].
  destruct (closure_child a) as [child|] eqn:C; [exact A|].
  constructor; [repeat constructor; assumption|].
  intros other H. apply closure_root_cases in H.
  destruct H as [H|[H|[b H]]]; try contradiction.
  subst a. rewrite closure_child_closure in C. discriminate.
Qed.

Lemma smart_node_normal : forall operator children,
  Forall Normal children -> Normal (smart_node operator children).
Proof.
  intros operator children H.
  destruct operator as [|[|[|[|[|operator]]]]];
    try (apply normal_application; [exact H|intros other R; inversion R]).
  - destruct children as [|a [|b [|c rest]]];
      try (apply normal_application; [exact H|intros other R; inversion R]).
    inversion H as [|? ? A Hrest]; subst.
    inversion Hrest as [|? ? B Hnil]; subst.
    now apply smart_alternative_normal.
  - destruct children as [|a [|b [|c rest]]];
      try (apply normal_application; [exact H|intros other R; inversion R]).
    inversion H as [|? ? A Hrest]; subst.
    inversion Hrest as [|? ? B Hnil]; subst.
    now apply smart_product_normal.
  - destruct children as [|a [|b rest]];
      try (apply normal_application; [exact H|intros other R; inversion R]).
    inversion H; subst. now apply smart_closure_normal.
Qed.

Theorem reference_normalization_is_normal : forall term, Normal (normalize term).
Proof.
  apply term_induction.
  - intros. constructor.
  - intros operator children H. apply smart_node_normal.
    apply Forall_map. exact H.
Qed.

Lemma reaches_context : forall x y,
  Reaches x y -> forall operator before after,
  Reaches (LogicApplication operator (before ++ x :: after))
          (LogicApplication operator (before ++ y :: after)).
Proof.
  intros x y H. induction H; intros;
    eauto using reaches_refl, reaches_step, step_context, reaches_trans.
Qed.

Lemma normalize_children_reachable : forall children,
  Forall (fun child => Reaches child (normalize child)) children ->
  forall operator before,
  Reaches (LogicApplication operator (before ++ children))
          (LogicApplication operator (before ++ map normalize children)).
Proof.
  intros children H. induction H as [|a rest A Hrest IH]; intros operator before.
  - simpl. apply reaches_refl.
  - simpl. eapply reaches_trans with
      (y := LogicApplication operator (before ++ normalize a :: rest)).
    + now apply reaches_context.
    + specialize (IH operator (before ++ [normalize a])).
      now rewrite <- !app_assoc in IH.
Qed.

Theorem reference_normalization_is_reachable : forall term,
  Reaches term (normalize term).
Proof.
  apply term_induction.
  - intros. apply reaches_refl.
  - intros operator children H.
    eapply reaches_trans with (y := LogicApplication operator (map normalize children)).
    + exact (normalize_children_reachable children H operator []).
    + destruct (smart_node_reduces operator (map normalize children)) as [E|R].
      * change (Reaches (LogicApplication operator (map normalize children))
          (smart_node operator (map normalize children))).
        rewrite E. apply reaches_refl.
      * apply reaches_step. now apply step_root.
Qed.

Theorem every_term_has_a_reachable_normal_form : forall term,
  exists normal, Reaches term normal /\ Normal normal.
Proof.
  intros term. exists (normalize term). split;
    [apply reference_normalization_is_reachable|apply reference_normalization_is_normal].
Qed.

Lemma normal_has_no_root_step : forall term, Normal term -> forall other, ~ RootStep term other.
Proof. intros term H. destruct H; [intros other R; inversion R|assumption]. Qed.
Lemma normal_context_child : forall operator before after term,
  Normal (LogicApplication operator (before ++ term :: after)) -> Normal term.
Proof.
  intros operator before after term H. inversion H; subst.
  match goal with A : Forall Normal _ |- _ =>
    apply Forall_forall with (x := term) in A; [exact A|]
  end.
  apply in_or_app. right. now left.
Qed.

Definition Irreducible term := forall other, ~ Step term other.
Theorem normal_is_irreducible : forall term, Normal term -> Irreducible term.
Proof.
  intros term N other H. revert N. induction H; intros N.
  - exact (normal_has_no_root_step x N y H).
  - apply IHStep. now apply normal_context_child in N.
Qed.

Theorem irreducible_is_normal : forall term, Irreducible term -> Normal term.
Proof.
  apply (term_induction (fun term => Irreducible term -> Normal term)).
  - intros variable H. constructor.
  - intros operator children IH H. constructor.
    + apply Forall_forall. intros child Hin.
      apply Forall_forall with (x := child) in IH; [|exact Hin].
      apply IH. intros other R. apply in_split in Hin as [before [after E]].
      apply (H (LogicApplication operator (before ++ other :: after))).
      rewrite E. now apply step_context.
    + intros other R. apply (H other). now apply step_root.
Qed.

Lemma map_fixed : forall (f : Term -> Term) children,
  Forall (fun child => f child = child) children -> map f children = children.
Proof. intros f children H. induction H; simpl; congruence. Qed.

Theorem normal_terms_are_reference_fixed_points : forall term,
  Normal term -> normalize term = term.
Proof.
  apply (term_induction (fun term => Normal term -> normalize term = term)).
  - reflexivity.
  - intros operator children IH N.
    inversion N as [|? ? C R]; subst.
    assert (F : Forall (fun child => normalize child = child) children).
    { apply Forall_forall. intros child Hin.
      apply Forall_forall with (x := child) in IH; [|exact Hin].
      apply IH. now apply Forall_forall with (x := child) in C. }
    change (smart_node operator (map normalize children) = LogicApplication operator children).
    rewrite (map_fixed normalize children F).
    destruct (smart_node_reduces operator children) as [E|S]; [exact E|].
    exfalso. exact (R _ S).
Qed.

Theorem reference_normalization_idempotent : forall term,
  normalize (normalize term) = normalize term.
Proof. intros. apply normal_terms_are_reference_fixed_points, reference_normalization_is_normal. Qed.

Theorem equivalent_normal_forms_are_equal : forall x y,
  Congruence x y -> Normal x -> Normal y -> x = y.
Proof.
  intros x y E X Y.
  pose proof (source_congruence_preserves_reference_normal_form x y E) as H.
  now rewrite (normal_terms_are_reference_fixed_points x X),
    (normal_terms_are_reference_fixed_points y Y) in H.
Qed.

Theorem congruence_iff_equal_normal_forms : forall x y,
  Congruence x y <-> normalize x = normalize y.
Proof.
  intros x y. split; [apply source_congruence_preserves_reference_normal_form|].
  intros H. eapply congruence_trans.
  - apply reaches_in_congruence, reference_normalization_is_reachable.
  - rewrite H. apply congruence_sym, reaches_in_congruence,
      reference_normalization_is_reachable.
Qed.

(** This is the extraction-facing section theorem.  Its hypotheses are
    deliberately independent of minimum-weight selection, saturation order,
    productive e-class cycles, and floating-point tie behavior. *)
Theorem accepted_equivalent_irreducible_output_is_the_section : forall input output,
  Congruence input output -> Irreducible output -> output = normalize input.
Proof.
  intros input output E I.
  pose proof (source_congruence_preserves_reference_normal_form input output E) as H.
  rewrite (normal_terms_are_reference_fixed_points output (irreducible_is_normal output I)) in H.
  symmetry. exact H.
Qed.

Theorem accepted_outputs_do_not_depend_on_extraction_order : forall input first second,
  Congruence input first -> Irreducible first ->
  Congruence input second -> Irreducible second -> first = second.
Proof.
  intros input first second E F G H.
  rewrite (accepted_equivalent_irreducible_output_is_the_section input first E F),
    (accepted_equivalent_irreducible_output_is_the_section input second G H).
  reflexivity.
Qed.

(** Exact, constant-depth source-schema admission.  Core's constructor and
    variable arena is sufficient here because every admitted equation uses
    only those forms.  Other rich source forms are NOT erased into a match.
    The caller separately establishes resolved declaration membership and
    constructor typing; the reader checks node and variable sorts itself. *)
Record Roles := {
  role_sort : Core.SortId;
  role_zero : Core.ConstructorId;
  role_unit : Core.ConstructorId;
  role_alternative : Core.ConstructorId;
  role_product : Core.ConstructorId;
  role_closure : Core.ConstructorId
}.

Definition role_ids roles := [role_zero roles; role_unit roles;
  role_alternative roles; role_product roles; role_closure roles].
Fixpoint distinct_idsb (ids : list nat) :=
  match ids with
  | [] => true
  | first :: rest => negb (existsb (Nat.eqb first) rest) && distinct_idsb rest
  end.
Definition distinct_rolesb roles := distinct_idsb (role_ids roles).
Lemma distinct_idsb_sound : forall ids, distinct_idsb ids = true -> NoDup ids.
Proof.
  induction ids as [|first rest IH]; intros H; [constructor|].
  simpl in H. apply andb_true_iff in H as [N R]. constructor; [|now apply IH].
  intros I. assert (E : existsb (Nat.eqb first) rest = true).
  { apply existsb_exists. exists first. split; [exact I|apply Nat.eqb_refl]. }
  rewrite E in N. discriminate.
Qed.

Definition operator_role roles constructor : option nat :=
  if Nat.eq_dec constructor (role_zero roles) then Some 0 else
  if Nat.eq_dec constructor (role_unit roles) then Some 1 else
  if Nat.eq_dec constructor (role_alternative roles) then Some 2 else
  if Nat.eq_dec constructor (role_product roles) then Some 3 else
  if Nat.eq_dec constructor (role_closure roles) then Some 4 else None.
Definition role_arity tag := match tag with 0 | 1 => 0 | 2 | 3 => 2 | _ => 1 end.

Definition source_variable variable : Term :=
  LogicVariable {| scoped_activation := 0; scoped_local := variable |}.
Definition input_variableb roles rule variable :=
  match nth_error (Core.rule_variables rule) variable with
  | Some {| Core.variable_sort := sort; Core.variable_role := Core.InputVariable |} =>
      Nat.eqb sort (role_sort roles)
  | _ => false
  end.

Fixpoint traverse {A B : Type} (f : A -> option B) (values : list A) : option (list B) :=
  match values with
  | [] => Some []
  | value :: rest =>
      match f value, traverse f rest with
      | Some result, Some results => Some (result :: results)
      | _, _ => None
      end
  end.
Lemma traverse_sound : forall (A B : Type) (f : A -> option B) values results,
  traverse f values = Some results -> Forall2 (fun a b => f a = Some b) values results.
Proof.
  intros A B f values. induction values as [|value rest IH]; intros results H; simpl in H.
  - inversion H. constructor.
  - destruct (f value) as [result|] eqn:F; [|discriminate].
    destruct (traverse f rest) as [tail|] eqn:T; [|discriminate].
    inversion H; subst. constructor; auto.
Qed.

Fixpoint read_schema depth roles rule root : option Term :=
  match depth with
  | 0 => None
  | S rest =>
      match nth_error (Core.rule_terms rule) root with
      | Some node =>
          if Nat.eqb (Core.term_sort node) (role_sort roles) then
            match Core.term_form node with
            | Core.VariableTerm variable =>
                if input_variableb roles rule variable then Some (source_variable variable) else None
            | Core.ConstructorTerm constructor arguments =>
                match operator_role roles constructor with
                | Some tag =>
                    if Nat.eqb (length arguments) (role_arity tag) then
                      match traverse (read_schema rest roles rule) arguments with
                      | Some children => Some (LogicApplication tag children)
                      | None => None
                      end
                    else None
                | None => None
                end
            | _ => None
            end
          else None
      | None => None
      end
  end.

Inductive SourceShape roles rule : Core.TermId -> Term -> Prop :=
| shape_variable : forall root variable,
    nth_error (Core.rule_terms rule) root = Some
      {| Core.term_sort := role_sort roles; Core.term_form := Core.VariableTerm variable |} ->
    nth_error (Core.rule_variables rule) variable = Some
      {| Core.variable_sort := role_sort roles; Core.variable_role := Core.InputVariable |} ->
    SourceShape roles rule root (source_variable variable)
| shape_constructor : forall root constructor arguments tag children,
    nth_error (Core.rule_terms rule) root = Some
      {| Core.term_sort := role_sort roles;
         Core.term_form := Core.ConstructorTerm constructor arguments |} ->
    operator_role roles constructor = Some tag ->
    length arguments = role_arity tag ->
    Forall2 (SourceShape roles rule) arguments children ->
    SourceShape roles rule root (LogicApplication tag children).

Lemma input_variableb_sound : forall roles rule variable,
  input_variableb roles rule variable = true ->
  nth_error (Core.rule_variables rule) variable = Some
    {| Core.variable_sort := role_sort roles; Core.variable_role := Core.InputVariable |}.
Proof.
  intros roles rule variable H. unfold input_variableb in H.
  destruct (nth_error (Core.rule_variables rule) variable) as [[sort role]|] eqn:E;
    [destruct role|]; try discriminate.
  apply Nat.eqb_eq in H. now subst.
Qed.

Theorem schema_reader_preserves_actual_source_nodes : forall depth roles rule root term,
  read_schema depth roles rule root = Some term -> SourceShape roles rule root term.
Proof.
  induction depth as [|depth IH]; intros roles rule root term H; [discriminate|].
  simpl in H.
  destruct (nth_error (Core.rule_terms rule) root) as [[sort form]|] eqn:N; [|discriminate].
  simpl in H. destruct (Nat.eqb sort (role_sort roles)) eqn:S; [|discriminate].
  apply Nat.eqb_eq in S. subst sort.
  destruct form; try discriminate.
  - destruct (input_variableb roles rule variable) eqn:V; [|discriminate].
    inversion H; subst. eapply shape_variable; [exact N|]. now apply input_variableb_sound.
  - destruct (operator_role roles constructor) as [tag|] eqn:T; [|discriminate].
    destruct (Nat.eqb (length arguments) (role_arity tag)) eqn:A; [|discriminate].
    destruct (traverse (read_schema depth roles rule) arguments) as [children|] eqn:C;
      [|discriminate]. inversion H; subst.
    eapply shape_constructor; [exact N|exact T|now apply Nat.eqb_eq|].
    apply traverse_sound in C. clear N A H.
    induction C; constructor; eauto.
Qed.

Inductive Law := AltZeroLeft | AltZeroRight | AltIdempotent |
  ProductZeroLeft | ProductZeroRight | ProductUnitLeft | ProductUnitRight |
  ClosureZero | ClosureUnit | ClosureNested.
Definition all_laws := [AltZeroLeft; AltZeroRight; AltIdempotent;
  ProductZeroLeft; ProductZeroRight; ProductUnitLeft; ProductUnitRight;
  ClosureZero; ClosureUnit; ClosureNested].
Definition law_eq_dec : forall (x y : Law), {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition law_eqb x y := if law_eq_dec x y then true else false.

Definition law_left law variable :=
  let x := source_variable variable in
  match law with
  | AltZeroLeft => alternative zero x
  | AltZeroRight => alternative x zero
  | AltIdempotent => alternative x x
  | ProductZeroLeft => product zero x
  | ProductZeroRight => product x zero
  | ProductUnitLeft => product unit x
  | ProductUnitRight => product x unit
  | ClosureZero => closure zero
  | ClosureUnit => closure unit
  | ClosureNested => closure (closure x)
  end.
Definition law_right law variable :=
  let x := source_variable variable in
  match law with
  | ProductZeroLeft | ProductZeroRight => zero
  | ClosureZero | ClosureUnit => unit
  | ClosureNested => closure x
  | _ => x
  end.

Definition candidate_law term : option (Law * Core.VariableId) :=
  match term with
  | LogicApplication 2 [LogicApplication 0 []; LogicVariable x] => Some (AltZeroLeft, scoped_local x)
  | LogicApplication 2 [LogicVariable x; LogicApplication 0 []] => Some (AltZeroRight, scoped_local x)
  | LogicApplication 2 [LogicVariable x; LogicVariable _] => Some (AltIdempotent, scoped_local x)
  | LogicApplication 3 [LogicApplication 0 []; LogicVariable x] => Some (ProductZeroLeft, scoped_local x)
  | LogicApplication 3 [LogicVariable x; LogicApplication 0 []] => Some (ProductZeroRight, scoped_local x)
  | LogicApplication 3 [LogicApplication 1 []; LogicVariable x] => Some (ProductUnitLeft, scoped_local x)
  | LogicApplication 3 [LogicVariable x; LogicApplication 1 []] => Some (ProductUnitRight, scoped_local x)
  | LogicApplication 4 [LogicApplication 0 []] => Some (ClosureZero, 0)
  | LogicApplication 4 [LogicApplication 1 []] => Some (ClosureUnit, 0)
  | LogicApplication 4 [LogicApplication 4 [LogicVariable x]] => Some (ClosureNested, scoped_local x)
  | _ => None
  end.
Definition recognize left right :=
  match candidate_law left with
  | Some (law, variable) =>
      if term_eqb left (law_left law variable) && term_eqb right (law_right law variable)
      then Some (law, variable) else None
  | None => None
  end.
Lemma recognize_sound : forall left right law variable,
  recognize left right = Some (law, variable) ->
  left = law_left law variable /\ right = law_right law variable.
Proof.
  intros left right law variable H. unfold recognize in H.
  destruct (candidate_law left) as [[found v]|]; [|discriminate].
  destruct (term_eqb left (law_left found v) && term_eqb right (law_right found v)) eqn:E;
    [|discriminate]. inversion H; subst.
  apply andb_true_iff in E as [L R]. split; now apply term_eqb_spec.
Qed.

Inductive Orientation := Forward | Reverse.
Definition oriented_roots rule orientation :=
  match orientation with
  | Forward => (Core.rule_lhs rule, Core.rule_rhs rule)
  | Reverse => (Core.rule_rhs rule, Core.rule_lhs rule)
  end.
Record Witness := {
  witness_orientation : Orientation;
  witness_law : Law;
  witness_variable : Core.VariableId
}.
Definition check_direction roles rule orientation : option Witness :=
  let '(left_root, right_root) := oriented_roots rule orientation in
  match read_schema 3 roles rule left_root, read_schema 3 roles rule right_root with
  | Some lhs, Some rhs =>
      match recognize lhs rhs with
      | Some (law, variable) => Some {| witness_orientation := orientation;
          witness_law := law; witness_variable := variable |}
      | None => None
      end
  | _, _ => None
  end.
Definition check_equation roles rule :=
  match Core.rule_premises rule, Core.rule_premise_roots rule with
  | [], [] =>
      match check_direction roles rule Forward with
      | Some witness => Some witness
      | None => check_direction roles rule Reverse
      end
  | _, _ => None
  end.

Definition WitnessInEquation roles rule witness :=
  Core.rule_premises rule = [] /\ Core.rule_premise_roots rule = [] /\
  SourceShape roles rule (fst (oriented_roots rule (witness_orientation witness)))
    (law_left (witness_law witness) (witness_variable witness)) /\
  SourceShape roles rule (snd (oriented_roots rule (witness_orientation witness)))
    (law_right (witness_law witness) (witness_variable witness)).

Lemma check_direction_sound : forall roles rule orientation witness,
  check_direction roles rule orientation = Some witness ->
  witness_orientation witness = orientation /\
  SourceShape roles rule (fst (oriented_roots rule orientation))
    (law_left (witness_law witness) (witness_variable witness)) /\
  SourceShape roles rule (snd (oriented_roots rule orientation))
    (law_right (witness_law witness) (witness_variable witness)).
Proof.
  intros roles rule orientation witness H. unfold check_direction in H.
  destruct (oriented_roots rule orientation) as [left right] eqn:O; simpl.
  destruct (read_schema 3 roles rule left) as [lhs|] eqn:L; [|discriminate].
  destruct (read_schema 3 roles rule right) as [rhs|] eqn:R; [|discriminate].
  destruct (recognize lhs rhs) as [[law variable]|] eqn:E; [|discriminate].
  inversion H; subst. simpl. apply recognize_sound in E as [A B]. subst lhs rhs.
  repeat split; eauto using schema_reader_preserves_actual_source_nodes.
Qed.

Theorem checked_equation_retains_exact_source_witness : forall roles rule witness,
  check_equation roles rule = Some witness -> WitnessInEquation roles rule witness.
Proof.
  intros roles rule witness H. unfold check_equation in H.
  destruct (Core.rule_premises rule) eqn:P; [|discriminate].
  destruct (Core.rule_premise_roots rule) eqn:R; [|discriminate].
  destruct (check_direction roles rule Forward) as [found|] eqn:F.
  - inversion H; subst. destruct (check_direction_sound _ _ _ _ F) as [O [L Q]].
    unfold WitnessInEquation. rewrite O. auto.
  - destruct (check_direction_sound _ _ _ _ H) as [O [L Q]].
    unfold WitnessInEquation. rewrite O. auto.
Qed.

Definition covers_all_laws witnesses :=
  forallb (fun law => existsb (fun witness => law_eqb (witness_law witness) law) witnesses) all_laws.
(** Every row must be recognized and all ten schemas must be covered.
    Duplicate equations do not change the presentation and are accepted. *)
Definition check_roster roles equations : option (list Witness) :=
  if distinct_rolesb roles then
    match traverse (check_equation roles) equations with
    | Some witnesses => if covers_all_laws witnesses then Some witnesses else None
    | None => None
    end
  else None.

Lemma covers_all_laws_sound : forall witnesses,
  covers_all_laws witnesses = true ->
  forall law, exists witness, In witness witnesses /\ witness_law witness = law.
Proof.
  intros witnesses H law. unfold covers_all_laws in H.
  apply forallb_forall with (x := law) in H.
  - apply existsb_exists in H as [witness [I E]]. exists witness. split; [exact I|].
    unfold law_eqb in E. destruct (law_eq_dec (witness_law witness) law); congruence.
  - destruct law; simpl; tauto.
Qed.

Theorem admitted_roster_is_exact_and_complete : forall roles equations witnesses,
  check_roster roles equations = Some witnesses ->
  NoDup (role_ids roles) /\
  Forall2 (WitnessInEquation roles) equations witnesses /\
  (forall law, exists witness, In witness witnesses /\ witness_law witness = law).
Proof.
  intros roles equations witnesses H. unfold check_roster in H.
  destruct (distinct_rolesb roles) eqn:D; [|discriminate].
  destruct (traverse (check_equation roles) equations) as [found|] eqn:T; [|discriminate].
  destruct (covers_all_laws found) eqn:C; [|discriminate]. inversion H; subst.
  assert (ND : NoDup (role_ids roles)).
  { now apply distinct_idsb_sound. }
  split; [exact ND|]. split.
  - apply traverse_sound in T. clear H C.
    induction T; constructor; eauto using checked_equation_retains_exact_source_witness.
  - now apply covers_all_laws_sound.
Qed.

(** A valuation ranges over arbitrary structural terms, not bounded schema
    trees.  This includes arbitrary other constructors and arbitrarily deep
    products.  The schema reader's fixed depth does not restrict valuations. *)
Fixpoint substitute (valuation : Core.VariableId -> Term) term :=
  match term with
  | LogicVariable variable => valuation (scoped_local variable)
  | LogicApplication operator children =>
      LogicApplication operator (map (substitute valuation) children)
  end.
Lemma instantiated_law_is_root_step : forall law variable valuation,
  RootStep (substitute valuation (law_left law variable))
           (substitute valuation (law_right law variable)).
Proof. destruct law; intros; simpl; constructor. Qed.
Lemma root_step_is_instantiated_law : forall x y,
  RootStep x y -> exists law, forall variable,
    exists valuation,
      substitute valuation (law_left law variable) = x /\
      substitute valuation (law_right law variable) = y.
Proof.
  intros x y H. destruct H.
  - exists AltZeroLeft. intros variable. exists (fun _ => x). split; reflexivity.
  - exists AltZeroRight. intros variable. exists (fun _ => x). split; reflexivity.
  - exists AltIdempotent. intros variable. exists (fun _ => x). split; reflexivity.
  - exists ProductZeroLeft. intros variable. exists (fun _ => x). split; reflexivity.
  - exists ProductZeroRight. intros variable. exists (fun _ => x). split; reflexivity.
  - exists ProductUnitLeft. intros variable. exists (fun _ => x). split; reflexivity.
  - exists ProductUnitRight. intros variable. exists (fun _ => x). split; reflexivity.
  - exists ClosureZero. intros variable. exists (fun _ => zero). split; reflexivity.
  - exists ClosureUnit. intros variable. exists (fun _ => zero). split; reflexivity.
  - exists ClosureNested. intros variable. exists (fun _ => x). split; reflexivity.
Qed.

(** This generated congruence interprets the admitted source presentation:
    each source-order witness selects an actual equation and orientation.
    It does not assume that arbitrary unadmitted equations are the ten laws.
    For an admitted roster the next theorem identifies this congruence with
    the exact ten-rule congruence used by the section proof. *)
Inductive PresentedCongruence (witnesses : list Witness) : Term -> Term -> Prop :=
| presented_refl : forall x, PresentedCongruence witnesses x x
| presented_sym : forall x y,
    PresentedCongruence witnesses x y -> PresentedCongruence witnesses y x
| presented_trans : forall x y z,
    PresentedCongruence witnesses x y -> PresentedCongruence witnesses y z ->
    PresentedCongruence witnesses x z
| presented_equation : forall witness valuation,
    In witness witnesses ->
    PresentedCongruence witnesses
      (substitute valuation (law_left (witness_law witness) (witness_variable witness)))
      (substitute valuation (law_right (witness_law witness) (witness_variable witness)))
| presented_context : forall operator before after x y,
    PresentedCongruence witnesses x y ->
    PresentedCongruence witnesses (LogicApplication operator (before ++ x :: after))
      (LogicApplication operator (before ++ y :: after)).

Lemma presented_congruence_is_sound : forall witnesses x y,
  PresentedCongruence witnesses x y -> Congruence x y.
Proof.
  intros witnesses x y H. induction H; eauto using congruence_refl,
    congruence_sym, congruence_trans, congruence_context,
    congruence_root, instantiated_law_is_root_step.
Qed.

Lemma complete_roster_generates_every_equation : forall witnesses,
  (forall law, exists witness, In witness witnesses /\ witness_law witness = law) ->
  forall x y, Congruence x y -> PresentedCongruence witnesses x y.
Proof.
  intros witnesses Complete x y H. induction H;
    eauto using presented_refl, presented_sym, presented_trans, presented_context.
  destruct (root_step_is_instantiated_law _ _ H) as [law L].
  destruct (Complete law) as [witness [I E]].
  destruct (L (witness_variable witness)) as [valuation [A B]].
  rewrite <- A, <- B, <- E. now apply presented_equation.
Qed.

Theorem admitted_source_presentation_has_exactly_the_ten_equation_quotient :
  forall roles equations witnesses,
  check_roster roles equations = Some witnesses -> forall x y,
  PresentedCongruence witnesses x y <-> Congruence x y.
Proof.
  intros roles equations witnesses H x y. split; [apply presented_congruence_is_sound|].
  apply complete_roster_generates_every_equation.
  exact (proj2 (proj2 (admitted_roster_is_exact_and_complete _ _ _ H))).
Qed.

Theorem admitted_source_section_is_sound_and_idempotent : forall roles equations witnesses,
  check_roster roles equations = Some witnesses -> forall term,
  PresentedCongruence witnesses term (normalize term) /\
  Irreducible (normalize term) /\ normalize (normalize term) = normalize term.
Proof.
  intros roles equations witnesses H term. split.
  - apply (proj2 (admitted_source_presentation_has_exactly_the_ten_equation_quotient
      roles equations witnesses H _ _)).
    apply reaches_in_congruence, reference_normalization_is_reachable.
  - split; [apply normal_is_irreducible, reference_normalization_is_normal|
      apply reference_normalization_idempotent].
Qed.

Theorem admitted_source_section_is_quotient_invariant : forall roles equations witnesses,
  check_roster roles equations = Some witnesses -> forall x y,
  PresentedCongruence witnesses x y <-> normalize x = normalize y.
Proof.
  intros roles equations witnesses H x y.
  rewrite (admitted_source_presentation_has_exactly_the_ten_equation_quotient
    roles equations witnesses H x y). apply congruence_iff_equal_normal_forms.
Qed.

Theorem admitted_source_accepted_output_is_exact : forall roles equations witnesses input output,
  check_roster roles equations = Some witnesses ->
  PresentedCongruence witnesses input output -> Irreducible output -> output = normalize input.
Proof.
  intros roles equations witnesses input output A E N.
  apply accepted_equivalent_irreducible_output_is_the_section; [|exact N].
  now apply presented_congruence_is_sound in E.
Qed.

(** Small controls distinguish this quotient from surface elaboration and
    regular-language equivalence.  Operator 5 is an arbitrary opaque head. *)
Example nonlinear_occurrences_can_reduce_independently :
  normalize (alternative (alternative zero (LogicApplication 5 []))
    (product unit (LogicApplication 5 []))) = LogicApplication 5 [].
Proof. reflexivity. Qed.
Example nested_closure_is_part_of_the_exact_quotient :
  normalize (closure (closure (LogicApplication 5 []))) = closure (LogicApplication 5 []).
Proof. reflexivity. Qed.
Example opaque_constructor_is_not_expanded :
  normalize (LogicApplication 5 [LogicApplication 6 []]) =
    LogicApplication 5 [LogicApplication 6 []].
Proof. reflexivity. Qed.
Example every_opaque_context_normalizes_its_children :
  normalize (LogicApplication 5 [alternative zero (LogicApplication 6 []);
    closure (closure (LogicApplication 7 []))]) =
    LogicApplication 5 [LogicApplication 6 []; closure (LogicApplication 7 [])].
Proof. reflexivity. Qed.
Example unequal_variables_are_not_an_idempotence_schema :
  recognize (alternative (source_variable 0) (source_variable 1)) (source_variable 0) = None.
Proof. reflexivity. Qed.
Example closure_expansion_is_not_an_admitted_schema :
  recognize (LogicApplication 5 [source_variable 0])
    (product (source_variable 0) (closure (source_variable 0))) = None.
Proof. reflexivity. Qed.

Theorem opaque_expansion_is_not_in_the_generated_congruence :
  ~ Congruence (LogicApplication 5 [LogicApplication 6 []])
      (product (LogicApplication 6 []) (closure (LogicApplication 6 []))).
Proof.
  intros H. apply source_congruence_preserves_reference_normal_form in H.
  change (LogicApplication 5 [LogicApplication 6 []] =
    product (LogicApplication 6 []) (closure (LogicApplication 6 []))) in H.
  discriminate.
Qed.

(** Actual backward-reference source arenas show admission is inhabited.
    Source IDs deliberately differ from the mathematical role tags.  Nodes
    0 and 5 denote the SAME input variable; the idempotence equation uses
    both nodes, so node identity cannot replace variable identity. *)
Definition example_roles := {| role_sort := 2; role_zero := 7; role_unit := 11;
  role_alternative := 13; role_product := 17; role_closure := 19 |}.
Definition example_variable :=
  {| Core.term_sort := 2; Core.term_form := Core.VariableTerm 0 |}.
Definition example_application constructor arguments :=
  {| Core.term_sort := 2; Core.term_form := Core.ConstructorTerm constructor arguments |}.
Definition example_terms := [
  example_variable; example_application 7 []; example_application 11 [];
  example_application 13 [1; 0]; example_application 13 [0; 1]; example_variable;
  example_application 13 [0; 5]; example_application 17 [1; 0];
  example_application 17 [0; 1]; example_application 17 [2; 0];
  example_application 17 [0; 2]; example_application 19 [1];
  example_application 19 [2]; example_application 19 [0]; example_application 19 [13]
].
Definition example_root_variables root :=
  if (root =? 1) || (root =? 2) || (root =? 11) || (root =? 12) then [] else [0].
Definition example_equation left_root right_root : Core.RuleArena :=
  {| Core.rule_variables :=
       [{| Core.variable_sort := 2; Core.variable_role := Core.InputVariable |}];
     Core.rule_terms := example_terms;
     Core.rule_premises := []; Core.rule_premise_roots := [];
     Core.rule_allows_transition := false;
     Core.rule_lhs := left_root; Core.rule_rhs := right_root;
     Core.rule_lhs_variables := example_root_variables left_root;
     Core.rule_rhs_variables := example_root_variables right_root |}.
Definition example_roster := [
  example_equation 3 0; example_equation 4 0; example_equation 6 0;
  example_equation 7 1; example_equation 8 1; example_equation 9 0;
  example_equation 10 0; example_equation 11 2; example_equation 12 2;
  example_equation 14 13
].
Definition example_witness orientation law :=
  {| witness_orientation := orientation; witness_law := law; witness_variable := 0 |}.

Example complete_actual_source_roster_is_accepted :
  check_roster example_roles example_roster =
    Some (map (example_witness Forward) all_laws).
Proof. reflexivity. Qed.

Example reversed_actual_source_equations_are_accepted :
  check_roster example_roles [
    example_equation 0 3; example_equation 0 4; example_equation 0 6;
    example_equation 1 7; example_equation 1 8; example_equation 0 9;
    example_equation 0 10; example_equation 2 11; example_equation 2 12;
    example_equation 13 14
  ] = Some (map (example_witness Reverse) all_laws).
Proof. reflexivity. Qed.

Example duplicate_actual_source_equation_is_accepted :
  check_roster example_roles (example_roster ++ [example_equation 6 0]) =
    Some (map (example_witness Forward) all_laws ++ [example_witness Forward AltIdempotent]).
Proof. reflexivity. Qed.

Example missing_nested_closure_equation_is_rejected :
  check_roster example_roles (firstn 9 example_roster) = None.
Proof. reflexivity. Qed.

Example additional_unrecognized_equation_is_rejected :
  check_roster example_roles (example_roster ++ [example_equation 0 0]) = None.
Proof. reflexivity. Qed.

(** Finite structural carrier, separate from the set of represented terms.

    A root contractum reuses a child or a seeded constant. A contextual step
    need NOT return an original syntactic subterm: an ancestor can denote a
    different tree after one child class is merged. The carrier model below
    makes that distinction explicit. Its immutable cells are operator/child
    handles; the class map interprets their equivalence classes. A cyclic
    carrier can represent arbitrarily many finite trees without adding cells.
    This is a representation relation, not a graph algorithm or allocator.

    Physical reuse requires the existing engine's source match to correspond
    to Represented, closed child references and both constant seeds. Rebuild
    and hash-consing must realize the same quotient of existing cells. The
    following theorems prove the LOCAL mathematical reuse obligation; they do
    not assume or establish those entire Rust implementations as a theorem. *)
Definition ImmediateChild child parent :=
  exists operator children, parent = LogicApplication operator children /\ In child children.

Inductive ProperSubterm : Term -> Term -> Prop :=
| proper_immediate : forall child parent, ImmediateChild child parent -> ProperSubterm child parent
| proper_transitive : forall small middle large,
    ProperSubterm small middle -> ProperSubterm middle large -> ProperSubterm small large.

Theorem root_contractum_is_immediate_child_or_seed : forall redex contractum,
  RootStep redex contractum ->
  ImmediateChild contractum redex \/ contractum = zero \/ contractum = unit.
Proof.
  intros redex contractum H. destruct H;
    try (right; left; reflexivity); try (right; right; reflexivity).
  all: left; unfold ImmediateChild; eexists; eexists; split; [reflexivity|simpl; auto].
Qed.

Theorem root_contractum_is_proper_subterm_or_seed : forall redex contractum,
  RootStep redex contractum ->
  ProperSubterm contractum redex \/ contractum = zero \/ contractum = unit.
Proof.
  intros redex contractum H.
  destruct (root_contractum_is_immediate_child_or_seed _ _ H) as [C|S];
    [left; now apply proper_immediate|now right].
Qed.

Lemma child_occurrences_member : forall child children,
  In child children -> occurrences child <= child_occurrences children.
Proof.
  intros child children. induction children as [|first rest IH]; intros H; [contradiction|].
  destruct H as [H|H]; [subst; simpl; lia|].
  specialize (IH H). change (occurrences child <= occurrences first + child_occurrences rest). lia.
Qed.

Theorem proper_subterms_have_strictly_fewer_occurrences : forall child parent,
  ProperSubterm child parent -> occurrences child < occurrences parent.
Proof.
  intros child parent H. induction H; [|lia].
  destruct H as [operator [children [E I]]]. subst parent.
  pose proof (child_occurrences_member child children I) as B.
  change (occurrences child < S (child_occurrences children)). lia.
Qed.

Inductive CarrierCell :=
| VariableCell (variable : ScopedVariable)
| ApplicationCell (operator : nat) (children : list nat).

Definition ClosedCarrier (cells : list CarrierCell) :=
  forall node operator children,
    nth_error cells node = Some (ApplicationCell operator children) ->
    Forall (fun child => child < length cells) children.

Inductive Represented (cells : list CarrierCell) (classes : nat -> nat) : nat -> Term -> Prop :=
| represented_variable : forall handle node variable,
    nth_error cells node = Some (VariableCell variable) ->
    classes handle = classes node ->
    Represented cells classes handle (LogicVariable variable)
| represented_application : forall handle node operator references children,
    nth_error cells node = Some (ApplicationCell operator references) ->
    classes handle = classes node ->
    Forall2 (Represented cells classes) references children ->
    Represented cells classes handle (LogicApplication operator children).

Lemma forall2_right_member : forall (A B : Type) (relation : A -> B -> Prop) xs ys,
  Forall2 relation xs ys -> forall y, In y ys -> exists x, In x xs /\ relation x y.
Proof.
  intros A B relation xs ys H. induction H; intros value I; [contradiction|].
  destruct I as [E|I].
  - subst value. exists x. split; [now left|assumption].
  - destruct (IHForall2 _ I) as [found [F R]]. exists found. split; [now right|exact R].
Qed.

Theorem represented_child_reuses_an_existing_handle : forall cells classes handle parent child,
  ClosedCarrier cells -> Represented cells classes handle parent ->
  ImmediateChild child parent ->
  exists child_handle, child_handle < length cells /\ Represented cells classes child_handle child.
Proof.
  intros cells classes handle parent child Closed R [operator [children [E I]]]. subst parent.
  inversion R as [h node variable N C|h node op references terms N C T]; subst.
  destruct (forall2_right_member _ _ _ _ _ T child I) as [target [InRefs At]].
  exists target. split; [|exact At].
  specialize (Closed node operator references N).
  now apply Forall_forall with (x := target) in Closed.
Qed.

(** This is the exact seed/closure interface needed by the reducing-rule
    instantiator: existence of a contractum handle in the SAME cell table.
    No absence of productive class cycles or term-depth bound is required. *)
Theorem root_contractum_reuses_seeded_finite_carrier :
  forall cells classes root redex contractum zero_handle unit_handle,
  ClosedCarrier cells ->
  Represented cells classes root redex ->
  zero_handle < length cells -> Represented cells classes zero_handle zero ->
  unit_handle < length cells -> Represented cells classes unit_handle unit ->
  RootStep redex contractum ->
  exists result, result < length cells /\ Represented cells classes result contractum.
Proof.
  intros cells classes root redex contractum zh uh Closed R ZB Z UB U S.
  destruct (root_contractum_is_immediate_child_or_seed _ _ S) as [C|[E|E]].
  - exact (represented_child_reuses_an_existing_handle
      cells classes root redex contractum Closed R C).
  - subst contractum. exists zh. auto.
  - subst contractum. exists uh. auto.
Qed.

Lemma represented_equal_class_handle : forall cells classes handle term,
  Represented cells classes handle term -> forall alias,
  classes alias = classes handle -> Represented cells classes alias term.
Proof.
  intros cells classes handle term R. destruct R; intros alias E;
    [eapply represented_variable|eapply represented_application]; eauto; congruence.
Qed.

(** The unchanged parent cell represents BOTH trees once its selected child
    and the replacement have equal class labels. Iterating this local fact up
    an enclosing context does not require allocating new ancestor cell shapes.
    It does not assert that the two trees were literally equal before merging. *)
Theorem equivalent_child_replacement_reuses_the_parent_cell :
  forall cells classes parent operator before_ids after_ids child_handle replacement_handle
    before after child replacement,
  nth_error cells parent =
    Some (ApplicationCell operator (before_ids ++ child_handle :: after_ids)) ->
  Forall2 (Represented cells classes) before_ids before ->
  Forall2 (Represented cells classes) after_ids after ->
  Represented cells classes child_handle child ->
  Represented cells classes replacement_handle replacement ->
  classes child_handle = classes replacement_handle ->
  Represented cells classes parent (LogicApplication operator (before ++ child :: after)) /\
  Represented cells classes parent (LogicApplication operator (before ++ replacement :: after)).
Proof.
  intros cells classes parent operator before_ids after_ids ch rh before after child replacement
    Node Before After Child Replacement Equal. split.
  - eapply represented_application; [exact Node|reflexivity|].
    apply Forall2_app; [exact Before|]. constructor; assumption.
  - eapply represented_application; [exact Node|reflexivity|].
    apply Forall2_app; [exact Before|]. constructor; [|exact After].
    eapply represented_equal_class_handle; eauto.
Qed.

(** A successful class merge is an onto quotient of the old finite class set
    which identifies two previously DISTINCT classes. This interface permits
    additional congruence-induced merges and arbitrary representative labels.
    It contains neither a decreasing-count premise nor an engine-correctness
    premise. No-op/refired equalities do not satisfy the distinct-class field.

    Physical refinement must establish exact class enumeration and the onto
    quotient map for a reported successful merge. The numerical theorem does
    not certify Rust's union-find, rebuild, match enumeration or loop reports. *)
Definition FiniteClassMerge (before after : list nat) : Prop :=
  NoDup before /\ NoDup after /\ exists quotient : nat -> nat,
    (forall new_class, In new_class after <->
      exists old_class, In old_class before /\ quotient old_class = new_class) /\
    exists first second, In first before /\ In second before /\
      first <> second /\ quotient first = quotient second.

Theorem successful_finite_class_merge_strictly_decreases_classes : forall before after,
  FiniteClassMerge before after -> length after < length before.
Proof.
  intros before after [Old [New [quotient [Image [first [second [F [S [Different Equal]]]]]]]]].
  assert (Included : incl after (map quotient (remove Nat.eq_dec first before))).
  { intros new_class InAfter.
    destruct (proj1 (Image new_class) InAfter) as [old_class [InBefore Maps]].
    destruct (Nat.eq_dec old_class first) as [Same|Other].
    - subst old_class. apply in_map_iff. exists second. split; [congruence|].
      apply in_in_remove; [congruence|exact S].
    - apply in_map_iff. exists old_class. split; [exact Maps|].
      now apply in_in_remove. }
  pose proof (@NoDup_incl_length nat after
    (map quotient (remove Nat.eq_dec first before)) New Included) as Bound.
  rewrite length_map in Bound.
  pose proof (@remove_length_lt nat Nat.eq_dec before first F) as Strict. lia.
Qed.

Definition EnumeratesCarrierClasses (cells : list CarrierCell) (classes : nat -> nat) labels :=
  NoDup labels /\ forall label, In label labels <->
    exists handle, handle < length cells /\ classes handle = label.

Theorem finite_classes_are_bounded_by_carrier_nodes : forall cells classes labels,
  EnumeratesCarrierClasses cells classes labels -> length labels <= length cells.
Proof.
  intros cells classes labels [Distinct Exact].
  assert (Included : incl labels (map classes (seq 0 (length cells)))).
  { intros label I. destruct (proj1 (Exact label) I) as [handle [Bound Same]].
    apply in_map_iff. exists handle. split; [exact Same|]. apply in_seq. lia. }
  pose proof (@NoDup_incl_length nat labels (map classes (seq 0 (length cells)))
    Distinct Included) as Bound.
  now rewrite length_map, length_seq in Bound.
Qed.

Inductive SuccessfulMergeChain : nat -> list nat -> list nat -> Prop :=
| merge_chain_empty : forall classes, SuccessfulMergeChain 0 classes classes
| merge_chain_next : forall count before middle after,
    FiniteClassMerge before middle -> SuccessfulMergeChain count middle after ->
    SuccessfulMergeChain (S count) before after.

Theorem successful_merge_chain_consumes_finite_class_count : forall count before after,
  SuccessfulMergeChain count before after -> count + length after <= length before.
Proof.
  intros count before after H. induction H; [lia|].
  pose proof (successful_finite_class_merge_strictly_decreases_classes _ _ H). lia.
Qed.

Theorem successful_merges_are_bounded_by_the_initial_carrier :
  forall cells classes before after count,
  EnumeratesCarrierClasses cells classes before ->
  SuccessfulMergeChain count before after -> count + length after <= length cells.
Proof.
  intros cells classes before after count E C.
  pose proof (finite_classes_are_bounded_by_carrier_nodes _ _ _ E).
  pose proof (successful_merge_chain_consumes_finite_class_count _ _ _ C). lia.
Qed.

(** Reuse Dovetail's existing fact-set saturation soundness. Each generated
    equality carries a LOCAL root-schema instance and the two interpretation
    equalities connecting that instance to its handles. The root equation's
    soundness is proved above, not an opaque native-fold assumption. There are
    no directed guest rewrite facts and no native callbacks in this profile.

    This fact-set composition does not establish completeness of physical
    matching, reported convergence, or bounded extraction. In particular the
    finite merge bound is not a proof that an arbitrary matcher terminates or
    that an iteration-limit report can be treated as convergence. *)
Definition section_fact_good (meaning : nat -> Term) fact :=
  match fact with
  | Sat.EqFact first second => Congruence (meaning first) (meaning second)
  | Sat.RwFact _ _ => False
  end.
Definition section_root_facts (meaning : nat -> Term) fact :=
  exists first second redex contractum,
    fact = Sat.EqFact first second /\
    Congruence (meaning first) redex /\ RootStep redex contractum /\
    Congruence contractum (meaning second).

Lemma section_root_facts_are_sound : forall meaning,
  Sat.sound_state (section_fact_good meaning) (section_root_facts meaning).
Proof.
  intros meaning fact [first [second [redex [contractum [E [L [S R]]]]]]].
  subst fact. simpl. eapply congruence_trans with (y := redex); [exact L|].
  eapply congruence_trans with (y := contractum); [now apply congruence_root|exact R].
Qed.

Theorem existing_saturation_step_preserves_section_soundness : forall meaning state,
  Sat.sound_state (section_fact_good meaning) state ->
  Sat.sound_state (section_fact_good meaning)
    (Sat.saturate_step state (section_root_facts meaning)).
Proof.
  intros meaning state H. apply Sat.saturate_step_sound;
    [exact H|apply section_root_facts_are_sound].
Qed.

Theorem existing_iterated_saturation_preserves_section_soundness : forall count meaning state,
  Sat.sound_state (section_fact_good meaning) state ->
  Sat.sound_state (section_fact_good meaning)
    (Sat.saturate_n count (section_root_facts meaning) state).
Proof.
  intros count meaning state H. apply Sat.saturate_n_sound;
    [exact H|apply section_root_facts_are_sound].
Qed.

Print Assumptions every_contextual_collapse_strictly_decreases_occurrences.
Print Assumptions collapse_reduction_terminates.
Print Assumptions source_congruence_preserves_reference_normal_form.
Print Assumptions every_term_has_a_reachable_normal_form.
Print Assumptions equivalent_normal_forms_are_equal.
Print Assumptions congruence_iff_equal_normal_forms.
Print Assumptions reference_normalization_idempotent.
Print Assumptions accepted_equivalent_irreducible_output_is_the_section.
Print Assumptions admitted_roster_is_exact_and_complete.
Print Assumptions admitted_source_presentation_has_exactly_the_ten_equation_quotient.
Print Assumptions admitted_source_section_is_sound_and_idempotent.
Print Assumptions admitted_source_section_is_quotient_invariant.
Print Assumptions admitted_source_accepted_output_is_exact.
Print Assumptions opaque_expansion_is_not_in_the_generated_congruence.
Print Assumptions complete_actual_source_roster_is_accepted.
Print Assumptions reversed_actual_source_equations_are_accepted.
Print Assumptions duplicate_actual_source_equation_is_accepted.
Print Assumptions missing_nested_closure_equation_is_rejected.
Print Assumptions additional_unrecognized_equation_is_rejected.
Print Assumptions root_contractum_is_proper_subterm_or_seed.
Print Assumptions proper_subterms_have_strictly_fewer_occurrences.
Print Assumptions root_contractum_reuses_seeded_finite_carrier.
Print Assumptions equivalent_child_replacement_reuses_the_parent_cell.
Print Assumptions successful_finite_class_merge_strictly_decreases_classes.
Print Assumptions successful_merges_are_bounded_by_the_initial_carrier.
Print Assumptions existing_saturation_step_preserves_section_soundness.
Print Assumptions existing_iterated_saturation_preserves_section_soundness.

End SourceEquationSection.
