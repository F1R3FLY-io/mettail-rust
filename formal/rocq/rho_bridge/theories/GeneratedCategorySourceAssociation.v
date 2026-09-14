(** Recover the original category arm from the existing concrete source.
    A position's immutable lookup determines its category and both operands.
    Category equality is explicitly decidable; same-index pair injection uses
    Stdlib Eqdep_dec, not Term equality or a proof-irrelevance axiom. This
    transports the SAME constructor-binding witness, not a semantic result.
    The Rust census/selector association remains a separate source audit. *)
From Stdlib Require Import List Logic.Eqdep_dec.
From RhoBridge Require Import GeneratedSourceRowComparison GeneratedMapOwnerTraversal
  GeneratedMapSourceOwnership GeneratedConstructorComparisonClasses
  GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.

Module GeneratedCategorySourceAssociation.
Section OriginalLookupAssociation.
Context {Cat : Type}.
Variable category_eq_dec : forall left right : Cat, {left = right} + {left <> right}.
Variable Term : Cat -> Type.
Variable lookup : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  option { category : Cat & (Term category * Term category)%type }.

Theorem the_same_position_has_the_same_original_category :
  forall category other_category position (left right : Term category)
    (other_left other_right : Term other_category),
  pair_at Term lookup category position left right ->
  pair_at Term lookup other_category position other_left other_right ->
  category = other_category.
Proof.
  intros category other_category position left right other_left other_right LEFT RIGHT.
  unfold pair_at in LEFT, RIGHT.
  assert (PACKED : existT (fun c => (Term c * Term c)%type) category (left, right) =
    existT (fun c => (Term c * Term c)%type) other_category (other_left, other_right))
    by congruence.
  exact (f_equal (@projT1 Cat (fun c => (Term c * Term c)%type)) PACKED).
Qed.

Theorem the_same_category_position_has_the_exact_original_operands :
  forall category position (left right other_left other_right : Term category),
  pair_at Term lookup category position left right ->
  pair_at Term lookup category position other_left other_right ->
  left = other_left /\ right = other_right.
Proof.
  intros category position left right other_left other_right LEFT RIGHT.
  unfold pair_at in LEFT, RIGHT.
  assert (PACKED : existT (fun c => (Term c * Term c)%type) category (left, right) =
    existT (fun c => (Term c * Term c)%type) category (other_left, other_right))
    by congruence.
  pose proof (@inj_pair2_eq_dec Cat category_eq_dec (fun c => (Term c * Term c)%type)
    category (left, right) (other_left, other_right) PACKED) as PAIR.
  injection PAIR as L R. split; assumption.
Qed.

Variables maximum owner_ceiling : nat.
Variable category_callback : Cat -> nat.
Variables uid_digest binder_digest : nat -> nat.
Variable signature : Cat -> list (@Row Cat).
Variable observe : forall category, Term category -> SourceObservation signature Term category.
Local Notation Cells := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.State Cat Term).
Local Notation Make := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.make_map_box
  Cat Term maximum owner_ceiling category_callback).
Local Notation Binding := (@CategoryArmBinding Cat signature Term Cells uid_digest binder_digest
  observe lookup Make).
Local Notation Source := (@GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.arm_source
  Cat Term maximum owner_ceiling category_callback uid_digest binder_digest lookup signature observe).

Theorem the_original_arm_binding_retains_its_lookup_pair :
  forall category position left right before exit events after,
  Binding category position left right before exit events after ->
  pair_at Term lookup category position left right.
Proof.
  intros category position left right before exit events after BINDING.
  destruct BINDING; assumption.
Qed.

Theorem the_concrete_source_recovers_the_callers_original_constructor_binding :
  forall category position left right before exit events after,
  pair_at Term lookup category position left right ->
  Source position before exit events after ->
  Binding category position left right before exit events after.
Proof.
  intros category position left right before exit events after REQUEST
    [other_category [other_left [other_right BINDING]]].
  pose proof (the_original_arm_binding_retains_its_lookup_pair
    other_category position other_left other_right before exit events after BINDING) as ORIGINAL.
  pose proof (the_same_position_has_the_same_original_category
    category other_category position left right other_left other_right REQUEST ORIGINAL) as CATEGORY.
  subst other_category.
  destruct (the_same_category_position_has_the_exact_original_operands
    category position left right other_left other_right REQUEST ORIGINAL) as [LEFT RIGHT].
  subst other_left other_right. exact BINDING.
Qed.
End OriginalLookupAssociation.
End GeneratedCategorySourceAssociation.

Print Assumptions GeneratedCategorySourceAssociation.the_same_position_has_the_same_original_category.
Print Assumptions GeneratedCategorySourceAssociation.the_same_category_position_has_the_exact_original_operands.
Print Assumptions GeneratedCategorySourceAssociation.the_original_arm_binding_retains_its_lookup_pair.
Print Assumptions GeneratedCategorySourceAssociation.the_concrete_source_recovers_the_callers_original_constructor_binding.
