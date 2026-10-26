From Stdlib Require Import Bool.

Section QuotientCommitment.

Context {Term Class Digest : Type}.
Context (quotient : Term -> Class) (section : Class -> Term) (digest : Term -> Digest).

Definition class_commitment (term : Term) := digest (section (quotient term)).

Theorem quotient_equal_terms_have_equal_class_commitments : forall left right,
  quotient left = quotient right -> class_commitment left = class_commitment right.
Proof. intros left right Heq. unfold class_commitment. now rewrite Heq. Qed.

Theorem section_round_trip_keeps_class :
  (forall class, quotient (section class) = class) ->
  forall term, quotient (section (quotient term)) = quotient term.
Proof. intros Hsection term. apply Hsection. Qed.

Theorem class_commitment_cannot_distinguish_equal_class_representatives :
  forall left right, left <> right -> quotient left = quotient right ->
  ~ (forall x y, class_commitment x = class_commitment y -> x = y).
Proof.
  intros left right Hdifferent Hclass Hinjective.
  apply Hdifferent. apply Hinjective.
  now apply quotient_equal_terms_have_equal_class_commitments.
Qed.

Theorem representative_injectivity_does_not_supply_quotient_coherence :
  (forall x y, digest x = digest y -> x = y) ->
  forall left right, left <> right -> quotient left = quotient right ->
  digest left <> digest right /\ class_commitment left = class_commitment right.
Proof.
  intros Hinjective left right Hdifferent Hclass. split.
  - intro Hsame. apply Hdifferent. now apply Hinjective.
  - now apply quotient_equal_terms_have_equal_class_commitments.
Qed.

End QuotientCommitment.

Definition example_quotient (_ : bool) := tt.
Definition example_section (_ : unit) := true.
Definition example_digest (term : bool) := term.

Example nontrivial_section_satisfies_its_round_trip :
  forall class, example_quotient (example_section class) = class.
Proof. intros []. reflexivity. Qed.

Example raw_and_class_commitments_are_different_contracts :
  example_digest true <> example_digest false /\
  class_commitment example_quotient example_section example_digest true =
  class_commitment example_quotient example_section example_digest false.
Proof. split; [discriminate | reflexivity]. Qed.

Print Assumptions quotient_equal_terms_have_equal_class_commitments.
Print Assumptions section_round_trip_keeps_class.
Print Assumptions class_commitment_cannot_distinguish_equal_class_representatives.
Print Assumptions representative_injectivity_does_not_supply_quotient_coherence.
Print Assumptions nontrivial_section_satisfies_its_round_trip.
Print Assumptions raw_and_class_commitments_are_different_contracts.
