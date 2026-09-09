(** * Declared nonassociativity for the existing unary-postfix admission step

    Recognition and category-child selection are unchanged. Once a retained
    candidate reaches the postfix check, its operand's top production supplies
    an optional power. An unranked grouping production is therefore admitted
    without interpreting parentheses or descending through the group.

    Missing parent power preserves the existing unconditional admission; this
    differs from an unranked child under a ranked parent. Strictness is a
    comparison, never an increment in the bounded implementation's power type.

    Candidate laws are relative to the supplied family. They establish neither
    global forest completeness nor preservation of raw derivations already
    identified by the runtime's existing deduplication. The Rust category-index
    selection, schema codec, and image commitment require concrete checks. *)
From Stdlib Require Import List Arith Bool Lia.
From RuntimeGrammar Require Import CategoricalPrattFloor JuxtapositionPrecedence.
Import ListNotations.

Definition postfix_allows_equal (assoc : Associativity) : bool :=
  match assoc with NonAssociative => false | _ => true end.

Definition postfix_admission (assoc : Associativity)
    (parent child : option nat) : bool :=
  match parent with
  | None => true
  | Some power => tighter power (postfix_allows_equal assoc) child
  end.

Theorem absent_parent_power_preserves_admission : forall assoc child,
  postfix_admission assoc None child = true.
Proof. reflexivity. Qed.

Theorem unranked_child_remains_admitted : forall assoc parent,
  postfix_admission assoc parent None = true.
Proof. intros assoc [power|]; reflexivity. Qed.

Theorem left_and_right_postfix_behavior_is_unchanged : forall parent child,
  postfix_admission Left parent child =
    match parent with None => true | Some power => tighter power true child end /\
  postfix_admission Right parent child = postfix_admission Left parent child.
Proof. intros [power|] child; split; reflexivity. Qed.

Theorem equal_power_is_rejected_only_when_declared_nonassociative : forall power,
  postfix_admission Left (Some power) (Some power) = true /\
  postfix_admission Right (Some power) (Some power) = true /\
  postfix_admission NonAssociative (Some power) (Some power) = false.
Proof.
  intro power; unfold postfix_admission, postfix_allows_equal, tighter.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl; repeat split; reflexivity.
Qed.

Theorem ranked_nonassociative_postfix_is_exact_strict_comparison : forall parent child,
  postfix_admission NonAssociative (Some parent) (Some child) = true <-> parent < child.
Proof.
  intros; unfold postfix_admission, postfix_allows_equal, tighter; simpl.
  rewrite orb_false_r; apply Nat.ltb_lt.
Qed.

Theorem tighter_child_is_admitted_for_every_associativity : forall assoc parent child,
  parent < child -> postfix_admission assoc (Some parent) (Some child) = true.
Proof.
  intros assoc parent child H.
  assert (Hlt : (parent <? child) = true) by (apply Nat.ltb_lt; exact H).
  unfold postfix_admission, tighter; now rewrite Hlt.
Qed.

Theorem lower_power_child_is_rejected_for_every_associativity : forall assoc parent child,
  child < parent -> postfix_admission assoc (Some parent) (Some child) = false.
Proof.
  intros assoc parent child H.
  assert (Hlt : (parent <? child) = false) by (apply Nat.ltb_ge; lia).
  assert (Heq : (child =? parent) = false) by (apply Nat.eqb_neq; lia).
  unfold postfix_admission, tighter; rewrite Hlt, Heq.
  now rewrite andb_false_r.
Qed.

Theorem maximum_power_needs_no_increment : forall maximum child,
  child <= maximum ->
  postfix_admission NonAssociative (Some maximum) (Some child) = false.
Proof.
  intros maximum child H.
  unfold postfix_admission, postfix_allows_equal, tighter; simpl.
  rewrite orb_false_r; apply Nat.ltb_ge; exact H.
Qed.

Theorem postfix_reuses_category_indexed_pratt_admission : forall assoc parent child,
  postfix_admission assoc (Some parent) (Some child) =
  admits_infix (operand_floor parent (postfix_allows_equal assoc)) (child_operator child).
Proof. intros; apply tighter_refines_existing_pratt_admission. Qed.

Section RetainedCandidates.
  Context {Candidate : Type}.
  Variable assoc : Associativity.
  Variable parent : option nat.
  Variable operand_power : Candidate -> option nat.

  Definition postfix_evidence (candidate : Candidate) : bool :=
    postfix_admission assoc parent (operand_power candidate).
  Definition retained_postfix_candidates := @admitted Candidate postfix_evidence.

  Theorem postfix_filter_preserves_exact_candidate : forall candidates candidate,
    In candidate (retained_postfix_candidates candidates) <->
    In candidate candidates /\ postfix_evidence candidate = true.
  Proof. intros; apply admission_preserves_exact_candidate. Qed.

  Theorem admitted_postfix_family_is_unchanged : forall candidates,
    Forall (fun candidate => postfix_evidence candidate = true) candidates ->
    retained_postfix_candidates candidates = candidates.
  Proof. intros; now apply already_admitted_family_is_unchanged. Qed.

  Theorem admitted_occurrence_retains_its_order_and_payload : forall before after candidate,
    postfix_evidence candidate = true ->
    retained_postfix_candidates (before ++ candidate :: after) =
      retained_postfix_candidates before ++ candidate :: retained_postfix_candidates after.
  Proof.
    intros before after candidate H.
    unfold retained_postfix_candidates, admitted; rewrite filter_app; simpl.
    now rewrite H.
  Qed.
End RetainedCandidates.

Print Assumptions absent_parent_power_preserves_admission.
Print Assumptions unranked_child_remains_admitted.
Print Assumptions left_and_right_postfix_behavior_is_unchanged.
Print Assumptions equal_power_is_rejected_only_when_declared_nonassociative.
Print Assumptions ranked_nonassociative_postfix_is_exact_strict_comparison.
Print Assumptions tighter_child_is_admitted_for_every_associativity.
Print Assumptions lower_power_child_is_rejected_for_every_associativity.
Print Assumptions maximum_power_needs_no_increment.
Print Assumptions postfix_reuses_category_indexed_pratt_admission.
Print Assumptions postfix_filter_preserves_exact_candidate.
Print Assumptions admitted_postfix_family_is_unchanged.
Print Assumptions admitted_occurrence_retains_its_order_and_payload.
