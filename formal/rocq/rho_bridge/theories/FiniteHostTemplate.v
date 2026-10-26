From Stdlib Require Import Lists.List Sorting.Permutation Lia.
From RhoBridge Require Import FiniteCostGradeFold.
From CostAccountedRho Require Import CostAccountedSyntax CAJoinConservation
  AuthorityPresentation.
Import ListNotations.

(* [nil_quote] denotes the native encoding of the canonical quoted Nil.
   This module does not model its codec, lane hash, or Rust demand analyzer.
   It connects the existing finite template to native payable authority atoms.
   Rust canonicalization must establish [canonical_signature_for]; native
   analyzer correspondence is checked separately against the real functions. *)
Section FiniteHostTemplate.

Variable nil_quote : list bool.

Fixpoint native_grade_signature (grade : Grade) : sig :=
  match grade with
  | GradeUnit => SUnit
  | GradeGenerator _ => SQuote nil_quote
  | GradeProduct lhs rhs =>
      SAnd (native_grade_signature lhs) (native_grade_signature rhs)
  end.

Definition native_template_cells (grade : Grade) : list (list sig) :=
  map (map (fun _ : nat => SQuote nil_quote)) (template_demand_lanes grade).

Theorem native_grade_atoms_match_finite_interpretation : forall grade,
  payable_sig_atoms (native_grade_signature grade) =
  map (fun _ : nat => SQuote nil_quote) (signature_atoms grade).
Proof.
  induction grade as [|id|left IHleft right IHright]; simpl; auto.
  rewrite map_app, IHleft, IHright. reflexivity.
Qed.

Theorem native_grade_preserves_generator_occurrences : forall grade,
  length (payable_sig_atoms (native_grade_signature grade)) =
  length (grade_generators grade).
Proof.
  intro grade. rewrite native_grade_atoms_match_finite_interpretation, length_map.
  apply no_guest_generator_occurrence_is_lost.
Qed.

Lemma quoted_atom_count : forall atoms,
  count_occ sig_eq_dec (map (fun _ : nat => SQuote nil_quote) atoms)
    (SQuote nil_quote) = length atoms.
Proof.
  induction atoms as [|head tail IH]; [reflexivity |].
  change (count_occ sig_eq_dec
    (SQuote nil_quote :: map (fun _ : nat => SQuote nil_quote) tail)
    (SQuote nil_quote) = S (length tail)).
  rewrite count_occ_cons_eq by reflexivity. now rewrite IH.
Qed.

Theorem native_grade_preserves_quoted_nil_multiplicity : forall grade,
  count_occ sig_eq_dec (payable_sig_atoms (native_grade_signature grade))
    (SQuote nil_quote) = length (grade_generators grade).
Proof.
  intro grade. rewrite native_grade_atoms_match_finite_interpretation,
    quoted_atom_count. apply no_guest_generator_occurrence_is_lost.
Qed.

Theorem native_grade_unit_is_neutral : forall grade,
  payable_sig_atoms (native_grade_signature (GradeProduct GradeUnit grade)) =
    payable_sig_atoms (native_grade_signature grade) /\
  payable_sig_atoms (native_grade_signature (GradeProduct grade GradeUnit)) =
    payable_sig_atoms (native_grade_signature grade).
Proof. intro grade. apply payable_unit_is_neutral. Qed.

Theorem native_grade_product_keeps_all_atoms : forall left right,
  payable_sig_atoms (native_grade_signature (GradeProduct left right)) =
  payable_sig_atoms (native_grade_signature left) ++
    payable_sig_atoms (native_grade_signature right).
Proof. reflexivity. Qed.

Theorem native_template_flattens_to_grade_atoms : forall grade,
  concat (native_template_cells grade) =
  payable_sig_atoms (native_grade_signature grade).
Proof.
  intro grade. rewrite native_grade_atoms_match_finite_interpretation.
  unfold native_template_cells, template_demand_lanes.
  destruct (signature_atoms grade); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Theorem native_template_exactly_covers_grade : forall grade,
  exact_cover (payable_sig_atoms (native_grade_signature grade))
    (native_template_cells grade).
Proof.
  intro grade. unfold exact_cover, presentation_atoms.
  rewrite native_template_flattens_to_grade_atoms. apply Permutation_refl.
Qed.

Theorem native_unit_template_has_no_cells :
  native_template_cells GradeUnit = [].
Proof. reflexivity. Qed.

Theorem native_nonunit_template_is_one_whole_cell : forall grade,
  signature_atoms grade <> [] ->
  native_template_cells grade =
    [payable_sig_atoms (native_grade_signature grade)].
Proof.
  intros grade Hnonempty. rewrite native_grade_atoms_match_finite_interpretation.
  unfold native_template_cells, template_demand_lanes.
  destruct (signature_atoms grade); [contradiction | reflexivity].
Qed.

(* This is an explicit source-refinement premise, not a theorem about the
   Rust normalizer. It allows rebracketing, reordering, and removal of units
   while forbidding atom loss, duplication, or replacement. *)
Definition canonical_signature_for (grade : Grade) (canonical : sig) : Prop :=
  Permutation (payable_sig_atoms canonical)
    (payable_sig_atoms (native_grade_signature grade)).

Theorem canonical_template_preserves_exact_cover : forall grade canonical,
  canonical_signature_for grade canonical ->
  exact_cover (payable_sig_atoms canonical) (native_template_cells grade).
Proof.
  intros grade canonical Hcanonical.
  unfold exact_cover, presentation_atoms.
  rewrite native_template_flattens_to_grade_atoms.
  apply Permutation_sym. exact Hcanonical.
Qed.

Theorem canonical_signature_keeps_quoted_nil_multiplicity : forall grade canonical,
  canonical_signature_for grade canonical ->
  count_occ sig_eq_dec (payable_sig_atoms canonical) (SQuote nil_quote) =
    length (grade_generators grade).
Proof.
  intros grade canonical Hcanonical.
  rewrite (proj1 (Permutation_count_occ sig_eq_dec _ _) Hcanonical).
  apply native_grade_preserves_quoted_nil_multiplicity.
Qed.

Theorem canonical_funding_retains_every_atom : forall grade canonical presented atom,
  canonical_signature_for grade canonical ->
  exact_cover (payable_sig_atoms canonical) presented ->
  count_occ sig_eq_dec (presentation_atoms presented) atom =
  count_occ sig_eq_dec
    (map (fun _ : nat => SQuote nil_quote) (signature_atoms grade)) atom.
Proof.
  intros grade canonical presented atom Hcanonical Hcover.
  rewrite (exact_cover_preserves_each_atom sig_eq_dec _ _ atom Hcover).
  rewrite (proj1 (Permutation_count_occ sig_eq_dec _ _) Hcanonical).
  rewrite native_grade_atoms_match_finite_interpretation. reflexivity.
Qed.

Theorem canonical_funding_cannot_drop_generator_occurrences :
  forall grade canonical presented,
  canonical_signature_for grade canonical ->
  exact_cover (payable_sig_atoms canonical) presented ->
  count_occ sig_eq_dec (presentation_atoms presented) (SQuote nil_quote) =
    length (grade_generators grade).
Proof.
  intros grade canonical presented Hcanonical Hcover.
  rewrite (canonical_funding_retains_every_atom grade canonical presented
    (SQuote nil_quote) Hcanonical Hcover), quoted_atom_count.
  apply no_guest_generator_occurrence_is_lost.
Qed.

End FiniteHostTemplate.

Print Assumptions native_grade_atoms_match_finite_interpretation.
Print Assumptions native_grade_preserves_generator_occurrences.
Print Assumptions native_grade_preserves_quoted_nil_multiplicity.
Print Assumptions native_grade_unit_is_neutral.
Print Assumptions native_grade_product_keeps_all_atoms.
Print Assumptions native_template_flattens_to_grade_atoms.
Print Assumptions native_template_exactly_covers_grade.
Print Assumptions native_unit_template_has_no_cells.
Print Assumptions native_nonunit_template_is_one_whole_cell.
Print Assumptions canonical_template_preserves_exact_cover.
Print Assumptions canonical_signature_keeps_quoted_nil_multiplicity.
Print Assumptions canonical_funding_retains_every_atom.
Print Assumptions canonical_funding_cannot_drop_generator_occurrences.
