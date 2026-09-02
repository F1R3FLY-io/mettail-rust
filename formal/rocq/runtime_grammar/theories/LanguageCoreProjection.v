(**
  LanguageCoreProjection: lossless canonical projection obligations shared by
  the compile-time [language!] frontend and the in-Rholang DDL frontend.

  The model names the four parser-relevant fields that a migration must not
  erase: category variable admission, shared precedence levels, contextual
  keyword exceptions, and the complete recovery profile.  It also separates
  GrammarCore identity from TheoryCore identity and checks the structural-only
  migration of [language/2] plus the presence constraints of [language/3].

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Module LanguageCoreProjection.

Record RecoveryProfile := {
  recovery_costs : list nat;
  recovery_thresholds : list nat;
  recovery_multipliers : list nat;
  recovery_beam : option nat
}.

Record ParserProfile := {
  parser_beam : option nat;
  parser_contextual_keywords : list nat;
  parser_recovery : RecoveryProfile
}.

Record CategoryDecl := {
  category_name : nat;
  category_primary : bool;
  category_admits_variables : bool
}.

Record TermDecl := {
  term_label : nat;
  term_result : nat;
  term_binding_power : option nat;
  term_shares_previous_level : bool
}.

Record GrammarSurface := {
  surface_categories : list CategoryDecl;
  surface_terms : list TermDecl;
  surface_parser : ParserProfile
}.

(** The canonical grammar value deliberately has the same information but a
    separately named type, so the round-trip theorem is not definitional
    equality on one record. *)
Record CanonicalGrammarValue := {
  value_categories : list CategoryDecl;
  value_terms : list TermDecl;
  value_parser : ParserProfile
}.

Definition encode_grammar (surface : GrammarSurface) : CanonicalGrammarValue :=
  {| value_categories := surface_categories surface;
     value_terms := surface_terms surface;
     value_parser := surface_parser surface |}.

Definition decode_grammar (value : CanonicalGrammarValue) : GrammarSurface :=
  {| surface_categories := value_categories value;
     surface_terms := value_terms value;
     surface_parser := value_parser value |}.

Theorem grammar_encoding_is_lossless :
  forall surface, decode_grammar (encode_grammar surface) = surface.
Proof.
  intros [categories terms parser].
  reflexivity.
Qed.

Theorem variable_admission_survives_round_trip :
  forall surface,
    map category_admits_variables
        (surface_categories (decode_grammar (encode_grammar surface))) =
    map category_admits_variables (surface_categories surface).
Proof.
  intros surface.
  now rewrite grammar_encoding_is_lossless.
Qed.

Theorem precedence_cohorts_survive_round_trip :
  forall surface,
    map term_shares_previous_level
        (surface_terms (decode_grammar (encode_grammar surface))) =
    map term_shares_previous_level (surface_terms surface).
Proof.
  intros surface.
  now rewrite grammar_encoding_is_lossless.
Qed.

Theorem parser_policy_survives_round_trip :
  forall surface,
    surface_parser (decode_grammar (encode_grammar surface)) =
    surface_parser surface.
Proof.
  intros surface.
  now rewrite grammar_encoding_is_lossless.
Qed.

Inductive TheoryProfile :=
| StructuralOnly
| OslfTheory
    (interactive : bool)
    (continued : bool)
    (cost : bool)
    (semantic_commitment : list nat).

Definition theory_profile_valid (theory : TheoryProfile) : bool :=
  match theory with
  | StructuralOnly => true
  | OslfTheory interactive continued cost _ =>
      implb continued interactive && implb cost continued
  end.

Inductive LanguageValue :=
| Language2 (grammar : CanonicalGrammarValue)
| Language3 (grammar : CanonicalGrammarValue) (theory : TheoryProfile).

Record LanguageCoreV1 := {
  core_grammar : GrammarSurface;
  core_theory : TheoryProfile
}.

Definition lower_language (value : LanguageValue) : option LanguageCoreV1 :=
  match value with
  | Language2 grammar =>
      Some {| core_grammar := decode_grammar grammar;
              core_theory := StructuralOnly |}
  | Language3 grammar theory =>
      if theory_profile_valid theory then
        Some {| core_grammar := decode_grammar grammar;
                core_theory := theory |}
      else None
  end.

Theorem language2_migrates_to_structural_only :
  forall grammar,
    lower_language (Language2 grammar) =
    Some {| core_grammar := decode_grammar grammar;
            core_theory := StructuralOnly |}.
Proof.
  reflexivity.
Qed.

Lemma implb_true_left :
  forall premise conclusion,
    implb premise conclusion = true -> premise = true -> conclusion = true.
Proof.
  intros [] [] Himpl Hpremise; simpl in *; congruence.
Qed.

Theorem admitted_continued_profile_is_interactive :
  forall grammar interactive continued cost commitment core,
    lower_language
      (Language3 grammar (OslfTheory interactive continued cost commitment)) =
      Some core ->
    continued = true ->
    interactive = true.
Proof.
  intros grammar interactive continued cost commitment core Hlower Hcontinued.
  unfold lower_language, theory_profile_valid in Hlower.
  remember (implb continued interactive && implb cost continued) as valid
    eqn:Hvalid.
  destruct valid; [| discriminate].
  symmetry in Hvalid.
  apply andb_true_iff in Hvalid as [Hpresence _].
  now apply (implb_true_left continued interactive Hpresence Hcontinued).
Qed.

Theorem admitted_cost_profile_is_continued :
  forall grammar interactive continued cost commitment core,
    lower_language
      (Language3 grammar (OslfTheory interactive continued cost commitment)) =
      Some core ->
    cost = true ->
    continued = true.
Proof.
  intros grammar interactive continued cost commitment core Hlower Hcost.
  unfold lower_language, theory_profile_valid in Hlower.
  remember (implb continued interactive && implb cost continued) as valid
    eqn:Hvalid.
  destruct valid; [| discriminate].
  symmetry in Hvalid.
  apply andb_true_iff in Hvalid as [_ Hpresence].
  now apply (implb_true_left cost continued Hpresence Hcost).
Qed.

Definition grammar_commitment (core : LanguageCoreV1) : GrammarSurface :=
  core_grammar core.

Definition theory_commitment (core : LanguageCoreV1) : TheoryProfile :=
  core_theory core.

Definition language_commitment (core : LanguageCoreV1) :
    GrammarSurface * TheoryProfile :=
  (grammar_commitment core, theory_commitment core).

Theorem theory_only_change_preserves_grammar_commitment :
  forall grammar left right,
    grammar_commitment {| core_grammar := grammar; core_theory := left |} =
    grammar_commitment {| core_grammar := grammar; core_theory := right |}.
Proof.
  reflexivity.
Qed.

Theorem language_commitment_equality_exposes_both_projections :
  forall left right,
    language_commitment left = language_commitment right ->
    grammar_commitment left = grammar_commitment right /\
    theory_commitment left = theory_commitment right.
Proof.
  intros [left_grammar left_theory] [right_grammar right_theory] Heq.
  simpl in Heq.
  inversion Heq.
  now split.
Qed.

Theorem language2_and_structural_language3_share_parser_projection :
  forall grammar core2 core3,
    lower_language (Language2 grammar) = Some core2 ->
    lower_language (Language3 grammar (OslfTheory false false false [])) = Some core3 ->
    grammar_commitment core2 = grammar_commitment core3.
Proof.
  intros grammar core2 core3 Htwo Hthree.
  simpl in Htwo, Hthree.
  inversion Htwo; inversion Hthree.
  reflexivity.
Qed.

End LanguageCoreProjection.
