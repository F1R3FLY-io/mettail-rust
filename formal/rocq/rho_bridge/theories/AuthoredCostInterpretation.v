(* Conditional interpretation lemmas, not admission of authored witness names.
   Source shapes, step correspondence, and law-side interpretations are inputs.
   Their binding to installed grammar/rule identities is not proved here.
   Native well-wrapping alone is insufficient: every signed_term is wrapped.
   The no-leak conclusions below use correspondence of actual source steps.
   This file defines no DDL syntax, runtime certificate, or new evaluator. *)

From Stdlib Require Import Lists.List Bool.
From CostAccountedRho Require Import CostAccountedSyntax CASyntax CAReduction
  CAGradedTransition WrappingSubjectReduction CostMonad CACategory.
Import ListNotations.

Section SourceSteps.

Context {Source Label : Type}.
Variable interpret : Source -> signed_term.
Variable interpret_label : Label -> sig.
Variable source_step : Source -> Label -> Source -> Prop.

Hypothesis source_step_correspondence : forall before label after,
  source_step before label after ->
  graded_step (interpret before) (interpret_label label) (interpret after).

Theorem source_step_has_native_reduction : forall before label after,
  source_step before label after -> ca_step (interpret before) (interpret after).
Proof.
  intros before label after Hstep.
  apply (graded_step_sound _ (interpret_label label) _).
  now apply source_step_correspondence.
Qed.

Theorem source_seal_blocks_every_step : forall source body authority,
  interpret source = STSigned body authority ->
  forall label target, ~ source_step source label target.
Proof.
  intros source body authority Hshape label target Hstep.
  pose proof (source_step_has_native_reduction _ _ _ Hstep) as Hnative.
  rewrite Hshape in Hnative.
  exact (no_leak_requires_token _ _ _ Hnative).
Qed.

Theorem source_whole_cut_keeps_exact_grade_and_continuation_seal :
  forall source target label channel body payload outer inner remaining,
    interpret source =
      STPar
        (STSigned (CPPar (CPInput channel (STSigned body inner))
          (CPOutput channel payload)) outer)
        (STStack (TGate outer remaining)) ->
    source_step source label target ->
    interpret_label label = outer /\
    interpret target =
      STPar (STSigned (subst_caproc body 0 (CQuote payload)) inner)
        (STStack remaining).
Proof.
  intros source target label channel body payload outer inner remaining Hshape Hstep.
  pose proof (source_step_correspondence _ _ _ Hstep) as Hnative.
  rewrite Hshape in Hnative.
  exact (whole_redex_step_has_exact_grade_and_residual
    channel (STSigned body inner) payload outer remaining
    (interpret_label label) (interpret target) Hnative).
Qed.

End SourceSteps.

(* A supplied CIMor already carries its step and signature-map obligations.
   This corollary does not construct one from continued/Cost(G) strings.
   In particular, a many-to-one funding interpretation is not thereby a CIMor. *)
Theorem supplied_cimor_to_rho_preserves_no_leak :
  forall (G : CIObj) (morphism : CIMor G Rho_ciGSLT)
    source body authority,
    mor_map morphism source = STSigned body authority ->
    forall label target, ~ cstep G source label target.
Proof.
  intros G morphism source body authority Hshape.
  exact (@source_seal_blocks_every_step (carrier G) sig
    (mor_map morphism) (mor_sig_map morphism) (cstep G)
    (fun before label after Hstep => mor_pres morphism Hstep)
    source body authority Hshape).
Qed.

(* The identity interpretation satisfies the correspondence premise. The
   second example is an actual funded native step with distinct outer/inner
   signatures; neither example validates an arbitrary authored declaration. *)
Example native_identity_step_correspondence :
  forall before label after, graded_step before label after ->
    graded_step ((fun term => term) before) ((fun signature => signature) label)
      ((fun term => term) after).
Proof. intros before label after Hstep. exact Hstep. Qed.

Example native_identity_has_a_seal_preserving_step :
  graded_step
    (STPar
      (STSigned (CPPar (CPInput (CNVar 0) (STSigned CPNil (SGround [])))
        (CPOutput (CNVar 0) (STStack TUnit))) SUnit)
      (STStack (TGate SUnit TUnit)))
    SUnit
    (STPar (STSigned CPNil (SGround [])) (STStack TUnit)).
Proof. apply lollipop_outer_step_preserves_continuation_seal. Qed.

Section SourceLaws.

Context {Source Value : Type}.
Variable interpret_cost : Source -> cost Value.

(* The source terms below are the already chosen sides of a proposed law.
   These equalities are the operation-interpretation premises, not a checker
   for source eta/mu/map declarations. They do not imply source equality. *)
Theorem left_unit_after_interpretation : forall lhs original,
  interpret_cost lhs = cost_mu (cost_eta (interpret_cost original)) ->
  cost_equiv (interpret_cost lhs) (interpret_cost original).
Proof.
  intros lhs original Hinterpret. rewrite Hinterpret. apply cost_left_unit.
Qed.

Theorem right_unit_after_interpretation : forall lhs original,
  interpret_cost lhs = cost_mu (cost_map cost_eta (interpret_cost original)) ->
  cost_equiv (interpret_cost lhs) (interpret_cost original).
Proof.
  intros lhs original Hinterpret. rewrite Hinterpret. apply cost_right_unit.
Qed.

Theorem associativity_after_interpretation :
  forall lhs rhs (nested : cost (cost (cost Value))),
    interpret_cost lhs = cost_mu (cost_mu nested) ->
    interpret_cost rhs = cost_mu (cost_map cost_mu nested) ->
    cost_equiv (interpret_cost lhs) (interpret_cost rhs).
Proof.
  intros lhs rhs nested Hleft Hright. rewrite Hleft, Hright. apply cost_assoc.
Qed.

Variable source_equiv : Source -> Source -> Prop.
Variable declared_law : Source -> Source -> Prop.
Hypothesis interpretation_reflects_declared_law : forall left right,
  declared_law left right ->
  cost_equiv (interpret_cost left) (interpret_cost right) -> source_equiv left right.

Theorem source_left_unit_from_interpretation_and_reflection : forall lhs original,
  declared_law lhs original ->
  interpret_cost lhs = cost_mu (cost_eta (interpret_cost original)) ->
  source_equiv lhs original.
Proof.
  intros lhs original Hdeclared Hinterpret.
  apply (interpretation_reflects_declared_law _ _ Hdeclared).
  now apply left_unit_after_interpretation.
Qed.

Theorem source_right_unit_from_interpretation_and_reflection : forall lhs original,
  declared_law lhs original ->
  interpret_cost lhs = cost_mu (cost_map cost_eta (interpret_cost original)) ->
  source_equiv lhs original.
Proof.
  intros lhs original Hdeclared Hinterpret.
  apply (interpretation_reflects_declared_law _ _ Hdeclared).
  now apply right_unit_after_interpretation.
Qed.

Theorem source_associativity_from_interpretation_and_reflection :
  forall lhs rhs (nested : cost (cost (cost Value))),
    declared_law lhs rhs ->
    interpret_cost lhs = cost_mu (cost_mu nested) ->
    interpret_cost rhs = cost_mu (cost_map cost_mu nested) ->
    source_equiv lhs rhs.
Proof.
  intros lhs rhs nested Hdeclared Hleft Hright.
  apply (interpretation_reflects_declared_law _ _ Hdeclared).
  exact (associativity_after_interpretation lhs rhs nested Hleft Hright).
Qed.

End SourceLaws.

Example interpreted_law_does_not_imply_raw_source_equality :
  cost_equiv ((fun _ : bool => cost_eta tt) true)
    ((fun _ : bool => cost_eta tt) false) /\ true <> false.
Proof. split; [apply cost_equiv_refl | discriminate]. Qed.

Print Assumptions source_step_has_native_reduction.
Print Assumptions source_seal_blocks_every_step.
Print Assumptions source_whole_cut_keeps_exact_grade_and_continuation_seal.
Print Assumptions supplied_cimor_to_rho_preserves_no_leak.
Print Assumptions native_identity_step_correspondence.
Print Assumptions native_identity_has_a_seal_preserving_step.
Print Assumptions left_unit_after_interpretation.
Print Assumptions right_unit_after_interpretation.
Print Assumptions associativity_after_interpretation.
Print Assumptions source_left_unit_from_interpretation_and_reflection.
Print Assumptions source_right_unit_from_interpretation_and_reflection.
Print Assumptions source_associativity_from_interpretation_and_reflection.
Print Assumptions interpreted_law_does_not_imply_raw_source_equality.
