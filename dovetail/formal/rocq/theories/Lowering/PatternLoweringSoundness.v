(*
 * PatternLoweringSoundness: abstract coverage proof for lowering MeTTaIL
 * patterns and premises into Dovetail rule/e-graph obligations.
 *
 * The executable inventory test checks current AST variants. This file proves
 * that the abstract lowering taxonomy maps every recursive pattern/premise
 * requirement to the already-covered Dovetail requirement taxonomy.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.

From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.

Import ListNotations.

Section PatternLoweringSoundness.

  Inductive PatternShape : Type :=
    | PatVar
    | PatApply : list PatternShape -> PatternShape
    | PatCollection : list PatternShape -> PatternShape
    | PatMap : PatternShape -> PatternShape -> PatternShape
    | PatZip : PatternShape -> PatternShape -> PatternShape
    | PatBinder : PatternShape -> PatternShape
    | PatSubst : PatternShape -> PatternShape -> PatternShape.

  Fixpoint pattern_requirements (p : PatternShape) : list RewriteRequirement :=
    match p with
    | PatVar => [ReqExactContentKey]
    | PatApply children =>
        ReqExactContentKey :: flat_map pattern_requirements children
    | PatCollection elems =>
        ReqCollectionPattern :: flat_map pattern_requirements elems
    | PatMap source body =>
        ReqMapPattern :: pattern_requirements source ++ pattern_requirements body
    | PatZip lhs rhs =>
        ReqZipPattern :: pattern_requirements lhs ++ pattern_requirements rhs
    | PatBinder body =>
        ReqBinderPattern :: pattern_requirements body
    | PatSubst subject replacement =>
        ReqSubstitutionPattern :: pattern_requirements subject ++ pattern_requirements replacement
    end.

  Inductive PremiseShape : Type :=
    | PremFreshness
    | PremCongruence
    | PremRelation
    | PremForAll : PremiseShape -> PremiseShape
    | PremBehavioralGuard
    | PremSyntheticInjectionGuard.

  Fixpoint premise_requirements (p : PremiseShape) : list RewriteRequirement :=
    match p with
    | PremFreshness => [ReqFreshnessPremise]
    | PremCongruence => [ReqCongruencePremise]
    | PremRelation => [ReqEnvRelationPremise]
    | PremForAll body => ReqForAllPremise :: premise_requirements body
    | PremBehavioralGuard => [ReqBehavioralGuard]
    | PremSyntheticInjectionGuard => [ReqSyntheticInjectionGuard]
    end.

  Theorem pattern_lowering_requirements_covered : forall p r,
    In r (pattern_requirements p) ->
    requirement_covered r.
  Proof.
    intros p r _. apply every_requirement_constructor_is_covered.
  Qed.

  Theorem premise_lowering_requirements_covered : forall p r,
    In r (premise_requirements p) ->
    requirement_covered r.
  Proof.
    intros p r _. apply every_requirement_constructor_is_covered.
  Qed.

  Theorem rewrite_rule_lowering_covered : forall lhs rhs premises r,
    In r
      (ReqDirectionalRewrite
       :: pattern_requirements lhs
       ++ pattern_requirements rhs
       ++ flat_map premise_requirements premises) ->
    requirement_covered r.
  Proof.
    intros lhs rhs premises r _. apply every_requirement_constructor_is_covered.
  Qed.

  Theorem equation_lowering_covered : forall lhs rhs premises r,
    In r
      (ReqEquation
       :: pattern_requirements lhs
       ++ pattern_requirements rhs
       ++ flat_map premise_requirements premises) ->
    requirement_covered r.
  Proof.
    intros lhs rhs premises r _. apply every_requirement_constructor_is_covered.
  Qed.

End PatternLoweringSoundness.
