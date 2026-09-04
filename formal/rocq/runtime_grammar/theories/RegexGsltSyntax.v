(**
  RegexGsltSyntax.v

  A typed, reified signature for the capture-free regular-expression theory
  used by the in-Rholang language-extension demonstration.  This file models
  the data that a checked TheoryCore image must carry; it does not introduce a
  privileged regex evaluator.

  The presentation follows the MeTTaIL division between Types, Terms,
  Equations, and directed Rewrites.  Variables are intrinsically sorted, while
  constructor applications are checked against the finite signature.  The
  explicit-substitution theorem is the proof obligation later consumed by the
  generalized rule-image compiler.
*)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

Inductive RegexSort : Type :=
| PatternSort
| TextSort
| ScalarSort
| BoolSort
| NatSort
| MatchStateSort
| SearchStateSort
| MatchResultSort
| ReplacementTemplateSort
| OutputSort.

Scheme Equality for RegexSort.

(** The finite constructor signature.  Parentheses/grouping are concrete
    syntax and therefore elaborate to their child rather than becoming a
    semantic constructor. *)
Inductive RegexConstructor : Type :=
| PFail | PEpsilon | PLiteral | PAny
| PAlt | PConcat | PStar | PPlus | POptional | PRepeat
| TEmpty | TCons
| BFalse | BTrue
| NZero | NSucc
| MatchScan | SearchScan
| NoMatch | MatchFound
| ReplacementEmpty | ReplacementLiteral | ReplacementWhole | ReplacementAppend
| OutputPattern | OutputBool | OutputMatch | OutputText | OutputUndetermined.

Scheme Equality for RegexConstructor.

Definition constructor_domain (constructor : RegexConstructor) : list RegexSort :=
  match constructor with
  | PFail | PEpsilon | PAny | TEmpty | BFalse | BTrue | NZero
  | NoMatch | ReplacementEmpty | ReplacementWhole | OutputUndetermined => []
  | PLiteral => [ScalarSort]
  | PAlt | PConcat => [PatternSort; PatternSort]
  | PStar | PPlus | POptional => [PatternSort]
  | PRepeat => [PatternSort; NatSort; NatSort]
  | TCons => [ScalarSort; TextSort]
  | NSucc => [NatSort]
  | MatchScan => [PatternSort; TextSort]
  | SearchScan => [PatternSort; TextSort; NatSort]
  | MatchFound => [NatSort; NatSort; TextSort]
  | ReplacementLiteral => [TextSort]
  | ReplacementAppend => [ReplacementTemplateSort; ReplacementTemplateSort]
  | OutputPattern => [PatternSort]
  | OutputBool => [BoolSort]
  | OutputMatch => [MatchResultSort]
  | OutputText => [TextSort]
  end.

Definition constructor_codomain (constructor : RegexConstructor) : RegexSort :=
  match constructor with
  | PFail | PEpsilon | PLiteral | PAny | PAlt | PConcat | PStar | PPlus
  | POptional | PRepeat => PatternSort
  | TEmpty | TCons => TextSort
  | BFalse | BTrue => BoolSort
  | NZero | NSucc => NatSort
  | MatchScan => MatchStateSort
  | SearchScan => SearchStateSort
  | NoMatch | MatchFound => MatchResultSort
  | ReplacementEmpty | ReplacementLiteral | ReplacementWhole | ReplacementAppend =>
      ReplacementTemplateSort
  | OutputPattern | OutputBool | OutputMatch | OutputText | OutputUndetermined => OutputSort
  end.

(** A flat rule-image node can represent this tree by topologically numbering
    children before their parent.  The tree is retained here because it makes
    the typing theorem independent of a particular arena encoding. *)
Inductive RegexTerm : Type :=
| RegexVariable : nat -> RegexSort -> RegexTerm
| RegexApplication : RegexConstructor -> list RegexTerm -> RegexTerm.

Inductive HasRegexSort : RegexTerm -> RegexSort -> Prop :=
| SortVariable : forall variable sort,
    HasRegexSort (RegexVariable variable sort) sort
| SortApplication : forall constructor arguments,
    HasRegexSortList arguments (constructor_domain constructor) ->
    HasRegexSort
      (RegexApplication constructor arguments)
      (constructor_codomain constructor)
with HasRegexSortList : list RegexTerm -> list RegexSort -> Prop :=
| SortListNil : HasRegexSortList [] []
| SortListCons : forall term sort terms sorts,
    HasRegexSort term sort ->
    HasRegexSortList terms sorts ->
    HasRegexSortList (term :: terms) (sort :: sorts).

Scheme HasRegexSort_ind' := Induction for HasRegexSort Sort Prop
with HasRegexSortList_ind' := Induction for HasRegexSortList Sort Prop.
Combined Scheme HasRegexSort_mutind
  from HasRegexSort_ind', HasRegexSortList_ind'.

Definition RegexSubstitution : Type := nat -> RegexSort -> RegexTerm.

Definition WellSortedSubstitution (substitution : RegexSubstitution) : Prop :=
  forall variable sort,
    HasRegexSort (substitution variable sort) sort.

Fixpoint substitute_regex
    (substitution : RegexSubstitution) (term : RegexTerm) : RegexTerm :=
  match term with
  | RegexVariable variable sort => substitution variable sort
  | RegexApplication constructor arguments =>
      RegexApplication constructor (map (substitute_regex substitution) arguments)
  end.

Lemma regex_substitution_preserves_sort_mutually :
  forall substitution,
    WellSortedSubstitution substitution ->
    (forall term sort,
       HasRegexSort term sort ->
       HasRegexSort (substitute_regex substitution term) sort) /\
    (forall terms sorts,
       HasRegexSortList terms sorts ->
       HasRegexSortList (map (substitute_regex substitution) terms) sorts).
Proof.
  intros substitution Hsub.
  apply HasRegexSort_mutind; simpl.
  - intros variable sort. apply Hsub.
  - intros constructor arguments Harguments IHarguments.
    constructor. exact IHarguments.
  - constructor.
  - intros term sort terms sorts Hterm IHterm Hterms IHterms.
    constructor; assumption.
Qed.

Theorem regex_substitution_preserves_sort :
  forall substitution term sort,
    WellSortedSubstitution substitution ->
    HasRegexSort term sort ->
    HasRegexSort (substitute_regex substitution term) sort.
Proof.
  intros substitution term sort Hsub.
  exact (proj1 (regex_substitution_preserves_sort_mutually substitution Hsub) term sort).
Qed.

(** The algebraic equations are reified separately from executable rewrites.
    They are normalization laws and never consume text. *)
Inductive RegexEquationSchema : Type :=
| AltFailLeft | AltFailRight | AltIdempotent
| ConcatFailLeft | ConcatFailRight
| ConcatEpsilonLeft | ConcatEpsilonRight
| StarFail | StarEpsilon
| ExpandPlus | ExpandOptional.

Definition pattern_variable (index : nat) : RegexTerm :=
  RegexVariable index PatternSort.

Definition pattern_application
    (constructor : RegexConstructor) (arguments : list RegexTerm) : RegexTerm :=
  RegexApplication constructor arguments.

Definition equation_schema_terms
    (schema : RegexEquationSchema) : RegexTerm * RegexTerm :=
  let p := pattern_variable 0 in
  let fail := pattern_application PFail [] in
  let epsilon := pattern_application PEpsilon [] in
  match schema with
  | AltFailLeft =>
      (pattern_application PAlt [fail; p], p)
  | AltFailRight =>
      (pattern_application PAlt [p; fail], p)
  | AltIdempotent =>
      (pattern_application PAlt [p; p], p)
  | ConcatFailLeft =>
      (pattern_application PConcat [fail; p], fail)
  | ConcatFailRight =>
      (pattern_application PConcat [p; fail], fail)
  | ConcatEpsilonLeft =>
      (pattern_application PConcat [epsilon; p], p)
  | ConcatEpsilonRight =>
      (pattern_application PConcat [p; epsilon], p)
  | StarFail =>
      (pattern_application PStar [fail], epsilon)
  | StarEpsilon =>
      (pattern_application PStar [epsilon], epsilon)
  | ExpandPlus =>
      (pattern_application PPlus [p],
       pattern_application PConcat [p; pattern_application PStar [p]])
  | ExpandOptional =>
      (pattern_application POptional [p],
       pattern_application PAlt [epsilon; p])
  end.

Lemma pattern_variable_has_pattern_sort :
  forall index, HasRegexSort (pattern_variable index) PatternSort.
Proof. intros. constructor. Qed.

Theorem every_regex_equation_is_sort_preserving :
  forall schema,
    HasRegexSort (fst (equation_schema_terms schema)) PatternSort /\
    HasRegexSort (snd (equation_schema_terms schema)) PatternSort.
Proof.
  intros schema; destruct schema; simpl;
    repeat constructor; apply pattern_variable_has_pattern_sort.
Qed.

Inductive RegexJudgment : Type :=
| NullableJudgment
| DerivativeJudgment
| FullMatchJudgment
| SearchJudgment
| ReplaceFirstJudgment
| ReplaceAllJudgment.

Definition judgment_domain (judgment : RegexJudgment) : list RegexSort :=
  match judgment with
  | NullableJudgment => [PatternSort]
  | DerivativeJudgment => [ScalarSort; PatternSort]
  | FullMatchJudgment => [PatternSort; TextSort]
  | SearchJudgment => [PatternSort; TextSort]
  | ReplaceFirstJudgment | ReplaceAllJudgment =>
      [PatternSort; ReplacementTemplateSort; TextSort]
  end.

Definition judgment_codomain (judgment : RegexJudgment) : RegexSort :=
  match judgment with
  | NullableJudgment | FullMatchJudgment => BoolSort
  | DerivativeJudgment => PatternSort
  | SearchJudgment => MatchResultSort
  | ReplaceFirstJudgment | ReplaceAllJudgment => TextSort
  end.

Theorem regex_judgment_signatures_are_total :
  forall judgment,
    exists domain codomain,
      judgment_domain judgment = domain /\
      judgment_codomain judgment = codomain.
Proof.
  intro judgment.
  exists (judgment_domain judgment), (judgment_codomain judgment).
  auto.
Qed.

Print Assumptions regex_substitution_preserves_sort.
Print Assumptions every_regex_equation_is_sort_preserving.
Print Assumptions regex_judgment_signatures_are_total.
