(**
  RegexGsltRules.v

  A single typed directed-rewrite interface for every observable regex
  judgment.  The constructors are the reified rule families carried by a
  semantic image; [interpret_regex_rule] is their executable denotation.
  Detailed correctness results for derivative, search, and replacement are
  proved in the preceding modules.
*)

From RuntimeGrammar Require Import
  RegexGsltSyntax RegexGsltMatch RegexGsltSearch RegexGsltReplace.

Inductive RegexRuleValue : Type :=
| RulePatternValue : RegexPattern -> RegexRuleValue
| RuleBoolValue : bool -> RegexRuleValue
| RuleMatchValue : option MatchSpan -> RegexRuleValue
| RuleTextValue : Text -> RegexRuleValue.

Definition rule_value_sort (value : RegexRuleValue) : RegexSort :=
  match value with
  | RulePatternValue _ => PatternSort
  | RuleBoolValue _ => BoolSort
  | RuleMatchValue _ => MatchResultSort
  | RuleTextValue _ => TextSort
  end.

Inductive RegexRuleInput : Type :=
| NullableInput : RegexPattern -> RegexRuleInput
| DerivativeInput : Scalar -> RegexPattern -> RegexRuleInput
| FullMatchInput : RegexPattern -> Text -> RegexRuleInput
| SearchInput : RegexPattern -> Text -> RegexRuleInput
| ReplaceFirstInput :
    RegexPattern -> ReplacementTemplateValue -> Text -> RegexRuleInput
| ReplaceAllInput :
    ReplacementExecutionLimits -> RegexPattern ->
    ReplacementTemplateValue -> Text -> RegexRuleInput.

Definition input_judgment (input : RegexRuleInput) : RegexJudgment :=
  match input with
  | NullableInput _ => NullableJudgment
  | DerivativeInput _ _ => DerivativeJudgment
  | FullMatchInput _ _ => FullMatchJudgment
  | SearchInput _ _ => SearchJudgment
  | ReplaceFirstInput _ _ _ => ReplaceFirstJudgment
  | ReplaceAllInput _ _ _ _ => ReplaceAllJudgment
  end.

Inductive RegexRuleOutcome : Type :=
| RuleSucceeded : RegexRuleValue -> RegexRuleOutcome
| RuleExhausted : RegexExhaustion -> RegexRuleOutcome.

Definition replace_all_outcome
    (decision : RegexDecision (Text * list MatchSpan)) : RegexRuleOutcome :=
  match decision with
  | RegexProven (output, _) => RuleSucceeded (RuleTextValue output)
  | RegexUndetermined reason => RuleExhausted reason
  end.

Definition interpret_regex_rule (input : RegexRuleInput) : RegexRuleOutcome :=
  match input with
  | NullableInput pattern => RuleSucceeded (RuleBoolValue (nullable pattern))
  | DerivativeInput scalar pattern =>
      RuleSucceeded (RulePatternValue (derivative scalar pattern))
  | FullMatchInput pattern text =>
      RuleSucceeded (RuleBoolValue (full_match pattern text))
  | SearchInput pattern text =>
      RuleSucceeded (RuleMatchValue (search pattern text))
  | ReplaceFirstInput pattern template text =>
      RuleSucceeded (RuleTextValue (replace_first pattern template text))
  | ReplaceAllInput limits pattern template text =>
      replace_all_outcome (bounded_replace_all limits pattern template text)
  end.

Inductive RegexRuleStep : RegexRuleInput -> RegexRuleOutcome -> Prop :=
| StepNullable : forall pattern,
    RegexRuleStep (NullableInput pattern)
      (RuleSucceeded (RuleBoolValue (nullable pattern)))
| StepDerivative : forall scalar pattern,
    RegexRuleStep (DerivativeInput scalar pattern)
      (RuleSucceeded (RulePatternValue (derivative scalar pattern)))
| StepFullMatch : forall pattern text,
    RegexRuleStep (FullMatchInput pattern text)
      (RuleSucceeded (RuleBoolValue (full_match pattern text)))
| StepSearch : forall pattern text,
    RegexRuleStep (SearchInput pattern text)
      (RuleSucceeded (RuleMatchValue (search pattern text)))
| StepReplaceFirst : forall pattern template text,
    RegexRuleStep (ReplaceFirstInput pattern template text)
      (RuleSucceeded (RuleTextValue (replace_first pattern template text)))
| StepReplaceAllProven : forall limits pattern template text output spans,
    bounded_replace_all limits pattern template text =
      RegexProven (output, spans) ->
    RegexRuleStep (ReplaceAllInput limits pattern template text)
      (RuleSucceeded (RuleTextValue output))
| StepReplaceAllExhausted : forall limits pattern template text reason,
    bounded_replace_all limits pattern template text =
      RegexUndetermined reason ->
    RegexRuleStep (ReplaceAllInput limits pattern template text)
      (RuleExhausted reason).

Theorem every_regex_rule_input_steps :
  forall input, exists outcome, RegexRuleStep input outcome.
Proof.
  intros input.
  destruct input as
    [pattern | scalar pattern | pattern text | pattern text |
     pattern template text | limits pattern template text].
  - eexists. constructor.
  - eexists. constructor.
  - eexists. constructor.
  - eexists. constructor.
  - eexists. constructor.
  - destruct (bounded_replace_all limits pattern template text)
      as [[output spans]|reason] eqn:Hdecision.
    + exists (RuleSucceeded (RuleTextValue output)).
      now apply StepReplaceAllProven with spans.
    + exists (RuleExhausted reason).
      now apply StepReplaceAllExhausted.
Qed.

Theorem regex_rule_step_computes_the_interpreter :
  forall input outcome,
    RegexRuleStep input outcome ->
    outcome = interpret_regex_rule input.
Proof.
  intros input outcome Hstep.
  inversion Hstep; subst; simpl; try reflexivity.
  - unfold replace_all_outcome. now rewrite H.
  - unfold replace_all_outcome. now rewrite H.
Qed.

Theorem regex_rule_step_is_deterministic :
  forall input lhs rhs,
    RegexRuleStep input lhs ->
    RegexRuleStep input rhs ->
    lhs = rhs.
Proof.
  intros input lhs rhs Hlhs Hrhs.
  rewrite (regex_rule_step_computes_the_interpreter _ _ Hlhs).
  rewrite (regex_rule_step_computes_the_interpreter _ _ Hrhs).
  reflexivity.
Qed.

Theorem successful_regex_rule_steps_preserve_the_judgment_sort :
  forall input value,
    RegexRuleStep input (RuleSucceeded value) ->
    rule_value_sort value = judgment_codomain (input_judgment input).
Proof.
  intros input value Hstep.
  inversion Hstep; reflexivity.
Qed.

Definition regex_rule_outcome_commits (outcome : RegexRuleOutcome) : bool :=
  match outcome with
  | RuleSucceeded _ => true
  | RuleExhausted _ => false
  end.

Theorem exhausted_regex_rule_steps_fail_closed :
  forall reason,
    regex_rule_outcome_commits (RuleExhausted reason) = false.
Proof. reflexivity. Qed.

Print Assumptions every_regex_rule_input_steps.
Print Assumptions regex_rule_step_computes_the_interpreter.
Print Assumptions regex_rule_step_is_deterministic.
Print Assumptions successful_regex_rule_steps_preserve_the_judgment_sort.
Print Assumptions exhausted_regex_rule_steps_fail_closed.
