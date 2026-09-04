(**
  RegexGsltMatch.v

  Executable, capture-free regular-expression semantics expressed as typed
  equations and directed derivative rewrites.  The core calculus contains no
  PCRE-specific host callback: surface sugar is elaborated into Fail, Epsilon,
  Literal, Any, Alt, Concat, and Star, then matching repeatedly applies the
  Brzozowski derivative rules.

  A Unicode scalar is represented abstractly by [nat] in this layer.  The
  primitive text interface is responsible for supplying valid scalar values
  and byte widths; RegexGsltSearch proves the corresponding span obligations.
*)

From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltSyntax.
Import ListNotations.

Definition Scalar : Type := nat.
Definition Text : Type := list Scalar.

Inductive RegexPattern : Type :=
| FailPattern
| EpsilonPattern
| LiteralPattern : Scalar -> RegexPattern
| AnyPattern
| AltPattern : RegexPattern -> RegexPattern -> RegexPattern
| ConcatPattern : RegexPattern -> RegexPattern -> RegexPattern
| StarPattern : RegexPattern -> RegexPattern.

Scheme Equality for RegexPattern.

(** Canonical equation constructors.  These are deterministic orientations of
    the algebraic equations declared in RegexGsltSyntax. *)
Definition smart_alt (lhs rhs : RegexPattern) : RegexPattern :=
  match lhs, rhs with
  | FailPattern, other => other
  | other, FailPattern => other
  | _, _ =>
      if RegexPattern_eq_dec lhs rhs
      then lhs
      else AltPattern lhs rhs
  end.

Definition smart_concat (lhs rhs : RegexPattern) : RegexPattern :=
  match lhs, rhs with
  | FailPattern, _ | _, FailPattern => FailPattern
  | EpsilonPattern, other => other
  | other, EpsilonPattern => other
  | _, _ => ConcatPattern lhs rhs
  end.

Definition smart_star (pattern : RegexPattern) : RegexPattern :=
  match pattern with
  | FailPattern | EpsilonPattern => EpsilonPattern
  | StarPattern body => StarPattern body
  | other => StarPattern other
  end.

Theorem equation_alt_fail_left :
  forall pattern, smart_alt FailPattern pattern = pattern.
Proof. reflexivity. Qed.

Theorem equation_alt_fail_right :
  forall pattern, smart_alt pattern FailPattern = pattern.
Proof. destruct pattern; reflexivity. Qed.

Theorem equation_alt_idempotent :
  forall pattern, smart_alt pattern pattern = pattern.
Proof.
  destruct pattern; simpl; try reflexivity;
    destruct (RegexPattern_eq_dec _ _); congruence.
Qed.

Theorem equation_concat_fail_left :
  forall pattern, smart_concat FailPattern pattern = FailPattern.
Proof. reflexivity. Qed.

Theorem equation_concat_fail_right :
  forall pattern, smart_concat pattern FailPattern = FailPattern.
Proof. destruct pattern; reflexivity. Qed.

Theorem equation_concat_epsilon_left :
  forall pattern, smart_concat EpsilonPattern pattern = pattern.
Proof. destruct pattern; reflexivity. Qed.

Theorem equation_concat_epsilon_right :
  forall pattern, smart_concat pattern EpsilonPattern = pattern.
Proof. destruct pattern; reflexivity. Qed.

Theorem equation_star_fail : smart_star FailPattern = EpsilonPattern.
Proof. reflexivity. Qed.

Theorem equation_star_epsilon : smart_star EpsilonPattern = EpsilonPattern.
Proof. reflexivity. Qed.

Fixpoint nullable (pattern : RegexPattern) : bool :=
  match pattern with
  | FailPattern | LiteralPattern _ | AnyPattern => false
  | EpsilonPattern | StarPattern _ => true
  | AltPattern lhs rhs => nullable lhs || nullable rhs
  | ConcatPattern lhs rhs => nullable lhs && nullable rhs
  end.

Fixpoint derivative (scalar : Scalar) (pattern : RegexPattern) : RegexPattern :=
  match pattern with
  | FailPattern | EpsilonPattern => FailPattern
  | LiteralPattern expected =>
      if Nat.eqb scalar expected then EpsilonPattern else FailPattern
  | AnyPattern => EpsilonPattern
  | AltPattern lhs rhs =>
      smart_alt (derivative scalar lhs) (derivative scalar rhs)
  | ConcatPattern lhs rhs =>
      let lhs_derivative := smart_concat (derivative scalar lhs) rhs in
      if nullable lhs
      then smart_alt lhs_derivative (derivative scalar rhs)
      else lhs_derivative
  | StarPattern body =>
      smart_concat (derivative scalar body) (smart_star body)
  end.

Fixpoint derivatives (pattern : RegexPattern) (text : Text) : RegexPattern :=
  match text with
  | [] => pattern
  | scalar :: rest => derivatives (derivative scalar pattern) rest
  end.

Definition full_match (pattern : RegexPattern) (text : Text) : bool :=
  nullable (derivatives pattern text).

(** The one-step derivative theorem is definitional: the interpreter for the
    theory is a fold of the declared derivative rewrites, not a second regex
    implementation. *)
Theorem derivative_step_sound :
  forall scalar pattern rest,
    full_match pattern (scalar :: rest) =
    full_match (derivative scalar pattern) rest.
Proof. reflexivity. Qed.

Inductive DerivativeRewrite : Scalar -> RegexPattern -> RegexPattern -> Prop :=
| RewriteDerivativeFail : forall scalar,
    DerivativeRewrite scalar FailPattern FailPattern
| RewriteDerivativeEpsilon : forall scalar,
    DerivativeRewrite scalar EpsilonPattern FailPattern
| RewriteDerivativeLiteral : forall scalar expected,
    DerivativeRewrite scalar (LiteralPattern expected)
      (if Nat.eqb scalar expected then EpsilonPattern else FailPattern)
| RewriteDerivativeAny : forall scalar,
    DerivativeRewrite scalar AnyPattern EpsilonPattern
| RewriteDerivativeAlt : forall scalar lhs rhs,
    DerivativeRewrite scalar (AltPattern lhs rhs)
      (smart_alt (derivative scalar lhs) (derivative scalar rhs))
| RewriteDerivativeConcat : forall scalar lhs rhs,
    DerivativeRewrite scalar (ConcatPattern lhs rhs)
      (let lhs_derivative := smart_concat (derivative scalar lhs) rhs in
       if nullable lhs
       then smart_alt lhs_derivative (derivative scalar rhs)
       else lhs_derivative)
| RewriteDerivativeStar : forall scalar body,
    DerivativeRewrite scalar (StarPattern body)
      (smart_concat (derivative scalar body) (smart_star body)).

Theorem derivative_rewrite_computes :
  forall scalar source target,
    DerivativeRewrite scalar source target ->
    target = derivative scalar source.
Proof. intros scalar source target H; inversion H; reflexivity. Qed.

Theorem derivative_rewrite_is_semantically_sound :
  forall scalar source target rest,
    DerivativeRewrite scalar source target ->
    full_match source (scalar :: rest) = full_match target rest.
Proof.
  intros scalar source target rest Hstep.
  rewrite (derivative_rewrite_computes _ _ _ Hstep).
  apply derivative_step_sound.
Qed.

Theorem derivative_rewrite_is_deterministic :
  forall scalar source lhs rhs,
    DerivativeRewrite scalar source lhs ->
    DerivativeRewrite scalar source rhs ->
    lhs = rhs.
Proof.
  intros scalar source lhs rhs Hleft Hright.
  rewrite (derivative_rewrite_computes _ _ _ Hleft).
  rewrite (derivative_rewrite_computes _ _ _ Hright).
  reflexivity.
Qed.

(** Surface-only constructors.  Greediness has no capture-sensitive meaning in
    this initial subset; deterministic leftmost-longest search supplies its
    observable interpretation. *)
Inductive SurfacePattern : Type :=
| SurfaceFail | SurfaceEpsilon
| SurfaceLiteral : Scalar -> SurfacePattern
| SurfaceAny
| SurfaceGroup : SurfacePattern -> SurfacePattern
| SurfaceAlt : SurfacePattern -> SurfacePattern -> SurfacePattern
| SurfaceConcat : SurfacePattern -> SurfacePattern -> SurfacePattern
| SurfaceStar : SurfacePattern -> SurfacePattern
| SurfacePlus : SurfacePattern -> SurfacePattern
| SurfaceOptional : SurfacePattern -> SurfacePattern
| SurfaceRepeat : SurfacePattern -> nat -> nat -> SurfacePattern.

Fixpoint repeat_exactly (pattern : RegexPattern) (count : nat) : RegexPattern :=
  match count with
  | 0 => EpsilonPattern
  | S rest => smart_concat pattern (repeat_exactly pattern rest)
  end.

Fixpoint repeat_at_most (pattern : RegexPattern) (count : nat) : RegexPattern :=
  match count with
  | 0 => EpsilonPattern
  | S rest =>
      smart_alt EpsilonPattern
        (smart_concat pattern (repeat_at_most pattern rest))
  end.

Definition bounded_repeat
    (pattern : RegexPattern) (lower upper : nat) : RegexPattern :=
  if lower <=? upper
  then smart_concat
         (repeat_exactly pattern lower)
         (repeat_at_most pattern (upper - lower))
  else FailPattern.

Fixpoint elaborate_surface (surface : SurfacePattern) : RegexPattern :=
  match surface with
  | SurfaceFail => FailPattern
  | SurfaceEpsilon => EpsilonPattern
  | SurfaceLiteral scalar => LiteralPattern scalar
  | SurfaceAny => AnyPattern
  | SurfaceGroup body => elaborate_surface body
  | SurfaceAlt lhs rhs =>
      smart_alt (elaborate_surface lhs) (elaborate_surface rhs)
  | SurfaceConcat lhs rhs =>
      smart_concat (elaborate_surface lhs) (elaborate_surface rhs)
  | SurfaceStar body => smart_star (elaborate_surface body)
  | SurfacePlus body =>
      let core := elaborate_surface body in
      smart_concat core (smart_star core)
  | SurfaceOptional body =>
      smart_alt EpsilonPattern (elaborate_surface body)
  | SurfaceRepeat body lower upper =>
      bounded_repeat (elaborate_surface body) lower upper
  end.

Theorem group_is_semantically_transparent :
  forall body,
    elaborate_surface (SurfaceGroup body) = elaborate_surface body.
Proof. reflexivity. Qed.

Theorem plus_is_equation_expansion :
  forall body,
    elaborate_surface (SurfacePlus body) =
    smart_concat (elaborate_surface body) (smart_star (elaborate_surface body)).
Proof. reflexivity. Qed.

Theorem optional_is_equation_expansion :
  forall body,
    elaborate_surface (SurfaceOptional body) =
    smart_alt EpsilonPattern (elaborate_surface body).
Proof. reflexivity. Qed.

Theorem invalid_repeat_bounds_are_rejected :
  forall pattern lower upper,
    upper < lower ->
    bounded_repeat pattern lower upper = FailPattern.
Proof.
  intros pattern lower upper Hlt.
  unfold bounded_repeat.
  apply Nat.leb_gt in Hlt. now rewrite Hlt.
Qed.

Fixpoint pattern_nodes (pattern : RegexPattern) : nat :=
  match pattern with
  | FailPattern | EpsilonPattern | LiteralPattern _ | AnyPattern => 1
  | AltPattern lhs rhs | ConcatPattern lhs rhs =>
      1 + pattern_nodes lhs + pattern_nodes rhs
  | StarPattern body => 1 + pattern_nodes body
  end.

Fixpoint derivative_work (pattern : RegexPattern) : nat :=
  match pattern with
  | FailPattern | EpsilonPattern | LiteralPattern _ | AnyPattern => 1
  | AltPattern lhs rhs | ConcatPattern lhs rhs =>
      1 + derivative_work lhs + derivative_work rhs
  | StarPattern body => 1 + derivative_work body
  end.

Fixpoint execution_metrics
    (pattern : RegexPattern) (text : Text) : RegexPattern * nat * nat :=
  match text with
  | [] => (pattern, 1, pattern_nodes pattern)
  | scalar :: rest =>
      let next := derivative scalar pattern in
      let '(final_pattern, rest_work, rest_peak) := execution_metrics next rest in
      (final_pattern,
       derivative_work pattern + rest_work,
       Nat.max (pattern_nodes pattern) rest_peak)
  end.

Record RegexExecutionLimits : Type := {
  maximum_work : nat;
  maximum_pattern_nodes : nat
}.

Inductive RegexExhaustion : Type :=
| WorkExhausted
| PatternNodesExhausted
| OutputExhausted.

Inductive RegexDecision (A : Type) : Type :=
| RegexProven : A -> RegexDecision A
| RegexUndetermined : RegexExhaustion -> RegexDecision A.

Arguments RegexProven {A} _.
Arguments RegexUndetermined {A} _.

Definition bounded_full_match
    (limits : RegexExecutionLimits) (pattern : RegexPattern) (text : Text)
    : RegexDecision bool :=
  let '(final_pattern, work, peak) := execution_metrics pattern text in
  if maximum_work limits <? work
  then RegexUndetermined WorkExhausted
  else if maximum_pattern_nodes limits <? peak
       then RegexUndetermined PatternNodesExhausted
       else RegexProven (nullable final_pattern).

Lemma execution_metrics_pattern :
  forall pattern text final_pattern work peak,
    execution_metrics pattern text = (final_pattern, work, peak) ->
    final_pattern = derivatives pattern text.
Proof.
  intros pattern text.
  revert pattern.
  induction text as [| scalar rest IH]; intros pattern final_pattern work peak Hrun.
  - simpl in Hrun. inversion Hrun. reflexivity.
  - simpl in Hrun.
    remember (execution_metrics (derivative scalar pattern) rest)
      as metrics eqn:Hmetrics.
    destruct metrics as [[rest_pattern rest_work] rest_peak].
    inversion Hrun; subst.
    simpl.
    apply (IH (derivative scalar pattern) final_pattern rest_work rest_peak).
    symmetry. exact Hmetrics.
Qed.

Theorem bounded_full_match_never_fabricates_a_result :
  forall limits pattern text result,
    bounded_full_match limits pattern text = RegexProven result ->
    result = full_match pattern text.
Proof.
  intros limits pattern text result Hbounded.
  unfold bounded_full_match in Hbounded.
  remember (execution_metrics pattern text) as metrics eqn:Hmetrics.
  destruct metrics as [[final_pattern work] peak].
  destruct (maximum_work limits <? work); try discriminate.
  destruct (maximum_pattern_nodes limits <? peak); try discriminate.
  inversion Hbounded; subst result.
  unfold full_match.
  f_equal.
  apply (execution_metrics_pattern pattern text final_pattern work peak).
  symmetry. exact Hmetrics.
Qed.

Definition decision_passes (decision : RegexDecision bool) : bool :=
  match decision with
  | RegexProven result => result
  | RegexUndetermined _ => false
  end.

Theorem resource_exhaustion_fails_closed :
  forall reason, decision_passes (RegexUndetermined reason) = false.
Proof. reflexivity. Qed.

Theorem bounded_full_match_is_deterministic :
  forall limits pattern text lhs rhs,
    bounded_full_match limits pattern text = lhs ->
    bounded_full_match limits pattern text = rhs ->
    lhs = rhs.
Proof. congruence. Qed.

Print Assumptions every_regex_equation_is_sort_preserving.
Print Assumptions regex_substitution_preserves_sort.
Print Assumptions derivative_rewrite_is_semantically_sound.
Print Assumptions derivative_rewrite_is_deterministic.
Print Assumptions invalid_repeat_bounds_are_rejected.
Print Assumptions bounded_full_match_never_fabricates_a_result.
Print Assumptions resource_exhaustion_fails_closed.
