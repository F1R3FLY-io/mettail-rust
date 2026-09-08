(** Declared smart-constructor control states, refining the existing equations.

    Fail/Epsilon/Star tests are disjoint constructor patterns. Only structural
    idempotence needs the already provided exact-term-equality intrinsic; its
    Boolean result is consumed by a separate decision state. No negative
    premise, ordered catch-all rule, equation saturation or regex callback is
    needed. SmartDone is a local return, NOT the public Computation terminal.
    Transition bounds below exclude intrinsic-local equality work and do not
    stand for parser weight, semantic Cost(G), funding or physical memory. *)

From Stdlib Require Import PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch.

Inductive SmartState :=
| AltStart (lhs rhs : RegexPattern)
| AltCheckRight (lhs rhs : RegexPattern)
| AltCheckEqual (lhs rhs : RegexPattern)
| AltDecideEqual (equal : bool) (lhs rhs : RegexPattern)
| ConcatStart (lhs rhs : RegexPattern)
| ConcatCheckRight (lhs rhs : RegexPattern)
| StarStart (body : RegexPattern)
| SmartDone (result : RegexPattern).

Definition exact_pattern_equal (lhs rhs : RegexPattern) : bool :=
  if RegexPattern_eq_dec lhs rhs then true else false.

Definition smart_machine_step (state : SmartState) : option SmartState :=
  match state with
  | AltStart lhs rhs => Some
      (match lhs with FailPattern => SmartDone rhs | _ => AltCheckRight lhs rhs end)
  | AltCheckRight lhs rhs => Some
      (match rhs with FailPattern => SmartDone lhs | _ => AltCheckEqual lhs rhs end)
  | AltCheckEqual lhs rhs => Some (AltDecideEqual (exact_pattern_equal lhs rhs) lhs rhs)
  | AltDecideEqual equal lhs rhs =>
      Some (SmartDone (if equal then lhs else AltPattern lhs rhs))
  | ConcatStart lhs rhs => Some
      (match lhs with
      | FailPattern => SmartDone FailPattern
      | EpsilonPattern => SmartDone rhs
      | _ => ConcatCheckRight lhs rhs
      end)
  | ConcatCheckRight lhs rhs => Some
      (match rhs with
      | FailPattern => SmartDone FailPattern
      | EpsilonPattern => SmartDone lhs
      | _ => SmartDone (ConcatPattern lhs rhs)
      end)
  | StarStart body => Some
      (match body with
      | FailPattern | EpsilonPattern => SmartDone EpsilonPattern
      | StarPattern inner => SmartDone (StarPattern inner)
      | _ => SmartDone (StarPattern body)
      end)
  | SmartDone _ => None
  end.

Definition smart_equal_meaning (lhs rhs : RegexPattern) :=
  if exact_pattern_equal lhs rhs then lhs else AltPattern lhs rhs.

Definition smart_state_meaning (state : SmartState) : RegexPattern :=
  match state with
  | AltStart lhs rhs => smart_alt lhs rhs
  | AltCheckRight lhs rhs =>
      match rhs with FailPattern => lhs | _ => smart_equal_meaning lhs rhs end
  | AltCheckEqual lhs rhs => smart_equal_meaning lhs rhs
  | AltDecideEqual equal lhs rhs => if equal then lhs else AltPattern lhs rhs
  | ConcatStart lhs rhs => smart_concat lhs rhs
  | ConcatCheckRight lhs rhs =>
      match rhs with
      | FailPattern => FailPattern
      | EpsilonPattern => lhs
      | _ => ConcatPattern lhs rhs
      end
  | StarStart body => smart_star body
  | SmartDone result => result
  end.

Lemma smart_equal_meaning_is_reference_test : forall lhs rhs,
  smart_equal_meaning lhs rhs =
    if RegexPattern_eq_dec lhs rhs then lhs else AltPattern lhs rhs.
Proof.
  intros. unfold smart_equal_meaning, exact_pattern_equal.
  destruct (RegexPattern_eq_dec lhs rhs); reflexivity.
Qed.

Theorem smart_machine_step_preserves_meaning : forall source target,
  smart_machine_step source = Some target ->
  smart_state_meaning source = smart_state_meaning target.
Proof.
  intros source target H. destruct source.
  - destruct lhs; cbn [smart_machine_step] in H; inversion H; subst;
      cbn [smart_state_meaning smart_alt]; try reflexivity;
      destruct rhs; cbn [smart_state_meaning smart_alt]; try reflexivity;
      symmetry; apply smart_equal_meaning_is_reference_test.
  - destruct rhs; inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - destruct lhs, rhs; inversion H; reflexivity.
  - destruct rhs; inversion H; reflexivity.
  - destruct body; inversion H; reflexivity.
  - discriminate.
Qed.

Definition smart_remaining_bound (state : SmartState) : nat :=
  match state with
  | AltStart _ _ => 4
  | AltCheckRight _ _ => 3
  | AltCheckEqual _ _ => 2
  | AltDecideEqual _ _ _ => 1
  | ConcatStart _ _ => 2
  | ConcatCheckRight _ _ | StarStart _ => 1
  | SmartDone _ => 0
  end.

Theorem smart_step_decreases_remaining_bound : forall source target,
  smart_machine_step source = Some target ->
  smart_remaining_bound target < smart_remaining_bound source.
Proof.
  intros source target H. destruct source.
  - destruct lhs; inversion H; subst; cbn [smart_remaining_bound]; lia.
  - destruct rhs; inversion H; subst; cbn [smart_remaining_bound]; lia.
  - inversion H; subst; cbn [smart_remaining_bound]; lia.
  - inversion H; subst; cbn [smart_remaining_bound]; lia.
  - destruct lhs; inversion H; subst; cbn [smart_remaining_bound]; lia.
  - destruct rhs; inversion H; subst; cbn [smart_remaining_bound]; lia.
  - destruct body; inversion H; subst; cbn [smart_remaining_bound]; lia.
  - discriminate.
Qed.

Fixpoint run_smart_machine (fuel : nat) (state : SmartState) : option RegexPattern :=
  match state with
  | SmartDone result => Some result
  | _ => match fuel with
    | 0 => None
    | S rest => match smart_machine_step state with
      | Some next => run_smart_machine rest next
      | None => None
      end
    end
  end.

Lemma smart_nonterminal_progress : forall state,
  (exists result, state = SmartDone result) \/
  (exists next, smart_machine_step state = Some next).
Proof.
  intros state; destruct state; try (right; eexists; reflexivity); left; eauto.
Qed.

Lemma smart_step_is_nonterminal : forall state next,
  smart_machine_step state = Some next ->
  forall fuel, run_smart_machine (S fuel) state = run_smart_machine fuel next.
Proof.
  intros state next H fuel. destruct state;
    cbn [smart_machine_step] in H; inversion H; reflexivity.
Qed.

Theorem bounded_smart_machine_is_sound : forall fuel state result,
  run_smart_machine fuel state = Some result -> result = smart_state_meaning state.
Proof.
  induction fuel as [|fuel IH]; intros state result H.
  - destruct state; cbn in H; inversion H; reflexivity.
  - destruct (smart_nonterminal_progress state) as [[value E]|[next E]].
    + subst state. cbn in H. inversion H; reflexivity.
    + rewrite (smart_step_is_nonterminal _ _ E) in H.
      rewrite (smart_machine_step_preserves_meaning _ _ E). now apply IH.
Qed.

Theorem sufficient_smart_work_completes : forall fuel state,
  smart_remaining_bound state <= fuel ->
  run_smart_machine fuel state = Some (smart_state_meaning state).
Proof.
  induction fuel as [|fuel IH]; intros state Hbound.
  - destruct state; cbn [smart_remaining_bound] in Hbound; try lia; reflexivity.
  - destruct (smart_nonterminal_progress state) as [[value E]|[next E]].
    + subst state. reflexivity.
    + rewrite (smart_step_is_nonterminal _ _ E).
      rewrite (smart_machine_step_preserves_meaning _ _ E).
      apply IH. pose proof (smart_step_decreases_remaining_bound _ _ E). lia.
Qed.

Corollary declared_alt_computes_reference : forall lhs rhs,
  run_smart_machine 4 (AltStart lhs rhs) = Some (smart_alt lhs rhs).
Proof. intros. apply sufficient_smart_work_completes. reflexivity. Qed.

Corollary declared_concat_computes_reference : forall lhs rhs,
  run_smart_machine 2 (ConcatStart lhs rhs) = Some (smart_concat lhs rhs).
Proof. intros. apply sufficient_smart_work_completes. reflexivity. Qed.

Corollary declared_star_computes_reference : forall body,
  run_smart_machine 1 (StarStart body) = Some (smart_star body).
Proof. intros. apply sufficient_smart_work_completes. reflexivity. Qed.

Theorem insufficient_work_does_not_return_a_partial_pattern : forall state,
  (forall result, state <> SmartDone result) -> run_smart_machine 0 state = None.
Proof. intros state H; destruct state; try reflexivity; exfalso; eapply H; reflexivity. Qed.

Print Assumptions smart_equal_meaning_is_reference_test.
Print Assumptions smart_machine_step_preserves_meaning.
Print Assumptions smart_step_decreases_remaining_bound.
Print Assumptions smart_nonterminal_progress.
Print Assumptions smart_step_is_nonterminal.
Print Assumptions bounded_smart_machine_is_sound.
Print Assumptions sufficient_smart_work_completes.
Print Assumptions declared_alt_computes_reference.
Print Assumptions declared_concat_computes_reference.
Print Assumptions declared_star_computes_reference.
Print Assumptions insufficient_work_does_not_return_a_partial_pattern.
