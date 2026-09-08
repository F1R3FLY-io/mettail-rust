(** Small-step continuation machine for the declared Nullable computation.

    Pattern semantics are imported, not redefined. Each step below is one
    disjoint constructor rewrite; there is no recursive nullable call in step.
    Recursive functions appear only in the reference denotation and termination
    measure. The future DDL encoding must match these state/frame cases and the
    existing generic normalization kernel, with explicit source tests. *)

From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch.
Import ListNotations.

Inductive NullableFrame :=
| AltLeft (rhs : RegexPattern)
| AltRight (lhs : bool)
| ConcatLeft (rhs : RegexPattern)
| ConcatRight (lhs : bool).

Inductive NullableState :=
| EvaluateNullable (pattern : RegexPattern) (frames : list NullableFrame)
| ReturnNullable (result : bool) (frames : list NullableFrame)
| DoneNullable (result : bool).

Definition nullable_machine_step (state : NullableState) : option NullableState :=
  match state with
  | EvaluateNullable pattern frames =>
    Some (match pattern with
    | FailPattern | LiteralPattern _ | AnyPattern => ReturnNullable false frames
    | EpsilonPattern | StarPattern _ => ReturnNullable true frames
    | AltPattern lhs rhs => EvaluateNullable lhs (AltLeft rhs :: frames)
    | ConcatPattern lhs rhs => EvaluateNullable lhs (ConcatLeft rhs :: frames)
    end)
  | ReturnNullable result [] => Some (DoneNullable result)
  | ReturnNullable result (frame :: frames) =>
    Some (match frame with
    | AltLeft rhs => EvaluateNullable rhs (AltRight result :: frames)
    | AltRight lhs => ReturnNullable (orb lhs result) frames
    | ConcatLeft rhs => EvaluateNullable rhs (ConcatRight result :: frames)
    | ConcatRight lhs => ReturnNullable (andb lhs result) frames
    end)
  | DoneNullable _ => None
  end.

Fixpoint nullable_frames_meaning (frames : list NullableFrame) (result : bool) : bool :=
  match frames with
  | [] => result
  | frame :: rest => nullable_frames_meaning rest
      (match frame with
      | AltLeft rhs => orb result (nullable rhs)
      | AltRight lhs => orb lhs result
      | ConcatLeft rhs => andb result (nullable rhs)
      | ConcatRight lhs => andb lhs result
      end)
  end.

Definition nullable_state_meaning (state : NullableState) : bool :=
  match state with
  | EvaluateNullable pattern frames => nullable_frames_meaning frames (nullable pattern)
  | ReturnNullable result frames => nullable_frames_meaning frames result
  | DoneNullable result => result
  end.

Theorem nullable_machine_step_preserves_meaning : forall source target,
  nullable_machine_step source = Some target ->
  nullable_state_meaning source = nullable_state_meaning target.
Proof.
  intros source target H. destruct source as [pattern frames|result frames|result].
  - destruct pattern; cbn [nullable_machine_step] in H; inversion H; reflexivity.
  - destruct frames as [|frame rest].
    + cbn [nullable_machine_step] in H. inversion H; reflexivity.
    + destruct frame; cbn [nullable_machine_step] in H; inversion H; reflexivity.
  - discriminate.
Qed.

(** Logical transitions, not parser ranking, semantic grades, funding or RSS. *)
Fixpoint nullable_evaluation_steps (pattern : RegexPattern) : nat :=
  match pattern with
  | AltPattern lhs rhs | ConcatPattern lhs rhs =>
      nullable_evaluation_steps lhs + nullable_evaluation_steps rhs + 3
  | _ => 1
  end.

Fixpoint nullable_frame_steps (frames : list NullableFrame) : nat :=
  match frames with
  | [] => 0
  | frame :: rest =>
      (match frame with
      | AltLeft rhs | ConcatLeft rhs => 2 + nullable_evaluation_steps rhs
      | AltRight _ | ConcatRight _ => 1
      end) + nullable_frame_steps rest
  end.

Definition nullable_remaining_steps (state : NullableState) : nat :=
  match state with
  | EvaluateNullable pattern frames =>
      nullable_evaluation_steps pattern + 1 + nullable_frame_steps frames
  | ReturnNullable _ frames => 1 + nullable_frame_steps frames
  | DoneNullable _ => 0
  end.

Theorem nullable_step_decreases_exact_remaining_work : forall source target,
  nullable_machine_step source = Some target ->
  nullable_remaining_steps source = S (nullable_remaining_steps target).
Proof.
  intros source target H. destruct source as [pattern frames|result frames|result].
  - destruct pattern; cbn [nullable_machine_step] in H; inversion H; subst;
      cbn [nullable_remaining_steps nullable_evaluation_steps nullable_frame_steps]; lia.
  - destruct frames as [|frame rest].
    + cbn [nullable_machine_step] in H. inversion H; reflexivity.
    + destruct frame; cbn [nullable_machine_step] in H; inversion H; subst;
        cbn [nullable_remaining_steps nullable_frame_steps]; lia.
  - discriminate.
Qed.

Fixpoint run_nullable_machine (fuel : nat) (state : NullableState) : option bool :=
  match state with
  | DoneNullable result => Some result
  | _ =>
    match fuel with
    | 0 => None
    | S rest =>
      match nullable_machine_step state with
      | None => None
      | Some next => run_nullable_machine rest next
      end
    end
  end.

Lemma nullable_step_is_nonterminal : forall state next,
  nullable_machine_step state = Some next ->
  forall fuel, run_nullable_machine (S fuel) state = run_nullable_machine fuel next.
Proof.
  intros state next H fuel; destruct state as [pattern frames|result frames|result].
  - destruct pattern; inversion H; reflexivity.
  - destruct frames as [|frame rest]; [inversion H; reflexivity|].
    destruct frame; inversion H; reflexivity.
  - discriminate.
Qed.

Theorem bounded_nullable_machine_is_sound : forall fuel state result,
  run_nullable_machine fuel state = Some result -> result = nullable_state_meaning state.
Proof.
  induction fuel as [|fuel IH]; intros state result H;
    destruct state as [pattern frames|value frames|value];
    try (cbn in H; inversion H; reflexivity).
  - change (match nullable_machine_step (EvaluateNullable pattern frames) with
      | Some next => run_nullable_machine fuel next | None => None end = Some result) in H.
    destruct (nullable_machine_step (EvaluateNullable pattern frames)) as [next|] eqn:E;
      [|discriminate].
    rewrite (nullable_machine_step_preserves_meaning _ _ E). now apply IH.
  - change (match nullable_machine_step (ReturnNullable value frames) with
      | Some next => run_nullable_machine fuel next | None => None end = Some result) in H.
    destruct (nullable_machine_step (ReturnNullable value frames)) as [next|] eqn:E;
      [|discriminate].
    rewrite (nullable_machine_step_preserves_meaning _ _ E). now apply IH.
Qed.

Theorem sufficient_nullable_work_completes : forall fuel state,
  nullable_remaining_steps state <= fuel ->
  run_nullable_machine fuel state = Some (nullable_state_meaning state).
Proof.
  induction fuel as [|fuel IH]; intros state Hbound.
  - destruct state; cbn [nullable_remaining_steps] in Hbound; try lia; reflexivity.
  - destruct state as [pattern frames|result frames|result]; [| |reflexivity].
    + assert (Hex : exists next,
        nullable_machine_step (EvaluateNullable pattern frames) = Some next).
      { destruct pattern; eexists; reflexivity. }
      destruct Hex as [next E]. rewrite (nullable_step_is_nonterminal _ _ E).
      rewrite (nullable_machine_step_preserves_meaning _ _ E).
      apply IH. pose proof (nullable_step_decreases_exact_remaining_work _ _ E). lia.
    + assert (Hex : exists next,
        nullable_machine_step (ReturnNullable result frames) = Some next).
      { destruct frames as [|frame rest]; [eexists; reflexivity|].
        destruct frame; eexists; reflexivity. }
      destruct Hex as [next E]. rewrite (nullable_step_is_nonterminal _ _ E).
      rewrite (nullable_machine_step_preserves_meaning _ _ E).
      apply IH. pose proof (nullable_step_decreases_exact_remaining_work _ _ E). lia.
Qed.

Corollary declared_nullable_machine_computes_reference : forall pattern,
  run_nullable_machine (nullable_evaluation_steps pattern + 1)
    (EvaluateNullable pattern []) = Some (nullable pattern).
Proof.
  intro pattern. apply sufficient_nullable_work_completes.
  cbn [nullable_remaining_steps nullable_frame_steps]. lia.
Qed.

Example nullable_zero_budget_does_not_fabricate_false :
  run_nullable_machine 0 (EvaluateNullable FailPattern []) = None.
Proof. reflexivity. Qed.

Print Assumptions nullable_machine_step_preserves_meaning.
Print Assumptions nullable_step_decreases_exact_remaining_work.
Print Assumptions nullable_step_is_nonterminal.
Print Assumptions bounded_nullable_machine_is_sound.
Print Assumptions sufficient_nullable_work_completes.
Print Assumptions declared_nullable_machine_computes_reference.
Print Assumptions nullable_zero_budget_does_not_fabricate_false.
