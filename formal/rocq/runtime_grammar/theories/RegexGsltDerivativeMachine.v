(** Derivative driver composed from the checked nullable and smart machines.

    Every operational call advances one explicit control state. Reference
    derivative/nullable functions occur only in denotations and proofs, never
    as big-step callbacks in derivative_machine_step. AwaitNullable keeps
    Boolean results separate from pattern-return frames. Internal submachine
    completion is not a public DonePattern result.

    This module covers the seven elaborated core constructors. Public surface
    grouping, plus, optionality and bounded repetition require their declared
    elaboration refinement before these core results can be applied. *)

From Stdlib Require Import List PeanoNat.
From RuntimeGrammar Require Import RegexGsltMatch
  RegexGsltNullableMachine RegexGsltSmartMachine.
Import ListNotations.

Inductive DerivativeFrame :=
| DAltLeft (scalar : Scalar) (rhs : RegexPattern)
| DAltRight (lhs : RegexPattern)
| DConcatLeft (scalar : Scalar) (lhs rhs : RegexPattern)
| DConcatProduct (scalar : Scalar) (lhs rhs : RegexPattern)
| DConcatRight (base : RegexPattern)
| DStarBody (body : RegexPattern)
| DStarFactor (dbody : RegexPattern).

Inductive DerivativeState :=
| EvaluateDerivative (scalar : Scalar) (pattern : RegexPattern)
    (frames : list DerivativeFrame)
| CompareLiteral (scalar expected : Scalar) (frames : list DerivativeFrame)
| DecideLiteral (equal : bool) (frames : list DerivativeFrame)
| ReturnPattern (result : RegexPattern) (frames : list DerivativeFrame)
| AwaitNullable (state : NullableState) (scalar : Scalar)
    (rhs base : RegexPattern) (frames : list DerivativeFrame)
| AwaitSmart (state : SmartState) (frames : list DerivativeFrame)
| DonePattern (result : RegexPattern).

Definition derivative_machine_step (state : DerivativeState) : option DerivativeState :=
  match state with
  | EvaluateDerivative scalar pattern frames => Some
    (match pattern with
    | FailPattern | EpsilonPattern => ReturnPattern FailPattern frames
    | LiteralPattern expected => CompareLiteral scalar expected frames
    | AnyPattern => ReturnPattern EpsilonPattern frames
    | AltPattern lhs rhs => EvaluateDerivative scalar lhs (DAltLeft scalar rhs :: frames)
    | ConcatPattern lhs rhs =>
        EvaluateDerivative scalar lhs (DConcatLeft scalar lhs rhs :: frames)
    | StarPattern body => EvaluateDerivative scalar body (DStarBody body :: frames)
    end)
  | CompareLiteral scalar expected frames => Some (DecideLiteral (Nat.eqb scalar expected) frames)
  | DecideLiteral equal frames =>
      Some (ReturnPattern (if equal then EpsilonPattern else FailPattern) frames)
  | ReturnPattern result [] => Some (DonePattern result)
  | ReturnPattern result (frame :: frames) => Some
    (match frame with
    | DAltLeft scalar rhs => EvaluateDerivative scalar rhs (DAltRight result :: frames)
    | DAltRight lhs => AwaitSmart (AltStart lhs result) frames
    | DConcatLeft scalar lhs rhs =>
        AwaitSmart (ConcatStart result rhs) (DConcatProduct scalar lhs rhs :: frames)
    | DConcatProduct scalar lhs rhs =>
        AwaitNullable (EvaluateNullable lhs []) scalar rhs result frames
    | DConcatRight base => AwaitSmart (AltStart base result) frames
    | DStarBody body => AwaitSmart (StarStart body) (DStarFactor result :: frames)
    | DStarFactor dbody => AwaitSmart (ConcatStart dbody result) frames
    end)
  | AwaitNullable sub scalar rhs base frames =>
    match sub with
    | DoneNullable result => Some
        (if result then EvaluateDerivative scalar rhs (DConcatRight base :: frames)
         else ReturnPattern base frames)
    | _ => option_map (fun next => AwaitNullable next scalar rhs base frames)
        (nullable_machine_step sub)
    end
  | AwaitSmart sub frames =>
    match sub with
    | SmartDone result => Some (ReturnPattern result frames)
    | _ => option_map (fun next => AwaitSmart next frames) (smart_machine_step sub)
    end
  | DonePattern _ => None
  end.

Fixpoint derivative_frames_meaning (frames : list DerivativeFrame)
    (result : RegexPattern) : RegexPattern :=
  match frames with
  | [] => result
  | frame :: rest => derivative_frames_meaning rest
    (match frame with
    | DAltLeft scalar rhs => smart_alt result (derivative scalar rhs)
    | DAltRight lhs => smart_alt lhs result
    | DConcatLeft scalar lhs rhs =>
        let base := smart_concat result rhs in
        if nullable lhs then smart_alt base (derivative scalar rhs) else base
    | DConcatProduct scalar lhs rhs =>
        if nullable lhs then smart_alt result (derivative scalar rhs) else result
    | DConcatRight base => smart_alt base result
    | DStarBody body => smart_concat result (smart_star body)
    | DStarFactor dbody => smart_concat dbody result
    end)
  end.

Definition derivative_state_meaning (state : DerivativeState) : RegexPattern :=
  match state with
  | EvaluateDerivative scalar pattern frames =>
      derivative_frames_meaning frames (derivative scalar pattern)
  | CompareLiteral scalar expected frames => derivative_frames_meaning frames
      (if Nat.eqb scalar expected then EpsilonPattern else FailPattern)
  | DecideLiteral equal frames => derivative_frames_meaning frames
      (if equal then EpsilonPattern else FailPattern)
  | ReturnPattern result frames => derivative_frames_meaning frames result
  | AwaitNullable sub scalar rhs base frames => derivative_frames_meaning frames
      (if nullable_state_meaning sub then smart_alt base (derivative scalar rhs) else base)
  | AwaitSmart sub frames => derivative_frames_meaning frames (smart_state_meaning sub)
  | DonePattern result => result
  end.

Lemma nullable_step_lifts_to_derivative : forall sub next scalar rhs base frames,
  nullable_machine_step sub = Some next ->
  derivative_machine_step (AwaitNullable sub scalar rhs base frames) =
    Some (AwaitNullable next scalar rhs base frames).
Proof.
  intros sub next scalar rhs base frames H. destruct sub; try discriminate;
    cbn [derivative_machine_step]; now rewrite H.
Qed.

Lemma smart_step_lifts_to_derivative : forall sub next frames,
  smart_machine_step sub = Some next ->
  derivative_machine_step (AwaitSmart sub frames) = Some (AwaitSmart next frames).
Proof.
  intros sub next frames H. destruct sub; try discriminate;
    cbn [derivative_machine_step]; now rewrite H.
Qed.

Theorem derivative_machine_step_preserves_meaning : forall source target,
  derivative_machine_step source = Some target ->
  derivative_state_meaning source = derivative_state_meaning target.
Proof.
  intros source target H. destruct source as
    [scalar pattern frames|scalar expected frames|equal frames|result frames|
     sub scalar rhs base frames|sub frames|result].
  - destruct pattern; inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - destruct frames as [|frame rest]; [inversion H; reflexivity|].
    destruct frame; inversion H; reflexivity.
  - destruct sub as [pattern stack|value stack|value].
    + change (option_map (fun next => AwaitNullable next scalar rhs base frames)
        (nullable_machine_step (EvaluateNullable pattern stack)) =
        Some target) in H.
      destruct (nullable_machine_step (EvaluateNullable pattern stack)) as [next|] eqn:E;
        [|discriminate]. inversion H; subst.
      cbn [derivative_state_meaning]. now rewrite (nullable_machine_step_preserves_meaning _ _ E).
    + change (option_map (fun next => AwaitNullable next scalar rhs base frames)
        (nullable_machine_step (ReturnNullable value stack)) =
        Some target) in H.
      destruct (nullable_machine_step (ReturnNullable value stack)) as [next|] eqn:E;
        [|discriminate]. inversion H; subst.
      cbn [derivative_state_meaning]. now rewrite (nullable_machine_step_preserves_meaning _ _ E).
    + destruct value; inversion H; reflexivity.
  - destruct (smart_nonterminal_progress sub) as [[value E]|[next E]].
    + subst sub. inversion H; reflexivity.
    + rewrite (smart_step_lifts_to_derivative _ _ _ E) in H. inversion H; subst.
      cbn [derivative_state_meaning]. now rewrite (smart_machine_step_preserves_meaning _ _ E).
  - discriminate.
Qed.

Inductive DerivativeSteps : DerivativeState -> DerivativeState -> Prop :=
| DerivativeStepsRefl : forall state, DerivativeSteps state state
| DerivativeStepsNext : forall source next target,
    derivative_machine_step source = Some next ->
    DerivativeSteps next target -> DerivativeSteps source target.

Lemma derivative_steps_trans : forall source middle target,
  DerivativeSteps source middle -> DerivativeSteps middle target -> DerivativeSteps source target.
Proof. intros source middle target Hfirst Hlast; induction Hfirst; eauto using DerivativeStepsNext. Qed.

Lemma derivative_one_step : forall source target,
  derivative_machine_step source = Some target -> DerivativeSteps source target.
Proof. intros; eapply DerivativeStepsNext; [eassumption|constructor]. Qed.

Theorem derivative_steps_preserve_meaning : forall source target,
  DerivativeSteps source target -> derivative_state_meaning source = derivative_state_meaning target.
Proof.
  intros source target H; induction H; [reflexivity|].
  rewrite (derivative_machine_step_preserves_meaning _ _ H). exact IHDerivativeSteps.
Qed.

Lemma completed_smart_run_lifts : forall fuel sub result frames,
  run_smart_machine fuel sub = Some result ->
  DerivativeSteps (AwaitSmart sub frames) (ReturnPattern result frames).
Proof.
  induction fuel as [|fuel IH]; intros sub result frames H.
  - destruct sub; cbn in H; try discriminate; inversion H; subst;
      apply derivative_one_step; reflexivity.
  - destruct (smart_nonterminal_progress sub) as [[value E]|[next E]].
    + subst sub. cbn in H. inversion H; subst. apply derivative_one_step; reflexivity.
    + rewrite (smart_step_is_nonterminal _ _ E) in H.
      eapply DerivativeStepsNext; [exact (smart_step_lifts_to_derivative _ _ _ E)|].
      now apply IH.
Qed.

Lemma completed_nullable_run_lifts : forall fuel sub result scalar rhs base frames,
  run_nullable_machine fuel sub = Some result ->
  DerivativeSteps (AwaitNullable sub scalar rhs base frames)
    (if result then EvaluateDerivative scalar rhs (DConcatRight base :: frames)
     else ReturnPattern base frames).
Proof.
  induction fuel as [|fuel IH]; intros sub result scalar rhs base frames H.
  - destruct sub; cbn in H; try discriminate; inversion H; subst;
      apply derivative_one_step; reflexivity.
  - destruct sub as [pattern stack|value stack|value].
    + assert (Hex : exists next,
        nullable_machine_step (EvaluateNullable pattern stack) = Some next).
      { destruct pattern; eexists; reflexivity. }
      destruct Hex as [next E]. rewrite (nullable_step_is_nonterminal _ _ E) in H.
      eapply DerivativeStepsNext;
        [exact (nullable_step_lifts_to_derivative _ _ _ _ _ _ E)|]. now apply IH.
    + assert (Hex : exists next,
        nullable_machine_step (ReturnNullable value stack) = Some next).
      { destruct stack as [|frame rest]; [eexists; reflexivity|].
        destruct frame; eexists; reflexivity. }
      destruct Hex as [next E]. rewrite (nullable_step_is_nonterminal _ _ E) in H.
      eapply DerivativeStepsNext;
        [exact (nullable_step_lifts_to_derivative _ _ _ _ _ _ E)|]. now apply IH.
    + cbn in H. inversion H; subst. apply derivative_one_step; reflexivity.
Qed.

(** The continuation parameter remains untouched by this finite trace. This
    is what allows induction to reuse the same machine under nested frames. *)
Theorem derivative_evaluation_returns_reference : forall pattern scalar frames,
  DerivativeSteps (EvaluateDerivative scalar pattern frames)
    (ReturnPattern (derivative scalar pattern) frames).
Proof.
  induction pattern as [| |expected| |lhs IHlhs rhs IHrhs|lhs IHlhs rhs IHrhs|body IHbody];
    intros scalar frames.
  - apply derivative_one_step; reflexivity.
  - apply derivative_one_step; reflexivity.
  - eapply DerivativeStepsNext; [reflexivity|].
    eapply DerivativeStepsNext; [reflexivity|]. apply derivative_one_step; reflexivity.
  - apply derivative_one_step; reflexivity.
  - eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans; [apply IHlhs|].
    eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans; [apply IHrhs|].
    eapply DerivativeStepsNext; [reflexivity|].
    apply completed_smart_run_lifts with (fuel := 4). apply declared_alt_computes_reference.
  - eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans; [apply IHlhs|].
    eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans.
    + apply completed_smart_run_lifts with (fuel := 2). apply declared_concat_computes_reference.
    + eapply DerivativeStepsNext; [reflexivity|].
      eapply derivative_steps_trans.
      * apply completed_nullable_run_lifts with (fuel := nullable_evaluation_steps lhs + 1).
        apply declared_nullable_machine_computes_reference.
      * cbn [derivative]. destruct (nullable lhs) eqn:E; [|constructor].
        eapply derivative_steps_trans; [apply IHrhs|].
        eapply DerivativeStepsNext; [reflexivity|].
        apply completed_smart_run_lifts with (fuel := 4). apply declared_alt_computes_reference.
  - eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans; [apply IHbody|].
    eapply DerivativeStepsNext; [reflexivity|].
    eapply derivative_steps_trans.
    + apply completed_smart_run_lifts with (fuel := 1). apply declared_star_computes_reference.
    + eapply DerivativeStepsNext; [reflexivity|].
      apply completed_smart_run_lifts with (fuel := 2). apply declared_concat_computes_reference.
Qed.

Theorem derivative_core_completes : forall scalar pattern,
  DerivativeSteps (EvaluateDerivative scalar pattern []) (DonePattern (derivative scalar pattern)).
Proof.
  intros. eapply derivative_steps_trans; [apply derivative_evaluation_returns_reference|].
  apply derivative_one_step; reflexivity.
Qed.

Theorem completed_derivative_cannot_misreport : forall scalar pattern result,
  DerivativeSteps (EvaluateDerivative scalar pattern []) (DonePattern result) ->
  result = derivative scalar pattern.
Proof. intros. symmetry. exact (derivative_steps_preserve_meaning _ _ H). Qed.

Print Assumptions nullable_step_lifts_to_derivative.
Print Assumptions smart_step_lifts_to_derivative.
Print Assumptions derivative_machine_step_preserves_meaning.
Print Assumptions derivative_steps_trans.
Print Assumptions derivative_one_step.
Print Assumptions derivative_steps_preserve_meaning.
Print Assumptions completed_smart_run_lifts.
Print Assumptions completed_nullable_run_lifts.
Print Assumptions derivative_evaluation_returns_reference.
Print Assumptions derivative_core_completes.
Print Assumptions completed_derivative_cannot_misreport.
