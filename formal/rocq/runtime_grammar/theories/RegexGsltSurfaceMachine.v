(** Surface elaboration with explicit continuations.

    Grouping, plus, optionality and bounded repetition are language-defined
    operations, not parser-side text expansion. Each step below consumes one
    constructor/frame or advances one checked smart/repetition control state.
    No recursive elaborate_surface or bounded_repeat call occurs in step.
    Public nullable/derivative requests must first run this elaboration and
    only then enter their core machines. Scalar and native counter encoding
    remain admission obligations at the actual declaration boundary. *)

From Stdlib Require Import List PeanoNat.
From RuntimeGrammar Require Import RegexGsltMatch RegexGsltSmartMachine
  RegexGsltRepeatMachine.
Import ListNotations.

Inductive SurfaceFrame :=
| EAltLeft (rhs : SurfacePattern)
| EAltRight (lhs : RegexPattern)
| EConcatLeft (rhs : SurfacePattern)
| EConcatRight (lhs : RegexPattern)
| EStar
| EPlus
| EPlusFactor (body : RegexPattern)
| EOptional
| ERepeat (lower upper : nat).

Inductive SurfaceState :=
| EvaluateSurface (pattern : SurfacePattern) (frames : list SurfaceFrame)
| ReturnExpanded (pattern : RegexPattern) (frames : list SurfaceFrame)
| AwaitExpansionSmart (sub : SmartState) (frames : list SurfaceFrame)
| AwaitExpansionRepeat (sub : RepeatState) (frames : list SurfaceFrame)
| DoneExpanded (pattern : RegexPattern).

Definition surface_machine_step (state : SurfaceState) : option SurfaceState :=
  match state with
  | EvaluateSurface pattern frames => Some
      (match pattern with
      | SurfaceFail => ReturnExpanded FailPattern frames
      | SurfaceEpsilon => ReturnExpanded EpsilonPattern frames
      | SurfaceLiteral scalar => ReturnExpanded (LiteralPattern scalar) frames
      | SurfaceAny => ReturnExpanded AnyPattern frames
      | SurfaceGroup body => EvaluateSurface body frames
      | SurfaceAlt lhs rhs => EvaluateSurface lhs (EAltLeft rhs :: frames)
      | SurfaceConcat lhs rhs => EvaluateSurface lhs (EConcatLeft rhs :: frames)
      | SurfaceStar body => EvaluateSurface body (EStar :: frames)
      | SurfacePlus body => EvaluateSurface body (EPlus :: frames)
      | SurfaceOptional body => EvaluateSurface body (EOptional :: frames)
      | SurfaceRepeat body lower upper => EvaluateSurface body (ERepeat lower upper :: frames)
      end)
  | ReturnExpanded result [] => Some (DoneExpanded result)
  | ReturnExpanded result (frame :: frames) => Some
      (match frame with
      | EAltLeft rhs => EvaluateSurface rhs (EAltRight result :: frames)
      | EAltRight lhs => AwaitExpansionSmart (AltStart lhs result) frames
      | EConcatLeft rhs => EvaluateSurface rhs (EConcatRight result :: frames)
      | EConcatRight lhs => AwaitExpansionSmart (ConcatStart lhs result) frames
      | EStar => AwaitExpansionSmart (StarStart result) frames
      | EPlus => AwaitExpansionSmart (StarStart result) (EPlusFactor result :: frames)
      | EPlusFactor body => AwaitExpansionSmart (ConcatStart body result) frames
      | EOptional => AwaitExpansionSmart (AltStart EpsilonPattern result) frames
      | ERepeat lower upper =>
          AwaitExpansionRepeat (RepeatRequired result lower upper 0 EpsilonPattern) frames
      end)
  | AwaitExpansionSmart sub frames =>
      match sub with
      | SmartDone result => Some (ReturnExpanded result frames)
      | _ => option_map (fun next => AwaitExpansionSmart next frames) (smart_machine_step sub)
      end
  | AwaitExpansionRepeat sub frames =>
      match sub with
      | RepeatDone result => Some (ReturnExpanded result frames)
      | _ => option_map (fun next => AwaitExpansionRepeat next frames) (repeat_machine_step sub)
      end
  | DoneExpanded _ => None
  end.

Inductive SurfaceSteps : SurfaceState -> SurfaceState -> Prop :=
| SurfaceStepsRefl : forall state, SurfaceSteps state state
| SurfaceStepsNext : forall source next target,
    surface_machine_step source = Some next -> SurfaceSteps next target -> SurfaceSteps source target.

Lemma surface_steps_trans : forall source middle target,
  SurfaceSteps source middle -> SurfaceSteps middle target -> SurfaceSteps source target.
Proof. intros source middle target Hfirst Hlast; induction Hfirst; eauto using SurfaceStepsNext. Qed.

Lemma surface_one_step : forall source target,
  surface_machine_step source = Some target -> SurfaceSteps source target.
Proof. intros; eapply SurfaceStepsNext; [eassumption|constructor]. Qed.

Lemma smart_step_lifts_to_surface : forall sub next frames,
  smart_machine_step sub = Some next ->
  surface_machine_step (AwaitExpansionSmart sub frames) = Some (AwaitExpansionSmart next frames).
Proof.
  intros sub next frames H; destruct sub; try discriminate;
    cbn [surface_machine_step]; now rewrite H.
Qed.

Lemma repeat_step_lifts_to_surface : forall sub next frames,
  repeat_machine_step sub = Some next ->
  surface_machine_step (AwaitExpansionRepeat sub frames) = Some (AwaitExpansionRepeat next frames).
Proof.
  intros sub next frames H; destruct sub; try discriminate;
    cbn [surface_machine_step]; now rewrite H.
Qed.

Lemma surface_lifts_completed_smart_run : forall fuel sub result frames,
  run_smart_machine fuel sub = Some result ->
  SurfaceSteps (AwaitExpansionSmart sub frames) (ReturnExpanded result frames).
Proof.
  induction fuel as [|fuel IH]; intros sub result frames H.
  - destruct sub; cbn in H; try discriminate; inversion H; subst;
      apply surface_one_step; reflexivity.
  - destruct (smart_nonterminal_progress sub) as [[value E]|[next E]].
    + subst sub. cbn in H. inversion H; subst. apply surface_one_step; reflexivity.
    + rewrite (smart_step_is_nonterminal _ _ E) in H.
      eapply SurfaceStepsNext; [exact (smart_step_lifts_to_surface _ _ _ E)|]. now apply IH.
Qed.

Lemma surface_lifts_repeat_steps : forall source target frames,
  RepeatSteps source target ->
  SurfaceSteps (AwaitExpansionRepeat source frames) (AwaitExpansionRepeat target frames).
Proof.
  intros source target frames H; induction H; [constructor|].
  eapply SurfaceStepsNext; [exact (repeat_step_lifts_to_surface _ _ _ H)|assumption].
Qed.

Lemma surface_repeat_completes : forall pattern lower upper frames,
  SurfaceSteps (AwaitExpansionRepeat (RepeatRequired pattern lower upper 0 EpsilonPattern) frames)
    (ReturnExpanded (bounded_repeat pattern lower upper) frames).
Proof.
  intros. eapply surface_steps_trans.
  - apply surface_lifts_repeat_steps, declared_repeat_computes_reference.
  - apply surface_one_step; reflexivity.
Qed.

(** The finite trace returns to the original continuation without executing
    it. This context-parametric statement justifies nesting all surface forms. *)
Theorem surface_evaluation_returns_reference : forall pattern frames,
  SurfaceSteps (EvaluateSurface pattern frames) (ReturnExpanded (elaborate_surface pattern) frames).
Proof.
  induction pattern as [| |scalar| |body IHbody|lhs IHlhs rhs IHrhs|
    lhs IHlhs rhs IHrhs|body IHbody|body IHbody|body IHbody|body IHbody lower upper];
    intro frames.
  - apply surface_one_step; reflexivity.
  - apply surface_one_step; reflexivity.
  - apply surface_one_step; reflexivity.
  - apply surface_one_step; reflexivity.
  - eapply SurfaceStepsNext; [reflexivity|]. apply IHbody.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHlhs|].
    eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHrhs|].
    eapply SurfaceStepsNext; [reflexivity|].
    apply surface_lifts_completed_smart_run with (fuel := 4), declared_alt_computes_reference.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHlhs|].
    eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHrhs|].
    eapply SurfaceStepsNext; [reflexivity|].
    apply surface_lifts_completed_smart_run with (fuel := 2), declared_concat_computes_reference.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHbody|].
    eapply SurfaceStepsNext; [reflexivity|].
    apply surface_lifts_completed_smart_run with (fuel := 1), declared_star_computes_reference.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHbody|].
    eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans.
    + apply surface_lifts_completed_smart_run with (fuel := 1), declared_star_computes_reference.
    + eapply SurfaceStepsNext; [reflexivity|].
      apply surface_lifts_completed_smart_run with (fuel := 2), declared_concat_computes_reference.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHbody|].
    eapply SurfaceStepsNext; [reflexivity|].
    apply surface_lifts_completed_smart_run with (fuel := 4), declared_alt_computes_reference.
  - eapply SurfaceStepsNext; [reflexivity|].
    eapply surface_steps_trans; [apply IHbody|].
    eapply SurfaceStepsNext; [reflexivity|]. apply surface_repeat_completes.
Qed.

Theorem declared_surface_computes_reference : forall pattern,
  SurfaceSteps (EvaluateSurface pattern []) (DoneExpanded (elaborate_surface pattern)).
Proof.
  intros. eapply surface_steps_trans; [apply surface_evaluation_returns_reference|].
  apply surface_one_step; reflexivity.
Qed.

Lemma surface_terminal_is_unique : forall source first,
  SurfaceSteps source first -> surface_machine_step first = None ->
  forall second, SurfaceSteps source second -> surface_machine_step second = None -> first = second.
Proof.
  intros source first Hfirst; induction Hfirst; intros Hterminal second Hsecond Hterminal2.
  - inversion Hsecond; subst; [reflexivity|congruence].
  - inversion Hsecond; subst; [congruence|].
    assert (next = next0) by congruence. subst next0. eapply IHHfirst; eassumption.
Qed.

Theorem completed_surface_cannot_misreport : forall pattern result,
  SurfaceSteps (EvaluateSurface pattern []) (DoneExpanded result) ->
  result = elaborate_surface pattern.
Proof.
  intros. pose proof (surface_terminal_is_unique _ _ H eq_refl _
    (declared_surface_computes_reference pattern) eq_refl) as E. now inversion E.
Qed.

Print Assumptions surface_steps_trans.
Print Assumptions surface_one_step.
Print Assumptions smart_step_lifts_to_surface.
Print Assumptions repeat_step_lifts_to_surface.
Print Assumptions surface_lifts_completed_smart_run.
Print Assumptions surface_lifts_repeat_steps.
Print Assumptions surface_repeat_completes.
Print Assumptions surface_evaluation_returns_reference.
Print Assumptions declared_surface_computes_reference.
Print Assumptions surface_terminal_is_unique.
Print Assumptions completed_surface_cannot_misreport.
