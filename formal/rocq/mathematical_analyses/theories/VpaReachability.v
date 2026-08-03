(*
 * VpaReachability: exact finite summary specification for VPA emptiness.
 *
 * The Rust implementation computes the least relations specified below.
 * This file proves that every summary, ground reachability fact, and
 * above-bottom prefix fact denotes a concrete VPA run under final-state /
 * arbitrary-stack acceptance and bottom-read/no-pop return semantics.
 *)

From Stdlib Require Import List.
Import ListNotations.

Section Reachability.

Variables State Symbol Stack : Type.
Variable Initial : State -> Prop.
Variable Final : State -> Prop.
Variable InternalEdge : State -> Symbol -> State -> Prop.
Variable CallEdge : State -> Symbol -> Stack -> State -> Prop.
Variable ReturnEdge : State -> Symbol -> Stack -> State -> Prop.
Variable BottomReturnEdge : State -> Symbol -> State -> Prop.

Definition config := (State * list Stack)%type.

Inductive transition : config -> Symbol -> config -> Prop :=
  | transition_internal : forall state symbol target stack,
      InternalEdge state symbol target ->
      transition (state, stack) symbol (target, stack)
  | transition_call : forall state symbol pushed target stack,
      CallEdge state symbol pushed target ->
      transition (state, stack) symbol (target, pushed :: stack)
  | transition_return : forall state symbol top target stack,
      ReturnEdge state symbol top target ->
      transition (state, top :: stack) symbol (target, stack)
  | transition_bottom_return : forall state symbol target,
      BottomReturnEdge state symbol target ->
      transition (state, []) symbol (target, []).

Inductive steps : config -> list Symbol -> config -> Prop :=
  | steps_nil : forall current, steps current [] current
  | steps_cons : forall current symbol next word final,
      transition current symbol next ->
      steps next word final ->
      steps current (symbol :: word) final.

Lemma steps_append : forall first left middle right last,
  steps first left middle ->
  steps middle right last ->
  steps first (left ++ right) last.
Proof.
  intros first left middle right last Hleft Hright.
  induction Hleft.
  - simpl. exact Hright.
  - simpl. econstructor; eauto.
Qed.

(* Least relation of stack-neutral, well-matched runs. *)
Inductive balanced_summary : State -> State -> Prop :=
  | balanced_identity : forall state,
      balanced_summary state state
  | balanced_internal : forall source symbol target,
      InternalEdge source symbol target ->
      balanced_summary source target
  | balanced_concat : forall source middle target,
      balanced_summary source middle ->
      balanced_summary middle target ->
      balanced_summary source target
  | balanced_wrap : forall source call pushed inner_start inner_end ret target,
      CallEdge source call pushed inner_start ->
      balanced_summary inner_start inner_end ->
      ReturnEdge inner_end ret pushed target ->
      balanced_summary source target.

Theorem balanced_summary_run_sound : forall source target,
  balanced_summary source target ->
  forall surrounding_stack,
    exists word,
      steps (source, surrounding_stack) word (target, surrounding_stack).
Proof.
  intros source target Hsummary.
  induction Hsummary; intro surrounding_stack.
  - exists []. constructor.
  - exists [symbol]. econstructor.
    + apply transition_internal. exact H.
    + constructor.
  - destruct (IHHsummary1 surrounding_stack) as [left Hleft].
    destruct (IHHsummary2 surrounding_stack) as [right Hright].
    exists (left ++ right). eapply steps_append; eauto.
  - destruct (IHHsummary (pushed :: surrounding_stack)) as [inside Hinside].
    exists (call :: inside ++ [ret]).
    econstructor.
    + apply transition_call. exact H.
    + eapply steps_append.
      * exact Hinside.
      * econstructor.
        -- apply transition_return. exact H0.
        -- constructor.
Qed.

Theorem balanced_summary_is_least :
  forall relation : State -> State -> Prop,
    (forall state, relation state state) ->
    (forall source symbol target,
      InternalEdge source symbol target -> relation source target) ->
    (forall source middle target,
      relation source middle -> relation middle target -> relation source target) ->
    (forall source call pushed inner_start inner_end ret target,
      CallEdge source call pushed inner_start ->
      relation inner_start inner_end ->
      ReturnEdge inner_end ret pushed target ->
      relation source target) ->
    forall source target,
      balanced_summary source target -> relation source target.
Proof.
  intros relation Hidentity Hinternal Hconcat Hwrap source target Hsummary.
  induction Hsummary; eauto.
Qed.

(* Reachability while the concrete stack is at bottom. *)
Inductive ground_reachable : State -> Prop :=
  | ground_initial : forall state,
      Initial state -> ground_reachable state
  | ground_balanced : forall source target,
      ground_reachable source ->
      balanced_summary source target ->
      ground_reachable target
  | ground_bottom_return : forall source symbol target,
      ground_reachable source ->
      BottomReturnEdge source symbol target ->
      ground_reachable target.

Theorem ground_reachable_run_sound : forall target,
  ground_reachable target ->
  exists initial word,
    Initial initial /\ steps (initial, []) word (target, []).
Proof.
  intros target Hground.
  induction Hground.
  - exists state, []. split; [assumption | constructor].
  - destruct IHHground as [initial [prefix [Hinitial Hprefix]]].
    match goal with
    | Hsummary : balanced_summary _ _ |- _ =>
        destruct (balanced_summary_run_sound _ _ Hsummary []) as [suffix Hsuffix]
    end.
    exists initial, (prefix ++ suffix). split; [assumption |].
    eapply steps_append; eauto.
  - destruct IHHground as [initial [prefix [Hinitial Hprefix]]].
    exists initial, (prefix ++ [symbol]). split; [assumption |].
    eapply steps_append; [exact Hprefix |].
    econstructor.
    + apply transition_bottom_return.
      match goal with
      | Hbottom : BottomReturnEdge _ _ _ |- _ => exact Hbottom
      end.
    + constructor.
Qed.

(* After the final visit to bottom, balanced factors may be separated by calls
   whose frames remain unmatched at the accepted final state. *)
Inductive prefix_reachable : State -> Prop :=
  | prefix_ground : forall state,
      ground_reachable state -> prefix_reachable state
  | prefix_balanced : forall source target,
      prefix_reachable source ->
      balanced_summary source target ->
      prefix_reachable target
  | prefix_unmatched_call : forall source symbol pushed target,
      prefix_reachable source ->
      CallEdge source symbol pushed target ->
      prefix_reachable target.

Theorem prefix_reachable_run_sound : forall target,
  prefix_reachable target ->
  exists initial word stack,
    Initial initial /\ steps (initial, []) word (target, stack).
Proof.
  intros target Hprefix.
  induction Hprefix.
  - match goal with
    | Hground : ground_reachable _ |- _ =>
        destruct (ground_reachable_run_sound _ Hground) as
        [initial [word [Hinitial Hrun]]]
    end.
    exists initial, word, []. auto.
  - destruct IHHprefix as [initial [prefix [stack [Hinitial Hrun]]]].
    match goal with
    | Hsummary : balanced_summary _ _ |- _ =>
        destruct (balanced_summary_run_sound _ _ Hsummary stack) as [suffix Hsuffix]
    end.
    exists initial, (prefix ++ suffix), stack. split; [assumption |].
    eapply steps_append; eauto.
  - destruct IHHprefix as [initial [prefix [stack [Hinitial Hrun]]]].
    exists initial, (prefix ++ [symbol]), (pushed :: stack). split; [assumption |].
    eapply steps_append; [exact Hrun |].
    econstructor.
    + apply transition_call.
      match goal with
      | Hcall : CallEdge _ _ _ _ |- _ => exact Hcall
      end.
    + constructor.
Qed.

(* A normalized concrete configuration remembers exactly the unmatched call
   frames. The control-state segment at each stack level is summarized by the
   least balanced relation. This is the completeness invariant used to map an
   arbitrary operational run back into the finite decision abstraction. *)
Inductive normalized_reachable : State -> list Stack -> Prop :=
  | normalized_ground : forall state,
      ground_reachable state ->
      normalized_reachable state []
  | normalized_frame :
      forall caller surrounding call pushed entry current,
        normalized_reachable caller surrounding ->
        CallEdge caller call pushed entry ->
        balanced_summary entry current ->
        normalized_reachable current (pushed :: surrounding).

Lemma normalized_balanced : forall source stack,
  normalized_reachable source stack ->
  forall target,
    balanced_summary source target ->
    normalized_reachable target stack.
Proof.
  intros source stack Hnormalized target Hsummary.
  destruct Hnormalized.
  - apply normalized_ground.
    eapply ground_balanced; eauto.
  - eapply normalized_frame; eauto.
    eapply balanced_concat; eauto.
Qed.

Lemma normalized_internal : forall source stack symbol target,
  normalized_reachable source stack ->
  InternalEdge source symbol target ->
  normalized_reachable target stack.
Proof.
  intros source stack symbol target Hnormalized Hedge.
  eapply normalized_balanced; eauto.
  apply balanced_internal with symbol. exact Hedge.
Qed.

Lemma normalized_call : forall source stack symbol pushed target,
  normalized_reachable source stack ->
  CallEdge source symbol pushed target ->
  normalized_reachable target (pushed :: stack).
Proof.
  intros source stack symbol pushed target Hnormalized Hedge.
  eapply normalized_frame; eauto.
  apply balanced_identity.
Qed.

Lemma normalized_return : forall source stack symbol pushed target,
  normalized_reachable source (pushed :: stack) ->
  ReturnEdge source symbol pushed target ->
  normalized_reachable target stack.
Proof.
  intros source stack symbol pushed target Hnormalized Hreturn.
  inversion Hnormalized; subst.
  eapply normalized_balanced; eauto.
  eapply balanced_wrap; eauto.
Qed.

Lemma normalized_bottom_return : forall source symbol target,
  normalized_reachable source [] ->
  BottomReturnEdge source symbol target ->
  normalized_reachable target [].
Proof.
  intros source symbol target Hnormalized Hreturn.
  inversion Hnormalized; subst.
  apply normalized_ground.
  eapply ground_bottom_return; eauto.
Qed.

Lemma transition_preserves_normalized :
  forall source source_stack symbol target target_stack,
    transition (source, source_stack) symbol (target, target_stack) ->
    normalized_reachable source source_stack ->
    normalized_reachable target target_stack.
Proof.
  intros source source_stack symbol target target_stack Hstep Hnormalized.
  inversion Hstep; subst.
  - eapply normalized_internal; eauto.
  - eapply normalized_call; eauto.
  - eapply normalized_return; eauto.
  - eapply normalized_bottom_return; eauto.
Qed.

Theorem steps_preserve_normalized : forall start word finish,
  steps start word finish ->
  normalized_reachable (fst start) (snd start) ->
  normalized_reachable (fst finish) (snd finish).
Proof.
  intros start word finish Hsteps.
  induction Hsteps; intro Hnormalized.
  - exact Hnormalized.
  - apply IHHsteps.
    destruct current as [source source_stack].
    destruct next as [target target_stack].
    simpl in *.
    eapply transition_preserves_normalized; eauto.
Qed.

Lemma normalized_implies_prefix : forall state stack,
  normalized_reachable state stack ->
  prefix_reachable state.
Proof.
  intros state stack Hnormalized.
  induction Hnormalized.
  - apply prefix_ground. exact H.
  - eapply prefix_balanced.
    + eapply prefix_unmatched_call; eauto.
    + assumption.
Qed.

Definition summary_language_nonempty : Prop :=
  exists accepting, prefix_reachable accepting /\ Final accepting.

Definition operational_language_nonempty : Prop :=
  exists initial word accepting stack,
    Initial initial /\ Final accepting /\
    steps (initial, []) word (accepting, stack).

Theorem summary_nonempty_implies_operational_nonempty :
  summary_language_nonempty -> operational_language_nonempty.
Proof.
  intros [accepting [Hreachable Hfinal]].
  destruct (prefix_reachable_run_sound _ Hreachable) as
      [initial [word [stack [Hinitial Hrun]]]].
  exists initial, word, accepting, stack. auto.
Qed.

Theorem operational_nonempty_implies_summary_nonempty :
  operational_language_nonempty -> summary_language_nonempty.
Proof.
  intros [initial [word [accepting [stack
      [Hinitial [Hfinal Hrun]]]]]].
  assert (Hnormalized_start : normalized_reachable initial []).
  {
    apply normalized_ground.
    apply ground_initial.
    exact Hinitial.
  }
  assert (Hnormalized_finish : normalized_reachable accepting stack).
  {
    pose proof
      (steps_preserve_normalized
        (initial, []) word (accepting, stack) Hrun Hnormalized_start)
      as Hfinish.
    simpl in Hfinish.
    exact Hfinish.
  }
  exists accepting. split.
  - eapply normalized_implies_prefix. exact Hnormalized_finish.
  - exact Hfinal.
Qed.

Theorem summary_operational_nonempty_iff :
  summary_language_nonempty <-> operational_language_nonempty.
Proof.
  split.
  - apply summary_nonempty_implies_operational_nonempty.
  - apply operational_nonempty_implies_summary_nonempty.
Qed.

Print Assumptions balanced_summary_run_sound.
Print Assumptions balanced_summary_is_least.
Print Assumptions summary_nonempty_implies_operational_nonempty.
Print Assumptions operational_nonempty_implies_summary_nonempty.
Print Assumptions summary_operational_nonempty_iff.

End Reachability.
