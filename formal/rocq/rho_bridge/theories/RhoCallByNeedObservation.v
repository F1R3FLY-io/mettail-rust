(*
 * RhoCallByNeedObservation: weak observation correctness for the generic
 * call-by-need encoding.
 *
 * A source computation is represented by a private thunk id and a deterministic
 * value.  The Rho encoding forces the thunk by sending a continuation to that
 * private channel and memoizes the first result.  The internal force/memo COMM
 * steps are deliberately hidden by the observation function; the public
 * observation is the value delivered to the continuation.
 *
 * Proven here:
 *   - forcing a sound memoized thunk observes the same value as source_eval;
 *   - a force miss memoizes the source value;
 *   - repeated forcing is observationally idempotent;
 *   - a repeated force after a miss does not grow or rewrite the memo;
 *   - forcing preserves the memo soundness needed for the same thunk.
 *   - the generated call-by-need artifact boundary accepts AST artifacts with
 *     the call-by-need validation profile and rejects source-text artifacts or
 *     scalar-contract profile confusion;
 *   - the current cold/hot AST thunk plans have the same two-force public
 *     observations as source evaluation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section RhoCallByNeedObservation.

  Definition ThunkId : Type := nat.
  Definition Value : Type := nat.
  Definition Memo : Type := list (ThunkId * Value).

  Record Expr : Type := {
    expr_thunk : ThunkId;
    expr_value : Value
  }.

  Fixpoint lookup (id : ThunkId) (memo : Memo) : option Value :=
    match memo with
    | [] => None
    | (k, v) :: rest => if Nat.eqb id k then Some v else lookup id rest
    end.

  Definition source_eval (e : Expr) : Value :=
    expr_value e.

  Definition memo_sound_for (e : Expr) (memo : Memo) : Prop :=
    forall v, lookup (expr_thunk e) memo = Some v -> v = expr_value e.

  Definition force (e : Expr) (memo : Memo) : Value * Memo :=
    match lookup (expr_thunk e) memo with
    | Some v => (v, memo)
    | None => (expr_value e, (expr_thunk e, expr_value e) :: memo)
    end.

  Theorem force_observes_source : forall e memo,
    memo_sound_for e memo ->
    fst (force e memo) = source_eval e.
  Proof.
    intros e memo Hsound. unfold force, source_eval.
    destruct (lookup (expr_thunk e) memo) eqn:Hlookup.
    - apply Hsound. exact Hlookup.
    - reflexivity.
  Qed.

  Theorem force_memoizes_on_miss : forall e memo,
    lookup (expr_thunk e) memo = None ->
    lookup (expr_thunk e) (snd (force e memo)) = Some (expr_value e).
  Proof.
    intros e memo Hmiss. unfold force. rewrite Hmiss. simpl.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem force_hit_preserves_memo : forall e memo v,
    lookup (expr_thunk e) memo = Some v ->
    snd (force e memo) = memo.
  Proof.
    intros e memo v Hhit. unfold force. rewrite Hhit. reflexivity.
  Qed.

  Theorem force_preserves_memo_sound_for : forall e memo,
    memo_sound_for e memo ->
    memo_sound_for e (snd (force e memo)).
  Proof.
    intros e memo Hsound v. unfold force.
    destruct (lookup (expr_thunk e) memo) eqn:Hlookup.
    - simpl. apply Hsound.
    - simpl. rewrite Nat.eqb_refl. intro H. inversion H. reflexivity.
  Qed.

  Theorem repeated_force_observation_idempotent : forall e memo,
    memo_sound_for e memo ->
    fst (force e (snd (force e memo))) = fst (force e memo).
  Proof.
    intros e memo Hsound.
    rewrite (force_observes_source e memo Hsound).
    rewrite (force_observes_source e (snd (force e memo))).
    - reflexivity.
    - apply force_preserves_memo_sound_for. exact Hsound.
  Qed.

  Theorem force_miss_then_repeated_force_preserves_memo : forall e memo,
    lookup (expr_thunk e) memo = None ->
    snd (force e (snd (force e memo))) = snd (force e memo).
  Proof.
    intros e memo Hmiss.
    unfold force. rewrite Hmiss. simpl.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem weak_observation_equivalent_to_source : forall e memo,
    memo_sound_for e memo ->
    fst (force e memo) = source_eval e
    /\ fst (force e (snd (force e memo))) = source_eval e.
  Proof.
    intros e memo Hsound. split.
    - apply force_observes_source. exact Hsound.
    - apply force_observes_source.
      apply force_preserves_memo_sound_for. exact Hsound.
  Qed.

  Inductive NeedArtifactKind : Type :=
    | NeedAst
    | NeedSourceText.

  Inductive NeedValidationProfile : Type :=
    | NeedScalarContracts
    | NeedCallByNeedThunk.

  Record NeedThunkAstPlan : Type := {
    need_artifact_kind : NeedArtifactKind;
    need_validation_profile : NeedValidationProfile;
    need_initial_memo : Memo
  }.

  Definition accepted_need_artifact (plan : NeedThunkAstPlan) : Prop :=
    need_artifact_kind plan = NeedAst
    /\ need_validation_profile plan = NeedCallByNeedThunk.

  Definition cold_need_ast_plan (_e : Expr) : NeedThunkAstPlan :=
    {| need_artifact_kind := NeedAst;
       need_validation_profile := NeedCallByNeedThunk;
       need_initial_memo := [] |}.

  Definition hot_need_ast_plan (e : Expr) : NeedThunkAstPlan :=
    {| need_artifact_kind := NeedAst;
       need_validation_profile := NeedCallByNeedThunk;
       need_initial_memo := [(expr_thunk e, expr_value e)] |}.

  Definition force_plan_twice (e : Expr) (plan : NeedThunkAstPlan)
      : list Value * Memo :=
    match force e (need_initial_memo plan) with
    | (v1, memo1) =>
        match force e memo1 with
        | (v2, memo2) => ([v1; v2], memo2)
        end
    end.

  Theorem accepted_need_artifact_is_ast : forall plan,
    accepted_need_artifact plan ->
    need_artifact_kind plan = NeedAst.
  Proof.
    intros plan Haccepted. destruct Haccepted as [Hkind _]. exact Hkind.
  Qed.

  Theorem accepted_need_artifact_has_thunk_validation_profile : forall plan,
    accepted_need_artifact plan ->
    need_validation_profile plan = NeedCallByNeedThunk.
  Proof.
    intros plan Haccepted. destruct Haccepted as [_ Hprofile]. exact Hprofile.
  Qed.

  Theorem accepted_need_artifact_rejects_source_text : forall plan,
    accepted_need_artifact plan ->
    need_artifact_kind plan <> NeedSourceText.
  Proof.
    intros plan Haccepted Hsource.
    destruct Haccepted as [Hkind _].
    rewrite Hkind in Hsource. discriminate Hsource.
  Qed.

  Theorem accepted_need_artifact_rejects_scalar_contract_profile : forall plan,
    accepted_need_artifact plan ->
    need_validation_profile plan <> NeedScalarContracts.
  Proof.
    intros plan Haccepted Hscalar.
    destruct Haccepted as [_ Hprofile].
    rewrite Hprofile in Hscalar. discriminate Hscalar.
  Qed.

  Theorem cold_ast_plan_observes_source_twice : forall e,
    fst (force_plan_twice e (cold_need_ast_plan e)) =
    [source_eval e; source_eval e].
  Proof.
    intros [id value].
    unfold force_plan_twice, cold_need_ast_plan, force, source_eval.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem hot_ast_plan_observes_source_twice : forall e,
    fst (force_plan_twice e (hot_need_ast_plan e)) =
    [source_eval e; source_eval e].
  Proof.
    intros [id value].
    unfold force_plan_twice, hot_need_ast_plan, force, source_eval.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem cold_ast_plan_memoizes_once : forall e,
    snd (force_plan_twice e (cold_need_ast_plan e)) =
    [(expr_thunk e, expr_value e)].
  Proof.
    intros [id value].
    unfold force_plan_twice, cold_need_ast_plan, force.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem hot_ast_plan_preserves_existing_memo : forall e,
    snd (force_plan_twice e (hot_need_ast_plan e)) =
    [(expr_thunk e, expr_value e)].
  Proof.
    intros [id value].
    unfold force_plan_twice, hot_need_ast_plan, force.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl.
    simpl. cbn [lookup].
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem cold_and_hot_ast_plans_are_accepted : forall e,
    accepted_need_artifact (cold_need_ast_plan e)
    /\ accepted_need_artifact (hot_need_ast_plan e).
  Proof.
    intros e. split; split; reflexivity.
  Qed.

End RhoCallByNeedObservation.
