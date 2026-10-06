(*
 * RhoCommScheduleFamily: arity-parametric schedule boundary for the generated
 * RhoNet/Dovetail COMM process slices.
 *
 * The mCRL2, Maude, and TLA+ process models in formal/{mcrl2,maude,tla}
 * instantiate a finite COMM family for executable counterexample search. This
 * file proves the corresponding family theorem for every finite list of
 * independent redex identifiers:
 *
 *   - Rho reserve/reserveJoin steps erase to tau;
 *   - every Rho reserve/fire schedule has the same visible trace as the direct
 *     Dovetail fact-step schedule;
 *   - completion is enabled exactly after every redex in the required universe
 *     has visibly fired;
 *   - a trace with a missing required redex cannot validly complete;
 *   - permutation schedules observe the same fired redex set.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.

Section RhoCommScheduleFamily.

  Definition Redex : Type := nat.

  Inductive RhoStep : Type :=
  | Reserve : Redex -> RhoStep
  | RhoFire : Redex -> RhoStep
  | ReserveJoin : RhoStep
  | RhoComplete : RhoStep.

  Inductive Observation : Type :=
  | ObsFire : Redex -> Observation
  | ObsComplete : Observation.

  Definition rho_step_observation (step : RhoStep) : list Observation :=
    match step with
    | Reserve _ => []
    | RhoFire r => [ObsFire r]
    | ReserveJoin => []
    | RhoComplete => [ObsComplete]
    end.

  Fixpoint erase_rho (steps : list RhoStep) : list Observation :=
    match steps with
    | [] => []
    | step :: rest => rho_step_observation step ++ erase_rho rest
    end.

  Fixpoint rho_fire_phase (schedule : list Redex) : list RhoStep :=
    match schedule with
    | [] => []
    | r :: rest => Reserve r :: RhoFire r :: rho_fire_phase rest
    end.

  Definition rho_complete_schedule (schedule : list Redex) : list RhoStep :=
    rho_fire_phase schedule ++ [ReserveJoin; RhoComplete].

  Definition dovetail_complete_schedule
      (schedule : list Redex) : list Observation :=
    map ObsFire schedule ++ [ObsComplete].

  Fixpoint fired_observations (trace : list Observation) : list Redex :=
    match trace with
    | [] => []
    | ObsFire r :: rest => r :: fired_observations rest
    | ObsComplete :: rest => fired_observations rest
    end.

  Definition completion_enabled
      (required fired : list Redex) : Prop :=
    forall r, In r required -> In r fired.

  Definition same_redex_set (left right : list Redex) : Prop :=
    forall r, In r left <-> In r right.

  Lemma erase_rho_app : forall left right,
    erase_rho (left ++ right) = erase_rho left ++ erase_rho right.
  Proof.
    induction left as [| step rest IH]; intros right.
    - reflexivity.
    - simpl. rewrite IH. rewrite app_assoc. reflexivity.
  Qed.

  Lemma reserve_steps_are_silent : forall r,
    erase_rho [Reserve r] = [].
  Proof.
    intros r. reflexivity.
  Qed.

  Lemma reserve_join_is_silent :
    erase_rho [ReserveJoin] = [].
  Proof.
    reflexivity.
  Qed.

  Lemma erase_rho_fire_phase : forall schedule,
    erase_rho (rho_fire_phase schedule) = map ObsFire schedule.
  Proof.
    induction schedule as [| r rest IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Theorem rho_dovetail_visible_schedule_equal : forall schedule,
    erase_rho (rho_complete_schedule schedule)
    = dovetail_complete_schedule schedule.
  Proof.
    intros schedule.
    unfold rho_complete_schedule, dovetail_complete_schedule.
    rewrite erase_rho_app.
    rewrite erase_rho_fire_phase.
    reflexivity.
  Qed.

  Lemma fired_observations_app : forall left right,
    fired_observations (left ++ right)
    = fired_observations left ++ fired_observations right.
  Proof.
    induction left as [| obs rest IH]; intros right.
    - reflexivity.
    - destruct obs as [r |]; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma fired_observations_map_fire : forall schedule,
    fired_observations (map ObsFire schedule) = schedule.
  Proof.
    induction schedule as [| r rest IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Lemma fired_observations_dovetail_complete : forall schedule,
    fired_observations (dovetail_complete_schedule schedule) = schedule.
  Proof.
    intros schedule.
    unfold dovetail_complete_schedule.
    rewrite fired_observations_app.
    rewrite fired_observations_map_fire.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma fired_observations_rho_complete : forall schedule,
    fired_observations (erase_rho (rho_complete_schedule schedule)) = schedule.
  Proof.
    intros schedule.
    rewrite rho_dovetail_visible_schedule_equal.
    apply fired_observations_dovetail_complete.
  Qed.

  Theorem completion_enabled_after_permutation : forall required schedule,
    Permutation schedule required ->
    completion_enabled required schedule.
  Proof.
    intros required schedule Hperm.
    unfold completion_enabled.
    intros r Hin.
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hin.
  Qed.

  Theorem completion_rejected_when_missing : forall required fired missing,
    In missing required ->
    ~ In missing fired ->
    ~ completion_enabled required fired.
  Proof.
    intros required fired missing Hin Hmissing Hcomplete.
    apply Hmissing.
    apply Hcomplete.
    exact Hin.
  Qed.

  Theorem rho_completion_enabled_after_full_schedule : forall required schedule,
    Permutation schedule required ->
    completion_enabled required
      (fired_observations (erase_rho (rho_complete_schedule schedule))).
  Proof.
    intros required schedule Hperm.
    rewrite fired_observations_rho_complete.
    apply completion_enabled_after_permutation.
    exact Hperm.
  Qed.

  Theorem dovetail_completion_enabled_after_full_schedule : forall required schedule,
    Permutation schedule required ->
    completion_enabled required
      (fired_observations (dovetail_complete_schedule schedule)).
  Proof.
    intros required schedule Hperm.
    rewrite fired_observations_dovetail_complete.
    apply completion_enabled_after_permutation.
    exact Hperm.
  Qed.

  Theorem rho_premature_completion_rejected : forall required prefix missing,
    In missing required ->
    ~ In missing prefix ->
    ~ completion_enabled required
        (fired_observations (erase_rho (rho_complete_schedule prefix))).
  Proof.
    intros required prefix missing Hin Hmissing.
    rewrite fired_observations_rho_complete.
    apply completion_rejected_when_missing with (missing := missing).
    - exact Hin.
    - exact Hmissing.
  Qed.

  Theorem dovetail_premature_completion_rejected : forall required prefix missing,
    In missing required ->
    ~ In missing prefix ->
    ~ completion_enabled required
        (fired_observations (dovetail_complete_schedule prefix)).
  Proof.
    intros required prefix missing Hin Hmissing.
    rewrite fired_observations_dovetail_complete.
    apply completion_rejected_when_missing with (missing := missing).
    - exact Hin.
    - exact Hmissing.
  Qed.

  Theorem permutation_schedules_same_fired_set : forall left right,
    Permutation left right ->
    same_redex_set
      (fired_observations (erase_rho (rho_complete_schedule left)))
      (fired_observations (erase_rho (rho_complete_schedule right))).
  Proof.
    intros left right Hperm r.
    repeat rewrite fired_observations_rho_complete.
    split; intro Hin.
    - eapply Permutation_in.
      + exact Hperm.
      + exact Hin.
    - eapply Permutation_in.
      + apply Permutation_sym. exact Hperm.
      + exact Hin.
  Qed.

  Theorem rho_and_dovetail_complete_same_fired_set : forall schedule,
    same_redex_set
      (fired_observations (erase_rho (rho_complete_schedule schedule)))
      (fired_observations (dovetail_complete_schedule schedule)).
  Proof.
    intros schedule r.
    rewrite fired_observations_rho_complete.
    rewrite fired_observations_dovetail_complete.
    split; intro Hin; exact Hin.
  Qed.

End RhoCommScheduleFamily.

(** The step observer emits a committed COMM before waiting for the driver's
    permit. A dropped session or disconnected receiver is a typed error from
    that wait, and the worker's checkpoint branch restores its prior state.
    This small control model abstracts away RSpace matching and payloads; it
    covers an arbitrary finite prefix of already delivered COMMs without
    constructing or reducing a trace of a particular length in the proof. *)
Section RhoStepCancellation.

  Inductive StepSignal := Permit | GateAborted | ReceiverClosed.
  Inductive StepError := Aborted | Disconnected.
  Inductive StepResult := Finished (live : nat) | Failed (reason : StepError).

  Fixpoint observe_steps (live : nat) (signals : list StepSignal) : StepResult :=
    match signals with
    | [] => Finished live
    | Permit :: rest => observe_steps (S live) rest
    | GateAborted :: _ => Failed Aborted
    | ReceiverClosed :: _ => Failed Disconnected
    end.

  Definition finish_transaction
      (checkpoint live : nat) (signals : list StepSignal) : nat * StepResult :=
    match observe_steps live signals with
    | Finished final => (final, Finished final)
    | Failed reason => (checkpoint, Failed reason)
    end.

  Lemma permit_prefix_then_failure : forall count live rest reason,
    observe_steps live
      (repeat Permit count ++
        (match reason with
         | Aborted => GateAborted
         | Disconnected => ReceiverClosed
         end) :: rest) = Failed reason.
  Proof.
    induction count as [| count IH]; intros live rest reason.
    - destruct reason; reflexivity.
    - simpl. apply IH.
  Qed.

  Theorem observer_failure_returns_error_and_rolls_back :
    forall checkpoint live count rest reason,
      finish_transaction checkpoint live
        (repeat Permit count ++
          (match reason with
           | Aborted => GateAborted
           | Disconnected => ReceiverClosed
           end) :: rest) = (checkpoint, Failed reason).
  Proof.
    intros checkpoint live count rest reason.
    unfold finish_transaction.
    rewrite permit_prefix_then_failure.
    reflexivity.
  Qed.

End RhoStepCancellation.

Print Assumptions observer_failure_returns_error_and_rolls_back.
