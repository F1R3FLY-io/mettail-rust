From Stdlib Require Import List PeanoNat.
Import ListNotations.

Section Saturation.

Variable successors : nat -> list nat.
Variable seeds : list nat.

Inductive Reachable : nat -> Prop :=
| ReachSeed : forall state, In state seeds -> Reachable state
| ReachStep : forall source target,
    Reachable source ->
    In target (successors source) ->
    Reachable target.

Record Configuration : Type := {
  seen : list nat;
  pending : list nat
}.

Definition sound_configuration (configuration : Configuration) : Prop :=
  (forall state, In state (seen configuration) -> Reachable state) /\
  (forall state, In state (pending configuration) -> Reachable state).

Definition closed (states : list nat) : Prop :=
  forall source target,
    In source states ->
    In target (successors source) ->
    In target states.

Definition seeded (states : list nat) : Prop :=
  forall state, In state seeds -> In state states.

Inductive work_step : Configuration -> Configuration -> Prop :=
| ProcessPending : forall processed rest already fresh,
    Forall (fun state => In state (successors processed)) fresh ->
    work_step
      {| seen := already; pending := processed :: rest |}
      {| seen := processed :: already; pending := rest ++ fresh |}.

Theorem initial_configuration_sound :
  sound_configuration {| seen := []; pending := seeds |}.
Proof.
  split.
  - intros state Hin. contradiction.
  - intros state Hin. constructor. exact Hin.
Qed.

Theorem work_step_preserves_soundness :
  forall before after,
    sound_configuration before ->
    work_step before after ->
    sound_configuration after.
Proof.
  intros before after Hsound Hstep. destruct Hstep.
  destruct Hsound as [Hseen Hpending]. split.
  - intros state [Heq | Hin].
    + subst state. apply Hpending. left. reflexivity.
    + apply Hseen. exact Hin.
  - intros state Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply Hpending. right. exact Hin.
    + rewrite Forall_forall in H. specialize (H state Hin).
      eapply ReachStep.
      * apply Hpending. left. reflexivity.
      * exact H.
Qed.

Theorem terminal_saturation_complete :
  forall states state,
    seeded states ->
    closed states ->
    Reachable state ->
    In state states.
Proof.
  intros states state Hseed Hclosed Hreachable.
  induction Hreachable.
  - apply Hseed. exact H.
  - eapply Hclosed; eassumption.
Qed.

Theorem terminal_saturation_exact :
  forall configuration,
    sound_configuration configuration ->
    pending configuration = [] ->
    seeded (seen configuration) ->
    closed (seen configuration) ->
    forall state, In state (seen configuration) <-> Reachable state.
Proof.
  intros configuration Hsound Hterminal Hseed Hclosed state. split.
  - apply (proj1 Hsound).
  - apply terminal_saturation_complete; assumption.
Qed.

Theorem work_step_processes_one_new_descriptor :
  forall before after,
    work_step before after ->
    NoDup (seen before ++ pending before) ->
    length (seen after) = S (length (seen before)).
Proof.
  intros before after Hstep Hunique. destruct Hstep. simpl. reflexivity.
Qed.

Theorem finite_descriptor_bound :
  forall universe configuration,
    NoDup (seen configuration) ->
    (forall state, In state (seen configuration) -> In state universe) ->
    length (seen configuration) <= length universe.
Proof.
  intros universe configuration Hnodup Hincluded.
  apply NoDup_incl_length; [exact Hnodup |]. unfold incl. exact Hincluded.
Qed.

Print Assumptions work_step_preserves_soundness.
Print Assumptions terminal_saturation_exact.
Print Assumptions finite_descriptor_bound.

End Saturation.
