(** * All-outcome transport of semantic execution work

    A caller suspends its counter while a bounded child executes with a fresh
    local counter. Returning the child counter is not optional on refutation:
    it is absorbed before the caller may inspect that outcome or continue.
    This finite pushdown transition system separates counter ownership from
    the semantic branch policy. It covers matching, judgment proof search and
    normalization without specifying a second evaluator.

    Each transition records only NEW accepted work. Enter, return, absorption,
    cancellation and diagnostic failure have zero additional work. The sum
    includes active and suspended counters, so it cannot lose a failed child
    or charge it twice. The trace theorem proves conservation for arbitrary
    finite nesting and all three semantic outcomes. It does not establish
    matcher correctness, callback honesty, physical memory/CPU bounds, or that
    every implementation operation has an appropriate logical charge.

    Naturals model checked machine arithmetic: successful additions must fit
    the supplied ceiling; a machine ceiling itself must fit its integer type.
    A pre-existing admission prefix larger than a new execution ceiling is a
    separate refusal, not a well-formed execution with erased prior usage. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From RuntimeGrammar Require Import InstalledFltJudgments InstalledFltUsage.
Import ListNotations.

Module SemanticWorkTransport.
Module Budget := InstalledFltJudgments.InstalledFltJudgments.
Module Usage := InstalledFltUsage.InstalledFltUsage.

Inductive Outcome := Proven | Refuted | Undetermined.
Inductive Phase := Running | Returned (result : Outcome).

Record Frame := frame { prefix : nat; parent_limit : nat }.
Record State := state {
  used : nat;
  allowance : nat;
  callers : list Frame;
  phase : Phase
}.

Fixpoint suspended (frames : list Frame) : nat :=
  match frames with
  | [] => 0
  | f :: rest => prefix f + suspended rest
  end.

Definition total (s : State) := used s + suspended (callers s).

Fixpoint stack_fits (limit : nat) (frames : list Frame) (root_limit : nat) : Prop :=
  match frames with
  | [] => limit = root_limit
  | f :: rest =>
      prefix f <= parent_limit f /\
      limit = parent_limit f - prefix f /\
      stack_fits (parent_limit f) rest root_limit
  end.

Definition bounded (root_limit : nat) (s : State) :=
  used s <= allowance s /\ stack_fits (allowance s) (callers s) root_limit.

Inductive step : State -> nat -> State -> Prop :=
| LocalCharge : forall work limit frames amount next,
    Budget.charge_work limit work amount = Some next ->
    step (state work limit frames Running) amount
         (state next limit frames Running)
| EnterChild : forall work limit frames,
    work <= limit ->
    step (state work limit frames Running) 0
         (state 0 (limit - work) (frame work limit :: frames) Running)
| ReturnLocal : forall work limit frames result,
    step (state work limit frames Running) 0
         (state work limit frames (Returned result))
| AbsorbChild : forall work limit saved frames result next,
    Budget.charge_work (parent_limit saved) (prefix saved) work = Some next ->
    step (state work limit (saved :: frames) (Returned result)) 0
         (state next (parent_limit saved) frames (Returned result))
| ContinueCaller : forall work limit frames result,
    step (state work limit frames (Returned result)) 0
         (state work limit frames Running)
| FailedCharge : forall work limit frames amount,
    Budget.charge_work limit work amount = None ->
    step (state work limit frames Running) 0
         (state work limit frames (Returned Undetermined))
| Cancel : forall work limit frames,
    step (state work limit frames Running) 0
         (state work limit frames (Returned Undetermined))
| DiagnosticFailure : forall work limit frames result,
    step (state work limit frames (Returned result)) 0
         (state work limit frames (Returned Undetermined)).

Theorem step_conserves_every_accepted_charge : forall before amount after,
  step before amount after -> total after = total before + amount.
Proof.
  intros before amount after H; destruct H; unfold total; cbn;
    try match goal with
    | Hcharge : Budget.charge_work _ _ _ = Some _ |- _ =>
        apply Budget.successful_charge_preserves_prefix_and_ceiling in Hcharge
    end; lia.
Qed.

Theorem step_preserves_nested_ceilings : forall root before amount after,
  step before amount after -> bounded root before -> bounded root after.
Proof.
  intros root before amount after H; destruct H;
    unfold bounded; cbn; intros [Hused Hstack];
    try match goal with
    | Hcharge : Budget.charge_work _ _ _ = Some _ |- _ =>
        apply Budget.successful_charge_preserves_prefix_and_ceiling in Hcharge
    end; intuition lia.
Qed.

Lemma stack_bounds_total : forall frames limit root work,
  stack_fits limit frames root -> work <= limit ->
  work + suspended frames <= root.
Proof.
  induction frames as [|[saved parent] rest IH]; cbn.
  - intros; lia.
  - intros limit root work [Hsaved [Hlimit Hrest]] Hwork.
    specialize (IH parent root (saved + work) Hrest ltac:(lia)). lia.
Qed.

Theorem bounded_state_bounds_aggregate : forall root s,
  bounded root s -> total s <= root.
Proof.
  intros root [work limit frames current] [Hwork Hstack].
  exact (stack_bounds_total frames limit root work Hstack Hwork).
Qed.

Inductive trace : State -> list nat -> State -> Prop :=
| TraceEmpty : forall s, trace s [] s
| TraceStep : forall start amount middle charges finish,
    step start amount middle -> trace middle charges finish ->
    trace start (amount :: charges) finish.

Definition accepted_work := fold_right Nat.add 0.

Theorem trace_conserves_all_outcomes : forall start charges finish,
  trace start charges finish ->
  total finish = total start + accepted_work charges.
Proof.
  intros start charges finish H; induction H;
    unfold accepted_work in *; cbn [fold_right] in *.
  - lia.
  - pose proof (step_conserves_every_accepted_charge _ _ _ H). lia.
Qed.

Theorem trace_preserves_nested_ceilings : forall start charges finish,
  trace start charges finish -> forall root,
  bounded root start -> bounded root finish.
Proof.
  intros start charges finish H; induction H; intros root Hbound.
  - exact Hbound.
  - apply IHtrace. eapply step_preserves_nested_ceilings; eauto.
Qed.

Theorem terminal_report_includes_admission_and_every_child :
  forall ceiling admission charges aggregate result,
    admission <= ceiling ->
    trace (state admission ceiling [] Running) charges
          (state aggregate ceiling [] (Returned result)) ->
    aggregate = admission + accepted_work charges /\ aggregate <= ceiling.
Proof.
  intros ceiling admission charges aggregate result Hadmit Htrace.
  pose proof (trace_conserves_all_outcomes _ _ _ Htrace) as Hsum.
  assert (Hinitial : bounded ceiling (state admission ceiling [] Running))
    by (split; cbn; auto).
  pose proof (trace_preserves_nested_ceilings _ _ _ Htrace _ Hinitial) as Hfinal.
  apply bounded_state_bounds_aggregate in Hfinal.
  unfold total in *; cbn in *; lia.
Qed.

(** A negative child followed by another candidate uses the SAME transfer as
    a successful child. No branch outcome controls whether the charge occurs.
    This also covers a successful scan followed by a later evidence failure. *)
Theorem all_child_outcomes_are_absorbed_before_continuation :
  forall parent saved child frames result,
    saved + child <= parent ->
    trace (state child (parent - saved) (frame saved parent :: frames)
                 (Returned result)) [0; 0]
          (state (saved + child) parent frames Running).
Proof.
  intros. eapply TraceStep.
  - apply AbsorbChild. unfold Budget.charge_work; cbn.
    rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
  - eapply TraceStep; [apply ContinueCaller | apply TraceEmpty].
Qed.

Theorem later_diagnostic_failure_retains_absorbed_work :
  forall parent saved child frames result,
    saved + child <= parent ->
    trace (state child (parent - saved) (frame saved parent :: frames)
                 (Returned result)) [0; 0]
          (state (saved + child) parent frames (Returned Undetermined)).
Proof.
  intros. eapply TraceStep.
  - apply AbsorbChild. unfold Budget.charge_work; cbn.
    rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
  - eapply TraceStep; [apply DiagnosticFailure | apply TraceEmpty].
Qed.

(** An already-spent admission prefix is retained even when a caller supplies
    a smaller execution ceiling. No new work occurs. The legacy decision may
    embed zero for this preflight refusal; the separate aggregate remains A. *)
Definition admission_preflight ceiling admission : option (Outcome * nat) :=
  if Nat.leb admission ceiling then None else Some (Undetermined, admission).

Theorem overdraw_refuses_without_erasing_prior_usage : forall ceiling admission,
  ceiling < admission ->
  admission_preflight ceiling admission = Some (Undetermined, admission).
Proof.
  intros. unfold admission_preflight.
  rewrite (proj2 (Nat.leb_gt _ _) H). reflexivity.
Qed.

Theorem service_absorbs_the_execution_increment_once :
  forall ceiling conversion admission aggregate next,
    Usage.absorb_kernel ceiling (conversion + admission) admission aggregate = Some next ->
    admission <= aggregate /\ next = conversion + aggregate /\ next <= ceiling.
Proof. exact Usage.execution_aggregate_is_charged_exactly_once. Qed.

End SemanticWorkTransport.

Print Assumptions SemanticWorkTransport.step_conserves_every_accepted_charge.
Print Assumptions SemanticWorkTransport.step_preserves_nested_ceilings.
Print Assumptions SemanticWorkTransport.bounded_state_bounds_aggregate.
Print Assumptions SemanticWorkTransport.trace_conserves_all_outcomes.
Print Assumptions SemanticWorkTransport.trace_preserves_nested_ceilings.
Print Assumptions SemanticWorkTransport.terminal_report_includes_admission_and_every_child.
Print Assumptions SemanticWorkTransport.all_child_outcomes_are_absorbed_before_continuation.
Print Assumptions SemanticWorkTransport.later_diagnostic_failure_retains_absorbed_work.
Print Assumptions SemanticWorkTransport.overdraw_refuses_without_erasing_prior_usage.
Print Assumptions SemanticWorkTransport.service_absorbs_the_execution_increment_once.
