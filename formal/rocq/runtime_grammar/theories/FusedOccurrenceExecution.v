(** * Execute the existing occurrence compiler without storing its program

    [advance_compiler] already specifies a deterministic explicit work stack
    and emits at most one instruction per step.  Here that instruction is
    executed immediately against the value stack.  This is a scheduling
    refinement of the existing assembler, not a new semantic evaluator.

    The reference work items contain proof-only occurrence trees.  A borrowed
    implementation must separately show what each source coordinate denotes;
    it need not allocate those trees or an instruction program at runtime.

    Control fuel counts transitions of this machine, not bytes, allocations,
    semantic reductions or host funding.  Those resources need their own
    checked charges.  Exhausted is explicitly distinct from a failed partial
    constructor action, and cannot be interpreted as evidence of rejection. *)

From Stdlib Require Import List Arith Lia.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
Import ListNotations.
Set Implicit Arguments.

Module FusedOccurrenceExecution.

Section FusedExecution.
Context {Value Label : Type}.
Variable assemble : Label -> list Value -> option Value.

Inductive Outcome :=
| Completed (values : list Value)
| Rejected
| Exhausted.

Definition execution_outcome (result : option (list Value)) : Outcome :=
  match result with Some values => Completed values | None => Rejected end.

Fixpoint run_fused (fuel : nat) (work : list (@compile_task Value Label))
    (values : list Value) : Outcome :=
  match work with
  | [] => Completed values
  | _ => match fuel with
    | 0 => Exhausted
    | S later => match advance_compiler work [] with
      | Some (next, emitted) =>
          match execute assemble (rev emitted) values with
          | Some next_values => run_fused later next next_values
          | None => Rejected
          end
      | None => Rejected
      end
    end
  end.

Lemma each_transition_emits_at_most_one_instruction : forall work next emitted,
  @advance_compiler Value Label work [] = Some (next, emitted) -> length emitted <= 1.
Proof.
  intros [|task rest] next emitted H; [discriminate|].
  destruct task as [tree|children|op];
    [destruct tree|destruct children|]; inversion H; cbn; lia.
Qed.

Theorem sufficient_control_fuel_preserves_exact_execution : forall fuel work values,
  remaining_work work <= fuel ->
  run_fused fuel work values = execution_outcome (execute assemble (work_meaning work) values).
Proof.
  induction fuel as [|fuel IH]; intros work values Hbound.
  - destruct work as [|task rest]; [reflexivity|].
    pose proof (unfinished_compiler_has_positive_work (work := task :: rest)
      ltac:(discriminate)). lia.
  - destruct work as [|task rest]; [reflexivity|].
    destruct (unfinished_compiler_has_a_transition (work := task :: rest) []
      ltac:(discriminate)) as [next [emitted Hstep]].
    pose proof (@compiler_transition_refines_postorder Value Label
      (task :: rest) [] next emitted Hstep) as [Hmeaning Hless].
    cbn [rev app] in Hmeaning.
    change (match advance_compiler (task :: rest) [] with
      | Some (next, emitted) => match execute assemble (rev emitted) values with
        | Some next_values => run_fused fuel next next_values
        | None => Rejected end
      | None => Rejected end =
      execution_outcome (execute assemble (work_meaning (task :: rest)) values)).
    rewrite Hstep, <- Hmeaning, execute_append.
    destruct (execute assemble (rev emitted) values); [apply IH; lia|reflexivity].
Qed.

(** A completed or rejected run is sound at any fuel.  Sufficient fuel is
    needed for guaranteed termination, never as a premise for correctness of
    a result already returned by the machine. *)
Theorem terminated_execution_is_sound : forall fuel work values result,
  run_fused fuel work values = result -> result <> Exhausted ->
  result = execution_outcome (execute assemble (work_meaning work) values).
Proof.
  induction fuel as [|fuel IH]; intros work values result Hrun Hterminated.
  - destruct work as [|task rest].
    + cbn [run_fused] in Hrun. subst result. reflexivity.
    + cbn [run_fused] in Hrun. subst result. contradiction.
  - destruct work as [|task rest].
    + cbn [run_fused] in Hrun. subst result. reflexivity.
    + destruct (unfinished_compiler_has_a_transition (work := task :: rest) []
        ltac:(discriminate)) as [next [emitted Hstep]].
      pose proof (@compiler_transition_refines_postorder Value Label
        (task :: rest) [] next emitted Hstep) as [Hmeaning Hless].
      cbn [rev app] in Hmeaning.
      change (match advance_compiler (task :: rest) [] with
        | Some (next, emitted) => match execute assemble (rev emitted) values with
          | Some next_values => run_fused fuel next next_values
          | None => Rejected end
        | None => Rejected end = result) in Hrun.
      rewrite Hstep in Hrun. rewrite <- Hmeaning, execute_append.
      destruct (execute assemble (rev emitted) values) as [next_values|].
      * exact (IH next next_values result Hrun Hterminated).
      * cbn [execution_outcome]. symmetry. exact Hrun.
Qed.

Corollary completed_fused_run_has_exact_stack : forall fuel work values output,
  run_fused fuel work values = Completed output ->
  execute assemble (work_meaning work) values = Some output.
Proof.
  intros fuel work values output Hrun.
  pose proof (terminated_execution_is_sound fuel work values Hrun ltac:(discriminate)) as H.
  destruct (execute assemble (work_meaning work) values); inversion H; reflexivity.
Qed.

Corollary rejected_fused_run_has_a_real_assembly_failure : forall fuel work values,
  run_fused fuel work values = Rejected ->
  execute assemble (work_meaning work) values = None.
Proof.
  intros fuel work values Hrun.
  pose proof (terminated_execution_is_sound fuel work values Hrun ltac:(discriminate)) as H.
  destruct (execute assemble (work_meaning work) values); inversion H; reflexivity.
Qed.

Theorem fused_occurrence_preserves_declarative_assembly : forall tree values,
  run_fused (tree_work tree) [VisitTree tree] values =
    execution_outcome (option_map (fun value => value :: values) (denote_tree assemble tree)).
Proof.
  intros tree values. rewrite sufficient_control_fuel_preserves_exact_execution.
  - unfold work_meaning. cbn [flat_map task_meaning]. rewrite app_nil_r.
    rewrite (proj1 (compiled_occurrences_refine_declarative_assembly assemble)). reflexivity.
  - unfold remaining_work. cbn [fold_right task_work]. lia.
Qed.

Example zero_fuel_does_not_reject_a_valid_leaf : forall value,
  run_fused 0 [VisitTree (SelectedLeaf value)] [] = Exhausted /\
  run_fused 1 [VisitTree (SelectedLeaf value)] [] = Completed [value].
Proof. intro value. split; reflexivity. Qed.

End FusedExecution.
End FusedOccurrenceExecution.

Print Assumptions FusedOccurrenceExecution.each_transition_emits_at_most_one_instruction.
Print Assumptions FusedOccurrenceExecution.sufficient_control_fuel_preserves_exact_execution.
Print Assumptions FusedOccurrenceExecution.terminated_execution_is_sound.
Print Assumptions FusedOccurrenceExecution.completed_fused_run_has_exact_stack.
Print Assumptions FusedOccurrenceExecution.rejected_fused_run_has_a_real_assembly_failure.
Print Assumptions FusedOccurrenceExecution.fused_occurrence_preserves_declarative_assembly.
