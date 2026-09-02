(** * Factoring constructor-specific reconstruction assembly tasks

    The legacy generated reconstruction pushdown automaton (PDA) gives every
    invertible constructor its own task variant.  The factored machine carries
    the same category, constructor, and child-count information as data in one
    tagged assembly task.  Visit tasks and the value stack are unchanged.

    The dispatch table is abstract here: its result is the existing generated
    constructor body.  The proofs establish that task factoring changes only
    representation, including for failure and for every finite PDA run. *)

From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.

Module FactoredReconstructionAssembly.

  Section Machine.
    Context {Category Constructor Visit Value : Type}.

    Inductive OldTask : Type :=
    | OldVisit : Visit -> OldTask
    | OldAssemble : Category -> Constructor -> nat -> OldTask.

    Record AssemblyTag : Type := assembly_tag {
      tag_category : Category;
      tag_constructor : Constructor
    }.

    Inductive NewTask : Type :=
    | NewVisit : Visit -> NewTask
    | NewAssemble : AssemblyTag -> nat -> NewTask.

    Definition encode_task (task : OldTask) : NewTask :=
      match task with
      | OldVisit visit => NewVisit visit
      | OldAssemble category constructor child_count =>
          NewAssemble (assembly_tag category constructor) child_count
      end.

    Definition decode_task (task : NewTask) : OldTask :=
      match task with
      | NewVisit visit => OldVisit visit
      | NewAssemble tag child_count =>
          OldAssemble
            (tag_category tag) (tag_constructor tag) child_count
      end.

    Theorem decode_encode_task :
      forall task, decode_task (encode_task task) = task.
    Proof.
      intros task. destruct task; reflexivity.
    Qed.

    Theorem encode_decode_task :
      forall task, encode_task (decode_task task) = task.
    Proof.
      intros task. destruct task as [visit | [category constructor] child_count]; reflexivity.
    Qed.

    Record OldState : Type := old_state {
      old_tasks : list OldTask;
      old_values : list Value
    }.

    Record NewState : Type := new_state {
      new_tasks : list NewTask;
      new_values : list Value
    }.

    Definition encode_state (state : OldState) : NewState :=
      new_state (map encode_task (old_tasks state)) (old_values state).

    Variable visit_plan : Visit -> list OldTask.
    Variable assemble : Category -> Constructor -> nat -> list Value -> option (list Value).

    Definition old_step (state : OldState) : option OldState :=
      match old_tasks state with
      | [] => None
      | task :: rest =>
          match task with
          | OldVisit visit =>
              Some (old_state (visit_plan visit ++ rest) (old_values state))
          | OldAssemble category constructor child_count =>
              match assemble category constructor child_count (old_values state) with
              | Some values => Some (old_state rest values)
              | None => None
              end
          end
      end.

    Definition new_step (state : NewState) : option NewState :=
      match new_tasks state with
      | [] => None
      | task :: rest =>
          match task with
          | NewVisit visit =>
              Some (new_state (map encode_task (visit_plan visit) ++ rest) (new_values state))
          | NewAssemble tag child_count =>
              match assemble
                (tag_category tag) (tag_constructor tag) child_count (new_values state) with
              | Some values => Some (new_state rest values)
              | None => None
              end
          end
      end.

    Theorem one_step_preserved :
      forall state,
        new_step (encode_state state) = option_map encode_state (old_step state).
    Proof.
      intros [tasks values]. destruct tasks as [|task rest].
      - reflexivity.
      - destruct task as [visit | category constructor child_count].
        + unfold new_step, old_step, encode_state.
          simpl. now rewrite map_app.
        + unfold new_step, old_step, encode_state.
          simpl.
          destruct (assemble category constructor child_count values); reflexivity.
    Qed.

    Theorem failure_preserved :
      forall state,
        old_step state = None <-> new_step (encode_state state) = None.
    Proof.
      intro state. rewrite one_step_preserved.
      destruct (old_step state); split; intro H; try discriminate; reflexivity.
    Qed.

    Fixpoint old_run (fuel : nat) (state : OldState) : option OldState :=
      match fuel with
      | 0 => None
      | S remaining =>
          match old_tasks state with
          | [] => Some state
          | _ :: _ =>
              match old_step state with
              | Some next => old_run remaining next
              | None => None
              end
          end
      end.

    Fixpoint new_run (fuel : nat) (state : NewState) : option NewState :=
      match fuel with
      | 0 => None
      | S remaining =>
          match new_tasks state with
          | [] => Some state
          | _ :: _ =>
              match new_step state with
              | Some next => new_run remaining next
              | None => None
              end
          end
      end.

    Theorem finite_run_preserved :
      forall fuel state,
        new_run fuel (encode_state state) =
        option_map encode_state (old_run fuel state).
    Proof.
      induction fuel as [|fuel IH]; intros [tasks values]; [reflexivity|].
      destruct tasks as [|task rest]; [reflexivity|].
      cbn [new_run old_run encode_state].
      rewrite one_step_preserved.
      destruct (old_step (old_state (task :: rest) values)) as [next|];
        [apply IH | reflexivity].
    Qed.

    Theorem successful_value_stack_preserved :
      forall fuel state final_state,
        old_run fuel state = Some final_state ->
        exists compact_final,
          new_run fuel (encode_state state) = Some compact_final /\
          new_values compact_final = old_values final_state.
    Proof.
      intros fuel state final_state Hrun.
      exists (encode_state final_state).
      split.
      - rewrite finite_run_preserved, Hrun. reflexivity.
      - reflexivity.
    Qed.

  End Machine.

  Print Assumptions decode_encode_task.
  Print Assumptions encode_decode_task.
  Print Assumptions one_step_preserved.
  Print Assumptions failure_preserved.
  Print Assumptions finite_run_preserved.
  Print Assumptions successful_value_stack_preserved.

End FactoredReconstructionAssembly.
