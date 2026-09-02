(** * Tagged normalization frames over one explicit worklist

    The generated normalizer historically gives every constructor its own
    assembly-task variant.  The compact machine retains typed visit tasks and
    represents ordinary assembly by one checked tag containing the category,
    constructor, destination slot, and exact value-buffer range.  Beta,
    multi-beta, cancellation, native-fold, and owned-source revisit steps are
    classified separately: factoring ordinary construction cannot turn one of
    those semantic transitions into a constructor assembly.

    This model proves representation equivalence independently of a concrete
    generated language.  The Rust generator reflects the finite constructor
    census and supplies the same visit, ordinary-assembly, and special-step
    functions to both representations.  All pending work remains a list (the
    model of the heap-backed Rust [Vec]); no native call-stack recursion is
    introduced by the factoring. *)

From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.
Set Implicit Arguments.

Module TaggedNormalizationMachine.

  Inductive SpecialKind : Type :=
  | Beta
  | MultiBeta
  | Cancellation
  | NativeFold
  | OwnedSourceRevisit.

  Record AssemblyTag (Category Constructor : Type) : Type := assembly_tag {
    tag_category : Category;
    tag_constructor : Constructor
  }.

  Record Frame : Type := frame {
    (** Abstract identity of the already-live typed source node.  Rust keeps
        this as the existing category-typed raw pointer; the refactor neither
        erases nor extends its lifetime. *)
    frame_source_id : nat;
    frame_result_slot : nat;
    frame_value_base : nat;
    frame_value_count : nat
  }.

  Definition frame_in_bounds {Value : Type}
      (frm : Frame) (values : list Value) : Prop :=
    frame_value_base frm + frame_value_count frm <= length values.

  Definition frame_values {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    firstn (frame_value_count frm)
      (skipn (frame_value_base frm) values).

  Theorem frame_values_have_exact_length :
    forall (Value : Type) (frm : Frame) (values : list Value),
      frame_in_bounds frm values ->
      length (frame_values frm values) = frame_value_count frm.
  Proof.
    intros Value [source_id result_slot value_base value_count] values Hbounds.
    unfold frame_values, frame_in_bounds in *. cbn in *.
    rewrite length_firstn, length_skipn. lia.
  Qed.

  Definition frame_prefix {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    firstn (frame_value_base frm) values.

  Definition frame_suffix {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    skipn (frame_value_base frm + frame_value_count frm) values.

  Theorem frame_partition_recombines :
    forall (Value : Type) (frm : Frame) (values : list Value),
      frame_in_bounds frm values ->
      values =
        frame_prefix frm values ++ frame_values frm values ++
          frame_suffix frm values.
  Proof.
    intros Value [source_id result_slot value_base value_count] values Hbounds.
    unfold frame_prefix, frame_values, frame_suffix, frame_in_bounds in *.
    cbn in *.
    rewrite <- (firstn_skipn value_base values) at 1.
    f_equal.
    rewrite <- (firstn_skipn value_count (skipn value_base values)) at 1.
    f_equal.
    rewrite skipn_skipn. f_equal. lia.
  Qed.

  Section Tasks.
    Context {Category Constructor Visit Value Source : Type}.

    Inductive OldTask : Type :=
    | OldVisit : Visit -> OldTask
    | OldConstructorAssembly : Category -> Constructor -> Frame -> OldTask
    | OldSpecial : SpecialKind -> Category -> Constructor -> Frame -> OldTask.

    Inductive NewTask : Type :=
    | NewVisit : Visit -> NewTask
    | NewTaggedAssembly : AssemblyTag Category Constructor -> Frame -> NewTask
    | NewSpecial : SpecialKind -> Category -> Constructor -> Frame -> NewTask.

    Definition encode_task (task : OldTask) : NewTask :=
      match task with
      | OldVisit visit => NewVisit visit
      | OldConstructorAssembly category constructor frm =>
          NewTaggedAssembly (assembly_tag category constructor) frm
      | OldSpecial kind category constructor frm =>
          NewSpecial kind category constructor frm
      end.

    Definition decode_task (task : NewTask) : OldTask :=
      match task with
      | NewVisit visit => OldVisit visit
      | NewTaggedAssembly tag frm =>
          OldConstructorAssembly
            (tag_category tag) (tag_constructor tag) frm
      | NewSpecial kind category constructor frm =>
          OldSpecial kind category constructor frm
      end.

    Theorem decode_encode_task : forall task,
        decode_task (encode_task task) = task.
    Proof.
      intros task. destruct task; reflexivity.
    Qed.

    Theorem encode_decode_task : forall task,
        encode_task (decode_task task) = task.
    Proof.
      intros task.
      destruct task as [visit | [category constructor] frm |
        kind category constructor frm]; reflexivity.
    Qed.

    Inductive TaskClass : Type :=
    | VisitClass
    | OrdinaryClass
    | SpecialClass : SpecialKind -> TaskClass.

    Definition old_task_class (task : OldTask) : TaskClass :=
      match task with
      | OldVisit _ => VisitClass
      | OldConstructorAssembly _ _ _ => OrdinaryClass
      | OldSpecial kind _ _ _ => SpecialClass kind
      end.

    Definition new_task_class (task : NewTask) : TaskClass :=
      match task with
      | NewVisit _ => VisitClass
      | NewTaggedAssembly _ _ => OrdinaryClass
      | NewSpecial kind _ _ _ => SpecialClass kind
      end.

    Theorem task_class_preserved : forall task,
        new_task_class (encode_task task) = old_task_class task.
    Proof.
      intros task. destruct task; reflexivity.
    Qed.

    Theorem ordinary_never_becomes_special :
      forall category constructor frm kind,
        new_task_class
          (encode_task (OldConstructorAssembly category constructor frm)) <>
        SpecialClass kind.
    Proof.
      intros. discriminate.
    Qed.

    Record OldState : Type := old_state {
      old_tasks : list OldTask;
      old_values : list Value;
      old_sources : list Source
    }.

    Record NewState : Type := new_state {
      new_tasks : list NewTask;
      new_values : list Value;
      new_sources : list Source
    }.

    Definition encode_state (state : OldState) : NewState :=
      new_state
        (map encode_task (old_tasks state))
        (old_values state)
        (old_sources state).

    Variable visit_plan : Visit -> list OldTask.
    Variable ordinary_assembly :
      Category -> Constructor -> Frame -> list Value -> option (list Value).
    Variable special_transition :
      SpecialKind -> Category -> Constructor -> Frame ->
      list Value -> list Source -> option (list OldTask * list Value * list Source).

    Definition old_step (state : OldState) : option OldState :=
      match old_tasks state with
      | [] => None
      | task :: rest =>
          match task with
          | OldVisit visit =>
              Some (old_state
                (visit_plan visit ++ rest)
                (old_values state)
                (old_sources state))
          | OldConstructorAssembly category constructor frm =>
              match ordinary_assembly
                category constructor frm (old_values state) with
              | Some values => Some (old_state rest values (old_sources state))
              | None => None
              end
          | OldSpecial kind category constructor frm =>
              match special_transition kind category constructor frm
                (old_values state) (old_sources state) with
              | Some (planned, values, sources) =>
                  Some (old_state (planned ++ rest) values sources)
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
              Some (new_state
                (map encode_task (visit_plan visit) ++ rest)
                (new_values state)
                (new_sources state))
          | NewTaggedAssembly tag frm =>
              match ordinary_assembly
                (tag_category tag) (tag_constructor tag) frm
                (new_values state) with
              | Some values => Some (new_state rest values (new_sources state))
              | None => None
              end
          | NewSpecial kind category constructor frm =>
              match special_transition kind category constructor frm
                (new_values state) (new_sources state) with
              | Some (planned, values, sources) =>
                  Some (new_state
                    (map encode_task planned ++ rest) values sources)
              | None => None
              end
          end
      end.

    Theorem one_step_preserved : forall state,
        new_step (encode_state state) = option_map encode_state (old_step state).
    Proof.
      intros [tasks values sources]. destruct tasks as [|task rest].
      - reflexivity.
      - destruct task as [visit | category constructor frm |
          kind category constructor frm].
        + unfold new_step, old_step, encode_state. cbn. now rewrite map_app.
        + unfold new_step, old_step, encode_state. cbn.
          destruct (ordinary_assembly category constructor frm values);
            reflexivity.
        + unfold new_step, old_step, encode_state. cbn.
          destruct (special_transition kind category constructor frm values sources)
            as [[[planned next_values] next_sources] |] eqn:Hspecial;
            cbn; [now rewrite map_app | reflexivity].
    Qed.

    Theorem failure_preserved : forall state,
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

    Theorem finite_run_preserved : forall fuel state,
        new_run fuel (encode_state state) =
        option_map encode_state (old_run fuel state).
    Proof.
      induction fuel as [|fuel IH]; intros [tasks values sources];
        [reflexivity |].
      destruct tasks as [|task rest]; [reflexivity |].
      cbn [new_run old_run encode_state].
      rewrite one_step_preserved.
      destruct (old_step (old_state (task :: rest) values sources)) as [next |];
        [apply IH | reflexivity].
    Qed.

    Theorem successful_results_and_sources_preserved :
      forall fuel state final_state,
        old_run fuel state = Some final_state ->
        exists compact_final,
          new_run fuel (encode_state state) = Some compact_final /\
          new_values compact_final = old_values final_state /\
          new_sources compact_final = old_sources final_state.
    Proof.
      intros fuel state final_state Hrun.
      exists (encode_state final_state). split.
      - now rewrite finite_run_preserved, Hrun.
      - now split.
    Qed.

  End Tasks.

  Print Assumptions frame_values_have_exact_length.
  Print Assumptions frame_partition_recombines.
  Print Assumptions decode_encode_task.
  Print Assumptions encode_decode_task.
  Print Assumptions task_class_preserved.
  Print Assumptions ordinary_never_becomes_special.
  Print Assumptions one_step_preserved.
  Print Assumptions failure_preserved.
  Print Assumptions finite_run_preserved.
  Print Assumptions successful_results_and_sources_preserved.

End TaggedNormalizationMachine.
