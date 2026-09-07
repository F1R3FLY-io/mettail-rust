(** * Borrowed node traversal refines the existing occurrence machine

    A reference may include an expected sort as well as a source coordinate.
    [lookup] is an immutable, checked local observation: a native leaf, an
    exact constructor with ordered typed child references, or refusal.  Its
    concrete Par/kernel framing and authority obligations are not assumed
    solved by this generic traversal theorem.

    [Unfolds] is finite proof data describing each occurrence, not a runtime
    allocation.  Sharing a reference never erases its repeated child slots.
    Work items retain borrowed references and constructor instructions only;
    every source visit performs one local lookup.  No whole instruction
    program or intermediate occurrence tree is built by [run_borrowed].

    The theorem is a forward refinement for sources with a finite unfolding.
    Source admission must establish that premise.  A missing view is refused,
    control exhaustion stays distinct, and neither a cyclic source nor a
    malformed source is claimed to have an unfolding merely from its type.
    Ancestor-cycle filtering and arena realization are separate obligations. *)

From Stdlib Require Import List Arith Lia.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
From RuntimeGrammar Require Import FusedOccurrenceExecution.
Import ListNotations.
Set Implicit Arguments.

Module BorrowedOccurrenceExecution.
Module Fused := FusedOccurrenceExecution.FusedOccurrenceExecution.

Section BorrowedTraversal.
Context {Reference Value Label : Type}.

Inductive Node :=
| NativeNode (value : Value)
| ConstructorNode (label : Label) (children : list Reference).

Variable lookup : Reference -> option Node.
Variable assemble : Label -> list Value -> option Value.

Inductive Unfolds : Reference -> @selected_tree Value Label -> Prop :=
| UnfoldNative : forall reference value,
    lookup reference = Some (NativeNode value) ->
    Unfolds reference (SelectedLeaf value)
| UnfoldConstructor : forall reference label children occurrences,
    lookup reference = Some (ConstructorNode label children) ->
    UnfoldChildren children occurrences ->
    Unfolds reference (SelectedBranch label occurrences)
with UnfoldChildren : list Reference -> @selected_children Value Label -> Prop :=
| UnfoldNoChildren : UnfoldChildren [] NoChildren
| UnfoldMoreChildren : forall reference references occurrence occurrences,
    Unfolds reference occurrence ->
    UnfoldChildren references occurrences ->
    UnfoldChildren (reference :: references) (MoreChildren occurrence occurrences).

Scheme unfolds_mut := Induction for Unfolds Sort Prop
  with unfold_children_mut := Induction for UnfoldChildren Sort Prop.
Combined Scheme unfold_mutual from unfolds_mut, unfold_children_mut.

Lemma unfolding_preserves_every_child_slot : forall references occurrences,
  UnfoldChildren references occurrences -> length references = child_count occurrences.
Proof.
  intros references occurrences H. induction H; cbn; congruence.
Qed.

Theorem deterministic_lookup_has_unique_finite_unfolding :
  (forall reference occurrence, Unfolds reference occurrence ->
    forall other, Unfolds reference other -> occurrence = other) /\
  (forall references occurrences, UnfoldChildren references occurrences ->
    forall other, UnfoldChildren references other -> occurrences = other).
Proof.
  apply unfold_mutual.
  - intros reference value Hlookup other Hother.
    inversion Hother as [reference' value' Hlookup'|
      reference' label children occurrences Hlookup' Hchildren]; subst;
      rewrite Hlookup in Hlookup'; inversion Hlookup'; reflexivity.
  - intros reference label children occurrences Hlookup Hchildren IH other Hother.
    inversion Hother as [reference' value' Hlookup'|
      reference' label' children' occurrences' Hlookup' Hchildren']; subst;
      rewrite Hlookup in Hlookup'; inversion Hlookup'; subst.
    f_equal. now apply IH.
  - intros other Hother. inversion Hother. reflexivity.
  - intros reference references occurrence occurrences Hfirst IHfirst Hlater IHlater other Hother.
    inversion Hother as [|reference' references' occurrence' occurrences' Hfirst' Hlater']; subst.
    f_equal; [now apply IHfirst|now apply IHlater].
Qed.

Inductive Task :=
| VisitReference (reference : Reference)
| VisitReferences (references : list Reference)
| EmitInstruction (instruction : @instruction Value Label).

Definition advance_borrowed (work : list Task)
    : option (list Task * list (@instruction Value Label)) :=
  match work with
  | [] => None
  | VisitReference reference :: rest =>
      match lookup reference with
      | Some (NativeNode value) => Some (rest, [PushSelected value])
      | Some (ConstructorNode label children) =>
          Some (VisitReferences children ::
            EmitInstruction (AssembleSelected label (length children)) :: rest, [])
      | None => None
      end
  | VisitReferences [] :: rest => Some (rest, [])
  | VisitReferences (reference :: references) :: rest =>
      Some (VisitReference reference :: VisitReferences references :: rest, [])
  | EmitInstruction instruction :: rest => Some (rest, [instruction])
  end.

Inductive TaskCorresponds : Task -> @compile_task Value Label -> Prop :=
| VisitCorresponds : forall reference occurrence,
    Unfolds reference occurrence ->
    TaskCorresponds (VisitReference reference) (VisitTree occurrence)
| ChildrenCorrespond : forall references occurrences,
    UnfoldChildren references occurrences ->
    TaskCorresponds (VisitReferences references) (VisitChildren occurrences)
| InstructionCorresponds : forall instruction,
    TaskCorresponds (EmitInstruction instruction) (Emit instruction).

Definition WorkCorresponds := Forall2 TaskCorresponds.

Theorem borrowed_step_refines_occurrence_step : forall work witness,
  WorkCorresponds work witness -> work <> [] ->
  exists next next_witness emitted,
    advance_borrowed work = Some (next, emitted) /\
    advance_compiler witness [] = Some (next_witness, emitted) /\
    WorkCorresponds next next_witness.
Proof.
  intros work witness Hwork Hnonempty.
  inversion Hwork as [|task witness_task rest witness_rest Htask Hrest]; subst;
    [contradiction|].
  inversion Htask as [reference occurrence Hunfold|references occurrences Hunfold|instruction]; subst.
  - inversion Hunfold as [reference' value Hlookup|
      reference' label children occurrences Hlookup Hchildren]; subst.
    + exists rest, witness_rest, [PushSelected value].
      split; [cbn [advance_borrowed]; now rewrite Hlookup|].
      split; [reflexivity|exact Hrest].
    + exists (VisitReferences children ::
        EmitInstruction (AssembleSelected label (length children)) :: rest),
        (VisitChildren occurrences ::
        Emit (AssembleSelected label (child_count occurrences)) :: witness_rest), [].
      split; [cbn [advance_borrowed]; now rewrite Hlookup|].
      split; [reflexivity|].
      constructor; [now constructor|].
      constructor; [|exact Hrest].
      rewrite (unfolding_preserves_every_child_slot Hchildren). constructor.
  - inversion Hunfold as [|reference references' occurrence occurrences' Hfirst Hlater]; subst.
    + exists rest, witness_rest, []. repeat split; try reflexivity. exact Hrest.
    + exists (VisitReference reference :: VisitReferences references' :: rest),
        (VisitTree occurrence :: VisitChildren occurrences' :: witness_rest), [].
      repeat split; try reflexivity.
      constructor; [now constructor|]. constructor; [now constructor|exact Hrest].
  - exists rest, witness_rest, [instruction]. repeat split; try reflexivity. exact Hrest.
Qed.

Fixpoint run_borrowed (fuel : nat) (work : list Task) (values : list Value)
    : @Fused.Outcome Value :=
  match work with
  | [] => Fused.Completed values
  | _ => match fuel with
    | 0 => Fused.Exhausted
    | S later => match advance_borrowed work with
      | Some (next, emitted) =>
          match execute assemble (rev emitted) values with
          | Some next_values => run_borrowed later next next_values
          | None => Fused.Rejected
          end
      | None => Fused.Rejected
      end
    end
  end.

Theorem borrowed_run_refines_occurrence_run : forall fuel work witness values,
  WorkCorresponds work witness ->
  run_borrowed fuel work values = Fused.run_fused assemble fuel witness values.
Proof.
  induction fuel as [|fuel IH]; intros work witness values Hwork.
  - inversion Hwork; reflexivity.
  - destruct work as [|task rest].
    + inversion Hwork. reflexivity.
    + destruct (borrowed_step_refines_occurrence_step Hwork ltac:(discriminate))
        as [next [next_witness [emitted [Hstep [Hwitness Hnext]]]]].
      inversion Hwork as [|task' witness_task rest' witness_rest Htask Hrest]; subst.
      change (match advance_borrowed (task :: rest) with
        | Some (next, emitted) => match execute assemble (rev emitted) values with
          | Some next_values => run_borrowed fuel next next_values
          | None => Fused.Rejected end
        | None => Fused.Rejected end =
        match advance_compiler (witness_task :: witness_rest) [] with
        | Some (next, emitted) => match execute assemble (rev emitted) values with
          | Some next_values => Fused.run_fused assemble fuel next next_values
          | None => Fused.Rejected end
        | None => Fused.Rejected end).
      rewrite Hstep, Hwitness.
      destruct (execute assemble (rev emitted) values); [apply IH; exact Hnext|reflexivity].
Qed.

Corollary borrowed_root_preserves_exact_declarative_assembly :
  forall reference occurrence values,
  Unfolds reference occurrence ->
  run_borrowed (tree_work occurrence) [VisitReference reference] values =
    Fused.execution_outcome
      (option_map (fun value => value :: values) (denote_tree assemble occurrence)).
Proof.
  intros reference occurrence values H.
  assert (Hwork : WorkCorresponds [VisitReference reference] [VisitTree occurrence]).
  { constructor; [now constructor|constructor]. }
  rewrite (@borrowed_run_refines_occurrence_run (tree_work occurrence)
    [VisitReference reference] [VisitTree occurrence] values Hwork).
  apply Fused.fused_occurrence_preserves_declarative_assembly.
Qed.

End BorrowedTraversal.
End BorrowedOccurrenceExecution.

Print Assumptions BorrowedOccurrenceExecution.unfolding_preserves_every_child_slot.
Print Assumptions BorrowedOccurrenceExecution.deterministic_lookup_has_unique_finite_unfolding.
Print Assumptions BorrowedOccurrenceExecution.borrowed_step_refines_occurrence_step.
Print Assumptions BorrowedOccurrenceExecution.borrowed_run_refines_occurrence_run.
Print Assumptions BorrowedOccurrenceExecution.borrowed_root_preserves_exact_declarative_assembly.
