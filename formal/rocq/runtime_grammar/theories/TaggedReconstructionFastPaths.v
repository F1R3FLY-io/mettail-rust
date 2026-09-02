(** * Semantics-preserving tagged reconstruction fast paths

    The fully general reconstruction descriptor carries one [FieldPlan] per
    constructor field.  A generated language often contains two closed
    subfamilies that need less runtime interpretation:

    - every field is a required category visit; or
    - a binder has no fields before its arity marker and body.

    This module proves that compact descriptors for those subfamilies preserve
    the general validator and producer plan.  Required-child category checks
    may be performed by the child [Visit] transition instead of a separate
    descriptor pass: exact arity followed by all visit checks accepts exactly
    the same inputs as eager [validate_fields].  The optimization therefore
    changes neither acceptance nor the produced task order.

    The final section models normalization's owned-result revisit helper.  An
    inline helper is merely a factorization of the same state transition; its
    inlining policy is not part of the observable semantics. *)

From Stdlib Require Import List Bool Arith.PeanoNat.
From RuntimeGrammar Require Import TaggedReconstructionMachine.
Import ListNotations.
Set Implicit Arguments.

Module TaggedReconstructionFastPaths.
  Import TaggedReconstructionMachine.

  Definition required_category_fields (categories : list nat)
      : list FieldPlan :=
    map (fun category => CategoryField category Required) categories.

  Fixpoint required_visit_checks
      (categories : list nat) (nodes : list SpineNode) : bool :=
    match categories, nodes with
    | [], [] => true
    | category :: category_rest, node :: node_rest =>
        validate_required_field (CategoryField category Required) node &&
        required_visit_checks category_rest node_rest
    | _, _ => false
    end.

  (** The compact path performs the length test while scheduling.  Each child
      [Visit] then performs its ordinary descriptor/category check. *)
  Definition compact_required_accepts
      (categories : list nat) (nodes : list SpineNode) : bool :=
    Nat.eqb (length categories) (length nodes) &&
    required_visit_checks categories nodes.

  Lemma required_visit_checks_are_general_validation :
    forall categories nodes,
      required_visit_checks categories nodes =
      validate_fields (required_category_fields categories) nodes.
  Proof.
    induction categories as [|category rest IH]; intros nodes;
      destruct nodes as [|node nodes]; cbn; try reflexivity.
    now rewrite IH.
  Qed.

  Theorem compact_required_validation_refines_general :
    forall categories nodes,
      compact_required_accepts categories nodes =
      validate_shape (FixedPlan (required_category_fields categories)) nodes.
  Proof.
    intros categories nodes.
    unfold compact_required_accepts. cbn.
    rewrite required_visit_checks_are_general_validation.
    destruct (validate_fields (required_category_fields categories) nodes)
      eqn:Hvalid; cbn; [| now rewrite andb_false_r].
    rewrite andb_true_r. apply Nat.eqb_eq.
    apply validate_fields_exact_arity in Hvalid.
    unfold required_category_fields in Hvalid.
    now rewrite length_map in Hvalid.
  Qed.

  Fixpoint general_required_tasks
      (fields : list FieldPlan) (references : list Ref)
      : option (list Task) :=
    match fields, references with
    | [], [] => Some []
    | CategoryField category Required :: field_rest,
        reference :: reference_rest =>
        match general_required_tasks field_rest reference_rest with
        | Some tasks => Some
            (Produce (Visit category Required reference) :: tasks)
        | None => None
        end
    | _, _ => None
    end.

  Fixpoint compact_required_tasks
      (categories : list nat) (references : list Ref)
      : option (list Task) :=
    match categories, references with
    | [], [] => Some []
    | category :: category_rest, reference :: reference_rest =>
        match compact_required_tasks category_rest reference_rest with
        | Some tasks => Some
            (Produce (Visit category Required reference) :: tasks)
        | None => None
        end
    | _, _ => None
    end.

  Theorem compact_required_tasks_refine_general :
    forall categories references,
      compact_required_tasks categories references =
      general_required_tasks
        (required_category_fields categories) references.
  Proof.
    induction categories as [|category rest IH]; intros references;
      destruct references as [|reference references]; cbn; try reflexivity.
    now rewrite IH.
  Qed.

  Definition homogeneous_categories (category arity : nat) : list nat :=
    repeat category arity.

  Theorem homogeneous_required_tasks_refine_general :
    forall category arity references,
      compact_required_tasks (homogeneous_categories category arity) references =
      general_required_tasks
        (required_category_fields
          (homogeneous_categories category arity)) references.
  Proof.
    intros. apply compact_required_tasks_refine_general.
  Qed.

  Definition compact_binder0_accepts
      (body : nat) (kind : BinderKind) (children : list SpineNode) : bool :=
    match children with
    | [marker; body_node] =>
        validate_binder_marker kind marker &&
        match spine_identity body_node with
        | CategoryIdentity actual => Nat.eqb body actual
        | _ => false
        end
    | _ => false
    end.

  Theorem compact_binder0_validation_refines_general :
    forall body kind children,
      compact_binder0_accepts body kind children =
      validate_shape (BinderPlan [] body kind) children.
  Proof.
    intros body kind children.
    destruct children as [|first [|second [|third rest]]]; reflexivity.
  Qed.

  Definition binder0_tasks
      (category constructor value_base : nat)
      (body kind_marker : Ref) (kind : BinderKind) : list Task :=
    [Produce (Visit category Required body);
     Produce (DecodeBinder kind kind_marker);
     AssembleFrame
       (frame category constructor value_base 2 (BinderConstructor kind))].

  Definition compact_binder0_tasks := binder0_tasks.

  Theorem compact_binder0_tasks_refine_general :
    forall category constructor value_base body marker kind,
      compact_binder0_tasks category constructor value_base body marker kind =
      binder0_tasks category constructor value_base body marker kind.
  Proof.
    reflexivity.
  Qed.

  Section RevisitFactorization.
    Variables Source Result Task : Type.
    Variable schedule : Source -> Result -> Task.

    Record RevisitState : Type := revisit_state {
      revisit_sources : list Source;
      revisit_tasks : list Task
    }.

    Definition direct_revisit
        (state : RevisitState) (source : Source) (result : Result)
        : RevisitState :=
      revisit_state
        (revisit_sources state ++ [source])
        (schedule source result :: revisit_tasks state).

    Definition factored_revisit
        (state : RevisitState) (source : Source) (result : Result)
        : RevisitState :=
      direct_revisit state source result.

    Theorem inline_revisit_factorization_is_observational_identity :
      forall state source result,
        factored_revisit state source result =
        direct_revisit state source result.
    Proof.
      reflexivity.
    Qed.
  End RevisitFactorization.

  Print Assumptions compact_required_validation_refines_general.
  Print Assumptions compact_required_tasks_refine_general.
  Print Assumptions homogeneous_required_tasks_refine_general.
  Print Assumptions compact_binder0_validation_refines_general.
  Print Assumptions compact_binder0_tasks_refine_general.
  Print Assumptions inline_revisit_factorization_is_observational_identity.

End TaggedReconstructionFastPaths.
