(** * Checked tagged dispatch for generated reconstruction

    A typed semantic backend must eventually rebuild a language-specific
    constructor, but it does not need one generated inverse-visitor arm for
    every constructor.  The irreducible boundary is the constructor assembly
    operation.  Child scheduling is determined entirely by a checked flat
    table whose key is the pair (category, constructor) and whose payload is
    the ordered list of child categories.

    This module proves the table-driven scheduling step equal to the original
    constructor-local scheduling step.  A well-formed table has unique keys;
    lookup therefore cannot use first-arm-wins behavior to hide a conflict.
    Arity mismatches fail before any assembly task is published.  Pending work
    is an explicit list: one transition consumes at most one source node, and
    a successful visit adds exactly one task per child plus one assembly task.

    In the Rust implementation the pending list is a pooled vector used as a
    last-in, first-out stack.  Pushing the assembly task first and the child
    visits in reverse order is the vector representation of the list plan
    defined here. *)

From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
Set Implicit Arguments.

Module TaggedReconstructionDispatch.

  Record ConstructorLayout : Type := constructor_layout {
    layout_category : nat;
    layout_constructor : nat;
    layout_child_categories : list nat
  }.

  Definition layout_key (layout : ConstructorLayout) : nat * nat :=
    (layout_category layout, layout_constructor layout).

  Definition layout_matches
      (category constructor : nat) (layout : ConstructorLayout) : bool :=
    Nat.eqb category (layout_category layout) &&
    Nat.eqb constructor (layout_constructor layout).

  Definition ValidLayoutTable (table : list ConstructorLayout) : Prop :=
    NoDup (map layout_key table).

  Fixpoint lookup_layout
      (category constructor : nat) (table : list ConstructorLayout)
      : option ConstructorLayout :=
    match table with
    | [] => None
    | layout :: rest =>
        if layout_matches category constructor layout
        then Some layout
        else lookup_layout category constructor rest
    end.

  Lemma layout_matches_refl : forall layout,
      layout_matches
        (layout_category layout) (layout_constructor layout) layout = true.
  Proof.
    intros []. unfold layout_matches. cbn.
    apply andb_true_iff. split; apply Nat.eqb_refl.
  Qed.

  Lemma layout_matches_equalities :
    forall category constructor layout,
      layout_matches category constructor layout = true ->
      category = layout_category layout /\
      constructor = layout_constructor layout.
  Proof.
    intros category constructor layout Hmatches.
    unfold layout_matches in Hmatches.
    apply andb_true_iff in Hmatches as [Hcategory Hconstructor].
    now rewrite Nat.eqb_eq in Hcategory, Hconstructor.
  Qed.

  Lemma lookup_layout_sound :
    forall table category constructor layout,
      lookup_layout category constructor table = Some layout ->
      In layout table /\
      layout_category layout = category /\
      layout_constructor layout = constructor.
  Proof.
    intros table. induction table as [|head rest IH];
      intros category constructor layout Hlookup; cbn in Hlookup;
      [discriminate |].
    destruct (layout_matches category constructor head) eqn:Hmatches.
    - inversion Hlookup; subst head.
      apply layout_matches_equalities in Hmatches as [Hcategory Hconstructor].
      split; [now left |].
      split; symmetry; assumption.
    - apply IH in Hlookup as [Hin [Hcategory Hconstructor]].
      split; [now right |].
      now split.
  Qed.

  Lemma lookup_layout_complete :
    forall table layout,
      ValidLayoutTable table ->
      In layout table ->
      lookup_layout
        (layout_category layout) (layout_constructor layout) table = Some layout.
  Proof.
    intros table. induction table as [|head rest IH];
      intros layout Hvalid Hin; [inversion Hin |].
    inversion Hvalid as [|head_key rest_keys Hfresh Hrest]; subst.
    destruct Hin as [Hequal | Hin].
    - subst head. cbn. now rewrite layout_matches_refl.
    - cbn.
      destruct (layout_matches
        (layout_category layout) (layout_constructor layout) head)
        eqn:Hmatches.
      + apply layout_matches_equalities in Hmatches as [Hcategory Hconstructor].
        exfalso. apply Hfresh.
        assert (Hkey : layout_key head = layout_key layout).
        { unfold layout_key. cbn. now rewrite <- Hcategory, <- Hconstructor. }
        rewrite Hkey. now apply in_map.
      + now apply IH.
  Qed.

  Inductive RebuildTask : Type :=
  | VisitChild : nat -> nat -> RebuildTask
  | AssembleConstructor : nat -> nat -> nat -> RebuildTask.

  Fixpoint child_visit_tasks
      (categories references : list nat) : option (list RebuildTask) :=
    match categories, references with
    | [], [] => Some []
    | category :: category_rest, reference :: reference_rest =>
        option_map (cons (VisitChild category reference))
          (child_visit_tasks category_rest reference_rest)
    | _, _ => None
    end.

  Definition constructor_visit_plan
      (layout : ConstructorLayout) (references : list nat)
      : option (list RebuildTask) :=
    match child_visit_tasks (layout_child_categories layout) references with
    | Some visits =>
        Some (visits ++
          [AssembleConstructor
            (layout_category layout)
            (layout_constructor layout)
            (length references)])
    | None => None
    end.

  Definition table_visit_plan
      (table : list ConstructorLayout)
      (category constructor : nat) (references : list nat)
      : option (list RebuildTask) :=
    match lookup_layout category constructor table with
    | Some layout => constructor_visit_plan layout references
    | None => None
    end.

  Theorem checked_table_visit_preserves_constructor_plan :
    forall table layout references,
      ValidLayoutTable table ->
      In layout table ->
      table_visit_plan table
        (layout_category layout) (layout_constructor layout) references =
      constructor_visit_plan layout references.
  Proof.
    intros table layout references Hvalid Hin.
    unfold table_visit_plan.
    now rewrite lookup_layout_complete.
  Qed.

  Lemma child_visit_tasks_rejects_arity_mismatch :
    forall categories references,
      length categories <> length references ->
      child_visit_tasks categories references = None.
  Proof.
    intros categories. induction categories as [|category category_rest IH];
      intros references Hlength; destruct references as [|reference reference_rest];
      cbn in *; try contradiction; try reflexivity.
    rewrite IH; [reflexivity | lia].
  Qed.

  Theorem table_visit_rejects_arity_mismatch :
    forall table category constructor layout references,
      lookup_layout category constructor table = Some layout ->
      length (layout_child_categories layout) <> length references ->
      table_visit_plan table category constructor references = None.
  Proof.
    intros table category constructor layout references Hlookup Hlength.
    unfold table_visit_plan. rewrite Hlookup.
    unfold constructor_visit_plan.
    now rewrite child_visit_tasks_rejects_arity_mismatch.
  Qed.

  Lemma child_visit_tasks_length :
    forall categories references tasks,
      child_visit_tasks categories references = Some tasks ->
      length tasks = length references.
  Proof.
    intros categories. induction categories as [|category category_rest IH];
      intros references tasks Htasks; destruct references as [|reference reference_rest];
      cbn in Htasks; try discriminate.
    - inversion Htasks. reflexivity.
    - destruct (child_visit_tasks category_rest reference_rest)
        as [rest_tasks |] eqn:Hrest; try discriminate.
      inversion Htasks; subst. cbn. f_equal. now eapply IH.
  Qed.

  Theorem successful_visit_plan_has_exact_bounded_growth :
    forall layout references tasks,
      constructor_visit_plan layout references = Some tasks ->
      length tasks = S (length references).
  Proof.
    intros layout references tasks Hplan.
    unfold constructor_visit_plan in Hplan.
    destruct (child_visit_tasks (layout_child_categories layout) references)
      as [visits |] eqn:Hvisit; try discriminate.
    inversion Hplan; subst. rewrite length_app. cbn.
    rewrite (@child_visit_tasks_length
      (layout_child_categories layout) references visits Hvisit).
    lia.
  Qed.

  Definition transition_consumption (pending : list RebuildTask) : nat :=
    match pending with
    | VisitChild _ _ :: _ => 1
    | AssembleConstructor _ _ _ :: _ => 0
    | [] => 0
    end.

  Theorem table_transition_consumes_at_most_one_source_node :
    forall pending, transition_consumption pending <= 1.
  Proof.
    intros [|task rest]; [cbn; lia |].
    destruct task; cbn; lia.
  Qed.

  Print Assumptions lookup_layout_sound.
  Print Assumptions lookup_layout_complete.
  Print Assumptions checked_table_visit_preserves_constructor_plan.
  Print Assumptions table_visit_rejects_arity_mismatch.
  Print Assumptions successful_visit_plan_has_exact_bounded_growth.
  Print Assumptions table_transition_consumes_at_most_one_source_node.

End TaggedReconstructionDispatch.
