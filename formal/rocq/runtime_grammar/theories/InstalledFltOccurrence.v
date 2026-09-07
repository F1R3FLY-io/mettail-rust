(** * Checked installed FLTs use the existing occurrence assembler

    A [CheckedOccurrence] is a proof-only witness: its leaves have passed the
    actual native codec and its branches carry the constructor selected by
    the exact installed binding, with children checked against that binding's
    ordered domain.  It is not an extra runtime syntax tree or evaluator.

    This module connects that witness to [InstalledFltTermCodec.project_tree]
    and instantiates [SelectedOccurrencePlan]'s existing postorder theorem
    with concrete semantic-node construction.  The assembler cannot supply
    an arbitrary value: it constructs exactly the given head and children.
    Successful projection always has such a witness, so the correspondence
    is not obtained by assuming a possibly empty class of checked inputs.

    Borrowed graph lookup, coordinate allocation, physical reflection and
    per-operation resource charging remain separate refinements. *)

From Stdlib Require Import List Strings.String.
From RuntimeGrammar Require Import InstalledFltHeadCodec InstalledFltTermCodec
  FusedOccurrenceExecution BorrowedOccurrenceExecution.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
Import ListNotations.

Module InstalledFltOccurrence.
Module Head := InstalledFltHeadCodec.InstalledFltHeadCodec.
Module Codec := InstalledFltTermCodec.InstalledFltTermCodec.
Module Fused := FusedOccurrenceExecution.FusedOccurrenceExecution.
Module Borrowed := BorrowedOccurrenceExecution.BorrowedOccurrenceExecution.

Fixpoint semantic_children (values : list Codec.SemanticTerm) : Codec.SemanticChildren :=
  match values with
  | [] => NoChildren
  | value :: rest => MoreChildren value (semantic_children rest)
  end.

Definition assemble_semantic (head : nat * nat) (values : list Codec.SemanticTerm)
    : option Codec.SemanticTerm :=
  Some (SelectedBranch head (semantic_children values)).

Definition Occurrence := @selected_tree Codec.SemanticTerm (nat * nat).
Definition OccurrenceChildren := @selected_children Codec.SemanticTerm (nat * nat).

Fixpoint typed_references (domain : list nat) (children : Codec.ReflectedChildren)
    : option (list (nat * Codec.ReflectedTerm)) :=
  match domain, children with
  | [], NoChildren => Some []
  | sort :: sorts, MoreChildren child children =>
      option_map (cons (sort, child)) (typed_references sorts children)
  | _, _ => None
  end.

Section CheckedProjection.
Variable table : list Head.ConstructorBinding.
Variable owner : string.
Variable carriers : nat -> option Codec.NativeKind.
Variable text_valid : string -> bool.

Inductive CheckedOccurrence : nat -> Codec.ReflectedTerm -> Occurrence -> Prop :=
| CheckedNative : forall expected leaf value,
    Codec.project_leaf owner carriers text_valid expected leaf = Some value ->
    CheckedOccurrence expected (SelectedLeaf leaf) (SelectedLeaf (SelectedLeaf value))
| CheckedConstructor : forall expected actual label children entry occurrences,
    String.eqb actual owner = true ->
    Head.reflected_lookup table expected label = Some entry ->
    CheckedChildren (Head.semantic_domain entry) children occurrences ->
    CheckedOccurrence expected (SelectedBranch (actual, label) children)
      (SelectedBranch (expected, Head.semantic_constructor entry) occurrences)
with CheckedChildren : list nat -> Codec.ReflectedChildren -> OccurrenceChildren -> Prop :=
| CheckedNoChildren : CheckedChildren [] NoChildren NoChildren
| CheckedMoreChildren : forall sort domain child children occurrence occurrences,
    CheckedOccurrence sort child occurrence ->
    CheckedChildren domain children occurrences ->
    CheckedChildren (sort :: domain) (MoreChildren child children)
      (MoreChildren occurrence occurrences).

Scheme checked_occurrence_mut := Induction for CheckedOccurrence Sort Prop
  with checked_children_mut := Induction for CheckedChildren Sort Prop.
Combined Scheme checked_mutual from checked_occurrence_mut, checked_children_mut.

Theorem checked_occurrences_denote_exact_projection :
  (forall expected source occurrence, CheckedOccurrence expected source occurrence ->
    denote_tree assemble_semantic occurrence =
      Codec.project_tree table owner carriers text_valid expected source) /\
  (forall domain source occurrences, CheckedChildren domain source occurrences ->
    option_map semantic_children (denote_children assemble_semantic occurrences) =
      Codec.project_children table owner carriers text_valid domain source).
Proof.
  apply checked_mutual.
  - intros expected leaf value H. cbn [denote_tree Codec.project_tree].
    rewrite H. reflexivity.
  - intros expected actual label children entry occurrences Eowner Eentry Hchildren IH.
    cbn [denote_tree Codec.project_tree]. rewrite Eowner, Eentry.
    change (match denote_children assemble_semantic occurrences with
      | Some values => assemble_semantic (expected, Head.semantic_constructor entry) values
      | None => None end =
      option_map (SelectedBranch (expected, Head.semantic_constructor entry))
        (Codec.project_children table owner carriers text_valid
          (Head.semantic_domain entry) children)).
    rewrite <- IH.
    destruct (denote_children assemble_semantic occurrences); reflexivity.
  - reflexivity.
  - intros sort domain child children occurrence occurrences Hchild IHchild Hchildren IHchildren.
    change (option_map semantic_children
      (match denote_tree assemble_semantic occurrence,
        denote_children assemble_semantic occurrences with
       | Some first, Some later => Some (first :: later)
       | _, _ => None end) =
      match Codec.project_tree table owner carriers text_valid sort child,
        Codec.project_children table owner carriers text_valid domain children with
      | Some first, Some later => Some (MoreChildren first later)
      | _, _ => None end).
    rewrite <- IHchild, <- IHchildren.
    destruct (denote_tree assemble_semantic occurrence),
      (denote_children assemble_semantic occurrences); reflexivity.
Qed.

Theorem successful_projection_has_checked_occurrences :
  (forall source expected output,
    Codec.project_tree table owner carriers text_valid expected source = Some output ->
    exists occurrence, CheckedOccurrence expected source occurrence) /\
  (forall source domain output,
    Codec.project_children table owner carriers text_valid domain source = Some output ->
    exists occurrences, CheckedChildren domain source occurrences).
Proof.
  apply selected_mutual.
  - intros leaf expected output H. cbn [Codec.project_tree] in H.
    destruct (Codec.project_leaf owner carriers text_valid expected leaf) as [value|] eqn:E;
      try discriminate.
    exists (SelectedLeaf (SelectedLeaf value)). constructor. exact E.
  - intros [actual label] children IH expected output H. cbn [Codec.project_tree] in H.
    destruct (String.eqb actual owner) eqn:Eowner; try discriminate.
    destruct (Head.reflected_lookup table expected label) as [entry|] eqn:Eentry;
      try discriminate.
    change (option_map (SelectedBranch (expected, Head.semantic_constructor entry))
      (Codec.project_children table owner carriers text_valid
        (Head.semantic_domain entry) children) = Some output) in H.
    destruct (Codec.project_children table owner carriers text_valid
      (Head.semantic_domain entry) children) as [values|] eqn:Echildren; try discriminate.
    destruct (IH _ _ Echildren) as [occurrences Hchecked].
    exists (SelectedBranch (expected, Head.semantic_constructor entry) occurrences).
    econstructor; eassumption.
  - intros [|sort domain] output H; cbn [Codec.project_children] in H; try discriminate.
    exists NoChildren. constructor.
  - intros child IHchild children IHchildren [|sort domain] output H; [discriminate|].
    change (match Codec.project_tree table owner carriers text_valid sort child,
      Codec.project_children table owner carriers text_valid domain children with
      | Some first, Some later => Some (MoreChildren first later)
      | _, _ => None end = Some output) in H.
    destruct (Codec.project_tree table owner carriers text_valid sort child)
      as [value|] eqn:Echild; try discriminate.
    destruct (Codec.project_children table owner carriers text_valid domain children)
      as [values|] eqn:Echildren; try discriminate.
    destruct (IHchild _ _ Echild) as [occurrence Hchild].
    destruct (IHchildren _ _ Echildren) as [occurrences Hchildren].
    exists (MoreChildren occurrence occurrences). constructor; assumption.
Qed.

Theorem checked_postorder_preserves_projection_and_stack :
  forall expected source occurrence stack,
  CheckedOccurrence expected source occurrence ->
  execute assemble_semantic (compile_tree occurrence) stack =
    option_map (fun value => value :: stack)
      (Codec.project_tree table owner carriers text_valid expected source).
Proof.
  intros expected source occurrence stack H.
  rewrite (proj1 (compiled_occurrences_refine_declarative_assembly assemble_semantic)).
  rewrite (proj1 checked_occurrences_denote_exact_projection _ _ _ H). reflexivity.
Qed.

Corollary checked_postorder_returns_exact_projected_root : forall expected source output,
  Codec.project_tree table owner carriers text_valid expected source = Some output <->
  exists occurrence, CheckedOccurrence expected source occurrence /\
    execute assemble_semantic (compile_tree occurrence) [] = Some [output].
Proof.
  intros expected source output. split.
  - intro H. destruct (proj1 successful_projection_has_checked_occurrences _ _ _ H)
      as [occurrence Hchecked].
    exists occurrence. split; [exact Hchecked|].
    rewrite (checked_postorder_preserves_projection_and_stack _ _ _ [] Hchecked), H.
    reflexivity.
  - intros [occurrence [Hchecked Hrun]].
    rewrite (checked_postorder_preserves_projection_and_stack _ _ _ [] Hchecked) in Hrun.
    destruct (Codec.project_tree table owner carriers text_valid expected source);
      inversion Hrun; reflexivity.
Qed.

(** Instantiation of the shared borrowed walker.  These structural source
    references are proof data for strictly contained Par children; production
    keeps references to the actual borrowed Par, not copies of these trees. *)
Definition SourceNode :=
  @Borrowed.Node (nat * Codec.ReflectedTerm) Codec.SemanticTerm (nat * nat).

Definition source_lookup (reference : nat * Codec.ReflectedTerm) : option SourceNode :=
  let '(expected, source) := reference in
  match source with
  | SelectedLeaf leaf =>
      option_map (fun value => Borrowed.NativeNode (SelectedLeaf value))
        (Codec.project_leaf owner carriers text_valid expected leaf)
  | SelectedBranch (actual, label) children =>
      if String.eqb actual owner then
        match Head.reflected_lookup table expected label with
        | Some entry => option_map
            (Borrowed.ConstructorNode (expected, Head.semantic_constructor entry))
            (typed_references (Head.semantic_domain entry) children)
        | None => None
        end
      else None
  end.

Theorem checked_projection_supplies_borrowed_unfolding :
  (forall expected source occurrence, CheckedOccurrence expected source occurrence ->
    Borrowed.Unfolds source_lookup (expected, source) occurrence) /\
  (forall domain source occurrences, CheckedChildren domain source occurrences ->
    exists references, typed_references domain source = Some references /\
      Borrowed.UnfoldChildren source_lookup references occurrences).
Proof.
  apply checked_mutual.
  - intros expected leaf value H. constructor. cbn [source_lookup]. rewrite H. reflexivity.
  - intros expected actual label children entry occurrences Eowner Eentry Hchildren IH.
    destruct IH as [references [Ereferences Hunfold]].
    econstructor; [|exact Hunfold].
    cbn [source_lookup]. rewrite Eowner, Eentry, Ereferences. reflexivity.
  - exists []. split; [reflexivity|constructor].
  - intros sort domain child children occurrence occurrences Hchild IHchild Hchildren IHchildren.
    destruct IHchildren as [references [Ereferences Hunfold]].
    exists ((sort, child) :: references). split.
    + cbn [typed_references]. rewrite Ereferences. reflexivity.
    + constructor; assumption.
Qed.

Corollary checked_borrowed_execution_preserves_projection :
  forall expected source occurrence values,
  CheckedOccurrence expected source occurrence ->
  Borrowed.run_borrowed source_lookup assemble_semantic (tree_work occurrence)
    [Borrowed.VisitReference (expected, source)] values =
    Fused.execution_outcome (option_map (fun value => value :: values)
      (Codec.project_tree table owner carriers text_valid expected source)).
Proof.
  intros expected source occurrence values Hchecked.
  pose proof (proj1 checked_projection_supplies_borrowed_unfolding
    _ _ _ Hchecked) as Hunfold.
  rewrite (Borrowed.borrowed_root_preserves_exact_declarative_assembly
    assemble_semantic values Hunfold).
  rewrite (proj1 checked_occurrences_denote_exact_projection _ _ _ Hchecked).
  reflexivity.
Qed.

Corollary successful_projection_executes_through_borrowed_references :
  forall expected source output,
  Codec.project_tree table owner carriers text_valid expected source = Some output ->
  exists control_fuel,
    Borrowed.run_borrowed source_lookup assemble_semantic control_fuel
      [Borrowed.VisitReference (expected, source)] [] = Fused.Completed [output].
Proof.
  intros expected source output H.
  destruct (proj1 successful_projection_has_checked_occurrences _ _ _ H)
    as [occurrence Hchecked].
  exists (tree_work occurrence).
  rewrite (checked_borrowed_execution_preserves_projection _ _ _ [] Hchecked), H.
  reflexivity.
Qed.

End CheckedProjection.
End InstalledFltOccurrence.

Print Assumptions InstalledFltOccurrence.checked_occurrences_denote_exact_projection.
Print Assumptions InstalledFltOccurrence.successful_projection_has_checked_occurrences.
Print Assumptions InstalledFltOccurrence.checked_postorder_preserves_projection_and_stack.
Print Assumptions InstalledFltOccurrence.checked_postorder_returns_exact_projected_root.
Print Assumptions InstalledFltOccurrence.checked_projection_supplies_borrowed_unfolding.
Print Assumptions InstalledFltOccurrence.checked_borrowed_execution_preserves_projection.
Print Assumptions InstalledFltOccurrence.successful_projection_executes_through_borrowed_references.
