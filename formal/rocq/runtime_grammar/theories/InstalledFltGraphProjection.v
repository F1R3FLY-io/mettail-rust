(** * Reachable graph projection preserves complete borrowed occurrences

    The kernel's existing [ReachabilityProjection] changes arena coordinates
    while preserving node labels and every ordered child slot.  A label here
    indexes one immutable table of COMPLETE heads: native payload and sort,
    or full constructor identity/signature.  It is not a lossy constructor
    discriminant.  Both arenas use the same decoding table.

    This module adds the missing finite-unfolding transport theorem to that
    existing projection contract.  It does not assume identifiers stay equal
    or that the remapping is injective.  It also does not certify a Rust label
    table, operator framing, source admission, or graph insertion: production
    must realize the complete-head and projection premises exactly. *)

From Stdlib Require Import List.
From RuntimeGrammar Require Import SemanticTransitionKernel BorrowedOccurrenceExecution.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
Import ListNotations.
Set Implicit Arguments.

Module InstalledFltGraphProjection.
Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.
Module Borrowed := BorrowedOccurrenceExecution.BorrowedOccurrenceExecution.

Section GraphProjection.
Context {Value Label : Type}.

Inductive CompleteHead :=
| NativeHead (value : Value)
| ConstructorHead (label : Label).

Variable decode_head : nat -> option CompleteHead.

Definition graph_lookup (graph : Kernel.PublicationGraph) (reference : nat)
    : option (@Borrowed.Node nat Value Label) :=
  match graph reference with
  | Some node =>
      match decode_head (Kernel.publication_label node) with
      | Some (NativeHead value) =>
          match Kernel.publication_children node with
          | [] => Some (Borrowed.NativeNode value)
          | _ => None
          end
      | Some (ConstructorHead label) =>
          Some (Borrowed.ConstructorNode label (Kernel.publication_children node))
      | None => None
      end
  | None => None
  end.

Variable source : Kernel.PublicationGraph.
Variable roots : list nat.
Variable projection : Kernel.ReachabilityProjection source roots.

Let remap := Kernel.projection_remap source roots projection.
Let target := Kernel.projection_graph source roots projection.

Lemma projected_native_keeps_its_complete_head : forall reference value target_reference,
  graph_lookup source reference = Some (Borrowed.NativeNode value) ->
  remap reference = Some target_reference ->
  graph_lookup target target_reference = Some (Borrowed.NativeNode value).
Proof.
  intros reference value target_reference Hlookup Hmap.
  unfold graph_lookup in Hlookup.
  destruct (source reference) as [[label children]|] eqn:Esource; try discriminate.
  cbn in Hlookup.
  destruct (decode_head label) as [[native|constructor]|] eqn:Ehead; try discriminate.
  destruct children as [|child children]; try discriminate.
  inversion Hlookup; subst native.
  destruct (Kernel.projection_nodes_exact source roots projection
    reference target_reference _ Hmap Esource)
    as [target_children [Hchildren Hnode]].
  cbn in Hchildren. inversion Hchildren; subst target_children.
  unfold graph_lookup, target. rewrite Hnode. cbn. rewrite Ehead. reflexivity.
Qed.

Lemma projected_constructor_keeps_its_complete_head :
  forall reference label children target_reference,
  graph_lookup source reference = Some (Borrowed.ConstructorNode label children) ->
  remap reference = Some target_reference ->
  exists target_children,
    Kernel.ChildrenRemapped remap children target_children /\
    graph_lookup target target_reference = Some (Borrowed.ConstructorNode label target_children).
Proof.
  intros reference label children target_reference Hlookup Hmap.
  unfold graph_lookup in Hlookup.
  destruct (source reference) as [[source_label source_children]|] eqn:Esource; try discriminate.
  cbn in Hlookup.
  destruct (decode_head source_label) as [[native|constructor]|] eqn:Ehead; try discriminate.
  - destruct source_children; discriminate.
  - inversion Hlookup; subst constructor source_children.
    destruct (Kernel.projection_nodes_exact source roots projection
      reference target_reference _ Hmap Esource)
      as [target_children [Hchildren Hnode]].
    exists target_children. split; [exact Hchildren|].
    unfold graph_lookup, target. rewrite Hnode. cbn. rewrite Ehead. reflexivity.
Qed.

Theorem reachable_projection_preserves_finite_unfolding :
  (forall reference occurrence, Borrowed.Unfolds (graph_lookup source) reference occurrence ->
    forall target_reference, remap reference = Some target_reference ->
    Borrowed.Unfolds (graph_lookup target) target_reference occurrence) /\
  (forall references occurrences,
    Borrowed.UnfoldChildren (graph_lookup source) references occurrences ->
    forall target_references, Kernel.ChildrenRemapped remap references target_references ->
    Borrowed.UnfoldChildren (graph_lookup target) target_references occurrences).
Proof.
  apply Borrowed.unfold_mutual.
  - intros reference value Hlookup target_reference Hmap.
    constructor. eapply projected_native_keeps_its_complete_head; eassumption.
  - intros reference label children occurrences Hlookup Hchildren IH target_reference Hmap.
    destruct (@projected_constructor_keeps_its_complete_head
      reference label children target_reference Hlookup Hmap)
      as [target_children [Hmapped Hlookup_target]].
    econstructor; [exact Hlookup_target|now apply IH].
  - intros target_references Hmapped. inversion Hmapped. constructor.
  - intros reference references occurrence occurrences Hfirst IHfirst Hlater IHlater
      target_references Hmapped.
    inversion Hmapped as [|source_id target_id sources targets Hmap Hmaps]; subst.
    constructor; [now apply IHfirst|now apply IHlater].
Qed.

Corollary every_published_root_keeps_its_complete_occurrence :
  forall root occurrence,
  In root roots -> Borrowed.Unfolds (graph_lookup source) root occurrence ->
  exists target_root,
    remap root = Some target_root /\
    Borrowed.Unfolds (graph_lookup target) target_root occurrence.
Proof.
  intros root occurrence Hroot Hunfold.
  destruct (Kernel.every_publication_root_receives_an_identifier
    source roots projection root Hroot) as [target_root Hmap].
  exists target_root. split; [exact Hmap|].
  eapply (proj1 reachable_projection_preserves_finite_unfolding); eassumption.
Qed.

End GraphProjection.
End InstalledFltGraphProjection.

Print Assumptions InstalledFltGraphProjection.projected_native_keeps_its_complete_head.
Print Assumptions InstalledFltGraphProjection.projected_constructor_keeps_its_complete_head.
Print Assumptions InstalledFltGraphProjection.reachable_projection_preserves_finite_unfolding.
Print Assumptions InstalledFltGraphProjection.every_published_root_keeps_its_complete_occurrence.
