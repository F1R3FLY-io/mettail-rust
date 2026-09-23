(** Finite-run composition for the extended ORIGINAL capture vocabulary.

    Store/Capture now directly include Arrow.domain and MultiBinder.inner.
    Their original State, Step, schedule and FiniteRun controller are unchanged.
    The checked proofs here compose their actual operations: no alternate
    controller, Arrow-as-Map encoding, erased-reference interpretation, or
    reconstructed source is used. The local delta's exact embeddings are in
    AuthoredTypeExtensionProjection.

    Declaration names are additional ordered roots of this same run and have
    the same memo/name-class table. Header association and explicit-owner laws
    are imported from AuthoredDeclarationsProjection. Header metadata is not
    itself a ninth arena node. Source-to-core association IDs still require
    original lowering-site correspondence; this file does not infer them.

    Claims are for finite accepted runs under the source/read/admission
    premises of the original model. No total-termination, decoder/native-value
    correspondence, Rust allocator, ABI serializer, or context-DAG work budget
    is proved. RuntimeCaptureAdmission remains the separate logical-size gate.
*)
From Stdlib Require Import List Arith Lia.
From PrattailWpdaRuntime Require Import AuthoredRuleStoreProjection
  AuthoredRuleCaptureProjection AuthoredTypeExtensionProjection
  AuthoredDeclarationsProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredExtendedCaptureComposition.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.
Module D := AuthoredDeclarationsProjection.AuthoredDeclarationsProjection.
Module E := AuthoredTypeExtensionProjection.AuthoredTypeExtensionProjection.

Theorem extended_arrow_schedule_visits_both_children_in_field_order :
  forall owner domain codomain rest,
  C.schedule owner (A.SourceTypeNode (A.ExistingType (A.B.SArrow domain codomain))) rest =
    C.Enter (A.TypeTag, domain) :: C.Enter (A.TypeTag, codomain) ::
    C.Finish owner (A.SourceTypeNode (A.ExistingType (A.B.SArrow domain codomain))) :: rest.
Proof. reflexivity. Qed.
Theorem extended_multi_schedule_visits_child_before_finish : forall owner inner rest,
  C.schedule owner (A.SourceTypeNode (A.ExistingMultiBinder inner)) rest =
    C.Enter (A.TypeTag, inner) ::
    C.Finish owner (A.SourceTypeNode (A.ExistingMultiBinder inner)) :: rest.
Proof. reflexivity. Qed.

Theorem successful_arrow_remap_resolves_both_actual_children :
  forall reader domain codomain mapped,
  C.remap_type reader (A.ExistingType (A.B.SArrow domain codomain)) = Some mapped ->
  exists d c, reader (A.TypeTag, domain) = Some d /\
    reader (A.TypeTag, codomain) = Some c /\
    mapped = A.ExistingType (A.B.SArrow d c).
Proof.
  intros reader domain codomain mapped H.
  cbn [C.remap_type] in H; unfold C.resolve in H.
  destruct (reader (A.TypeTag, domain)) as [d|] eqn:D; cbn [C.bind] in H; [|discriminate].
  destruct (reader (A.TypeTag, codomain)) as [c|] eqn:E; cbn [C.bind] in H; [|discriminate].
  inversion H; subst; exists d, c; auto.
Qed.
Theorem successful_multi_remap_resolves_actual_child : forall reader inner mapped,
  C.remap_type reader (A.ExistingMultiBinder inner) = Some mapped ->
  exists target, reader (A.TypeTag, inner) = Some target /\
    mapped = A.ExistingMultiBinder target.
Proof.
  intros reader inner mapped H.
  cbn [C.remap_type] in H; unfold C.resolve in H.
  destruct (reader (A.TypeTag, inner)) as [target|] eqn:E; cbn [C.bind] in H; [|discriminate].
  inversion H; subst; eauto.
Qed.

Lemma continued_step_preserves_stored_lookup : forall graph admit roots before after position node,
  C.Step graph admit roots before (C.Continue after) ->
  nth_error (C.arena before) position = Some node ->
  nth_error (C.arena after) position = Some node.
Proof.
  intros graph admit roots before after position node Transition Read.
  inversion Transition; subst; cbn in *; try exact Read.
  match goal with H : A.append_checked _ _ = Some _ |- _ =>
    apply A.append_checked_exact in H; destruct H as [-> _] end.
  apply A.lookup_append_stable; exact Read.
Qed.
Theorem finite_suffix_preserves_stored_lookup : forall graph admit roots before count after position node,
  C.FiniteRun graph admit roots before count after ->
  nth_error (C.arena before) position = Some node ->
  nth_error (C.arena after) position = Some node.
Proof.
  intros graph admit roots before count after position node Run.
  induction Run; intros Read; [exact Read|].
  apply IHRun; eapply continued_step_preserves_stored_lookup; eauto.
Qed.

(** Accepted publication has both the existing invariant and exact root-to-
    typed-node correspondence, now over the genuinely extended vocabulary. *)
Theorem full_extended_capture_publishes_typed_ordered_roots :
  forall graph admit roots count st nodes ids,
  C.FiniteRun graph admit roots (C.initial roots) count st ->
  C.Step graph admit roots st (C.Complete nodes ids) ->
  A.ValidArena nodes /\ nodes = List.map A.own_node (C.events st) /\
  List.length ids = List.length roots /\
  forall position edge, nth_error roots position = Some edge ->
    exists target node, nth_error ids position = Some target /\
      nth_error nodes target = Some node /\ A.node_tag node = fst edge.
Proof.
  intros graph admit roots count st nodes ids Run Done.
  destruct (@C.finite_capture_postorder_and_typed_store _ _ _ _ _ Run)
    as [Valid [Events [Ready Pending]]].
  destruct (@C.returned_roots_keep_order_and_multiplicity _ _ _ _ _ _ Done)
    as [Length Root].
  assert (Nodes : nodes = C.arena st) by (inversion Done; reflexivity).
  subst nodes; repeat split; try assumption.
  intros position edge Read.
  destruct (Root position edge Read) as [target [Position Mark]].
  destruct (Ready edge target Mark) as [node [Lookup Tag]].
  exists target, node; auto.
Qed.

Theorem emitted_extended_arrow_retains_both_prior_typed_children :
  forall graph admit roots count st position domain codomain,
  C.FiniteRun graph admit roots (C.initial roots) count st ->
  nth_error (C.events st) position =
    Some (A.SourceTypeNode (A.ExistingType (A.B.SArrow domain codomain))) ->
  nth_error (C.arena st) position =
    Some (A.TypeNode (A.Arrow (A.Ref domain) (A.Ref codomain))) /\
  exists domain_node codomain_node,
    nth_error (C.arena st) domain = Some domain_node /\
    A.node_tag domain_node = A.TypeTag /\ domain < position /\
    nth_error (C.arena st) codomain = Some codomain_node /\
    A.node_tag codomain_node = A.TypeTag /\ codomain < position.
Proof.
  intros graph admit roots count st position domain codomain Run Event.
  destruct (@C.finite_capture_postorder_and_typed_store _ _ _ _ _ Run)
    as [Valid [Events _]].
  assert (Lookup : nth_error (C.arena st) position =
    Some (A.TypeNode (A.Arrow (A.Ref domain) (A.Ref codomain)))).
  { rewrite Events, A.map_nth_exact, Event; reflexivity. }
  split; [exact Lookup|].
  destruct (@A.valid_arena_edges_strictly_decrease _ Valid position _
    (A.TypeTag, domain) Lookup (or_introl eq_refl)) as [d [DL [DT DB]]].
  destruct (@A.valid_arena_edges_strictly_decrease _ Valid position _
    (A.TypeTag, codomain) Lookup (or_intror (or_introl eq_refl))) as [c [CL [CT CB]]].
  exists d, c; repeat split; assumption.
Qed.
Theorem emitted_extended_multi_retains_prior_typed_child :
  forall graph admit roots count st position inner,
  C.FiniteRun graph admit roots (C.initial roots) count st ->
  nth_error (C.events st) position = Some (A.SourceTypeNode (A.ExistingMultiBinder inner)) ->
  nth_error (C.arena st) position = Some (A.TypeNode (A.MultiBinder (A.Ref inner))) /\
  exists child, nth_error (C.arena st) inner = Some child /\
    A.node_tag child = A.TypeTag /\ inner < position.
Proof.
  intros graph admit roots count st position inner Run Event.
  destruct (@C.finite_capture_postorder_and_typed_store _ _ _ _ _ Run)
    as [Valid [Events _]].
  assert (Lookup : nth_error (C.arena st) position =
    Some (A.TypeNode (A.MultiBinder (A.Ref inner)))).
  { rewrite Events, A.map_nth_exact, Event; reflexivity. }
  split; [exact Lookup|].
  exact (@A.valid_arena_edges_strictly_decrease _ Valid position _
    (A.TypeTag, inner) Lookup (or_introl eq_refl)).
Qed.

Theorem full_extended_run_keeps_declaration_roots_in_same_store :
  forall graph admit rules header count st nodes ids position edge,
  C.FiniteRun graph admit (D.capture_roots rules header)
    (C.initial (D.capture_roots rules header)) count st ->
  C.Step graph admit (D.capture_roots rules header) st (C.Complete nodes ids) ->
  nth_error (D.declaration_names header) position = Some edge ->
  exists target node,
    nth_error ids (List.length rules + position) = Some target /\
    nth_error nodes target = Some node /\ A.node_tag node = fst edge.
Proof.
  intros graph admit rules header count st nodes ids position edge Run Done Read.
  destruct (@full_extended_capture_publishes_typed_ordered_roots _ _ _ _ _ _ _ Run Done)
    as [_ [_ [_ Roots]]].
  apply Roots; rewrite D.declaration_root_positions_follow_rule_roster; exact Read.
Qed.

Print Assumptions extended_arrow_schedule_visits_both_children_in_field_order.
Print Assumptions extended_multi_schedule_visits_child_before_finish.
Print Assumptions successful_arrow_remap_resolves_both_actual_children.
Print Assumptions successful_multi_remap_resolves_actual_child.
Print Assumptions continued_step_preserves_stored_lookup.
Print Assumptions finite_suffix_preserves_stored_lookup.
Print Assumptions full_extended_capture_publishes_typed_ordered_roots.
Print Assumptions emitted_extended_arrow_retains_both_prior_typed_children.
Print Assumptions emitted_extended_multi_retains_prior_typed_child.
Print Assumptions full_extended_run_keeps_declaration_roots_in_same_store.
End AuthoredExtendedCaptureComposition.
