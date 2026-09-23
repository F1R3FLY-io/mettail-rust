(** Local obligations for retaining Arrow.domain and MultiBinder.inner.

    This is a delta to AuthoredRuleStoreProjection, not a second arena or
    capture controller. All other Type payloads and all eight node tags remain
    unchanged. The old binder observation deliberately ignores Arrow.domain
    and observes MultiBinder as Other(original_handle). The context-to-items
    reader additionally needs the two shallow probes below.

    Existing capture Step is concrete over the old vocabulary. Its complete
    run theorem is NOT asserted for new payloads by this file. This file proves
    the added edge-validation and remapping obligations which must be composed
    with that controller when its vocabulary is extended. Rust allocation,
    source traversal, termination, and context occurrence budgets are outside
    these local laws. In particular, typed backward edges alone do not bound
    repeated traversal of a shared Params DAG.
*)
From Stdlib Require Import List Bool Arith.
From PrattailWpdaRuntime Require Import
  AuthoredRuleStoreProjection AuthoredRuleCaptureProjection.
Import ListNotations.
Set Implicit Arguments.

Module AuthoredTypeExtensionProjection.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.

Inductive AddedTypePayload :=
| RetainedArrow (domain codomain : A.Handle A.TypeTag)
| RetainedMultiBinder (inner : A.Handle A.TypeTag).

Definition added_edges payload : list A.Edge := match payload with
| RetainedArrow domain codomain => [A.edge domain; A.edge codomain]
| RetainedMultiBinder inner => [A.edge inner]
end.
Definition arrow_probe payload := match payload with
| RetainedArrow domain codomain => Some (domain, codomain)
| RetainedMultiBinder _ => None end.
Definition multi_probe payload := match payload with
| RetainedArrow _ _ => None
| RetainedMultiBinder inner => Some inner end.
Definition old_binder_observation original payload := match payload with
| RetainedArrow _ codomain => A.ArrowObservation (A.index codomain)
| RetainedMultiBinder _ => A.OtherTypeObservation original end.

Theorem arrow_retains_both_ordered_children : forall domain codomain,
  arrow_probe (RetainedArrow domain codomain) = Some (domain, codomain) /\
  added_edges (RetainedArrow domain codomain) = [A.edge domain; A.edge codomain].
Proof. intros; split; reflexivity. Qed.
Theorem multi_retains_its_immediate_child : forall inner,
  multi_probe (RetainedMultiBinder inner) = Some inner /\
  added_edges (RetainedMultiBinder inner) = [A.edge inner].
Proof. intros; split; reflexivity. Qed.
Theorem old_arrow_reader_is_unchanged : forall original domain codomain,
  old_binder_observation original (RetainedArrow domain codomain) =
  A.read_type original (A.Arrow codomain).
Proof. reflexivity. Qed.
Theorem old_multi_reader_keeps_original_identity : forall original inner,
  old_binder_observation original (RetainedMultiBinder inner) =
  A.read_type original (A.UnsupportedType 0).
Proof. reflexivity. Qed.
Theorem equal_children_remain_two_reference_fields : forall child,
  List.length (added_edges (RetainedArrow child child)) = 2.
Proof. reflexivity. Qed.

(** Same prior-prefix predicate used by checked append, without copying it. *)
Definition added_edges_valid arena payload :=
  forallb (A.reference_valid arena) (added_edges payload).
Theorem every_added_edge_has_a_prior_typed_target : forall arena payload reference,
  added_edges_valid arena payload = true -> In reference (added_edges payload) ->
  exists target, nth_error arena (snd reference) = Some target /\
    A.node_tag target = fst reference /\ snd reference < List.length arena.
Proof.
  intros arena payload reference Valid Member.
  unfold added_edges_valid in Valid.
  apply forallb_forall with (x := reference) in Valid; [|exact Member].
  apply A.reference_valid_sound; exact Valid.
Qed.
Theorem missing_arrow_domain_refuses : forall arena domain codomain,
  A.reference_valid arena (A.edge domain) = false ->
  added_edges_valid arena (RetainedArrow domain codomain) = false.
Proof.
  intros arena domain codomain H.
  change (A.reference_valid arena (A.edge domain) &&
    (A.reference_valid arena (A.edge codomain) && true) = false).
  rewrite H; reflexivity.
Qed.
Theorem missing_arrow_codomain_refuses : forall arena domain codomain,
  A.reference_valid arena (A.edge codomain) = false ->
  added_edges_valid arena (RetainedArrow domain codomain) = false.
Proof.
  intros arena domain codomain H.
  change (A.reference_valid arena (A.edge domain) &&
    (A.reference_valid arena (A.edge codomain) && true) = false).
  rewrite H.
  destruct (A.reference_valid arena (A.edge domain)); reflexivity.
Qed.

Definition remap_added (resolve : C.Resolver) payload := match payload with
| RetainedArrow domain codomain =>
    match resolve (A.edge domain) with
    | None => None
    | Some mapped_domain => match resolve (A.edge codomain) with
      | None => None
      | Some mapped_codomain =>
          Some (RetainedArrow (A.Ref mapped_domain) (A.Ref mapped_codomain))
      end
    end
| RetainedMultiBinder inner =>
    option_map (fun target => RetainedMultiBinder (A.Ref target)) (resolve (A.edge inner))
end.
Theorem arrow_remap_resolves_domain_before_codomain : forall resolve domain codomain mapped,
  remap_added resolve (RetainedArrow domain codomain) = Some mapped ->
  exists mapped_domain mapped_codomain,
    resolve (A.edge domain) = Some mapped_domain /\
    resolve (A.edge codomain) = Some mapped_codomain /\
    mapped = RetainedArrow (A.Ref mapped_domain) (A.Ref mapped_codomain).
Proof.
  intros resolve domain codomain mapped H; cbn [remap_added] in H.
  destruct (resolve (A.edge domain)) as [d|] eqn:D; [|discriminate].
  destruct (resolve (A.edge codomain)) as [c|] eqn:E; [|discriminate].
  inversion H; subst; exists d, c; auto.
Qed.
Theorem unresolved_domain_does_not_produce_a_partial_arrow : forall resolve domain codomain,
  resolve (A.edge domain) = None ->
  remap_added resolve (RetainedArrow domain codomain) = None.
Proof. intros; cbn [remap_added]; rewrite H; reflexivity. Qed.
Theorem multi_remap_preserves_constructor : forall resolve inner mapped,
  remap_added resolve (RetainedMultiBinder inner) = Some mapped ->
  exists target, resolve (A.edge inner) = Some target /\
    mapped = RetainedMultiBinder (A.Ref target).
Proof.
  intros resolve inner mapped H; cbn [remap_added] in H.
  destruct (resolve (A.edge inner)) as [target|] eqn:E; [|discriminate].
  inversion H; subst; eauto.
Qed.
Theorem remapping_retains_exact_reference_field_count : forall resolve source mapped,
  remap_added resolve source = Some mapped ->
  List.length (added_edges mapped) = List.length (added_edges source).
Proof.
  intros resolve [domain codomain|inner] mapped H.
  - destruct (@arrow_remap_resolves_domain_before_codomain _ _ _ _ H)
      as [d [c [_ [_ ->]]]]; reflexivity.
  - destruct (@multi_remap_preserves_constructor _ _ _ H) as [target [_ ->]]; reflexivity.
Qed.

Print Assumptions arrow_retains_both_ordered_children.
Print Assumptions multi_retains_its_immediate_child.
Print Assumptions old_arrow_reader_is_unchanged.
Print Assumptions old_multi_reader_keeps_original_identity.
Print Assumptions equal_children_remain_two_reference_fields.
Print Assumptions every_added_edge_has_a_prior_typed_target.
Print Assumptions missing_arrow_domain_refuses.
Print Assumptions missing_arrow_codomain_refuses.
Print Assumptions arrow_remap_resolves_domain_before_codomain.
Print Assumptions unresolved_domain_does_not_produce_a_partial_arrow.
Print Assumptions multi_remap_preserves_constructor.
Print Assumptions remapping_retains_exact_reference_field_count.
End AuthoredTypeExtensionProjection.
