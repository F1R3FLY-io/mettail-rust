(** Erasing an already-normalized fresh binder roster to an emission descriptor.

    Binder identities remain with the source environment. The target needs the
    emitted count and the URI projection, not another copy of the roster. This
    file proves that the smaller representation retains the existing checked
    construction protocol, including its rejection order. It does not sort,
    parse URI text, translate caller imports, or materialize node processes.

    Ordinary allocation and URI allocation remain distinct even at width zero.
    Injection keys name ordered value children, not lexical binders or authority.
    The descriptor's child layout is body first, then every injection value.
    Graph scheduling, nested metadata/copy accounting and stack-safe ownership
    require separate proofs before graph emission can consume this descriptor. *)
From Stdlib Require Import List String Bool Arith Lia ZArith.
From RhoBridge Require Import RholangTargetConstruction RholangConstructionProtocol.
Import ListNotations.

Inductive FreshShape :=
| PlainShape (width : nat)
| UriShape (width : nat) (uris : list string).
Definition shape_width (shape : FreshShape) : nat :=
  match shape with PlainShape width | UriShape width _ => width end.
Definition shape_uris (shape : FreshShape) : list string :=
  match shape with PlainShape _ => [] | UriShape _ uris => uris end.
Definition shape_valid (shape : FreshShape) : bool :=
  match shape with
  | PlainShape _ => true
  | UriShape width uris => Nat.eqb (List.length uris) width && normalized_uris uris
  end.

Definition erase_fresh_roster (plan : FreshPlan) : FreshShape :=
  match plan with
  | PlainFresh binders => PlainShape (List.length binders)
  | UriFresh pairs => UriShape (List.length pairs) (map fst pairs)
  end.

Theorem erased_width_counts_every_binder_occurrence : forall plan,
  shape_width (erase_fresh_roster plan) = List.length (fresh_binders plan).
Proof. intros [binders|pairs]; cbn; [reflexivity|now rewrite length_map]. Qed.
Theorem erased_uris_retain_the_exact_projection : forall plan,
  shape_uris (erase_fresh_roster plan) = fresh_uris plan.
Proof. intros [binders|pairs]; reflexivity. Qed.
Theorem erasure_preserves_the_existing_layout_check : forall plan,
  shape_valid (erase_fresh_roster plan) = fresh_plan_valid plan.
Proof. intros [binders|pairs]; cbn; [reflexivity|]. now rewrite length_map, Nat.eqb_refl. Qed.

Definition checked_shape_fresh (shape : FreshShape) (keys : list string)
    (children : list Value) : ConstructionResult :=
  match children with
  | [] => ConstructionRejected ChildArityMismatch
  | body :: injections =>
    if shape_valid shape && ordered_injection_keys keys then
      within_target_indices [shape_width shape]
        (fresh_with_injections (shape_width shape) (shape_uris shape) keys body injections)
    else ConstructionRejected InvalidBinderLayout
  end.

Theorem erased_constructor_commutes_with_the_full_protocol : forall plan keys children,
  checked_shape_fresh (erase_fresh_roster plan) keys children =
  interpret (FreshOp plan keys) children.
Proof.
  intros plan keys [|body injections]; [reflexivity|].
  cbn [checked_shape_fresh interpret checked_injected_fresh].
  now rewrite erasure_preserves_the_existing_layout_check,
    erased_width_counts_every_binder_occurrence, erased_uris_retain_the_exact_projection.
Qed.

Record FreshDescriptor := {
  descriptor_shape : FreshShape;
  descriptor_keys : list string
}.
Definition admit_fresh_descriptor shape keys : option FreshDescriptor :=
  if (shape_valid shape && ordered_injection_keys keys) && fits_target_index (shape_width shape)
  then Some {| descriptor_shape := shape; descriptor_keys := keys |}
  else None.

Theorem admitted_descriptor_has_exact_fields_and_checked_domain : forall shape keys descriptor,
  admit_fresh_descriptor shape keys = Some descriptor ->
  descriptor_shape descriptor = shape /\ descriptor_keys descriptor = keys /\
  shape_valid shape = true /\ ordered_injection_keys keys = true /\
  (Z.of_nat (shape_width shape) <= 2147483647)%Z.
Proof.
  intros shape keys descriptor H. unfold admit_fresh_descriptor in H.
  destruct ((shape_valid shape && ordered_injection_keys keys) &&
    fits_target_index (shape_width shape)) eqn:HD; [|discriminate].
  inversion H; subst descriptor. apply andb_true_iff in HD as [HL HI].
  apply andb_true_iff in HL as [HS HK]. unfold fits_target_index in HI.
  apply Z.leb_le in HI. cbn. repeat split; assumption.
Qed.

Theorem admitted_descriptor_reuses_existing_fresh_target : forall shape keys descriptor body injections,
  admit_fresh_descriptor shape keys = Some descriptor ->
  checked_shape_fresh (descriptor_shape descriptor) (descriptor_keys descriptor) (body :: injections) =
  fresh_with_injections (shape_width shape) (shape_uris shape) keys body injections.
Proof.
  intros shape keys descriptor body injections H. unfold admit_fresh_descriptor in H.
  destruct ((shape_valid shape && ordered_injection_keys keys) &&
    fits_target_index (shape_width shape)) eqn:HD; [|discriminate].
  inversion H; subst descriptor. apply andb_true_iff in HD as [HL HI].
  cbn [checked_shape_fresh descriptor_shape descriptor_keys]. rewrite HL.
  unfold within_target_indices. cbn [forallb]. now rewrite HI.
Qed.

Theorem erased_success_preserves_keys_children_and_body_only_summary : forall plan keys body injections value,
  checked_shape_fresh (erase_fresh_roster plan) keys (body :: injections) = Constructed value ->
  List.length keys = List.length injections /\
  heads_of value = [MakeHead
    (NewHead (List.length (fresh_binders plan)) (fresh_uris plan) keys) (body :: injections)] /\
  summary_of value = shifted_summary (List.length (fresh_binders plan)) (summary_of body).
Proof.
  intros plan keys body injections value H.
  rewrite erased_constructor_commutes_with_the_full_protocol in H.
  apply injected_fresh_success_has_exact_layout in H. tauto.
Qed.

Theorem erased_empty_injections_specialize_original_fresh : forall plan body,
  checked_shape_fresh (erase_fresh_roster plan) [] [body] = checked_fresh plan body.
Proof.
  intros. rewrite erased_constructor_commutes_with_the_full_protocol.
  apply empty_injection_operation_reuses_fresh.
Qed.

(** The machine-sized arity check is separate from the signed emitted count.
    Its bound is supplied by the implementation's usize width; no huge Peano
    number is evaluated here. Success allocates no child values. *)
Definition checked_fresh_arity (maximum : nat) (keys : list string) : option nat :=
  let arity := S (List.length keys) in
  if arity <=? maximum then Some arity else None.
Theorem checked_arity_retains_body_and_every_injection : forall maximum keys arity,
  checked_fresh_arity maximum keys = Some arity ->
  arity = S (List.length keys) /\ arity <= maximum.
Proof.
  intros maximum keys arity H. unfold checked_fresh_arity in H.
  destruct (S (List.length keys) <=? maximum) eqn:HB; [|discriminate].
  inversion H; subst. apply Nat.leb_le in HB. auto.
Qed.
Theorem overflowing_arity_rejects : forall maximum keys,
  maximum < S (List.length keys) -> checked_fresh_arity maximum keys = None.
Proof.
  intros maximum keys H. unfold checked_fresh_arity.
  apply Nat.leb_gt in H. now rewrite H.
Qed.

Example zero_width_plain_and_uri_shapes_are_distinct :
  shape_valid (PlainShape 0) = true /\ shape_valid (UriShape 0 []) = false.
Proof. split; reflexivity. Qed.
Example duplicate_uri_projection_is_not_admitted :
  admit_fresh_descriptor (UriShape 2 ["a"; "a"]%string) [] = None.
Proof. reflexivity. Qed.
Example unused_empty_key_is_preserved_in_the_descriptor :
  admit_fresh_descriptor (PlainShape 0) [EmptyString] =
  Some {| descriptor_shape := PlainShape 0; descriptor_keys := [EmptyString] |}.
Proof. reflexivity. Qed.

Print Assumptions erased_width_counts_every_binder_occurrence.
Print Assumptions erased_uris_retain_the_exact_projection.
Print Assumptions erasure_preserves_the_existing_layout_check.
Print Assumptions erased_constructor_commutes_with_the_full_protocol.
Print Assumptions admitted_descriptor_has_exact_fields_and_checked_domain.
Print Assumptions admitted_descriptor_reuses_existing_fresh_target.
Print Assumptions erased_success_preserves_keys_children_and_body_only_summary.
Print Assumptions erased_empty_injections_specialize_original_fresh.
Print Assumptions checked_arity_retains_body_and_every_injection.
Print Assumptions overflowing_arity_rejects.
Print Assumptions zero_width_plain_and_uri_shapes_are_distinct.
Print Assumptions duplicate_uri_projection_is_not_admitted.
Print Assumptions unused_empty_key_is_preserved_in_the_descriptor.
