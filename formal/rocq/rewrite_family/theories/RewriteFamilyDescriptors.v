From Stdlib Require Import List Bool PeanoNat Lia.
Require Import RewriteFamilyFocus.
From RuntimeGrammar Require Import SemanticTransitionKernel.
Import ListNotations.
Module F := RewriteFamilyFocus.RewriteFamilyFocus.
Module K := SemanticTransitionKernel.SemanticTransitionKernel.

Module RewriteFamilyDescriptors.

Fixpoint index_of {A : Type} (name : nat) (rows : list (nat * A)) : option nat :=
  match rows with
  | [] => None
  | (other, _) :: rest =>
      if Nat.eqb name other then Some 0 else option_map S (index_of name rest)
  end.

Definition lookup {A : Type} (name : nat) (rows : list (nat * A)) : option A :=
  match index_of name rows with
  | Some index => option_map snd (nth_error rows index)
  | None => None
  end.

Fixpoint scan {A : Type} (name : nat) (rows : list (nat * A)) : option A :=
  match rows with
  | [] => None
  | (other, value) :: rest => if Nat.eqb name other then Some value else scan name rest
  end.

Lemma lookup_scan : forall (A : Type) name (rows : list (nat * A)),
  lookup name rows = scan name rows.
Proof.
  intros A name rows. induction rows as [|[other value] rest IH]; [reflexivity|].
  unfold lookup at 1. simpl. destruct (Nat.eqb name other); [reflexivity|].
  destruct (index_of name rest) eqn:Hindex; simpl;
    unfold lookup in IH; rewrite Hindex in IH; exact IH.
Qed.

Theorem registered_lookup_is_exact : forall (A : Type) name (rows : list (nat * A)) value,
  NoDup (map fst rows) ->
  (lookup name rows = Some value <-> In (name, value) rows).
Proof.
  intros A name rows. induction rows as [|[other head] rest IH]; intros value Hunique;
    rewrite lookup_scan; simpl; [split; [discriminate|contradiction]|].
  inversion Hunique as [|? ? Hnot Htail]; subst.
  specialize (IH value Htail). rewrite lookup_scan in IH.
  destruct (Nat.eqb name other) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst other. split.
    + intros H. inversion H; subst. now left.
    + intros [H|H].
      * inversion H. reflexivity.
      * exfalso. apply Hnot. apply in_map with (f := @fst nat A) in H. exact H.
  - apply Nat.eqb_neq in Heq. rewrite IH. split.
    + now right.
    + intros [H|H]; [inversion H; congruence|assumption].
Qed.

Theorem unknown_registered_name_is_refused : forall (A : Type) name (rows : list (nat * A)),
  ~ In name (map fst rows) -> lookup name rows = None.
Proof.
  intros A name rows. induction rows as [|[other value] rest IH]; intros Hmissing;
    rewrite lookup_scan; simpl; [reflexivity|].
  destruct (Nat.eqb name other) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst. exfalso. apply Hmissing. now left.
  - rewrite <- lookup_scan. apply IH. intros H. apply Hmissing. now right.
Qed.

Inductive CollectionKind := ListKind | BagKind | SetKind | MapKind | PathMapKind.

Inductive Descriptor :=
| Syntax
| Opaque
| Function (domain codomain : nat) (multiple : bool)
| Collection (kind : CollectionKind) (key : option nat) (element : nat)
| Product (factors : list nat).

Definition Sorts := list (nat * Descriptor).
Definition Constructors := list (nat * (list nat * nat)).

Definition expected_matches (expected : option nat) (actual : nat) :=
  match expected with None => true | Some value => Nat.eqb value actual end.

Lemma expected_matches_spec : forall expected actual,
  expected_matches expected actual = true <-> expected = None \/ expected = Some actual.
Proof.
  intros [value|] actual; simpl.
  - rewrite Nat.eqb_eq. split; [intros ->; now right|intros [H|H]; inversion H; reflexivity].
  - tauto.
Qed.

Definition constructor_view (rows : Constructors) name arity expected :=
  match lookup name rows with
  | Some (domains, result) =>
      if Nat.eqb arity (length domains) && expected_matches expected result
      then Some (domains, result) else None
  | None => None
  end.

Definition ConstructorFields (rows : Constructors) name arity expected domains result :=
  In (name, (domains, result)) rows /\ arity = length domains /\
  (expected = None \/ expected = Some result).

Theorem constructor_projection_is_exact : forall rows name arity expected domains result,
  NoDup (map fst rows) ->
  (constructor_view rows name arity expected = Some (domains, result) <->
   ConstructorFields rows name arity expected domains result).
Proof.
  intros rows name arity expected domains result Hunique.
  unfold constructor_view, ConstructorFields. split.
  - destruct (lookup name rows) as [[ds r]|] eqn:Hlookup; [|discriminate].
    destruct (Nat.eqb arity (length ds) && expected_matches expected r) eqn:Hcheck;
      [|discriminate]. intros H. inversion H; subst ds r.
    apply andb_true_iff in Hcheck. destruct Hcheck as [Ha He].
    apply Nat.eqb_eq in Ha. apply expected_matches_spec in He.
    apply registered_lookup_is_exact in Hlookup; [tauto|assumption].
  - intros [Hrow [Ha He]].
    apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hrow.
    rewrite Hrow, Ha, Nat.eqb_refl.
    apply expected_matches_spec in He. now rewrite He.
Qed.

Theorem constructor_nth_preserves_order_and_range :
  forall rows name arity expected domains result index,
  NoDup (map fst rows) ->
  constructor_view rows name arity expected = Some (domains, result) ->
  In (name, (domains, result)) rows /\
  (nth_error domains index = None <-> arity <= index).
Proof.
  intros rows name arity expected domains result index Hunique Hview.
  apply constructor_projection_is_exact in Hview; [|assumption].
  destruct Hview as [Hrow [Ha _]]. split; [assumption|rewrite Ha; apply nth_error_None].
Qed.

Definition unary_view (rows : Sorts) name binders :=
  match lookup name rows, binders with
  | Some (Function domain codomain false), 1 => Some (domain, codomain)
  | _, _ => None
  end.

Definition UnaryFields (rows : Sorts) name binders domain codomain :=
  In (name, Function domain codomain false) rows /\ binders = 1.

Theorem unary_projection_is_exact : forall rows name binders domain codomain,
  NoDup (map fst rows) ->
  (unary_view rows name binders = Some (domain, codomain) <->
   UnaryFields rows name binders domain codomain).
Proof.
  intros rows name binders domain codomain Hunique.
  unfold unary_view, UnaryFields. split.
  - destruct (lookup name rows) as [descriptor|] eqn:Hlookup; [|discriminate].
    destruct descriptor; try discriminate. destruct multiple; try discriminate.
    destruct binders as [|[|extra]]; try discriminate.
    intros H. inversion H; subst.
    apply registered_lookup_is_exact in Hlookup; [tauto|assumption].
  - intros [Hrow ->].
    apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hrow.
    now rewrite Hrow.
Qed.

Theorem multiple_function_cannot_supply_unary_binders : forall rows name domain codomain binders,
  NoDup (map fst rows) -> In (name, Function domain codomain true) rows ->
  unary_view rows name binders = None.
Proof.
  intros rows name domain codomain binders Hunique Hrow.
  apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hrow.
  unfold unary_view. now rewrite Hrow.
Qed.

Definition collection_view (rows : Sorts) name mode :=
  match lookup name rows with
  | Some (Collection PathMapKind key element) =>
      match mode with Some K.RuntimePathMapSet => key | _ => Some element end
  | Some (Collection _ _ element) =>
      match mode with None => Some element | Some _ => None end
  | _ => None
  end.

Inductive CollectionField (rows : Sorts) name : option K.RuntimePathMapMode -> nat -> Prop :=
| field_non_pathmap : forall kind key element,
    kind <> PathMapKind -> In (name, Collection kind key element) rows ->
    CollectionField rows name None element
| field_pathmap_set : forall key element,
    In (name, Collection PathMapKind (Some key) element) rows ->
    CollectionField rows name (Some K.RuntimePathMapSet) key
| field_pathmap_other : forall key element mode,
    mode <> Some K.RuntimePathMapSet ->
    In (name, Collection PathMapKind key element) rows ->
    CollectionField rows name mode element.

Theorem collection_projection_is_exact : forall rows name mode element,
  NoDup (map fst rows) ->
  (collection_view rows name mode = Some element <-> CollectionField rows name mode element).
Proof.
  intros rows name mode element Hunique. split.
  - unfold collection_view. destruct (lookup name rows) as [descriptor|] eqn:Hlookup;
      [|discriminate]. destruct descriptor; try discriminate.
    apply registered_lookup_is_exact in Hlookup; [|assumption].
    destruct kind.
    + destruct mode; [discriminate|]. intros H. inversion H; subst.
      eapply field_non_pathmap with (kind := ListKind); [discriminate|eassumption].
    + destruct mode; [discriminate|]. intros H. inversion H; subst.
      eapply field_non_pathmap with (kind := BagKind); [discriminate|eassumption].
    + destruct mode; [discriminate|]. intros H. inversion H; subst.
      eapply field_non_pathmap with (kind := SetKind); [discriminate|eassumption].
    + destruct mode; [discriminate|]. intros H. inversion H; subst.
      eapply field_non_pathmap with (kind := MapKind); [discriminate|eassumption].
    + destruct mode as [mode|].
      * destruct mode.
        -- intros H. inversion H; subst. eapply field_pathmap_other; [discriminate|eassumption].
        -- destruct key; [|discriminate]. intros H. inversion H; subst.
           eapply field_pathmap_set; eassumption.
        -- intros H. inversion H; subst. eapply field_pathmap_other; [discriminate|eassumption].
      * intros H. inversion H; subst. eapply field_pathmap_other; [discriminate|eassumption].
  - intros H. inversion H; subst; unfold collection_view.
    + match goal with Hr : In _ rows |- _ =>
        apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hr; rewrite Hr end.
      destruct kind; try reflexivity; contradiction.
    + match goal with Hr : In _ rows |- _ =>
        apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hr; rewrite Hr end.
      reflexivity.
    + match goal with Hr : In _ rows |- _ =>
        apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hr; rewrite Hr end.
      destruct mode as [[]|]; try reflexivity; contradiction.
Qed.

Definition product_view (rows : Sorts) name arity :=
  match lookup name rows with
  | Some (Product factors) => if Nat.eqb arity (length factors) then Some factors else None
  | _ => None
  end.

Theorem product_projection_is_exact : forall rows name arity factors,
  NoDup (map fst rows) ->
  (product_view rows name arity = Some factors <->
   In (name, Product factors) rows /\ arity = length factors).
Proof.
  intros rows name arity factors Hunique. unfold product_view. split.
  - destruct (lookup name rows) as [descriptor|] eqn:Hlookup; [|discriminate].
    destruct descriptor; try discriminate.
    destruct (Nat.eqb arity (length factors0)) eqn:Heq; [|discriminate].
    intros H. inversion H; subst.
    apply registered_lookup_is_exact in Hlookup; [|assumption].
    apply Nat.eqb_eq in Heq. tauto.
  - intros [Hrow ->].
    apply (proj2 (registered_lookup_is_exact _ _ _ _ Hunique)) in Hrow.
    now rewrite Hrow, Nat.eqb_refl.
Qed.

Theorem product_nth_preserves_order_and_range : forall rows name arity factors index,
  NoDup (map fst rows) -> product_view rows name arity = Some factors ->
  In (name, Product factors) rows /\
  (nth_error factors index = None <-> arity <= index).
Proof.
  intros rows name arity factors index Hunique Hview.
  apply product_projection_is_exact in Hview; [|assumption].
  destruct Hview as [Hrow ->]. split; [assumption|apply nth_error_None].
Qed.

Theorem unknown_descriptor_supplies_no_fields : forall rows name binders mode arity,
  ~ In name (map fst rows) ->
  unary_view rows name binders = None /\ collection_view rows name mode = None /\
  product_view rows name arity = None.
Proof.
  intros rows name binders mode arity Hmissing.
  pose proof (unknown_registered_name_is_refused _ _ _ Hmissing) as Hlookup.
  unfold unary_view, collection_view, product_view. rewrite Hlookup. auto.
Qed.

Theorem syntax_and_opaque_descriptors_do_not_supply_structural_fields :
  forall rows name descriptor binders mode arity,
  lookup name rows = Some descriptor -> (descriptor = Syntax \/ descriptor = Opaque) ->
  unary_view rows name binders = None /\ collection_view rows name mode = None /\
  product_view rows name arity = None.
Proof.
  intros rows name descriptor binders mode arity Hlookup [-> | ->];
    unfold unary_view, collection_view, product_view; rewrite Hlookup; auto.
Qed.

Theorem pathmap_set_projection_matches_existing_kernel : forall rows name key pair,
  NoDup (map fst rows) -> In (name, Collection PathMapKind (Some key) pair) rows ->
  collection_view rows name (Some K.RuntimePathMapSet) = Some key /\
  K.runtime_pathmap_child_contract (Some K.RuntimePathMapSet) key pair =
    K.RuntimePathMapHomogeneous key.
Proof.
  intros rows name key pair Hunique Hrow. split.
  - apply collection_projection_is_exact; [assumption|now apply field_pathmap_set with (element := pair)].
  - apply K.set_pathmap_uses_the_declared_key_sort.
Qed.

Theorem pathmap_map_projection_matches_existing_kernel : forall rows name key pair,
  NoDup (map fst rows) -> In (name, Collection PathMapKind (Some key) pair) rows ->
  collection_view rows name (Some K.RuntimePathMapMap) = Some pair /\
  K.runtime_pathmap_child_contract (Some K.RuntimePathMapMap) key pair =
    K.RuntimePathMapHomogeneous pair.
Proof.
  intros rows name key pair Hunique Hrow. split.
  - apply collection_projection_is_exact; [assumption|].
    eapply field_pathmap_other; [discriminate|eassumption].
  - apply K.map_pathmap_uses_the_declared_pair_sort.
Qed.

Theorem pathmap_neutral_and_absent_modes_keep_existing_final_restrictions : forall key pair,
  K.runtime_pathmap_child_contract (Some K.RuntimePathMapNeutral) key pair =
    K.RuntimePathMapFixed [] /\
  K.runtime_pathmap_child_contract None key pair = K.RuntimePathMapRemainderOnly.
Proof.
  intros. split; [apply K.neutral_pathmap_accepts_no_payload_children|
    apply K.mode_polymorphic_pathmap_is_remainder_only].
Qed.

Theorem missing_or_incompatible_edge_disables_all_descendants : forall left right rest,
  (left = None \/ right = None \/
    exists first second, left = Some first /\ right = Some second /\ first <> second) ->
  F.path_eligible (F.edge_eligible true (left, right)) rest = false.
Proof.
  intros left right rest Hbad.
  assert (Hdisabled : F.edge_eligible true (left, right) = false).
  { destruct Hbad as [-> | [-> | [first [second [-> [-> Hneq]]]]]].
    - reflexivity.
    - destruct left; reflexivity.
    - simpl. apply Nat.eqb_neq. exact Hneq. }
  rewrite Hdisabled. apply F.disabled_context_disables_all_descendants.
Qed.

Theorem matching_descriptor_evidence_keeps_existing_path_admission : forall evidence,
  Forall F.MatchingSortEvidence evidence -> F.path_eligible true evidence = true.
Proof.
  intros evidence H. apply F.path_eligibility_requires_matching_sort_evidence. auto.
Qed.

End RewriteFamilyDescriptors.

Print Assumptions RewriteFamilyDescriptors.registered_lookup_is_exact.
Print Assumptions RewriteFamilyDescriptors.unknown_registered_name_is_refused.
Print Assumptions RewriteFamilyDescriptors.constructor_projection_is_exact.
Print Assumptions RewriteFamilyDescriptors.constructor_nth_preserves_order_and_range.
Print Assumptions RewriteFamilyDescriptors.unary_projection_is_exact.
Print Assumptions RewriteFamilyDescriptors.multiple_function_cannot_supply_unary_binders.
Print Assumptions RewriteFamilyDescriptors.collection_projection_is_exact.
Print Assumptions RewriteFamilyDescriptors.product_projection_is_exact.
Print Assumptions RewriteFamilyDescriptors.product_nth_preserves_order_and_range.
Print Assumptions RewriteFamilyDescriptors.unknown_descriptor_supplies_no_fields.
Print Assumptions RewriteFamilyDescriptors.syntax_and_opaque_descriptors_do_not_supply_structural_fields.
Print Assumptions RewriteFamilyDescriptors.pathmap_set_projection_matches_existing_kernel.
Print Assumptions RewriteFamilyDescriptors.pathmap_map_projection_matches_existing_kernel.
Print Assumptions RewriteFamilyDescriptors.pathmap_neutral_and_absent_modes_keep_existing_final_restrictions.
Print Assumptions RewriteFamilyDescriptors.missing_or_incompatible_edge_disables_all_descendants.
Print Assumptions RewriteFamilyDescriptors.matching_descriptor_evidence_keeps_existing_path_admission.
