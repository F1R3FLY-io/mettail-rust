(** Typed original-source projections into the finite constructor key family.

    Term category below denotes the existing immutable typed category borrow;
    it is not defined recursively here. An observation selects a row of the
    actual signature and borrows its original fields. Products below are only
    the finite field telescope for that row. Vec and Map lists project the
    original element/entry order; they do not construct another source AST.

    AUDITED SOURCE BINDING STILL REQUIRED: observe must be instantiated from
    collect_category_variants / generate_variant_index_fn and the same enum
    field projections used by iterative_cmp.rs. The actual census already
    emits rows in variants.iter().enumerate() order, not label-map order.
    Scope observations flatten prefields, native pattern, then borrowed body.
    Optional opaque leaves remain refused under the current shallow profile.
    A supplied observer is not, by itself, a proof of this Rust association.

    These definitions establish successful projection and constructor-tag
    correspondence. They neither assume nor prove a complete ArmResult/core
    result law. The remaining finite-height source factor must instantiate
    GeneratedChildTraversal's actual arm/core/disposal witnesses, using the
    successful lower-height projections for ANY two child operands, including
    comparisons within one Map sort roster. Native reached-yield extraction,
    pair/unit-lex results and sorted-class uniqueness supply the Map case.

    No runtime key allocation, recursive Value datatype, alternate comparator
    or sorter is introduced. Canonicalization retains the existing sort's
    option result; its already proved totality rules out a missing result. *)
From Stdlib Require Import List Arith.PeanoNat Bool Sorting.Sorted.
From RhoBridge Require Import GeneratedConstructorComparisonClasses.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.

Module GeneratedConstructorSourceProjection.

Fixpoint project_list {A B : Type} (project : A -> option B) (values : list A)
    : option (list B) :=
  match values with
  | [] => Some []
  | value :: rest =>
      match project value, project_list project rest with
      | Some key, Some keys => Some (key :: keys)
      | _, _ => None
      end
  end.
Definition project_pair {A B : Type} (left : option A) (right : option B)
    : option (A * B) :=
  match left, right with Some x, Some y => Some (x, y) | _, _ => None end.

Theorem successful_list_projection_keeps_every_original_position :
  forall (A B : Type) (project : A -> option B) values keys,
  project_list project values = Some keys ->
  Forall2 (fun value key => project value = Some key) values keys.
Proof.
  intros A B project values. induction values as [|value rest IH]; intros keys RESULT.
  - cbn [project_list] in RESULT. inversion RESULT; constructor.
  - cbn [project_list] in RESULT.
    destruct (project value) as [key|] eqn:HEAD; try discriminate.
    destruct (project_list project rest) as [tail|] eqn:TAIL; try discriminate.
    inversion RESULT; subst keys. constructor; [exact HEAD | now apply IH].
Qed.
Theorem successful_pair_projection_keeps_both_original_positions :
  forall (A B : Type) (left : option A) (right : option B) x y,
  project_pair left right = Some (x, y) -> left = Some x /\ right = Some y.
Proof.
  intros A B [a|] [b|] x y RESULT; try discriminate.
  inversion RESULT; subst. split; reflexivity.
Qed.

Section SignatureProjection.
Context {Cat : Type}.
Variable signature : Cat -> list (@Row Cat).
Variable Term : Cat -> Type.
Variables uid_digest binder_digest : nat -> nat.

(** This is an index/path through the finite existing signature, not a term. *)
Inductive RowPath : list (@Row Cat) -> @Row Cat -> Type :=
| RowHere : forall row rest, RowPath (row :: rest) row
| RowThere : forall head rest row, RowPath rest row -> RowPath (head :: rest) row.

Fixpoint inject_row (children : Cat -> Ordered) {rows row}
    (path : RowPath rows row) :
    carrier (row_order children row) -> carrier (rows_order children rows) :=
  match path in RowPath selected_rows selected_row return
    carrier (row_order children selected_row) -> carrier (rows_order children selected_rows)
  with
  | RowHere selected_row rest => fun payload => inl payload
  | RowThere head rest selected_row tail => fun payload =>
      inr (inject_row children tail payload)
  end.

Fixpoint key_ordinal (children : Cat -> Ordered) (rows : list (@Row Cat)) :
    carrier (rows_order children rows) -> nat :=
  match rows as selected_rows return carrier (rows_order children selected_rows) -> nat with
  | [] => fun impossible => match impossible with end
  | row :: rest => fun key =>
      match key with inl _ => row_ordinal row | inr tail => key_ordinal children rest tail end
  end.

Theorem injected_key_retains_its_actual_ordinal : forall children rows row
    (path : RowPath rows row) payload,
  key_ordinal children rows (inject_row children path payload) = row_ordinal row.
Proof. intros children rows row path. induction path; intro payload; cbn; auto. Qed.

Theorem same_row_injection_preserves_field_comparison : forall children rows row
    (path : RowPath rows row) left right,
  comparison_function (rows_order children rows)
    (inject_row children path left) (inject_row children path right) =
  comparison_function (row_order children row) left right.
Proof. intros children rows row path. induction path; intros left right; cbn; auto. Qed.

Lemma every_key_ordinal_belongs_to_the_original_signature : forall children rows key,
  In (key_ordinal children rows key) (map row_ordinal rows).
Proof.
  intros children rows. induction rows as [|row rest IH]; intro key.
  - destruct key.
  - destruct key as [payload|tail]; cbn [key_ordinal map];
      [left; reflexivity | right; apply IH].
Qed.

Theorem different_constructor_keys_compare_by_actual_ordinal : forall children rows,
  StronglySorted Nat.lt (map row_ordinal rows) -> forall left right,
  key_ordinal children rows left <> key_ordinal children rows right ->
  comparison_function (rows_order children rows) left right =
    Nat.compare (key_ordinal children rows left) (key_ordinal children rows right).
Proof.
  intros children rows. induction rows as [|row rest IH]; intros ORDER left right DIFFERENT.
  - destruct left.
  - change (StronglySorted Nat.lt (row_ordinal row :: map row_ordinal rest)) in ORDER.
    destruct (StronglySorted_inv ORDER) as [TAIL BOUND].
    destruct left as [left|left]; destruct right as [right|right].
    + exfalso. apply DIFFERENT. reflexivity.
    + change (Lt = Nat.compare (row_ordinal row) (key_ordinal children rest right)).
      symmetry. apply Nat.compare_lt_iff. rewrite Forall_forall in BOUND.
      apply BOUND. apply every_key_ordinal_belongs_to_the_original_signature.
    + change (Gt = Nat.compare (key_ordinal children rest left) (row_ordinal row)).
      symmetry. apply Nat.compare_gt_iff. rewrite Forall_forall in BOUND.
      apply BOUND. apply every_key_ordinal_belongs_to_the_original_signature.
    + apply IH; [exact TAIL | exact DIFFERENT].
Qed.

Definition source_base_type (base : @BaseField Cat) : Type := match base with
  | Native atom => atom_source_type atom
  | Child category => Term category
  | Vector category => list (Term category)
  | MapPairs category => list (Term category * Term category)
  end.
Definition source_field_type (field : @Field Cat) : Type :=
  if field_optional field then option (source_base_type (field_base field))
  else source_base_type (field_base field).
Fixpoint source_fields_type (fields : list (@Field Cat)) : Type := match fields with
  | [] => unit
  | field :: rest => (source_field_type field * source_fields_type rest)%type
  end.
Definition source_row_type (row : @Row Cat) : Type :=
  if row_admitted row then source_fields_type (row_fields row) else unit.
Definition SourceObservation category :=
  { row : @Row Cat & (RowPath (signature category) row * source_row_type row)%type }.

(** Actual enum projection binding: no comparison result occurs in its type. *)
Variable observe : forall category, Term category -> SourceObservation category.

Definition project_base (children : Cat -> Ordered)
    (next : forall category, Term category -> option (carrier (children category)))
    (base : @BaseField Cat) : source_base_type base -> option (carrier (base_order children base)) :=
  match base return source_base_type base -> option (carrier (base_order children base)) with
  | Native atom => fun value => Some (atom_view uid_digest binder_digest atom value)
  | Child category => next category
  | Vector category => project_list (next category)
  | MapPairs category => fun entries =>
      match project_list
        (fun entry => project_pair (next category (fst entry)) (next category (snd entry))) entries with
      | Some keys => canonical_result (pair_order (children category) (children category)) keys
      | None => None
      end
  end.

Theorem successful_native_field_projection_has_the_original_leaf_result :
  forall children next atom left right left_key right_key,
  project_base children next (Native atom) left = Some left_key ->
  project_base children next (Native atom) right = Some right_key ->
  atom_source_compare uid_digest binder_digest atom left right =
    comparison_function (atom_order atom) left_key right_key.
Proof.
  intros children next atom left right left_key right_key LEFT RIGHT.
  cbn [project_base] in LEFT, RIGHT. inversion LEFT; inversion RIGHT; subst.
  apply all_native_recipe_results_factor_through_their_concrete_keys.
Qed.

Theorem successful_vector_projection_keeps_every_child_view :
  forall children next category values keys,
  project_base children next (Vector category) values = Some keys ->
  Forall2 (fun value key => next category value = Some key) values keys.
Proof.
  intros children next category values keys RESULT.
  apply successful_list_projection_keeps_every_original_position. exact RESULT.
Qed.

Theorem successful_map_projection_keeps_original_pairing_before_canonicalization :
  forall children next category entries canonical,
  project_base children next (MapPairs category) entries = Some canonical ->
  exists paired_keys,
  Forall2 (fun entry keys =>
    next category (fst entry) = Some (fst keys) /\
    next category (snd entry) = Some (snd keys)) entries paired_keys /\
  canonical_result (pair_order (children category) (children category)) paired_keys = Some canonical.
Proof.
  intros children next category entries canonical RESULT.
  cbn [project_base] in RESULT.
  destruct (project_list
    (fun entry => project_pair (next category (fst entry)) (next category (snd entry))) entries)
    as [paired_keys|] eqn:PAIRED; try discriminate.
  exists paired_keys. split; [|exact RESULT].
  pose proof (successful_list_projection_keeps_every_original_position _ _ _ _ _ PAIRED) as PAIRS.
  clear PAIRED RESULT.
  induction PAIRS as [|entry keys entries rest HEAD TAIL IH].
  - constructor.
  - constructor; [|exact IH]. destruct keys as [left_key right_key].
    exact (successful_pair_projection_keeps_both_original_positions _ _ _ _ _ _ HEAD).
Qed.

Definition project_field (children : Cat -> Ordered)
    (next : forall category, Term category -> option (carrier (children category)))
    (field : @Field Cat) : source_field_type field -> option (carrier (field_order children field)).
Proof.
  destruct field as [base optional]. destruct optional;
    cbn [source_field_type field_order field_optional field_base].
  - intro source. destruct source as [value|].
    + destruct (project_base children next base value) as [key|].
      * exact (Some (inr key)).
      * exact None.
    + exact (Some (inl tt)).
  - exact (project_base children next base).
Defined.

Fixpoint project_fields (children : Cat -> Ordered)
    (next : forall category, Term category -> option (carrier (children category)))
    (fields : list (@Field Cat)) : source_fields_type fields -> option (carrier (fields_order children fields)) :=
  match fields as selected_fields return
    source_fields_type selected_fields -> option (carrier (fields_order children selected_fields)) with
  | [] => fun _ => Some tt
  | field :: rest => fun source => project_pair
      (project_field children next field (fst source))
      (project_fields children next rest (snd source))
  end.

Definition project_row (children : Cat -> Ordered)
    (next : forall category, Term category -> option (carrier (children category)))
    (row : @Row Cat) : source_row_type row -> option (carrier (row_order children row)).
Proof.
  destruct row as [ordinal admitted fields]. destruct admitted;
    cbn [source_row_type row_order row_admitted row_fields].
  - exact (project_fields children next fields).
  - exact (fun _ => None).
Defined.

Theorem successful_row_projection_requires_shallow_admission :
  forall children next row source key,
  project_row children next row source = Some key -> row_admitted row = true.
Proof.
  intros children next [ordinal admitted fields]. destruct admitted; intros source key RESULT.
  - reflexivity.
  - discriminate RESULT.
Qed.

Fixpoint source_view (height : nat) (category : Cat) (term : Term category) :
    option (Key signature height category) :=
  match height as selected_height return option (Key signature selected_height category) with
  | 0 => None
  | S previous =>
      match observe category term with
      | existT _ row (path, source) =>
          option_map (inject_row (category_order signature previous) path)
            (project_row (category_order signature previous)
              (fun category child => source_view previous category child) row source)
      end
  end.

Definition Domain height category (term : Term category) :=
  exists key, source_view height category term = Some key.
Definition observed_ordinal category (term : Term category) :=
  match observe category term with existT _ row _ => row_ordinal row end.

Theorem zero_height_rejects_every_original_operand : forall category term,
  source_view 0 category term = None.
Proof. reflexivity. Qed.

Theorem successful_source_view_exposes_the_exact_original_row :
  forall height category term key,
  source_view (S height) category term = Some key ->
  exists (row : @Row Cat) (path : RowPath (signature category) row)
    (source : source_row_type row)
    (payload : carrier (row_order (category_order signature height) row)),
  observe category term = existT _ row (path, source) /\
  project_row (category_order signature height)
    (fun category child => source_view height category child) row source = Some payload /\
  key = inject_row (category_order signature height) path payload.
Proof.
  intros height category term key RESULT. cbn [source_view] in RESULT.
  destruct (observe category term) as [row [path source]] eqn:OBSERVED.
  destruct (project_row (category_order signature height)
    (fun category child => source_view height category child) row source)
    as [payload|] eqn:PROJECTED; try discriminate.
  inversion RESULT; subst key. exists row, path, source, payload.
  repeat split; assumption || reflexivity.
Qed.

Theorem successful_source_view_retains_the_original_ordinal :
  forall height category term key,
  source_view (S height) category term = Some key ->
  key_ordinal (category_order signature height) (signature category) key =
    observed_ordinal category term.
Proof.
  intros height category term key RESULT.
  destruct (successful_source_view_exposes_the_exact_original_row
    height category term key RESULT) as [row [path [source [payload [OBSERVED [PROJECTED KEY]]]]]].
  subst key. rewrite injected_key_retains_its_actual_ordinal.
  unfold observed_ordinal. rewrite OBSERVED. reflexivity.
Qed.

Theorem source_constructor_mismatch_factors_without_an_arm_result_premise :
  signature_ordinals_ordered signature -> forall height category left right left_key right_key,
  source_view (S height) category left = Some left_key ->
  source_view (S height) category right = Some right_key ->
  observed_ordinal category left <> observed_ordinal category right ->
  key_compare signature (S height) category left_key right_key =
    Nat.compare (observed_ordinal category left) (observed_ordinal category right).
Proof.
  intros ORDER height category left right left_key right_key LEFT RIGHT DIFFERENT.
  pose proof (successful_source_view_retains_the_original_ordinal
    height category left left_key LEFT) as LEFT_TAG.
  pose proof (successful_source_view_retains_the_original_ordinal
    height category right right_key RIGHT) as RIGHT_TAG.
  change (comparison_function (rows_order (category_order signature height) (signature category))
    left_key right_key = Nat.compare (observed_ordinal category left) (observed_ordinal category right)).
  rewrite <- LEFT_TAG, <- RIGHT_TAG.
  apply different_constructor_keys_compare_by_actual_ordinal.
  - apply ORDER.
  - now rewrite LEFT_TAG, RIGHT_TAG.
Qed.

End SignatureProjection.

Print Assumptions successful_list_projection_keeps_every_original_position.
Print Assumptions successful_pair_projection_keeps_both_original_positions.
Print Assumptions injected_key_retains_its_actual_ordinal.
Print Assumptions same_row_injection_preserves_field_comparison.
Print Assumptions every_key_ordinal_belongs_to_the_original_signature.
Print Assumptions different_constructor_keys_compare_by_actual_ordinal.
Print Assumptions successful_native_field_projection_has_the_original_leaf_result.
Print Assumptions successful_vector_projection_keeps_every_child_view.
Print Assumptions successful_map_projection_keeps_original_pairing_before_canonicalization.
Print Assumptions successful_row_projection_requires_shallow_admission.
Print Assumptions zero_height_rejects_every_original_operand.
Print Assumptions successful_source_view_exposes_the_exact_original_row.
Print Assumptions successful_source_view_retains_the_original_ordinal.
Print Assumptions source_constructor_mismatch_factors_without_an_arm_result_premise.
End GeneratedConstructorSourceProjection.
