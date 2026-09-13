(** Concrete finite-height comparison-key family for generated constructors.
    A signature row is one existing comparison constructor, in numeric
    comparison-index order. Fields retain their original positional order.
    Scope rows flatten only their comparison positions: prefields, the native
    pattern verdict, then the body child. This is a proof-only typed recipe,
    not another Rholang AST, parser, runtime key allocation or comparator.

    Empty carriers represent refused rows and exhausted height; they never
    grant source admission. A recursively successful source projection and
    actual generated-traversal factorization are still required to use these
    keys for a source term. The signature must be bound to the existing
    census/emitter, including actual ordinals, not alphabetical labels.

    Orders are constructed solely by the existing product/sum/list laws and
    the concrete audited native leaf recipes. The bundled proof is a stored
    result of those constructions, not an assumed source-comparator law.
    Map keys are sorted pair-class lists, without a length-first prefix.
    Canonicalization uses the existing merge model and retains its option
    result; its totality proof excludes failure without a default/fallback. *)
From Stdlib Require Import List Bool ZArith Sorting.Sorted Sorting.Permutation.
From RuntimeGrammar Require Import SemanticComparisonLaws SemanticResultMerge.
From RhoBridge Require Import AdmittedNativeComparisonFactors AdmittedStructuralKeyHash.
Import ListNotations.

Module GeneratedConstructorComparisonClasses.
Record Ordered := {
  carrier : Type;
  comparison_function : carrier -> carrier -> comparison;
  comparison_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws comparison_function
}.
Definition pack {A : Type} (cmp : A -> A -> comparison) (law : SemanticComparisonLaws.SemanticComparisonLaws.Laws cmp) : Ordered :=
  {| carrier := A; comparison_function := cmp; comparison_laws := law |}.
Definition empty_compare (x y : Empty_set) : comparison := match x with end.
Lemma empty_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws empty_compare.
Proof. constructor; intros x; destruct x. Qed.
Definition empty_order := pack empty_compare empty_laws.
Definition unit_compare (_ _ : unit) := Eq.
Lemma unit_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws unit_compare.
Proof.
  constructor.
  - intros [] []; split; reflexivity.
  - intros [] []; reflexivity.
  - intros [] [] [] c H1 H2. exact H1.
Qed.
Definition unit_order := pack unit_compare unit_laws.
Definition pair_order (a b : Ordered) : Ordered :=
  pack (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare (comparison_function a) (comparison_function b))
    (SemanticComparisonLaws.SemanticComparisonLaws.pair_laws (carrier a) (carrier b) _ _ (comparison_laws a) (comparison_laws b)).
Definition sum_order (a b : Ordered) : Ordered :=
  pack (SemanticComparisonLaws.SemanticComparisonLaws.sum_compare (comparison_function a) (comparison_function b))
    (SemanticComparisonLaws.SemanticComparisonLaws.sum_laws (carrier a) (carrier b) _ _ (comparison_laws a) (comparison_laws b)).
Definition list_order (a : Ordered) : Ordered :=
  pack (list_compare (comparison_function a))
    (SemanticComparisonLaws.SemanticComparisonLaws.list_laws (carrier a) _ (comparison_laws a)).
Definition nat_order := pack Nat.compare SemanticComparisonLaws.SemanticComparisonLaws.natural_laws.
Definition byte_order := pack AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.bytes_compare AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.bytes_laws.

Inductive Atom := Signed | Boolean | Bytes | VariableIdentity | GuestFlt | SinglePattern | MultiPattern.
Definition atom_order a : Ordered := match a with
  | Signed => pack Z.compare AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.signed_laws
  | Boolean | SinglePattern => nat_order
  | Bytes => byte_order
  | VariableIdentity => pack AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.var_key_compare AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.var_key_laws
  | GuestFlt => pack AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.flt_key_compare AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.flt_key_laws
  | MultiPattern => pack AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.multi_pattern_key_compare AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.multi_pattern_key_laws
  end.
Definition atom_source_type atom : Type := match atom with
  | Signed => Z | Boolean => bool | Bytes => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString
  | VariableIdentity => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.MonikerVar | GuestFlt => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltNode
  | SinglePattern => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder | MultiPattern => list AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder end.

Section NativeViews.
Variables uid_digest binder_digest : nat -> nat.
Definition atom_view (atom : Atom) : atom_source_type atom -> carrier (atom_order atom) :=
  match atom return atom_source_type atom -> carrier (atom_order atom) with
  | Signed => fun x => x
  | Boolean => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.bool_key
  | Bytes => fun x => x
  | VariableIdentity => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.var_key uid_digest
  | GuestFlt => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.flt_key uid_digest
  | SinglePattern => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.binder_key binder_digest
  | MultiPattern => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.multi_pattern_key binder_digest
  end.
Definition atom_source_compare (atom : Atom) :
    atom_source_type atom -> atom_source_type atom -> comparison :=
  match atom return atom_source_type atom -> atom_source_type atom -> comparison with
  | Signed => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.signed_source_compare
  | Boolean => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.bool_source_compare
  | Bytes => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.string_source_compare
  | VariableIdentity => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.ordvar_source_compare uid_digest
  | GuestFlt => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.flt_source_compare uid_digest
  | SinglePattern => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.single_pattern_source_compare binder_digest
  | MultiPattern => AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.multi_pattern_source_compare binder_digest
  end.
Theorem all_native_recipe_results_factor_through_their_concrete_keys :
  forall atom x y,
  atom_source_compare atom x y =
    comparison_function (atom_order atom) (atom_view atom x) (atom_view atom y).
Proof.
  intros atom. destruct atom; intros x y;
    cbn [atom_source_compare atom_order atom_view comparison_function pack nat_order byte_order].
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.signed_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.bool_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.string_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.ordvar_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.flt_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.single_pattern_factor.
  - apply AdmittedNativeComparisonFactors.AdmittedNativeComparisonFactors.multi_pattern_factor.
Qed.
End NativeViews.

Section SignatureFamily.
Context {Cat : Type}.
Inductive BaseField :=
  | Native (atom : Atom) | Child (category : Cat)
  | Vector (category : Cat) | MapPairs (category : Cat).
Record Field := { field_base : BaseField; field_optional : bool }.
Record Row := { row_ordinal : nat; row_admitted : bool; row_fields : list Field }.
Variable signature : Cat -> list Row.
Definition signature_ordinals_ordered :=
  forall category, StronglySorted Nat.lt (map row_ordinal (signature category)).
Definition base_order (children : Cat -> Ordered) field : Ordered :=
  match field with
  | Native atom => atom_order atom
  | Child c => children c
  | Vector c => list_order (children c)
  | MapPairs c => list_order (pair_order (children c) (children c))
  end.
Definition field_order children field :=
  if field_optional field then sum_order unit_order (base_order children (field_base field))
  else base_order children (field_base field).
Fixpoint fields_order children fields : Ordered :=
  match fields with
  | [] => unit_order
  | field :: rest => pair_order (field_order children field) (fields_order children rest)
  end.
Definition row_order children row :=
  if row_admitted row then fields_order children (row_fields row) else empty_order.
Fixpoint rows_order children rows : Ordered :=
  match rows with
  | [] => empty_order
  | row :: rest => sum_order (row_order children row) (rows_order children rest)
  end.
Fixpoint category_order (height : nat) : Cat -> Ordered :=
  match height with
  | 0 => fun _ => empty_order
  | S previous => fun c => rows_order (category_order previous) (signature c)
  end.
Definition Key height category := carrier (category_order height category).
Definition key_compare height category := comparison_function (category_order height category).
Theorem finite_height_key_laws : forall height category, SemanticComparisonLaws.SemanticComparisonLaws.Laws (key_compare height category).
Proof. intros height category. exact (comparison_laws (category_order height category)). Qed.
Theorem zero_height_has_no_category_key : forall category, Key 0 category -> False.
Proof. intros category key. destruct key. Qed.
Theorem a_refused_row_has_no_key : forall children row,
  row_admitted row = false -> carrier (row_order children row) -> False.
Proof. intros children row REFUSED. unfold row_order. rewrite REFUSED. intro key. destruct key. Qed.
Theorem map_field_key_order_is_pair_list_lexicographic : forall children category left right,
  comparison_function (base_order children (MapPairs category)) left right =
    list_compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare (comparison_function (children category))
      (comparison_function (children category))) left right.
Proof. reflexivity. Qed.
End SignatureFamily.

Section ExistingCanonicalization.
Variable order : Ordered.
Definition pure_key_compare (a b : carrier order) (_ : unit) :=
  (Some (comparison_function order a b), tt).
Definition canonical_result (values : list (carrier order)) :=
  fst (SemanticResultMerge.SemanticResultMerge.sort pure_key_compare values tt).
Lemma pure_key_comparison_responds : forall a b state,
  exists decision next, pure_key_compare a b state = (Some decision, next).
Proof. intros. exists (comparison_function order a b), tt. reflexivity. Qed.
Theorem canonical_result_is_always_present : forall values,
  exists output, canonical_result values = Some output.
Proof.
  intro values.
  destruct (SemanticResultMerge.SemanticResultMerge.sort_termination_index_suffices pure_key_compare
    pure_key_comparison_responds values tt) as [output [last SORT]].
  exists output. unfold canonical_result. rewrite SORT. reflexivity.
Qed.
Lemma canonical_success_is_the_existing_sort_result : forall values output,
  canonical_result values = Some output ->
  SemanticResultMerge.SemanticResultMerge.sort pure_key_compare values tt = (Some output, tt).
Proof.
  intros values output RESULT. unfold canonical_result in RESULT.
  destruct (SemanticResultMerge.SemanticResultMerge.sort pure_key_compare values tt) as [result []] eqn:SORT.
  cbn [fst] in RESULT. subst result. reflexivity.
Qed.
Theorem canonical_result_has_exact_sorted_permutation_evidence : forall values output,
  canonical_result values = Some output ->
  StronglySorted (fun a b => comparison_function order a b <> Gt) output /\
  Permutation values output.
Proof.
  intros values output RESULT.
  pose proof (canonical_success_is_the_existing_sort_result values output RESULT) as SORT.
  assert (FAITHFUL : forall a b state decision next,
    pure_key_compare a b state = (Some decision, next) ->
    comparison_function order a b = decision).
  { intros a b state decision next RESPONSE. injection RESPONSE as E REST. exact E. }
  split.
  - eapply SemanticResultMerge.SemanticResultMerge.sort_is_sorted; [| |exact SORT].
    + apply (SemanticComparisonLaws.SemanticComparisonLaws.not_greater_is_transitive (carrier order)
        (comparison_function order) (comparison_laws order)).
    + exact (SemanticResultMerge.SemanticResultMerge.exact_key_comparison_is_sound pure_key_compare (carrier order)
        (fun x => x) (comparison_function order)
        (SemanticComparisonLaws.SemanticComparisonLaws.comparison_opposite (comparison_laws order)) FAITHFUL).
  - eapply SemanticResultMerge.SemanticResultMerge.sort_preserves_occurrences. exact SORT.
Qed.
End ExistingCanonicalization.

Print Assumptions empty_laws.
Print Assumptions unit_laws.
Print Assumptions all_native_recipe_results_factor_through_their_concrete_keys.
Print Assumptions finite_height_key_laws.
Print Assumptions zero_height_has_no_category_key.
Print Assumptions a_refused_row_has_no_key.
Print Assumptions map_field_key_order_is_pair_list_lexicographic.
Print Assumptions canonical_result_is_always_present.
Print Assumptions canonical_success_is_the_existing_sort_result.
Print Assumptions canonical_result_has_exact_sorted_permutation_evidence.
End GeneratedConstructorComparisonClasses.
