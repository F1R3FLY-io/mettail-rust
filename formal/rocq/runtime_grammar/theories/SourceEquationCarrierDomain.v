(** * Typed domains of the source equation section

    The equation sort and the selected carrier sort are independent.  This
    file describes the finite typed operator signatures already retained by
    the semantic image; it is neither a new evaluator nor a new normalizer.
    RuntimeSortShape is reused without its old binary-product restriction.
    Pair-entry and mode types below are INTERNAL child contracts: they do not
    add source sorts or permit a PathMap marker as an ordinary guest value.

    The domain invariant for keyed collections is local: the existing
    observation distinguishes sibling KEYS.  Values and multiplicities are
    never discarded.  Equation-inert key sorts are sufficient to establish
    this invariant from an ordinary canonical input.  A different domain may
    establish the same precise key-injectivity obligation directly.  Failing
    this sufficient check does not reject a language or change collision
    policy.

    Source/image ownership, resolved operator labels, and the signature-table
    projection are bound by the admission layer, not authenticated by a
    natural-number label.  This model proves closure from those LOCAL tables
    and the existing equation-role signatures.  It does not assume a completed
    section, a whole-builder theorem, or physical matcher correctness.
*)

From Stdlib Require Import List PeanoNat Lia Sorting.Permutation.
From RuntimeGrammar Require Import SourceEquationCollectionUniqueness
  ExecutableTheoryCore AuthoredSourceImage.
Import ListNotations.

Module SourceEquationCarrierDomain.
Module U := SourceEquationCollectionUniqueness.
Module X := U.X.
Module E := U.E.
Module C := U.C.
Module K := E.K.
Module Core := ExecutableTheoryCore.
Module A := AuthoredSourceImage.
Module T := A.T.
Import K.
Definition Term := E.Term.

(** The source projection keeps full function and product metadata.  The
    existing constructor/function cases are reused verbatim.  Only product
    arity is generalized; PathMap's separate mode contract is retained. *)
Definition rich_runtime_signature sorts operator :=
  match operator with
  | K.RuntimeProductNode sort =>
      match nth_error sorts sort with
      | Some (K.RuntimeProduct factors) =>
          Some {| K.runtime_result_sort := sort;
                  K.runtime_child_contract := K.FixedChildren factors |}
      | _ => None
      end
  | _ => K.runtime_operator_signature sorts operator
  end.

Theorem arbitrary_product_keeps_every_factor : forall sorts sort factors,
  nth_error sorts sort = Some (K.RuntimeProduct factors) ->
  rich_runtime_signature sorts (K.RuntimeProductNode sort) =
    Some {| K.runtime_result_sort := sort;
            K.runtime_child_contract := K.FixedChildren factors |}.
Proof. intros. simpl. now rewrite H. Qed.

Theorem substitution_keeps_reverse_function_dependency :
  forall sorts function domain codomain multiple,
  nth_error sorts function = Some (K.RuntimeFunction domain codomain multiple) ->
  rich_runtime_signature sorts (K.RuntimeSubstitution function) =
    Some {| K.runtime_result_sort := codomain;
            K.runtime_child_contract := K.FixedChildren [function; domain] |}.
Proof. apply K.substitution_signature_recovers_the_function_domain_and_codomain. Qed.

Theorem abstraction_keeps_binder_then_body :
  forall sorts function domain codomain multiple,
  nth_error sorts function = Some (K.RuntimeFunction domain codomain multiple) ->
  rich_runtime_signature sorts (K.RuntimeAbstraction function) =
    Some {| K.runtime_result_sort := function;
            K.runtime_child_contract := K.FixedChildren [domain; codomain] |}.
Proof. apply K.abstraction_signature_places_the_binder_before_the_body. Qed.

Inductive ChildType :=
| ValueType (sort : Core.SortId)
| EntryType (pair key value : nat)
| ModeType (marker : nat).

(** Fixed includes exact constructor/literal/abstraction/substitution payloads.
    Their authenticated payload remains in the label table.  List is an
    ordered homogeneous operator.  Bag/Set are unordered homogeneous ones.
    Product is separate so entry readback cannot mistake a constructor of the
    pair sort for the physical Product operator required by Map admission. *)
Inductive Shape :=
| FixedShape (result : Core.SortId) (arguments : list Core.SortId)
| ProductShape (result : Core.SortId) (factors : list Core.SortId)
| ListShape (result element : Core.SortId)
| BagShape (result element : Core.SortId)
| SetShape (result element : Core.SortId)
| MapShape (result pair key value : nat)
| PathMapShape (result pair key value neutral set map : nat)
| MarkerShape.

(** Projection of existing checked tables, not a second typing evaluator.
    Numeric carrier/kind codes are the already-decoded table convention.
    Exact literals remain in T.LiteralOperator, not in a replacement ground
    atom.  A Map comprehension is not a retained ground operator: its existing
    SourceApply/BuildMap construction supplies a collection with one of these
    child contracts, retaining every source column, parameter and remainder.
    The owner-bound projection itself is discharged by source admission. *)
Section SourceProjection.
  Variable source_sorts : K.RuntimeSortTable.
  Variable constructors : list Core.ConstructorDecl.
  Variable kind_code : K.RuntimeCollectionKind -> nat.
  Variable literal_code : A.S.Literal -> nat.
  Variable product_label : Core.SortId -> nat.
  Variable mode_label : Core.SortId -> K.RuntimePathMapMode -> nat.

  Inductive SourceOperatorShape : T.Operator -> Shape -> Prop :=
  | source_constructor_shape : forall constructor declaration,
      nth_error constructors constructor = Some declaration ->
      SourceOperatorShape (T.ConstructorOperator constructor)
        (FixedShape (Core.constructor_codomain declaration) (Core.constructor_domain declaration))
  | source_abstraction_shape : forall function domain codomain multiple,
      nth_error source_sorts function = Some (K.RuntimeFunction domain codomain multiple) ->
      SourceOperatorShape (T.AbstractionOperator function) (FixedShape function [domain; codomain])
  | source_substitution_shape : forall function domain codomain multiple,
      nth_error source_sorts function = Some (K.RuntimeFunction domain codomain multiple) ->
      SourceOperatorShape (T.SubstitutionOperator codomain function) (FixedShape codomain [function; domain])
  | source_product_shape : forall sort factors,
      nth_error source_sorts sort = Some (K.RuntimeProduct factors) ->
      SourceOperatorShape (T.ProductOperator sort) (ProductShape sort factors)
  | source_literal_shape : forall sort literal,
      nth_error source_sorts sort = Some (K.RuntimeSyntax (Some (literal_code literal))) ->
      SourceOperatorShape (T.LiteralOperator sort literal) (FixedShape sort [])
  | source_list_shape : forall sort element,
      nth_error source_sorts sort = Some (K.RuntimeCollection (kind_code K.AdmissionList) None element) ->
      SourceOperatorShape (T.CollectionOperator sort element K.AdmissionList) (ListShape sort element)
  | source_bag_shape : forall sort element,
      nth_error source_sorts sort = Some (K.RuntimeCollection (kind_code K.AdmissionBag) None element) ->
      SourceOperatorShape (T.CollectionOperator sort element K.AdmissionBag) (BagShape sort element)
  | source_set_shape : forall sort element,
      nth_error source_sorts sort = Some (K.RuntimeCollection (kind_code K.AdmissionSet) None element) ->
      SourceOperatorShape (T.CollectionOperator sort element K.AdmissionSet) (SetShape sort element)
  | source_map_shape : forall sort pair key value,
      nth_error source_sorts sort = Some (K.RuntimeCollection (kind_code K.AdmissionMap) (Some key) pair) ->
      nth_error source_sorts pair = Some (K.RuntimeProduct [key; value]) ->
      SourceOperatorShape (T.CollectionOperator sort pair K.AdmissionMap)
        (MapShape sort (product_label pair) key value)
  | source_pathmap_shape : forall sort pair key value,
      nth_error source_sorts sort = Some (K.RuntimeCollection (kind_code K.AdmissionPathMap) (Some key) pair) ->
      nth_error source_sorts pair = Some (K.RuntimeProduct [key; value]) ->
      SourceOperatorShape (T.CollectionOperator sort pair K.AdmissionPathMap)
        (PathMapShape sort (product_label pair) key value
          (mode_label sort K.RuntimePathMapNeutral) (mode_label sort K.RuntimePathMapSet)
          (mode_label sort K.RuntimePathMapMap)).

  Theorem source_product_projection_retains_arbitrary_arity : forall sort factors,
    nth_error source_sorts sort = Some (K.RuntimeProduct factors) ->
    SourceOperatorShape (T.ProductOperator sort) (ProductShape sort factors).
  Proof. intros. now constructor. Qed.
  Theorem source_substitution_projection_retains_function_identity : forall function result shape,
    SourceOperatorShape (T.SubstitutionOperator result function) shape ->
    exists domain multiple,
      nth_error source_sorts function = Some (K.RuntimeFunction domain result multiple) /\
      shape = FixedShape result [function; domain].
  Proof. intros function result shape Shape. inversion Shape; subst. eauto. Qed.
  Theorem source_literal_projection_retains_payload_and_carrier : forall sort literal shape,
    SourceOperatorShape (T.LiteralOperator sort literal) shape ->
    nth_error source_sorts sort = Some (K.RuntimeSyntax (Some (literal_code literal))) /\
    shape = FixedShape sort [].
  Proof. intros sort literal shape Shape. inversion Shape; subst. auto. Qed.
End SourceProjection.

Record Signature := {
  operator_shape : nat -> option Shape;
  equation_sort : Core.SortId;
  zero_signature : operator_shape 0 = Some (FixedShape equation_sort []);
  unit_signature : operator_shape 1 = Some (FixedShape equation_sort []);
  alternative_signature : operator_shape 2 =
    Some (FixedShape equation_sort [equation_sort; equation_sort]);
  product_signature : operator_shape 3 =
    Some (FixedShape equation_sort [equation_sort; equation_sort]);
  closure_signature : operator_shape 4 = Some (FixedShape equation_sort [equation_sort]);
  collection_profile : X.Profile;
  profile_is_shape : forall operator,
    X.collection_kind collection_profile operator =
      match operator_shape operator with
      | Some (BagShape _ _) => Some X.BagKind
      | Some (SetShape _ _) => Some X.SetKind
      | Some (MapShape _ pair_id _ _) => Some (X.MapKind pair_id)
      | Some (PathMapShape _ pair_id _ _ neutral set map) =>
          Some (X.PathMapKind pair_id neutral set map)
      | _ => None
      end;
  map_pair_signature : forall operator result pair key value,
    operator_shape operator = Some (MapShape result pair key value) ->
    exists pair_sort, operator_shape pair = Some (ProductShape pair_sort [key; value]);
  path_pair_signature : forall operator result pair key value neutral set map,
    operator_shape operator = Some (PathMapShape result pair key value neutral set map) ->
    exists pair_sort, operator_shape pair = Some (ProductShape pair_sort [key; value]);
  path_marker_signatures : forall operator result pair key value neutral set map,
    operator_shape operator = Some (PathMapShape result pair key value neutral set map) ->
    operator_shape neutral = Some MarkerShape /\
    operator_shape set = Some MarkerShape /\ operator_shape map = Some MarkerShape
}.

Inductive HasSignature (signature : Signature) : nat -> list ChildType -> ChildType -> Prop :=
| signature_fixed : forall operator result arguments,
    operator_shape signature operator = Some (FixedShape result arguments) ->
    HasSignature signature operator (List.map ValueType arguments) (ValueType result)
| signature_product : forall operator result factors,
    operator_shape signature operator = Some (ProductShape result factors) ->
    HasSignature signature operator (List.map ValueType factors) (ValueType result)
| signature_entry : forall operator result key value,
    operator_shape signature operator = Some (ProductShape result [key; value]) ->
    HasSignature signature operator [ValueType key; ValueType value] (EntryType operator key value)
| signature_list : forall operator result element count,
    operator_shape signature operator = Some (ListShape result element) ->
    HasSignature signature operator (repeat (ValueType element) count) (ValueType result)
| signature_bag : forall operator result element count,
    operator_shape signature operator = Some (BagShape result element) ->
    HasSignature signature operator (repeat (ValueType element) count) (ValueType result)
| signature_set : forall operator result element count,
    operator_shape signature operator = Some (SetShape result element) ->
    HasSignature signature operator (repeat (ValueType element) count) (ValueType result)
| signature_map : forall operator result pair key value count,
    operator_shape signature operator = Some (MapShape result pair key value) ->
    HasSignature signature operator (repeat (EntryType pair key value) count) (ValueType result)
| signature_path_neutral : forall operator result pair key value neutral set map,
    operator_shape signature operator = Some (PathMapShape result pair key value neutral set map) ->
    HasSignature signature operator [ModeType neutral] (ValueType result)
| signature_path_set : forall operator result pair key value neutral set map count,
    operator_shape signature operator = Some (PathMapShape result pair key value neutral set map) ->
    HasSignature signature operator (ModeType set :: repeat (ValueType key) count) (ValueType result)
| signature_path_map : forall operator result pair key value neutral set map count,
    operator_shape signature operator = Some (PathMapShape result pair key value neutral set map) ->
    HasSignature signature operator (ModeType map :: repeat (EntryType pair key value) count) (ValueType result)
| signature_marker : forall operator,
    operator_shape signature operator = Some MarkerShape ->
    HasSignature signature operator [] (ModeType operator).

Section TypedDomain.
  Variable signature : Signature.
  Variable variables : K.ScopedVariable -> Core.SortId.

  Inductive Typed : ChildType -> Term -> Prop :=
  | typed_variable : forall variable,
      Typed (ValueType (variables variable)) (LogicVariable variable)
  | typed_application : forall operator children sorts result,
      HasSignature signature operator sorts result ->
      Forall2 Typed sorts children -> Typed result (LogicApplication operator children).

  Lemma typed_entry_shape : forall pair key value term,
    Typed (EntryType pair key value) term -> exists k v,
    term = X.pair_term pair (k, v) /\ Typed (ValueType key) k /\ Typed (ValueType value) v.
  Proof.
    intros pair key value term Typing. inversion Typing; subst.
    match goal with S : HasSignature _ _ _ (EntryType _ _ _) |- _ => inversion S; subst end.
    match goal with F : Forall2 _ (_ :: _) _ |- _ => inversion F; subst end.
    match goal with F : Forall2 _ [_] _ |- _ => inversion F; subst end.
    match goal with F : Forall2 _ [] _ |- _ => inversion F; subst end.
    eexists _, _. repeat split; eauto.
  Qed.

  Lemma typed_mode_shape : forall mode term,
    Typed (ModeType mode) term -> term = X.marker mode.
  Proof.
    intros mode term Typing. inversion Typing; subst.
    match goal with S : HasSignature _ _ _ (ModeType _) |- _ => inversion S; subst end.
    match goal with F : Forall2 _ [] _ |- _ => inversion F; subst end. reflexivity.
  Qed.

  Lemma fixed_typing : forall operator result arguments children type,
    operator_shape signature operator = Some (FixedShape result arguments) ->
    Typed type (LogicApplication operator children) ->
    type = ValueType result /\ Forall2 Typed (map ValueType arguments) children.
  Proof.
    intros operator result arguments children type Shape Typing. inversion Typing; subst.
    match goal with S : HasSignature _ _ _ _ |- _ => inversion S; subst end;
      try congruence.
    split; congruence.
  Qed.

  Lemma typed_zero : Typed (ValueType (equation_sort signature)) E.zero.
  Proof. econstructor; [apply signature_fixed, zero_signature|constructor]. Qed.
  Lemma typed_unit : Typed (ValueType (equation_sort signature)) E.unit.
  Proof. econstructor; [apply signature_fixed, unit_signature|constructor]. Qed.

  Lemma typed_alternative : forall type a b,
    Typed type (E.alternative a b) ->
    type = ValueType (equation_sort signature) /\ Typed type a /\ Typed type b.
  Proof.
    intros type a b Typing.
    destruct (fixed_typing 2 _ _ _ _ (alternative_signature signature) Typing) as [-> Children].
    inversion Children; subst. match goal with F : Forall2 _ [_] _ |- _ => inversion F; subst end.
    auto.
  Qed.
  Lemma typed_product : forall type a b,
    Typed type (E.product a b) ->
    type = ValueType (equation_sort signature) /\ Typed type a /\ Typed type b.
  Proof.
    intros type a b Typing.
    destruct (fixed_typing 3 _ _ _ _ (product_signature signature) Typing) as [-> Children].
    inversion Children; subst. match goal with F : Forall2 _ [_] _ |- _ => inversion F; subst end.
    auto.
  Qed.
  Lemma typed_closure : forall type a,
    Typed type (E.closure a) ->
    type = ValueType (equation_sort signature) /\ Typed type a.
  Proof.
    intros type a Typing.
    destruct (fixed_typing 4 _ _ _ _ (closure_signature signature) Typing) as [-> Children].
    inversion Children; subst. auto.
  Qed.

  Theorem every_root_collapse_preserves_its_actual_sort : forall before after,
    E.RootStep before after -> forall type, Typed type before -> Typed type after.
  Proof.
    intros before after Step. destruct Step; intros type Typing;
      try apply typed_alternative in Typing; try apply typed_product in Typing;
      try apply typed_closure in Typing; intuition subst; auto using typed_zero, typed_unit.
  Qed.

  Lemma typed_context_replace : forall operator before after child replacement type,
    Typed type (LogicApplication operator (before ++ child :: after)) ->
    (forall child_type, Typed child_type child -> Typed child_type replacement) ->
    Typed type (LogicApplication operator (before ++ replacement :: after)).
  Proof.
    intros operator before after child replacement type Typing Replace.
    inversion Typing as [|? ? sorts ? Sig Children]; subst.
    econstructor; [exact Sig|]. clear Sig Typing. revert sorts Children.
    induction before as [|head before IH]; intros sorts Children; simpl in *;
      inversion Children; subst.
    - constructor; auto.
    - constructor; auto.
  Qed.

  Theorem contextual_equations_preserve_selected_carrier : forall before after,
    E.Step before after -> forall type, Typed type before -> Typed type after.
  Proof.
    intros before after Step. induction Step; intros type Typing.
    - eapply every_root_collapse_preserves_its_actual_sort; eauto.
    - eapply typed_context_replace; eauto.
  Qed.

  Theorem equation_phase_preserves_selected_carrier : forall before after,
    E.Reaches before after -> forall type, Typed type before -> Typed type after.
  Proof.
    intros before after Run. induction Run; eauto using contextual_equations_preserve_selected_carrier.
  Qed.

  (** Reachability includes EACH actual child contract, including substitution
      from its result to the full function sort.  It is not just the outgoing
      fields of the selected sort declaration. *)
  Inductive SortReach : ChildType -> ChildType -> Prop :=
  | reach_refl : forall type, SortReach type type
  | reach_child : forall operator sorts result child,
      HasSignature signature operator sorts result -> In child sorts -> SortReach result child
  | reach_trans : forall first middle last,
      SortReach first middle -> SortReach middle last -> SortReach first last.

  Definition EquationInert type := ~ SortReach type (ValueType (equation_sort signature)).

  Definition ClosedTypes (types : list ChildType) : Prop :=
    forall operator children result child,
      HasSignature signature operator children result ->
      In result types -> In child children -> In child types.

  Lemma finite_closed_types_contain_every_dependency : forall types root child,
    ClosedTypes types -> In root types -> SortReach root child -> In child types.
  Proof.
    intros types root child Closed Member Reach. revert Member.
    induction Reach; intros Member; eauto.
  Qed.

  Theorem finite_closed_key_domain_is_equation_inert : forall types key_type,
    ClosedTypes types -> In key_type types ->
    ~ In (ValueType (equation_sort signature)) types -> EquationInert key_type.
  Proof.
    intros types key_type Closed Key Absent Reach. apply Absent.
    eapply finite_closed_types_contain_every_dependency; eauto.
  Qed.

  Lemma typed_context_child : forall operator before after child type,
    Typed type (LogicApplication operator (before ++ child :: after)) ->
    exists child_type, Typed child_type child /\ SortReach type child_type.
  Proof.
    intros operator before after child type Typing.
    inversion Typing as [|? ? sorts ? Sig Children]; subst.
    assert (Member : In child (before ++ child :: after)) by (apply in_or_app; right; now left).
    clear Typing. induction Children as [|s term sorts terms Head Tail IH]; [contradiction|].
    destruct Member as [<-|Member].
    - exists s. split; [exact Head|]. eapply reach_child; [exact Sig|now left].
    - assert (Pair : exists child_type, In child_type sorts /\ Typed child_type child).
      { clear Sig IH Head. revert Member. induction Tail; intros Member; [contradiction|].
        destruct Member as [Equal|Member].
        - subst y. exists x. split; [now left|assumption].
        - destruct (IHTail Member) as [found [Found TypedFound]].
          exists found. split; [now right|exact TypedFound]. }
      destruct Pair as [found [Found TypedFound]]. exists found. split; [exact TypedFound|].
      eapply reach_child; [exact Sig|now right].
  Qed.

  Lemma root_collapse_requires_equation_sort : forall before after,
    E.RootStep before after -> forall type, Typed type before ->
    type = ValueType (equation_sort signature).
  Proof.
    intros before after Step. destruct Step; intros type Typing;
      try apply typed_alternative in Typing; try apply typed_product in Typing;
      try apply typed_closure in Typing; tauto.
  Qed.

  Lemma a_typed_redex_requires_sort_reachability : forall before after,
    E.Step before after -> forall type, Typed type before ->
    SortReach type (ValueType (equation_sort signature)).
  Proof.
    intros before after Step. induction Step; intros type Typing.
    - rewrite (root_collapse_requires_equation_sort _ _ H _ Typing). constructor.
    - destruct (typed_context_child _ _ _ _ _ Typing) as [child_type [Child Reach]].
      eapply reach_trans; [exact Reach|]. now apply IHStep.
  Qed.

  Theorem equation_inert_typed_terms_are_irreducible : forall type term,
    EquationInert type -> Typed type term -> E.Irreducible term.
  Proof.
    intros type term Inert Typing output Step. apply Inert.
    eapply a_typed_redex_requires_sort_reachability; eauto.
  Qed.
End TypedDomain.

Lemma forall2_repeat : forall (A B : Type) (P : A -> B -> Prop) value count values,
  Forall2 P (repeat value count) values -> Forall (P value) values.
Proof.
  intros A B P value count. induction count; intros values F; inversion F; subst;
    constructor; eauto.
Qed.
Lemma repeat_forall2 : forall (A B : Type) (P : A -> B -> Prop) value values,
  Forall (P value) values -> Forall2 P (repeat value (length values)) values.
Proof. intros A B P value values F. induction F; simpl; constructor; assumption. Qed.
Lemma forall_permutation : forall (A : Type) (P : A -> Prop) xs ys,
  Permutation xs ys -> Forall P xs -> Forall P ys.
Proof.
  intros A P xs ys Perm All. rewrite Forall_forall in *.
  intros x Member. apply All. eapply Permutation_in; [apply Permutation_sym; exact Perm|exact Member].
Qed.
Lemma forall_nodup : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) P xs,
  Forall P xs -> Forall P (nodup dec xs).
Proof.
  intros A dec P xs All. rewrite Forall_forall in *.
  intros x Member. apply All. now apply (proj1 (nodup_In dec xs x)).
Qed.
Lemma nodup_mapped_refinement : forall (A B D : Type) (f : A -> B) (g : A -> D) xs,
  (forall x y, In x xs -> In y xs -> g x = g y -> f x = f y) ->
  NoDup (map f xs) -> NoDup (map g xs).
Proof.
  intros A B D f g xs. induction xs as [|x xs IH]; intros Refine Unique; simpl in *.
  - constructor.
  - inversion Unique as [|? ? Fresh Tail]; subst. constructor.
    + intros Member. apply in_map_iff in Member as [y [Equal Member]].
      apply Fresh. apply in_map_iff. exists y. split; [|exact Member].
      apply Refine; auto.
    + apply IH; [|exact Tail]. intros a b AIn BIn Equal. apply Refine; auto.
Qed.

Section KeyDomain.
  Variable signature : Signature.
  Variable variables : K.ScopedVariable -> Core.SortId.
  Variable exact_key : Term -> nat.
  Hypothesis exact_key_reflects : forall x y, exact_key x = exact_key y -> x = y.
  Let profile := collection_profile signature.
  Let observation := U.observe exact_key profile.

  Definition entry_observation pair term : option Term :=
    match term with
    | LogicApplication operator [key; value] =>
        if Nat.eq_dec operator pair then Some key else None
    | _ => None
    end.

  Definition KeyGuard operator observed_children : Prop :=
    match X.collection_kind profile operator with
    | Some (X.MapKind pair_id) => NoDup (map (entry_observation pair_id) observed_children)
    | Some (X.PathMapKind pair_id neutral set map_marker) =>
        match observed_children with
        | [] => False
        | mode :: entries =>
            if E.term_eq_dec mode (X.marker neutral) then entries = [] else
            if E.term_eq_dec mode (X.marker set) then NoDup entries else
            if E.term_eq_dec mode (X.marker map_marker)
            then NoDup (map (entry_observation pair_id) entries) else False
        end
    | _ => True
    end.

  Inductive GoodKeys : Term -> Prop :=
  | good_variable : forall variable, GoodKeys (LogicVariable variable)
  | good_application : forall operator children,
      Forall GoodKeys children -> KeyGuard operator (map observation children) ->
      GoodKeys (LogicApplication operator children).

  Definition Domain type term := Typed signature variables type term /\ GoodKeys term.

  Lemma product_label_is_not_equation_role : forall operator result factors,
    operator_shape signature operator = Some (ProductShape result factors) -> 5 <= operator.
  Proof.
    intros operator result factors Shape.
    destruct operator as [|[|[|[|[|operator]]]]]; try lia;
      [rewrite zero_signature in Shape|rewrite unit_signature in Shape|
       rewrite alternative_signature in Shape|rewrite product_signature in Shape|
       rewrite closure_signature in Shape]; discriminate.
  Qed.
  Lemma product_profile_is_positional : forall operator result factors,
    operator_shape signature operator = Some (ProductShape result factors) ->
    X.collection_kind profile operator = None.
  Proof. intros. unfold profile. rewrite profile_is_shape, H. reflexivity. Qed.
  Lemma marker_profile_is_positional : forall operator,
    operator_shape signature operator = Some MarkerShape ->
    X.collection_kind profile operator = None.
  Proof. intros. unfold profile. rewrite profile_is_shape, H. reflexivity. Qed.

  Lemma observe_pair : forall pair pair_sort key_sort value_sort key value,
    operator_shape signature pair = Some (ProductShape pair_sort [key_sort; value_sort]) ->
    observation (X.pair_term pair (key, value)) =
      X.pair_term pair (observation key, observation value).
  Proof.
    intros pair pair_sort key_sort value_sort key value Shape.
    pose proof (product_label_is_not_equation_role _ _ _ Shape) as Large.
    change (U.observed_node exact_key profile pair [observation key; observation value] =
      LogicApplication pair [observation key; observation value]).
    unfold U.observed_node. rewrite (product_profile_is_positional _ _ _ Shape).
    destruct pair as [|[|[|[|[|pair]]]]]; try lia; reflexivity.
  Qed.
  Lemma observe_mode : forall marker,
    operator_shape signature marker = Some MarkerShape ->
    observation (X.marker marker) = X.marker marker.
  Proof.
    intros marker Shape. change (U.observed_node exact_key profile marker [] = X.marker marker).
    unfold U.observed_node. rewrite (marker_profile_is_positional _ Shape).
    destruct marker as [|[|[|[|[|marker]]]]]; reflexivity.
  Qed.
  Lemma observe_entries : forall pair pair_sort key_sort value_sort entries,
    operator_shape signature pair = Some (ProductShape pair_sort [key_sort; value_sort]) ->
    map (entry_observation pair) (map observation (X.pair_terms pair entries)) =
      map (fun entry => Some (observation (fst entry))) entries.
  Proof.
    intros pair pair_sort key_sort value_sort entries Shape. induction entries as [|[key value] rest IH];
      [reflexivity|].
    change (entry_observation pair (observation (X.pair_term pair (key, value))) ::
      map (entry_observation pair) (map observation (X.pair_terms pair rest)) =
      Some (observation key) :: map (fun entry => Some (observation (fst entry))) rest).
    rewrite (observe_pair _ _ _ _ _ _ Shape). unfold entry_observation at 1.
    cbn [X.pair_term fst snd].
    destruct (Nat.eq_dec pair pair); [now rewrite IH|contradiction].
  Qed.

  Lemma good_context_child : forall operator before after child,
    GoodKeys (LogicApplication operator (before ++ child :: after)) -> GoodKeys child.
  Proof.
    intros operator before after child Good. inversion Good; subst.
    match goal with All : Forall GoodKeys _ |- _ => apply Forall_forall with (x := child) in All;
      [exact All|] end.
    apply in_or_app. right. now left.
  Qed.
  Lemma good_child : forall operator children child,
    GoodKeys (LogicApplication operator children) -> In child children -> GoodKeys child.
  Proof. intros operator children child Good Member. inversion Good; subst.
    match goal with All : Forall GoodKeys _ |- _ => now apply Forall_forall with (x := child) in All end. Qed.
  Lemma equation_role_guard : forall operator children,
    operator < 5 -> KeyGuard operator children.
  Proof.
    intros operator children Small. unfold KeyGuard.
    rewrite (U.equation_roles_are_positional profile operator Small). exact I.
  Qed.
  Lemma good_zero : GoodKeys E.zero.
  Proof. constructor; [constructor|apply equation_role_guard; lia]. Qed.
  Lemma good_unit : GoodKeys E.unit.
  Proof. constructor; [constructor|apply equation_role_guard; lia]. Qed.

  Lemma root_collapse_preserves_good_keys : forall before after,
    E.RootStep before after -> GoodKeys before -> GoodKeys after.
  Proof.
    intros before after Step. destruct Step; intros Good;
      auto using good_zero, good_unit.
    all: eapply good_child; [exact Good|simpl; auto].
  Qed.
  Lemma good_context_replace : forall operator before after old next,
    GoodKeys (LogicApplication operator (before ++ old :: after)) ->
    GoodKeys next -> observation old = observation next ->
    GoodKeys (LogicApplication operator (before ++ next :: after)).
  Proof.
    intros operator before after old next Good Next Equal.
    inversion Good as [|? ? All Guard]; subst. constructor.
    - rewrite Forall_app in *. destruct All as [Before Rest].
      inversion Rest; subst. split; [exact Before|]. now constructor.
    - rewrite map_app in *. simpl in *. now rewrite <- Equal.
  Qed.
  Lemma equation_step_preserves_good_keys : forall before after,
    E.Step before after -> GoodKeys before -> GoodKeys after.
  Proof.
    intros before after Step. induction Step; intros Good.
    - eapply root_collapse_preserves_good_keys; eauto.
    - eapply good_context_replace; [exact Good| |].
      + apply IHStep. eapply good_context_child; eauto.
      + apply U.equations_preserve_observation, E.reaches_in_congruence,
          E.reaches_step. exact Step.
  Qed.
  Lemma equations_preserve_good_keys : forall before after,
    E.Reaches before after -> GoodKeys before -> GoodKeys after.
  Proof. intros before after Run. induction Run; eauto using equation_step_preserves_good_keys. Qed.

  Theorem typed_equations_preserve_key_domain : forall type before after,
    Domain type before -> E.Reaches before after -> Domain type after.
  Proof.
    intros type before after [Typing Keys] Run. split.
    - eapply equation_phase_preserves_selected_carrier; eauto.
    - eapply equations_preserve_good_keys; eauto.
  Qed.

  Lemma path_guard_permutation : forall operator mode before after,
    Permutation before after ->
    KeyGuard operator (mode :: before) -> KeyGuard operator (mode :: after).
  Proof.
    intros operator mode before after Perm Guard. unfold KeyGuard in *.
    destruct (X.collection_kind profile operator) as [[| |pair|pair neutral set map_marker]|]; auto.
    - eapply Permutation_NoDup; [apply Permutation_map; exact (perm_skip mode Perm)|exact Guard].
    - destruct (E.term_eq_dec mode (X.marker neutral));
        [subst before; now apply Permutation_nil|].
      destruct (E.term_eq_dec mode (X.marker set)).
      + eapply Permutation_NoDup; eauto.
      + destruct (E.term_eq_dec mode (X.marker map_marker)); [|contradiction].
        eapply Permutation_NoDup; [exact (Permutation_map (entry_observation pair) Perm)|exact Guard].
  Qed.

  Lemma canonical_root_preserves_good_keys : forall before after,
    X.CanonicalRoot exact_key profile before after -> GoodKeys before -> GoodKeys after.
  Proof.
    intros before after Root. destruct Root; intros Good;
      inversion Good as [|? ? All Guard]; subst; constructor.
    - eapply forall_permutation; [eapply X.bag_observation_preserves_multiplicity; eauto|exact All].
    - unfold KeyGuard. rewrite H. exact I.
    - rewrite Forall_forall in *. intros child Member. apply All.
      apply (proj2 (X.set_observation_preserves_membership exact_key exact_key_reflects _ _ H0 child)). exact Member.
    - unfold KeyGuard. rewrite H. exact I.
    - eapply forall_permutation; [|exact All]. unfold X.pair_terms.
      apply Permutation_map. eapply X.map_observation_preserves_entries; eauto.
    - unfold KeyGuard in *. rewrite H in *. eapply Permutation_NoDup; [|exact Guard].
      apply Permutation_map, Permutation_map. unfold X.pair_terms.
      apply Permutation_map. eapply X.map_observation_preserves_entries; eauto.
    - exact All.
    - exact Guard.
    - eapply forall_permutation; [|exact All]. constructor.
      eapply X.bag_observation_preserves_multiplicity; eauto. exact (proj2 H0).
    - cbn [List.map] in *. eapply path_guard_permutation; [|exact Guard].
      apply Permutation_map. eapply X.bag_observation_preserves_multiplicity; eauto. exact (proj2 H0).
    - eapply forall_permutation; [|exact All]. constructor. unfold X.pair_terms.
      apply Permutation_map. eapply X.map_observation_preserves_entries; eauto.
    - cbn [List.map] in *. eapply path_guard_permutation; [|exact Guard].
      apply Permutation_map. unfold X.pair_terms. apply Permutation_map.
      eapply X.map_observation_preserves_entries; eauto.
  Qed.

  Lemma canonical_step_preserves_good_keys : forall before after,
    X.CanonicalStep exact_key profile before after -> GoodKeys before -> GoodKeys after.
  Proof.
    intros before after Step. induction Step; intros Good.
    - eapply canonical_root_preserves_good_keys; eauto.
    - eapply good_context_replace; [exact Good| |].
      + apply IHStep. eapply good_context_child; eauto.
      + apply (U.combined_congruence_preserves_observation exact_key exact_key_reflects profile).
        eapply X.canonical_step_is_sound; eauto.
  Qed.
  Lemma canonical_pass_preserves_good_keys : forall before after,
    X.CanonicalReaches exact_key profile before after -> GoodKeys before -> GoodKeys after.
  Proof.
    intros before after Run. induction Run; eauto using canonical_step_preserves_good_keys.
  Qed.

  Lemma guard_implies_actual_map_key_uniqueness : forall operator pair result key value entries,
    operator_shape signature operator = Some (MapShape result pair key value) ->
    KeyGuard operator (map observation (X.pair_terms pair entries)) ->
    NoDup (X.entry_keys exact_key entries).
  Proof.
    intros operator pair result key value entries Shape Guard.
    destruct (map_pair_signature signature _ _ _ _ _ Shape) as [pair_sort Pair].
    unfold KeyGuard in Guard. unfold profile in Guard. rewrite profile_is_shape, Shape in Guard.
    rewrite (observe_entries _ _ _ _ _ Pair) in Guard.
    eapply nodup_mapped_refinement; [|exact Guard].
    intros [k v] [k' v'] Member Member' Equal. simpl in *.
    apply exact_key_reflects in Equal. now subst.
  Qed.

  Lemma path_set_guard_implies_actual_key_uniqueness :
    forall operator result pair key value neutral set map_marker entries,
    operator_shape signature operator =
      Some (PathMapShape result pair key value neutral set map_marker) ->
    KeyGuard operator (map observation (X.marker set :: entries)) ->
    NoDup (X.keys exact_key entries).
  Proof.
    intros operator result pair key value neutral set map_marker entries Shape Guard.
    pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ Shape) as [N [S M]].
    assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map_marker)).
    { unfold profile. rewrite profile_is_shape, Shape. reflexivity. }
    pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
    unfold KeyGuard in Guard. rewrite Kind in Guard. cbn [List.map] in Guard.
    rewrite (observe_mode _ S) in Guard.
    destruct (E.term_eq_dec (X.marker set) (X.marker neutral)); [unfold X.marker in e; congruence|].
    destruct (E.term_eq_dec (X.marker set) (X.marker set)); [|contradiction].
    eapply nodup_mapped_refinement; [|exact Guard]. intros x y Xmem Ymem Equal.
    now apply exact_key_reflects in Equal; subst.
  Qed.

  Lemma path_map_guard_implies_actual_key_uniqueness :
    forall operator result pair key value neutral set map_marker entries,
    operator_shape signature operator =
      Some (PathMapShape result pair key value neutral set map_marker) ->
    KeyGuard operator (map observation (X.marker map_marker :: X.pair_terms pair entries)) ->
    NoDup (X.entry_keys exact_key entries).
  Proof.
    intros operator result pair key value neutral set map_marker entries Shape Guard.
    pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ Shape) as [N [S M]].
    destruct (path_pair_signature signature _ _ _ _ _ _ _ _ Shape) as [pair_sort Pair].
    assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map_marker)).
    { unfold profile. rewrite profile_is_shape, Shape. reflexivity. }
    pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
    unfold KeyGuard in Guard. rewrite Kind in Guard. cbn [List.map] in Guard.
    rewrite (observe_mode _ M) in Guard.
    destruct (E.term_eq_dec (X.marker map_marker) (X.marker neutral)); [unfold X.marker in e; congruence|].
    destruct (E.term_eq_dec (X.marker map_marker) (X.marker set)); [unfold X.marker in e; congruence|].
    destruct (E.term_eq_dec (X.marker map_marker) (X.marker map_marker)); [|contradiction].
    rewrite (observe_entries _ _ _ _ _ Pair) in Guard.
    eapply nodup_mapped_refinement; [|exact Guard].
    intros [k v] [k' v'] Member Member' Equal. simpl in *.
    apply exact_key_reflects in Equal. now subst.
  Qed.

  Lemma map_insert_commutes : forall (B D : Type) (f : B -> D) l r,
    (forall x y, l x y = r (f x) (f y)) -> forall x xs,
    map f (C.insert l x xs) = C.insert r (f x) (map f xs).
  Proof.
    intros B D f l r Order x xs. induction xs as [|a xs IH]; simpl; [reflexivity|].
    rewrite Order. destruct (r (f x) (f a)); simpl; congruence.
  Qed.
  Lemma map_sort_commutes : forall (B D : Type) (f : B -> D) l r,
    (forall x y, l x y = r (f x) (f y)) -> forall xs,
    map f (C.sort l xs) = C.sort r (map f xs).
  Proof.
    intros B D f l r Order xs. induction xs as [|a xs IH]; simpl; [reflexivity|].
    rewrite (map_insert_commutes _ _ _ _ _ Order), IH. reflexivity.
  Qed.

  Lemma existing_bag_sort_observation : forall children,
    X.BagObservation exact_key children (U.ordered exact_key children).
  Proof.
    intros. unfold X.BagObservation, X.keys, U.ordered, C.canonical_bag, C.nat_sort.
    apply map_sort_commutes. reflexivity.
  Qed.
  Lemma existing_set_sort_observation : forall children,
    X.SetObservation exact_key children (U.extensional exact_key children).
  Proof.
    intros children. unfold X.SetObservation.
    apply C.sorted_nodup_membership_unique.
    - apply U.ordered_key_sorted.
    - eapply nodup_mapped_refinement with (f := fun term : Term => term).
      + intros x y Xmem Ymem Equal. now apply exact_key_reflects.
      + rewrite map_id. unfold U.extensional.
        eapply Permutation_NoDup; [apply U.ordered_permutation|apply NoDup_nodup].
    - apply C.canonical_keys_sorted.
    - apply C.canonical_keys_nodup.
    - intros code. rewrite C.canonical_keys_in. unfold X.keys. repeat rewrite in_map_iff.
      split; intros [term [Equal Member]]; exists term; split; [exact Equal| |exact Equal|].
      + now apply (proj1 (U.extensional_membership exact_key children term)).
      + now apply (proj2 (U.extensional_membership exact_key children term)).
  Qed.

  Definition entry_order (left right : Term * Term) :=
    Nat.leb (exact_key (fst left)) (exact_key (fst right)).
  Definition ordered_entries entries := C.sort entry_order entries.

  Lemma existing_map_sort_observation : forall entries,
    NoDup (X.entry_keys exact_key entries) ->
    X.MapObservation exact_key entries (ordered_entries entries).
  Proof.
    intros entries Unique. split; [exact Unique|]. unfold X.entry_codes, ordered_entries, C.canonical_map.
    apply map_sort_commutes. reflexivity.
  Qed.
  Lemma ordered_entries_canonical : forall entries,
    NoDup (X.entry_keys exact_key entries) -> X.MapCanonical exact_key (ordered_entries entries).
  Proof.
    intros entries Unique. pose proof (existing_map_sort_observation entries Unique) as Obs.
    split.
    - rewrite (proj2 Obs). apply C.canonical_map_is_key_sorted.
    - eapply X.map_observation_preserves_key_uniqueness; eauto.
  Qed.
  Lemma ordered_entries_permutation : forall entries, Permutation entries (ordered_entries entries).
  Proof. intros. apply C.sort_permutation. Qed.

  Lemma canonical_reaches_trans : forall x y z,
    X.CanonicalReaches exact_key profile x y ->
    X.CanonicalReaches exact_key profile y z -> X.CanonicalReaches exact_key profile x z.
  Proof. intros x y z First. induction First; eauto using X.canonical_next. Qed.
  Lemma canonical_reaches_context : forall x y,
    X.CanonicalReaches exact_key profile x y -> forall operator before after,
    X.CanonicalReaches exact_key profile (LogicApplication operator (before ++ x :: after))
      (LogicApplication operator (before ++ y :: after)).
  Proof.
    intros x y Run. induction Run; intros.
    - constructor.
    - econstructor; [apply X.canonical_in_context; eassumption|auto].
  Qed.
  Lemma canonical_reaches_children : forall children outputs,
    Forall2 (X.CanonicalReaches exact_key profile) children outputs -> forall operator before,
    X.CanonicalReaches exact_key profile (LogicApplication operator (before ++ children))
      (LogicApplication operator (before ++ outputs)).
  Proof.
    intros children outputs Runs. induction Runs; intros operator before; simpl.
    - constructor.
    - eapply canonical_reaches_trans with (y := LogicApplication operator (before ++ y :: l)).
      + apply canonical_reaches_context. exact H.
      + specialize (IHRuns operator (before ++ [y])). now rewrite <- !app_assoc in IHRuns.
  Qed.
  Lemma canonical_root_reaches : forall before after,
    X.CanonicalRoot exact_key profile before after -> X.CanonicalReaches exact_key profile before after.
  Proof. intros before after Root. eapply X.canonical_next;
    [exact (X.canonical_at_root exact_key profile before after Root)|constructor]. Qed.

  Lemma typed_entry_vector : forall pair key value children,
    Forall (Typed signature variables (EntryType pair key value)) children ->
    exists entries, children = X.pair_terms pair entries.
  Proof.
    intros pair key value children All. induction All as [|child children Typing All [entries Equal]].
    - exists []. reflexivity.
    - destruct (typed_entry_shape signature variables _ _ _ _ Typing) as [k [v [Shape Types]]].
      exists ((k, v) :: entries).
      change (child :: children = X.pair_term pair (k, v) :: X.pair_terms pair entries).
      now rewrite Shape, Equal.
  Qed.
  Lemma canonical_children_permutation : forall xs ys,
    Permutation xs ys -> Forall (X.CollectionCanonical exact_key profile) xs ->
    Forall (X.CollectionCanonical exact_key profile) ys.
  Proof. intros. eapply forall_permutation; eauto. Qed.

  (** ONE existing constructor call is always available once children are
      canonical and the local key invariant holds.  No global completion or
      engine correctness is a premise of this result. *)
  Lemma canonical_root_available : forall operator children type,
    Typed signature variables type (LogicApplication operator children) ->
    Forall (X.CollectionCanonical exact_key profile) children ->
    GoodKeys (LogicApplication operator children) ->
    exists output, X.CanonicalReaches exact_key profile (LogicApplication operator children) output /\
      X.CollectionCanonical exact_key profile output /\ Typed signature variables type output.
  Proof.
    intros operator children type Typing Canonical Good.
    inversion Good as [|? ? GoodChildren Guard]; subst.
    inversion Typing as [|? ? sorts ? Sig Children]; subst.
    inversion Sig; subst.
    - exists (LogicApplication operator children). split; [constructor|]. split; [|exact Typing].
      constructor; [|exact Canonical]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. exact I.
    - exists (LogicApplication operator children). split; [constructor|]. split; [|exact Typing].
      constructor; [|exact Canonical]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. exact I.
    - exists (LogicApplication operator children). split; [constructor|]. split; [|exact Typing].
      constructor; [|exact Canonical]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. exact I.
    - exists (LogicApplication operator children). split; [constructor|]. split; [|exact Typing].
      constructor; [|exact Canonical]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. exact I.
    - assert (Kind : X.collection_kind profile operator = Some X.BagKind).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      exists (LogicApplication operator (U.ordered exact_key children)). split.
      + apply canonical_root_reaches. eapply X.canonical_bag; [exact Kind|apply existing_bag_sort_observation].
      + split.
        * constructor. unfold X.LocallyCanonical. rewrite Kind. apply U.ordered_key_sorted.
          eapply canonical_children_permutation; [apply U.ordered_permutation|exact Canonical].
        * econstructor. eapply signature_bag; exact H. apply repeat_forall2.
          eapply forall_permutation; [apply U.ordered_permutation|]. eapply forall2_repeat; exact Children.
    - assert (Kind : X.collection_kind profile operator = Some X.SetKind).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      pose proof (existing_set_sort_observation children) as Observation.
      assert (Perm : Permutation (nodup E.term_eq_dec children) (U.extensional exact_key children)).
      { eapply X.set_observation_is_dedup_permutation; eauto. }
      exists (LogicApplication operator (U.extensional exact_key children)). split.
      + apply canonical_root_reaches. eapply X.canonical_set; eauto.
      + split.
        * constructor. unfold X.LocallyCanonical. rewrite Kind. split.
          -- apply U.ordered_key_sorted.
          -- change (NoDup (X.keys exact_key (U.extensional exact_key children))).
             rewrite Observation. apply C.canonical_set_has_unique_elements.
          -- eapply canonical_children_permutation; [exact Perm|now apply forall_nodup].
        * econstructor. eapply signature_set; exact H. apply repeat_forall2.
          eapply forall_permutation; [exact Perm|]. apply forall_nodup.
          eapply forall2_repeat; exact Children.
    - assert (Kind : X.collection_kind profile operator = Some (X.MapKind pair)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      pose proof (forall2_repeat _ _ _ _ _ _ Children) as EntryTypes.
      destruct (typed_entry_vector _ _ _ _ EntryTypes) as [entries Equal]. subst children.
      assert (Unique : NoDup (X.entry_keys exact_key entries)).
      { eapply guard_implies_actual_map_key_uniqueness; eauto. }
      assert (Perm : Permutation (X.pair_terms pair entries) (X.pair_terms pair (ordered_entries entries))).
      { unfold X.pair_terms. apply Permutation_map, ordered_entries_permutation. }
      exists (LogicApplication operator (X.pair_terms pair (ordered_entries entries))). split.
      + apply canonical_root_reaches. eapply X.canonical_map; [exact Kind|now apply existing_map_sort_observation].
      + split.
        * constructor. unfold X.LocallyCanonical. rewrite Kind. exists (ordered_entries entries).
          split; [reflexivity|now apply ordered_entries_canonical].
          eapply canonical_children_permutation; eauto.
        * econstructor. eapply signature_map; exact H. apply repeat_forall2.
          eapply forall_permutation; eauto.
    - inversion Children; subst. match goal with F : Forall2 _ [] _ |- _ => inversion F; subst end.
      match goal with M : Typed _ _ (ModeType _) _ |- _ =>
        apply typed_mode_shape in M; subst end.
      exists (LogicApplication operator [X.marker neutral]). split; [constructor|]. split; [|exact Typing].
      constructor; [|exact Canonical]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. now left.
    - inversion Children as [|? mode ? entries Mode EntryTypes]; subst.
      apply typed_mode_shape in Mode. subst mode.
      assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      assert (Unique : NoDup (X.keys exact_key entries)).
      { eapply path_set_guard_implies_actual_key_uniqueness; eauto. }
      assert (Perm : Permutation entries (U.ordered exact_key entries)) by apply U.ordered_permutation.
      exists (LogicApplication operator (X.marker set :: U.ordered exact_key entries)). split.
      + apply canonical_root_reaches. eapply X.canonical_path_set; [exact Kind|].
        split; [exact Unique|apply existing_bag_sort_observation].
      + split.
        * constructor. unfold X.LocallyCanonical. rewrite Kind. right; left.
          exists (U.ordered exact_key entries). split; [reflexivity|]. split; [apply U.ordered_key_sorted|].
          eapply Permutation_NoDup; [exact (Permutation_map exact_key Perm)|exact Unique].
          eapply canonical_children_permutation; [exact (perm_skip _ Perm)|exact Canonical].
        * econstructor. eapply signature_path_set; exact H. constructor.
          -- pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ H) as [N [S M]].
             econstructor; [now apply signature_marker|constructor].
          -- apply repeat_forall2. eapply forall_permutation; [exact Perm|].
             eapply forall2_repeat; exact EntryTypes.
    - inversion Children as [|? mode ? entries Mode EntryTypes]; subst.
      apply typed_mode_shape in Mode. subst mode.
      pose proof (forall2_repeat _ _ _ _ _ _ EntryTypes) as EachEntry.
      destruct (typed_entry_vector _ _ _ _ EachEntry) as [pairs Equal]. subst entries.
      assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      assert (Unique : NoDup (X.entry_keys exact_key pairs)).
      { eapply path_map_guard_implies_actual_key_uniqueness; eauto. }
      assert (Perm : Permutation (X.pair_terms pair pairs) (X.pair_terms pair (ordered_entries pairs))).
      { unfold X.pair_terms. apply Permutation_map, ordered_entries_permutation. }
      exists (LogicApplication operator (X.marker map :: X.pair_terms pair (ordered_entries pairs))). split.
      + apply canonical_root_reaches. eapply X.canonical_path_map; [exact Kind|now apply existing_map_sort_observation].
      + split.
        * constructor. unfold X.LocallyCanonical. rewrite Kind. right; right.
          exists (ordered_entries pairs). split; [reflexivity|now apply ordered_entries_canonical].
          eapply canonical_children_permutation; [exact (perm_skip _ Perm)|exact Canonical].
        * econstructor. eapply signature_path_map; exact H. constructor.
          -- pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ H) as [N [S M]].
             econstructor; [now apply signature_marker|constructor].
          -- apply repeat_forall2. eapply forall_permutation; eauto.
    - inversion Children; subst.
      exists (X.marker operator). split; [constructor|]. split; [|exact Typing].
      constructor; [|constructor]. unfold X.LocallyCanonical, profile.
      rewrite profile_is_shape, H. exact I.
  Qed.

  Lemma canonical_children_available : forall children,
    Forall (fun child => forall type, Domain type child -> exists output,
      X.CollectionPass exact_key profile child output /\ Domain type output) children ->
    forall sorts, Forall2 (Typed signature variables) sorts children -> Forall GoodKeys children ->
    exists outputs, Forall2 (Typed signature variables) sorts outputs /\
      Forall (X.CollectionCanonical exact_key profile) outputs /\
      Forall2 (X.CanonicalReaches exact_key profile) children outputs.
  Proof.
    intros children IH sorts Types. induction Types; intros Goods; inversion IH; subst; inversion Goods; subst.
    - exists []. repeat split; constructor.
    - match goal with I : forall type, Domain type y -> _ |- _ =>
        destruct (I x) as [out [[Run Canon] [Typing Good]]]; [split; assumption|] end.
      destruct IHTypes as [outs [Types' [Canon' Runs']]]; try assumption.
      exists (out :: outs). repeat split; constructor; assumption.
  Qed.

  Theorem canonical_pass_available_in_typed_key_domain : forall term type,
    Domain type term -> exists output,
    X.CollectionPass exact_key profile term output /\ Domain type output.
  Proof.
    apply (E.term_induction (fun term => forall type, Domain type term -> exists output,
      X.CollectionPass exact_key profile term output /\ Domain type output)).
    - intros variable type [Typing Good]. exists (LogicVariable variable).
      repeat split; try assumption; constructor.
    - intros operator children IH type [Typing Good].
      inversion Typing as [|? ? sorts ? Sig Types]; subst.
      inversion Good as [|? ? Goods Guard]; subst.
      destruct (canonical_children_available children IH sorts Types Goods)
        as [outputs [OutputTypes [Canonical Runs]]].
      assert (ChildRun : X.CanonicalReaches exact_key profile
        (LogicApplication operator children) (LogicApplication operator outputs)).
      { exact (canonical_reaches_children _ _ Runs operator []). }
      assert (RawType : Typed signature variables type (LogicApplication operator outputs)).
      { econstructor; eauto. }
      assert (RawGood : GoodKeys (LogicApplication operator outputs)).
      { eapply canonical_pass_preserves_good_keys; eauto. }
      destruct (canonical_root_available _ _ _ RawType Canonical RawGood)
        as [output [RootRun [OutputCanonical OutputType]]].
      exists output. split; [split|split]; try assumption.
      + eapply canonical_reaches_trans; eauto.
      + eapply canonical_pass_preserves_good_keys; eauto.
  Qed.

  Theorem typed_key_domain_is_closed : forall type,
    X.DomainClosure exact_key profile (Domain type).
  Proof.
    intros type. constructor.
    - intros before after Before Run. eapply typed_equations_preserve_key_domain; eauto.
    - intros before Before. eapply canonical_pass_available_in_typed_key_domain; eauto.
  Qed.

  Theorem every_typed_key_domain_term_has_a_joint_normal_form : forall type input,
    Domain type input -> exists ready count output,
    X.InitialPass exact_key profile input ready /\
    X.Coordination exact_key profile count ready output.
  Proof.
    intros type input Input. eapply X.closed_domain_has_accepted_completion;
      [exact exact_key_reflects|apply typed_key_domain_is_closed|exact Input].
  Qed.

  (** A selected carrier need not exclude keyed or unordered collections.
      Only reachable KEY domains need this sufficient equation-inertness
      evidence.  A client with finer evidence may instead prove Domain for
      its own selected inputs directly. *)
  Definition StableKeySorts root : Prop :=
    (forall operator result pair key value,
      operator_shape signature operator = Some (MapShape result pair key value) ->
      SortReach signature root (ValueType result) ->
      EquationInert signature (ValueType key)) /\
    (forall operator result pair key value neutral set map_marker,
      operator_shape signature operator =
        Some (PathMapShape result pair key value neutral set map_marker) ->
      SortReach signature root (ValueType result) ->
      EquationInert signature (ValueType key)).

  Lemma stable_key_sorts_descend : forall root child,
    StableKeySorts root -> SortReach signature root child -> StableKeySorts child.
  Proof.
    intros root child [Maps Paths] Reach. split; intros.
    - eapply Maps; [eassumption|]. eapply reach_trans; eauto.
    - eapply Paths; [eassumption|]. eapply reach_trans; eauto.
  Qed.

  Lemma canonical_pair_key : forall pair key value,
    X.CollectionCanonical exact_key profile (X.pair_term pair (key, value)) ->
    X.CollectionCanonical exact_key profile key.
  Proof.
    intros pair key value Canonical. inversion Canonical; subst.
    match goal with F : Forall _ [_; _] |- _ => inversion F; subst; assumption end.
  Qed.
  Lemma typed_pair_key : forall pair key_sort value_sort key value,
    Typed signature variables (EntryType pair key_sort value_sort) (X.pair_term pair (key, value)) ->
    Typed signature variables (ValueType key_sort) key.
  Proof.
    intros pair key_sort value_sort key value Typing.
    destruct (typed_entry_shape signature variables _ _ _ _ Typing) as [k [v [Equal [KT VT]]]].
    apply (U.pair_term_injective pair) in Equal. inversion Equal; subst. exact KT.
  Qed.

  Lemma inert_canonical_key_observation_reflects : forall sort left right,
    EquationInert signature (ValueType sort) ->
    Typed signature variables (ValueType sort) left ->
    Typed signature variables (ValueType sort) right ->
    X.CollectionCanonical exact_key profile left ->
    X.CollectionCanonical exact_key profile right ->
    observation left = observation right -> left = right.
  Proof.
    intros sort left right Inert LT RT LC RC Equal.
    eapply U.observation_reflects_jointly_normal_terms; eauto;
      eapply equation_inert_typed_terms_are_irreducible; eauto.
  Qed.

  Lemma canonical_entries_have_distinct_observed_keys : forall pair key value entries,
    EquationInert signature (ValueType key) ->
    Forall (Typed signature variables (EntryType pair key value)) (X.pair_terms pair entries) ->
    Forall (X.CollectionCanonical exact_key profile) (X.pair_terms pair entries) ->
    NoDup (X.entry_keys exact_key entries) ->
    NoDup (map (fun entry => Some (observation (fst entry))) entries).
  Proof.
    intros pair key value entries Inert Types Canonical Unique.
    eapply nodup_mapped_refinement; [|exact Unique].
    intros [k v] [k' v'] Member Member' Equal. injection Equal as Equal. simpl in *.
    assert (KType : Typed signature variables (ValueType key) k).
    { apply (typed_pair_key pair key value k v). rewrite Forall_forall in Types. apply Types.
      unfold X.pair_terms. now apply in_map. }
    assert (K'Type : Typed signature variables (ValueType key) k').
    { apply (typed_pair_key pair key value k' v'). rewrite Forall_forall in Types. apply Types.
      unfold X.pair_terms. now apply in_map. }
    assert (KCanonical : X.CollectionCanonical exact_key profile k).
    { apply (canonical_pair_key pair k v). rewrite Forall_forall in Canonical. apply Canonical.
      unfold X.pair_terms. now apply in_map. }
    assert (K'Canonical : X.CollectionCanonical exact_key profile k').
    { apply (canonical_pair_key pair k' v'). rewrite Forall_forall in Canonical. apply Canonical.
      unfold X.pair_terms. now apply in_map. }
    assert (k = k') by (eapply inert_canonical_key_observation_reflects; eauto).
    now subst.
  Qed.

  Lemma locally_canonical_path_set : forall operator pair neutral set map_marker entries,
    X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map_marker) ->
    X.LocallyCanonical exact_key profile operator (X.marker set :: entries) ->
    X.KeySorted exact_key entries /\ NoDup (X.keys exact_key entries).
  Proof.
    intros operator pair neutral set map_marker entries Kind Local.
    pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
    unfold X.LocallyCanonical in Local. rewrite Kind in Local.
    destruct Local as [Equal|[[other [Equal Canon]]|[other [Equal Canon]]]].
    - injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
    - injection Equal as Equal. now subst other.
    - injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
  Qed.
  Lemma locally_canonical_path_map : forall operator pair neutral set map_marker entries,
    X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map_marker) ->
    X.LocallyCanonical exact_key profile operator (X.marker map_marker :: entries) ->
    exists pairs, entries = X.pair_terms pair pairs /\ X.MapCanonical exact_key pairs.
  Proof.
    intros operator pair neutral set map_marker entries Kind Local.
    pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
    unfold X.LocallyCanonical in Local. rewrite Kind in Local.
    destruct Local as [Equal|[[other [Equal Canon]]|[other [Equal Canon]]]].
    - injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
    - injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
    - injection Equal as Equal. exists other. auto.
  Qed.

  Lemma canonical_node_in_stable_sorts_has_key_guard : forall type operator children,
    Typed signature variables type (LogicApplication operator children) ->
    StableKeySorts type -> X.CollectionCanonical exact_key profile (LogicApplication operator children) ->
    KeyGuard operator (map observation children).
  Proof.
    intros type operator children Typing Stable Canonical.
    inversion Canonical as [|? ? Local CanonChildren]; subst.
    inversion Typing as [|? ? sorts ? Sig Types]; subst. inversion Sig; subst.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
    - assert (Kind : X.collection_kind profile operator = Some (X.MapKind pair)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      unfold X.LocallyCanonical in Local. rewrite Kind in Local.
      destruct Local as [entries [Equal [Sorted Unique]]]. subst children.
      unfold KeyGuard. rewrite Kind.
      destruct (map_pair_signature signature _ _ _ _ _ H) as [pair_sort Pair].
      rewrite (observe_entries _ _ _ _ _ Pair).
      eapply canonical_entries_have_distinct_observed_keys; try eassumption.
      + apply (proj1 Stable operator result pair key value H). constructor.
      + eapply forall2_repeat; exact Types.
    - inversion Types; subst. match goal with F : Forall2 _ [] _ |- _ => inversion F; subst end.
      match goal with M : Typed _ _ (ModeType _) _ |- _ => apply typed_mode_shape in M; subst end.
      pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ H) as [N [S M]].
      unfold KeyGuard, profile. rewrite profile_is_shape, H. cbn [List.map].
      rewrite (observe_mode _ N). destruct (E.term_eq_dec (X.marker neutral) (X.marker neutral));
        [reflexivity|contradiction].
    - inversion Types as [|? mode ? entries Mode EntryTypes]; subst.
      apply typed_mode_shape in Mode. subst mode.
      assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ H) as [N [S M]].
      pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
      destruct (locally_canonical_path_set _ _ _ _ _ _ Kind Local) as [Sorted Unique].
      unfold KeyGuard. rewrite Kind. cbn [List.map]. rewrite (observe_mode _ S).
      destruct (E.term_eq_dec (X.marker set) (X.marker neutral)); [unfold X.marker in e; congruence|].
      destruct (E.term_eq_dec (X.marker set) (X.marker set)); [|contradiction].
      eapply nodup_mapped_refinement; [|exact Unique]. intros x y Xmem Ymem Equal.
      assert (x = y).
      { eapply inert_canonical_key_observation_reflects; [| | | | |exact Equal].
        - apply (proj2 Stable operator result pair key value neutral set map H). constructor.
        - pose proof (forall2_repeat _ _ _ _ _ _ EntryTypes) as All.
          now apply Forall_forall with (x := x) in All.
        - pose proof (forall2_repeat _ _ _ _ _ _ EntryTypes) as All.
          now apply Forall_forall with (x := y) in All.
        - rewrite Forall_forall in CanonChildren. apply CanonChildren. now right.
        - rewrite Forall_forall in CanonChildren. apply CanonChildren. now right. }
      now subst.
    - inversion Types as [|? mode ? entries Mode EntryTypes]; subst.
      apply typed_mode_shape in Mode. subst mode.
      assert (Kind : X.collection_kind profile operator = Some (X.PathMapKind pair neutral set map)).
      { unfold profile. rewrite profile_is_shape, H. reflexivity. }
      pose proof (path_marker_signatures signature _ _ _ _ _ _ _ _ H) as [N [S M]].
      pose proof (X.pathmap_markers_separate profile _ _ _ _ _ Kind) as [NS [NM SM]].
      destruct (locally_canonical_path_map _ _ _ _ _ _ Kind Local) as [pairs [Equal [Sorted Unique]]].
      subst entries. unfold KeyGuard. rewrite Kind. cbn [List.map]. rewrite (observe_mode _ M).
      destruct (E.term_eq_dec (X.marker map) (X.marker neutral)); [unfold X.marker in e; congruence|].
      destruct (E.term_eq_dec (X.marker map) (X.marker set)); [unfold X.marker in e; congruence|].
      destruct (E.term_eq_dec (X.marker map) (X.marker map)); [|contradiction].
      destruct (path_pair_signature signature _ _ _ _ _ _ _ _ H) as [pair_sort Pair].
      rewrite (observe_entries _ _ _ _ _ Pair).
      eapply canonical_entries_have_distinct_observed_keys; try eassumption.
      + apply (proj2 Stable operator result pair key value neutral set map H). constructor.
      + eapply forall2_repeat; exact EntryTypes.
      + inversion CanonChildren; assumption.
    - unfold KeyGuard, profile. rewrite profile_is_shape, H. exact I.
  Qed.

  Theorem canonical_input_with_stable_key_sorts_is_in_domain : forall term type,
    Typed signature variables type term -> StableKeySorts type ->
    X.CollectionCanonical exact_key profile term -> Domain type term.
  Proof.
    apply (E.term_induction (fun term => forall type,
      Typed signature variables type term -> StableKeySorts type ->
      X.CollectionCanonical exact_key profile term -> Domain type term)).
    - intros variable type Typing Stable Canonical. split; [exact Typing|constructor].
    - intros operator children IH type Typing Stable Canonical. split; [exact Typing|]. constructor.
      + rewrite Forall_forall in IH. apply Forall_forall. intros child Member.
        apply in_split in Member as [before [after Equal]]. subst children.
        destruct (typed_context_child signature variables _ _ _ _ _ Typing) as [child_type [Child Reach]].
        assert (StableChild : StableKeySorts child_type) by (eapply stable_key_sorts_descend; eauto).
        assert (CanonicalChild : X.CollectionCanonical exact_key profile child).
        { inversion Canonical; subst.
          match goal with F : Forall _ _ |- _ => apply Forall_forall with (x := child) in F;
            [exact F|] end. apply in_or_app. right. now left. }
        assert (Member : In child (before ++ child :: after)) by (apply in_or_app; right; now left).
        exact (proj2 (IH child Member child_type Child StableChild CanonicalChild)).
      + eapply canonical_node_in_stable_sorts_has_key_guard; eauto.
  Qed.

  Theorem stable_selected_carrier_has_mathematical_completion : forall root input,
    StableKeySorts (ValueType root) -> Typed signature variables (ValueType root) input ->
    X.CollectionCanonical exact_key profile input ->
    exists ready count output, X.InitialPass exact_key profile input ready /\
      X.Coordination exact_key profile count ready output.
  Proof.
    intros root input Stable Typing Canonical.
    eapply every_typed_key_domain_term_has_a_joint_normal_form.
    eapply canonical_input_with_stable_key_sorts_is_in_domain; eauto.
  Qed.

  Theorem stable_selected_carrier_successful_results_agree :
    forall input ready_left ready_right left right nl nr,
    X.InitialPass exact_key profile input ready_left ->
    X.Coordination exact_key profile nl ready_left left ->
    X.InitialPass exact_key profile input ready_right ->
    X.Coordination exact_key profile nr ready_right right -> left = right.
  Proof.
    intros input ready_left ready_right left right nl nr FirstL RunL FirstR RunR.
    exact (U.successful_runs_agree exact_key exact_key_reflects profile
      input ready_left ready_right left right nl nr FirstL RunL FirstR RunR).
  Qed.

End KeyDomain.

Print Assumptions arbitrary_product_keeps_every_factor.
Print Assumptions substitution_keeps_reverse_function_dependency.
Print Assumptions source_product_projection_retains_arbitrary_arity.
Print Assumptions source_substitution_projection_retains_function_identity.
Print Assumptions source_literal_projection_retains_payload_and_carrier.
Print Assumptions every_root_collapse_preserves_its_actual_sort.
Print Assumptions contextual_equations_preserve_selected_carrier.
Print Assumptions equation_inert_typed_terms_are_irreducible.
Print Assumptions finite_closed_key_domain_is_equation_inert.
Print Assumptions typed_equations_preserve_key_domain.
Print Assumptions canonical_pass_available_in_typed_key_domain.
Print Assumptions typed_key_domain_is_closed.
Print Assumptions canonical_input_with_stable_key_sorts_is_in_domain.
Print Assumptions stable_selected_carrier_has_mathematical_completion.
Print Assumptions stable_selected_carrier_successful_results_agree.

End SourceEquationCarrierDomain.
