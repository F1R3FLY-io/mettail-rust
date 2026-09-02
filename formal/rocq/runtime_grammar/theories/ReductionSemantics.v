From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Inductive CollectionKind : Type :=
| ListKind
| BagKind
| SetKind
| MapKind
| PathMapKind.

Scheme Equality for CollectionKind.

Inductive Value : Type :=
| Atom : nat -> Value
| Sequence : list Value -> Value
| Collection : CollectionKind -> list Value -> Value.

Fixpoint empty_collections (layout : list CollectionKind) : list Value :=
  match layout with
  | [] => []
  | kind :: rest => Collection kind [] :: empty_collections rest
  end.

Fixpoint singleton_collections
    (layout : list CollectionKind) (values : list Value) : option (list Value) :=
  match layout, values with
  | [], [] => Some []
  | kind :: layout', value :: values' =>
      match singleton_collections layout' values' with
      | Some rest => Some (Collection kind [value] :: rest)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint append_collections
    (layout : list CollectionKind) (prefixes lasts : list Value)
    : option (list Value) :=
  match layout, prefixes, lasts with
  | [], [], [] => Some []
  | kind :: layout', Collection prefix_kind prefix :: prefixes', last :: lasts' =>
      if CollectionKind_eq_dec kind prefix_kind
      then match append_collections layout' prefixes' lasts' with
           | Some rest => Some (Collection kind (prefix ++ [last]) :: rest)
           | None => None
           end
      else None
  | _, _, _ => None
  end.

Fixpoint finalize_collections
    (layout : list CollectionKind) (values : list Value) : option (list Value) :=
  match layout, values with
  | [], [] => Some []
  | kind :: layout', Collection value_kind entries :: values' =>
      if CollectionKind_eq_dec kind value_kind
      then match finalize_collections layout' values' with
           | Some rest => Some (Collection kind entries :: rest)
           | None => None
           end
      else None
  | _, _ => None
  end.

Inductive AuxiliarySemantic : Type :=
| EmptyOptional : nat -> AuxiliarySemantic
| PresentOptional : nat -> AuxiliarySemantic
| EmptyCollection : list CollectionKind -> AuxiliarySemantic
| SingletonCollection : list CollectionKind -> AuxiliarySemantic
| AppendCollection : list CollectionKind -> AuxiliarySemantic
| FinalizeCollection : list CollectionKind -> AuxiliarySemantic
| Tuple : nat -> AuxiliarySemantic
| UnitSlots : nat -> AuxiliarySemantic.

Definition output_arity (semantic : AuxiliarySemantic) : nat :=
  match semantic with
  | EmptyOptional slots | PresentOptional slots | UnitSlots slots => slots
  | EmptyCollection layout
  | SingletonCollection layout
  | AppendCollection layout
  | FinalizeCollection layout => length layout
  | Tuple _ => 1
  end.

Definition apply_auxiliary
    (semantic : AuxiliarySemantic) (values : list Value)
    : option (list Value) :=
  match semantic with
  | EmptyOptional slots =>
      if Nat.eqb (length values) 0
      then Some (repeat (Sequence []) slots)
      else None
  | PresentOptional slots =>
      if Nat.eqb (length values) slots
      then Some (map (fun value => Sequence [value]) values)
      else None
  | EmptyCollection layout =>
      if Nat.eqb (length values) 0
      then Some (empty_collections layout)
      else None
  | SingletonCollection layout => singleton_collections layout values
  | AppendCollection layout =>
      if Nat.eqb (length values) (length layout + length layout)
      then append_collections
             layout (firstn (length layout) values) (skipn (length layout) values)
      else None
  | FinalizeCollection layout => finalize_collections layout values
  | Tuple slots =>
      if Nat.eqb (length values) slots
      then Some [Sequence values]
      else None
  | UnitSlots slots =>
      if Nat.eqb (length values) 0
      then Some (repeat (Atom 0) slots)
      else None
  end.

Record ReductionPlan : Type := {
  reduction_arity : nat;
  reduction_tag : nat
}.

Definition apply_reduction (plan : ReductionPlan) (values : list Value)
    : option Value :=
  if Nat.eqb (length values) (reduction_arity plan)
  then Some (Atom (reduction_tag plan))
  else None.

Lemma empty_collections_length :
  forall layout, length (empty_collections layout) = length layout.
Proof.
  induction layout; simpl; congruence.
Qed.

Lemma singleton_collections_length :
  forall layout values output,
    singleton_collections layout values = Some output ->
    length values = length layout /\ length output = length layout.
Proof.
  induction layout as [| kind layout IH]; intros values output H.
  - destruct values; simpl in H; try discriminate. inversion H. auto.
  - destruct values as [| value values]; simpl in H; try discriminate.
    destruct (singleton_collections layout values) as [rest|] eqn:Hrest;
      try discriminate.
    inversion H. subst output. specialize (IH values rest Hrest).
    destruct IH. simpl. split; congruence.
Qed.

Lemma append_collections_length :
  forall layout prefixes lasts output,
    append_collections layout prefixes lasts = Some output ->
    length prefixes = length layout /\
    length lasts = length layout /\
    length output = length layout.
Proof.
  induction layout as [| kind layout IH]; intros prefixes lasts output H.
  - destruct prefixes, lasts; simpl in H; try discriminate. inversion H. auto.
  - destruct prefixes as [| prefix prefixes].
    + simpl in H. discriminate.
    + destruct prefix as [atom | sequence | prefix_kind entries];
        destruct lasts as [| last lasts]; simpl in H; try discriminate.
      destruct (CollectionKind_eq_dec kind prefix_kind) as [Hequal | Hunequal].
      * destruct (append_collections layout prefixes lasts) as [rest|] eqn:Hrest.
        -- inversion H.
           specialize (IH prefixes lasts rest Hrest).
           destruct IH as [Hprefixes [Hlasts Houtput]]. split.
           ++ simpl. rewrite Hprefixes. reflexivity.
           ++ split.
              ** simpl. rewrite Hlasts. reflexivity.
              ** simpl. f_equal. exact Houtput.
        -- discriminate.
      * discriminate.
Qed.

Lemma finalize_collections_length :
  forall layout values output,
    finalize_collections layout values = Some output ->
    length values = length layout /\ length output = length layout.
Proof.
  induction layout as [| kind layout IH]; intros values output H.
  - destruct values; simpl in H; try discriminate. inversion H. auto.
  - destruct values as [| value values].
    + simpl in H. discriminate.
    + simpl in H.
      destruct value as [atom | sequence | value_kind entries].
      * discriminate.
      * discriminate.
      * destruct (CollectionKind_eq_dec kind value_kind) as [Hequal | Hunequal].
        -- destruct (finalize_collections layout values) as [rest|] eqn:Hrest.
           ++ inversion H.
              specialize (IH values rest Hrest).
              destruct IH as [Hvalues Houtput]. split.
              ** simpl. rewrite Hvalues. reflexivity.
              ** simpl. f_equal. exact Houtput.
           ++ discriminate.
        -- discriminate.
Qed.

Theorem successful_auxiliary_has_declared_output_arity :
  forall semantic values output,
    apply_auxiliary semantic values = Some output ->
    length output = output_arity semantic.
Proof.
  intros semantic values output H. destruct semantic; simpl in H.
  - destruct (Nat.eqb (length values) 0); try discriminate.
    inversion H. apply repeat_length.
  - destruct (Nat.eqb (length values) n) eqn:Heq; try discriminate.
    inversion H. rewrite length_map. apply Nat.eqb_eq. exact Heq.
  - destruct (Nat.eqb (length values) 0); try discriminate.
    inversion H. apply empty_collections_length.
  - pose proof (singleton_collections_length _ _ _ H) as [_ Hlength]. exact Hlength.
  - destruct (Nat.eqb (length values) (length l + length l)); try discriminate.
    pose proof (append_collections_length _ _ _ _ H) as [_ [_ Hlength]]. exact Hlength.
  - pose proof (finalize_collections_length _ _ _ H) as [_ Hlength]. exact Hlength.
  - destruct (Nat.eqb (length values) n); try discriminate. inversion H. reflexivity.
  - destruct (Nat.eqb (length values) 0); try discriminate.
    inversion H. apply repeat_length.
Qed.

Theorem append_list_collection_preserves_source_order :
  forall prefix last,
    append_collections [ListKind] [Collection ListKind prefix] [last] =
      Some [Collection ListKind (prefix ++ [last])].
Proof. reflexivity. Qed.

Theorem tuple_has_one_output_and_exact_input_arity :
  forall slots values output,
    apply_auxiliary (Tuple slots) values = Some output ->
    length values = slots /\ output = [Sequence values].
Proof.
  intros slots values output H. simpl in H.
  destruct (Nat.eqb (length values) slots) eqn:Heq; try discriminate.
  inversion H. split; [apply Nat.eqb_eq; exact Heq | reflexivity].
Qed.

Theorem reduction_rejects_wrong_arity :
  forall plan values,
    length values <> reduction_arity plan ->
    apply_reduction plan values = None.
Proof.
  intros plan values Hneq. unfold apply_reduction.
  destruct (Nat.eqb (length values) (reduction_arity plan)) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Theorem successful_reduction_has_exact_arity :
  forall plan values output,
    apply_reduction plan values = Some output ->
    length values = reduction_arity plan.
Proof.
  intros plan values output H. unfold apply_reduction in H.
  destruct (Nat.eqb (length values) (reduction_arity plan)) eqn:Heq;
    try discriminate.
  apply Nat.eqb_eq. exact Heq.
Qed.

Print Assumptions successful_auxiliary_has_declared_output_arity.
Print Assumptions append_list_collection_preserves_source_order.
Print Assumptions tuple_has_one_output_and_exact_input_arity.
Print Assumptions reduction_rejects_wrong_arity.
Print Assumptions successful_reduction_has_exact_arity.
