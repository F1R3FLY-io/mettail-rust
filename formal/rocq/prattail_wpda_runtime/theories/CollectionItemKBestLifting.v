(*
 * CollectionItemKBestLifting: the formal contract for lifting symbols hidden
 * below ordered SPPF containers into the existing lazy k-best coordinate
 * product.
 *
 * The old implementation mapped every collection item to its first raw
 * derivation.  That transformation is neither complete nor natural: changing
 * forest insertion order can change an enclosing AST even when the session's
 * election order is unchanged.  The replacement traverses the container
 * shape with an explicit worklist, assigns one coordinate to every symbol in
 * source order, and realizes the selected Cartesian point.  The abstract
 * binary sequence below represents an arbitrary finite ordered collection;
 * [collection] supplies the usual list encoding.
 *
 * This file deliberately uses only lightweight Stdlib developments.  It has
 * no admissions or opaque global assumptions and is intended to compile under
 * a small RSS cap before the Rust walker is changed.
 *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Set Implicit Arguments.

Section ExplicitContainerTraversal.

Variable A : Type.

Inductive Container : Type :=
| Slot : A -> Container
| Leaf : Container
| Sequence : Container -> Container -> Container
| Optional : option Container -> Container.

Fixpoint slots (shape : Container) : list A :=
  match shape with
  | Slot value => [value]
  | Leaf => []
  | Sequence first second => slots first ++ slots second
  | Optional None => []
  | Optional (Some inner) => slots inner
  end.

Fixpoint collection (items : list Container) : Container :=
  match items with
  | [] => Leaf
  | item :: rest => Sequence item (collection rest)
  end.

Lemma slots_collection :
  forall items,
    slots (collection items) = flat_map slots items.
Proof.
  induction items as [|item rest IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Fixpoint pending_slots (work : list Container) : list A :=
  match work with
  | [] => []
  | item :: rest => slots item ++ pending_slots rest
  end.

Record TraversalState : Type := {
  pending : list Container;
  produced : list A
}.

Definition traversal_denotation (state : TraversalState) : list A :=
  produced state ++ pending_slots (pending state).

Inductive traversal_step : TraversalState -> TraversalState -> Prop :=
| StepSlot : forall value rest output,
    traversal_step
      {| pending := Slot value :: rest; produced := output |}
      {| pending := rest; produced := output ++ [value] |}
| StepLeaf : forall rest output,
    traversal_step
      {| pending := Leaf :: rest; produced := output |}
      {| pending := rest; produced := output |}
| StepSequence : forall first second rest output,
    traversal_step
      {| pending := Sequence first second :: rest; produced := output |}
      {| pending := first :: second :: rest; produced := output |}
| StepOptionalNone : forall rest output,
    traversal_step
      {| pending := Optional None :: rest; produced := output |}
      {| pending := rest; produced := output |}
| StepOptionalSome : forall inner rest output,
    traversal_step
      {| pending := Optional (Some inner) :: rest; produced := output |}
      {| pending := inner :: rest; produced := output |}.

Theorem traversal_step_preserves_source_order :
  forall before after,
    traversal_step before after ->
    traversal_denotation before = traversal_denotation after.
Proof.
  intros before after Hstep.
  inversion Hstep; subst; unfold traversal_denotation; cbn.
  - change
      (output ++ ([value] ++ pending_slots rest) =
       (output ++ [value]) ++ pending_slots rest).
    apply app_assoc.
  - reflexivity.
  - rewrite <- (app_assoc (slots first) (slots second) (pending_slots rest)).
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint container_size (shape : Container) : nat :=
  match shape with
  | Slot _ | Leaf => 1
  | Sequence first second => 1 + container_size first + container_size second
  | Optional None => 1
  | Optional (Some inner) => 1 + container_size inner
  end.

Fixpoint pending_size (work : list Container) : nat :=
  match work with
  | [] => 0
  | item :: rest => container_size item + pending_size rest
  end.

Definition traversal_measure (state : TraversalState) : nat :=
  pending_size (pending state).

Theorem traversal_step_strictly_decreases :
  forall before after,
    traversal_step before after ->
    traversal_measure after < traversal_measure before.
Proof.
  intros before after Hstep.
  inversion Hstep; subst; unfold traversal_measure; cbn; lia.
Qed.

Theorem terminal_traversal_is_exact :
  forall state expected,
    traversal_denotation state = expected ->
    pending state = [] ->
    produced state = expected.
Proof.
  intros state expected Hinvariant Hdone.
  unfold traversal_denotation in Hinvariant.
  rewrite Hdone in Hinvariant.
  cbn in Hinvariant.
  now rewrite app_nil_r in Hinvariant.
Qed.

Corollary terminal_traversal_preserves_every_slot_position :
  forall state expected index,
    traversal_denotation state = expected ->
    pending state = [] ->
    nth_error (produced state) index = nth_error expected index.
Proof.
  intros state expected index Hinvariant Hdone.
  now rewrite (terminal_traversal_is_exact state Hinvariant Hdone).
Qed.

End ExplicitContainerTraversal.

Section CartesianCoordinateLifting.

Variable A : Type.

Fixpoint cartesian (families : list (list A)) : list (list A) :=
  match families with
  | [] => [[]]
  | family :: rest =>
      flat_map
        (fun value => map (fun suffix => value :: suffix) (cartesian rest))
        family
  end.

Lemma in_flat_map_exact :
  forall (B C : Type) (f : B -> list C) values result,
    In result (flat_map f values) <->
    exists value, In value values /\ In result (f value).
Proof.
  intros B C f values.
  induction values as [|value rest IH]; intro result; cbn.
  - split; [contradiction | intros [? [H _]]; contradiction].
  - rewrite in_app_iff, IH.
    split.
    + intros [Here | Later].
      * exists value. split; [now left | exact Here].
      * destruct Later as [found [Hfound Hin]].
        exists found. split; [now right | exact Hin].
    + intros [found [[-> | Hfound] Hin]].
      * now left.
      * right. now exists found.
Qed.

Theorem cartesian_sound_and_complete :
  forall families choice,
    In choice (cartesian families) <->
    Forall2 (fun value family => In value family) choice families.
Proof.
  induction families as [|family rest IH]; intro choice; cbn.
  - split.
    + intros [Hchoice | impossible].
      * inversion Hchoice. constructor.
      * contradiction.
    + intro Hall. inversion Hall. now left.
  - rewrite in_flat_map_exact.
    split.
    + intros [value [HinFamily HinMapped]].
      apply in_map_iff in HinMapped.
      destruct HinMapped as [suffix [Hchoice HinSuffix]].
      subst choice.
      constructor; [exact HinFamily |].
      now apply IH.
    + destruct choice as [|value suffix].
      * intro Hall. inversion Hall.
      * intro Hall.
        inversion Hall as [|value' suffix' family' rest' HinFamily Hrest]; subst.
      exists value. split; [exact HinFamily |].
      apply in_map_iff.
      exists suffix. split; [reflexivity |].
      now apply IH.
Qed.

Fixpoint select_coordinate
  (families : list (list A))
  (coordinate : list nat) : option (list A) :=
  match families, coordinate with
  | [], [] => Some []
  | family :: rest, index :: suffix =>
      match nth_error family index, select_coordinate rest suffix with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint coordinate_product (arities : list nat) : list (list nat) :=
  match arities with
  | [] => [[]]
  | arity :: rest =>
      flat_map
        (fun index => map (fun suffix => index :: suffix) (coordinate_product rest))
        (seq 0 arity)
  end.

Definition coordinates (families : list (list A)) : list (list nat) :=
  coordinate_product (map (@length A) families).

Lemma nth_error_member :
  forall (values : list A) index value,
    nth_error values index = Some value -> In value values.
Proof.
  induction values as [|head tail IH]; intros [|index] value Hnth; cbn in Hnth.
  - discriminate.
  - discriminate.
  - now inversion Hnth; left.
  - right. now apply (IH index value).
Qed.

Lemma nth_error_bound :
  forall (values : list A) index value,
    nth_error values index = Some value -> index < length values.
Proof.
  induction values as [|head tail IH]; intros [|index] value Hnth; cbn in Hnth.
  - discriminate.
  - discriminate.
  - cbn. lia.
  - cbn. specialize (IH index value Hnth). lia.
Qed.

Lemma member_has_index :
  forall (values : list A) value,
    In value values -> exists index, nth_error values index = Some value.
Proof.
  induction values as [|head tail IH]; intros value Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists 0. reflexivity.
    + destruct (IH value Hin) as [index Hindex].
      exists (S index). exact Hindex.
Qed.

Theorem coordinate_selection_sound :
  forall families coordinate choice,
    select_coordinate families coordinate = Some choice ->
    In coordinate (coordinates families) /\
    In choice (cartesian families).
Proof.
  induction families as [|family rest IH];
    intros [|index suffix] choice Hselect; cbn in Hselect.
  - inversion Hselect; subst. split; now left.
  - discriminate.
  - discriminate.
  - destruct (nth_error family index) as [value|] eqn:Hvalue; [|discriminate].
    destruct (select_coordinate rest suffix) as [values|] eqn:Hvalues;
      [|discriminate].
    inversion Hselect; subst choice.
    specialize (IH suffix values Hvalues) as [Hcoordinate Hchoice].
    split.
    + unfold coordinates in *; cbn.
      apply in_flat_map_exact.
      exists index. split.
      * apply in_seq. split; [lia |].
        exact (@nth_error_bound family index value Hvalue).
      * apply in_map_iff. exists suffix. now split.
    + apply cartesian_sound_and_complete.
      constructor.
      * exact (@nth_error_member family index value Hvalue).
      * now apply cartesian_sound_and_complete.
Qed.

Theorem coordinate_selection_complete :
  forall families choice,
    In choice (cartesian families) ->
    exists coordinate,
      In coordinate (coordinates families) /\
      select_coordinate families coordinate = Some choice.
Proof.
  intros families choice Hchoice.
  apply cartesian_sound_and_complete in Hchoice.
  induction Hchoice as [|value family values rest HinFamily Hrest IH].
  - exists []. split; [now left | reflexivity].
  - destruct (@member_has_index family value HinFamily) as [index Hindex].
    destruct IH as [suffix [HinSuffix Hselect]].
    exists (index :: suffix). split.
    + unfold coordinates in *; cbn.
      apply in_flat_map_exact.
      exists index. split.
      * apply in_seq. split; [lia |].
        exact (@nth_error_bound family index value Hindex).
      * apply in_map_iff. exists suffix. now split.
    + cbn. now rewrite Hindex, Hselect.
Qed.

Variable W : Type.
Variable one : W.
Variable times : W -> W -> W.
Variable weight : A -> W.

Fixpoint ordered_weight (values : list A) : W :=
  match values with
  | [] => one
  | value :: rest => times (weight value) (ordered_weight rest)
  end.

Theorem selected_weight_is_source_ordered :
  forall families coordinate choice,
    select_coordinate families coordinate = Some choice ->
    ordered_weight choice = fold_right times one (map weight choice).
Proof.
  intros families coordinate choice _.
  induction choice as [|value rest IH]; cbn; [reflexivity | now rewrite IH].
Qed.

End CartesianCoordinateLifting.

Theorem cartesian_naturality :
  forall (A B : Type) (map_value : A -> B) (families : list (list A)),
    @cartesian B (map (map map_value) families) =
    map (map map_value) (@cartesian A families).
Proof.
  intros A B map_value families.
  induction families as [|family rest IH]; cbn.
  - reflexivity.
  - rewrite IH.
    induction family as [|value values IHvalues]; cbn.
    + reflexivity.
    + rewrite IHvalues, map_app.
      f_equal.
      repeat rewrite map_map.
      apply map_ext. intro suffix. reflexivity.
Qed.

Inductive MiniAst : Type :=
| MiniVar : nat -> MiniAst
| MiniNode : nat -> list MiniAst -> MiniAst.

Definition nullary_ambiguity : list (list MiniAst) :=
  [[MiniVar 0; MiniNode 0 []]].

Example first_raw_is_not_collection_complete :
  hd_error (cartesian nullary_ambiguity) = Some [MiniVar 0] /\
  In [MiniNode 0 []] (cartesian nullary_ambiguity).
Proof.
  cbn. intuition.
Qed.

Example nullary_constructor_survives_coordinate_lifting :
  exists coordinate,
    In coordinate (coordinates nullary_ambiguity) /\
    select_coordinate nullary_ambiguity coordinate = Some [MiniNode 0 []].
Proof.
  apply coordinate_selection_complete.
  cbn. intuition.
Qed.

Print Assumptions traversal_step_preserves_source_order.
Print Assumptions traversal_step_strictly_decreases.
Print Assumptions terminal_traversal_preserves_every_slot_position.
Print Assumptions cartesian_sound_and_complete.
Print Assumptions coordinate_selection_sound.
Print Assumptions coordinate_selection_complete.
Print Assumptions selected_weight_is_source_ordered.
Print Assumptions cartesian_naturality.
Print Assumptions first_raw_is_not_collection_complete.
Print Assumptions nullary_constructor_survives_coordinate_lifting.
