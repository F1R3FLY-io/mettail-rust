(**
  CollectionComprehension: exact, stack-safe laws for rule metasyntax.

  [Map] and [Zip] in a MeTTaIL rule are not constructors of the object
  language.  They describe a finite collection comprehension which the rule
  matcher or constructor eliminates.  This module fixes the executable laws
  needed by the runtime image:

  - zip is exact, so unequal input lengths are rejected rather than silently
    truncated;
  - a correlated left-hand-side search consumes one driver row per transition
    and never reuses a subject position;
  - mapped rows are spliced into their enclosing collection explicitly.

  The Rust machine implements the transition relation with an explicit FIFO
  frontier.  The strictly decreasing [remaining_rows] measure below is the
  stack-safety and termination argument for each branch; the frontier and work
  budgets bound the breadth of the search.

  Rocq 9.1 compatible.  No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import Bool List PeanoNat Relation_Operators.
From Stdlib Require Import Lia.

Import ListNotations.

Module CollectionComprehension.

(** Exact binary zip.  Unlike the standard library's truncating [combine],
    this partial operation has no value when either input has an unmatched
    suffix. *)
Fixpoint zip_exact {A B : Type} (left : list A) (right : list B)
    : option (list (A * B)) :=
  match left, right with
  | [], [] => Some []
  | left_head :: left_tail, right_head :: right_tail =>
      match zip_exact left_tail right_tail with
      | Some tail => Some ((left_head, right_head) :: tail)
      | None => None
      end
  | _, _ => None
  end.

Theorem zip_exact_preserves_both_projections :
  forall (A B : Type) (left : list A) (right : list B) pairs,
    zip_exact left right = Some pairs ->
    map fst pairs = left /\ map snd pairs = right.
Proof.
  intros A B left.
  induction left as [|left_head left_tail IH]; intros right pairs Hzip;
    destruct right as [|right_head right_tail]; simpl in Hzip;
    try discriminate.
  - inversion Hzip. auto.
  - destruct (zip_exact left_tail right_tail) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hzip; subst pairs. simpl.
    specialize (IH right_tail tail Htail) as [Hleft Hright].
    now rewrite Hleft, Hright.
Qed.

Corollary zip_exact_requires_equal_lengths :
  forall (A B : Type) (left : list A) (right : list B) pairs,
    zip_exact left right = Some pairs ->
    length left = length right /\ length pairs = length left.
Proof.
  intros A B left right pairs Hzip.
  pose proof (zip_exact_preserves_both_projections A B left right pairs Hzip)
    as [Hleft Hright].
  split.
  - rewrite <- Hleft, <- Hright. now rewrite !length_map.
  - rewrite <- Hleft. now rewrite length_map.
Qed.

Theorem equal_lengths_have_an_exact_zip :
  forall (A B : Type) (left : list A) (right : list B),
    length left = length right ->
    exists pairs, zip_exact left right = Some pairs.
Proof.
  intros A B left.
  induction left as [|left_head left_tail IH]; intros right Hlength;
    destruct right as [|right_head right_tail]; simpl in Hlength;
    try discriminate.
  - exists []. reflexivity.
  - injection Hlength as Htails.
    destruct (IH right_tail Htails) as [pairs Hpairs].
    exists ((left_head, right_head) :: pairs). simpl. now rewrite Hpairs.
Qed.

Theorem unequal_lengths_cannot_be_truncated :
  forall (A B : Type) (left : list A) (right : list B),
    length left <> length right -> zip_exact left right = None.
Proof.
  intros A B left right Hlength.
  destruct (zip_exact left right) as [pairs|] eqn:Hzip; [|reflexivity].
  exfalso. apply Hlength.
  now apply (proj1 (zip_exact_requires_equal_lengths A B left right pairs Hzip)).
Qed.

(** Mapping is a separate elimination step over the exact row stream. *)
Definition zip_map_exact {A B C : Type}
    (body : A * B -> C) (left : list A) (right : list B)
    : option (list C) :=
  match zip_exact left right with
  | Some rows => Some (map body rows)
  | None => None
  end.

Theorem zip_map_exact_preserves_cardinality :
  forall (A B C : Type) (body : A * B -> C) left right output,
    zip_map_exact body left right = Some output ->
    length output = length left /\ length left = length right.
Proof.
  intros A B C body left right output Hmap.
  unfold zip_map_exact in Hmap.
  destruct (zip_exact left right) as [rows|] eqn:Hzip; try discriminate.
  inversion Hmap; subst output.
  pose proof (zip_exact_requires_equal_lengths A B left right rows Hzip)
    as [Hequal Hrows].
  split; [now rewrite length_map, Hrows|exact Hequal].
Qed.

(** A map parameter is a lexical row binder.  Its occurrences in the body
    are therefore removed from the free variables of the complete
    comprehension, while occurrences in a source remain free.  The latter
    condition prevents a binder from defining its own input stream. *)
Definition map_free_occurs
    (variable : nat)
    (source_variables body_variables parameters : list nat) : Prop :=
  In variable source_variables \/
  (In variable body_variables /\ ~ In variable parameters).

Theorem bound_map_parameter_is_not_free :
  forall variable source_variables body_variables parameters,
    In variable parameters ->
    ~ In variable source_variables ->
    ~ map_free_occurs variable source_variables body_variables parameters.
Proof.
  intros variable source_variables body_variables parameters Hbound Hsource Hfree.
  destruct Hfree as [Hfree_source | [Hfree_body Hnot_bound]].
  - exact (Hsource Hfree_source).
  - exact (Hnot_bound Hbound).
Qed.

Theorem unbound_body_occurrence_remains_free :
  forall variable source_variables body_variables parameters,
    In variable body_variables ->
    ~ In variable parameters ->
    map_free_occurs variable source_variables body_variables parameters.
Proof. intros. right. auto. Qed.

(** For a declared map parameter, the compositional free-variable summary is
    exact: the parameter is free in the complete comprehension precisely when
    it occurs in a source.  Consequently a canonical admission check can
    reject self-dependent sources and escaped binders by inspecting the free
    variables of every semantic root; it need not re-walk or recursively
    interpret the body. *)
Theorem bound_map_parameter_is_free_iff_used_by_source :
  forall variable source_variables body_variables parameters,
    In variable parameters ->
    (map_free_occurs variable source_variables body_variables parameters
      <-> In variable source_variables).
Proof.
  intros variable source_variables body_variables parameters Hbound.
  split.
  - intros [Hsource | [_ Hnot_bound]].
    + exact Hsource.
    + exfalso. exact (Hnot_bound Hbound).
  - intros Hsource. now left.
Qed.

(** A use summarized by a second parent remains observable when that parent
    does not bind the variable.  This is the shared-DAG case: binding a shared
    body below one map must not erase an occurrence reached along an outside
    edge. *)
Theorem shared_occurrence_remains_free_outside_its_owner :
  forall variable outside_source shared_variables outside_parameters,
    In variable shared_variables ->
    ~ In variable outside_parameters ->
    map_free_occurs
      variable outside_source shared_variables outside_parameters.
Proof. intros. right. auto. Qed.

(** Parameter ownership is unambiguous when the flattened parameter table is
    duplicate-free.  This is the finite-arena condition enforced before any
    binder is used as an executable map parameter. *)
Definition unique_map_parameters (parameter_rows : list (list nat)) : Prop :=
  NoDup (concat parameter_rows).

Theorem unique_map_parameters_have_at_most_one_owner_occurrence :
  forall parameter_rows variable,
    unique_map_parameters parameter_rows ->
    count_occ Nat.eq_dec (concat parameter_rows) variable <= 1.
Proof.
  intros parameter_rows variable Hunique.
  apply (proj1 (NoDup_count_occ Nat.eq_dec (concat parameter_rows))).
  exact Hunique.
Qed.

(** The validator computes the meet of all lexical contexts which reach a
    term.  This list implementation is the executable finite-set
    specification.  Rust uses the equivalent persistent-frame-tree quotient:
    extending a body creates one frame, and lowest common ancestor computes
    this meet without storing a binder set at every term. *)
Definition context_meet (left right : list nat) : list nat :=
  filter
    (fun frame => existsb (Nat.eqb frame) right)
    left.

Theorem frame_in_context_meet :
  forall frame left right,
    In frame (context_meet left right) <->
    In frame left /\ In frame right.
Proof.
  intros frame left right. unfold context_meet.
  rewrite filter_In. split.
  - intros [Hleft Hright]. split; [exact Hleft|].
    apply existsb_exists in Hright.
    destruct Hright as [candidate [Hin Hequal]].
    apply Nat.eqb_eq in Hequal. now subst candidate.
  - intros [Hleft Hright]. split; [exact Hleft|].
    apply existsb_exists. exists frame. split.
    + exact Hright.
    + apply Nat.eqb_refl.
Qed.

Definition context_equivalent (left right : list nat) : Prop :=
  forall frame, In frame left <-> In frame right.

Theorem context_meet_is_commutative :
  forall left right,
    context_equivalent (context_meet left right) (context_meet right left).
Proof.
  intros left right frame. rewrite !frame_in_context_meet. tauto.
Qed.

Theorem context_meet_is_associative :
  forall first second third,
    context_equivalent
      (context_meet (context_meet first second) third)
      (context_meet first (context_meet second third)).
Proof.
  intros first second third frame. rewrite !frame_in_context_meet. tauto.
Qed.

Theorem context_meet_is_idempotent :
  forall context,
    context_equivalent (context_meet context context) context.
Proof.
  intros context frame. rewrite frame_in_context_meet. tauto.
Qed.

(** Every pmap/pzip source uses its parent's context.  All parameters enter
    the body simultaneously; none can define its own source. *)
Definition source_context (parent : list nat) : list nat := parent.
Definition body_context (parameters parent : list nat) : list nat :=
  parameters ++ parent.

Theorem source_context_introduces_no_parameter :
  forall parameter parent,
    ~ In parameter parent -> ~ In parameter (source_context parent).
Proof. intros parameter parent Habsent. exact Habsent. Qed.

Theorem body_context_introduces_every_parameter :
  forall parameter parameters parent,
    In parameter parameters -> In parameter (body_context parameters parent).
Proof.
  intros parameter parameters parent Hparameter.
  unfold body_context. apply in_or_app. now left.
Qed.

(** If any incoming path bypasses an owner's body edge, the meet removes that
    owner.  This is precisely the shared-DAG and multiple-root escape case. *)
Theorem bypass_path_removes_owner_from_join :
  forall owner through_body bypass,
    ~ In owner bypass ->
    ~ In owner (context_meet through_body bypass).
Proof.
  intros owner through_body bypass Hbypass Hin.
  apply frame_in_context_meet in Hin. tauto.
Qed.

Corollary zip_map_exact_rejects_unequal_lengths :
  forall (A B C : Type) (body : A * B -> C) left right,
    length left <> length right ->
    zip_map_exact body left right = None.
Proof.
  intros A B C body left right Hlength.
  unfold zip_map_exact.
  now rewrite (unequal_lengths_cannot_be_truncated A B left right Hlength).
Qed.

(** One candidate row contains the subject positions which can satisfy the
    body for the corresponding driver element.  A machine state stores only
    the unprocessed suffix and the already selected positions, in reverse
    driver order so extension is constant time. *)
Record CorrelationState := {
  remaining_rows : list (list nat);
  selected_reverse : list nat
}.

Definition initial_correlation (rows : list (list nat)) : CorrelationState :=
  {| remaining_rows := rows; selected_reverse := [] |}.

Inductive correlation_step (subject_width : nat)
    : CorrelationState -> CorrelationState -> Prop :=
| CorrelationChoose :
    forall row rows selected position,
      In position row ->
      position < subject_width ->
      ~ In position selected ->
      correlation_step subject_width
        {| remaining_rows := row :: rows;
           selected_reverse := selected |}
        {| remaining_rows := rows;
           selected_reverse := position :: selected |}.

Definition correlation_injective (state : CorrelationState) : Prop :=
  NoDup (selected_reverse state).

Definition correlation_bounded (subject_width : nat)
    (state : CorrelationState) : Prop :=
  Forall (fun position => position < subject_width)
    (selected_reverse state).

Theorem initial_correlation_is_injective_and_bounded :
  forall subject_width rows,
    correlation_injective (initial_correlation rows) /\
    correlation_bounded subject_width (initial_correlation rows).
Proof. intros. split; constructor. Qed.

Theorem correlation_step_preserves_injectivity :
  forall subject_width before after,
    correlation_injective before ->
    correlation_step subject_width before after ->
    correlation_injective after.
Proof.
  intros subject_width before after Hinjective Hstep.
  inversion Hstep; subst. constructor; assumption.
Qed.

Theorem correlation_step_preserves_subject_bounds :
  forall subject_width before after,
    correlation_bounded subject_width before ->
    correlation_step subject_width before after ->
    correlation_bounded subject_width after.
Proof.
  intros subject_width before after Hbounded Hstep.
  inversion Hstep; subst. constructor; assumption.
Qed.

Theorem correlation_step_consumes_exactly_one_driver :
  forall subject_width before after,
    correlation_step subject_width before after ->
    length (remaining_rows before) = S (length (remaining_rows after)) /\
    length (selected_reverse after) = S (length (selected_reverse before)).
Proof. intros subject_width before after Hstep. inversion Hstep; subst; auto. Qed.

Theorem correlation_step_preserves_total_cardinality :
  forall subject_width before after,
    correlation_step subject_width before after ->
    length (remaining_rows before) + length (selected_reverse before) =
    length (remaining_rows after) + length (selected_reverse after).
Proof. intros subject_width before after Hstep. inversion Hstep; subst; simpl; lia. Qed.

Theorem correlation_branch_is_well_founded :
  forall subject_width before after,
    correlation_step subject_width before after ->
    length (remaining_rows after) < length (remaining_rows before).
Proof. intros subject_width before after Hstep. inversion Hstep; subst; simpl; lia. Qed.

Definition correlation_complete (state : CorrelationState) : Prop :=
  remaining_rows state = [].

Theorem correlation_steps_preserve_total_cardinality :
  forall subject_width before after,
    clos_refl_trans_1n CorrelationState (correlation_step subject_width)
      before after ->
    length (remaining_rows before) + length (selected_reverse before) =
    length (remaining_rows after) + length (selected_reverse after).
Proof.
  intros subject_width before after Hsteps.
  induction Hsteps as [state|first middle last Hstep Hsteps IH].
  - reflexivity.
  - transitivity
      (length (remaining_rows middle) + length (selected_reverse middle)).
    + now apply (correlation_step_preserves_total_cardinality subject_width).
    + exact IH.
Qed.

Theorem complete_correlation_selects_exactly_one_position_per_driver :
  forall subject_width rows terminal,
    clos_refl_trans_1n CorrelationState (correlation_step subject_width)
      (initial_correlation rows) terminal ->
    correlation_complete terminal ->
    length (selected_reverse terminal) = length rows.
Proof.
  intros subject_width rows terminal Hsteps Hcomplete.
  pose proof
    (correlation_steps_preserve_total_cardinality
      subject_width (initial_correlation rows) terminal Hsteps) as Htotal.
  unfold initial_correlation in Htotal. simpl in Htotal.
  unfold correlation_complete in Hcomplete.
  rewrite Hcomplete in Htotal. simpl in Htotal. lia.
Qed.

(** Collection construction retains the distinction between one object term
    and a mapped splice.  Flattening happens exactly once at the enclosing
    collection boundary. *)
Inductive CollectionSegment (A : Type) :=
| SegmentElement (element : A)
| SegmentSplice (elements : list A).

Arguments SegmentElement {A} _.
Arguments SegmentSplice {A} _.

Fixpoint flatten_segments {A : Type} (segments : list (CollectionSegment A))
    : list A :=
  match segments with
  | [] => []
  | SegmentElement element :: tail => element :: flatten_segments tail
  | SegmentSplice elements :: tail => elements ++ flatten_segments tail
  end.

Fixpoint segment_width {A : Type} (segments : list (CollectionSegment A)) : nat :=
  match segments with
  | [] => 0
  | SegmentElement _ :: tail => S (segment_width tail)
  | SegmentSplice elements :: tail => length elements + segment_width tail
  end.

Theorem flatten_segments_has_exact_declared_width :
  forall (A : Type) (segments : list (CollectionSegment A)),
    length (flatten_segments segments) = segment_width segments.
Proof.
  intros A segments. induction segments as [|segment tail IH]; simpl; [reflexivity|].
  destruct segment; simpl.
  - now rewrite IH.
  - now rewrite length_app, IH.
Qed.

(** Zip and map are eliminated by the metapattern machine.  Only products are
    object-level structural nodes.  Keeping the two alphabets disjoint makes
    it impossible for a rule meta-operation to leak into a canonical term. *)
Inductive ObjectCollectionNode :=
| ObjectElement (constructor : nat)
| ObjectProduct (product_sort : nat) (factors : list nat).

Inductive CollectionMetaInstruction :=
| MetaMap (source_sorts parameter_sorts : list nat) (target_sort : nat)
| MetaZipExact (left_sort right_sort : nat).

Inductive RuntimeCollectionForm :=
| RuntimeObjectNode (node : ObjectCollectionNode)
| RuntimeMetaInstruction (instruction : CollectionMetaInstruction).

Definition publishable_object_form (form : RuntimeCollectionForm) : bool :=
  match form with
  | RuntimeObjectNode _ => true
  | RuntimeMetaInstruction _ => false
  end.

Theorem map_instruction_is_never_publishable_as_an_object_node :
  forall source_sorts parameter_sorts target_sort,
    publishable_object_form
      (RuntimeMetaInstruction
        (MetaMap source_sorts parameter_sorts target_sort)) = false.
Proof. reflexivity. Qed.

Theorem zip_instruction_is_never_publishable_as_an_object_node :
  forall left_sort right_sort,
    publishable_object_form
      (RuntimeMetaInstruction (MetaZipExact left_sort right_sort)) = false.
Proof. reflexivity. Qed.

End CollectionComprehension.

Print Assumptions CollectionComprehension.zip_exact_preserves_both_projections.
Print Assumptions CollectionComprehension.unequal_lengths_cannot_be_truncated.
Print Assumptions CollectionComprehension.bound_map_parameter_is_not_free.
Print Assumptions CollectionComprehension.unbound_body_occurrence_remains_free.
Print Assumptions CollectionComprehension.bound_map_parameter_is_free_iff_used_by_source.
Print Assumptions CollectionComprehension.shared_occurrence_remains_free_outside_its_owner.
Print Assumptions CollectionComprehension.unique_map_parameters_have_at_most_one_owner_occurrence.
Print Assumptions CollectionComprehension.frame_in_context_meet.
Print Assumptions CollectionComprehension.context_meet_is_commutative.
Print Assumptions CollectionComprehension.context_meet_is_associative.
Print Assumptions CollectionComprehension.context_meet_is_idempotent.
Print Assumptions CollectionComprehension.source_context_introduces_no_parameter.
Print Assumptions CollectionComprehension.body_context_introduces_every_parameter.
Print Assumptions CollectionComprehension.bypass_path_removes_owner_from_join.
Print Assumptions CollectionComprehension.correlation_step_preserves_injectivity.
Print Assumptions CollectionComprehension.correlation_branch_is_well_founded.
Print Assumptions CollectionComprehension.complete_correlation_selects_exactly_one_position_per_driver.
Print Assumptions CollectionComprehension.flatten_segments_has_exact_declared_width.
Print Assumptions CollectionComprehension.map_instruction_is_never_publishable_as_an_object_node.
Print Assumptions CollectionComprehension.zip_instruction_is_never_publishable_as_an_object_node.
