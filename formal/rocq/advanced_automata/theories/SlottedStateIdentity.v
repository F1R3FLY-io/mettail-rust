(*
 * SlottedStateIdentity
 *
 * Zero-admission model of D-E5's canonical state interface. A pattern trace is
 * separated into (1) its constructor/arity skeleton and (2) the source names
 * encountered in left-to-right traversal order. State identity retains the
 * skeleton plus the first-occurrence slot of every name. Consequently names,
 * alpha-renamings, and uniform de-Bruijn shifts never enter the shared key,
 * while repeated-variable partitions remain observable.
 *
 * Rust correspondence:
 *   - slots                    PatternCompiler's first-occurrence SlotId assignment
 *   - slot_map                StateInvocation child-slot -> parent-slot map
 *   - slot_key                StateKey::Var / StateKey::App{op, invocations}
 *   - restore                 PatternEntry::slot_names boundary reconstruction
 *   - installed_channel       language fingerprint + canonical state identity
 *
 * The proofs cover alpha/shift invariance, specificity, slot-map composition,
 * output-name restoration, cross-language isolation, inequivalent-shape
 * injectivity, and structural termination/size. No Admitted, Axioms, or
 * assumptions.
 *)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Definition injective (f : nat -> nat) : Prop :=
  forall x y, f x = f y -> x = y.

Fixpoint first_index (name : nat) (names : list nat) : nat :=
  match names with
  | [] => 0
  | head :: tail =>
      if Nat.eqb name head then 0 else S (first_index name tail)
  end.

Definition slots (names : list nat) : list nat :=
  map (fun name => first_index name names) names.

Record pattern_trace : Type := {
  skeleton : list nat;
  source_names : list nat
}.

Definition rename_trace (f : nat -> nat) (trace : pattern_trace) : pattern_trace :=
  {| skeleton := skeleton trace;
     source_names := map f (source_names trace) |}.

Definition slot_key (trace : pattern_trace) : list nat * list nat :=
  (skeleton trace, slots (source_names trace)).

Definition slot_equiv (left right : pattern_trace) : Prop :=
  skeleton left = skeleton right /\
  slots (source_names left) = slots (source_names right).

Definition installed_channel (fingerprint : nat) (trace : pattern_trace)
  : nat * (list nat * list nat) :=
  (fingerprint, slot_key trace).

Lemma eqb_injective_rename : forall f,
  injective f ->
  forall x y, Nat.eqb (f x) (f y) = Nat.eqb x y.
Proof.
  intros f Hf x y.
  destruct (Nat.eqb x y) eqn:Hxy.
  - apply Nat.eqb_eq in Hxy. subst y. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in Hxy.
    apply Nat.eqb_neq. intro Hrenamed.
    apply Hxy. apply Hf. exact Hrenamed.
Qed.

Lemma first_index_map_injective : forall f,
  injective f ->
  forall names name,
    first_index (f name) (map f names) = first_index name names.
Proof.
  intros f Hf names. induction names as [| head tail IH]; intro name.
  - reflexivity.
  - simpl. rewrite (eqb_injective_rename f Hf name head).
    destruct (Nat.eqb name head); simpl; [reflexivity |].
    f_equal. apply IH.
Qed.

Lemma slots_rename_invariant : forall f,
  injective f ->
  forall names, slots (map f names) = slots names.
Proof.
  intros f Hf names. unfold slots. rewrite map_map.
  apply map_ext. intro name.
  apply first_index_map_injective. exact Hf.
Qed.

Theorem alpha_rename_preserves_slot_key : forall f,
  injective f ->
  forall trace, slot_key (rename_trace f trace) = slot_key trace.
Proof.
  intros f Hf trace. unfold slot_key, rename_trace. simpl.
  rewrite slots_rename_invariant by exact Hf. reflexivity.
Qed.

Theorem slot_quotient_sound_complete : forall left right,
  slot_key left = slot_key right <-> slot_equiv left right.
Proof.
  intros left right. unfold slot_key, slot_equiv. split.
  - intro H. inversion H. auto.
  - intros [Hskeleton Hslots]. rewrite Hskeleton, Hslots. reflexivity.
Qed.

Theorem inequivalent_shapes_have_distinct_channels : forall fingerprint left right,
  ~ slot_equiv left right ->
  installed_channel fingerprint left <> installed_channel fingerprint right.
Proof.
  intros fingerprint left right Hneq Heq.
  apply Hneq. unfold slot_equiv.
  inversion Heq. auto.
Qed.

Theorem installed_languages_are_isolated : forall fp_left fp_right left right,
  fp_left <> fp_right ->
  installed_channel fp_left left <> installed_channel fp_right right.
Proof.
  intros fp_left fp_right left right Hfp Heq.
  inversion Heq. contradiction.
Qed.

Definition linear_pair : pattern_trace :=
  {| skeleton := [2; 2]; source_names := [0; 1] |}.

Definition diagonal_pair : pattern_trace :=
  {| skeleton := [2; 2]; source_names := [0; 0] |}.

Example nonlinear_specificity_is_not_quotiented :
  slot_key linear_pair <> slot_key diagonal_pair.
Proof.
  cbv [slot_key slots linear_pair diagonal_pair first_index].
  discriminate.
Qed.

Lemma first_index_injective_on_members : forall names x y,
  In x names -> In y names ->
  first_index x names = first_index y names -> x = y.
Proof.
  induction names as [| head tail IH]; intros x y Hx Hy Hindex.
  - contradiction.
  - simpl in Hindex.
    destruct (Nat.eqb x head) eqn:Hxhead;
      destruct (Nat.eqb y head) eqn:Hyhead.
    + apply Nat.eqb_eq in Hxhead. apply Nat.eqb_eq in Hyhead. congruence.
    + discriminate.
    + discriminate.
    + apply IH.
      * destruct Hx as [Hx | Hx].
        -- subst x. rewrite Nat.eqb_refl in Hxhead. discriminate.
        -- exact Hx.
      * destruct Hy as [Hy | Hy].
        -- subst y. rewrite Nat.eqb_refl in Hyhead. discriminate.
        -- exact Hy.
      * injection Hindex. trivial.
Qed.

Theorem nominal_equality_iff_slot_equality : forall names x y,
  In x names -> In y names ->
  (x = y <-> first_index x names = first_index y names).
Proof.
  intros names x y Hx Hy. split.
  - intro Heq. subst y. reflexivity.
  - apply first_index_injective_on_members; assumption.
Qed.

Theorem injective_renaming_preserves_capture_distinctions : forall f,
  injective f ->
  forall x y, x <> y -> f x <> f y.
Proof.
  intros f Hf x y Hxy Hrenamed.
  apply Hxy. apply Hf. exact Hrenamed.
Qed.

Definition slot_map (child_names parent_names : list nat) : list nat :=
  map (fun name => first_index name parent_names) child_names.

Theorem slot_map_alpha_invariant : forall f,
  injective f ->
  forall child_names parent_names,
    slot_map (map f child_names) (map f parent_names) =
    slot_map child_names parent_names.
Proof.
  intros f Hf child_names parent_names.
  unfold slot_map. rewrite map_map. apply map_ext. intro name.
  apply first_index_map_injective. exact Hf.
Qed.

Lemma mapped_value_at_first_index : forall (A : Type) names name
  (transform : nat -> A) (default : A),
  In name names ->
  nth (first_index name names) (map transform names) default = transform name.
Proof.
  induction names as [| head tail IH]; intros name transform default Hin.
  - contradiction.
  - simpl. destruct (Nat.eqb name head) eqn:Hname.
    + symmetry. apply f_equal. apply Nat.eqb_eq. exact Hname.
    + apply IH. destruct Hin as [Hin | Hin].
      * subst name. rewrite Nat.eqb_refl in Hname. discriminate.
      * exact Hin.
Qed.

Theorem slot_remap_composes_through_parent : forall child_name parent_names root_names,
  In child_name parent_names ->
  nth (first_index child_name parent_names)
      (slot_map parent_names root_names) 0 =
  first_index child_name root_names.
Proof.
  intros child_name parent_names root_names Hin.
  unfold slot_map.
  apply mapped_value_at_first_index. exact Hin.
Qed.

Definition restore (entry_names slot_values : list nat) (name : nat) : option nat :=
  nth_error slot_values (first_index name entry_names).

Theorem entry_name_restoration_is_alpha_equivariant : forall f,
  injective f ->
  forall entry_names slot_values name,
    restore (map f entry_names) slot_values (f name) =
    restore entry_names slot_values name.
Proof.
  intros f Hf entry_names slot_values name.
  unfold restore. rewrite first_index_map_injective by exact Hf. reflexivity.
Qed.

Definition debruijn_shift (amount index : nat) : nat := amount + index.

Lemma debruijn_shift_injective : forall amount,
  injective (debruijn_shift amount).
Proof.
  unfold injective, debruijn_shift. intros amount x y Heq. lia.
Qed.

Theorem debruijn_shift_preserves_slot_key : forall amount trace,
  slot_key (rename_trace (debruijn_shift amount) trace) = slot_key trace.
Proof.
  intros amount trace.
  apply alpha_rename_preserves_slot_key.
  apply debruijn_shift_injective.
Qed.

Theorem multibinder_shift_preserves_slot_map : forall binder_count child parent,
  slot_map (map (debruijn_shift binder_count) child)
           (map (debruijn_shift binder_count) parent) =
  slot_map child parent.
Proof.
  intros binder_count child parent.
  apply slot_map_alpha_invariant.
  apply debruijn_shift_injective.
Qed.

Theorem slots_terminate_with_linear_output : forall names,
  length (slots names) = length names.
Proof.
  intro names. unfold slots. apply length_map.
Qed.

Theorem slot_map_terminates_with_child_interface_size : forall child parent,
  length (slot_map child parent) = length child.
Proof.
  intros child parent. unfold slot_map. apply length_map.
Qed.

Print Assumptions alpha_rename_preserves_slot_key.
Print Assumptions slot_quotient_sound_complete.
Print Assumptions inequivalent_shapes_have_distinct_channels.
Print Assumptions installed_languages_are_isolated.
Print Assumptions nonlinear_specificity_is_not_quotiented.
Print Assumptions nominal_equality_iff_slot_equality.
Print Assumptions slot_remap_composes_through_parent.
Print Assumptions entry_name_restoration_is_alpha_equivariant.
Print Assumptions debruijn_shift_preserves_slot_key.
Print Assumptions multibinder_shift_preserves_slot_map.
Print Assumptions slots_terminate_with_linear_output.
