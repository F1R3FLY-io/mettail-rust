(** Known-roster variable operations used by the checked binding traversal.

    Source: moniker-0.5.0/src/bound/mod.rs, Vec<Binder> callbacks and
    Var::close_term/open_term. Closing selects the first matching identity;
    opening selects by index only at the current depth. Diagnostic names do
    not determine identity. Closing preserves the source name; opening uses
    the selected binder's name.

    Missing opening indices are represented by None: legacy Moniker panics
    there, whereas the checked interface must refuse. Closing below models
    the mathematical index, agreeing with Moniker's u32 cast only when that
    index is representable. The checked operation rejects larger indices.
    Depth representability is a caller obligation. This is a leaf model,
    not a freshening, resource accounting, or whole-AST traversal proof. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module KnownRosterLeaves.
Section Leaves.
Context {Payload : Type}.

Record FreeName := {
  name_identity : nat;
  name_pretty : option Payload
}.

Inductive LeafVariable :=
| Free (name : FreeName)
| Bound (scope index : nat) (pretty : option Payload).

Inductive Operation := CloneLeaf | OpenLeaf | CloseLeaf.

Fixpoint first_identity (wanted : nat) (identities : list nat)
    : option nat :=
  match identities with
  | [] => None
  | candidate :: rest =>
    if Nat.eqb wanted candidate then Some 0
    else option_map S (first_identity wanted rest)
  end.

Definition roster_lookup wanted (roster : list FreeName) :=
  first_identity wanted (map name_identity roster).

Definition reference_close depth roster variable : LeafVariable :=
  match variable with
  | Bound scope index pretty => Bound scope index pretty
  | Free name =>
    match roster_lookup (name_identity name) roster with
    | None => Free name
    | Some index => Bound depth index (name_pretty name)
    end
  end.

Definition checked_close maximum_index depth roster variable
    : option LeafVariable :=
  match variable with
  | Bound scope index pretty => Some (Bound scope index pretty)
  | Free name =>
    match roster_lookup (name_identity name) roster with
    | None => Some (Free name)
    | Some index =>
      if index <=? maximum_index
      then Some (Bound depth index (name_pretty name))
      else None
    end
  end.

Definition reference_open depth (roster : list FreeName) variable
    : option LeafVariable :=
  match variable with
  | Free name => Some (Free name)
  | Bound scope index pretty =>
    if Nat.eqb scope depth then option_map Free (nth_error roster index)
    else Some (Bound scope index pretty)
  end.

Definition checked_operation operation maximum_index depth roster variable :=
  match operation with
  | CloneLeaf => Some variable
  | CloseLeaf => checked_close maximum_index depth roster variable
  | OpenLeaf => reference_open depth roster variable
  end.

Lemma first_identity_is_in_range :
  forall identities wanted index,
  first_identity wanted identities = Some index ->
  index < length identities.
Proof.
  induction identities as [|candidate rest IH]; intros wanted index H;
    cbn in H; [discriminate|].
  destruct (Nat.eqb wanted candidate).
  - inversion H; subst. cbn. lia.
  - destruct (first_identity wanted rest) as [tail_index|] eqn:HT;
      cbn in H; [|discriminate].
    inversion H; subst.
    specialize (IH wanted tail_index HT). cbn. lia.
Qed.

Theorem roster_lookup_is_in_range :
  forall roster wanted index,
  roster_lookup wanted roster = Some index -> index < length roster.
Proof.
  intros roster wanted index H. unfold roster_lookup in H.
  apply first_identity_is_in_range in H. now rewrite length_map in H.
Qed.

Theorem checked_close_success_matches_reference :
  forall maximum depth roster variable result,
  checked_close maximum depth roster variable = Some result ->
  result = reference_close depth roster variable.
Proof.
  intros maximum depth roster [name|scope index pretty] result H.
  - unfold checked_close, reference_close in *.
    destruct (roster_lookup (name_identity name) roster) as [index|].
    + destruct (index <=? maximum); inversion H; reflexivity.
    + inversion H; reflexivity.
  - inversion H; reflexivity.
Qed.

Theorem matched_close_checks_exact_index :
  forall maximum depth roster name index,
  roster_lookup (name_identity name) roster = Some index ->
  (checked_close maximum depth roster (Free name) =
     Some (Bound depth index (name_pretty name)) <-> index <= maximum).
Proof.
  intros maximum depth roster name index Hlookup.
  unfold checked_close. rewrite Hlookup.
  destruct (index <=? maximum) eqn:HF.
  - apply Nat.leb_le in HF. split; auto.
  - apply Nat.leb_gt in HF. split; [discriminate|lia].
Qed.

Theorem bounded_roster_close_is_total_and_matches_reference :
  forall roster maximum depth variable,
  length roster <= S maximum ->
  checked_close maximum depth roster variable =
    Some (reference_close depth roster variable).
Proof.
  intros roster maximum depth [name|scope index pretty] Hlength;
    [|reflexivity].
  unfold checked_close, reference_close.
  destruct (roster_lookup (name_identity name) roster) as [index|] eqn:HL;
    [|reflexivity].
  pose proof (roster_lookup_is_in_range _ _ _ HL) as HI.
  assert (HF : (index <=? maximum) = true) by (apply Nat.leb_le; lia).
  now rewrite HF.
Qed.

Theorem checked_open_is_exact_reference :
  forall maximum depth roster variable,
  checked_operation OpenLeaf maximum depth roster variable =
  reference_open depth roster variable.
Proof. reflexivity. Qed.

Theorem matching_depth_open_selects_roster_identity_and_pretty :
  forall maximum depth roster index old_pretty selected,
  nth_error roster index = Some selected ->
  checked_operation OpenLeaf maximum depth roster
    (Bound depth index old_pretty) = Some (Free selected).
Proof.
  intros maximum depth roster index old_pretty selected H.
  cbn [checked_operation reference_open]. now rewrite Nat.eqb_refl, H.
Qed.

Theorem missing_matching_depth_index_refuses :
  forall maximum depth roster index pretty,
  nth_error roster index = None ->
  checked_operation OpenLeaf maximum depth roster
    (Bound depth index pretty) = None.
Proof.
  intros maximum depth roster index pretty H.
  cbn [checked_operation reference_open]. now rewrite Nat.eqb_refl, H.
Qed.

Theorem different_depth_open_preserves_bound_variable :
  forall maximum depth roster scope index pretty,
  scope <> depth ->
  checked_operation OpenLeaf maximum depth roster
    (Bound scope index pretty) = Some (Bound scope index pretty).
Proof.
  intros maximum depth roster scope index pretty H.
  cbn [checked_operation reference_open].
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Theorem free_open_is_unchanged :
  forall maximum depth roster name,
  checked_operation OpenLeaf maximum depth roster (Free name) = Some (Free name).
Proof. reflexivity. Qed.

Theorem already_bound_close_is_unchanged :
  forall maximum depth roster scope index pretty,
  checked_operation CloseLeaf maximum depth roster
    (Bound scope index pretty) = Some (Bound scope index pretty).
Proof. reflexivity. Qed.

Theorem clone_is_unchanged :
  forall maximum depth roster variable,
  checked_operation CloneLeaf maximum depth roster variable = Some variable.
Proof. reflexivity. Qed.

Theorem first_matching_identity_wins_despite_later_duplicates :
  forall id first_pretty later_pretty middle tail,
  roster_lookup id
    ({| name_identity := id; name_pretty := first_pretty |} ::
     middle ++ {| name_identity := id; name_pretty := later_pretty |} :: tail) =
  Some 0.
Proof.
  intros. cbn [roster_lookup first_identity map name_identity].
  now rewrite Nat.eqb_refl.
Qed.

Theorem pretty_names_do_not_determine_lookup :
  forall first second wanted,
  map name_identity first = map name_identity second ->
  roster_lookup wanted first = roster_lookup wanted second.
Proof. intros. unfold roster_lookup. now rewrite H. Qed.

Theorem close_preserves_source_pretty_not_binder_pretty :
  forall id source_pretty binder_pretty maximum depth,
  checked_close maximum depth
    [{| name_identity := id; name_pretty := binder_pretty |}]
    (Free {| name_identity := id; name_pretty := source_pretty |}) =
  Some (Bound depth 0 source_pretty).
Proof.
  intros. cbn [checked_close roster_lookup first_identity map
    name_identity name_pretty]. now rewrite Nat.eqb_refl.
Qed.

End Leaves.
Print Assumptions roster_lookup_is_in_range.
Print Assumptions checked_close_success_matches_reference.
Print Assumptions matched_close_checks_exact_index.
Print Assumptions bounded_roster_close_is_total_and_matches_reference.
Print Assumptions checked_open_is_exact_reference.
Print Assumptions matching_depth_open_selects_roster_identity_and_pretty.
Print Assumptions missing_matching_depth_index_refuses.
Print Assumptions different_depth_open_preserves_bound_variable.
Print Assumptions free_open_is_unchanged.
Print Assumptions already_bound_close_is_unchanged.
Print Assumptions clone_is_unchanged.
Print Assumptions first_matching_identity_wins_despite_later_duplicates.
Print Assumptions pretty_names_do_not_determine_lookup.
Print Assumptions close_preserves_source_pretty_not_binder_pretty.
End KnownRosterLeaves.
