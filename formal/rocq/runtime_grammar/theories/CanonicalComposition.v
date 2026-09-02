From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Definition Key := nat.
Definition Value := nat.
Definition LanguageMap := list (Key * Value).

Fixpoint lookup (key : Key) (values : LanguageMap) : option Value :=
  match values with
  | [] => None
  | (candidate, value) :: rest =>
      if Nat.eqb key candidate then Some value else lookup key rest
  end.

Definition overlay (local imported : LanguageMap) : LanguageMap := local ++ imported.

Definition observationally_equal (left right : LanguageMap) : Prop :=
  forall key, lookup key left = lookup key right.

Lemma lookup_append :
  forall key left right,
    lookup key (left ++ right) =
    match lookup key left with
    | Some value => Some value
    | None => lookup key right
    end.
Proof.
  intros key left. induction left as [| [candidate value] rest IH]; intros right.
  - reflexivity.
  - simpl. destruct (Nat.eqb key candidate); [reflexivity | exact (IH right)].
Qed.

Theorem overlay_local_wins :
  forall key value local imported,
    lookup key local = Some value ->
    lookup key (overlay local imported) = Some value.
Proof.
  intros key value local imported H.
  unfold overlay. rewrite lookup_append, H. reflexivity.
Qed.

Theorem overlay_import_fallback :
  forall key local imported,
    lookup key local = None ->
    lookup key (overlay local imported) = lookup key imported.
Proof.
  intros key local imported H.
  unfold overlay. rewrite lookup_append, H. reflexivity.
Qed.

Theorem overlay_associative :
  forall first second third,
    observationally_equal
      (overlay first (overlay second third))
      (overlay (overlay first second) third).
Proof.
  intros first second third key.
  unfold overlay. rewrite app_assoc. reflexivity.
Qed.

Definition entry_compatible (right : LanguageMap) (entry : Key * Value) : bool :=
  match lookup (fst entry) right with
  | None => true
  | Some value => Nat.eqb (snd entry) value
  end.

Definition extends_merge (left right : LanguageMap) : option LanguageMap :=
  if forallb (entry_compatible right) left
  then Some (overlay left right)
  else None.

Lemma forallb_entry_compatible :
  forall left right,
    forallb (entry_compatible right) left = true ->
    forall key value,
      lookup key left = Some value ->
      lookup key right = None \/ lookup key right = Some value.
Proof.
  intros left. induction left as [| [candidate own] rest IH]; intros right H key value Hlookup.
  - discriminate.
  - simpl in H. unfold entry_compatible in H.
    apply andb_true_iff in H as [Hhead Htail].
    simpl in Hlookup. destruct (Nat.eqb key candidate) eqn:Hkey.
    + apply Nat.eqb_eq in Hkey. subst candidate. inversion Hlookup; subst value.
      destruct (lookup key right) eqn:Hright; [right | left]; auto.
      cbn in Hhead. rewrite Hright in Hhead. cbn in Hhead.
      apply Nat.eqb_eq in Hhead. subst v. reflexivity.
    + eapply IH; eauto.
Qed.

Theorem extends_merge_never_silently_overrides :
  forall left right merged,
    extends_merge left right = Some merged ->
    forall key left_value right_value,
      lookup key left = Some left_value ->
      lookup key right = Some right_value ->
      left_value = right_value.
Proof.
  intros left right merged Hmerge key left_value right_value Hleft Hright.
  unfold extends_merge in Hmerge.
  destruct (forallb (entry_compatible right) left) eqn:Hcheck; [| discriminate].
  inversion Hmerge; subst merged.
  pose proof (forallb_entry_compatible left right Hcheck key left_value Hleft)
    as [Hnone | Hequal].
  - rewrite Hright in Hnone. discriminate.
  - rewrite Hright in Hequal. inversion Hequal. reflexivity.
Qed.

Definition diagnostic_key (key : Key) : bool := Nat.eqb key 0 || Nat.eqb key 1.

Fixpoint strip_diagnostics (values : LanguageMap) : LanguageMap :=
  match values with
  | [] => []
  | (key, value) :: rest =>
      if diagnostic_key key
      then strip_diagnostics rest
      else (key, value) :: strip_diagnostics rest
  end.

Lemma lookup_strip_non_diagnostic :
  forall key values,
    diagnostic_key key = false ->
    lookup key (strip_diagnostics values) = lookup key values.
Proof.
  intros key values Hkey. induction values as [| [candidate value] rest IH].
  - reflexivity.
  - simpl. destruct (diagnostic_key candidate) eqn:Hcandidate.
    + unfold diagnostic_key in Hcandidate, Hkey.
      destruct (Nat.eqb key candidate) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst candidate. rewrite Hcandidate in Hkey. discriminate.
      * apply IH.
    + simpl. destruct (Nat.eqb key candidate); [reflexivity | apply IH].
Qed.

Definition resolving (name : nat) (stack : list nat) : bool :=
  existsb (Nat.eqb name) stack.

Theorem composition_cycle_is_rejected :
  forall name stack,
    In name stack -> resolving name stack = true.
Proof.
  intros name stack Hin. unfold resolving.
  apply existsb_exists. exists name. split; [exact Hin | apply Nat.eqb_refl].
Qed.

Print Assumptions overlay_associative.
Print Assumptions extends_merge_never_silently_overrides.
Print Assumptions composition_cycle_is_rejected.
