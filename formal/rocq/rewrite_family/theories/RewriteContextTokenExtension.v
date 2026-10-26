From Stdlib Require Import List Bool PeanoNat Lia.
Require Import LexForkKeywordReservation.
Import ListNotations.

Inductive Kind := Ident | Fixed (name : nat) | Custom (name : nat).

Record Accept := {
  kind : Kind;
  priority : nat
}.

Definition keep (reserved : bool) (value : Accept) : bool :=
  match kind value with Ident => negb reserved | _ => true end.

Definition reserve reserved values := filter (keep reserved) values.

Fixpoint insert (value : Accept) (values : list Accept) : list Accept :=
  match values with
  | [] => [value]
  | head :: tail =>
      if priority head <? priority value then value :: values
      else head :: insert value tail
  end.

Lemma lower_priority_insertion_appends : forall values value,
  Forall (fun old => priority value < priority old) values ->
  insert value values = values ++ [value].
Proof.
  intros values value H. induction H; simpl; [reflexivity|].
  assert (priority x <? priority value = false) as LT by
    (apply Nat.ltb_ge; lia).
  now rewrite LT, IHForall.
Qed.

Theorem custom_reservation_preserves_exact_membership : forall reserved values value name,
  kind value = Custom name ->
  (In value (reserve reserved values) <-> In value values).
Proof.
  intros reserved values value name KIND. unfold reserve.
  rewrite filter_In. unfold keep. rewrite KIND. tauto.
Qed.

Theorem lower_priority_custom_extension_preserves_prior_roster :
  forall reserved values value name,
  kind value = Custom name ->
  Forall (fun old => priority value < priority old) values ->
  reserve reserved (insert value values) = reserve reserved values ++ [value].
Proof.
  intros reserved values value name KIND LOWER.
  rewrite lower_priority_insertion_appends by exact LOWER.
  unfold reserve. rewrite filter_app. simpl. unfold keep at 2.
  rewrite KIND. reflexivity.
Qed.

Theorem custom_extension_preserves_old_primary :
  forall reserved values value name primary tail,
  kind value = Custom name ->
  Forall (fun old => priority value < priority old) values ->
  reserve reserved values = primary :: tail ->
  hd_error (reserve reserved (insert value values)) = Some primary.
Proof.
  intros reserved values value name primary tail KIND LOWER OLD.
  rewrite (lower_priority_custom_extension_preserves_prior_roster
    reserved values value name KIND LOWER), OLD. reflexivity.
Qed.

Theorem secondary_capture_keeps_existing_fork : forall count same_length contextual,
  0 < count ->
  CollectionOpenFork.fall_through false count false false same_length contextual false true
    = false.
Proof.
  intros count same_length contextual NONEMPTY. destruct count; [lia|].
  unfold CollectionOpenFork.fall_through. simpl.
  destruct count; reflexivity.
Qed.

Lemma insertion_preserves_lower_prefix : forall prefix suffix value,
  Forall (fun old => priority value < priority old) prefix ->
  insert value (prefix ++ suffix) = prefix ++ insert value suffix.
Proof.
  intros prefix suffix value LOWER. induction LOWER; simpl; [reflexivity|].
  assert (priority x <? priority value = false) as LT by
    (apply Nat.ltb_ge; lia).
  now rewrite LT, IHLOWER.
Qed.

Lemma insertion_preserves_custom : forall values value,
  Forall (fun x => exists name, kind x = Custom name) values ->
  (exists name, kind value = Custom name) ->
  Forall (fun x => exists name, kind x = Custom name) (insert value values).
Proof.
  intros values value ALL NEW. induction ALL; simpl; [auto|].
  destruct (priority x <? priority value); repeat constructor; auto.
Qed.

Lemma custom_reservation_is_identity : forall values reserved,
  Forall (fun x => exists name, kind x = Custom name) values ->
  reserve reserved values = values.
Proof.
  intros values reserved ALL. induction ALL; [reflexivity|].
  destruct H as [name KIND]. unfold reserve in *. simpl.
  unfold keep at 1. rewrite KIND. now rewrite IHALL.
Qed.

Theorem custom_batch_preserves_exact_old_prefix : forall old fresh reserved,
  Forall (fun x => 0 < priority x) old ->
  Forall (fun x => priority x = 0 /\ exists name, kind x = Custom name) fresh ->
  NoDup (map kind fresh) ->
  (forall value, In value fresh -> ~ In (kind value) (map kind old)) ->
  reserve reserved (fold_right insert old fresh) =
    reserve reserved old ++ fold_right insert [] fresh.
Proof.
  intros old fresh reserved OLD FRESH UNIQUE DISJOINT.
  clear UNIQUE DISJOINT.
  assert (forall suffix,
    fold_right insert (old ++ suffix) fresh =
    old ++ fold_right insert suffix fresh) as PREFIX.
  { induction FRESH as [|value rest [ZERO CUSTOM] REST IH]; intro suffix; simpl.
    - reflexivity.
    - rewrite IH. apply insertion_preserves_lower_prefix.
      rewrite Forall_forall in *. intros x IN. rewrite ZERO. now apply OLD. }
  rewrite <- (app_nil_r old) at 1. rewrite PREFIX.
  unfold reserve at 1. rewrite filter_app.
  f_equal. apply custom_reservation_is_identity.
  clear PREFIX.
  induction FRESH as [|value rest [ZERO CUSTOM] REST IH]; simpl; [constructor|].
  now apply insertion_preserves_custom.
Qed.

Print Assumptions custom_reservation_preserves_exact_membership.
Print Assumptions lower_priority_custom_extension_preserves_prior_roster.
Print Assumptions custom_extension_preserves_old_primary.
Print Assumptions secondary_capture_keeps_existing_fork.
Print Assumptions custom_batch_preserves_exact_old_prefix.
