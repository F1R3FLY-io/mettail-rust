(* Checked debits for reconstruction's concrete work/storage obligations.
 * Debit before the corresponding traversal or allocation. Multi-part sizes
 * are checked separately, so their unchecked machine-integer sum/product is
 * never required in order to discover that the request exceeds its budget.
 * Units are specified by each caller; these lemmas do not turn element counts
 * into a CPU-time or byte bound for arbitrary semiring implementations.
 *)
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition debit (remaining amount : nat) : option nat :=
  if amount <=? remaining then Some (remaining - amount) else None.

Fixpoint debit_all (remaining : nat) (amounts : list nat) : option nat :=
  match amounts with
  | [] => Some remaining
  | amount :: rest => match debit remaining amount with
      | None => None
      | Some next => debit_all next rest
      end
  end.

Fixpoint total_charge (amounts : list nat) : nat :=
  match amounts with [] => 0 | amount :: rest => amount + total_charge rest end.

Theorem successful_debit_is_exact : forall remaining amount next,
  debit remaining amount = Some next -> next + amount = remaining.
Proof.
  intros remaining amount next H. unfold debit in H.
  destruct (amount <=? remaining) eqn:Hfits; [|discriminate].
  apply Nat.leb_le in Hfits. inversion H; subst. lia.
Qed.

Theorem failed_debit_means_the_requested_charge_does_not_fit : forall remaining amount,
  debit remaining amount = None <-> remaining < amount.
Proof.
  intros remaining amount. unfold debit. destruct (amount <=? remaining) eqn:Hfits.
  - apply Nat.leb_le in Hfits. split; [discriminate|lia].
  - apply Nat.leb_gt in Hfits. split; [intro; exact Hfits|intro; reflexivity].
Qed.

Theorem successful_sequence_has_exact_total_cost : forall amounts remaining next,
  debit_all remaining amounts = Some next -> next + total_charge amounts = remaining.
Proof.
  induction amounts as [|amount rest IH]; intros remaining next Hrun; cbn in Hrun.
  - inversion Hrun; subst. cbn. lia.
  - destruct (debit remaining amount) as [middle|] eqn:Hdebit; [|discriminate].
    pose proof (successful_debit_is_exact remaining amount middle Hdebit).
    pose proof (IH middle next Hrun). cbn. lia.
Qed.

Theorem every_affordable_sequence_succeeds : forall amounts remaining,
  total_charge amounts <= remaining ->
  debit_all remaining amounts = Some (remaining - total_charge amounts).
Proof.
  induction amounts as [|amount rest IH]; intros remaining Hfits; cbn in *.
  - now rewrite Nat.sub_0_r.
  - unfold debit. assert (Hhead : (amount <=? remaining) = true) by (apply Nat.leb_le; lia).
    rewrite Hhead. rewrite IH by lia. f_equal. lia.
Qed.

Theorem debit_sequence_is_exactly_affordable : forall amounts remaining,
  (exists next, debit_all remaining amounts = Some next) <-> total_charge amounts <= remaining.
Proof.
  intros amounts remaining. split.
  - intros [next H]. pose proof (successful_sequence_has_exact_total_cost amounts remaining next H). lia.
  - intro H. exists (remaining - total_charge amounts). now apply every_affordable_sequence_succeeds.
Qed.

Theorem component_checks_make_their_later_size_sum_machine_safe :
  forall amounts maximum remaining next,
  remaining <= maximum -> debit_all remaining amounts = Some next ->
  total_charge amounts <= maximum /\ next <= maximum.
Proof.
  intros amounts maximum remaining next Hmaximum Hrun.
  pose proof (successful_sequence_has_exact_total_cost amounts remaining next Hrun). lia.
Qed.

Theorem positive_control_steps_are_bounded_by_the_initial_budget :
  forall amounts remaining next,
  Forall (fun amount => 0 < amount) amounts ->
  debit_all remaining amounts = Some next -> length amounts <= remaining.
Proof.
  intros amounts remaining next Hpositive Hrun.
  assert (Hcount : length amounts <= total_charge amounts).
  { clear Hrun remaining next. induction Hpositive; cbn; lia. }
  pose proof (successful_sequence_has_exact_total_cost amounts remaining next Hrun). lia.
Qed.

Theorem exhausting_one_charge_prevents_all_later_charges : forall remaining amount rest,
  debit remaining amount = None -> debit_all remaining (amount :: rest) = None.
Proof. intros; cbn. now rewrite H. Qed.

Example a_zero_charge_does_not_invent_work : debit 7 0 = Some 7.
Proof. reflexivity. Qed.

Example exact_budget_is_admitted : debit_all 9 [2; 3; 4] = Some 0.
Proof. reflexivity. Qed.

Example a_late_excess_is_not_partial_success : debit_all 8 [2; 3; 4] = None.
Proof. reflexivity. Qed.

Print Assumptions successful_debit_is_exact.
Print Assumptions failed_debit_means_the_requested_charge_does_not_fit.
Print Assumptions successful_sequence_has_exact_total_cost.
Print Assumptions debit_sequence_is_exactly_affordable.
Print Assumptions component_checks_make_their_later_size_sum_machine_safe.
Print Assumptions positive_control_steps_are_bounded_by_the_initial_budget.
Print Assumptions exhausting_one_charge_prevents_all_later_charges.
