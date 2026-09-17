(** Paid reversal of only the newly appended binding-task batch.

    The generated loop retains two endpoint indices in the existing task
    vector. A task includes its ScopeState and result-slot index: A below is
    the WHOLE task record, not its category or an equality-class identifier.
    One iteration swaps the endpoint records and shrinks the middle by two.
    The exterior is never visited, copied, allocated, or dropped.

    Source association: safe slice.swap at the two proved in-range indices
    performs the endpoint exchange shown by swapped below. This primitive
    memory-move contract is trusted; no statement verifies the Rust library,
    allocator, pointer provenance, panic unwinding, or physical instruction
    count. In particular there is no assumed final-reversal premise.

    Proposed logical source groups: initial endpoint/setup groups cost 3 work
    and 2 scalar records; each loop guard costs 1 work (including terminal);
    a successful iteration costs 6 work and 1 temporary record for right-index
    calculation, left projection, right projection, swap, left advance and
    right retreat. Task payloads are moved, not cloned or inspected. Existing
    owned-output credits and pending-task charges are not charged again.
    The emitter must prepay each group before it executes. The paid-swap laws
    below reuse atomic debit and retain the original vector on refusal.
    Machine-word endpoint checks and source-to-group association remain the
    emitter's obligations. This is a normal-error logical resource model. *)
From Stdlib Require Import List Arith Lia Sorting.Permutation.
From RhoBridge Require Import RholangInitialGraphResources
  RequiredVecBindingReservation GeneratedBindingOutputReservation.
Import ListNotations.

Module PaidTaskBatchReversal.

Section Batch.
Context {A : Type}.

Definition joined (prefix middle suffix : list A) := prefix ++ middle ++ suffix.
Definition swapped (prefix : list A) (first : A) (middle : list A)
    (last : A) (suffix : list A) :=
  joined (prefix ++ [last]) middle (first :: suffix).

(** Each constructor is one actual endpoint step or a terminal guard. The
    recursive premise begins AFTER the endpoint exchange, with smaller middle. *)
Inductive Run : list A -> list A -> list A -> nat -> list A -> Prop :=
| Empty : forall prefix suffix,
    Run prefix [] suffix 0 (joined prefix [] suffix)
| Singleton : forall prefix value suffix,
    Run prefix [value] suffix 0 (joined prefix [value] suffix)
| Exchange : forall prefix first middle last suffix swaps output,
    Run (prefix ++ [last]) middle (first :: suffix) swaps output ->
    Run prefix (first :: middle ++ [last]) suffix (S swaps) output.

Lemma endpoint_indices_are_valid : forall prefix first middle last suffix,
  let source := joined prefix (first :: middle ++ [last]) suffix in
  length prefix < length prefix + S (length middle) /\
  length prefix + S (length middle) < length source /\
  length (first :: middle ++ [last]) = S (S (length middle)).
Proof.
  intros. unfold source, joined. rewrite !length_app. cbn [length].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma endpoint_exchange_preserves_exterior :
  forall prefix first middle last suffix,
  swapped prefix first middle last suffix =
    prefix ++ (last :: middle ++ [first]) ++ suffix.
Proof.
  intros. unfold swapped, joined. rewrite <- !app_assoc. cbn [app].
  now rewrite <- !app_assoc.
Qed.

Theorem completed_batch_is_reversed : forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output ->
  output = joined prefix (rev middle) suffix.
Proof.
  intros prefix middle suffix swaps output RUN. induction RUN.
  - reflexivity.
  - reflexivity.
  - rewrite IHRUN. unfold joined. cbn [rev]. rewrite rev_app_distr.
    cbn [rev]. rewrite <- !app_assoc. cbn [app].
    try rewrite <- !app_assoc. reflexivity.
Qed.

Theorem completed_exterior_is_unchanged : forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output ->
  firstn (length prefix) output = prefix /\
  skipn (length prefix + length middle) output = suffix.
Proof.
  intros prefix middle suffix swaps output RUN.
  rewrite (completed_batch_is_reversed _ _ _ _ _ RUN).
  unfold joined. split.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn.
    now rewrite app_nil_r.
  - replace (length prefix + length middle) with
      (length (prefix ++ rev middle)) by (rewrite length_app, length_rev; reflexivity).
    rewrite app_assoc, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Theorem swap_count_is_derived : forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output ->
  2 * swaps <= length middle /\ length middle <= 2 * swaps + 1.
Proof.
  intros prefix middle suffix swaps output RUN. induction RUN.
  - cbn. lia.
  - cbn. lia.
  - cbn [length]. rewrite length_app. cbn [length]. lia.
Qed.

Theorem swaps_fit_half_width : forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output -> swaps <= length middle / 2.
Proof.
  intros prefix middle suffix swaps output RUN.
  destruct (swap_count_is_derived _ _ _ _ _ RUN) as [BOUND _].
  apply Nat.div_le_lower_bound; lia.
Qed.

Theorem task_occurrences_are_preserved : forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output ->
  Permutation (joined prefix middle suffix) output.
Proof.
  intros prefix middle suffix swaps output RUN.
  rewrite (completed_batch_is_reversed _ _ _ _ _ RUN).
  unfold joined. apply Permutation_app_head, Permutation_app_tail.
  apply Permutation_rev.
Qed.

Theorem output_credits_are_unchanged : forall prefix middle suffix swaps output
    (credit : A -> GeneratedDummyCleanupReservation.GeneratedDummyCleanupReservation.Counts)
    event,
  Run prefix middle suffix swaps output ->
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts
    credit (joined prefix middle suffix) event =
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts
    credit output event.
Proof.
  intros. apply GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts_permutation.
  now apply task_occurrences_are_preserved with (swaps := swaps).
Qed.

Theorem lifo_visits_original_batch : forall batch swaps output,
  Run [] batch [] swaps output -> rev output = batch.
Proof.
  intros batch swaps output RUN.
  rewrite (completed_batch_is_reversed _ _ _ _ _ RUN).
  unfold joined. cbn [app]. rewrite app_nil_r.
  apply RequiredVecBindingReservation.RequiredVecBindingReservation.reverse_push_then_lifo_preserves_sequence.
Qed.

(** Exactly one final guard and one guard per exchange. A refusal before an
    exchange has no additional move, and earlier paid exchanges stay paid. *)
Definition work swaps := 3 + (swaps + 1) + 6 * swaps.
Definition records swaps := 2 + swaps.
Theorem logical_charge_projection : forall swaps,
  work swaps = 4 + 7 * swaps /\ records swaps = 2 + swaps.
Proof. intros. unfold work, records. lia. Qed.

Theorem completed_charge_is_bounded_by_width :
  forall prefix middle suffix swaps output,
  Run prefix middle suffix swaps output ->
  work swaps <= 4 + 7 * (length middle / 2) /\
  records swaps <= 2 + length middle / 2.
Proof.
  intros prefix middle suffix swaps output RUN.
  pose proof (swaps_fit_half_width _ _ _ _ _ RUN).
  unfold work, records. lia.
Qed.

Definition paid_swap cancelled available prefix first middle last suffix :=
  precharged_action cancelled available 6 4
    (fun _ => Some (swapped prefix first middle last suffix)).

Definition after_swap original (result : ActionResult (list A)) :=
  match result with Refused _ => original | Accepted _ next => next end.

Theorem refused_swap_keeps_original :
  forall available prefix first middle last suffix,
  reserve available 6 4 = None ->
  after_swap (joined prefix (first :: middle ++ [last]) suffix)
    (paid_swap false available prefix first middle last suffix) =
  joined prefix (first :: middle ++ [last]) suffix.
Proof.
  intros. unfold paid_swap.
  rewrite failed_precharge_is_independent_of_constructor by assumption.
  reflexivity.
Qed.

Theorem cancelled_swap_keeps_original :
  forall available prefix first middle last suffix,
  after_swap (joined prefix (first :: middle ++ [last]) suffix)
    (paid_swap true available prefix first middle last suffix) =
  joined prefix (first :: middle ++ [last]) suffix.
Proof. reflexivity. Qed.

Theorem accepted_swap_was_prepaid :
  forall cancelled available prefix first middle last suffix paid output,
  paid_swap cancelled available prefix first middle last suffix = Accepted paid output ->
  cancelled = false /\ output = swapped prefix first middle last suffix /\
  work_left paid + 6 = work_left available /\
  units_left paid + 4 = units_left available.
Proof.
  intros. unfold paid_swap in H.
  apply successful_action_constructs_only_the_paid_result in H.
  destruct H as [C [OUT [W U]]]. inversion OUT. subst.
  auto.
Qed.

End Batch.

Print Assumptions completed_batch_is_reversed.
Print Assumptions completed_exterior_is_unchanged.
Print Assumptions swap_count_is_derived.
Print Assumptions swaps_fit_half_width.
Print Assumptions task_occurrences_are_preserved.
Print Assumptions output_credits_are_unchanged.
Print Assumptions lifo_visits_original_batch.
Print Assumptions completed_charge_is_bounded_by_width.
Print Assumptions refused_swap_keeps_original.
Print Assumptions cancelled_swap_keeps_original.
Print Assumptions accepted_swap_was_prepaid.
End PaidTaskBatchReversal.
