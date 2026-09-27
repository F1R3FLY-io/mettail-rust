(** * Producer receipts and finite owned-backend preparation

    Source correspondence: the macro bridge captures language.terms in order,
    then appends auxiliary collection productions. The DDL lowerer emits one
    production per original term and appends no helper productions. Neither
    consumer may reconstruct the original roster by filtering authored handles.
    The producer supplies the authoritative receipt; the equality gate below
    models producer-level transport, not a second roster recovered at runtime.
    The runtime read_receipt gate observes only the stored immutable receipt,
    its bounds, and Core validation's exact selected authored-reference check.
    Producer tests/source correspondence establish where that receipt came from.

    derive_authored_rules admits its event payloads before their original work.
    derive_authored_descriptors admits its whole source domain before entering
    the original helpers. The charges below denote those measured policy domains:
    flat arena nodes, item/reference slots, strings, and admitted helper domains.
    They are NOT a polynomial CPU/instruction bound or a physical allocator/RSS
    bound. A helper whose domain cannot be covered must be refused or expose
    admission observations in its existing worker. No new recognizer is modeled.

    ReconstructionWorkBudget supplies the actual checked-debit operation. The
    remaining balance is threaded through every stage, never reset. A stage's
    private construction state is not published until the entire batch succeeds.
    This says nothing about rolling back external effects of callbacks.
*)
From Stdlib Require Import List Arith Bool Lia.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget.
Import ListNotations.
Local Open Scope type_scope.

Module OwnedBackendPreparation.

Definition producer_receipt {A : Type} (original : list A) := seq 0 (length original).

Theorem original_prefix_lookup_survives_appended_helpers :
  forall (A : Type) (original helpers : list A) index,
  index < length original ->
  nth_error (original ++ helpers) index = nth_error original index.
Proof. intros; apply nth_error_app1; assumption. Qed.

Theorem producer_receipt_selects_only_original_prefix :
  forall (A : Type) (original helpers : list A),
  map (nth_error (original ++ helpers)) (producer_receipt original) =
  map (nth_error original) (producer_receipt original).
Proof.
  intros A original helpers. apply map_ext_in. intros index Member.
  unfold producer_receipt in Member. apply in_seq in Member.
  apply original_prefix_lookup_survives_appended_helpers. lia.
Qed.

Theorem ddl_empty_helper_case : forall (A : Type) (original : list A),
  original ++ [] = original /\
  producer_receipt (original ++ []) = producer_receipt original.
Proof. intros; rewrite app_nil_r; split; reflexivity. Qed.

Definition receipt_in_bounds count receipt :=
  forallb (fun index => index <? count) receipt.

(** Producer-level transport relation. The generic backend has no independent
    authoritative roster with which to perform this equality comparison. *)
Definition admit_receipt count authoritative presented :=
  match presented with
  | None => None
  | Some receipt =>
      if list_eq_dec Nat.eq_dec receipt authoritative then
        if receipt_in_bounds count receipt then Some receipt else None
      else None
  end.

Theorem admitted_receipt_is_exact_not_filtered :
  forall count authoritative presented receipt,
  admit_receipt count authoritative presented = Some receipt ->
  presented = Some authoritative /\ receipt = authoritative /\
  receipt_in_bounds count receipt = true.
Proof.
  intros count authoritative [input|] receipt H; [|discriminate].
  unfold admit_receipt in H.
  destruct (list_eq_dec Nat.eq_dec input authoritative) as [Same|Different];
    [|discriminate].
  destruct (receipt_in_bounds count input) eqn:Bounds; [|discriminate].
  inversion H; subst. repeat split; auto.
Qed.

Theorem successful_receipt_indices_are_in_bounds : forall count receipt index,
  receipt_in_bounds count receipt = true -> In index receipt -> index < count.
Proof.
  intros count receipt index H Member. unfold receipt_in_bounds in H.
  rewrite forallb_forall in H. specialize (H index Member).
  now apply Nat.ltb_lt in H.
Qed.

Theorem unavailable_receipt_is_refused : forall count authoritative,
  admit_receipt count authoritative None = None.
Proof. reflexivity. Qed.

Theorem changed_receipt_is_refused : forall count authoritative receipt,
  receipt <> authoritative -> admit_receipt count authoritative (Some receipt) = None.
Proof.
  intros count authoritative receipt Different. unfold admit_receipt.
  destruct (list_eq_dec Nat.eq_dec receipt authoritative); congruence.
Qed.

Theorem invalid_receipt_is_refused : forall count authoritative,
  receipt_in_bounds count authoritative = false ->
  admit_receipt count authoritative (Some authoritative) = None.
Proof.
  intros count authoritative Invalid. unfold admit_receipt.
  destruct (list_eq_dec Nat.eq_dec authoritative authoritative); [now rewrite Invalid|congruence].
Qed.

(** Concrete consumer boundary: all_authored is the result of Core's checked
    reference validation for precisely the presented receipt. It is not a
    permission to filter missing authored handles or synthesize a new roster. *)
Definition read_receipt count all_authored presented :=
  match presented with
  | None => None
  | Some receipt =>
      if receipt_in_bounds count receipt && all_authored then Some receipt else None
  end.

Theorem read_success_preserves_exact_order_and_multiplicity :
  forall count all_authored presented receipt,
  read_receipt count all_authored presented = Some receipt ->
  presented = Some receipt /\ receipt_in_bounds count receipt = true /\
  all_authored = true.
Proof.
  intros count all_authored [input|] receipt H; [|discriminate].
  unfold read_receipt in H.
  destruct (receipt_in_bounds count input && all_authored) eqn:Valid;
    [|discriminate].
  inversion H; subst. apply andb_true_iff in Valid.
  split; [reflexivity|exact Valid].
Qed.

Theorem read_unavailable_receipt_is_refused : forall count all_authored,
  read_receipt count all_authored None = None.
Proof. reflexivity. Qed.

Theorem read_out_of_bounds_receipt_is_refused : forall count all_authored receipt,
  receipt_in_bounds count receipt = false ->
  read_receipt count all_authored (Some receipt) = None.
Proof. intros; unfold read_receipt; now rewrite H. Qed.

Theorem read_invalid_authored_references_are_refused : forall count receipt,
  read_receipt count false (Some receipt) = None.
Proof. intros; unfold read_receipt; now rewrite andb_false_r. Qed.

Theorem read_valid_receipt_is_returned_unchanged : forall count receipt,
  receipt_in_bounds count receipt = true ->
  read_receipt count true (Some receipt) = Some receipt.
Proof. intros; unfold read_receipt; now rewrite H. Qed.

Section ReceiptDispatch.
Context {Result : Type}.
Variable worker : list nat -> Result.
Definition receipt_dispatch count authoritative presented : option Result * bool :=
  match admit_receipt count authoritative presented with
  | None => (None, false)
  | Some receipt => (Some (worker receipt), true)
  end.

Theorem rejected_receipt_precedes_worker : forall count authoritative presented,
  admit_receipt count authoritative presented = None ->
  receipt_dispatch count authoritative presented = (None, false).
Proof. intros; unfold receipt_dispatch; now rewrite H. Qed.

Theorem successful_dispatch_preserves_exact_receipt :
  forall count authoritative presented receipt,
  admit_receipt count authoritative presented = Some receipt ->
  receipt_dispatch count authoritative presented = (Some (worker authoritative), true).
Proof.
  intros count authoritative presented receipt H.
  pose proof (admitted_receipt_is_exact_not_filtered _ _ _ _ H) as [_ [Same _]].
  unfold receipt_dispatch. rewrite H, Same. reflexivity.
Qed.

Definition read_dispatch count all_authored presented : option Result * bool :=
  match read_receipt count all_authored presented with
  | None => (None, false)
  | Some receipt => (Some (worker receipt), true)
  end.

Theorem failed_read_precedes_worker : forall count all_authored presented,
  read_receipt count all_authored presented = None ->
  read_dispatch count all_authored presented = (None, false).
Proof. intros; unfold read_dispatch; now rewrite H. Qed.

Theorem successful_read_dispatch_uses_exact_stored_receipt :
  forall count all_authored receipt,
  read_receipt count all_authored (Some receipt) = Some receipt ->
  read_dispatch count all_authored (Some receipt) = (Some (worker receipt), true).
Proof. intros; unfold read_dispatch; now rewrite H. Qed.
End ReceiptDispatch.

Theorem stage_debits_share_one_remaining_capacity : forall first second remaining next,
  debit_all remaining (first ++ second) = Some next ->
  (next + total_charge (first ++ second))%nat = remaining.
Proof. intros; now apply successful_sequence_has_exact_total_cost. Qed.

Theorem separate_stage_debits_equal_one_cumulative_debit :
  forall first second remaining,
  debit_all remaining (first ++ second) =
  match debit_all remaining first with
  | None => None
  | Some middle => debit_all middle second
  end.
Proof.
  induction first as [|amount rest IH]; intros second remaining; simpl; [reflexivity|].
  destruct (debit remaining amount); [apply IH|reflexivity].
Qed.

Theorem checked_domain_components_cannot_exceed_machine_capacity :
  forall amounts maximum remaining next,
  remaining <= maximum -> debit_all remaining amounts = Some next ->
  total_charge amounts <= maximum /\ next <= maximum.
Proof. exact component_checks_make_their_later_size_sum_machine_safe. Qed.

Section PrivateBatch.
Context {State Fault : Type}.
Variable exhausted : Fault.
Definition Stage := (list nat * (State -> (Fault + State))).

Fixpoint prepare_batch (stages : list Stage) remaining state
    : Fault + (State * nat) :=
  match stages with
  | [] => inr (state, remaining)
  | (amounts, worker) :: rest =>
      match debit_all remaining amounts with
      | None => inl exhausted
      | Some next =>
          match worker state with
          | inl fault => inl fault
          | inr private => prepare_batch rest next private
          end
      end
  end.

Definition published (result : Fault + (State * nat)) : option State :=
  match result with inl _ => None | inr (artifact, _) => Some artifact end.

Theorem exhausted_domain_precedes_stage_worker : forall amounts worker rest remaining state,
  debit_all remaining amounts = None ->
  prepare_batch ((amounts, worker) :: rest) remaining state = inl exhausted.
Proof. intros; simpl; now rewrite H. Qed.

Theorem worker_failure_prevents_later_stages :
  forall amounts worker rest remaining state next fault,
  debit_all remaining amounts = Some next -> worker state = inl fault ->
  prepare_batch ((amounts, worker) :: rest) remaining state = inl fault.
Proof. intros; simpl; now rewrite H, H0. Qed.

Theorem later_failure_does_not_publish_earlier_private_state :
  forall amounts worker rest remaining state next private fault,
  debit_all remaining amounts = Some next -> worker state = inr private ->
  prepare_batch rest next private = inl fault ->
  published (prepare_batch ((amounts, worker) :: rest) remaining state) = None.
Proof. intros; simpl; now rewrite H, H0, H1. Qed.

Theorem complete_batch_failure_publishes_nothing : forall stages remaining state fault,
  prepare_batch stages remaining state = inl fault ->
  published (prepare_batch stages remaining state) = None.
Proof. intros; now rewrite H. Qed.
End PrivateBatch.

Print Assumptions original_prefix_lookup_survives_appended_helpers.
Print Assumptions producer_receipt_selects_only_original_prefix.
Print Assumptions ddl_empty_helper_case.
Print Assumptions admitted_receipt_is_exact_not_filtered.
Print Assumptions successful_receipt_indices_are_in_bounds.
Print Assumptions unavailable_receipt_is_refused.
Print Assumptions changed_receipt_is_refused.
Print Assumptions invalid_receipt_is_refused.
Print Assumptions read_success_preserves_exact_order_and_multiplicity.
Print Assumptions read_unavailable_receipt_is_refused.
Print Assumptions read_out_of_bounds_receipt_is_refused.
Print Assumptions read_invalid_authored_references_are_refused.
Print Assumptions read_valid_receipt_is_returned_unchanged.
Print Assumptions rejected_receipt_precedes_worker.
Print Assumptions successful_dispatch_preserves_exact_receipt.
Print Assumptions failed_read_precedes_worker.
Print Assumptions successful_read_dispatch_uses_exact_stored_receipt.
Print Assumptions stage_debits_share_one_remaining_capacity.
Print Assumptions separate_stage_debits_equal_one_cumulative_debit.
Print Assumptions checked_domain_components_cannot_exceed_machine_capacity.
Print Assumptions exhausted_domain_precedes_stage_worker.
Print Assumptions worker_failure_prevents_later_stages.
Print Assumptions later_failure_does_not_publish_earlier_private_state.
Print Assumptions complete_batch_failure_publishes_nothing.
End OwnedBackendPreparation.
