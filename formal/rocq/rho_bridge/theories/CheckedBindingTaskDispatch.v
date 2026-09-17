(** Constant-frame factoring of the existing checked binding task dispatch.

    Visit and Assemble tags identify generated category/constructor arms;
    payloads retain the WHOLE original source pointer and destination/child
    slots. A selector and its wrapper are generated from the same arm. The
    wrapper accepts the whole task and checks that discriminant again. None
    below represents the impossible mismatched-wrapper branch, not a Rust
    fallback. Handler bodies are universally quantified functions, not an
    assumed Boolean assertion that a worker implements binding correctly.

    Machine includes the complete post-pop worklist, result slots, owned
    locals and any observation trace. Outcome includes handler-updated meter,
    machine and exact success/error payload. Factoring therefore preserves
    partial handler effects on error; it does not roll them back. The existing
    charge-before-pop, operation.with_state(saved), child scheduling, output
    credits and cleanup remain outside and unchanged.

    New source groups cost three work and one four-unit record: selection/
    function-pointer retention, call, and wrapper payload match. They must be
    admitted before selecting/calling; the same paid allowance enters the
    existing handler. The model uses existing atomic reservation. Rust's
    checked arithmetic, callback diagnostics and cancellation polling are
    source obligations. No theorem here bounds native stack bytes, proves
    compiler noinline behavior, validates raw-pointer provenance, or covers
    allocator failure/panic unwinding. Those require actual source/fixture
    evidence. Ordinary Clone is not changed by this factoring. *)
From Stdlib Require Import Arith.
From RhoBridge Require Import RholangInitialGraphResources.

Module CheckedBindingTaskDispatch.
Section Dispatch.
Context {VisitPayload AssemblePayload Operation Machine Error : Type}.

Inductive Task :=
| Visit (tag : nat) (payload : VisitPayload)
| Assemble (tag : nat) (payload : AssemblePayload).

Definition Outcome := (Allowance * Machine * (unit + Error))%type.
Variable visit_body : nat -> VisitPayload -> Operation -> Allowance -> Machine -> Outcome.
Variable assemble_body : nat -> AssemblePayload -> Operation -> Allowance -> Machine -> Outcome.

Definition original task operation available machine : Outcome :=
  match task with
  | Visit tag payload => visit_body tag payload operation available machine
  | Assemble tag payload => assemble_body tag payload operation available machine
  end.

Definition visit_wrapper selected task operation available machine : option Outcome :=
  match task with
  | Visit tag payload =>
      if Nat.eqb tag selected
      then Some (visit_body tag payload operation available machine) else None
  | Assemble _ _ => None
  end.

Definition assemble_wrapper selected task operation available machine : option Outcome :=
  match task with
  | Assemble tag payload =>
      if Nat.eqb tag selected
      then Some (assemble_body tag payload operation available machine) else None
  | Visit _ _ => None
  end.

Definition select task :=
  match task with
  | Visit tag _ => visit_wrapper tag
  | Assemble tag _ => assemble_wrapper tag
  end.

(** One common Result propagation is identity on the complete outcome,
    including the state and meter produced before an error. *)
Definition propagate (outcome : Outcome) : Outcome :=
  let '(available, machine, result) := outcome in
  match result with
  | inl success => (available, machine, inl success)
  | inr error => (available, machine, inr error)
  end.

Lemma propagate_is_exact : forall outcome, propagate outcome = outcome.
Proof. intros [[available machine] [success|error]]; reflexivity. Qed.

Definition factored task operation available machine :=
  option_map propagate (select task task operation available machine).

Theorem selector_cannot_mismatch_and_preserves_handler :
  forall task operation available machine,
  factored task operation available machine = Some (original task operation available machine).
Proof.
  intros [tag payload|tag payload] operation available machine;
    unfold factored, select, visit_wrapper, assemble_wrapper, original;
    rewrite Nat.eqb_refl; cbn [option_map]; now rewrite propagate_is_exact.
Qed.

Theorem saved_operation_state_is_unchanged :
  forall Saved (with_state : Operation -> Saved -> Operation)
    task operation saved available machine,
  factored task (with_state operation saved) available machine =
    Some (original task (with_state operation saved) available machine).
Proof. intros. apply selector_cannot_mismatch_and_preserves_handler. Qed.

Theorem handler_error_and_partial_state_are_preserved :
  forall task operation available machine after_meter after_machine error,
  original task operation available machine = (after_meter, after_machine, inr error) ->
  factored task operation available machine = Some (after_meter, after_machine, inr error).
Proof. intros. rewrite selector_cannot_mismatch_and_preserves_handler, H. reflexivity. Qed.

Inductive PaidOutcome :=
| StoppedBeforeHandler (remaining : Allowance) (unchanged : Machine)
| CalledHandler (outcome : option Outcome).

Definition paid (cancelled : bool) available task operation machine :=
  if cancelled then StoppedBeforeHandler available machine else
  match reserve available 3 4 with
  | None => StoppedBeforeHandler available machine
  | Some next => CalledHandler (factored task operation next machine)
  end.

Theorem cancelled_dispatch_calls_no_handler : forall available task operation machine,
  paid true available task operation machine = StoppedBeforeHandler available machine.
Proof. reflexivity. Qed.

Theorem exhausted_dispatch_calls_no_handler : forall available task operation machine,
  reserve available 3 4 = None ->
  paid false available task operation machine = StoppedBeforeHandler available machine.
Proof. intros. unfold paid. now rewrite H. Qed.

Theorem admitted_dispatch_calls_exact_original_with_paid_meter :
  forall available next task operation machine,
  reserve available 3 4 = Some next ->
  paid false available task operation machine =
    CalledHandler (Some (original task operation next machine)) /\
  work_left next + 3 = work_left available /\
  units_left next + 4 = units_left available.
Proof.
  intros. split.
  - unfold paid. rewrite H. f_equal. apply selector_cannot_mismatch_and_preserves_handler.
  - now apply successful_reservation_is_exact in H.
Qed.

Theorem cleanup_observation_is_unchanged :
  forall Observation (observe_cleanup : option Outcome -> Observation)
    task operation available machine,
  observe_cleanup (factored task operation available machine) =
    observe_cleanup (Some (original task operation available machine)).
Proof. intros. now rewrite selector_cannot_mismatch_and_preserves_handler. Qed.

End Dispatch.
Print Assumptions selector_cannot_mismatch_and_preserves_handler.
Print Assumptions saved_operation_state_is_unchanged.
Print Assumptions handler_error_and_partial_state_are_preserved.
Print Assumptions cancelled_dispatch_calls_no_handler.
Print Assumptions exhausted_dispatch_calls_no_handler.
Print Assumptions admitted_dispatch_calls_exact_original_with_paid_meter.
Print Assumptions cleanup_observation_is_unchanged.
End CheckedBindingTaskDispatch.
