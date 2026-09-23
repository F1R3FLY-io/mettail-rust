(** Admission envelope for the ORIGINAL context-to-items event schedule.

    TermContextItemsProjection supplies the concrete source/probe/frame model.
    This file does not define another converter. A list below is a mathematical
    finite execution trace, NOT a runtime allocation or a preflight traversal.
    Runtime admission must execute at the original loop/constructor sites,
    before parameter access, frame growth, item construction, and binding growth.

    Charges bound logical occurrence work and copied payload, not arena node
    count or physical RSS. In particular a backward-only shared Optional DAG
    may revisit the same parameter exponentially often: every ReadParam costs
    one regardless of identity. Name byte sizes are supplied by the actual
    retained reader. Allocation failure is an additional possible refusal;
    successful allocation is not established by this logical-budget model.

    The old infallible wrapper omits these checks. Sufficient budget erases the
    instrumentation; first refusal exposes no converted output and executes no
    suffix. Source-site correspondence, checked machine arithmetic, immutable
    lawful readers, and fallible reservation require separate Rust evidence.
    No theorem below certifies arbitrary callbacks or full parser equivalence.
*)
From Stdlib Require Import List String Arith Lia.
From PrattailWpdaRuntime Require Import TermContextItemsProjection.
Import ListNotations.
Set Implicit Arguments.

Module ContextItemsAdmission.
Module C := TermContextItemsProjection.TermContextItemsProjection.

Definition event_charge (name_bytes : nat -> nat) (event : C.Event) : nat :=
  match event with
  | C.ReadParam _ | C.EnterOptional _ => 1
  | C.MakeNT n | C.MakeBinder n => 1 + name_bytes n
  | C.MakeCollection _ n separator => 1 + name_bytes n + String.length separator
  | C.AddBinding _ _ => 2
  | _ => 0
  end.

Fixpoint spent (charge : C.Event -> nat) (events : list C.Event) : nat :=
  match events with [] => 0 | e :: rest => charge e + spent charge rest end.

Inductive Admission :=
  | Allowed (remaining : nat)
  | Refused (accepted : list C.Event) (next : C.Event)
      (unexecuted_suffix : list C.Event) (remaining : nat).

Fixpoint admit_trace (charge : C.Event -> nat) (budget : nat)
    (events : list C.Event) : Admission :=
  match events with
  | [] => Allowed budget
  | e :: rest =>
      if Nat.leb (charge e) budget then
        match admit_trace charge (budget - charge e) rest with
        | Allowed remaining => Allowed remaining
        | Refused accepted next suffix remaining =>
            Refused (e :: accepted) next suffix remaining
        end
      else Refused [] e rest budget
  end.

Theorem success_conserves_exact_budget : forall charge events budget remaining,
  admit_trace charge budget events = Allowed remaining ->
  spent charge events + remaining = budget.
Proof.
  intros charge events. induction events as [|e rest IH]; intros budget remaining H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (Nat.leb (charge e) budget) eqn:E; [|discriminate].
    apply Nat.leb_le in E.
    destruct (admit_trace charge (budget - charge e) rest) eqn:R; try discriminate.
    inversion H; subst. specialize (IH _ _ R). cbn. lia.
Qed.

Theorem sufficient_budget_preserves_complete_schedule : forall charge events budget,
  spent charge events <= budget ->
  admit_trace charge budget events = Allowed (budget - spent charge events).
Proof.
  intros charge events. induction events as [|e rest IH]; intros budget H.
  - cbn. now rewrite Nat.sub_0_r.
  - cbn in H |- *. assert (E : Nat.leb (charge e) budget = true)
      by (apply Nat.leb_le; lia).
    rewrite E, IH by lia. f_equal. lia.
Qed.

Theorem refusal_stops_before_first_unpaid_event :
  forall charge events budget accepted next suffix remaining,
  admit_trace charge budget events = Refused accepted next suffix remaining ->
  events = accepted ++ next :: suffix /\
  spent charge accepted + remaining = budget /\ remaining < charge next.
Proof.
  intros charge events. induction events as [|e rest IH];
    intros budget accepted next suffix remaining H.
  - discriminate.
  - cbn in H. destruct (Nat.leb (charge e) budget) eqn:E.
    + apply Nat.leb_le in E.
      destruct (admit_trace charge (budget - charge e) rest) eqn:R;
        try discriminate.
      inversion H; subst. specialize (IH _ _ _ _ _ R).
      destruct IH as [Partition [Conservation Unpaid]].
      split; [cbn; now rewrite Partition|]. split; [cbn; lia|exact Unpaid].
    + apply Nat.leb_gt in E. inversion H; subst.
      split; [reflexivity|]. split; [reflexivity|exact E].
Qed.

Fixpoint parameter_visits (events : list C.Event) : nat :=
  match events with
  | [] => 0
  | C.ReadParam _ :: rest => S (parameter_visits rest)
  | _ :: rest => parameter_visits rest
  end.

Theorem visits_are_charged_per_occurrence : forall name_bytes events,
  parameter_visits events <= spent (event_charge name_bytes) events.
Proof.
  intros name_bytes events. induction events as [|e rest IH]; [cbn; lia|].
  destruct e; cbn [parameter_visits spent event_charge]; lia.
Qed.

Theorem accepted_visits_cannot_exceed_budget : forall name_bytes events budget remaining,
  admit_trace (event_charge name_bytes) budget events = Allowed remaining ->
  parameter_visits events <= budget.
Proof.
  intros. pose proof (@success_conserves_exact_budget _ _ _ _ H).
  pose proof (visits_are_charged_per_occurrence name_bytes events). lia.
Qed.

Theorem repeated_identity_still_costs_each_visit : forall name_bytes handle count,
  spent (event_charge name_bytes) (repeat (C.ReadParam handle) count) = count.
Proof. intros. induction count; cbn; congruence. Qed.

Definition execution_trace (result : C.RunResult) : list C.Event :=
  match result with
  | C.Suspended st => C.trace (C.output st)
  | C.Completed out => C.trace out
  | C.BadReader => []
  end.

Theorem original_and_shared_execution_have_identical_admission :
  forall fuel source st charge budget,
  admit_trace charge budget (execution_trace (C.run fuel (C.shared_step source) st)) =
  admit_trace charge budget (execution_trace (C.run fuel (C.source_step source) st)).
Proof.
  intros. now rewrite C.every_finite_execution_preserves_outputs_bindings_and_order.
Qed.

(** Publication is all-or-error: a refused prefix is proof evidence, never an
    output buffer returned to callers. This does not implement rollback of
    arbitrary external effects; the converter's buffers remain private. *)
Definition publish charge budget (out : C.Buffer) : option C.Buffer :=
  match admit_trace charge budget (C.trace out) with
  | Allowed _ => Some out | Refused _ _ _ _ => None end.

Theorem successful_publication_is_exact : forall charge budget out published,
  publish charge budget out = Some published -> published = out.
Proof.
  intros. unfold publish in H.
  destruct (admit_trace charge budget (C.trace out)); inversion H; reflexivity.
Qed.

Theorem refused_publication_returns_no_partial_buffer :
  forall charge budget out accepted next suffix remaining,
  admit_trace charge budget (C.trace out) = Refused accepted next suffix remaining ->
  publish charge budget out = None.
Proof. intros. unfold publish. now rewrite H. Qed.

Theorem sufficient_budget_matches_infallible_output : forall charge budget out,
  spent charge (C.trace out) <= budget -> publish charge budget out = Some out.
Proof.
  intros. unfold publish.
  rewrite sufficient_budget_preserves_complete_schedule by exact H. reflexivity.
Qed.

Print Assumptions success_conserves_exact_budget.
Print Assumptions sufficient_budget_preserves_complete_schedule.
Print Assumptions refusal_stops_before_first_unpaid_event.
Print Assumptions visits_are_charged_per_occurrence.
Print Assumptions accepted_visits_cannot_exceed_budget.
Print Assumptions repeated_identity_still_costs_each_visit.
Print Assumptions original_and_shared_execution_have_identical_admission.
Print Assumptions successful_publication_is_exact.
Print Assumptions refused_publication_returns_no_partial_buffer.
Print Assumptions sufficient_budget_matches_infallible_output.
End ContextItemsAdmission.
