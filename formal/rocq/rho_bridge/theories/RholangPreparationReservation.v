(** Logical precharge for the existing direct-preparation worklist.

    Reuse [Allowance], [reserve], and [precharged_action] from the existing
    resource model; no second meter or allocator semantics is introduced.
    The word ceiling checks component sums before their machine counterpart
    is computed. Rust must likewise check components before sums/products.

    [build] is an ordinary functional operation, not a Boolean assertion that
    Rust is correct. Refusal has no published result, and the equations below
    show when its result is independent of [build]. They do not establish
    effects of an arbitrary imperative callback or global allocator recovery.
    Units in the worklist instances are logical slots, NOT physical bytes,
    Vec capacity, RSS, gas, allocator failure, or panic/unwind recovery.

    This is the first preparation increment only. Source traversal, clone,
    constructor, metadata and side-output cost correspondence remain separate.
    Existing constructors and worklist implementations are not replaced. *)
From Stdlib Require Import List Arith Lia.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget.
From RhoBridge Require Import RholangInitialGraphResources RholangWorklistStorage.
Import ListNotations.

Definition preparation_action {A} (cancelled : bool) (ceiling : nat)
    (available : Allowance) (work_parts slot_parts : list nat)
    (build : unit -> option A) : ActionResult A :=
  if cancelled then Refused available else
  match debit_all ceiling work_parts, debit_all ceiling slot_parts with
  | Some _, Some _ =>
      precharged_action false available
        (total_charge work_parts) (total_charge slot_parts) build
  | _, _ => Refused available
  end.

Theorem preparation_cancel_has_no_result :
  forall A ceiling available work slots (build : unit -> option A),
  preparation_action true ceiling available work slots build = Refused available.
Proof. reflexivity. Qed.

Theorem preparation_word_overflow_has_no_result :
  forall A ceiling available work slots (build : unit -> option A),
  debit_all ceiling work = None \/ debit_all ceiling slots = None ->
  preparation_action false ceiling available work slots build = Refused available.
Proof.
  intros A ceiling available work slots build [HW | HS];
    unfold preparation_action; rewrite ?HW, ?HS;
    destruct (debit_all ceiling work); reflexivity.
Qed.

Theorem preparation_overdraw_has_no_result :
  forall A ceiling available work slots (build : unit -> option A),
  reserve available (total_charge work) (total_charge slots) = None ->
  preparation_action false ceiling available work slots build = Refused available.
Proof.
  intros A ceiling available work slots build H.
  unfold preparation_action.
  destruct (debit_all ceiling work); [|reflexivity].
  destruct (debit_all ceiling slots); [|reflexivity].
  apply failed_precharge_is_independent_of_constructor. exact H.
Qed.

Theorem preparation_success_is_the_same_paid_operation :
  forall A cancelled ceiling available work slots (build : unit -> option A) next value,
  preparation_action cancelled ceiling available work slots build = Accepted next value ->
  cancelled = false /\ build tt = Some value /\
  total_charge work <= ceiling /\ total_charge slots <= ceiling /\
  work_left next + total_charge work = work_left available /\
  units_left next + total_charge slots = units_left available.
Proof.
  intros A cancelled ceiling available work slots build next value H.
  destruct cancelled; [discriminate|]. unfold preparation_action in H.
  destruct (debit_all ceiling work) as [remaining_work|] eqn:HW; [|discriminate].
  destruct (debit_all ceiling slots) as [remaining_slots|] eqn:HS; [|discriminate].
  apply successful_action_constructs_only_the_paid_result in H.
  pose proof (successful_sequence_has_exact_total_cost work ceiling remaining_work HW).
  pose proof (successful_sequence_has_exact_total_cost slots ceiling remaining_slots HS).
  intuition lia.
Qed.

Theorem preparation_callback_failure_keeps_the_charge :
  forall A ceiling available work slots rw rs next (build : unit -> option A),
  debit_all ceiling work = Some rw -> debit_all ceiling slots = Some rs ->
  reserve available (total_charge work) (total_charge slots) = Some next ->
  build tt = None ->
  preparation_action false ceiling available work slots build = Refused next.
Proof.
  intros A ceiling available work slots rw rs next build HW HS HP HB.
  unfold preparation_action. rewrite HW, HS.
  eapply callback_failure_does_not_refund; eassumption.
Qed.

(** Sequencing passes the paid allowance onward: a refused later operation
    cannot reset the budget to its value before the earlier operation. *)
Theorem later_overdraw_retains_prior_charges :
  forall A B ceiling available first_work first_slots
    (first : unit -> option A) paid value later_work later_slots
    (later : unit -> option B),
  preparation_action false ceiling available first_work first_slots first =
    Accepted paid value ->
  reserve paid (total_charge later_work) (total_charge later_slots) = None ->
  preparation_action false ceiling paid later_work later_slots later = Refused paid /\
  work_left paid + total_charge first_work = work_left available /\
  units_left paid + total_charge first_slots = units_left available.
Proof.
  intros A B ceiling available first_work first_slots first paid value
    later_work later_slots later Hfirst Hlater.
  apply preparation_success_is_the_same_paid_operation in Hfirst.
  split; [apply preparation_overdraw_has_no_result; exact Hlater|].
  tauto.
Qed.

(** A push reuses the old counter transition verbatim. Counter overflow is
    checked before constructing the returned work stack. The one slot below
    is the inserted logical job, not the allocator's growth policy. *)
Definition push_existing {J} ceiling (job : Work J)
    (work : list (Work J)) (counts : Counts)
    : option (list (Work J) * Counts) :=
  match checked_push_count ceiling job counts with
  | None => None
  | Some next => Some (job :: work, next)
  end.

Definition paid_push {J} cancelled ceiling available (job : Work J) work counts :=
  preparation_action cancelled ceiling available [1] [1]
    (fun _ => push_existing ceiling job work counts).

Theorem paid_push_preserves_exact_existing_counts :
  forall J cancelled ceiling available (job : Work J) work paid next_work next_counts,
  paid_push cancelled ceiling available job work (count_work work) =
    Accepted paid (next_work, next_counts) ->
  next_work = job :: work /\ next_counts = count_work next_work /\
  counts_fit ceiling next_counts = true.
Proof.
  intros J cancelled ceiling available job work paid next_work next_counts H.
  unfold paid_push in H.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct H as [_ [Hbuild _]]. unfold push_existing in Hbuild.
  destruct (checked_push_count ceiling job (count_work work)) as [counts|] eqn:HC;
    [|discriminate].
  inversion Hbuild; subst.
  apply checked_push_success_exact in HC. destruct HC as [HC HF].
  rewrite HC, push_counts_exact in *. auto.
Qed.

(** [checked_suffix] already defines the exact old-prefix/source-order suffix
    operation. Its result-slot charge precedes that operation, including a
    zero-length suffix. Local arity safety is not inferred from global debt. *)
Definition paid_suffix {V} cancelled ceiling available count (values : list V) :=
  preparation_action cancelled ceiling available [1; count] [count]
    (fun _ => checked_suffix count values).

Theorem paid_suffix_preserves_existing_suffix_law :
  forall V cancelled ceiling available count (values prefix suffix : list V) paid,
  paid_suffix cancelled ceiling available count values = Accepted paid (prefix, suffix) ->
  values = prefix ++ suffix /\ length suffix = count.
Proof.
  intros V cancelled ceiling available count values prefix suffix paid H.
  unfold paid_suffix in H.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct H as [_ [Hbuild _]].
  eapply suffix_success_exact. exact Hbuild.
Qed.

(** The temporary child roster is a borrowed list in source order. This
    instance charges its traversal and logical slots, not the later individual
    job pushes. Reversing before LIFO insertion recovers that same order. *)
Definition paid_child_roster {J} cancelled ceiling available (children : list J) :=
  preparation_action cancelled ceiling available [length children] [length children]
    (fun _ => Some children).

Theorem paid_roster_preserves_source_order :
  forall J cancelled ceiling available (children roster : list J) paid,
  paid_child_roster cancelled ceiling available children = Accepted paid roster ->
  roster = children /\ rev (rev roster) = children.
Proof.
  intros J cancelled ceiling available children roster paid H.
  unfold paid_child_roster in H.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct H as [_ [Hbuild _]]. inversion Hbuild; subst.
  split; [reflexivity|apply rev_involutive].
Qed.

(** Initial reservation uses declared logical slot counts, not a theorem that
    a particular numeric capacity equals physical allocator bytes. *)
Definition paid_initial_slots {A} cancelled ceiling available job_slots value_slots
    (initialize : unit -> option A) :=
  preparation_action cancelled ceiling available [1] [job_slots; value_slots] initialize.

Example exact_logical_reservation_is_admitted :
  preparation_action false 8 {| work_left := 3; units_left := 5 |}
    [1; 2] [2; 3] (fun _ => Some 7) =
  Accepted {| work_left := 0; units_left := 0 |} 7.
Proof. reflexivity. Qed.

Example one_under_declared_slots_refuses :
  preparation_action false 8 {| work_left := 3; units_left := 4 |}
    [1; 2] [2; 3] (fun _ => Some 7) =
  Refused {| work_left := 3; units_left := 4 |}.
Proof. reflexivity. Qed.

Example representable_components_can_have_an_overflowing_sum :
  preparation_action false 4 {| work_left := 9; units_left := 9 |}
    [1] [3; 2] (fun _ => Some 7) =
  Refused {| work_left := 9; units_left := 9 |}.
Proof. reflexivity. Qed.

Print Assumptions preparation_cancel_has_no_result.
Print Assumptions preparation_word_overflow_has_no_result.
Print Assumptions preparation_overdraw_has_no_result.
Print Assumptions preparation_success_is_the_same_paid_operation.
Print Assumptions preparation_callback_failure_keeps_the_charge.
Print Assumptions later_overdraw_retains_prior_charges.
Print Assumptions paid_push_preserves_exact_existing_counts.
Print Assumptions paid_suffix_preserves_existing_suffix_law.
Print Assumptions paid_roster_preserves_source_order.
Print Assumptions exact_logical_reservation_is_admitted.
Print Assumptions one_under_declared_slots_refuses.
Print Assumptions representable_components_can_have_an_overflowing_sum.
