(** Shared generated Hash scheduling, not a second hash engine.

    Source: macros/src/gen/term_ops/iterative_hash.rs uses an eager leaf prefix,
    reverse-pushed deferred fields, and category/U8/Usize/Opaque tasks. Ordinary
    and admitted generation share these builders. Opaque construction stores
    a borrowed pointer/callback; ONLY processing that task invokes the native
    Hash. The existing fixed/String/structural Fx leaf providers are reused.

    These lists describe source scheduling and observed native action labels;
    Rust must not allocate an execution plan or intermediate hash-byte buffer.
    The finite event fold below erases admission from the SAME event sequence.
    It is not a recursive AST hash definition, a new scheduler, a termination
    theorem, or a proof that every possible grammar branch has a provider.

    Logical push accounting reuses 2 NativeWork + 1 NativeRecord per task:
    construction/native Vec push and eventual pending-task disposal. Native
    Vec growth uses bounded wrapper arithmetic and at most one allocator
    request; allocator internals, relocation bytes, capacity and wall-clock
    work remain outside this logical convention, as in checked_binding.rs.
    A NativeRecord projects to FOUR callback units, not one. Root Vec header/
    cleanup is separate. Pop and routing are separately admitted; a terminal
    unsuccessful pop/iterator next is still an action that needs admission.

    Task payloads borrow the source; pending disposal never drops child ASTs.
    No scratch hasher is assumed. Refusal can follow earlier native calls and
    the caller must discard that partial local hasher. Unsupported branches
    refuse locally, with no fallback and no whole-profile support claim.
    Source pointers, shared-builder correspondence, concrete native receipts,
    and entry/exit lifecycle remain explicit Rust obligations. No theorem
    bounds arbitrary Hasher or admission callback implementations. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedKeyHashExecution AdmittedStructuralKeyHash
  GeneratedDummyCleanupReservation RholangInitialGraphResources.
Import ListNotations.

Module AdmittedGeneratedHashScheduling.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module D := GeneratedDummyCleanupReservation.

Section Scheduling.
Context {Task Call : Type}.
Definition pop_order (stack : list Task) := rev stack.
Definition deferred_pushes (fields : list (list Task)) := concat (map (@rev Task) (rev fields)).

Theorem reverse_field_pushes_are_flat_reverse : forall fields,
  deferred_pushes fields = rev (concat fields).
Proof.
  intro fields. unfold deferred_pushes. induction fields as [|field rest IH].
  - reflexivity.
  - cbn [rev concat]. rewrite map_app, concat_app. cbn [map concat].
    rewrite app_nil_r, IH, rev_app_distr. reflexivity.
Qed.

Theorem reverse_batch_pops_before_existing_stack : forall stack deferred,
  pop_order (stack ++ rev deferred) = deferred ++ pop_order stack.
Proof. intros. unfold pop_order. now rewrite rev_app_distr, rev_involutive. Qed.

Theorem reverse_fields_preserve_field_and_element_order : forall stack fields,
  pop_order (stack ++ deferred_pushes fields) = concat fields ++ pop_order stack.
Proof. intros. rewrite reverse_field_pushes_are_flat_reverse.
  apply reverse_batch_pops_before_existing_stack. Qed.

Definition calls_of_tasks (calls : Task -> list Call) (tasks : list Task) :=
  concat (map calls tasks).
Theorem eager_prefix_then_deferred_suffix_is_exact : forall calls eager stack fields,
  eager ++ calls_of_tasks calls (pop_order (stack ++ deferred_pushes fields)) =
  (eager ++ calls_of_tasks calls (concat fields)) ++
    calls_of_tasks calls (pop_order stack).
Proof.
  intros. rewrite reverse_fields_preserve_field_and_element_order.
  unfold calls_of_tasks. rewrite map_app, concat_app. now rewrite app_assoc.
Qed.

(** Source specializations: generated option tags are u8, NOT native Option's
    derived signed tag. Category discriminants and Vec length prefixes use
    usize. Binder pattern precedes body even when pre-scope fields defer. *)
Theorem vec_prefix_pops_before_elements : forall stack length_tag elements,
  pop_order (stack ++ rev elements ++ [length_tag]) =
  length_tag :: elements ++ pop_order stack.
Proof.
  intros. unfold pop_order. rewrite !rev_app_distr, rev_involutive.
  cbn [rev app]. reflexivity.
Qed.
Theorem optional_vec_tag_precedes_length_and_elements :
  forall stack some_tag length_tag elements,
  pop_order (stack ++ rev elements ++ [length_tag; some_tag]) =
  some_tag :: length_tag :: elements ++ pop_order stack.
Proof.
  intros. unfold pop_order. rewrite !rev_app_distr, rev_involutive.
  cbn [rev app]. reflexivity.
Qed.
Theorem binder_pattern_precedes_body_after_prefields : forall stack prefields pattern body,
  pop_order (stack ++ [body; pattern] ++ deferred_pushes prefields) =
  concat prefields ++ pattern :: body :: pop_order stack.
Proof.
  intros. rewrite reverse_field_pushes_are_flat_reverse.
  unfold pop_order. rewrite !rev_app_distr, rev_involutive.
  cbn [rev app]. now rewrite <- app_assoc.
Qed.

(** Occurrence counts, not key equality or source subtree ownership. *)
Inductive PendingInventory : list Task -> nat -> nat -> Prop :=
| EmptyInventory : PendingInventory [] 0 0
| PushedBatch : forall pending pushed popped batch,
    PendingInventory pending pushed popped ->
    PendingInventory (pending ++ batch) (pushed + length batch) popped
| PoppedTask : forall pending task pushed popped,
    PendingInventory (pending ++ [task]) pushed popped ->
    PendingInventory pending pushed (S popped).

Theorem pending_inventory_balance : forall pending pushed popped,
  PendingInventory pending pushed popped -> length pending + popped = pushed.
Proof.
  intros pending pushed popped HI. induction HI; cbn [length] in *.
  - reflexivity.
  - rewrite length_app. lia.
  - rewrite length_app in IHHI. cbn [length] in IHHI. lia.
Qed.
Theorem pending_disposal_is_already_prepaid : forall pending pushed popped event,
  PendingInventory pending pushed popped ->
  H.pending_disposal_counts (length pending) event <= H.push_range_counts pushed event.
Proof.
  intros pending pushed popped event HI.
  apply pending_inventory_balance in HI.
  unfold H.pending_disposal_counts, H.push_range_counts. nia.
Qed.
Theorem unused_disposal_credit_is_exact : forall pending pushed popped,
  PendingInventory pending pushed popped -> pushed - popped = length pending.
Proof. intros pending pushed popped HI. apply pending_inventory_balance in HI. lia. Qed.
End Scheduling.

Theorem raw_push_reservation_uses_four_units_per_record : forall width,
  D.weighted D.logical_work_weight (H.push_range_counts width) = 2 * width /\
  D.weighted D.logical_unit_weight (H.push_range_counts width) = 4 * width.
Proof.
  intro width. rewrite D.logical_work_projects_bytes_once,
    D.logical_units_project_records_and_bytes.
  destruct (H.push_range_projection width) as [HW [HR HB]].
  rewrite HW, HR, HB. split; lia.
Qed.

(** HashBag::hash reads total_count, counts.len(), sum_a, sum_b, xor_a, xor_b.
    This is its cached native hash, NOT semantic_hash or key hashing. Two usize
    and four u64 scalar hash groups cost 2 each on the audited Fx64 profile.
    Six field handoffs and one wrapper entry give 19 native work. A separate
    inspection group precedes extracting these fixed metadata. No key is read. *)
Definition cached_bag_native_work := S.struct_work [2; 2; 2; 2; 2; 2].
Theorem cached_bag_six_scalar_native_groups : cached_bag_native_work = 19.
Proof. reflexivity. Qed.

Theorem successful_terminal_pop_still_consumes_work : forall available paid,
  H.paid_counts false available H.pop_counts (fun _ => Some tt) = Accepted paid tt ->
  work_left paid + 1 = work_left available /\ units_left paid = units_left available.
Proof.
  intros available paid HP.
  unfold H.paid_counts in HP.
  apply successful_action_constructs_only_the_paid_result in HP.
  destruct HP as [_ [_ [HW HU]]].
  change (work_left paid + 1 = work_left available) in HW.
  change (units_left paid + 0 = units_left available) in HU. split; lia.
Qed.

Section AdmissionErasure.
Context {Call State : Type}.
Variable apply_native : Call -> State -> State.

(** An event is a proof trace entry from the shared emitter, not a runtime
    instruction or an arbitrary callback-cost oracle. Internal projection/
    routing/task actions emit None; native actions emit their original label.
    Structural leaf metadata supplies several internal events followed by ONE
    whole native call. Receipts retain their existing source-specific laws.
    Unsupported = false models local refusal before its action, not a fallback. *)
Record Event := {
  event_receipt : D.Counts;
  event_call : option Call;
  event_supported : bool
}.
Definition call_list (call : option Call) := match call with None => [] | Some call => [call] end.
Definition ordinary_calls events := concat (map (fun event => call_list (event_call event)) events).
Inductive TraceResult :=
| Finished (remaining : Allowance) (calls : list Call)
| Stopped (remaining : Allowance) (calls : list Call).
Definition observed_calls result := match result with
  | Finished _ calls | Stopped _ calls => calls end.
Definition succeeded result := match result with Finished _ _ => true | Stopped _ _ => false end.
Definition prepend_calls prefix result := match result with
  | Finished remaining calls => Finished remaining (prefix ++ calls)
  | Stopped remaining calls => Stopped remaining (prefix ++ calls)
  end.

(** A fold over the finite observed source trace, reusing precharged_action.
    Native semantic state is interpreted from its emitted original labels;
    admission events neither replace that hasher nor synthesize hash bytes. *)
Fixpoint admitted_events (events : list Event) available :=
  match events with
  | [] => Finished available []
  | event :: rest =>
    if event_supported event then
      match H.paid_counts false available (event_receipt event)
        (fun _ => Some (event_call event)) with
      | Refused remaining => Stopped remaining []
      | Accepted remaining call =>
          prepend_calls (call_list call) (admitted_events rest remaining)
      end
    else Stopped available []
  end.

Lemma prepend_observed_calls : forall prefix result,
  observed_calls (prepend_calls prefix result) = prefix ++ observed_calls result.
Proof. intros prefix []; reflexivity. Qed.
Lemma prepend_preserves_completion : forall prefix result,
  succeeded (prepend_calls prefix result) = succeeded result.
Proof. intros prefix []; reflexivity. Qed.

Theorem admission_success_erases_to_same_native_calls : forall events available,
  succeeded (admitted_events events available) = true ->
  observed_calls (admitted_events events available) = ordinary_calls events.
Proof.
  induction events as [|event rest IH]; intros available HS; [reflexivity|].
  cbn [admitted_events] in *.
  destruct (event_supported event); [|discriminate].
  destruct (H.paid_counts false available (event_receipt event)
    (fun _ => Some (event_call event))) as [remaining|remaining call] eqn:HP;
    [discriminate|].
  apply H.successful_paid_counts_reuses_same_action in HP.
  inversion HP; subst call.
  rewrite prepend_preserves_completion in HS.
  rewrite prepend_observed_calls, (IH remaining HS).
  reflexivity.
Qed.

Theorem every_result_is_an_original_call_prefix : forall events available,
  exists suffix, ordinary_calls events =
    observed_calls (admitted_events events available) ++ suffix.
Proof.
  induction events as [|event rest IH]; intro available.
  - exists []. reflexivity.
  - cbn [admitted_events]. destruct (event_supported event).
    + destruct (H.paid_counts false available (event_receipt event)
        (fun _ => Some (event_call event))) as [remaining|remaining call] eqn:HP.
      * exists (ordinary_calls (event :: rest)). reflexivity.
      * apply H.successful_paid_counts_reuses_same_action in HP.
        inversion HP; subst call. destruct (IH remaining) as [suffix HI].
        exists suffix. rewrite prepend_observed_calls.
        change (call_list (event_call event) ++ ordinary_calls rest =
          (call_list (event_call event) ++
            observed_calls (admitted_events rest remaining)) ++ suffix).
        rewrite HI, app_assoc. reflexivity.
    + exists (ordinary_calls (event :: rest)). reflexivity.
Qed.

Definition resulting_hasher calls state := fold_left (fun state call => apply_native call state) calls state.
Theorem admitted_success_preserves_original_hasher : forall events available state,
  succeeded (admitted_events events available) = true ->
  resulting_hasher (observed_calls (admitted_events events available)) state =
    resulting_hasher (ordinary_calls events) state.
Proof.
  intros events available state HS.
  now rewrite (admission_success_erases_to_same_native_calls _ _ HS).
Qed.

Theorem unsupported_event_refuses_without_its_native_call : forall event rest available,
  event_supported event = false ->
  admitted_events (event :: rest) available = Stopped available [].
Proof. intros event rest available HU. cbn [admitted_events]. now rewrite HU. Qed.

Theorem scheduling_opaque_does_not_hash : forall receipt state,
  resulting_hasher (ordinary_calls
    [{| event_receipt := receipt; event_call := None; event_supported := true |}]) state = state.
Proof. reflexivity. Qed.
End AdmissionErasure.

Print Assumptions reverse_field_pushes_are_flat_reverse.
Print Assumptions reverse_batch_pops_before_existing_stack.
Print Assumptions reverse_fields_preserve_field_and_element_order.
Print Assumptions eager_prefix_then_deferred_suffix_is_exact.
Print Assumptions vec_prefix_pops_before_elements.
Print Assumptions optional_vec_tag_precedes_length_and_elements.
Print Assumptions binder_pattern_precedes_body_after_prefields.
Print Assumptions pending_inventory_balance.
Print Assumptions pending_disposal_is_already_prepaid.
Print Assumptions unused_disposal_credit_is_exact.
Print Assumptions raw_push_reservation_uses_four_units_per_record.
Print Assumptions cached_bag_six_scalar_native_groups.
Print Assumptions successful_terminal_pop_still_consumes_work.
Print Assumptions admission_success_erases_to_same_native_calls.
Print Assumptions every_result_is_an_original_call_prefix.
Print Assumptions admitted_success_preserves_original_hasher.
Print Assumptions unsupported_event_refuses_without_its_native_call.
Print Assumptions scheduling_opaque_does_not_hash.
End AdmittedGeneratedHashScheduling.
