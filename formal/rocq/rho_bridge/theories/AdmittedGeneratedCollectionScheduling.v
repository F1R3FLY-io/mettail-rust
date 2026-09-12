(** Owned continuations in the existing generated comparison scheduler.

    Source: iterative_cmp.rs collection resume adapters, StartCollection /
    ResumeCollection driver arms and cmp_deliver. This is a scheduling
    refinement, not another comparator or a global sorting proof. The paid
    collection core is modeled in AdmittedCollectionComparisonOwnership.

    Start owner construction remains eager; only its first resume is deferred.
    Delivery may discard an unstarted Start without invoking it. A request
    pushes Resume FIRST and its typed child SECOND. Normal Resume supplies
    Some Equal; interception supplies the delivered ordering. Delivery stops
    at the nearest Resume, not the end of the whole stack. Await/Done Equal
    returns to the driver; Done nonEqual starts another outward round.
    Root publication requires a paid terminal pop without a continuation.

    Existing root/task shells cost 2W/1R (four raw units), attempted pop 1W,
    Some dispatch 1W. CallbackBegin pays adapter/core entry; CallbackResult
    pays the returned Compare/Done match. Each costs 1W; core work is separate.
    DriverResult pays callback Option/Ordering routing, also 1W.
    DeliveryRound costs 1W before resumed=false and covers its final gate.
    Every inner pop and Some dispatch remain paid. Interception has no nil
    pop. Eq's auxiliary driver pays local header and Start shell separately,
    uses the same Cmp driver, then pays FinalEquality 1W.

    Shell credit cannot pay for machine roots, rosters or scratch. Owner-slot
    identities and disjoint allocation inventories model Rust moves, not pointer
    value uniqueness. Refusal after either push disposes paid storage: before
    the first push the owner is local; afterwards Resume owns it. Private Rust
    constructors, moves, callback/category correspondence and valid source
    borrows remain explicit obligations. Coq values alone are duplicable.
    No arbitrary callback, allocator, hash-table scan, Eq/Cmp coherence or
    whole-profile bound is inferred.

    Qualified references deliberately avoid re-exporting large imported module
    aliases: the same imported laws are used without duplicating their module
    interfaces in this proof artifact. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedGeneratedComparisonScheduling
  AdmittedCollectionComparisonOwnership AdmittedGeneratedHashScheduling
  AdmittedKeyHashExecution AdmittedStructuralKeyHash IndexedCopySlots
  GeneratedBindingOutputReservation GeneratedDummyCleanupReservation.
Import ListNotations.

Module AdmittedGeneratedCollectionScheduling.

Inductive Task := Borrowed (task : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.BorrowedTask)
| Start (owner callback : nat) | Resume (owner callback : nat).
Definition not_resume task := match task with Resume _ _ => false | _ => true end.
Definition task_owners task := match task with
  | Borrowed _ => [] | Start owner _ | Resume owner _ => [owner] end.
Definition owner_refs tasks := concat (map task_owners tasks).
Definition normal_input task : option (option comparison) := match task with
  | Start _ _ => Some None | Resume _ _ => Some (Some Eq) | Borrowed _ => None end.

Theorem normal_start_and_resume_inputs : forall owner callback,
  normal_input (Start owner callback) = Some None /\
  normal_input (Resume owner callback) = Some (Some Eq).
Proof. intros; split; reflexivity. Qed.
Theorem resume_then_child_visits_child_first : forall stack owner callback child,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pop_order (stack ++ [Resume owner callback; Borrowed child]) =
    Borrowed child :: Resume owner callback :: AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pop_order stack.
Proof. intros. unfold AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pop_order. rewrite rev_app_distr. reflexivity. Qed.
Theorem start_to_resume_transfers_the_same_owner : forall owner callback,
  task_owners (Start owner callback) = task_owners (Resume owner callback).
Proof. reflexivity. Qed.
Theorem owner_references_partition_at_a_stack_split : forall prefix suffix,
  owner_refs (prefix ++ suffix) = owner_refs prefix ++ owner_refs suffix.
Proof. intros. unfold owner_refs. now rewrite map_app, concat_app. Qed.

(** A source list-position witness, not execution of the collection core. *)
Inductive Interception : list Task -> list Task -> nat -> nat -> list Task -> Prop :=
| InterceptHere : forall owner callback rest,
    Interception (Resume owner callback :: rest) [] owner callback rest
| InterceptLater : forall task tasks skipped owner callback rest,
    not_resume task = true -> Interception tasks skipped owner callback rest ->
    Interception (task :: tasks) (task :: skipped) owner callback rest.

Theorem interception_is_at_the_nearest_resume : forall tasks skipped owner callback rest,
  Interception tasks skipped owner callback rest ->
  tasks = skipped ++ Resume owner callback :: rest /\
  Forall (fun task => not_resume task = true) skipped.
Proof.
  intros tasks skipped owner callback rest HI. induction HI.
  - split; [reflexivity|constructor].
  - destruct IHHI as [HE HF]. split.
    + cbn [app]. now rewrite HE.
    + constructor; assumption.
Qed.
Theorem a_nonresume_prefix_reaches_its_continuation : forall skipped owner callback rest,
  Forall (fun task => not_resume task = true) skipped ->
  Interception (skipped ++ Resume owner callback :: rest) skipped owner callback rest.
Proof.
  intros skipped owner callback rest HF. induction HF.
  - apply InterceptHere.
  - cbn [app]. apply InterceptLater; assumption.
Qed.
Theorem an_intercepted_stack_has_no_root_completion_certificate :
  forall tasks skipped owner callback rest,
  Interception tasks skipped owner callback rest ->
  ~ Forall (fun task => not_resume task = true) tasks.
Proof.
  intros tasks skipped owner callback rest HI HF.
  destruct (interception_is_at_the_nearest_resume _ _ _ _ _ HI) as [HE _].
  rewrite HE in HF. apply Forall_app in HF. destruct HF as [_ HT].
  inversion HT as [|task tail HH HR]; subst. discriminate HH.
Qed.

Inductive CallbackOutcome := AwaitChild | Finished (ordering : comparison).
Inductive DeliveryRoute := BackToDriver | ContinueOutward (ordering : comparison).
Definition intercept_result outcome := match outcome with
  | AwaitChild | Finished Eq => BackToDriver
  | Finished Lt => ContinueOutward Lt | Finished Gt => ContinueOutward Gt end.
Theorem callback_result_routes_are_the_original_branches :
  intercept_result AwaitChild = BackToDriver /\
  intercept_result (Finished Eq) = BackToDriver /\
  intercept_result (Finished Lt) = ContinueOutward Lt /\
  intercept_result (Finished Gt) = ContinueOutward Gt.
Proof. repeat split; reflexivity. Qed.

Inductive Group := Existing (group : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.SourceGroup)
| CallbackBegin | CallbackResult | DriverResult | DeliveryRound | FinalEquality.
Definition group_counts group := match group with
  | Existing source => AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.group_counts source | _ => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.work_counts 1 end.
Definition group_work group := match group with
  | Existing source => AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.group_work source | _ => 1 end.
Definition group_units group := match group with
  | Existing source => AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.group_units source | _ => 0 end.
Theorem group_projection_reuses_existing_reservation_parts : forall group,
  GeneratedDummyCleanupReservation.weighted GeneratedDummyCleanupReservation.logical_work_weight (group_counts group) = group_work group /\
  GeneratedDummyCleanupReservation.weighted GeneratedDummyCleanupReservation.logical_unit_weight (group_counts group) = group_units group.
Proof.
  intro group. destruct group; cbn [group_counts group_work group_units].
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.source_group_callback_projection.
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
  - apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
Qed.

Fixpoint skipped_groups count := match count with
  | 0 => []
  | S count => Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.AttemptPop :: Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskDispatch :: skipped_groups count end.
Definition scan_groups (skipped : list Task) (intercepted : bool) :=
  DeliveryRound :: skipped_groups (length skipped) ++
    if intercepted then [Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.AttemptPop; Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskDispatch]
    else [Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.AttemptPop].
Lemma skipped_groups_length : forall count, length (skipped_groups count) = 2 * count.
Proof. induction count; cbn [skipped_groups length]; lia. Qed.
Theorem delivery_scan_has_only_reached_pop_sites : forall (skipped : list Task),
  length (scan_groups skipped true) = 2 * length skipped + 3 /\
  length (scan_groups skipped false) = 2 * length skipped + 2.
Proof.
  intro skipped. unfold scan_groups. split;
    cbn [length]; rewrite length_app, skipped_groups_length; cbn [length]; lia.
Qed.
Definition await_push_groups := [Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskPush; Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskPush].
Definition eq_auxiliary_groups driver :=
  [Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.RootHeader; Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskPush] ++ driver ++ [FinalEquality].
Theorem await_pays_two_distinct_shells :
  map group_work await_push_groups = [2; 2] /\
  map group_units await_push_groups = [4; 4].
Proof. split; reflexivity. Qed.
Theorem equality_auxiliary_groups_bracket_the_original_driver : forall driver,
  eq_auxiliary_groups driver =
  Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.RootHeader :: Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskPush :: driver ++ [FinalEquality].
Proof. reflexivity. Qed.

(** Machine root and buffer inventories are additional to task shells. *)
Definition owner_credit (buffers : list AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer) : GeneratedDummyCleanupReservation.Counts := fun event =>
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts 1 event + AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.inventory_credit buffers event.
Definition owner_cleanup (buffers : list AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer) : GeneratedDummyCleanupReservation.Counts := fun event =>
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.pending_disposal_counts 1 event + AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.inventory_cleanup buffers event.
Theorem root_and_buffers_have_separate_prepaid_cleanup : forall buffers event,
  Forall AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.buffer_valid buffers -> owner_cleanup buffers event <= owner_credit buffers event.
Proof.
  intros buffers event HF.
  pose proof (AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.inventory_cleanup_is_prepaid buffers event HF) as HB.
  assert (HR : AdmittedKeyHashExecution.AdmittedKeyHashExecution.pending_disposal_counts 1 event <= AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts 1 event).
  { unfold AdmittedKeyHashExecution.AdmittedKeyHashExecution.pending_disposal_counts, AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts. destruct event; cbn; lia. }
  unfold owner_cleanup, owner_credit. lia.
Qed.
Theorem owner_inventory_partition_during_delivery :
  forall (lookup : nat -> list AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer) (discarded retained : list nat) event,
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) (discarded ++ retained) event =
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) discarded event +
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) retained event.
Proof. intros. apply GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts_app. Qed.
Theorem owner_list_cleanup_is_prepaid : forall (lookup : nat -> list AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer) owners event,
  Forall (fun owner => Forall AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.buffer_valid (lookup owner)) owners ->
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_cleanup (lookup owner)) owners event <=
  GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) owners event.
Proof.
  intros lookup owners event HF. induction HF as [|owner rest HV HR IH].
  - reflexivity.
  - change (owner_cleanup (lookup owner) event +
      GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_cleanup (lookup owner)) rest event <=
      owner_credit (lookup owner) event +
      GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) rest event).
    pose proof (root_and_buffers_have_separate_prepaid_cleanup _ event HV). lia.
Qed.
Theorem pending_shells_and_owners_are_both_covered :
  forall pending pushed popped (lookup : nat -> list AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Buffer) event,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.PendingInventory pending pushed popped ->
  Forall (fun owner => Forall AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.buffer_valid (lookup owner)) (owner_refs pending) ->
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.pending_disposal_counts (length pending) event +
    GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_cleanup (lookup owner)) (owner_refs pending) event <=
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts pushed event +
    GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts (fun owner => owner_credit (lookup owner)) (owner_refs pending) event.
Proof.
  intros pending pushed popped lookup event HI HF.
  pose proof (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pending_disposal_is_already_prepaid pending pushed popped event HI).
  pose proof (owner_list_cleanup_is_prepaid lookup (owner_refs pending) event HF). lia.
Qed.
Theorem pushing_resume_transfers_the_inflight_owner_reference : forall pending owner callback,
  owner_refs (pending ++ [Resume owner callback]) = owner_refs pending ++ [owner].
Proof. intros. rewrite owner_references_partition_at_a_stack_split. reflexivity. Qed.

Section ConsumingOwner.
Context {Core : Type}.
Theorem resumed_owner_slot_cannot_be_reused :
  forall index tag (slots : @IndexedCopySlots.IndexedCopySlots.Slots (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Owner Core)) owner emptied,
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner index tag slots = Some (owner, emptied) ->
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner index tag emptied = None.
Proof. apply AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.owner_handle_is_taken_once. Qed.
Theorem failed_or_done_resume_has_no_owner_to_push :
  forall exit index tag (slots : @IndexedCopySlots.IndexedCopySlots.Slots (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.Owner Core)) owner emptied next_owner,
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner index tag slots = Some (owner, emptied) -> exit <> AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.AwaitComparison ->
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.finish_owner_transfer exit index tag next_owner emptied = Some emptied /\
  AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner index tag emptied = None.
Proof. apply AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.terminal_resume_returns_no_owner_handle. Qed.
End ConsumingOwner.

(** Original call labels; category/role decoding remains an emitter obligation. *)
Inductive Role := Primary | Secondary.
Inductive Observation := Native (call : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.NativeCall)
| ResumeEntered (owner : nat) (input : option comparison)
| RequestedChild (owner : nat) (role : Role) (position : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position)
| CoreCompleted (owner : nat) (ordering : comparison).
Definition Event := @AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.Event Observation.
Definition silent group : Event :=
  {| AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.event_receipt := group_counts group; AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.event_call := None;
     AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.event_supported := true |}.
Definition schedule_start (_owner _callback : nat) := silent (Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskPush).
Definition discard_start (_owner _callback : nat) := silent (Existing AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.TaskDispatch).
Theorem scheduling_then_discarding_start_never_resumes : forall owner callback,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.ordinary_calls [schedule_start owner callback; discard_start owner callback] = [].
Proof. reflexivity. Qed.
Theorem routing_events_do_not_invent_native_calls : forall groups,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.ordinary_calls (map silent groups) = [].
Proof.
  induction groups as [|group rest IH]; [reflexivity|].
  change (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.ordinary_calls (map silent rest) = []). exact IH.
Qed.
Theorem successful_scheduling_preserves_original_call_order :
  forall (events : list Event) available,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.succeeded (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events events available) = true ->
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.observed_calls (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events events available) = AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.ordinary_calls events.
Proof. apply AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admission_success_erases_to_same_native_calls. Qed.
Theorem refused_scheduling_observes_only_an_original_prefix :
  forall (events : list Event) available,
  exists suffix, AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.ordinary_calls events =
    AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.observed_calls (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events events available) ++ suffix.
Proof. apply AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.every_result_is_an_original_call_prefix. Qed.

(** The no-continuation witness is a proof object, not an extra runtime scan.
    A known ordering alone cannot bypass admission of the final scan. *)
Definition finish_root (discarded : list Task)
    (_ : Forall (fun task => not_resume task = true) discarded)
    (original : comparison) available :=
  if AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.succeeded (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events (map silent (scan_groups discarded false)) available)
  then Some original else None.
Theorem successful_root_publication_follows_the_paid_terminal_scan :
  forall discarded certificate original available published,
  finish_root discarded certificate original available = Some published ->
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.succeeded (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events (map silent (scan_groups discarded false)) available) = true /\
  published = original.
Proof.
  intros discarded certificate original available published HP. unfold finish_root in HP.
  destruct (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.succeeded (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events
    (map silent (scan_groups discarded false)) available)) eqn:HS; [|discriminate].
  inversion HP; subst. split; reflexivity.
Qed.
Theorem refused_terminal_scan_never_publishes_the_known_ordering :
  forall discarded certificate original available,
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.succeeded (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.admitted_events (map silent (scan_groups discarded false)) available) = false ->
  finish_root discarded certificate original available = None.
Proof. intros discarded certificate original available HF. unfold finish_root. now rewrite HF. Qed.

Print Assumptions normal_start_and_resume_inputs.
Print Assumptions resume_then_child_visits_child_first.
Print Assumptions start_to_resume_transfers_the_same_owner.
Print Assumptions owner_references_partition_at_a_stack_split.
Print Assumptions interception_is_at_the_nearest_resume.
Print Assumptions a_nonresume_prefix_reaches_its_continuation.
Print Assumptions an_intercepted_stack_has_no_root_completion_certificate.
Print Assumptions callback_result_routes_are_the_original_branches.
Print Assumptions group_projection_reuses_existing_reservation_parts.
Print Assumptions delivery_scan_has_only_reached_pop_sites.
Print Assumptions await_pays_two_distinct_shells.
Print Assumptions equality_auxiliary_groups_bracket_the_original_driver.
Print Assumptions root_and_buffers_have_separate_prepaid_cleanup.
Print Assumptions owner_inventory_partition_during_delivery.
Print Assumptions owner_list_cleanup_is_prepaid.
Print Assumptions pending_shells_and_owners_are_both_covered.
Print Assumptions pushing_resume_transfers_the_inflight_owner_reference.
Print Assumptions resumed_owner_slot_cannot_be_reused.
Print Assumptions failed_or_done_resume_has_no_owner_to_push.
Print Assumptions scheduling_then_discarding_start_never_resumes.
Print Assumptions routing_events_do_not_invent_native_calls.
Print Assumptions successful_scheduling_preserves_original_call_order.
Print Assumptions refused_scheduling_observes_only_an_original_prefix.
Print Assumptions successful_root_publication_follows_the_paid_terminal_scan.
Print Assumptions refused_terminal_scan_never_publishes_the_known_ordering.
End AdmittedGeneratedCollectionScheduling.
