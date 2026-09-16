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

(** Ordinary Hash wrapper, iterative_hash.rs1327-1357. These labels name
    bounded logical source groups; they do not measure TLS implementation,
    allocator internals, physical relocation, or arbitrary Hasher callbacks.
    Cell::take constructs an empty header and exchanges it with the pool.
    Cell::set exchanges headers and drops the replaced vector. Nested calls
    can leave an allocated EMPTY vector there, so its release is explicit.

    The driver relation below projects successful scheduling only: batches
    are the tasks the actual handler emitted, and nested calls occur while
    that handler owns its outer stack. It proves neither handler semantics
    nor termination. Driver/native-action receipts remain separate. *)
Inductive HashWrapperGroup :=
| HashWrapperEntry | TryHashPool | InitializeHashPool | EmptyReplacementHeader | TakeHashPool
| TestHashPoolEmpty | PushHashRoot | InvokeHashDriver | TestHashClear
| ClearEmptyHashStack | ReplaceHashPool | ReleaseReplacedHashHeader
| TestHashTlsResult | ReturnHashWrapper | LocalHashHeader | ReleaseLocalHashHeader.

Definition pooled_prefix :=
  [HashWrapperEntry; TryHashPool; EmptyReplacementHeader; TakeHashPool;
   TestHashPoolEmpty; PushHashRoot; InvokeHashDriver].
(** The thread_local initializer at line359 executes, when needed, during
    try_with and before its closure. This one bounded source group constructs
    Cell::new(Vec::new()); TLS implementation machinery remains excluded. *)
Definition first_pooled_prefix :=
  [HashWrapperEntry; TryHashPool; InitializeHashPool; EmptyReplacementHeader;
   TakeHashPool; TestHashPoolEmpty; PushHashRoot; InvokeHashDriver].
Definition pooled_suffix (was_empty : bool) :=
  [TestHashClear] ++ (if was_empty then [ClearEmptyHashStack] else []) ++
  [ReplaceHashPool; ReleaseReplacedHashHeader; TestHashTlsResult; ReturnHashWrapper].
Definition local_prefix :=
  [HashWrapperEntry; TryHashPool; TestHashTlsResult;
   LocalHashHeader; PushHashRoot; InvokeHashDriver].
Definition local_suffix := [ReleaseLocalHashHeader; ReturnHashWrapper].

Definition hash_wrapper_group_counts group : D.Counts :=
  match group with
  | PushHashRoot => H.push_range_counts 1
  | EmptyReplacementHeader | LocalHashHeader | InitializeHashPool =>
      fun event => D.atom D.NativeWork event + D.atom D.NativeRecord event
  | _ => D.atom D.NativeWork
  end.
Definition hash_wrapper_counts groups : D.Counts := fun event =>
  fold_right (fun group total => hash_wrapper_group_counts group event + total) 0 groups.

Section OrdinaryWrapperLifecycle.
Context {Task : Type}.
Definition private_pool_empty (pool : option (list Task)) :=
  match pool with None => True | Some pending => pending = [] end.
Definition stack_is_empty (stack : list Task) :=
  match stack with [] => true | _ :: _ => false end.

(** None denotes an unavailable TLS key, not an occupied cell. A taken
    available cell contains Some[], including throughout a nested call.
    NormalDriver's terminal constructor corresponds to the failed final
    stack.pop(); hence the caller's owned vector is empty at return.
    In particular no premise simply asserts that a successful driver drained
    an arbitrary vector. Every finite scheduling derivation ends at[]. *)
Inductive NormalHashCall : option (list Task) -> Task ->
    option (list Task) -> list HashWrapperGroup -> Prop :=
| NormalPooledHash : forall pool root returned nested,
    NormalHashDriver (pool ++ [root]) (Some []) (Some returned) nested ->
    NormalHashCall (Some pool) root (Some [])
      (pooled_prefix ++ nested ++ pooled_suffix (stack_is_empty pool))
| NormalLocalHash : forall root nested,
    NormalHashDriver [root] None None nested ->
    NormalHashCall None root None (local_prefix ++ nested ++ local_suffix)
with NormalHashDriver : list Task -> option (list Task) ->
    option (list Task) -> list HashWrapperGroup -> Prop :=
| NormalHashDriverEmpty : forall pool,
    NormalHashDriver [] pool pool []
| NormalHashDriverTask : forall pending task batch pool middle final during rest,
    NormalNestedHashCalls pool middle during ->
    NormalHashDriver (pending ++ batch) middle final rest ->
    NormalHashDriver (pending ++ [task]) pool final (during ++ rest)
with NormalNestedHashCalls : option (list Task) -> option (list Task) ->
    list HashWrapperGroup -> Prop :=
| NormalNestedHashNil : forall pool,
    NormalNestedHashCalls pool pool []
| NormalNestedHashCons : forall pool middle final root first rest,
    NormalHashCall pool root middle first ->
    NormalNestedHashCalls middle final rest ->
    NormalNestedHashCalls pool final (first ++ rest).

Theorem every_completed_hash_returns_an_empty_private_pool :
  forall pool root final groups,
  NormalHashCall pool root final groups -> private_pool_empty final.
Proof. intros pool root final groups CALL. destruct CALL; [reflexivity|exact I]. Qed.

Theorem completed_nested_hashes_preserve_the_empty_pool : forall pool final groups,
  NormalNestedHashCalls pool final groups ->
  private_pool_empty pool -> private_pool_empty final.
Proof.
  intros pool final groups CALLS. induction CALLS; intro EMPTY; [exact EMPTY|].
  apply IHCALLS. eapply every_completed_hash_returns_an_empty_private_pool; eassumption.
Qed.

Theorem successful_driver_preserves_the_empty_private_pool : forall pending pool final groups,
  NormalHashDriver pending pool final groups ->
  private_pool_empty pool -> private_pool_empty final.
Proof.
  intros pending pool final groups DRIVER. induction DRIVER; intro EMPTY; [exact EMPTY|].
  apply IHDRIVER. eapply completed_nested_hashes_preserve_the_empty_pool; eassumption.
Qed.

Theorem initialized_private_hash_pool_is_empty : private_pool_empty (Some []).
Proof. reflexivity. Qed.

Theorem taking_the_private_pool_exposes_an_empty_cell : forall pool,
  private_pool_empty (Some pool) -> pool = [] /\ private_pool_empty (Some []).
Proof. intros pool EMPTY. split; [exact EMPTY|reflexivity]. Qed.

Theorem pooled_completion_releases_only_an_empty_replaced_vector :
  forall pool root returned nested,
  NormalHashDriver (pool ++ [root]) (Some []) (Some returned) nested -> returned = [].
Proof.
  intros pool root returned nested DRIVER.
  exact (successful_driver_preserves_the_empty_private_pool _ _ _ _ DRIVER eq_refl).
Qed.

Theorem empty_pool_selects_the_original_clear_branch : forall pool root final groups,
  private_pool_empty (Some pool) -> NormalHashCall (Some pool) root final groups ->
  exists nested, groups = pooled_prefix ++ nested ++ pooled_suffix true /\ final = Some [].
Proof.
  intros pool root final groups EMPTY CALL. change (pool = []) in EMPTY. subst pool.
  inversion CALL; subst. eexists. split; reflexivity.
Qed.

(** Reuse the shared ownership inventory for the root task. Its later
    disposal is part of push credit, not an uncharged second recursive Drop. *)
Theorem empty_pool_root_push_uses_the_shared_inventory : forall root,
  @PendingInventory Task [root] 1 0.
Proof.
  intro root. change (PendingInventory ([] ++ [root]) (0 + length [root]) 0).
  apply PushedBatch. constructor.
Qed.

Theorem root_pending_disposal_reuses_original_push_credit : forall (root : Task) event,
  H.pending_disposal_counts (length [root]) event <= H.push_range_counts 1 event.
Proof.
  intros root event. eapply pending_disposal_is_already_prepaid.
  apply empty_pool_root_push_uses_the_shared_inventory.
Qed.

Theorem normal_driver_completes_the_shared_pending_inventory :
  forall pending pool final groups,
  NormalHashDriver pending pool final groups ->
  forall pushed popped, PendingInventory pending pushed popped ->
  exists total_pushed total_popped,
    @PendingInventory Task [] total_pushed total_popped /\
    total_pushed = total_popped /\ pushed <= total_pushed /\ popped <= total_popped.
Proof.
  intros pending pool final groups DRIVER. induction DRIVER; intros pushed popped INVENTORY.
  - exists pushed, popped. split; [exact INVENTORY|].
    pose proof (pending_inventory_balance _ _ _ INVENTORY) as BALANCE.
    cbn in BALANCE. repeat split; lia.
  - assert (POPPED : PendingInventory pending pushed (S popped))
      by (eapply PoppedTask; exact INVENTORY).
    assert (PUSHED : PendingInventory (pending ++ batch) (pushed + length batch) (S popped))
      by (apply PushedBatch; exact POPPED).
    destruct (IHDRIVER _ _ PUSHED) as [total_pushed [total_popped [FINAL [EQ [UP DOWN]]]]].
    exists total_pushed, total_popped. split; [exact FINAL|]. repeat split; lia.
Qed.
End OrdinaryWrapperLifecycle.

Theorem ordinary_wrapper_trace_counts_are_additive : forall first second event,
  hash_wrapper_counts (first ++ second) event =
    hash_wrapper_counts first event + hash_wrapper_counts second event.
Proof.
  induction first as [|group rest IH]; intros second event; [reflexivity|].
  unfold hash_wrapper_counts in *. cbn [app fold_right]. rewrite IH. lia.
Qed.

(** These numerals are computed from the named source groups above. The
    root contributes its existing 2 work / 1 record receipt; all remaining
    groups contribute one work event each. Each constructed vector header
    contributes a record as in the checked wrapper's header allowance.
    Driver-body work is excluded. *)
Theorem ordinary_pooled_wrapper_local_counts_are_exact : forall event,
  hash_wrapper_counts (pooled_prefix ++ pooled_suffix true) event =
    14 * D.atom D.NativeWork event + 2 * D.atom D.NativeRecord event.
Proof. intro event. destruct event; reflexivity. Qed.

Theorem ordinary_fallback_wrapper_local_counts_are_exact : forall event,
  hash_wrapper_counts (local_prefix ++ local_suffix) event =
    9 * D.atom D.NativeWork event + 2 * D.atom D.NativeRecord event.
Proof. intro event. destruct event; reflexivity. Qed.

Theorem first_use_pooled_wrapper_local_counts_are_exact : forall event,
  hash_wrapper_counts (first_pooled_prefix ++ pooled_suffix true) event =
    15 * D.atom D.NativeWork event + 3 * D.atom D.NativeRecord event.
Proof. intro event. destruct event; reflexivity. Qed.

Theorem initialized_wrapper_is_covered_by_first_use_allowance : forall event,
  hash_wrapper_counts (pooled_prefix ++ pooled_suffix true) event <=
    hash_wrapper_counts (first_pooled_prefix ++ pooled_suffix true) event.
Proof.
  intro event. rewrite ordinary_pooled_wrapper_local_counts_are_exact,
    first_use_pooled_wrapper_local_counts_are_exact. lia.
Qed.

Theorem nested_wrapper_counts_are_counted_once : forall prefix nested suffix event,
  hash_wrapper_counts (prefix ++ nested ++ suffix) event =
    hash_wrapper_counts (prefix ++ suffix) event + hash_wrapper_counts nested event.
Proof. intros. rewrite !ordinary_wrapper_trace_counts_are_additive. lia. Qed.

Theorem ordinary_fallback_wrapper_is_covered_by_the_pooled_wrapper : forall event,
  hash_wrapper_counts (local_prefix ++ local_suffix) event <=
    hash_wrapper_counts (pooled_prefix ++ pooled_suffix true) event.
Proof.
  intro event. rewrite ordinary_pooled_wrapper_local_counts_are_exact,
    ordinary_fallback_wrapper_local_counts_are_exact. lia.
Qed.

Theorem original_pooled_call_has_a_source_wrapper_cover :
  forall Task pool root returned nested,
  @NormalHashDriver Task (pool ++ [root]) (Some []) (Some returned) nested ->
  private_pool_empty (Some pool) -> forall event,
    hash_wrapper_counts
      (pooled_prefix ++ nested ++ pooled_suffix (stack_is_empty pool)) event <=
      hash_wrapper_counts (first_pooled_prefix ++ pooled_suffix true) event +
      hash_wrapper_counts nested event.
Proof.
  intros Task pool root returned nested DRIVER EMPTY event.
  change (pool = []) in EMPTY. subst pool.
  cbn [stack_is_empty]. rewrite nested_wrapper_counts_are_counted_once.
  pose proof (initialized_wrapper_is_covered_by_first_use_allowance event). lia.
Qed.

Theorem original_local_call_has_a_source_wrapper_cover :
  forall Task root nested,
  @NormalHashDriver Task [root] None None nested -> forall event,
    hash_wrapper_counts (local_prefix ++ nested ++ local_suffix) event <=
      hash_wrapper_counts (first_pooled_prefix ++ pooled_suffix true) event +
      hash_wrapper_counts nested event.
Proof.
  intros Task root nested DRIVER event. rewrite nested_wrapper_counts_are_counted_once.
  pose proof (ordinary_fallback_wrapper_is_covered_by_the_pooled_wrapper event).
  pose proof (initialized_wrapper_is_covered_by_first_use_allowance event). lia.
Qed.

(** A supplied driver receipt covers its own scheduling/native work, excluding
    nested wrapper groups already in this observed trace. This composition is
    componentwise; it invents no constant bound for Map sorting or Hashers. *)
Theorem wrapper_composes_with_a_separately_verified_driver_bound :
  forall groups (driver_actual driver_bound : D.Counts),
  (forall event, driver_actual event <= driver_bound event) ->
  forall event, hash_wrapper_counts groups event + driver_actual event <=
    hash_wrapper_counts groups event + driver_bound event.
Proof. intros groups actual bound COVER event. specialize (COVER event). lia. Qed.

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
Print Assumptions every_completed_hash_returns_an_empty_private_pool.
Print Assumptions completed_nested_hashes_preserve_the_empty_pool.
Print Assumptions successful_driver_preserves_the_empty_private_pool.
Print Assumptions initialized_private_hash_pool_is_empty.
Print Assumptions taking_the_private_pool_exposes_an_empty_cell.
Print Assumptions pooled_completion_releases_only_an_empty_replaced_vector.
Print Assumptions empty_pool_selects_the_original_clear_branch.
Print Assumptions empty_pool_root_push_uses_the_shared_inventory.
Print Assumptions root_pending_disposal_reuses_original_push_credit.
Print Assumptions normal_driver_completes_the_shared_pending_inventory.
Print Assumptions ordinary_wrapper_trace_counts_are_additive.
Print Assumptions ordinary_pooled_wrapper_local_counts_are_exact.
Print Assumptions ordinary_fallback_wrapper_local_counts_are_exact.
Print Assumptions first_use_pooled_wrapper_local_counts_are_exact.
Print Assumptions initialized_wrapper_is_covered_by_first_use_allowance.
Print Assumptions nested_wrapper_counts_are_counted_once.
Print Assumptions ordinary_fallback_wrapper_is_covered_by_the_pooled_wrapper.
Print Assumptions original_pooled_call_has_a_source_wrapper_cover.
Print Assumptions original_local_call_has_a_source_wrapper_cover.
Print Assumptions wrapper_composes_with_a_separately_verified_driver_bound.
Print Assumptions raw_push_reservation_uses_four_units_per_record.
Print Assumptions cached_bag_six_scalar_native_groups.
Print Assumptions successful_terminal_pop_still_consumes_work.
Print Assumptions admission_success_erases_to_same_native_calls.
Print Assumptions every_result_is_an_original_call_prefix.
Print Assumptions admitted_success_preserves_original_hasher.
Print Assumptions unsupported_event_refuses_without_its_native_call.
Print Assumptions scheduling_opaque_does_not_hash.
End AdmittedGeneratedHashScheduling.
