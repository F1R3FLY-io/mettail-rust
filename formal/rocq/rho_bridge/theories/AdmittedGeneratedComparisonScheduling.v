(** Shared generated comparison scheduling and admission.

    Source: macros/src/gen/term_ops/iterative_cmp.rs eq_iterative/eq_arm_stmts,
    cmp_deliver, cmp_arm_stmts and scope pattern builders. The ordinary builders
    remain the semantic recipe. Eq evaluates native Ne in forward arm order
    while pushing category tasks forward: later LIFO visitation is reverse.
    Cmp evaluates an eager prefix forward, but computes suffix native comparisons
    during REVERSE task construction, including the scope pattern first.
    Verdict tasks store already computed results; consulting a Verdict does NOT
    compare again. This differs from deferred Opaque Hash execution.

    Observations retain operation kind, source position and original result.
    They are proof traces, not allocated runtime plans or a new comparator.
    Admission erases to the SAME finite source trace, already shortened by
    ordinary semantic early exits. Native Eq, Ne, Cmp and generated verdicts
    are not identified; no Eq/Cmp coherence or hash injectivity is presumed.
    Native leaf receipts retain their source/profile and arithmetic contracts.

    Logical source table: root Vec header/cleanup and each task push reserve
    2 NativeWork +1 NativeRecord (FOUR raw units). Attempted pop, including nil,
    costs1; successful dispatch costs1. Each operand's shallow support/tag
    projection costs1 BEFORE dereference; Eq pointer check1; both variant-index
    projections2; original usize != gate2, and unequal index cmp2. Variant
    matching and each field/scope/optional routing group1. Vec setup1 precedes
    construction; every paired next, including terminal, costs1. Original
    length !=/cmp independently costs2. Native leaves retain metadata/execution
    charges; field routing covers the outer result branch, not a second call.
    These are bounded logical source groups, not CPU or allocator internals.

    First checked inventory contains ONLY borrowed category pairs and copied
    Ordering verdicts, never owned collection continuation machines. Eq early
    return may dispose pending tasks using prepaid cleanup credit. Cmp delivery
    follows the ordinary drain: begin1, every attempted pop1, every Some discard
    route1, then terminal paid pop. Known ordering is published only AFTER the
    whole drain succeeds. Refusal returns failure; residual disposal uses prepaid
    credit, not an unpaid semantic pop. Root cleanup is separately paid.

    Unsupported collection branches refuse BEFORE pointer/index shortcuts,
    after paid shallow projection. No fallback, recursive collection entry or
    whole-profile certificate is inferred. Shared-builder/source correspondence,
    pointer validity, actual routing bounds and native receipts remain explicit
    Rust obligations. This is not an all-grammar proof. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedGeneratedHashScheduling AdmittedKeyHashExecution
  AdmittedStructuralKeyHash GeneratedDummyCleanupReservation RholangInitialGraphResources.
Import ListNotations.

Module AdmittedGeneratedComparisonScheduling.
Module G := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module D := GeneratedDummyCleanupReservation.

Definition Position := list nat.
Inductive NativeCall :=
| NativeEq (position : Position) (result : bool)
| NativeNe (position : Position) (result : bool)
| NativeCmp (position : Position) (result : comparison).
Inductive Verdict := EqualityVerdict (result : bool) | OrderingVerdict (result : comparison).
Inductive BorrowedTask :=
| CategoryPair (position : Position)
| PrecomputedVerdict (position : Position) (result : comparison).
Inductive ConstructionAction :=
| CallNative (call : NativeCall)
| PushTask (task : BorrowedTask)
| ConsultTask (task : BorrowedTask).
Definition action_calls action := match action with CallNative call => [call] | _ => [] end.
Definition action_pushes action := match action with PushTask task => [task] | _ => [] end.
Definition construction_calls actions := concat (map action_calls actions).
Definition construction_pushes actions := concat (map action_pushes actions).

Theorem consulting_precomputed_verdict_does_not_compare : forall position result,
  action_calls (ConsultTask (PrecomputedVerdict position result)) = [].
Proof. reflexivity. Qed.
Theorem source_action_concatenation_preserves_call_order : forall prefix suffix,
  construction_calls (prefix ++ suffix) = construction_calls prefix ++ construction_calls suffix.
Proof. intros. unfold construction_calls. now rewrite map_app, concat_app. Qed.

(** Calls belong to construction actions, not pending-task denotations. *)
Definition cmp_construction (eager : list ConstructionAction)
    (suffix : list (list ConstructionAction)) := eager ++ concat (rev suffix).
Theorem cmp_suffix_construction_is_reverse_group_order : forall eager a b,
  construction_calls (cmp_construction eager [a; b]) =
    construction_calls eager ++ construction_calls b ++ construction_calls a.
Proof.
  intros. unfold cmp_construction. cbn [rev concat app].
  rewrite app_nil_r, !source_action_concatenation_preserves_call_order. reflexivity.
Qed.
Theorem reverse_task_groups_still_consult_forward :
  forall (stack : list BorrowedTask) (fields : list (list BorrowedTask)),
  G.pop_order (stack ++ G.deferred_pushes fields) = concat fields ++ G.pop_order stack.
Proof. apply G.reverse_fields_preserve_field_and_element_order. Qed.
Theorem forward_eq_pushes_visit_reverse : forall (stack tasks : list BorrowedTask),
  G.pop_order (stack ++ tasks) = rev tasks ++ G.pop_order stack.
Proof. intros. unfold G.pop_order. apply rev_app_distr. Qed.
Theorem vec_length_verdict_is_consulted_after_elements :
  forall (stack : list BorrowedTask) (length_result : BorrowedTask) (elements : list BorrowedTask),
  G.pop_order (stack ++ [length_result] ++ rev elements) =
    elements ++ length_result :: G.pop_order stack.
Proof.
  intros. unfold G.pop_order. rewrite !rev_app_distr, rev_involutive.
  cbn [rev app]. now rewrite <- app_assoc.
Qed.
Theorem scope_pattern_verdict_precedes_body_after_prefields :
  forall (stack : list BorrowedTask) (prefields : list (list BorrowedTask)) (pattern body : BorrowedTask),
  G.pop_order (stack ++ [body; pattern] ++ G.deferred_pushes prefields) =
    concat prefields ++ pattern :: body :: G.pop_order stack.
Proof. apply G.binder_pattern_precedes_body_after_prefields. Qed.

Definition eq_order_witness :=
  [CallNative (NativeNe [0] false); PushTask (CategoryPair [1]);
   CallNative (NativeNe [2] false); PushTask (CategoryPair [3])].
Definition cmp_order_witness :=
  [CallNative (NativeCmp [0] Eq); PushTask (CategoryPair [3]);
   CallNative (NativeCmp [2] Gt); PushTask (PrecomputedVerdict [2] Gt);
   PushTask (CategoryPair [1])].
Theorem exact_eq_construction_witness :
  construction_calls eq_order_witness = [NativeNe [0] false; NativeNe [2] false] /\
  G.pop_order (construction_pushes eq_order_witness) = [CategoryPair [3]; CategoryPair [1]].
Proof. split; reflexivity. Qed.
Theorem exact_cmp_construction_witness :
  construction_calls cmp_order_witness = [NativeCmp [0] Eq; NativeCmp [2] Gt] /\
  G.pop_order (construction_pushes cmp_order_witness) =
    [CategoryPair [1]; PrecomputedVerdict [2] Gt; CategoryPair [3]].
Proof. split; reflexivity. Qed.

Inductive SourceGroup :=
| RootHeader | TaskPush | AttemptPop | TaskDispatch | ShallowOperand
| EqPointerCheck | IndexProjections | IndexNe | IndexCmp | VariantRoute
| FieldRoute | ScopeRoute | VecSetup | PairNext | LengthNe | LengthCmp
| DeliverBegin | DeliverDiscard.
Definition group_work group := match group with
  | RootHeader | TaskPush | IndexProjections | IndexNe | IndexCmp | LengthNe | LengthCmp => 2
  | _ => 1 end.
Definition group_units group := match group with RootHeader | TaskPush => 4 | _ => 0 end.
Definition group_counts group := match group with
  | RootHeader | TaskPush => H.push_range_counts 1
  | _ => S.work_counts (group_work group)
  end.
Lemma logical_work_only_projection : forall work,
  D.weighted D.logical_work_weight (S.work_counts work) = work /\
  D.weighted D.logical_unit_weight (S.work_counts work) = 0.
Proof.
  intro work. rewrite D.logical_work_projects_bytes_once,
    D.logical_units_project_records_and_bytes.
  destruct (S.work_counts_projection work) as [HW [HR HB]]. rewrite HW, HR, HB. split; lia.
Qed.
Theorem source_group_callback_projection : forall group,
  D.weighted D.logical_work_weight (group_counts group) = group_work group /\
  D.weighted D.logical_unit_weight (group_counts group) = group_units group.
Proof.
  intro group. destruct group; cbn [group_counts group_work group_units];
    try apply logical_work_only_projection;
    apply (G.raw_push_reservation_uses_four_units_per_record 1).
Qed.

Definition Event := @G.Event NativeCall.
Definition silent_group group : Event :=
  {| G.event_receipt := group_counts group; G.event_call := None; G.event_supported := true |}.
Inductive UnsupportedSite := UnorderedBag | UnorderedSet | UnorderedMap | RecursiveNativeCarrier.
Definition unsupported_event (_ : UnsupportedSite) : Event :=
  {| G.event_receipt := S.work_counts 0; G.event_call := None; G.event_supported := false |}.
Theorem local_refusal_precedes_shortcut_and_index_actions : forall site later available,
  G.admitted_events (unsupported_event site :: later) available = G.Stopped available [].
Proof. intros. apply G.unsupported_event_refuses_without_its_native_call. reflexivity. Qed.
Theorem successful_trace_preserves_operation_position_and_result :
  forall (events : list Event) available,
  G.succeeded (G.admitted_events events available) = true ->
  G.observed_calls (G.admitted_events events available) = G.ordinary_calls events.
Proof. apply G.admission_success_erases_to_same_native_calls. Qed.
Theorem refused_trace_is_an_original_native_prefix : forall (events : list Event) available,
  exists suffix, G.ordinary_calls events =
    G.observed_calls (G.admitted_events events available) ++ suffix.
Proof. apply G.every_result_is_an_original_call_prefix. Qed.

(** Gate the original known verdict on the same source trace, not a comparator. *)
Definition publication (events : list Event) (original : Verdict) available :=
  if G.succeeded (G.admitted_events events available) then Some original else None.
Theorem successful_publication_is_original : forall events original available published,
  publication events original available = Some published ->
  G.succeeded (G.admitted_events events available) = true /\ published = original.
Proof.
  intros events original available published HP. unfold publication in HP.
  destruct (G.succeeded (G.admitted_events events available)); [|discriminate].
  inversion HP. split; reflexivity.
Qed.
Theorem refusal_never_publishes_known_verdict : forall events original available,
  G.succeeded (G.admitted_events events available) = false -> publication events original available = None.
Proof. intros events original available HF. unfold publication. now rewrite HF. Qed.

Definition trace_work (events : list Event) := fold_right
  (fun event rest => D.weighted D.logical_work_weight (G.event_receipt event) + rest) 0 events.
Definition trace_units (events : list Event) := fold_right
  (fun event rest => D.weighted D.logical_unit_weight (G.event_receipt event) + rest) 0 events.
Theorem successful_trace_pays_its_existing_receipts : forall events available paid calls,
  G.admitted_events events available = G.Finished paid calls ->
  work_left paid + trace_work events = work_left available /\
  units_left paid + trace_units events = units_left available.
Proof.
  induction events as [|event rest IH]; intros available paid calls HC.
  - cbn [G.admitted_events] in HC. inversion HC; subst.
    cbn [trace_work trace_units fold_right]. split; lia.
  - cbn [G.admitted_events] in HC. destruct (G.event_supported event); [|discriminate].
    destruct (H.paid_counts false available (G.event_receipt event)
      (fun _ => Some (G.event_call event))) as [next|next call] eqn:HP; [discriminate|].
    destruct (G.admitted_events rest next) as [remaining tail|remaining tail] eqn:HT;
      cbn [G.prepend_calls] in HC; [|discriminate].
    pose proof (IH next remaining tail HT) as HH.
    unfold H.paid_counts in HP. apply successful_action_constructs_only_the_paid_result in HP.
    destruct HP as [_ [_ [HW HU]]]. inversion HC; subst.
    change (work_left paid +
      (D.weighted D.logical_work_weight (G.event_receipt event) + trace_work rest) =
      work_left available /\ units_left paid +
      (D.weighted D.logical_unit_weight (G.event_receipt event) + trace_units rest) =
      units_left available).
    change (work_left next + D.weighted D.logical_work_weight (G.event_receipt event) =
      work_left available) in HW.
    change (units_left next + D.weighted D.logical_unit_weight (G.event_receipt event) =
      units_left available) in HU.
    destruct HH as [HHW HHU]. split; lia.
Qed.

Lemma silent_cons_work : forall group events,
  trace_work (silent_group group :: events) = group_work group + trace_work events.
Proof.
  intros. change (D.weighted D.logical_work_weight (group_counts group) + trace_work events =
    group_work group + trace_work events).
  now rewrite (proj1 (source_group_callback_projection group)).
Qed.
Lemma silent_cons_units : forall group events,
  trace_units (silent_group group :: events) = group_units group + trace_units events.
Proof.
  intros. change (D.weighted D.logical_unit_weight (group_counts group) + trace_units events =
    group_units group + trace_units events).
  now rewrite (proj2 (source_group_callback_projection group)).
Qed.
Lemma silent_cons_calls : forall group events,
  G.ordinary_calls (silent_group group :: events) = G.ordinary_calls events.
Proof. reflexivity. Qed.

(** First-slice cmp_deliver trace, already in pop order. Nil still pays a pop. *)
Fixpoint drain_pop_events (tasks : list BorrowedTask) : list Event := match tasks with
  | [] => [silent_group AttemptPop]
  | _ :: rest => silent_group AttemptPop :: silent_group DeliverDiscard :: drain_pop_events rest
  end.
Definition delivery_events pending := silent_group DeliverBegin :: drain_pop_events (G.pop_order pending).
Theorem drain_event_projection : forall tasks,
  trace_work (drain_pop_events tasks) = 2 * length tasks + 1 /\
  trace_units (drain_pop_events tasks) = 0 /\ G.ordinary_calls (drain_pop_events tasks) = [].
Proof.
  intro tasks. induction tasks as [|task rest IH];
    cbn [drain_pop_events length];
    rewrite !silent_cons_work, !silent_cons_units, !silent_cons_calls;
    cbn [group_work group_units]; [repeat split; reflexivity|].
  destruct IH as [HIW [HIU HIC]]. rewrite HIW, HIU, HIC.
  repeat split; try reflexivity; lia.
Qed.
Theorem delivery_pays_begin_and_terminal_pop : forall pending,
  trace_work (delivery_events pending) = 2 * length pending + 2 /\
  trace_units (delivery_events pending) = 0 /\ G.ordinary_calls (delivery_events pending) = [].
Proof.
  intro pending. unfold delivery_events.
  rewrite silent_cons_work, silent_cons_units, silent_cons_calls.
  cbn [group_work group_units].
  destruct (drain_event_projection (G.pop_order pending)) as [HDW [HDU HDC]].
  rewrite HDW, HDU, HDC. unfold G.pop_order. rewrite rev_length.
  repeat split; try reflexivity; lia.
Qed.
Theorem completed_delivery_exact_charge : forall pending available paid calls,
  G.admitted_events (delivery_events pending) available = G.Finished paid calls ->
  work_left paid + (2 * length pending + 2) = work_left available /\
  units_left paid = units_left available /\ calls = [].
Proof.
  intros pending available paid calls HC.
  pose proof (successful_trace_pays_its_existing_receipts _ _ _ _ HC) as HP.
  destruct (delivery_pays_begin_and_terminal_pop pending) as [HW [HU HN]].
  rewrite HW, HU in HP.
  assert (HS : G.succeeded (G.admitted_events (delivery_events pending) available) = true).
  { rewrite HC. reflexivity. }
  apply G.admission_success_erases_to_same_native_calls in HS. rewrite HC, HN in HS.
  cbn [G.observed_calls] in HS. repeat split; lia || assumption.
Qed.
Theorem pending_failure_disposal_is_prepaid : forall pending pushed popped event,
  @G.PendingInventory BorrowedTask pending pushed popped ->
  H.pending_disposal_counts (length pending) event <= H.push_range_counts pushed event.
Proof. apply G.pending_disposal_is_already_prepaid. Qed.
Theorem completed_drain_consumes_the_remaining_occurrences : forall pending pushed popped,
  @G.PendingInventory BorrowedTask pending pushed popped ->
  popped + length (G.pop_order pending) = pushed.
Proof.
  intros pending pushed popped HI. apply G.pending_inventory_balance in HI.
  unfold G.pop_order. rewrite rev_length. lia.
Qed.

Print Assumptions consulting_precomputed_verdict_does_not_compare.
Print Assumptions source_action_concatenation_preserves_call_order.
Print Assumptions cmp_suffix_construction_is_reverse_group_order.
Print Assumptions reverse_task_groups_still_consult_forward.
Print Assumptions forward_eq_pushes_visit_reverse.
Print Assumptions vec_length_verdict_is_consulted_after_elements.
Print Assumptions scope_pattern_verdict_precedes_body_after_prefields.
Print Assumptions exact_eq_construction_witness.
Print Assumptions exact_cmp_construction_witness.
Print Assumptions source_group_callback_projection.
Print Assumptions local_refusal_precedes_shortcut_and_index_actions.
Print Assumptions successful_trace_preserves_operation_position_and_result.
Print Assumptions refused_trace_is_an_original_native_prefix.
Print Assumptions successful_publication_is_original.
Print Assumptions refusal_never_publishes_known_verdict.
Print Assumptions successful_trace_pays_its_existing_receipts.
Print Assumptions drain_event_projection.
Print Assumptions delivery_pays_begin_and_terminal_pop.
Print Assumptions completed_delivery_exact_charge.
Print Assumptions pending_failure_disposal_is_prepaid.
Print Assumptions completed_drain_consumes_the_remaining_occurrences.
End AdmittedGeneratedComparisonScheduling.
