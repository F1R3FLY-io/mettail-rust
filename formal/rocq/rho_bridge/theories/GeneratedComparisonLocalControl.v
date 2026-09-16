(** Local generated Eq/Ord control, excluding collection continuations.

    Source: iterative_cmp.rs generate_eq_engine, generate_cmp_engine,
    cmp_deliver and generate_category_trait_impls. A record retains the
    original popped task and its actual construction-order push batch.
    Handler relations project source outcomes; they provide NO count bound.
    Equality and ordering have distinct relations. A deferred Verdict stores
    its original comparison: consulting it neither reruns that comparison
    nor invents an Equal result. Native and handler-body work is separate.

    Prefixes include refusal during a handler after some pushes. Refusal
    before the next pop is also allowed. A decisive Eq exits immediately;
    a decisive Ord discards the remaining local tasks through cmp_deliver.
    There is no ResumeCollection in this slice, hence at most one delivery.
    Pending failure/Eq disposal uses the existing push cleanup credit.

    Exact source groups reuse AdmittedGeneratedComparisonScheduling:
    successful pop plus dispatch costs two work; each later push costs two
    work and one record. Exhaustion pays one terminal pop. Ord delivery
    pays two work per remaining task plus begin and terminal pop. These
    are logical groups, not allocator/TLS implementation or CPU costs.

    Both comparison wrappers have the same finite take/test/root-push/
    invoke/clear/set/fallback layout as the existing generic wrapper word.
    The clear group pays the vector-header operation; residual task disposal
    is covered separately by push credit, not by assuming the Eq stack empty.
    The first-use wrapper is 15 work and THREE records including the root
    push. Adding P later pushes and the driver gives at most 19+4P work,
    3+P records. With N=1+P this is 15+4N work, 2+N records: the apparent
    two-record constant has not removed TLS initialization or the root.

    An inspector must establish its emitted-occurrence cover before using
    the monotonicity theorem. This file does not assert that correspondence,
    certify native/body costs, or create a comparator or production trace.
    Ordinary native callbacks must complete normally. Refused represents
    checked admission/metadata failure, not panic unwinding of a native
    callback; unwinding and restoring a taken pool remain outside this model.
    In particular a metadata handler's unit return is only local completion,
    never evidence for the semantic Continue outcome below. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import AdmittedGeneratedComparisonScheduling
  AdmittedGeneratedHashScheduling AdmittedKeyHashExecution
  GeneratedDummyCleanupReservation.
Import ListNotations.

Module GeneratedComparisonLocalControl.
Module C := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.
Module W := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module D := GeneratedDummyCleanupReservation.

Inductive Mode := Equality | Ordering.
Inductive Outcome := Continue | Decisive | Refused.
Inductive Ending := Exhausted | Stopped | Rejected.

Section OriginalTasks.
Context {Pair : Type}.
Inductive Task := Child (operands : Pair) | Verdict (original : comparison).
Variable eq_handler ord_handler : Pair -> list Task -> Outcome -> Prop.

Inductive SourceStep : Mode -> Task -> list Task -> Outcome -> Prop :=
| EqChild : forall pair batch result,
    eq_handler pair batch result -> SourceStep Equality (Child pair) batch result
| OrdChild : forall pair batch result,
    ord_handler pair batch result -> SourceStep Ordering (Child pair) batch result
| ConsultEqual : forall mode, SourceStep mode (Verdict Eq) [] Continue
| ConsultLess : forall mode, SourceStep mode (Verdict Lt) [] Decisive
| ConsultGreater : forall mode, SourceStep mode (Verdict Gt) [] Decisive.

Definition Record := (Task * list Task)%type.
Inductive Run (mode : Mode) : list Task -> list Record -> list Task -> Ending -> Prop :=
| RunEmpty : Run mode [] [] [] Exhausted
| RunRefused : forall pending, Run mode pending [] pending Rejected
| RunContinue : forall pending task batch records residual ending,
    SourceStep mode task batch Continue ->
    Run mode (pending ++ batch) records residual ending ->
    Run mode (pending ++ [task]) ((task, batch) :: records) residual ending
| RunDecisive : forall pending task batch,
    SourceStep mode task batch Decisive ->
    Run mode (pending ++ [task]) [(task, batch)] (pending ++ batch) Stopped
| RunHandlerRefused : forall pending task batch,
    SourceStep mode task batch Refused ->
    Run mode (pending ++ [task]) [(task, batch)] (pending ++ batch) Rejected.

Definition later_pushes (records : list Record) :=
  fold_right (fun record total => length (snd record) + total) 0 records.
Definition sum_tasks (weight : Task -> nat) tasks :=
  fold_right (fun task total => weight task + total) 0 tasks.
Definition spawned_sum weight (records : list Record) :=
  fold_right (fun record total => sum_tasks weight (snd record) + total) 0 records.

Lemma sum_tasks_app : forall weight first second,
  sum_tasks weight (first ++ second) = sum_tasks weight first + sum_tasks weight second.
Proof.
  intros weight first. induction first; intro second; [reflexivity|].
  change (weight a + sum_tasks weight (first ++ second) =
    (weight a + sum_tasks weight first) + sum_tasks weight second).
  rewrite IHfirst. lia.
Qed.

(** Any occurrence-sensitive projection is conserved. Aliases are NOT
    deduplicated, and the retained Pair can carry category and both operands. *)
Theorem source_run_preserves_occurrence_inventory :
  forall mode initial records residual ending,
  Run mode initial records residual ending -> forall weight,
  sum_tasks weight initial + spawned_sum weight records =
    sum_tasks weight (map fst records) + sum_tasks weight residual.
Proof.
  intros mode initial records residual ending RUN. induction RUN; intro weight.
  - reflexivity.
  - cbn [spawned_sum sum_tasks map fold_right]. lia.
  - specialize (IHRUN weight).
    change (sum_tasks weight (pending ++ [task]) +
      (sum_tasks weight batch + spawned_sum weight records) =
      (weight task + sum_tasks weight (map fst records)) + sum_tasks weight residual).
    rewrite sum_tasks_app in IHRUN |- *.
    change (sum_tasks weight pending + (weight task + 0) +
      (sum_tasks weight batch + spawned_sum weight records) =
      (weight task + sum_tasks weight (map fst records)) + sum_tasks weight residual).
    lia.
  - change (sum_tasks weight (pending ++ [task]) + (sum_tasks weight batch + 0) =
      (weight task + 0) + sum_tasks weight (pending ++ batch)).
    rewrite !sum_tasks_app. change
      (sum_tasks weight pending + (weight task + 0) + (sum_tasks weight batch + 0) =
        (weight task + 0) + (sum_tasks weight pending + sum_tasks weight batch)). lia.
  - change (sum_tasks weight (pending ++ [task]) + (sum_tasks weight batch + 0) =
      (weight task + 0) + sum_tasks weight (pending ++ batch)).
    rewrite !sum_tasks_app. change
      (sum_tasks weight pending + (weight task + 0) + (sum_tasks weight batch + 0) =
        (weight task + 0) + (sum_tasks weight pending + sum_tasks weight batch)). lia.
Qed.

Theorem source_run_balance : forall mode initial records residual ending,
  Run mode initial records residual ending ->
  length initial + later_pushes records = length records + length residual.
Proof.
  intros mode initial records residual ending RUN. induction RUN.
  - reflexivity.
  - change (length pending + 0 = 0 + length pending). lia.
  - change (length (pending ++ [task]) + (length batch + later_pushes records) =
      S (length records) + length residual).
    rewrite length_app in IHRUN |- *. cbn [length]. lia.
  - change (length (pending ++ [task]) + (length batch + 0) =
      1 + length (pending ++ batch)). rewrite !length_app. cbn [length]. lia.
  - change (length (pending ++ [task]) + (length batch + 0) =
      1 + length (pending ++ batch)). rewrite !length_app. cbn [length]. lia.
Qed.

Theorem exhaustion_has_no_residual : forall mode initial records residual,
  Run mode initial records residual Exhausted -> residual = [].
Proof. intros mode initial records residual RUN. remember Exhausted as ending.
  induction RUN; try discriminate; auto. Qed.

Theorem source_run_reuses_pending_cleanup_inventory :
  forall mode initial records residual ending,
  Run mode initial records residual ending -> forall pushed popped,
  @W.PendingInventory Task initial pushed popped ->
  @W.PendingInventory Task residual (pushed + later_pushes records)
    (popped + length records).
Proof.
  intros mode initial records residual ending RUN. induction RUN; intros pushed popped INV.
  - cbn [later_pushes fold_right length]. now rewrite !Nat.add_0_r.
  - cbn [later_pushes fold_right length]. now rewrite !Nat.add_0_r.
  - pose proof (@W.PoppedTask Task pending task pushed popped INV) as POP.
    pose proof (@W.PushedBatch Task pending pushed (S popped) batch POP) as PUSH.
    specialize (IHRUN _ _ PUSH).
    change (@W.PendingInventory Task residual
      (pushed + (length batch + later_pushes records))
      (popped + S (length records))).
    replace (pushed + (length batch + later_pushes records)) with
      (pushed + length batch + later_pushes records) by lia.
    replace (popped + S (length records)) with (S popped + length records) by lia.
    exact IHRUN.
  - cbn [later_pushes fold_right snd length]. rewrite Nat.add_0_r.
    replace (popped + 1) with (S popped) by lia.
    apply W.PushedBatch. exact (@W.PoppedTask Task pending task pushed popped INV).
  - cbn [later_pushes fold_right snd length]. rewrite Nat.add_0_r.
    replace (popped + 1) with (S popped) by lia.
    apply W.PushedBatch. exact (@W.PoppedTask Task pending task pushed popped INV).
Qed.

Definition control_task task := match task with
  | Child _ => C.CategoryPair []
  | Verdict original => C.PrecomputedVerdict [] original end.
Definition delivery_work residual := C.trace_work
  (C.delivery_events (map control_task residual)).
Lemma source_delivery_counts : forall residual,
  delivery_work residual = 2 * length residual + 2.
Proof.
  intro residual. unfold delivery_work.
  rewrite (proj1 (C.delivery_pays_begin_and_terminal_pop _)), length_map.
  reflexivity.
Qed.

Definition terminal_work mode ending residual := match ending, mode with
  | Exhausted, _ => C.group_work C.AttemptPop
  | Stopped, Ordering => delivery_work residual
  | _, _ => 0 end.
Definition step_groups (record : Record) :=
  [C.AttemptPop; C.TaskDispatch] ++ repeat C.TaskPush (length (snd record)).
Definition groups_work groups := fold_right
  (fun group total => C.group_work group + total) 0 groups.
Definition records_work records := fold_right
  (fun record total => groups_work (step_groups record) + total) 0 records.

Lemma repeat_push_work : forall n,
  groups_work (repeat C.TaskPush n) = 2 * n.
Proof. induction n; [reflexivity|].
  change (2 + groups_work (repeat C.TaskPush n) = 2 * S n).
  rewrite IHn. lia. Qed.
Lemma record_work_exact : forall record,
  groups_work (step_groups record) = 2 + 2 * length (snd record).
Proof. intros [task batch]. change
  (2 + groups_work (repeat C.TaskPush (length batch)) = 2 + 2 * length batch).
  now rewrite repeat_push_work. Qed.
Theorem records_work_exact : forall records,
  records_work records = 2 * length records + 2 * later_pushes records.
Proof.
  induction records as [|record records IH]; [reflexivity|].
  change (groups_work (step_groups record) + records_work records =
    2 * S (length records) + 2 * (length (snd record) + later_pushes records)).
  rewrite record_work_exact, IH. lia.
Qed.

Theorem root_local_control_envelope : forall mode root records residual ending,
  Run mode [root] records residual ending ->
  records_work records + terminal_work mode ending residual <=
    4 + 4 * later_pushes records.
Proof.
  intros mode root records residual ending RUN.
  pose proof (source_run_balance _ _ _ _ _ RUN) as BALANCE.
  cbn [length] in BALANCE. rewrite records_work_exact.
  destruct ending, mode; cbn [terminal_work C.group_work];
    try rewrite source_delivery_counts; lia.
Qed.

(** Wrapper-word reuse, not a claim that Eq is a NormalHashDriver: Eq may
    leave tasks to clear. Both wrappers take an initially empty private pool;
    nested calls return an empty cell, and push credit pays pending disposal. *)
Definition first_wrapper_counts := W.hash_wrapper_counts
  (W.first_pooled_prefix ++ W.pooled_suffix true).
Theorem first_wrapper_includes_three_records_and_the_root_push : forall event,
  first_wrapper_counts event =
    15 * D.atom D.NativeWork event + 3 * D.atom D.NativeRecord event.
Proof. apply W.first_use_pooled_wrapper_local_counts_are_exact. Qed.

Definition control_envelope inspected_later event :=
  (19 + 4 * inspected_later) * D.atom D.NativeWork event +
  (3 + inspected_later) * D.atom D.NativeRecord event.
Definition actual_control mode records residual ending event :=
  first_wrapper_counts event +
  (records_work records + terminal_work mode ending residual) * D.atom D.NativeWork event +
  later_pushes records * D.atom D.NativeRecord event.

Theorem inspected_push_cover_suffices_for_local_control :
  forall mode root records residual ending inspected_later,
  Run mode [root] records residual ending ->
  later_pushes records <= inspected_later -> forall event,
  actual_control mode records residual ending event <= control_envelope inspected_later event.
Proof.
  intros mode root records residual ending inspected_later RUN COVER event.
  pose proof (root_local_control_envelope _ _ _ _ _ RUN) as BOUND.
  unfold actual_control, control_envelope.
  rewrite first_wrapper_includes_three_records_and_the_root_push. nia.
Qed.

Theorem root_reindexing_does_not_drop_a_wrapper_record : forall later event,
  control_envelope later event =
    (15 + 4 * S later) * D.atom D.NativeWork event +
    (2 + S later) * D.atom D.NativeRecord event.
Proof. intros. unfold control_envelope. nia. Qed.

(** Continuing requires an original source outcome, not an inspector's unit
    return. The rest of the worklist still determines the eventual ending. *)
Theorem source_continuation_keeps_remaining_jobs :
  forall mode pending task batch records residual ending,
  SourceStep mode task batch Continue ->
  Run mode (pending ++ batch) records residual ending ->
  Run mode (pending ++ [task]) ((task, batch) :: records) residual ending.
Proof. intros. now apply RunContinue. Qed.

End OriginalTasks.

Print Assumptions source_run_preserves_occurrence_inventory.
Print Assumptions source_run_balance.
Print Assumptions exhaustion_has_no_residual.
Print Assumptions source_run_reuses_pending_cleanup_inventory.
Print Assumptions source_delivery_counts.
Print Assumptions records_work_exact.
Print Assumptions root_local_control_envelope.
Print Assumptions first_wrapper_includes_three_records_and_the_root_push.
Print Assumptions inspected_push_cover_suffices_for_local_control.
Print Assumptions root_reindexing_does_not_drop_a_wrapper_record.
End GeneratedComparisonLocalControl.
