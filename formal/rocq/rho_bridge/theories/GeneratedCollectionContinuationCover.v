(** Finite occurrence accounting for the EXISTING generated Ord scheduler.

    Source: iterative_cmp.rs callback adapters, cmp_driver and cmp_deliver.
    These annotations retain original tasks, owner/callback identities, emitted
    handler batches and comparison answers. They do not evaluate a comparator.
    Handler and callback predicates are the source-observation boundary, not
    numeric-bound oracles. No inspector unit result supplies an Ordering.

    Pending lists use pop order. A source construction-order batch is reversed
    exactly once. Await emits Resume FIRST and its original typed child SECOND.
    Delivery reuses the existing nearest-Resume Interception witness; unstarted
    Starts in its discarded prefix never invoke their callbacks. Only a failed
    pop with no continuation finishes a nonEqual root. A completed ordinary
    driver has exactly one terminal failed pop, while every other delivery
    round consumes an actual Resume occurrence. Eq's outer local driver uses
    GeneratedComparisonLocalControl; each auxiliary driver here is Ord.

    The existing push credit pays eventual shell disposal. Machine roots and
    rosters retain their separate ownership credit through moves or discarded
    Starts. Their cost, native/core work, materialization and handler bodies
    are not included here. A conservative one-work RoleDispatch is added per
    request for the heterogeneous Map callback's key/value branch. This is a
    named logical source group, not an instruction count or stdlib model. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import AdmittedGeneratedCollectionScheduling
  GeneratedCollectionPreparation GeneratedComparisonLocalControl.
Import ListNotations.

Module GeneratedCollectionContinuationCover.
Module S := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.
Local Notation Task := S.Task.
Local Notation BorrowedTask :=
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.BorrowedTask.
Local Notation CategoryPair :=
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair.
Local Notation PrecomputedVerdict :=
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict.

Inductive Configuration := Drive (pending : list Task)
| Deliver (pending : list Task) (original : comparison).
Definition pending configuration := match configuration with
| Drive tasks | Deliver tasks _ => tasks end.
Definition route original tasks := match original with
| Eq => Drive tasks | Lt => Deliver tasks Lt | Gt => Deliver tasks Gt end.
Inductive Reply := Await (role : S.Role) (position : list nat)
| Finished (original : comparison).
Definition reply_tasks owner callback reply := match reply with
| Await _ position => [S.Borrowed (CategoryPair position); S.Resume owner callback]
| Finished _ => [] end.
Definition reply_requests reply := match reply with Await _ _ => 1 | Finished _ => 0 end.
Definition reply_configuration owner callback reply rest := match reply with
| Await _ position => Drive (S.Borrowed (CategoryPair position) :: S.Resume owner callback :: rest)
| Finished original => route original rest end.
Lemma route_keeps_pending : forall original tasks, pending (route original tasks) = tasks.
Proof. intros original tasks. destruct original; reflexivity. Qed.
Lemma reply_keeps_original_suffix : forall owner callback reply rest,
  pending (reply_configuration owner callback reply rest) = reply_tasks owner callback reply ++ rest.
Proof. intros owner callback [role child|original] rest; [reflexivity|].
  apply route_keeps_pending. Qed.

Record Move := { popped : list Task; pushed : list Task;
  callback_count : nat; request_count : nat; round_count : nat }.
Definition borrowed_move task batch :=
  {| popped := [S.Borrowed task]; pushed := rev batch;
     callback_count := 0; request_count := 0; round_count := 0 |}.
Definition callback_move tasks owner callback reply rounds :=
  {| popped := tasks; pushed := reply_tasks owner callback reply;
     callback_count := 1; request_count := reply_requests reply; round_count := rounds |}.

Section SourceObservations.
Variable handler : BorrowedTask -> list Task -> comparison -> Prop.
Variable callback : nat -> nat -> option comparison -> Reply -> Prop.
Inductive HandlerObservation : BorrowedTask -> list Task -> comparison -> Prop :=
| CategoryObservation : forall position batch original,
    handler (CategoryPair position) batch original ->
    HandlerObservation (CategoryPair position) batch original
| ConsultOriginalVerdict : forall position original,
    HandlerObservation (PrecomputedVerdict position original) [] original.
Theorem consulted_verdict_is_the_original_answer : forall position stored batch observed,
  HandlerObservation (PrecomputedVerdict position stored) batch observed ->
  batch = [] /\ observed = stored.
Proof. intros position stored batch observed SOURCE. inversion SOURCE; subst. auto. Qed.
Inductive Step : Configuration -> Configuration -> Move -> Prop :=
| HandlerStep : forall task rest batch original,
    HandlerObservation task batch original ->
    Forall (fun task => S.not_resume task = true) batch ->
    Step (Drive (S.Borrowed task :: rest)) (route original (rev batch ++ rest))
      (borrowed_move task batch)
| StartStep : forall owner cb rest reply,
    callback owner cb None reply ->
    Step (Drive (S.Start owner cb :: rest)) (reply_configuration owner cb reply rest)
      (callback_move [S.Start owner cb] owner cb reply 0)
| ResumeStep : forall owner cb rest reply,
    callback owner cb (Some Eq) reply ->
    Step (Drive (S.Resume owner cb :: rest)) (reply_configuration owner cb reply rest)
      (callback_move [S.Resume owner cb] owner cb reply 0)
| InterceptStep : forall tasks skipped owner cb rest original reply,
    original <> Eq -> S.Interception tasks skipped owner cb rest ->
    callback owner cb (Some original) reply ->
    Step (Deliver tasks original) (reply_configuration owner cb reply rest)
      (callback_move (skipped ++ [S.Resume owner cb]) owner cb reply 1).

Inductive Terminal : Configuration -> list Task -> nat -> Prop :=
| EmptyDriver : Terminal (Drive []) [] 0
| RootDelivery : forall tasks original,
    original <> Eq -> Forall (fun task => S.not_resume task = true) tasks ->
    Terminal (Deliver tasks original) tasks 1.
Inductive Run : Configuration -> list Move -> list Task -> nat -> Prop :=
| RunTerminal : forall configuration last rounds,
    Terminal configuration last rounds -> Run configuration [] last rounds
| RunStep : forall before after movement movements last rounds,
    Step before after movement -> Run after movements last rounds ->
    Run before (movement :: movements) last rounds.

Theorem each_step_retains_actual_occurrences : forall before after movement,
  Step before after movement -> exists rest,
  pending before = popped movement ++ rest /\ pending after = pushed movement ++ rest.
Proof.
  intros before after movement STEP. destruct STEP.
  - exists rest. split; [reflexivity|apply route_keeps_pending].
  - exists rest. split; [reflexivity|apply reply_keeps_original_suffix].
  - exists rest. split; [reflexivity|apply reply_keeps_original_suffix].
  - exists rest. split.
    + destruct (S.interception_is_at_the_nearest_resume _ _ _ _ _ H0) as [SPLIT _].
      cbn [pending popped callback_move]. rewrite SPLIT, <- app_assoc. reflexivity.
    + apply reply_keeps_original_suffix.
Qed.

Local Notation Inventory :=
  AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.PendingInventory.
Lemma popping_original_prefix_transports_inventory : forall (removed rest : list Task) pushed_count popped_count,
  Inventory (rev (removed ++ rest)) pushed_count popped_count ->
  Inventory (rev rest) pushed_count (popped_count + length removed).
Proof.
  induction removed as [|task removed IH]; intros rest pushed_count popped_count INV.
  - cbn [app length] in *. now rewrite Nat.add_0_r.
  - change (Inventory (rev (removed ++ rest) ++ [task]) pushed_count popped_count) in INV.
    pose proof (@AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.PoppedTask
      Task (rev (removed ++ rest)) task pushed_count popped_count INV) as POP.
    specialize (IH rest pushed_count (S popped_count) POP).
    replace (popped_count + length (task :: removed)) with
      (S popped_count + length removed) by (cbn [length]; lia). exact IH.
Qed.
Theorem each_source_step_transports_existing_inventory :
  forall before after movement pushed_count popped_count,
  Step before after movement ->
  Inventory (rev (pending before)) pushed_count popped_count ->
  Inventory (rev (pending after)) (pushed_count + length (pushed movement))
    (popped_count + length (popped movement)).
Proof.
  intros before after movement pushed_count popped_count STEP INV.
  destruct (each_step_retains_actual_occurrences _ _ _ STEP) as [rest [BEFORE AFTER]].
  rewrite BEFORE in INV. apply popping_original_prefix_transports_inventory in INV.
  rewrite AFTER, rev_app_distr.
  pose proof (@AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.PushedBatch
    Task (rev rest) pushed_count (popped_count + length (popped movement))
      (rev (pushed movement)) INV) as PUSH.
  now rewrite rev_length in PUSH.
Qed.

Definition task_sum (weight : Task -> nat) tasks :=
  fold_right (fun task total => weight task + total) 0 tasks.
Lemma task_sum_app : forall weight first second,
  task_sum weight (first ++ second) = task_sum weight first + task_sum weight second.
Proof. intros weight first. induction first as [|task rest IH]; intro second; [reflexivity|].
  change (weight task + task_sum weight (rest ++ second) =
    weight task + task_sum weight rest + task_sum weight second). rewrite IH. lia. Qed.
Lemma task_sum_rev : forall weight tasks, task_sum weight (rev tasks) = task_sum weight tasks.
Proof. intros weight tasks. induction tasks as [|task rest IH]; [reflexivity|].
  cbn [rev]. rewrite task_sum_app, IH.
  change (task_sum weight rest + (weight task + 0) = weight task + task_sum weight rest).
  lia. Qed.
Definition sum_moves (measure : Move -> nat) movements :=
  fold_right (fun movement total => measure movement + total) 0 movements.
Definition pushed_sum weight := sum_moves (fun movement => task_sum weight (pushed movement)).
Definition popped_sum weight := sum_moves (fun movement => task_sum weight (popped movement)).

Theorem complete_run_occurrence_balance : forall before movements last rounds,
  Run before movements last rounds -> forall weight,
  task_sum weight (pending before) + pushed_sum weight movements =
    popped_sum weight movements + task_sum weight last.
Proof.
  intros before movements last rounds RUN. induction RUN; intro weight.
  - destruct H; cbn [pending pushed_sum popped_sum sum_moves fold_right]; lia.
  - destruct (each_step_retains_actual_occurrences _ _ _ H) as [rest [BEFORE AFTER]].
    specialize (IHRUN weight). rewrite AFTER, task_sum_app in IHRUN.
    rewrite BEFORE, task_sum_app.
    change (task_sum weight (popped movement) + task_sum weight rest +
      (task_sum weight (pushed movement) + pushed_sum weight movements) =
      task_sum weight (popped movement) + popped_sum weight movements + task_sum weight last).
    lia.
Qed.

Definition start_weight task := match task with S.Start _ _ => 1 | _ => 0 end.
Definition resume_weight task := match task with S.Resume _ _ => 1 | _ => 0 end.
Definition borrowed_weight task := match task with S.Borrowed _ => 1 | _ => 0 end.
Lemma nonresume_has_zero_resume_weight : forall tasks,
  Forall (fun task => S.not_resume task = true) tasks -> task_sum resume_weight tasks = 0.
Proof. intros tasks ALL. induction ALL; [reflexivity|].
  destruct x; cbn [S.not_resume] in H; try discriminate;
    change (0 + task_sum resume_weight l = 0); exact IHALL. Qed.
Lemma each_task_has_one_kind : forall tasks,
  task_sum (fun _ => 1) tasks = task_sum borrowed_weight tasks +
    task_sum start_weight tasks + task_sum resume_weight tasks.
Proof. induction tasks as [|task rest IH]; [reflexivity|].
  change (1 + task_sum (fun _ => 1) rest =
    borrowed_weight task + task_sum borrowed_weight rest +
    (start_weight task + task_sum start_weight rest) +
    (resume_weight task + task_sum resume_weight rest)).
  destruct task; cbn [borrowed_weight start_weight resume_weight]; lia. Qed.
Lemma task_sum_unit_is_length : forall tasks, task_sum (fun _ => 1) tasks = length tasks.
Proof. induction tasks as [|task rest IH]; [reflexivity|].
  change (1 + task_sum (fun _ => 1) rest = S (length rest)). now rewrite IH. Qed.
Lemma reply_pushes_exactly_one_resume_per_request : forall owner cb reply,
  task_sum resume_weight (reply_tasks owner cb reply) = reply_requests reply.
Proof. intros owner cb []; reflexivity. Qed.

Theorem each_step_callbacks_and_delivery_are_original : forall before after movement,
  Step before after movement ->
  task_sum resume_weight (pushed movement) = request_count movement /\
  callback_count movement <= task_sum start_weight (popped movement) +
    task_sum resume_weight (popped movement) /\
  round_count movement <= task_sum resume_weight (popped movement).
Proof.
  intros before after movement STEP. destruct STEP.
  - cbn [borrowed_move pushed popped callback_count request_count round_count].
    rewrite task_sum_rev. rewrite nonresume_has_zero_resume_weight by assumption.
    repeat split; reflexivity.
  - cbn [callback_move pushed popped callback_count request_count round_count].
    rewrite reply_pushes_exactly_one_resume_per_request.
    cbn [task_sum fold_right start_weight resume_weight]. repeat split; lia.
  - cbn [callback_move pushed popped callback_count request_count round_count].
    rewrite reply_pushes_exactly_one_resume_per_request.
    cbn [task_sum fold_right start_weight resume_weight]. repeat split; lia.
  - cbn [callback_move pushed popped callback_count request_count round_count].
    rewrite reply_pushes_exactly_one_resume_per_request, !task_sum_app.
    change (reply_requests reply = reply_requests reply /\
      1 <= task_sum start_weight skipped + 0 + (task_sum resume_weight skipped + 1) /\
      1 <= task_sum resume_weight skipped + 1). lia.
Qed.

Theorem run_resume_callback_round_inventory : forall before movements last rounds,
  Run before movements last rounds ->
  pushed_sum resume_weight movements = sum_moves request_count movements /\
  sum_moves callback_count movements <= popped_sum start_weight movements + popped_sum resume_weight movements /\
  sum_moves round_count movements <= popped_sum resume_weight movements /\ rounds <= 1 /\
  task_sum resume_weight last = 0.
Proof.
  intros before movements last rounds RUN. induction RUN.
  - destruct H; cbn [pushed_sum popped_sum sum_moves fold_right];
      repeat split; try lia; try reflexivity.
    now apply nonresume_has_zero_resume_weight.
  - destruct (each_step_callbacks_and_delivery_are_original _ _ _ H) as [REQUEST [CALL ROUND]].
    destruct IHRUN as [REQ [CALLS [ROUNDS [FINAL LAST]]]].
    change (task_sum resume_weight (pushed movement) + pushed_sum resume_weight movements =
      request_count movement + sum_moves request_count movements /\
      callback_count movement + sum_moves callback_count movements <=
        task_sum start_weight (popped movement) + popped_sum start_weight movements +
        (task_sum resume_weight (popped movement) + popped_sum resume_weight movements) /\
      round_count movement + sum_moves round_count movements <=
        task_sum resume_weight (popped movement) + popped_sum resume_weight movements /\
      rounds <= 1 /\ task_sum resume_weight last = 0).
    repeat split; lia.
Qed.

(** Counts are projections of actual source movements, not supplied budgets. *)
Definition total_pushes := sum_moves (fun movement => length (pushed movement)).
Definition total_pops movements (last : list Task) :=
  sum_moves (fun movement => length (popped movement)) movements + length last.
Definition driver_work movements last terminal_rounds :=
  2 * total_pops movements last + 2 * total_pushes movements +
  sum_moves round_count movements + terminal_rounds + 1 +
  3 * sum_moves callback_count movements + sum_moves request_count movements.
Lemma pushes_are_unit_weight : forall movements,
  total_pushes movements = pushed_sum (fun _ => 1) movements.
Proof. induction movements as [|movement rest IH]; [reflexivity|].
  change (length (pushed movement) + total_pushes rest =
    task_sum (fun _ => 1) (pushed movement) + pushed_sum (fun _ => 1) rest).
  rewrite task_sum_unit_is_length, IH. reflexivity. Qed.
Lemma pops_are_unit_weight : forall movements last,
  total_pops movements last = popped_sum (fun _ => 1) movements + task_sum (fun _ => 1) last.
Proof.
  intros movements last. unfold total_pops. rewrite task_sum_unit_is_length.
  induction movements as [|movement rest IH]; [reflexivity|].
  change (length (popped movement) +
    sum_moves (fun movement => length (popped movement)) rest + length last =
    task_sum (fun _ => 1) (popped movement) + popped_sum (fun _ => 1) rest + length last).
  rewrite task_sum_unit_is_length. lia.
Qed.
Theorem complete_driver_control_cover : forall root movements last rounds,
  Run (Drive [root]) movements last rounds -> resume_weight root = 0 ->
  driver_work movements last rounds <=
    4 + 4 * total_pushes movements + 3 *
      (start_weight root + pushed_sum start_weight movements) +
      5 * sum_moves request_count movements.
Proof.
  intros root movements last rounds RUN ROOT.
  pose proof (complete_run_occurrence_balance _ _ _ _ RUN (fun _ => 1)) as POPS.
  pose proof (complete_run_occurrence_balance _ _ _ _ RUN start_weight) as STARTS.
  pose proof (complete_run_occurrence_balance _ _ _ _ RUN resume_weight) as RESUMES.
  destruct (run_resume_callback_round_inventory _ _ _ _ RUN)
    as [REQUEST [CALLS [ROUNDS [TERMINAL LAST]]]].
  change (1 + pushed_sum (fun _ => 1) movements =
    popped_sum (fun _ => 1) movements + task_sum (fun _ => 1) last) in POPS.
  change (start_weight root + 0 + pushed_sum start_weight movements =
    popped_sum start_weight movements + task_sum start_weight last) in STARTS.
  change (resume_weight root + 0 + pushed_sum resume_weight movements =
    popped_sum resume_weight movements + task_sum resume_weight last) in RESUMES.
  rewrite ROOT, REQUEST, LAST in RESUMES.
  rewrite <- pushes_are_unit_weight in POPS. rewrite <- pops_are_unit_weight in POPS.
  unfold driver_work. nia.
Qed.

Lemma pushes_partition_by_original_kind : forall movements,
  total_pushes movements = pushed_sum borrowed_weight movements +
    pushed_sum start_weight movements + pushed_sum resume_weight movements.
Proof.
  induction movements as [|movement rest IH]; [reflexivity|].
  pose proof (each_task_has_one_kind (pushed movement)) as KIND.
  rewrite task_sum_unit_is_length in KIND.
  change (length (pushed movement) + total_pushes rest =
    task_sum borrowed_weight (pushed movement) + pushed_sum borrowed_weight rest +
    (task_sum start_weight (pushed movement) + pushed_sum start_weight rest) +
    (task_sum resume_weight (pushed movement) + pushed_sum resume_weight rest)). lia.
Qed.
Theorem ordinary_collection_continuations_have_the_additive_cover :
  forall root movements last rounds,
  Run (Drive [S.Borrowed root]) movements last rounds ->
  15 + driver_work movements last rounds <=
    19 + 4 * pushed_sum borrowed_weight movements +
    7 * pushed_sum start_weight movements + 9 * sum_moves request_count movements.
Proof.
  intros root movements last rounds RUN.
  pose proof (complete_driver_control_cover _ _ _ _ RUN eq_refl) as BOUND.
  destruct (run_resume_callback_round_inventory _ _ _ _ RUN) as [REQUEST _].
  rewrite pushes_partition_by_original_kind, REQUEST in BOUND.
  cbn [start_weight] in BOUND. nia.
Qed.
Theorem equality_auxiliary_continuations_have_the_additive_cover :
  forall owner cb movements last rounds,
  Run (Drive [S.Start owner cb]) movements last rounds ->
  20 + driver_work movements last rounds <=
    27 + 4 * pushed_sum borrowed_weight movements +
    7 * pushed_sum start_weight movements + 9 * sum_moves request_count movements.
Proof.
  intros owner cb movements last rounds RUN.
  pose proof (complete_driver_control_cover _ _ _ _ RUN eq_refl) as BOUND.
  destruct (run_resume_callback_round_inventory _ _ _ _ RUN) as [REQUEST _].
  rewrite pushes_partition_by_original_kind, REQUEST in BOUND.
  cbn [start_weight] in BOUND. nia.
Qed.
Theorem native_task_records_are_not_duplicated : forall root movements last rounds,
  Run (Drive [root]) movements last rounds ->
  3 + total_pushes movements = 3 + pushed_sum borrowed_weight movements +
    pushed_sum start_weight movements + sum_moves request_count movements.
Proof.
  intros root movements last rounds RUN.
  destruct (run_resume_callback_round_inventory _ _ _ _ RUN) as [REQUEST _].
  rewrite pushes_partition_by_original_kind, REQUEST. lia.
Qed.
End SourceObservations.

Print Assumptions each_step_retains_actual_occurrences.
Print Assumptions consulted_verdict_is_the_original_answer.
Print Assumptions each_source_step_transports_existing_inventory.
Print Assumptions complete_run_occurrence_balance.
Print Assumptions each_step_callbacks_and_delivery_are_original.
Print Assumptions run_resume_callback_round_inventory.
Print Assumptions complete_driver_control_cover.
Print Assumptions ordinary_collection_continuations_have_the_additive_cover.
Print Assumptions equality_auxiliary_continuations_have_the_additive_cover.
Print Assumptions native_task_records_are_not_duplicated.
End GeneratedCollectionContinuationCover.
