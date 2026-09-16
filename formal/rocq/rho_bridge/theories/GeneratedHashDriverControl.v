(** Ordinary generated Hash: driver/task control, not complete Hash admission.

    Source: macros/src/gen/term_ops/iterative_hash.rs, generate_hash_engine
    and the ORDINARY branch of generate_hash_task_enum. The original borrowed
    tasks and the exact batches pushed by their category handlers are the
    inputs to this projection. There is no second AST walk or runtime plan.

    Source-group map:
      PopAttempt: while-let stack.pop, including its final None;
      DispatchTask: match the popped task and select its arm;
      InvokeCategory/BorrowCategory/IndexCategory/SelectVariant/ReturnCategory:
        helper call, &*ptr, variant_index_cat(val), match val, normal return;
      EraseHasher/InvokeOpaque/BorrowOpaqueValue/BorrowOpaqueHasher/ReturnOpaque:
        state as *mut H as *mut (), callback call, its two original reborrows,
        and normal callback return;
      PushTask: the existing task construction/push/pending-disposal group;
      ReturnDriver: normal return after the terminal pop.
    Discriminant and payload Hash calls are NOT counted here: their sealed
    native leaf work is separate. InvokeOpaque is the trampoline call, not
    its payload's Hash dispatch. Each named fixed source group contributes
    one NativeWork; PushTask reuses the existing two-work/one-record law.

    category_schedule is the projection of the ORIGINAL emitted handler:
    it relates its original task to its exact push-order batch. It is not a
    cost oracle and supplies no trace/count bound. SourceStep forces every
    non-category task to push nothing. Run retains the actual popped task,
    its batch, and exact resulting pending stack. Counts below are derived
    from that run, not supplied as independent annotations. This abstraction
    deliberately leaves handler semantics/source correspondence to the shared
    emitter; it does not establish those facts by assuming their costs.

    EXCLUDED local groups still requiring their own source projection: field
    projections and option matches; scope pattern/body extraction; collection
    length/iterator/collection-buffer operations; Map native sorting and its
    comparison callbacks. Eager native leaves and all native callback bodies
    are excluded too. No theorem calls this component a complete driver or
    category bound. PathMapMode's DISPATCH is included because ordinary Hash
    has that arm; this grants no leaf/profile support for PathMap.

    Header/TLS wrapper counts are reused separately and already include the
    initial root push. Therefore this component counts only handler-produced
    pushes. The final root theorem prevents counting that push twice.
    Normal finite runs, valid borrowed source pointers and actual source
    scheduling are required. No arbitrary Hasher/callback, allocator, physical
    memory, panic-unwind or native termination guarantee is asserted. *)
From Stdlib Require Import List Arith Lia Ring Sorting.Permutation.
From RhoBridge Require Import AdmittedKeyHashExecution
  AdmittedGeneratedHashScheduling GeneratedDummyCleanupReservation.
Import ListNotations.

Module GeneratedHashDriverControl.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module S := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Module D := GeneratedDummyCleanupReservation.

Inductive TaskKind := Category | Word | Byte | PathMapMode | Opaque.
Inductive Group := PopAttempt | DispatchTask | InvokeCategory | BorrowCategory
  | IndexCategory | SelectVariant | ReturnCategory | EraseHasher | InvokeOpaque
  | BorrowOpaqueValue | BorrowOpaqueHasher | ReturnOpaque | PushTask | ReturnDriver.

Definition group_counts group : D.Counts :=
  match group with
  | PushTask => H.push_range_counts 1
  | PopAttempt => H.pop_counts
  | _ => D.atom D.NativeWork
  end.
Definition word_counts groups : D.Counts := fun event =>
  fold_right (fun group total => group_counts group event + total) 0 groups.

Lemma word_counts_app : forall first second event,
  word_counts (first ++ second) event = word_counts first event + word_counts second event.
Proof.
  intros first. induction first as [|group rest IH]; intros second event; [reflexivity|].
  change (group_counts group event + word_counts (rest ++ second) event =
    (group_counts group event + word_counts rest event) + word_counts second event).
  rewrite IH. lia.
Qed.

Lemma pushed_word_counts : forall n event,
  word_counts (repeat PushTask n) event = H.push_range_counts n event.
Proof.
  induction n; intro event; [reflexivity|].
  change (group_counts PushTask event + word_counts (repeat PushTask n) event =
    H.push_range_counts (S n) event).
  rewrite IHn. unfold group_counts, H.push_range_counts. lia.
Qed.

Definition kind_category kind := match kind with Category => 1 | _ => 0 end.
Definition kind_opaque kind := match kind with Opaque => 1 | _ => 0 end.
Definition step_word kind width :=
  [PopAttempt; DispatchTask] ++
  match kind with
  | Category => [InvokeCategory; BorrowCategory; IndexCategory; SelectVariant] ++
      repeat PushTask width ++ [ReturnCategory]
  | Opaque => [EraseHasher; InvokeOpaque; BorrowOpaqueValue;
      BorrowOpaqueHasher; ReturnOpaque]
  | _ => []
  end.

Section SourceTasks.
Context {Task : Type}.
Variable kind : Task -> TaskKind.
Variable category_schedule : Task -> list Task -> Prop.

Inductive SourceStep : Task -> list Task -> Prop :=
| CategoryStep : forall task batch,
    kind task = Category -> category_schedule task batch -> SourceStep task batch
| WordStep : forall task, kind task = Word -> SourceStep task []
| ByteStep : forall task, kind task = Byte -> SourceStep task []
| PathMapModeStep : forall task, kind task = PathMapMode -> SourceStep task []
| OpaqueStep : forall task, kind task = Opaque -> SourceStep task [].

Definition SourceRecord := (Task * list Task)%type.
Inductive Run : list Task -> list SourceRecord -> Prop :=
| DriverDone : Run [] []
| DriverNext : forall pending task batch rest,
    SourceStep task batch -> Run (pending ++ batch) rest ->
    Run (pending ++ [task]) ((task, batch) :: rest).

Definition pushed (records : list SourceRecord) :=
  fold_right (fun record total => length (snd record) + total) 0 records.
Definition categories (records : list SourceRecord) :=
  fold_right (fun record total => kind_category (kind (fst record)) + total) 0 records.
Definition opaques (records : list SourceRecord) :=
  fold_right (fun record total => kind_opaque (kind (fst record)) + total) 0 records.
Definition source_word (records : list SourceRecord) :=
  concat (map (fun record => step_word (kind (fst record)) (length (snd record))) records) ++
    [PopAttempt; ReturnDriver].

Lemma source_word_cons : forall task batch rest,
  source_word ((task, batch) :: rest) =
  step_word (kind task) (length batch) ++ source_word rest.
Proof. intros. unfold source_word. cbn [map concat fst snd].
  now rewrite <- app_assoc. Qed.

(** A profile retains one original task kind and its exact emitted batch
    width. No profile is a whole-task/native receipt. In particular a Map
    handler's sorted and unsorted batches differ as lists, so callers must
    establish this occurrence-preserving projection, not trace equality. *)
Definition record_profile (record : SourceRecord) :=
  (kind (fst record), length (snd record)).
Definition profile_counts profiles event :=
  fold_right (fun profile total =>
    word_counts (step_word (fst profile) (snd profile)) event + total) 0 profiles.

Lemma source_word_is_its_profile_fold : forall records event,
  word_counts (source_word records) event =
  profile_counts (map record_profile records) event +
  word_counts [PopAttempt; ReturnDriver] event.
Proof.
  induction records as [|[task batch] rest IH]; intro event; [reflexivity|].
  rewrite source_word_cons.
  change (word_counts (step_word (kind task) (length batch) ++ source_word rest) event =
    (word_counts (step_word (kind task) (length batch)) event +
      profile_counts (map record_profile rest) event) +
    word_counts [PopAttempt; ReturnDriver] event).
  rewrite word_counts_app, IH. lia.
Qed.

Theorem task_kind_and_batch_occurrences_preserve_control_counts :
  forall first second,
  Permutation (map record_profile first) (map record_profile second) ->
  forall event, word_counts (source_word first) event = word_counts (source_word second) event.
Proof.
  intros first second ORDER event. rewrite !source_word_is_its_profile_fold.
  assert (SAME : forall left right,
    Permutation left right -> profile_counts left event = profile_counts right event).
  { intros left right PERM. induction PERM.
    - reflexivity.
    - change (word_counts (step_word (fst x) (snd x)) event + profile_counts l event =
        word_counts (step_word (fst x) (snd x)) event + profile_counts l' event).
      now rewrite IHPERM.
    - unfold profile_counts. cbn [fold_right]. lia.
    - now rewrite IHPERM1, IHPERM2. }
  now rewrite (SAME _ _ ORDER).
Qed.

Theorem source_step_has_no_hidden_noncategory_pushes : forall task batch,
  SourceStep task batch -> kind task <> Category -> batch = [].
Proof. intros task batch STEP NOTCAT. destruct STEP; congruence. Qed.

Theorem successful_run_has_exact_push_pop_inventory : forall pending records,
  Run pending records -> length pending + pushed records = length records.
Proof.
  intros pending records RUN. induction RUN.
  - reflexivity.
  - change (length (pending ++ [task]) + (length batch + pushed rest) =
      S (length rest)).
    rewrite length_app in IHRUN |- *.
    cbn [length]. lia.
Qed.

Theorem run_uses_the_existing_pending_inventory : forall pending records,
  Run pending records -> forall prior_pushes prior_pops,
  @S.PendingInventory Task pending prior_pushes prior_pops ->
  @S.PendingInventory Task [] (prior_pushes + pushed records) (prior_pops + length records).
Proof.
  intros pending records RUN. induction RUN; intros prior_pushes prior_pops INVENTORY.
  - cbn [pushed fold_right length]. now rewrite !Nat.add_0_r.
  - pose proof (@S.PoppedTask Task pending task prior_pushes prior_pops INVENTORY) as POP.
    pose proof (@S.PushedBatch Task pending prior_pushes (S prior_pops) batch POP) as PUSH.
    specialize (IHRUN _ _ PUSH).
    change (@S.PendingInventory Task []
      (prior_pushes + (length batch + pushed rest))
      (prior_pops + S (length rest))).
    replace (prior_pushes + (length batch + pushed rest)) with
      ((prior_pushes + length batch) + pushed rest) by lia.
    replace (prior_pops + S (length rest)) with (S prior_pops + length rest) by lia.
    exact IHRUN.
Qed.

Theorem exact_root_run_counts_only_nonroot_pushes : forall root records,
  Run [root] records -> S (pushed records) = length records.
Proof. intros root records RUN.
  pose proof (successful_run_has_exact_push_pop_inventory _ _ RUN) as BALANCE.
  cbn in BALANCE. lia. Qed.

Lemma source_step_counts : forall task batch,
  SourceStep task batch -> forall event,
  word_counts (step_word (kind task) (length batch)) event =
    (2 + 5 * kind_category (kind task) + 5 * kind_opaque (kind task) +
      2 * length batch) * D.atom D.NativeWork event +
    length batch * D.atom D.NativeRecord event.
Proof.
  intros task batch STEP event.
  destruct STEP as [task batch KIND SCHEDULE | task KIND | task KIND |
    task KIND | task KIND]; rewrite KIND;
    unfold step_word, kind_category, kind_opaque;
    rewrite !word_counts_app, ?pushed_word_counts;
    unfold word_counts, group_counts, H.pop_counts, H.push_range_counts;
    cbn [fold_right length]; nia.
Qed.

Lemma driver_step_arithmetic : forall n c o cs os b p w r : nat,
  (2 + 5*c + 5*o + 2*b)*w + b*r +
    ((2 + 2*n + 5*cs + 5*os + 2*p)*w + p*r) =
  (2 + 2*S n + 5*(c+cs) + 5*(o+os) + 2*(b+p))*w + (b+p)*r.
Proof. intros. ring. Qed.

Theorem source_driver_control_counts_are_derived : forall pending records,
  Run pending records -> forall event,
  word_counts (source_word records) event =
    (2 + 2 * length records + 5 * categories records + 5 * opaques records +
      2 * pushed records) * D.atom D.NativeWork event +
    pushed records * D.atom D.NativeRecord event.
Proof.
  intros pending records RUN.
  induction RUN as [|pending task batch rest STEP RUN IH]; intro event.
  - unfold source_word, word_counts, group_counts, H.pop_counts,
      categories, opaques, pushed. cbn. lia.
  - rewrite source_word_cons.
    change (word_counts (step_word (kind task) (length batch) ++ source_word rest) event =
      (2 + 2 * length ((task, batch) :: rest) +
        5 * categories ((task, batch) :: rest) + 5 * opaques ((task, batch) :: rest) +
        2 * pushed ((task, batch) :: rest)) * D.atom D.NativeWork event +
      pushed ((task, batch) :: rest) * D.atom D.NativeRecord event).
    rewrite word_counts_app, (source_step_counts _ _ STEP), IH.
    unfold categories, opaques, pushed. cbn [length fold_right fst snd].
    apply driver_step_arithmetic.
Qed.

(** PopAttempt alone is exactly the existing one-work event; the terminal
    ReturnDriver is a separate bounded group, not a fictitious popped task. *)
Lemma terminal_groups_are_two_work_and_no_records : forall event,
  word_counts [PopAttempt; ReturnDriver] event = 2 * D.atom D.NativeWork event.
Proof. intro event. unfold word_counts, group_counts, H.pop_counts.
  cbn [fold_right]. lia. Qed.

(** This combines ONLY the already-verified wrapper and this projection.
    The omitted handler/native groups must still be added before native Hash
    execution. The first-use wrapper covers both warm TLS and local fallback. *)
Theorem root_wrapper_plus_control_component : forall root records,
  Run [root] records -> forall event,
  S.hash_wrapper_counts (S.first_pooled_prefix ++ S.pooled_suffix true) event +
    word_counts (source_word records) event =
    (15 + 4 * length records + 5 * categories records + 5 * opaques records) *
      D.atom D.NativeWork event +
    (2 + length records) * D.atom D.NativeRecord event.
Proof.
  intros root records RUN event.
  rewrite S.first_use_pooled_wrapper_local_counts_are_exact,
    (source_driver_control_counts_are_derived _ _ RUN).
  pose proof (exact_root_run_counts_only_nonroot_pushes _ _ RUN) as BALANCE.
  nia.
Qed.

End SourceTasks.

Print Assumptions pushed_word_counts.
Print Assumptions source_step_has_no_hidden_noncategory_pushes.
Print Assumptions task_kind_and_batch_occurrences_preserve_control_counts.
Print Assumptions successful_run_has_exact_push_pop_inventory.
Print Assumptions run_uses_the_existing_pending_inventory.
Print Assumptions exact_root_run_counts_only_nonroot_pushes.
Print Assumptions source_driver_control_counts_are_derived.
Print Assumptions terminal_groups_are_two_work_and_no_records.
Print Assumptions root_wrapper_plus_control_component.
End GeneratedHashDriverControl.
