(** Ordinary generated collection preparation, not another comparison engine.

    iterative_cmp.rs unordered_collection_cmp_machine_expr maps borrowed
    Map/Bag entries to CollectionCmpItem BEFORE collect. The outer Map does
    not inherit IndexMap Iter's collect override or TrustedLen. Pinned Rust
    2e2b193f8ada105f27608b7be81c293e0d7292cb therefore uses
    alloc/vec/spec_from_iter_nested.rs's generic initial-next branch and
    spec_extend/extend_desugared. Both native iterators have exact size hints.
    After the first yield, capacity >= remaining+1, so no reserve is reached.
    Allocation/layout success remains the reviewed standard-library boundary.

    The producer word distinguishes next attempts, successful item adapters,
    slot writes, and scalar control. Flat writes/allocation/disposal use the
    existing flat_counts convention; their cost is NOT included in scalar
    control. Source next bodies are separate (Map's slice advance or Bag's
    already-bounded raw table scan). No term Hash/Eq/Ord/Clone is executed.
    CollectionCmpPda::new then sums repetitions with slice Map::fold/Sum;
    its do-while has no invented final failed iterator next.

    Eq's auxiliary wrapper has an Option machine, two unconditional clears,
    a separate private TLS pool, and unavailable-TLS fallback. A normally
    returning comparison driver MAY leave pending tasks. The lifecycle model
    therefore permits arbitrary residual tasks and charges their disposal
    from the original push/owner inventory, never from an exhaustion premise.
    Nested completed calls preserve the empty private cell. Panic unwinding,
    TLS internals and arbitrary callback termination are not claimed.

    Source words are bounded logical groups, not CPU instruction counts.
    Their source association and actual emitted handler batches are reviewed
    Rust obligations. These component laws do not grant whole-key authority. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import AdmittedGeneratedHashScheduling
  AdmittedGeneratedCollectionScheduling AdmittedCollectionComparisonOwnership.
Import ListNotations.

Module GeneratedCollectionPreparation.
Module H := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Module S := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.
Module O := AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.

Inductive ProducerControl := CollectDispatch | NextMatch | RemainingHint
| CapacitySelect | CommitLength | ExtendDispatch | LengthCapacityTest | ReturnBuffer.
Section Producer.
Context {Entry : Type}.
Inductive ProducerEvent := Control (group : ProducerControl) | NextAttempt
| ConstructItem (entry : Entry) | WriteSlot (index : nat) (entry : Entry)
| RequestBuffer (capacity : nat) | EmptyHeader.
Definition scalar event := match event with Control _ => 1 | _ => 0 end.
Definition controls trace := fold_right (fun event total => scalar event + total) 0 trace.
Definition nexts trace := length (filter (fun event => match event with
  NextAttempt => true | _ => false end) trace).
Fixpoint writes trace := match trace with
| [] => [] | WriteSlot index entry :: rest => (index,entry) :: writes rest
| _ :: rest => writes rest end.
Definition tail_step index entry :=
  [NextAttempt; ConstructItem entry; Control NextMatch; Control LengthCapacityTest;
   WriteSlot index entry; Control CommitLength].
Fixpoint tail_word index source := match source with
| [] => [NextAttempt; Control NextMatch; Control ReturnBuffer]
| entry :: rest => tail_step index entry ++ tail_word (S index) rest end.
Definition producer minimum source := match source with
| [] => [Control CollectDispatch; NextAttempt; Control NextMatch;
    EmptyHeader; Control ReturnBuffer]
| entry :: rest =>
    [Control CollectDispatch; NextAttempt; ConstructItem entry; Control NextMatch;
     Control RemainingHint; Control CapacitySelect;
     RequestBuffer (Nat.max minimum (length source)); WriteSlot 0 entry;
     Control CommitLength; Control ExtendDispatch] ++ tail_word 1 rest
end.
Lemma controls_app : forall a b, controls (a ++ b) = controls a + controls b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  change (scalar event + controls (rest ++ b) =
    scalar event + controls rest + controls b). rewrite IH. lia. Qed.
Lemma nexts_app : forall a b, nexts (a ++ b) = nexts a + nexts b.
Proof. intros. unfold nexts. now rewrite filter_app, length_app. Qed.
Lemma writes_app : forall a b, writes (a ++ b) = writes a ++ writes b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  destruct event; cbn [app writes]; now rewrite IH. Qed.
Lemma tail_word_counts : forall source index,
  controls (tail_word index source) = 3 * length source + 2 /\
  nexts (tail_word index source) = length source + 1 /\
  writes (tail_word index source) = combine (seq index (length source)) source.
Proof.
  induction source as [|entry rest IH]; intro index; [repeat split; reflexivity|].
  specialize (IH (S index)). destruct IH as [HC [HN HW]].
  cbn [tail_word]. rewrite controls_app, nexts_app, writes_app.
  change (3 + controls (tail_word (S index) rest) = 3 * S (length rest) + 2 /\
    1 + nexts (tail_word (S index) rest) = S (length rest) + 1 /\
    (index, entry) :: writes (tail_word (S index) rest) =
      (index, entry) :: combine (seq (S index) (length rest)) rest).
  rewrite HC, HN, HW. repeat split; try reflexivity; lia.
Qed.
Theorem producer_exact_groups : forall minimum source,
  controls (producer minimum source) =
    (match source with [] => 3 | _ :: _ => 3 * length source + 5 end) /\
  nexts (producer minimum source) = length source + 1 /\
  writes (producer minimum source) = combine (seq 0 (length source)) source.
Proof.
  intros minimum [|entry rest]; [repeat split; reflexivity|].
  pose proof (tail_word_counts rest 1) as [HC [HN HW]].
  cbn [producer]. rewrite controls_app, nexts_app, writes_app.
  change (6 + controls (tail_word 1 rest) = 3 * S (length rest) + 5 /\
    1 + nexts (tail_word 1 rest) = S (length rest) + 1 /\
    (0, entry) :: writes (tail_word 1 rest) =
      (0, entry) :: combine (seq 1 (length rest)) rest).
  rewrite HC, HN, HW. repeat split; try reflexivity; lia.
Qed.
Theorem exact_remaining_hint_prevents_growth : forall minimum (source : list Entry) index,
  index < length source -> index < Nat.max minimum (length source).
Proof. intros. pose proof (Nat.le_max_r minimum (length source)). lia. Qed.
Definition generic_control_bound (source : list Entry) := 3 * length source + 5.
Theorem producer_control_is_width_bounded : forall minimum source,
  controls (producer minimum source) <= generic_control_bound source.
Proof. intros. destruct (producer_exact_groups minimum source) as [HC _].
  rewrite HC. destruct source; [change (3 <= 5); lia|apply Nat.le_refl]. Qed.
End Producer.

(** One sum uses the original, immutable repetitions, not expanded elements.
    ReadProjectAdd is the scalar field read plus usize accumulator update;
    AdvanceEndGuard is the slice fold's index increment and end comparison.
    Checked initialization must separately establish representable totals. *)
Inductive SumGroup := SumSetup | SumEmptyGuard | SumInitialize
| ReadProjectAdd | AdvanceEndGuard | SumReturn.
Fixpoint sum_body (repetitions : list nat) := match repetitions with
| [] => [] | _ :: rest => ReadProjectAdd :: AdvanceEndGuard :: sum_body rest end.
Definition sum_word repetitions := [SumSetup; SumEmptyGuard] ++
  (match repetitions with [] => [] | _ :: _ => SumInitialize :: sum_body repetitions end)
  ++ [SumReturn].
Lemma sum_body_count : forall repetitions, length (sum_body repetitions) = 2 * length repetitions.
Proof. induction repetitions; cbn; lia. Qed.
Theorem repetition_sum_word_is_width_bounded : forall repetitions,
  length (sum_word repetitions) <= 2 * length repetitions + 4.
Proof. intros [|entry rest]; [change (3 <= 4); lia|].
  unfold sum_word. rewrite !length_app. cbn [length].
  rewrite sum_body_count. cbn [length]. lia. Qed.

(** Source-next and item-constructor costs are composed, not executed here.
    MapNext includes slice advance and Bucket::refs, as SourceMapEntryVisit.
    Bag scan is passed separately from the existing native scan theorem. *)
Definition map_materialization_work width :=
  1 + (width + 1) + width + (3 * width + 5) + (2 * width + 4).
Definition bag_materialization_work width scan :=
  1 + scan + 2 * width + (3 * width + 5) + (2 * width + 4).
Theorem actual_producer_and_sum_words_fit_map_groups :
  forall Entry minimum (source : list Entry) repetitions,
  length repetitions = length source ->
  1 + nexts (producer minimum source) + length source +
    controls (producer minimum source) + length (sum_word repetitions) <=
  map_materialization_work (length source).
Proof.
  intros Entry minimum source repetitions LENGTH.
  pose proof (producer_control_is_width_bounded minimum source) as PRODUCER.
  pose proof (repetition_sum_word_is_width_bounded repetitions) as SUM.
  destruct (producer_exact_groups minimum source) as [_ [NEXT _]].
  unfold generic_control_bound in PRODUCER. unfold map_materialization_work.
  rewrite NEXT. rewrite LENGTH in SUM. lia.
Qed.
Theorem actual_producer_and_sum_words_fit_bag_groups :
  forall Entry minimum (source : list Entry) repetitions scan,
  length repetitions = length source ->
  1 + scan + 2 * length source + controls (producer minimum source) +
    length (sum_word repetitions) <= bag_materialization_work (length source) scan.
Proof.
  intros Entry minimum source repetitions scan LENGTH.
  pose proof (producer_control_is_width_bounded minimum source) as PRODUCER.
  pose proof (repetition_sum_word_is_width_bounded repetitions) as SUM.
  unfold generic_control_bound in PRODUCER. unfold bag_materialization_work.
  rewrite LENGTH in SUM. lia.
Qed.
Theorem two_roster_materialization_groups : forall left right left_scan right_scan,
  map_materialization_work left + map_materialization_work right = 7 * (left + right) + 22 /\
  bag_materialization_work left left_scan + bag_materialization_work right right_scan =
    7 * (left + right) + 20 + left_scan + right_scan.
Proof. intros. unfold map_materialization_work, bag_materialization_work. lia. Qed.

Inductive WrapperGroup := Entry | StoreSomeMachine | TryPool | InitializePool
| EmptyReplacementHeader | TakePool | ClearEntry | TakeMachine | ExpectMachine
| DriveEntry | BoxOwner | PushStart | InvokeDriver | FinalEquality | ClearExit
| SetPool | ReleaseReplacedHeader | ReturnClosure | TestTlsResult | ReturnWrapper
| LocalHeader | ReleaseLocalHeader.
Definition pooled_prefix (first : bool) := [Entry; StoreSomeMachine; TryPool] ++
  (if first then [InitializePool] else []) ++
  [EmptyReplacementHeader; TakePool; ClearEntry; TakeMachine; ExpectMachine;
   DriveEntry; BoxOwner; PushStart; InvokeDriver].
Definition pooled_suffix := [FinalEquality; ClearExit; SetPool;
  ReleaseReplacedHeader; ReturnClosure; TestTlsResult; ReturnWrapper].
Definition local_prefix := [Entry; StoreSomeMachine; TryPool; TestTlsResult;
  LocalHeader; ExpectMachine; DriveEntry; BoxOwner; PushStart; InvokeDriver].
Definition local_suffix := [FinalEquality; ReleaseLocalHeader; ReturnWrapper].
(** Box credit is already in collection owner inventory. Exclude it here. *)
Definition wrapper_work group := match group with BoxOwner => 0 | PushStart => 2 | _ => 1 end.
Definition wrapper_records group := match group with
| InitializePool | EmptyReplacementHeader | LocalHeader | PushStart => 1 | _ => 0 end.
Definition word_work word := fold_right (fun group total => wrapper_work group + total) 0 word.
Definition word_records word := fold_right (fun group total => wrapper_records group + total) 0 word.
Theorem wrapper_words_have_exact_local_costs :
  word_work (pooled_prefix true ++ pooled_suffix) = 20 /\
  word_records (pooled_prefix true ++ pooled_suffix) = 3 /\
  word_work (pooled_prefix false ++ pooled_suffix) = 19 /\
  word_records (pooled_prefix false ++ pooled_suffix) = 2 /\
  word_work (local_prefix ++ local_suffix) = 13 /\
  word_records (local_prefix ++ local_suffix) = 2.
Proof. repeat split; reflexivity. Qed.

Section AuxiliaryLifecycle.
Context {Task : Type}.
Definition pool_empty (pool : option (list Task)) := match pool with
| None => True | Some pending => pending = [] end.
(** Return may occur at any pending suffix. Batches and nested calls are
    observations of the actual source driver, not predicted comparator results.
    Counts below include original task pushes/pops only, not nested drivers. *)
Inductive CompletedCall : option (list Task) -> Task -> option (list Task) ->
    list WrapperGroup -> Prop :=
| PooledCall : forall first initial root residual returned nested pushes pops,
    DriverReturn [root] (Some []) residual (Some returned) nested pushes pops ->
    CompletedCall (Some initial) root (Some [])
      (pooled_prefix first ++ nested ++ pooled_suffix)
| LocalCall : forall root residual nested pushes pops,
    DriverReturn [root] None residual None nested pushes pops ->
    CompletedCall None root None (local_prefix ++ nested ++ local_suffix)
with DriverReturn : list Task -> option (list Task) -> list Task -> option (list Task) ->
    list WrapperGroup -> nat -> nat -> Prop :=
| ReturnNow : forall pending pool, DriverReturn pending pool pending pool [] 0 0
| ReturnAfterTask : forall pending task pool middle final residual batch during rest pushes pops,
    NestedCalls pool middle during ->
    DriverReturn (pending ++ batch) middle residual final rest pushes pops ->
    DriverReturn (pending ++ [task]) pool residual final (during ++ rest)
      (length batch + pushes) (S pops)
with NestedCalls : option (list Task) -> option (list Task) -> list WrapperGroup -> Prop :=
| NoNestedCalls : forall pool, NestedCalls pool pool []
| MoreNestedCalls : forall pool middle final root first rest,
    CompletedCall pool root middle first -> NestedCalls middle final rest ->
    NestedCalls pool final (first ++ rest).

Theorem completed_call_clears_and_restores_private_pool : forall pool root final word,
  CompletedCall pool root final word -> pool_empty final.
Proof. intros pool root final word CALL. destruct CALL; [reflexivity|exact I]. Qed.
Theorem nested_completed_calls_preserve_empty_pool : forall pool final word,
  NestedCalls pool final word -> pool_empty pool -> pool_empty final.
Proof. intros pool final word CALLS. induction CALLS; intro EMPTY; [exact EMPTY|].
  apply IHCALLS. eapply completed_call_clears_and_restores_private_pool; eassumption. Qed.
Theorem driver_return_preserves_empty_pool : forall pending pool residual final word pushes pops,
  DriverReturn pending pool residual final word pushes pops -> pool_empty pool -> pool_empty final.
Proof. intros pending pool residual final word pushes pops DRIVER.
  induction DRIVER; intro EMPTY; [exact EMPTY|]. apply IHDRIVER.
  eapply nested_completed_calls_preserve_empty_pool; eassumption. Qed.
Theorem replaced_pool_contains_no_pending_tasks : forall root residual returned word pushes pops,
  DriverReturn [root] (Some []) residual (Some returned) word pushes pops -> returned = [].
Proof. intros root residual returned word pushes pops DRIVER.
  exact (driver_return_preserves_empty_pool _ _ _ _ _ _ _ DRIVER eq_refl). Qed.
Theorem driver_return_transports_original_push_inventory :
  forall pending pool residual final word pushes pops,
  DriverReturn pending pool residual final word pushes pops ->
  forall before_push before_pop,
  H.PendingInventory pending before_push before_pop ->
  H.PendingInventory residual (before_push + pushes) (before_pop + pops).
Proof.
  intros pending pool residual final word pushes pops DRIVER. induction DRIVER;
    intros before_push before_pop INVENTORY.
  - now rewrite !Nat.add_0_r.
  - assert (POP : H.PendingInventory pending before_push (S before_pop)).
    { eapply H.PoppedTask. exact INVENTORY. }
    pose proof (@H.PushedBatch Task pending before_push (S before_pop) batch POP) as PUSH.
    specialize (IHDRIVER _ _ PUSH).
    replace (before_push + (length batch + pushes)) with
      ((before_push + length batch) + pushes) by lia.
    replace (before_pop + S pops) with (S before_pop + pops) by lia. exact IHDRIVER.
Qed.
End AuxiliaryLifecycle.

(** No extra residual-owner charge: the same original inventory pays both
    shells and flat collection machines. Native child ASTs are only borrowed. *)
Theorem auxiliary_residual_cleanup_reuses_existing_credit :
  forall pending pushed popped lookup event,
  H.PendingInventory pending pushed popped ->
  Forall (fun owner => Forall O.buffer_valid (lookup owner)) (S.owner_refs pending) ->
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.pending_disposal_counts (length pending) event +
    GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts
      (fun owner => S.owner_cleanup (lookup owner)) (S.owner_refs pending) event <=
  AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts pushed event +
    GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.sum_counts
      (fun owner => S.owner_credit (lookup owner)) (S.owner_refs pending) event.
Proof. exact S.pending_shells_and_owners_are_both_covered. Qed.

Print Assumptions producer_exact_groups.
Print Assumptions exact_remaining_hint_prevents_growth.
Print Assumptions producer_control_is_width_bounded.
Print Assumptions repetition_sum_word_is_width_bounded.
Print Assumptions two_roster_materialization_groups.
Print Assumptions actual_producer_and_sum_words_fit_map_groups.
Print Assumptions actual_producer_and_sum_words_fit_bag_groups.
Print Assumptions wrapper_words_have_exact_local_costs.
Print Assumptions completed_call_clears_and_restores_private_pool.
Print Assumptions replaced_pool_contains_no_pending_tasks.
Print Assumptions driver_return_transports_original_push_inventory.
Print Assumptions auxiliary_residual_cleanup_reuses_existing_credit.
End GeneratedCollectionPreparation.
