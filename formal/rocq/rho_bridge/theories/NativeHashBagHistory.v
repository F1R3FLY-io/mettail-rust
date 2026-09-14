(** Completed native operations expose capacity after reserve and insertion.
    Recording its historical maximum covers tombstones left by later erases.
    Internal resize states need not satisfy that history bound: observation
    follows RawFinish, including Found after a reserve-before-lookup resize.
    This is an extent invariant, not a prepayment or allocator/RSS theorem. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From RhoBridge Require Import NativeHashBagExtent.

Module NativeHashBagHistory.
Import NativeHashBagExtent.NativeHashBagExtent.

Definition observe state :=
  {| buckets := buckets state; items := items state; deleted := deleted state;
     growth_left := growth_left state;
     history := Nat.max (history state) (observed_capacity state) |}.

Lemma observation_preserves_counters : forall state,
  valid_counters state -> valid_counters (observe state).
Proof. intros state VALID. exact VALID. Qed.

Lemma observation_preserves_coverage : forall state,
  history_covers_full_capacity state ->
  history_covers_full_capacity (observe state).
Proof.
  intros state COVER. unfold history_covers_full_capacity, observe in *; cbn.
  eapply Nat.le_trans; [exact COVER|apply Nat.le_max_l].
Qed.

Lemma clean_observation_covers_capacity : forall state,
  valid_counters state -> deleted state = 0 ->
  history_covers_full_capacity (observe state).
Proof.
  intros state [_ BALANCE] CLEAN.
  unfold history_covers_full_capacity, observe, observed_capacity; cbn.
  rewrite CLEAN in BALANCE.
  replace (full_capacity (buckets state)) with
    (items state + growth_left state) by lia. apply Nat.le_max_r.
Qed.

Lemma finish_preserves_cleanliness : forall before after,
  RawFinish before after -> deleted before = 0 -> deleted after = 0.
Proof.
  intros before after STEP CLEAN. destruct STEP; cbn in *; lia.
Qed.

Lemma finish_preserves_coverage : forall before after,
  RawFinish before after -> history_covers_full_capacity before ->
  history_covers_full_capacity after.
Proof.
  intros before after STEP COVER. destruct STEP; exact COVER.
Qed.

Theorem completed_insert_preserves_counters_and_coverage :
  forall before prepared finished,
  RawReserve before prepared -> RawFinish prepared finished ->
  valid_counters before -> history_covers_full_capacity before ->
  valid_counters (observe finished) /\
  history_covers_full_capacity (observe finished).
Proof.
  intros before prepared finished RESERVE FINISH VALID COVER.
  pose proof (raw_reserve_preserves_counters_and_history
    _ _ RESERVE VALID) as [PREPARED _].
  pose proof (raw_finish_preserves_counters_and_history
    _ _ FINISH PREPARED) as [FINISHED _].
  split; [apply observation_preserves_counters; exact FINISHED|].
  destruct RESERVE.
  - apply observation_preserves_coverage.
    eapply finish_preserves_coverage; eassumption.
  - apply clean_observation_covers_capacity; [exact FINISHED|].
    eapply finish_preserves_cleanliness; [exact FINISH|reflexivity].
  - apply clean_observation_covers_capacity; [exact FINISHED|].
    eapply finish_preserves_cleanliness; [exact FINISH|reflexivity].
Qed.

Theorem completed_erase_preserves_counters_and_coverage : forall before after,
  RawErase before after -> valid_counters before ->
  history_covers_full_capacity before ->
  valid_counters after /\ history_covers_full_capacity after.
Proof.
  intros before after STEP VALID COVER.
  pose proof (raw_erase_preserves_counters_and_history
    _ _ STEP VALID) as [AFTER _].
  split; [exact AFTER|]. destruct STEP; exact COVER.
Qed.

(** Clone copies scalar metadata as well as the native table, whose pinned
    Global allocation preserves the source bucket count. Replacing the whole
    backing table starts at the singleton instead. Neither operation resets
    history merely because the number of retained entries becomes zero. *)
Inductive CompletedOperation : TableState -> TableState -> Prop :=
| CompletedInsert : forall before prepared finished,
    RawReserve before prepared -> RawFinish prepared finished ->
    CompletedOperation before (observe finished)
| CompletedErase : forall before after,
    RawErase before after -> CompletedOperation before after
| CompletedClone : forall state, CompletedOperation state state
| CompletedReset : forall state, CompletedOperation state fresh_table.

Definition tracked state :=
  valid_counters state /\ history_covers_full_capacity state.

Theorem completed_operations_preserve_tracking : forall before after,
  CompletedOperation before after -> tracked before -> tracked after.
Proof.
  intros before after STEP [VALID COVER]. destruct STEP.
  - eapply completed_insert_preserves_counters_and_coverage; eassumption.
  - eapply completed_erase_preserves_counters_and_coverage; eassumption.
  - split; assumption.
  - destruct a_fresh_singleton_has_exact_counters_and_history
      as [FRESH [HISTORY _]]. split; assumption.
Qed.

(** This finite execution relation does not assume the target history bound.
    Each constructor records one completed native wrapper operation. *)
Inductive Reachable : TableState -> Prop :=
| ReachableFresh : Reachable fresh_table
| ReachableStep : forall before after,
    Reachable before -> CompletedOperation before after -> Reachable after.

Theorem reachable_tables_have_valid_counters_and_history : forall state,
  Reachable state -> tracked state.
Proof.
  intros state REACHABLE. induction REACHABLE.
  - destruct a_fresh_singleton_has_exact_counters_and_history
      as [FRESH [HISTORY _]]. split; assumption.
  - eapply completed_operations_preserve_tracking; eassumption.
Qed.

Definition historical_bucket_bound state := Nat.max 1 (2 * history state).

Theorem tracked_bucket_extent_is_bounded : forall state,
  tracked state -> buckets state <= historical_bucket_bound state.
Proof.
  intros state [[NATIVE BALANCE] COVER].
  unfold history_covers_full_capacity in COVER.
  unfold historical_bucket_bound. destruct NATIVE.
  - apply Nat.le_max_l.
  - pose proof (allocated_buckets_are_at_most_twice_their_full_capacity exponent).
    eapply Nat.le_trans; [|apply Nat.le_max_r]. lia.
Qed.

Corollary every_completed_native_execution_has_bounded_bucket_extent :
  forall state, Reachable state ->
  buckets state <= historical_bucket_bound state.
Proof.
  intros state REACHABLE. apply tracked_bucket_extent_is_bounded.
  apply reachable_tables_have_valid_counters_and_history. exact REACHABLE.
Qed.

End NativeHashBagHistory.

Print Assumptions NativeHashBagHistory.completed_insert_preserves_counters_and_coverage.
Print Assumptions NativeHashBagHistory.completed_erase_preserves_counters_and_coverage.
Print Assumptions NativeHashBagHistory.completed_operations_preserve_tracking.
Print Assumptions NativeHashBagHistory.reachable_tables_have_valid_counters_and_history.
Print Assumptions NativeHashBagHistory.tracked_bucket_extent_is_bounded.
Print Assumptions NativeHashBagHistory.every_completed_native_execution_has_bounded_bucket_extent.
