(** Prospective bucket sizing for one pinned native counts-table reservation.
    raw.rs capacity_to_buckets uses the small branch for capacity < 15.
    On the audited 64-bit/SSE2 profile, (T, usize) has size >= 8, so its
    minimum small capacity is three. This does not specialize T to Proc.

    These natural-number functions project successful source arithmetic.
    Rust checked multiplication, next-power-of-two and table-layout guards
    must succeed; a checked provider must validate predictable overflow before
    insertion, not rely on a later native panic. Global returns exactly the
    requested logical block length, so new_uninitialized does not enlarge the
    selected bucket count. Arbitrary allocators, RSS and allocation failure
    are outside this model. The library's least-power arithmetic is reused;
    this is not a verification of Rust bit_width or compiler lowering. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From RhoBridge Require Import NativeHashBagExtent NativeHashBagHistory.

Module NativeHashBagGrowth.
Import NativeHashBagExtent.NativeHashBagExtent.
Import NativeHashBagHistory.NativeHashBagHistory.

Definition source_capacity_to_buckets capacity :=
  if capacity <? 15 then
    let chosen := Nat.max 3 capacity in
    if chosen <? 4 then 4 else if chosen <? 8 then 8 else 16
  else 2 ^ Nat.log2_up (capacity * 8 / 7).

Definition source_resize_request state :=
  Nat.max (S (items state)) (S (full_capacity (buckets state))).

Theorem valid_counters_fix_the_resize_request : forall state,
  valid_counters state ->
  source_resize_request state = S (full_capacity (buckets state)).
Proof.
  intros state [_ BALANCE]. unfold source_resize_request.
  apply Nat.max_r. lia.
Qed.

Theorem singleton_resize_selects_four_buckets :
  source_capacity_to_buckets (S (full_capacity 1)) = 4.
Proof. reflexivity. Qed.

Theorem allocated_resize_selects_twice_the_original_buckets : forall exponent,
  source_capacity_to_buckets (S (full_capacity (2 ^ (exponent + 2)))) =
  2 * 2 ^ (exponent + 2).
Proof.
  intros [|[|exponent]].
  - change (source_capacity_to_buckets 4 = 8). reflexivity.
  - change (source_capacity_to_buckets 8 = 16). reflexivity.
  - assert (POWER : 2 ^ (S (S exponent) + 2) = 16 * 2 ^ exponent).
    { replace (S (S exponent) + 2) with (exponent + 4) by lia.
      rewrite Nat.pow_add_r. cbn [Nat.pow]. lia. }
    assert (POSITIVE : 0 < 2 ^ exponent).
    { pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
    assert (LARGE : (S (full_capacity (2 ^ (S (S exponent) + 2))) <? 15) = false).
    { apply Nat.ltb_ge. rewrite POWER.
      rewrite large_native_capacity_counts_seven_eighths by exact POSITIVE. lia. }
    assert (ADJUSTED : S (full_capacity (2 ^ (S (S exponent) + 2))) * 8 / 7 =
      S (2 ^ (S (S exponent) + 2))).
    { rewrite POWER.
      rewrite large_native_capacity_counts_seven_eighths by exact POSITIVE.
      symmetry. apply Nat.div_unique with (r := 1); lia. }
    unfold source_capacity_to_buckets. rewrite LARGE, ADJUSTED.
    rewrite Nat.log2_up_succ_pow2 by lia.
    rewrite Nat.pow_succ_r by lia. reflexivity.
Qed.

Definition source_resize_buckets state :=
  source_capacity_to_buckets (source_resize_request state).

Corollary valid_source_resize_has_the_exact_bucket_selection : forall state,
  valid_counters state ->
  source_resize_buckets state =
    if buckets state =? 1 then 4 else 2 * buckets state.
Proof.
  intros state VALID. unfold source_resize_buckets.
  rewrite valid_counters_fix_the_resize_request by exact VALID.
  destruct VALID as [NATIVE BALANCE]. destruct NATIVE.
  - exact singleton_resize_selects_four_buckets.
  - assert (NOT_SINGLETON : (2 ^ (exponent + 2) =? 1) = false).
    { apply Nat.eqb_neq. rewrite Nat.pow_add_r. cbn [Nat.pow].
      pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
    rewrite NOT_SINGLETON. apply allocated_resize_selects_twice_the_original_buckets.
Qed.

Lemma doubling_an_allocated_table_has_room_for_one_more : forall exponent,
  S (full_capacity (2 ^ (exponent + 2))) <=
  full_capacity (2 * 2 ^ (exponent + 2)).
Proof.
  intros [|[|exponent]]; [change (4 <= 7); lia|change (8 <= 14); lia|].
  assert (POWER : 2 ^ (S (S exponent) + 2) = 16 * 2 ^ exponent).
  { replace (S (S exponent) + 2) with (exponent + 4) by lia.
    rewrite Nat.pow_add_r. cbn [Nat.pow]. lia. }
  assert (POSITIVE : 0 < 2 ^ exponent).
  { pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
  rewrite POWER.
  replace (2 * (16 * 2 ^ exponent)) with (16 * (2 * 2 ^ exponent)) by lia.
  rewrite !large_native_capacity_counts_seven_eighths by lia. lia.
Qed.

Theorem valid_resize_selection_is_native_and_has_room : forall state,
  valid_counters state ->
  NativeBuckets (source_resize_buckets state) /\
  S (items state) <= full_capacity (source_resize_buckets state).
Proof.
  intros state VALID.
  rewrite valid_source_resize_has_the_exact_bucket_selection by exact VALID.
  destruct VALID as [NATIVE BALANCE]. destruct NATIVE.
  - cbn. split; [change (NativeBuckets (2 ^ (0 + 2))); constructor|].
    change (0 = items state + deleted state + growth_left state) in BALANCE. lia.
  - assert (NOT_SINGLETON : (2 ^ (exponent + 2) =? 1) = false).
    { apply Nat.eqb_neq. rewrite Nat.pow_add_r. cbn [Nat.pow].
      pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
    rewrite NOT_SINGLETON. split.
    + change (NativeBuckets (2 ^ (S exponent + 2))). constructor.
    + eapply Nat.le_trans; [|apply doubling_an_allocated_table_has_room_for_one_more].
      lia.
Qed.

(** Skip overapproximates omitted or unnecessary reservation, including an
    entry lookup that finds its key before reserving. It does not assert which
    native guard was selected. The resize constructor uses the derived source
    sizing function, not an assumed upper bound or spare-capacity premise. *)
Inductive SourceReserve : TableState -> TableState -> Prop :=
| SourceSkip : forall state, SourceReserve state state
| SourceRehash : forall state,
    growth_left state = 0 ->
    S (items state) <= full_capacity (buckets state) / 2 ->
    SourceReserve state (clean_table state (buckets state))
| SourceResize : forall state,
    growth_left state = 0 ->
    full_capacity (buckets state) / 2 < S (items state) ->
    SourceReserve state (clean_table state (source_resize_buckets state)).

Theorem source_reserve_refines_raw : forall before prepared,
  valid_counters before -> SourceReserve before prepared -> RawReserve before prepared.
Proof.
  intros before prepared VALID STEP. destruct STEP.
  - apply ReserveUnchanged.
  - apply ReserveRehash; assumption.
  - destruct (valid_resize_selection_is_native_and_has_room state VALID) as [NATIVE ROOM].
    apply ReserveResize; assumption.
Qed.

Lemma source_reserve_preserves_original_items : forall before prepared,
  SourceReserve before prepared -> items prepared = items before.
Proof. intros before prepared STEP. destruct STEP; reflexivity. Qed.

Definition prospective_bucket_bound state := Nat.max 4 (4 * history state).

Theorem source_reserve_is_prebounded : forall before prepared,
  Reachable before -> SourceReserve before prepared ->
  buckets prepared <= prospective_bucket_bound before.
Proof.
  intros before prepared REACHABLE STEP.
  pose proof (reachable_tables_have_valid_counters_and_history before REACHABLE)
    as [VALID COVER].
  pose proof (every_completed_native_execution_has_bounded_bucket_extent before REACHABLE)
    as OLD.
  destruct STEP; cbn [clean_table buckets];
    unfold prospective_bucket_bound, historical_bucket_bound in *.
  - lia.
  - lia.
  - rewrite valid_source_resize_has_the_exact_bucket_selection by exact VALID.
    destruct (buckets state =? 1) eqn:SINGLETON.
    + apply Nat.le_max_l.
    + apply Nat.eqb_neq in SINGLETON. lia.
Qed.

Theorem completed_source_insert_retains_the_prospective_bounds :
  forall before prepared finished,
  Reachable before -> SourceReserve before prepared -> RawFinish prepared finished ->
  Reachable (observe finished) /\
  buckets (observe finished) <= prospective_bucket_bound before /\
  items (observe finished) <= S (items before).
Proof.
  intros before prepared finished REACHABLE RESERVE FINISH.
  pose proof (reachable_tables_have_valid_counters_and_history before REACHABLE)
    as [VALID COVER].
  pose proof (source_reserve_refines_raw before prepared VALID RESERVE) as RAW.
  pose proof (source_reserve_is_prebounded before prepared REACHABLE RESERVE) as BOUND.
  pose proof (source_reserve_preserves_original_items before prepared RESERVE) as ITEMS.
  split.
  - eapply ReachableStep; [exact REACHABLE|].
    eapply CompletedInsert; [exact RAW|exact FINISH].
  - destruct FINISH; cbn [observe replace_counters buckets items] in *; split; lia.
Qed.

Theorem a_clean_exhausted_table_selects_resize_not_rehash : forall state,
  valid_counters state -> deleted state = 0 -> growth_left state = 0 ->
  full_capacity (buckets state) / 2 < S (items state).
Proof.
  intros state [_ BALANCE] CLEAN EXHAUSTED.
  assert (HALF : full_capacity (buckets state) / 2 <= full_capacity (buckets state)).
  { apply Nat.div_le_upper_bound; lia. }
  lia.
Qed.

Theorem completed_source_insert_preserves_cleanliness : forall before prepared finished,
  SourceReserve before prepared -> RawFinish prepared finished -> deleted before = 0 ->
  deleted (observe finished) = 0.
Proof.
  intros before prepared finished RESERVE FINISH CLEAN.
  assert (PREPARED : deleted prepared = 0).
  { destruct RESERVE; cbn [clean_table deleted]; assumption || reflexivity. }
  change (deleted finished = 0).
  eapply finish_preserves_cleanliness; [exact FINISH|exact PREPARED].
Qed.

End NativeHashBagGrowth.

Print Assumptions NativeHashBagGrowth.valid_counters_fix_the_resize_request.
Print Assumptions NativeHashBagGrowth.singleton_resize_selects_four_buckets.
Print Assumptions NativeHashBagGrowth.allocated_resize_selects_twice_the_original_buckets.
Print Assumptions NativeHashBagGrowth.valid_source_resize_has_the_exact_bucket_selection.
Print Assumptions NativeHashBagGrowth.doubling_an_allocated_table_has_room_for_one_more.
Print Assumptions NativeHashBagGrowth.valid_resize_selection_is_native_and_has_room.
Print Assumptions NativeHashBagGrowth.source_reserve_refines_raw.
Print Assumptions NativeHashBagGrowth.source_reserve_preserves_original_items.
Print Assumptions NativeHashBagGrowth.source_reserve_is_prebounded.
Print Assumptions NativeHashBagGrowth.completed_source_insert_retains_the_prospective_bounds.
Print Assumptions NativeHashBagGrowth.a_clean_exhausted_table_selects_resize_not_rehash.
Print Assumptions NativeHashBagGrowth.completed_source_insert_preserves_cleanliness.
