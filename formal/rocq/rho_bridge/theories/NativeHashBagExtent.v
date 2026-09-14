(** Bucket extent for the pinned native HashBag backing table.
    HashBag uses the standard HashMap and its trusted toolchain's
    hashbrown 0.17.1 implementation. In raw.rs, bucket_mask_to_capacity
    gives the full capacity below; capacity() instead returns items plus
    growth_left. Deleted control bytes can separate those two quantities.

    This scalar projection distinguishes the empty singleton from an empty
    allocated table. History records maximum observed capacity, not inserted
    entries or multiplicity. The initial arithmetic checkpoint does not
    establish mutation preservation, scan costs, or a preallocation budget.
    Native clone correspondence relies on the pinned Global allocator;
    arbitrary allocator behavior and panic unwinding are not claimed. *)
From Stdlib Require Import Arith.PeanoNat Lia.

Module NativeHashBagExtent.

Definition full_capacity (buckets : nat) : nat :=
  if buckets <=? 8 then buckets - 1 else (buckets / 8) * 7.

Inductive NativeBuckets : nat -> Prop :=
| EmptySingleton : NativeBuckets 1
| AllocatedBuckets : forall exponent, NativeBuckets (2 ^ (exponent + 2)).

Lemma large_native_capacity_counts_seven_eighths : forall groups,
  0 < groups -> full_capacity (16 * groups) = 14 * groups.
Proof.
  intros groups POSITIVE. unfold full_capacity.
  assert (LARGE : (16 * groups <=? 8) = false) by (apply Nat.leb_gt; lia).
  rewrite LARGE.
  replace (16 * groups) with ((2 * groups) * 8) by lia.
  rewrite Nat.div_mul by lia. lia.
Qed.

Theorem allocated_buckets_are_at_most_twice_their_full_capacity : forall exponent,
  2 ^ (exponent + 2) <= 2 * full_capacity (2 ^ (exponent + 2)).
Proof.
  intros [|[|exponent]]; [change (4 <= 6); lia|change (8 <= 14); lia|].
  assert (POWER : 2 ^ (S (S exponent) + 2) = 16 * 2 ^ exponent).
  { replace (S (S exponent) + 2) with (exponent + 4) by lia.
    rewrite Nat.pow_add_r. cbn [Nat.pow]. lia. }
  assert (POSITIVE : 0 < 2 ^ exponent).
  { pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)). lia. }
  rewrite POWER, large_native_capacity_counts_seven_eighths by exact POSITIVE.
  lia.
Qed.

(** All counters count native buckets, not HashBag occurrence multiplicity.
    The accounting identity includes tombstones; deleting a bucket need not
    return insertion growth credit. History is separate metadata. *)
Record TableState := {
  buckets : nat;
  items : nat;
  deleted : nat;
  growth_left : nat;
  history : nat
}.
Definition observed_capacity state := items state + growth_left state.
Definition valid_counters state :=
  NativeBuckets (buckets state) /\
  full_capacity (buckets state) = items state + deleted state + growth_left state.
Definition history_covers_full_capacity state :=
  full_capacity (buckets state) <= history state.
Definition fresh_table : TableState :=
  {| buckets := 1; items := 0; deleted := 0; growth_left := 0; history := 0 |}.

Theorem a_fresh_singleton_has_exact_counters_and_history :
  valid_counters fresh_table /\ history_covers_full_capacity fresh_table /\
  observed_capacity fresh_table = 0.
Proof. repeat split; try reflexivity; constructor. Qed.

(** These are scalar projections of successful native transitions, not a
    second table implementation. Optional reserve precedes final key lookup:
    resizing followed by Found is permitted. The unchanged reserve branch
    overapproximates skipped or unnecessary reservation. Chosen resize sizes
    retain native validity and room for one entry, but do not establish the
    allocation rounding algorithm or any pre-action resource budget.
    Only the wrapper's later observation updates history. *)
Definition replace_counters state new_items new_deleted new_growth :=
  {| buckets := buckets state; items := new_items; deleted := new_deleted;
     growth_left := new_growth; history := history state |}.
Definition clean_table state new_buckets :=
  {| buckets := new_buckets; items := items state; deleted := 0;
     growth_left := full_capacity new_buckets - items state;
     history := history state |}.

Inductive RawReserve : TableState -> TableState -> Prop :=
| ReserveUnchanged : forall state, RawReserve state state
| ReserveRehash : forall state,
    growth_left state = 0 ->
    S (items state) <= full_capacity (buckets state) / 2 ->
    RawReserve state (clean_table state (buckets state))
| ReserveResize : forall state new_buckets,
    growth_left state = 0 ->
    full_capacity (buckets state) / 2 < S (items state) ->
    NativeBuckets new_buckets -> S (items state) <= full_capacity new_buckets ->
    RawReserve state (clean_table state new_buckets).

Inductive RawFinish : TableState -> TableState -> Prop :=
| FinishFound : forall state, RawFinish state state
| FinishEmpty : forall state, 0 < growth_left state ->
    RawFinish state (replace_counters state (S (items state))
      (deleted state) (growth_left state - 1))
| FinishDeleted : forall state, 0 < deleted state ->
    RawFinish state (replace_counters state (S (items state))
      (deleted state - 1) (growth_left state)).

(** EraseDeleted's size guard records the pinned SSE2 control-group width:
    smaller tables cannot create tombstones. Both erase cases consume a FULL
    bucket; only marking EMPTY restores growth credit. *)
Inductive RawErase : TableState -> TableState -> Prop :=
| EraseEmpty : forall state, 0 < items state ->
    RawErase state (replace_counters state (items state - 1)
      (deleted state) (S (growth_left state)))
| EraseDeleted : forall state, 0 < items state -> 16 <= buckets state ->
    RawErase state (replace_counters state (items state - 1)
      (S (deleted state)) (growth_left state)).

Theorem raw_reserve_preserves_counters_and_history : forall before after,
  RawReserve before after -> valid_counters before ->
  valid_counters after /\ history after = history before.
Proof.
  intros before after STEP [NATIVE BALANCE]. destruct STEP;
    unfold valid_counters, clean_table; cbn; repeat split; try assumption;
    try reflexivity; lia.
Qed.

Theorem raw_finish_preserves_counters_and_history : forall before after,
  RawFinish before after -> valid_counters before ->
  valid_counters after /\ history after = history before.
Proof.
  intros before after STEP [NATIVE BALANCE]. destruct STEP;
    unfold valid_counters, replace_counters; cbn; repeat split;
    try assumption; try reflexivity; lia.
Qed.

Theorem raw_erase_preserves_counters_and_history : forall before after,
  RawErase before after -> valid_counters before ->
  valid_counters after /\ history after = history before.
Proof.
  intros before after STEP [NATIVE BALANCE]. destruct STEP;
    unfold valid_counters, replace_counters; cbn; repeat split;
    try assumption; try reflexivity; lia.
Qed.

End NativeHashBagExtent.

Print Assumptions NativeHashBagExtent.large_native_capacity_counts_seven_eighths.
Print Assumptions NativeHashBagExtent.allocated_buckets_are_at_most_twice_their_full_capacity.
Print Assumptions NativeHashBagExtent.a_fresh_singleton_has_exact_counters_and_history.
Print Assumptions NativeHashBagExtent.raw_reserve_preserves_counters_and_history.
Print Assumptions NativeHashBagExtent.raw_finish_preserves_counters_and_history.
Print Assumptions NativeHashBagExtent.raw_erase_preserves_counters_and_history.
