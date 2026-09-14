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

End NativeHashBagExtent.

Print Assumptions NativeHashBagExtent.large_native_capacity_counts_seven_eighths.
Print Assumptions NativeHashBagExtent.allocated_buckets_are_at_most_twice_their_full_capacity.
Print Assumptions NativeHashBagExtent.a_fresh_singleton_has_exact_counters_and_history.
