(** Group-control prefixes of the pinned hashbrown 0.17.1/SSE2 probe.
    raw.rs:2008 find_inner continues only without EMPTY; raw.rs:1790
    find_or_find_insert_index_inner first fills its absent insertion cache,
    then stops when that cache is present and the group contains EMPTY.
    raw.rs:1950 find_insert_index continues only without an insertion lane.

    ReachedGroup is an unbounded mathematical Nat shadow of those guards
    and raw.rs:82's increment, addition and mask. Its constructors contain
    no step limit, fuel or machine-overflow assumption. Candidate bodies
    are overapproximated: omitting their early successful-equality returns
    enlarges possible GROUP prefixes. This does not bound callback work or
    prove callback termination. The cache update is the actual post-fill
    update; unused caches in Lookup and InsertOnly remain harmless ghosts.

    An immutable original EMPTY witness and the existing whole-window
    coverage theorem derive a barrier. Only AFTER deriving that barrier
    do the layout laws justify plain usize additions. Source association
    must still bind physical tags, readable controls, mode and initial
    masked position to the same native table and the audited intrinsics.
    No loop-body replacement, compiler proof or runtime executor is added.
    Small-table fix_insert_index repair and cache-origin validity remain
    separate obligations; the group bounds below exclude that extra load. *)
From Stdlib Require Import Arith.PeanoNat Bool.Bool ZArith.BinInt ZArith.Znat Lia.
From RhoBridge Require Import NativeHashBagProbeSequence NativeHashBagProbeWindows
  NativeHashBagProbeCoverage NativeHashBagProbeMasks NativeHashBagLayout.
Open Scope nat_scope.

Module NativeHashBagProbeControl.
Import NativeHashBagProbeSequence.NativeHashBagProbeSequence.
Import NativeHashBagProbeWindows.NativeHashBagProbeWindows.
Import NativeHashBagProbeCoverage.NativeHashBagProbeCoverage.
Import NativeHashBagProbeMasks.NativeHashBagProbeMasks.
Import NativeHashBagLayout.NativeHashBagLayout.

Inductive ProbeMode := Lookup | Combined | InsertOnly.

Definition contains_empty physical position :=
  any_mask (tag_match physical position 255).

Definition cache_after mode bucket_count position physical cached :=
  match mode with
  | Combined => fill_absent_cache bucket_count position physical cached
  | _ => cached
  end.

Definition continue_group mode bucket_count position physical cached : Prop :=
  match mode with
  | Lookup => contains_empty physical position = false
  | Combined =>
      match fill_absent_cache bucket_count position physical cached with
      | None => True
      | Some _ => contains_empty physical position = false
      end
  | InsertOnly => insertion_slot bucket_count position physical = None
  end.

Inductive ReachedGroup (mode : ProbeMode) (bucket_count initial : nat)
    (physical : nat -> nat) : nat -> nat -> nat -> option nat -> Prop :=
| ReachedInitial : ReachedGroup mode bucket_count initial physical 0 initial 0 None
| ReachedAdvance : forall step position stride cached,
    ReachedGroup mode bucket_count initial physical step position stride cached ->
    continue_group mode bucket_count position physical cached ->
    ReachedGroup mode bucket_count initial physical (S step)
      (Nat.land (position + (stride + 16)) (bucket_count - 1)) (stride + 16)
      (cache_after mode bucket_count position physical cached).

Lemma opposite_boolean_observations_are_impossible : forall observed,
  observed = true -> observed = false -> False.
Proof. intros [] YES NO; discriminate. Qed.

Lemma a_filled_cache_and_empty_group_cannot_continue :
  forall (cached : option nat) empty,
  (exists index, cached = Some index) -> empty = true ->
  (match cached with None => True | Some _ => empty = false end) -> False.
Proof.
  intros cached empty [index CACHE] EMPTY CONTINUE. rewrite CACHE in CONTINUE.
  exact (opposite_boolean_observations_are_impossible empty EMPTY CONTINUE).
Qed.

Lemma a_present_option_cannot_be_absent : forall (cached : option nat),
  (exists index, cached = Some index) -> cached = None -> False.
Proof. intros cached [index PRESENT] ABSENT. rewrite ABSENT in PRESENT. discriminate. Qed.

Lemma filling_an_absent_cache_is_the_original_insertion_slot :
  forall bucket_count position physical,
  fill_absent_cache bucket_count position physical None =
    insertion_slot bucket_count position physical.
Proof. reflexivity. Qed.

Theorem an_empty_group_forbids_every_mode_from_advancing :
  forall mode bucket_count position physical cached,
  contains_empty physical position = true ->
  ~ continue_group mode bucket_count position physical cached.
Proof.
  intros mode bucket_count position physical cached EMPTY CONTINUE.
  destruct mode.
  - exact (opposite_boolean_observations_are_impossible
      (contains_empty physical position) EMPTY CONTINUE).
  - exact (a_filled_cache_and_empty_group_cannot_continue
      (fill_absent_cache bucket_count position physical cached)
      (contains_empty physical position)
      (an_empty_lane_enables_the_combined_insertion_cache
        bucket_count position physical cached EMPTY) EMPTY CONTINUE).
  - exact (a_present_option_cannot_be_absent
      (fill_absent_cache bucket_count position physical None)
      (an_empty_lane_enables_the_combined_insertion_cache
        bucket_count position physical None EMPTY)
      (eq_trans (filling_an_absent_cache_is_the_original_insertion_slot
        bucket_count position physical) CONTINUE)).
Qed.

Lemma power_buckets_have_the_native_mask_shape : forall exponent,
  power_bucket_count exponent = 2 ^ (exponent + 4).
Proof.
  intro exponent.
  assert (GROUPS : power_group_count exponent = 2 ^ exponent).
  { apply Nat2Z.inj. rewrite group_count_returns_the_original_integer,
      Nat2Z.inj_pow. reflexivity. }
  unfold power_bucket_count. rewrite GROUPS, Nat.pow_add_r. cbn. nia.
Qed.

Lemma masking_power_buckets_is_modulo : forall exponent value,
  Nat.land value (power_bucket_count exponent - 1) =
    value mod power_bucket_count exponent.
Proof.
  intros exponent value. rewrite power_buckets_have_the_native_mask_shape.
  apply native_power_of_two_mask_is_modulo.
Qed.

Lemma mathematical_start_returns_the_original_integer : forall exponent initial step,
  Z.of_nat (mathematical_start exponent initial step) =
    source_probe_position (Z.of_nat (power_bucket_count exponent)) (Z.of_nat initial) step.
Proof.
  intros exponent initial step. unfold mathematical_start. rewrite Z2Nat.id; [reflexivity|].
  unfold source_probe_position.
  pose proof (power_bucket_count_is_positive exponent) as POSITIVE.
  exact (proj1 (Z.mod_pos_bound _ (Z.of_nat (power_bucket_count exponent)) ltac:(lia))).
Qed.

Lemma the_initial_mathematical_start_is_the_original_position : forall exponent initial,
  initial < power_bucket_count exponent -> mathematical_start exponent initial 0 = initial.
Proof.
  intros exponent initial INITIAL. unfold mathematical_start, source_probe_position.
  cbn [triangle]. rewrite Z.mul_0_r, Z.add_0_r, Z.mod_small by lia.
  apply Nat2Z.id.
Qed.

Lemma mathematical_starts_follow_the_literal_nat_masked_step : forall exponent initial step,
  mathematical_start exponent initial (S step) =
    Nat.land (mathematical_start exponent initial step + 16 * S step)
      (power_bucket_count exponent - 1).
Proof.
  intros exponent initial step. rewrite masking_power_buckets_is_modulo.
  apply Nat2Z.inj. rewrite Nat2Z.inj_mod, Nat2Z.inj_add, Nat2Z.inj_mul,
    !mathematical_start_returns_the_original_integer.
  apply source_probe_position_follows_the_incremented_stride.
  pose proof (power_bucket_count_is_positive exponent). lia.
Qed.

(** This equality is solely about the unbounded Nat shadow. No machine
    execution correspondence is inferred until the later layout corollary. *)
Theorem every_reached_group_has_its_original_mathematical_position_and_stride :
  forall mode exponent initial physical step position stride cached,
  initial < power_bucket_count exponent ->
  ReachedGroup mode (power_bucket_count exponent) initial physical
    step position stride cached ->
  position = mathematical_start exponent initial step /\ stride = 16 * step.
Proof.
  intros mode exponent initial physical step position stride cached INITIAL REACHED.
  induction REACHED as [|step position stride cached REACHED IH CONTINUE].
  - split; [symmetry; apply the_initial_mathematical_start_is_the_original_position|];
      assumption || reflexivity.
  - destruct IH as [POSITION STRIDE]. split.
    + rewrite POSITION, STRIDE, mathematical_starts_follow_the_literal_nat_masked_step.
      replace (16 * step + 16) with (16 * S step) by lia. reflexivity.
    + lia.
Qed.

Theorem a_physical_empty_barrier_bounds_every_reached_group :
  forall mode exponent initial physical barrier step position stride cached,
  initial < power_bucket_count exponent ->
  contains_empty physical (mathematical_start exponent initial barrier) = true ->
  ReachedGroup mode (power_bucket_count exponent) initial physical
    step position stride cached -> step <= barrier.
Proof.
  intros mode exponent initial physical barrier step position stride cached INITIAL EMPTY REACHED.
  induction REACHED as [|step position stride cached REACHED IH CONTINUE]; [lia|].
  assert (NOT_BARRIER : step <> barrier).
  { intro SAME. destruct (every_reached_group_has_its_original_mathematical_position_and_stride
      _ _ _ _ _ _ _ _ INITIAL REACHED) as [POSITION _].
    subst step. rewrite <- POSITION in EMPTY.
    exact (an_empty_group_forbids_every_mode_from_advancing
      _ _ _ _ _ EMPTY CONTINUE). }
  lia.
Qed.

Theorem an_original_empty_witness_bounds_group_visits_and_moves :
  forall mode exponent initial original_empty physical index step position stride cached,
  initial < power_bucket_count exponent -> index < power_bucket_count exponent ->
  original_empty index = true ->
  physical_predicate_projects (power_bucket_count exponent) original_empty true
    (fun offset => Nat.eqb (physical offset) 255) ->
  ReachedGroup mode (power_bucket_count exponent) initial physical
    step position stride cached ->
  S step <= power_group_count exponent /\ step <= power_group_count exponent - 1 /\
    position < power_bucket_count exponent /\ stride < power_bucket_count exponent.
Proof.
  intros mode exponent initial original_empty physical index step position stride cached
    INITIAL INDEX EMPTY PROJECT REACHED.
  destruct (an_original_empty_witness_has_a_physical_lane_in_the_mathematical_cycle
    exponent initial original_empty (fun offset => Nat.eqb (physical offset) 255)
    index INITIAL INDEX EMPTY PROJECT) as [barrier [lane [BARRIER [LANE MATCH]]]].
  assert (STOP : contains_empty physical (mathematical_start exponent initial barrier) = true).
  { apply native_any_bit_set_iff_a_matching_lane. exists lane. split; assumption. }
  pose proof (a_physical_empty_barrier_bounds_every_reached_group
    _ _ _ _ _ _ _ _ _ INITIAL STOP REACHED) as BOUND.
  destruct (every_reached_group_has_its_original_mathematical_position_and_stride
    _ _ _ _ _ _ _ _ INITIAL REACHED) as [POSITION STRIDE].
  pose proof (every_mathematical_start_is_within_its_table exponent initial step) as INSIDE.
  unfold power_bucket_count in *. repeat split; lia.
Qed.

(** Accepted native layout plus the DERIVED prefix bounds validate the
    debug stride guard and both plain additions before masking. The actual
    machine/body projection must use these guards at each reached step;
    its safety is not a premise of ReachedGroup. *)
Theorem derived_group_bounds_validate_plain_usize_probe_additions :
  forall mode exponent initial original_empty physical index step position stride cached
    signed_limit word_limit alignment_exponent words bucket_exponent,
  initial < power_bucket_count exponent -> index < power_bucket_count exponent ->
  original_empty index = true ->
  physical_predicate_projects (power_bucket_count exponent) original_empty true
    (fun offset => Nat.eqb (physical offset) 255) ->
  ReachedGroup mode (power_bucket_count exponent) initial physical
    step position stride cached ->
  power_bucket_count exponent = allocated_buckets bucket_exponent ->
  accepted_layout signed_limit alignment_exponent words bucket_exponent ->
  signed_limit <= word_limit ->
  stride <= power_bucket_count exponent - 1 /\
    stride + 16 <= word_limit /\ position + (stride + 16) <= word_limit.
Proof.
  intros mode exponent initial original_empty physical index step position stride cached
    signed_limit word_limit alignment_exponent words bucket_exponent
    INITIAL INDEX EMPTY PROJECT REACHED BUCKETS ACCEPTED WORD.
  destruct (an_original_empty_witness_bounds_group_visits_and_moves
    _ _ _ _ _ _ _ _ _ _ INITIAL INDEX EMPTY PROJECT REACHED)
    as [_ [_ [POSITION STRIDE]]].
  split; [lia|]. eapply reached_probe_step_additions_fit_before_masking;
    [exact ACCEPTED|exact WORD|rewrite <- BUCKETS; exact POSITION|rewrite <- BUCKETS; exact STRIDE].
Qed.

Theorem an_initial_empty_group_never_advances :
  forall mode bucket_count initial physical step position stride cached,
  contains_empty physical initial = true ->
  ReachedGroup mode bucket_count initial physical step position stride cached ->
  step = 0 /\ position = initial /\ stride = 0 /\ cached = None.
Proof.
  intros mode bucket_count initial physical step position stride cached EMPTY REACHED.
  induction REACHED as [|step position stride cached REACHED IH CONTINUE].
  - repeat split; reflexivity.
  - destruct IH as [_ [POSITION _]]. subst position. exfalso.
    exact (an_empty_group_forbids_every_mode_from_advancing _ _ _ _ _ EMPTY CONTINUE).
Qed.

Theorem allocated_small_table_group_search_never_advances :
  forall mode bucket_count initial original physical step position stride cached,
  (bucket_count = 4 \/ bucket_count = 8) -> initial < bucket_count ->
  physical_tags_project bucket_count original physical ->
  ReachedGroup mode bucket_count initial physical step position stride cached -> step = 0.
Proof.
  intros mode bucket_count initial original physical step position stride cached
    SMALL INITIAL PROJECT REACHED.
  assert (EMPTY : contains_empty physical initial = true).
  { apply native_any_bit_set_iff_a_matching_lane.
    exists (bucket_count - initial). split; [lia|]. unfold tag_match.
    replace (initial + (bucket_count - initial)) with bucket_count by lia.
    rewrite PROJECT by lia. rewrite allocated_small_padding_lane by lia. reflexivity. }
  exact (proj1 (an_initial_empty_group_never_advances _ _ _ _ _ _ _ _ EMPTY REACHED)).
Qed.

Theorem a_static_empty_singleton_group_never_advances :
  forall mode physical step position stride cached,
  (forall lane, lane < 16 -> physical lane = 255) ->
  ReachedGroup mode 1 0 physical step position stride cached -> step = 0.
Proof.
  intros mode physical step position stride cached STATIC REACHED.
  assert (EMPTY : contains_empty physical 0 = true).
  { apply native_any_bit_set_iff_a_matching_lane. exists 0. split; [lia|].
    unfold tag_match. rewrite STATIC by lia. reflexivity. }
  exact (proj1 (an_initial_empty_group_never_advances _ _ _ _ _ _ _ _ EMPTY REACHED)).
Qed.

End NativeHashBagProbeControl.

Print Assumptions NativeHashBagProbeControl.an_empty_group_forbids_every_mode_from_advancing.
Print Assumptions NativeHashBagProbeControl.every_reached_group_has_its_original_mathematical_position_and_stride.
Print Assumptions NativeHashBagProbeControl.a_physical_empty_barrier_bounds_every_reached_group.
Print Assumptions NativeHashBagProbeControl.an_original_empty_witness_bounds_group_visits_and_moves.
Print Assumptions NativeHashBagProbeControl.derived_group_bounds_validate_plain_usize_probe_additions.
Print Assumptions NativeHashBagProbeControl.an_initial_empty_group_never_advances.
Print Assumptions NativeHashBagProbeControl.allocated_small_table_group_search_never_advances.
Print Assumptions NativeHashBagProbeControl.a_static_empty_singleton_group_never_advances.
