(** Required HashBag reconstruction in the existing checked binding worker.

    The source width is counts.len(), not total_count, the sum of surviving
    counts, or allocation capacity. Each stored key owns one output occurrence,
    including a zero-count key. Binding retains the first equal key object,
    the last supplied count and the original total. Clone here means GENERATED
    container reconstruction through insert_n, not HashBag's derived Clone:
    positive counts accumulate and zero-count incoming keys are discarded.

    OrderedBindingReconstruction supplies the keyed insertion and ownership
    partition laws. The lists below witness source order and key retention;
    they do not prescribe a new lookup loop or a HashMap implementation.
    Occurrence tags are independent of equality identities and no uniqueness
    premise is needed to conserve their multiplicities.

    The local cleanup shape follows iterative_drop.rs: mem::take constructs
    the EMPTY_CONTAINER default (one NativeWork and one NativeRecord), a
    consuming iterator has three boundary work events and one record, each
    stored key advances once and is pushed once, and the empty replacement
    has one field-glue work event. These are the same local events already
    proved for RequiredVecBindingReservation. Child cleanup is paid separately.

    Insertion, growth, key hashing/equality/comparison and summary rebuilding
    have NO numeric costs here. The native trace-cover premise must describe
    their real generated/native execution, including structural descendants,
    payloads, retained-key rehashing and comparison scratch. A cached HashBag
    hash is not a bound for arbitrary category Hash or for category Eq.
    Provider inspection and its own scratch need admission too. Trace-cover
    and source/operation correspondence remain concrete provider obligations.

    Slot readiness, Rust ownership moves, source lifetime, checked machine-word
    arithmetic and admission before each action remain emitter obligations.
    This is conditional normal-error accounting, not complete checked Rholang
    activation, panic/TLS recovery, allocator capacity or physical memory. *)
From Stdlib Require Import List Arith Bool Lia Sorting.Permutation.
From RhoBridge Require Import HashBagBindingReconstruction
  OrderedBindingReconstruction GeneratedDummyCleanupReservation
  GeneratedBindingOutputReservation IndexedCopySlots
  RequiredVecBindingReservation RholangInitialGraphResources.
Import ListNotations.

Module RequiredHashBagBindingReservation.
Module B := HashBagBindingReconstruction.
Module M := OrderedBindingReconstruction.
Module D := GeneratedDummyCleanupReservation.
Module O := GeneratedBindingOutputReservation.
Module I := IndexedCopySlots.
Module V := RequiredVecBindingReservation.

Inductive Mode := CloneEntries | BindingEntries.

Section Entries.
Context {Payload : Type}.
Definition Key := @B.Key Payload.
Definition Entry := (Key * nat)%type.

(** This lookup states insert_n's count result; it does not introduce an
    executable pre-insertion lookup or charge one as a constant-time action. *)
Definition accumulated_count (incoming : Entry) (entries : list Entry) : nat :=
  snd incoming +
  match M.lookup (B.identity (fst incoming)) entries with
  | Some old => old
  | None => 0
  end.

Definition insert (mode : Mode) (incoming : Entry) (entries : list Entry)
    : list Entry :=
  match mode with
  | BindingEntries => M.insert_map incoming entries
  | CloneEntries =>
      match snd incoming with
      | 0 => entries
      | S _ => M.insert_map (fst incoming, accumulated_count incoming entries) entries
      end
  end.

Definition rebuild (mode : Mode) (entries : list Entry) : list Entry :=
  fold_left (fun acc incoming => insert mode incoming acc) entries [].

Theorem binding_insert_is_existing : forall incoming entries,
  insert BindingEntries incoming entries = B.insert_entry incoming entries.
Proof. intros. apply M.nat_insert_reuses_bag. Qed.

Lemma binding_fold_is_existing : forall entries acc,
  fold_left (fun acc incoming => insert BindingEntries incoming acc) entries acc =
  fold_left B.insert_step entries acc.
Proof.
  induction entries as [|entry rest IH]; intro acc.
  - reflexivity.
  - cbn [fold_left]. rewrite binding_insert_is_existing.
    apply IH.
Qed.

Theorem binding_rebuild_is_existing : forall entries,
  rebuild BindingEntries entries = B.rebuild_entries entries.
Proof. intro entries. apply binding_fold_is_existing. Qed.

Theorem binding_transform_refines_existing : forall transform entries,
  rebuild BindingEntries (map (B.transform_entry transform) entries) =
  B.existing_binding_entries transform entries.
Proof.
  intros. rewrite binding_rebuild_is_existing.
  unfold B.rebuild_entries, B.existing_binding_entries.
  apply B.transformation_insertion_fusion.
Qed.

Theorem binding_bag_refines_existing : forall Summary
    (summary : list Entry -> Summary) transform total entries,
  B.from_binding_entries summary total (map (B.transform_entry transform) entries) =
  B.existing_binding_recipe summary transform total entries.
Proof. intros. apply B.pretransformed_helper_equals_existing_recipe. Qed.

Theorem binding_retains_source_total : forall Summary
    (summary : list Entry -> Summary) total entries,
  B.retained_total (B.from_binding_entries summary total entries) = total.
Proof. reflexivity. Qed.

Theorem binding_collision_keeps_first_key_last_count :
  forall first last earlier later,
  B.identity first = B.identity last ->
  rebuild BindingEntries [(first, earlier); (last, later)] = [(first, later)].
Proof.
  intros first last earlier later H.
  change (M.rebuild [(first, earlier); (last, later)] = [(first, later)]).
  apply M.collision_retains_first_key_and_last_value. exact H.
Qed.

Theorem clone_zero_discards_incoming : forall key entries,
  insert CloneEntries (key, 0) entries = entries.
Proof. reflexivity. Qed.

Theorem binding_zero_retains_an_owned_key : forall key,
  insert BindingEntries (key, 0) [] = [(key, 0)].
Proof. reflexivity. Qed.

Theorem clone_positive_collision_accumulates : forall first incoming old count,
  B.identity incoming = B.identity first ->
  insert CloneEntries (incoming, S count) [(first, old)] =
  [(first, old + S count)].
Proof.
  intros first incoming old count H.
  unfold insert, accumulated_count.
  cbn [fst snd M.lookup M.insert_map M.key_id].
  unfold M.key_id. rewrite H, Nat.eqb_refl.
  now rewrite Nat.add_comm.
Qed.

Theorem insert_width : forall mode incoming entries,
  length (insert mode incoming entries) <= S (length entries).
Proof.
  intros mode [key count] entries. destruct mode.
  - destruct count; cbn [insert snd fst]; [lia|apply M.insert_map_width].
  - apply M.insert_map_width.
Qed.

Lemma fold_width : forall mode entries acc,
  length (fold_left (fun acc incoming => insert mode incoming acc) entries acc)
  <= length acc + length entries.
Proof.
  intros mode entries. induction entries as [|entry rest IH]; intro acc.
  - cbn. lia.
  - cbn [fold_left]. specialize (IH (insert mode entry acc)).
    pose proof (insert_width mode entry acc). cbn [length]. lia.
Qed.

Theorem rebuild_width : forall mode entries,
  length (rebuild mode entries) <= length entries.
Proof.
  intros mode entries. exact (fold_width mode entries []).
Qed.

Theorem rebuilt_prefix_fits_source_width : forall mode supplied done pending,
  done ++ pending = supplied ->
  length (rebuild mode done) <= length supplied.
Proof.
  intros mode supplied done pending H. subst supplied.
  pose proof (rebuild_width mode done). rewrite length_app. lia.
Qed.

Section Ownership.
Variable owner : Key -> nat.
Definition key_owners (key : Key) := [owner key].
Definition owners (entries : list Entry) : list nat :=
  M.owners key_owners (fun _ : nat => []) entries.

Lemma owners_cons : forall key count rest,
  owners ((key, count) :: rest) = owner key :: owners rest.
Proof. reflexivity. Qed.

Theorem stored_width_is_owned_occurrence_count : forall entries,
  length (owners entries) = length entries.
Proof.
  induction entries as [|[key count] rest IH]; [reflexivity|].
  rewrite owners_cons. cbn [length]. now rewrite IH.
Qed.

Theorem count_changes_preserve_owned_inventory : forall key first second rest,
  owners ((key, first) :: rest) = owners ((key, second) :: rest).
Proof. reflexivity. Qed.

Lemma map_insert_owner_partition : forall key count entries,
  exists discarded,
  Permutation (owner key :: owners entries)
    (owners (M.insert_map (key, count) entries) ++ discarded).
Proof.
  intros key count entries.
  exact (@M.insert_owner_partition Payload nat key_owners (fun _ => [])
    (key, count) entries).
Qed.

Theorem insert_owner_partition : forall mode key count entries,
  exists discarded,
  Permutation (owner key :: owners entries)
    (owners (insert mode (key, count) entries) ++ discarded).
Proof.
  intros mode key count entries. destruct mode.
  - destruct count.
    + exists [owner key]. cbn [insert snd].
      apply Permutation_cons_append.
    + apply map_insert_owner_partition.
  - apply map_insert_owner_partition.
Qed.

Lemma fold_owner_partition : forall mode entries acc,
  exists discarded,
  Permutation (owners acc ++ owners entries)
    (owners (fold_left (fun acc incoming => insert mode incoming acc) entries acc)
      ++ discarded).
Proof.
  intros mode entries. induction entries as [|[key count] rest IH]; intro acc.
  - exists []. cbn [fold_left]. change (Permutation (owners acc ++ [])
      (owners acc ++ [])). reflexivity.
  - destruct (insert_owner_partition mode key count acc) as [first HP].
    destruct (IH (insert mode (key, count) acc)) as [later HQ].
    exists (first ++ later).
    apply (proj2 (Permutation_count_occ Nat.eq_dec _ _)). intro tag.
    pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) HP tag) as H.
    pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) HQ tag) as J.
    cbn [fold_left]. rewrite owners_cons.
    repeat rewrite count_occ_app in *. cbn [count_occ] in *.
    destruct (Nat.eq_dec (owner key) tag); lia.
Qed.

Theorem rebuild_owner_partition : forall mode entries,
  exists discarded,
  Permutation (owners entries) (owners (rebuild mode entries) ++ discarded).
Proof.
  intros mode entries. exact (fold_owner_partition mode entries []).
Qed.

(** The prefix may already have discarded equal or zero-count keys. Pending
    occurrences stay in source-order result slots or already-paid locals. *)
Theorem prefix_owner_partition : forall mode supplied done pending,
  done ++ pending = supplied ->
  exists discarded,
  Permutation (owners supplied)
    (owners (rebuild mode done) ++ discarded ++ owners pending).
Proof.
  intros mode supplied done pending H. subst supplied.
  destruct (rebuild_owner_partition mode done) as [discarded HP].
  exists discarded. unfold owners, M.owners at 1.
  rewrite flat_map_app.
  change (Permutation (owners done ++ owners pending)
    (owners (rebuild mode done) ++ discarded ++ owners pending)).
  rewrite app_assoc. now apply Permutation_app_tail.
Qed.

End Ownership.

(** Nat equations for Clone's checked running-total guard. Binding must not
    replace its transported source total by this sum. The emitter implements
    the proved additions using checked machine-word arithmetic. *)
Definition count_sum (entries : list Entry) : nat :=
  fold_right (fun entry rest => snd entry + rest) 0 entries.

Lemma accumulating_map_insert_count_sum : forall incoming entries,
  count_sum (M.insert_map
    (fst incoming, accumulated_count incoming entries) entries) =
  count_sum entries + snd incoming.
Proof.
  intros [key count] entries. induction entries as [|[stored old] rest IH].
  - change (count + 0 + 0 = 0 + count). lia.
  - unfold accumulated_count at 1.
    cbn [fst snd M.lookup M.insert_map]. unfold M.key_id.
    destruct (Nat.eqb (B.identity key) (B.identity stored)).
    + change (count + old + count_sum rest = old + count_sum rest + count). lia.
    + change (old + count_sum
        (M.insert_map (key, accumulated_count (key, count) rest) rest) =
        old + count_sum rest + count).
      cbn [fst snd] in IH. rewrite IH. lia.
Qed.

Theorem clone_insert_count_sum : forall incoming entries,
  count_sum (insert CloneEntries incoming entries) =
  count_sum entries + snd incoming.
Proof.
  intros [key count] entries. destruct count.
  - cbn [insert snd]. lia.
  - apply accumulating_map_insert_count_sum.
Qed.

Theorem clone_fold_count_sum : forall entries acc,
  count_sum
    (fold_left (fun acc incoming => insert CloneEntries incoming acc) entries acc) =
  count_sum acc + count_sum entries.
Proof.
  induction entries as [|entry rest IH]; intro acc.
  - change (count_sum acc = count_sum acc + 0). lia.
  - cbn [fold_left]. rewrite IH, clone_insert_count_sum.
    change (count_sum acc + snd entry + count_sum rest =
      count_sum acc + (snd entry + count_sum rest)). lia.
Qed.

Theorem clone_rebuild_count_sum : forall entries,
  count_sum (rebuild CloneEntries entries) = count_sum entries.
Proof. intro entries. exact (clone_fold_count_sum entries []). Qed.

Lemma lookup_count_le_sum : forall wanted entries old,
  M.lookup wanted entries = Some old -> old <= count_sum entries.
Proof.
  intros wanted entries. induction entries as [|[key count] rest IH]; intros old H.
  - discriminate.
  - cbn [M.lookup] in H.
    destruct (Nat.eqb wanted (M.key_id key)) eqn:HE.
    + inversion H; subst. change (old <= old + count_sum rest). lia.
    + specialize (IH old H). change (old <= count + count_sum rest). lia.
Qed.

Theorem clone_accumulator_lookup_is_bounded : forall supplied wanted old,
  M.lookup wanted (rebuild CloneEntries supplied) = Some old ->
  old <= count_sum supplied.
Proof.
  intros supplied wanted old H. apply lookup_count_le_sum in H.
  now rewrite clone_rebuild_count_sum in H.
Qed.

Theorem count_sum_app : forall done pending,
  count_sum (done ++ pending) = count_sum done + count_sum pending.
Proof.
  induction done as [|entry rest IH]; intro pending.
  - reflexivity.
  - change (snd entry + count_sum (rest ++ pending) =
      (snd entry + count_sum rest) + count_sum pending).
    rewrite IH. lia.
Qed.

Theorem clone_prefix_total_advances : forall done key count,
  count_sum (done ++ [(key, count)]) = count_sum done + count.
Proof.
  intros. rewrite count_sum_app.
  change (count_sum done + (count + 0) = count_sum done + count). lia.
Qed.

End Entries.

Theorem clone_running_total_guard_covers_occupied_addition :
  forall old running incoming ceiling,
  old <= running -> running + incoming <= ceiling ->
  old + incoming <= ceiling.
Proof. intros. lia. Qed.

(** The same local empty-default/consuming-iterator recipe has already been
    projected for Vec. Only CLEANUP is reused, never Vec insertion costs. *)
Definition bag_cleanup := V.vec_cleanup.

Theorem bag_cleanup_projection : forall width,
  D.weighted D.base_work_weight (bag_cleanup width) = 6 + 2 * width /\
  D.weighted D.record_weight (bag_cleanup width) = 2 + width /\
  D.weighted D.byte_weight (bag_cleanup width) = 0.
Proof. apply V.vec_cleanup_projection. Qed.

Theorem partial_bag_flat_cleanup_is_covered : forall retained width,
  retained <= width ->
  1 + retained <= D.weighted D.base_work_weight (bag_cleanup width).
Proof. apply V.partial_vec_flat_cleanup_is_covered. Qed.

Theorem prepared_slots_return_source_sequence :
  forall A prefix expected (supplied : list A) suffix,
  I.take_many (length supplied) (length prefix) expected
    (prefix ++ map (fun value => Some (expected, value)) supplied ++ suffix) =
  Some (supplied, prefix ++ repeat None (length supplied) ++ suffix).
Proof. intros. apply I.prepared_range_ready. Qed.

Section Cleanup.
Variable receipt : nat -> O.OutputReceipt.

Theorem occurrence_partition_transfers_output_credits :
  forall original retained discarded,
  Permutation original (retained ++ discarded) -> forall event,
  O.sum_counts O.output_credit (map receipt original) event =
  O.sum_counts O.output_credit (map receipt retained) event +
  O.sum_counts O.output_credit (map receipt discarded) event.
Proof.
  intros original retained discarded HP event.
  apply O.retained_and_discarded_credits_partition.
  rewrite <- map_app. now apply Permutation_map.
Qed.

(** Retained, already-discarded, and still-pending roots each spend their own
    existing allowance once. The flat container allowance is independent. *)
Theorem partitioned_partial_root_cleanup_is_covered :
  forall original retained discarded pending event,
  Permutation original (retained ++ discarded ++ pending) ->
  Forall O.bounded (map receipt original) ->
  O.sum_counts O.output_root (map receipt retained) event +
    O.sum_counts O.output_root (map receipt discarded) event +
    O.sum_counts O.output_root (map receipt pending) event <=
  O.sum_counts O.output_credit (map receipt original) event.
Proof.
  intros original retained discarded pending event HP HB.
  pose proof (O.independently_disposed_partial_roots_are_covered
    (map receipt original) HB event) as HC.
  assert (HM : Permutation (map receipt original)
    (map receipt retained ++ map receipt discarded ++ map receipt pending)).
  { rewrite <- !map_app. now apply Permutation_map. }
  rewrite (O.sum_counts_permutation O.OutputReceipt O.output_root _ _ HM event)
    in HC.
  rewrite !O.sum_counts_app in HC. lia.
Qed.

End Cleanup.

Section NativeOperations.
Context {NativeOperation : Type}.

(** A supplied trace EXPANDS the real operation into its accounted events;
    a Hash/Eq call is not represented by a single unit-work event. Native
    table actions, any growth rehashes, key descendants and scratch are in
    the trace or separately admitted by the provider. Operation identity
    must distinguish Start, Insert and FinalBindingSummary stages and include
    the relevant mode, incoming key, retained state and count. The same budget
    callback can admit each stage independently; a one-stage list below is
    its local action, and list composition adds already-covered stage traces.
    These parameters provide no generated Proc/Bag implementation by fiat. *)
Variable actual_trace : NativeOperation -> list D.Event.
Variable admitted_native : NativeOperation -> D.Counts.
Definition native_counts operation : D.Counts :=
  O.sum_counts D.atom (actual_trace operation).
Definition native_trace_cover operation : Prop :=
  forall event, native_counts operation event <= admitted_native operation event.

Theorem native_trace_list_is_covered : forall operations,
  Forall native_trace_cover operations -> forall event,
  O.sum_counts native_counts operations event <=
  O.sum_counts admitted_native operations event.
Proof.
  intros operations H. induction H as [|operation rest HC HR IH]; intro event.
  - reflexivity.
  - specialize (HC event). specialize (IH event).
    unfold O.sum_counts in *. cbn [fold_right]. lia.
Qed.

Theorem native_trace_weighted_cover : forall operations weight,
  Forall native_trace_cover operations ->
  D.weighted weight (O.sum_counts native_counts operations) <=
  D.weighted weight (O.sum_counts admitted_native operations).
Proof.
  intros operations weight H. apply D.weighted_componentwise_bound.
  now apply native_trace_list_is_covered.
Qed.

Definition paid_native {A} cancelled available operations (build : unit -> option A) :=
  precharged_action cancelled available
    (D.weighted D.logical_work_weight (O.sum_counts admitted_native operations))
    (D.weighted D.logical_unit_weight (O.sum_counts admitted_native operations)) build.

Theorem native_refusal_precedes_action : forall A available operations
    (build : unit -> option A),
  reserve available
    (D.weighted D.logical_work_weight (O.sum_counts admitted_native operations))
    (D.weighted D.logical_unit_weight (O.sum_counts admitted_native operations)) = None ->
  paid_native false available operations build = Refused available.
Proof. intros. now apply failed_precharge_is_independent_of_constructor. Qed.

Theorem accepted_native_action_covers_actual_trace :
  forall A cancelled available operations (build : unit -> option A) paid value,
  Forall native_trace_cover operations ->
  paid_native cancelled available operations build = Accepted paid value ->
  cancelled = false /\ build tt = Some value /\
  work_left paid +
    D.weighted D.logical_work_weight (O.sum_counts native_counts operations)
    <= work_left available /\
  units_left paid +
    D.weighted D.logical_unit_weight (O.sum_counts native_counts operations)
    <= units_left available.
Proof.
  intros A cancelled available operations build paid value HC HA.
  apply successful_action_constructs_only_the_paid_result in HA.
  destruct HA as [HX [HB [HW HU]]].
  pose proof (native_trace_weighted_cover operations D.logical_work_weight HC).
  pose proof (native_trace_weighted_cover operations D.logical_unit_weight HC).
  repeat split; try assumption; lia.
Qed.

End NativeOperations.

Print Assumptions binding_rebuild_is_existing.
Print Assumptions binding_transform_refines_existing.
Print Assumptions binding_bag_refines_existing.
Print Assumptions binding_retains_source_total.
Print Assumptions binding_collision_keeps_first_key_last_count.
Print Assumptions clone_zero_discards_incoming.
Print Assumptions binding_zero_retains_an_owned_key.
Print Assumptions clone_positive_collision_accumulates.
Print Assumptions rebuild_width.
Print Assumptions rebuilt_prefix_fits_source_width.
Print Assumptions stored_width_is_owned_occurrence_count.
Print Assumptions count_changes_preserve_owned_inventory.
Print Assumptions insert_owner_partition.
Print Assumptions rebuild_owner_partition.
Print Assumptions prefix_owner_partition.
Print Assumptions clone_prefix_total_advances.
Print Assumptions accumulating_map_insert_count_sum.
Print Assumptions clone_insert_count_sum.
Print Assumptions clone_fold_count_sum.
Print Assumptions clone_rebuild_count_sum.
Print Assumptions lookup_count_le_sum.
Print Assumptions clone_accumulator_lookup_is_bounded.
Print Assumptions clone_running_total_guard_covers_occupied_addition.
Print Assumptions bag_cleanup_projection.
Print Assumptions partial_bag_flat_cleanup_is_covered.
Print Assumptions prepared_slots_return_source_sequence.
Print Assumptions occurrence_partition_transfers_output_credits.
Print Assumptions partitioned_partial_root_cleanup_is_covered.
Print Assumptions native_trace_list_is_covered.
Print Assumptions native_trace_weighted_cover.
Print Assumptions native_refusal_precedes_action.
Print Assumptions accepted_native_action_covers_actual_trace.
End RequiredHashBagBindingReservation.
