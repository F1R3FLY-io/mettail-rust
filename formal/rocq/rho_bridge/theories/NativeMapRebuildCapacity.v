(** Capacity connector for fresh, preallocated HashMapLit reconstruction.

    The input is the ACTUAL ordered pair roster already produced by the body
    worklist. First-only FLT replacement is stateful across occurrences; no
    pure pointwise transformation of keys or values is assumed here.

    This file reuses OrderedBindingReconstruction's insertion semantics and
    width theorem. It adds finite-prefix arithmetic, not another map machine,
    hash table, allocator, or reservation algebra. Collisions may keep the
    width unchanged, and vacant insertion increases it by one. Both leave a
    fresh table reserved for the entire roster within its original capacity.

    Pinned source correspondence (IndexMap 2.14.0 / hashbrown 0.17.1):
    - Core::with_capacity allocates indices and dense entries for roster width.
    - Core::capacity is min(indices.capacity(), entries.capacity()).
    - RawTable::capacity is items + growth_left.
    - Core::insert_full replaces only the value on an occupied entry; a vacant
      entry stores the old dense length as its unique new index and appends.
    - find_or_find_insert_index reserves one slot BEFORE checking occupancy.
      A positive growth_left therefore matters even for a duplicate key.
    - This boundary creates a fresh table and only inserts: no removals,
      tombstones, arbitrary mutation or mutation of retained keys is allowed.

    Those concrete invariants relate native state to the numbers below; this
    is not a verification of the library implementation. Capacity is a lower
    bound on room, never a witness of raw bucket count, byte layout or RSS.
    Geometry, checked usize arithmetic, native Hash/Eq/probe costs, immutable
    roster delivery, and original/partial-result cleanup remain separate
    source obligations. Existing preparation/paid-stage laws admit those
    actions before execution, preserve accepted charges on failure, and do
    not become unnecessary merely because capacity is sufficient.

    The final generic projection lemma reuses Stdlib list facts to transport
    existing probe candidate NoDup/inclusion through IndexMap's slot-to-entry
    injection. Its premises are explicit source obligations, not assumptions
    that a Rust algorithm is correct. No probe or SIMD proof is repeated. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import OrderedBindingReconstruction.
Import ListNotations.

Module NativeMapCapacity.
Module M := OrderedBindingReconstruction.OrderedBindingReconstruction.

Section OrderedRoster.
Context {Payload Value : Type}.
Definition Entry := (@M.Key Payload * Value)%type.

Theorem next_insert_is_the_extended_ordered_prefix :
  forall (prefix : list Entry) incoming,
  M.rebuild (prefix ++ [incoming]) = M.insert_map incoming (M.rebuild prefix).
Proof.
  intros. unfold M.rebuild. rewrite fold_left_app. reflexivity.
Qed.

(** The exact two cardinality outcomes include collisions in any position. *)
Theorem insertion_width_is_unchanged_or_successor :
  forall (retained : list Entry) incoming,
  length (M.insert_map incoming retained) = length retained \/
  length (M.insert_map incoming retained) = S (length retained).
Proof.
  induction retained as [|[key value] rest IH]; intros [incoming next].
  - right. reflexivity.
  - cbn [M.insert_map fst snd].
    destruct (Nat.eqb (M.key_id incoming) (M.key_id key)).
    + left. reflexivity.
    + specialize (IH (incoming, next)). cbn [length]. lia.
Qed.

Theorem fresh_prefix_has_room :
  forall (roster prefix : list Entry) incoming suffix table_capacity entry_capacity,
  roster = prefix ++ incoming :: suffix ->
  length roster <= Nat.min table_capacity entry_capacity ->
  length (M.rebuild prefix) < table_capacity /\
  length (M.rebuild prefix) < entry_capacity.
Proof.
  intros roster prefix incoming suffix table_capacity entry_capacity SAME ROOM.
  pose proof (M.rebuild_width Value prefix) as WIDTH.
  rewrite SAME, length_app in ROOM. cbn [length] in ROOM.
  assert (STRICT : length prefix < length prefix + S (length suffix)).
  { rewrite Nat.add_succ_r. apply Nat.lt_succ_r. apply Nat.le_add_r. }
  split; eapply Nat.le_lt_trans; [exact WIDTH | | exact WIDTH |];
    eapply Nat.lt_le_trans; [exact STRICT | | exact STRICT |];
    eapply Nat.le_trans; [exact ROOM | | exact ROOM |].
  - apply Nat.le_min_l.
  - apply Nat.le_min_r.
Qed.

(** [items + growth_left] is the exact native capacity expression. This
    derives the condition of reserve(1)'s non-growing branch; it does not
    infer raw table geometry from the public min capacity. *)
Theorem prefix_has_growth_credit_and_dense_slot :
  forall (roster prefix : list Entry) incoming suffix growth_left entry_capacity,
  roster = prefix ++ incoming :: suffix ->
  length roster <= Nat.min (length (M.rebuild prefix) + growth_left) entry_capacity ->
  1 <= growth_left /\ length (M.rebuild prefix) < entry_capacity.
Proof.
  intros roster prefix incoming suffix growth_left entry_capacity SAME ROOM.
  pose proof (fresh_prefix_has_room roster prefix incoming suffix
    (length (M.rebuild prefix) + growth_left) entry_capacity SAME ROOM) as [GROW DENSE].
  split; [lia | exact DENSE].
Qed.

Theorem next_insert_stays_inside_initial_capacities :
  forall (roster prefix : list Entry) incoming suffix table_capacity entry_capacity,
  roster = prefix ++ incoming :: suffix ->
  length roster <= Nat.min table_capacity entry_capacity ->
  length (M.insert_map incoming (M.rebuild prefix)) <= table_capacity /\
  length (M.insert_map incoming (M.rebuild prefix)) <= entry_capacity.
Proof.
  intros roster prefix incoming suffix table_capacity entry_capacity SAME ROOM.
  pose proof (fresh_prefix_has_room roster prefix incoming suffix
    table_capacity entry_capacity SAME ROOM) as [TABLE DENSE].
  pose proof (M.insert_map_width Value incoming (M.rebuild prefix)). split; lia.
Qed.

(** Both native branches preserve usable table capacity: occupied insertion
    changes neither item count nor growth credit; vacant insertion consumes
    exactly one credit. This small arithmetic fact is not a native transition
    model. Its source premise requires an originally empty (not deleted) slot. *)
Theorem occupied_and_vacant_capacity_arithmetic : forall items growth_left,
  1 <= growth_left ->
  items + growth_left = items + growth_left /\
  S items + (growth_left - 1) = items + growth_left.
Proof. intros. split; lia. Qed.

Theorem complete_roster_fits_initial_capacities :
  forall (roster : list Entry) table_capacity entry_capacity,
  length roster <= Nat.min table_capacity entry_capacity ->
  length (M.rebuild roster) <= table_capacity /\
  length (M.rebuild roster) <= entry_capacity.
Proof.
  intros roster table_capacity entry_capacity ROOM.
  pose proof (M.rebuild_width Value roster) as WIDTH.
  split; eapply Nat.le_trans; [exact WIDTH | | exact WIDTH |];
    eapply Nat.le_trans; [exact ROOM | | exact ROOM |].
  - apply Nat.le_min_l.
  - apply Nat.le_min_r.
Qed.

Theorem empty_roster_has_no_retained_entries : M.rebuild ([] : list Entry) = [].
Proof. reflexivity. Qed.
End OrderedRoster.

Theorem slot_projection_preserves_candidate_coverage :
  forall (Slot EntryId : Type) (entry_at : Slot -> EntryId) candidates retained_slots,
  NoDup candidates -> incl candidates retained_slots ->
  (forall left right, In left retained_slots -> In right retained_slots ->
     entry_at left = entry_at right -> left = right) ->
  NoDup (map entry_at candidates) /\
  incl (map entry_at candidates) (map entry_at retained_slots).
Proof.
  intros Slot EntryId entry_at candidates retained_slots DISTINCT INCLUDED INJECTIVE.
  split.
  - apply NoDup_map_NoDup_ForallPairs; [|exact DISTINCT].
    intros left right LEFT RIGHT EQ.
    apply INJECTIVE; auto.
  - now apply incl_map.
Qed.

Print Assumptions next_insert_is_the_extended_ordered_prefix.
Print Assumptions insertion_width_is_unchanged_or_successor.
Print Assumptions fresh_prefix_has_room.
Print Assumptions prefix_has_growth_credit_and_dense_slot.
Print Assumptions next_insert_stays_inside_initial_capacities.
Print Assumptions occupied_and_vacant_capacity_arithmetic.
Print Assumptions complete_roster_fits_initial_capacities.
Print Assumptions empty_roster_has_no_retained_entries.
Print Assumptions slot_projection_preserves_candidate_coverage.
End NativeMapCapacity.
