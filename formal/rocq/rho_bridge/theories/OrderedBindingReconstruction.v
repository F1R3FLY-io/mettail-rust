(** Ordered binding reconstruction from an explicit source sequence.

    Map lists represent IndexMap insertion order. Set lists represent
    first-retained representatives, NOT HashSet iteration order or bucket
    layout. Key identities represent Eq classes; diagnostic payload is
    retained but does not participate in this modeled equality.

    Concrete sources: runtime/src/hashset_lit.rs and hashmap_lit.rs rebuild
    transformed entries by insertion; pathmap_lit.rs retains the Empty/Set/Map
    discriminant; zipper_lit.rs binds its context but not its focus bytes.
    The iterative clone emitter already uses these reconstruction recipes.

    Transformation/insertion fusion is pure. Stateful callbacks, resource
    admission, Rust hashing and iterator correspondence are outside this
    model. No collision-freedom hypothesis is required. *)
From Stdlib Require Import List Arith Bool Lia Sorting.Permutation.
From RhoBridge Require Import HashBagBindingReconstruction.
Import ListNotations.

Module OrderedBindingReconstruction.
Module Bag := HashBagBindingReconstruction.

Section Reconstruction.
Context {Payload : Type}.
Definition Key := @Bag.Key Payload.
Definition key_id : Key -> nat := @Bag.identity Payload.

Fixpoint insert_map {V : Type}
    (incoming : Key * V) (entries : list (Key * V))
    : list (Key * V) :=
  match entries with
  | [] => [incoming]
  | (stored, value) :: rest =>
      if Nat.eqb (key_id (fst incoming)) (key_id stored)
      then (stored, snd incoming) :: rest
      else (stored, value) :: insert_map incoming rest
  end.

Definition rebuild {V : Type} (entries : list (Key * V)) :=
  fold_left (fun acc entry => insert_map entry acc) entries [].

(** Reuse the existing bag insertion as the nat-valued specialization. *)
Lemma nat_insert_reuses_bag :
  forall incoming entries,
  @insert_map nat incoming entries = Bag.insert_entry incoming entries.
Proof.
  intros [key value] entries.
  induction entries as [|[stored old] rest IH].
  - reflexivity.
  - cbn [insert_map Bag.insert_entry fst snd key_id].
    unfold key_id.
    destruct (Nat.eqb (Bag.identity key) (Bag.identity stored)).
    + reflexivity.
    + now rewrite IH.
Qed.

(** General list law; specialization does not assume an engine is correct. *)
Lemma ordered_transform_insert_fusion :
  forall (A V : Type) (transform : A -> Key * V) entries accumulated,
  fold_left (fun acc entry => insert_map entry acc)
    (map transform entries) accumulated =
  fold_left (fun acc entry => insert_map (transform entry) acc)
    entries accumulated.
Proof.
  intros A V transform entries.
  induction entries as [|entry rest IH]; intros accumulated.
  - reflexivity.
  - cbn [map fold_left]. apply IH.
Qed.

Definition transform_pair {V : Type}
    (key_transform : Key -> Key) (value_transform : V -> V)
    (entry : Key * V) :=
  (key_transform (fst entry), value_transform (snd entry)).

Definition existing_map {V : Type}
    (key_transform : Key -> Key) (value_transform : V -> V)
    (entries : list (Key * V)) :=
  fold_left
    (fun acc entry =>
       insert_map (transform_pair key_transform value_transform entry) acc)
    entries [].

Theorem pretransformed_map_equals_existing :
  forall V key_transform value_transform (entries : list (Key * V)),
  rebuild (map (transform_pair key_transform value_transform) entries) =
  existing_map key_transform value_transform entries.
Proof.
  intros. unfold rebuild, existing_map.
  apply ordered_transform_insert_fusion.
Qed.

Theorem corresponding_entry_transforms :
  forall A V (first second : A -> Key * V) entries,
  (forall entry, In entry entries -> first entry = second entry) ->
  rebuild (map first entries) = rebuild (map second entries).
Proof.
  intros A V first second entries H.
  assert (HM : map first entries = map second entries).
  { apply map_ext_in. exact H. }
  now rewrite HM.
Qed.

(** An equal key updates in place and retains the stored key object. *)
Theorem insertion_retains_key_and_position :
  forall V prefix stored old suffix incoming (value : V),
  Forall (fun entry => key_id (fst entry) <> key_id incoming) prefix ->
  key_id incoming = key_id stored ->
  insert_map (incoming, value) (prefix ++ (stored, old) :: suffix) =
  prefix ++ (stored, value) :: suffix.
Proof.
  intros V prefix.
  induction prefix as [|[key previous] rest IH];
    intros stored old suffix incoming value Hprefix Heq.
  - cbn [app insert_map fst snd]. rewrite Heq, Nat.eqb_refl. reflexivity.
  - inversion Hprefix as [|entry tail Hhead Htail]; subst.
    cbn [fst] in Hhead.
    assert (Hne : Nat.eqb (key_id incoming) (key_id key) = false).
    { apply Nat.eqb_neq. congruence. }
    cbn [app insert_map fst snd]. rewrite Hne.
    now rewrite (IH stored old suffix incoming value Htail Heq).
Qed.

Fixpoint lookup {V : Type} (wanted : nat) (entries : list (Key * V))
    : option V :=
  match entries with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb wanted (key_id key) then Some value
      else lookup wanted rest
  end.

Lemma lookup_insert :
  forall V wanted incoming (entries : list (Key * V)),
  lookup wanted (insert_map incoming entries) =
  if Nat.eqb wanted (key_id (fst incoming))
  then Some (snd incoming) else lookup wanted entries.
Proof.
  intros V wanted [key value] entries.
  induction entries as [|[stored old] rest IH].
  - reflexivity.
  - cbn [insert_map fst snd].
    destruct (Nat.eqb (key_id key) (key_id stored)) eqn:Hks.
    + apply Nat.eqb_eq in Hks.
      cbn [lookup fst snd]. rewrite Hks.
      destruct (Nat.eqb wanted (key_id stored)); reflexivity.
    + cbn [lookup fst snd].
      destruct (Nat.eqb wanted (key_id stored)) eqn:Hws.
      * assert (Hwk : Nat.eqb wanted (key_id key) = false).
        { apply Nat.eqb_neq.
          apply Nat.eqb_eq in Hws.
          apply Nat.eqb_neq in Hks. congruence. }
        now rewrite Hwk.
      * exact IH.
Qed.

Definition last_value {V : Type}
    (wanted : nat) (entries : list (Key * V)) (initial : option V) :=
  fold_left
    (fun found entry =>
       if Nat.eqb wanted (key_id (fst entry))
       then Some (snd entry) else found)
    entries initial.

Lemma lookup_fold :
  forall V wanted entries (accumulated : list (Key * V)),
  lookup wanted
    (fold_left (fun acc entry => insert_map entry acc)
       entries accumulated) =
  last_value wanted entries (lookup wanted accumulated).
Proof.
  intros V wanted entries.
  induction entries as [|entry rest IH]; intros accumulated.
  - reflexivity.
  - cbn [fold_left]. rewrite IH, lookup_insert. reflexivity.
Qed.

Theorem reconstruction_uses_last_value :
  forall V wanted (entries : list (Key * V)),
  lookup wanted (rebuild entries) = last_value wanted entries None.
Proof.
  intros. unfold rebuild. apply lookup_fold.
Qed.

Theorem collision_retains_first_key_and_last_value :
  forall V first last (earlier later : V),
  key_id first = key_id last ->
  rebuild [(first, earlier); (last, later)] = [(first, later)].
Proof.
  intros V first last earlier later H.
  cbn [rebuild fold_left insert_map fst snd].
  rewrite H, Nat.eqb_refl. reflexivity.
Qed.

Theorem distinct_entries_preserve_order :
  forall V first last (earlier later : V),
  key_id first <> key_id last ->
  rebuild [(first, earlier); (last, later)] =
  [(first, earlier); (last, later)].
Proof.
  intros V first last earlier later H.
  assert (Hne : Nat.eqb (key_id last) (key_id first) = false).
  { apply Nat.eqb_neq. congruence. }
  cbn [rebuild fold_left insert_map fst snd]. now rewrite Hne.
Qed.

(** Unit-valued insertion has exactly set first-retention behavior.
    Its list order is only a representative-history witness for HashSetLit. *)
Definition set_rebuild (keys : list Key) : list Key :=
  map fst (rebuild (map (fun key => (key, tt)) keys)).

Definition existing_set (transform : Key -> Key) (keys : list Key) :=
  map fst
    (fold_left (fun acc key => insert_map (transform key, tt) acc) keys []).

Theorem pretransformed_set_equals_existing :
  forall transform keys,
  set_rebuild (map transform keys) = existing_set transform keys.
Proof.
  intros. unfold set_rebuild, existing_set, rebuild.
  rewrite map_map.
  rewrite ordered_transform_insert_fusion. reflexivity.
Qed.

Theorem set_collision_retains_first :
  forall first last,
  key_id first = key_id last ->
  set_rebuild [first; last] = [first].
Proof.
  intros first last H.
  unfold set_rebuild.
  change (map fst (rebuild [(first, tt); (last, tt)]) = [first]).
  rewrite collision_retains_first_key_and_last_value by exact H.
  reflexivity.
Qed.

(** SetPath models PathMapLit::Set's ordered HashMapLit<Key, ()>, not
    HashSetLit bucket order. Its representative history is its insertion
    order, so the same unit-valued reconstruction also preserves position. *)
Inductive Path (V : Type) :=
| EmptyPath : Path V
| SetPath : list Key -> Path V
| MapPath : list (Key * V) -> Path V.
Arguments EmptyPath {V}.
Arguments SetPath {V} _.
Arguments MapPath {V} _.

Definition transform_path {V}
    (kt : Key -> Key) (vt : V -> V) (path : Path V) :=
  match path with
  | EmptyPath => EmptyPath
  | SetPath keys => SetPath (map kt keys)
  | MapPath entries => MapPath (map (transform_pair kt vt) entries)
  end.

Definition rebuild_path {V} (path : Path V) :=
  match path with
  | EmptyPath => EmptyPath
  | SetPath keys => SetPath (set_rebuild keys)
  | MapPath entries => MapPath (rebuild entries)
  end.

Definition existing_path {V}
    (kt : Key -> Key) (vt : V -> V) (path : Path V) :=
  match path with
  | EmptyPath => EmptyPath
  | SetPath keys => SetPath (existing_set kt keys)
  | MapPath entries => MapPath (existing_map kt vt entries)
  end.

Theorem path_reconstruction_fusion :
  forall V kt vt (path : Path V),
  rebuild_path (transform_path kt vt path) = existing_path kt vt path.
Proof.
  intros V kt vt [|keys|entries]; cbn.
  - reflexivity.
  - now rewrite pretransformed_set_equals_existing.
  - now rewrite pretransformed_map_equals_existing.
Qed.

Theorem empty_modes_remain_distinct :
  forall V,
  @rebuild_path V EmptyPath = EmptyPath /\
  @rebuild_path V (SetPath []) = SetPath [] /\
  @rebuild_path V (MapPath []) = MapPath [] /\
  @SetPath V [] <> EmptyPath /\ @MapPath V [] <> EmptyPath.
Proof.
  intros. repeat split; try reflexivity; discriminate.
Qed.

Definition rebuild_zipper {V Focus}
    (kt : Key -> Key) (vt : V -> V) (zipper : Path V * Focus) :=
  (rebuild_path (transform_path kt vt (fst zipper)), snd zipper).

Theorem zipper_context_exact_focus_inert :
  forall V Focus kt vt (path : Path V) (focus : Focus),
  rebuild_zipper kt vt (path, focus) =
  (existing_path kt vt path, focus).
Proof.
  intros. unfold rebuild_zipper. cbn.
  now rewrite path_reconstruction_fusion.
Qed.

(** Width counts stored entries, not bag multiplicity or allocation capacity.
    Collisions can remove entries; no collision-freedom premise is needed. *)
Lemma insert_map_width :
  forall V incoming (entries : list (Key * V)),
  length (insert_map incoming entries) <= S (length entries).
Proof.
  intros V [key value] entries.
  induction entries as [|[stored old] rest IH].
  - cbn. lia.
  - cbn [insert_map fst snd].
    destruct (Nat.eqb (key_id key) (key_id stored)); cbn; lia.
Qed.

Lemma fold_insert_map_width :
  forall V entries (acc : list (Key * V)),
  length (fold_left (fun acc entry => insert_map entry acc) entries acc)
  <= length acc + length entries.
Proof.
  intros V entries.
  induction entries as [|entry rest IH]; intros acc.
  - cbn. lia.
  - cbn [fold_left].
    specialize (IH (insert_map entry acc)).
    pose proof (insert_map_width V entry acc).
    cbn [length]. lia.
Qed.

Theorem rebuild_width :
  forall V (entries : list (Key * V)),
  length (rebuild entries) <= length entries.
Proof.
  intros V entries. unfold rebuild.
  pose proof (fold_insert_map_width V entries []). cbn in *. lia.
Qed.

Theorem transformed_rebuild_width :
  forall A V (transform : A -> Key * V) entries,
  length (rebuild (map transform entries)) <= length entries.
Proof.
  intros. pose proof (rebuild_width V (map transform entries)) as H.
  now rewrite length_map in H.
Qed.

Theorem set_rebuild_width :
  forall keys, length (set_rebuild keys) <= length keys.
Proof.
  intros keys. unfold set_rebuild. rewrite length_map.
  apply transformed_rebuild_width.
Qed.

Definition path_width {V} (path : Path V) : nat :=
  match path with
  | EmptyPath => 0
  | SetPath keys => length keys
  | MapPath entries => length entries
  end.

Theorem path_rebuild_width :
  forall V (path : Path V),
  path_width (rebuild_path path) <= path_width path.
Proof.
  intros V [|keys|entries]; cbn [rebuild_path path_width].
  - lia.
  - apply set_rebuild_width.
  - apply rebuild_width.
Qed.

(** Inventories contain ownership-occurrence tags, not semantic identities or
    heap addresses. Equal values may have different occurrence tags. A map
    collision retains the old key and incoming value, so whole entries must
    not be treated as indivisible ownership units. The permutation below
    conserves multiplicities even without a distinct-tag premise. It does not
    specify hash cost, destructor order, or unwind behavior. *)
Section Ownership.
Context {V : Type}.
Variable key_owners : Key -> list nat.
Variable value_owners : V -> list nat.

Definition entry_owners (entry : Key * V) : list nat :=
  key_owners (fst entry) ++ value_owners (snd entry).
Definition owners (entries : list (Key * V)) : list nat :=
  flat_map entry_owners entries.

Lemma insert_owner_partition :
  forall incoming entries,
  exists discarded,
    Permutation (entry_owners incoming ++ owners entries)
      (owners (insert_map incoming entries) ++ discarded).
Proof.
  intros [key value] entries.
  induction entries as [|[stored old] rest IH].
  - exists []. cbn [insert_map owners flat_map].
    now rewrite !app_nil_r.
  - cbn [insert_map fst snd].
    destruct (Nat.eqb (key_id key) (key_id stored)).
    + exists (key_owners key ++ value_owners old).
      apply (proj2 (Permutation_count_occ Nat.eq_dec _ _)). intro tag.
      cbn [owners flat_map]. unfold entry_owners. cbn [fst snd].
      repeat rewrite count_occ_app. lia.
    + destruct IH as [discarded HP]. exists discarded.
      apply (proj2 (Permutation_count_occ Nat.eq_dec _ _)). intro tag.
      pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) HP tag) as H.
      unfold owners in *. cbn [flat_map] in *.
      repeat rewrite count_occ_app in *. lia.
Qed.

Lemma fold_owner_partition :
  forall entries acc,
  exists discarded,
    Permutation (owners acc ++ owners entries)
      (owners (fold_left (fun acc entry => insert_map entry acc) entries acc)
        ++ discarded).
Proof.
  induction entries as [|entry rest IH]; intros acc.
  - exists []. cbn [owners flat_map fold_left]. reflexivity.
  - destruct (insert_owner_partition entry acc) as [first HP].
    destruct (IH (insert_map entry acc)) as [later HQ].
    exists (first ++ later).
    apply (proj2 (Permutation_count_occ Nat.eq_dec _ _)). intro tag.
    pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) HP tag) as H.
    pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) HQ tag) as J.
    unfold owners in *. cbn [flat_map fold_left] in *.
    repeat rewrite count_occ_app in *. lia.
Qed.

Theorem rebuild_owner_partition :
  forall entries,
  exists discarded,
    Permutation (owners entries) (owners (rebuild entries) ++ discarded).
Proof.
  intro entries. unfold rebuild.
  exact (fold_owner_partition entries []).
Qed.

End Ownership.

Section SetOwnership.
Variable key_owners : Key -> list nat.

Lemma unit_owners_keys :
  forall entries : list (Key * unit),
  @owners unit key_owners (fun _ => []) entries =
  flat_map key_owners (map fst entries).
Proof.
  induction entries as [|[key []] rest IH].
  - reflexivity.
  - change ((key_owners key ++ []) ++
      @owners unit key_owners (fun _ => []) rest =
      key_owners key ++ flat_map key_owners (map fst rest)).
    rewrite app_nil_r. now rewrite IH.
Qed.

Theorem set_rebuild_owner_partition :
  forall keys,
  exists discarded,
    Permutation (flat_map key_owners keys)
      (flat_map key_owners (set_rebuild keys) ++ discarded).
Proof.
  intro keys.
  destruct (@rebuild_owner_partition unit key_owners (fun _ => [])
    (map (fun key => (key, tt)) keys)) as [discarded HP].
  exists discarded. rewrite !unit_owners_keys in HP.
  rewrite map_map in HP. cbn [fst] in HP. rewrite map_id in HP.
  exact HP.
Qed.

End SetOwnership.

Definition path_owners {V} (key_owners : Key -> list nat)
    (value_owners : V -> list nat) (path : Path V) : list nat :=
  match path with
  | EmptyPath => []
  | SetPath keys => flat_map key_owners keys
  | MapPath entries => owners key_owners value_owners entries
  end.

Theorem path_rebuild_owner_partition :
  forall V key_owners value_owners (path : Path V),
  exists discarded,
    Permutation (path_owners key_owners value_owners path)
      (path_owners key_owners value_owners (rebuild_path path) ++ discarded).
Proof.
  intros V key_owners value_owners [|keys|entries];
    cbn [path_owners rebuild_path].
  - exists []. reflexivity.
  - apply set_rebuild_owner_partition.
  - apply rebuild_owner_partition.
Qed.

(** Distinct occurrence tags make the retained and discarded inventories
    disjoint. This premise says nothing about equality of represented values.
    It applies to each partition theorem above, including partially built
    accumulators through fold_owner_partition. *)
Lemma nodup_inventory_disjoint :
  forall retained discarded : list nat,
  NoDup (retained ++ discarded) ->
  forall tag, In tag retained -> ~ In tag discarded.
Proof.
  induction retained as [|head rest IH]; intros discarded H tag Hin Hout.
  - contradiction.
  - inversion H as [|x xs Hnot Htail]; subst.
    destruct Hin as [Heq|Hin].
    + subst tag. apply Hnot. apply in_or_app. now right.
    + exact (IH discarded Htail tag Hin Hout).
Qed.

Theorem owner_partition_disjoint :
  forall original retained discarded : list nat,
  Permutation original (retained ++ discarded) -> NoDup original ->
  NoDup (retained ++ discarded) /\
  (forall tag, In tag retained -> ~ In tag discarded).
Proof.
  intros original retained discarded HP HN.
  pose proof (Permutation_NoDup HP HN) as H.
  split; [exact H|now apply nodup_inventory_disjoint].
Qed.

Definition inventory_credit (credit : nat -> nat) (inventory : list nat) :=
  fold_right (fun tag total => credit tag + total) 0 inventory.

Lemma inventory_credit_app :
  forall credit left right,
  inventory_credit credit (left ++ right) =
  inventory_credit credit left + inventory_credit credit right.
Proof.
  intros credit left. unfold inventory_credit.
  induction left as [|tag rest IH]; intro right.
  - reflexivity.
  - cbn [fold_right app]. rewrite IH. lia.
Qed.

Theorem owner_partition_credit_conservation :
  forall credit original retained discarded,
  Permutation original (retained ++ discarded) ->
  inventory_credit credit original =
  inventory_credit credit retained + inventory_credit credit discarded.
Proof.
  intros credit original retained discarded HP.
  rewrite <- inventory_credit_app.
  unfold inventory_credit.
  induction HP; cbn [fold_right] in *; lia.
Qed.

End Reconstruction.
Print Assumptions nat_insert_reuses_bag.
Print Assumptions ordered_transform_insert_fusion.
Print Assumptions pretransformed_map_equals_existing.
Print Assumptions corresponding_entry_transforms.
Print Assumptions insertion_retains_key_and_position.
Print Assumptions lookup_insert.
Print Assumptions reconstruction_uses_last_value.
Print Assumptions collision_retains_first_key_and_last_value.
Print Assumptions distinct_entries_preserve_order.
Print Assumptions pretransformed_set_equals_existing.
Print Assumptions set_collision_retains_first.
Print Assumptions path_reconstruction_fusion.
Print Assumptions empty_modes_remain_distinct.
Print Assumptions zipper_context_exact_focus_inert.
Print Assumptions insert_map_width.
Print Assumptions fold_insert_map_width.
Print Assumptions rebuild_width.
Print Assumptions transformed_rebuild_width.
Print Assumptions set_rebuild_width.
Print Assumptions path_rebuild_width.
Print Assumptions insert_owner_partition.
Print Assumptions fold_owner_partition.
Print Assumptions rebuild_owner_partition.
Print Assumptions unit_owners_keys.
Print Assumptions set_rebuild_owner_partition.
Print Assumptions path_rebuild_owner_partition.
Print Assumptions nodup_inventory_disjoint.
Print Assumptions owner_partition_disjoint.
Print Assumptions inventory_credit_app.
Print Assumptions owner_partition_credit_conservation.
End OrderedBindingReconstruction.
