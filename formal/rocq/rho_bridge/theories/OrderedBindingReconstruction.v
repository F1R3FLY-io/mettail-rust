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
From Stdlib Require Import List Arith Bool.
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
End OrderedBindingReconstruction.
