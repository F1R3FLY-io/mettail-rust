(** Exact HashBag binding reconstruction, including equal-key collisions.
    Input entries follow the source iterator order. Keys compare by identity,
    not diagnostic payload. Insertion retains the first equal key object and
    the last assigned count. The old total_count is transported verbatim:
    no theorem asserts that it equals the surviving counts' sum.

    The list represents keyed insertion semantics, not HashMap bucket order.
    The summary function abstracts order-independent final-entry hashing;
    its actual bytes and source-iterator correspondence need Rust tests.
    This is not a repair of general bag semantics or a resource proof. *)
From Stdlib Require Import List Arith Bool.
Import ListNotations.
Module HashBagBindingReconstruction.
Section Reconstruction.
Context {Payload Summary : Type}.
Record Key := { identity : nat; diagnostic : Payload }.
Definition Entry := (Key * nat)%type.

Fixpoint insert_entry (incoming : Entry) (entries : list Entry) : list Entry :=
  match entries with
  | [] => [incoming]
  | (stored, count) :: rest =>
    if Nat.eqb (identity (fst incoming)) (identity stored) then
      (stored, snd incoming) :: rest
    else (stored, count) :: insert_entry incoming rest
  end.
Definition insert_step (entries : list Entry) (incoming : Entry) :=
  insert_entry incoming entries.
Definition rebuild_entries (entries : list Entry) : list Entry :=
  fold_left insert_step entries [].
Record Bag := {
  stored_entries : list Entry;
  retained_total : nat;
  stored_summary : Summary
}.
Variable summary : list Entry -> Summary.
Definition from_binding_entries (total : nat) (entries : list Entry) : Bag :=
  let rebuilt := rebuild_entries entries in
  {| stored_entries := rebuilt; retained_total := total;
     stored_summary := summary rebuilt |}.
Definition transform_entry (transform : Key -> Key) (entry : Entry) : Entry :=
  (transform (fst entry), snd entry).

(** Existing loop: transform one original element, then insert it with the
    original count. A mapped iterator can use the same insertion recipe. *)
Definition existing_binding_entries
    (transform : Key -> Key) (entries : list Entry) : list Entry :=
  fold_left
    (fun accumulated entry =>
       insert_entry (transform_entry transform entry) accumulated) entries [].
Definition existing_binding_recipe
    (transform : Key -> Key) (total : nat) (entries : list Entry) : Bag :=
  let rebuilt := existing_binding_entries transform entries in
  {| stored_entries := rebuilt; retained_total := total;
     stored_summary := summary rebuilt |}.

Lemma transformation_insertion_fusion :
  forall entries accumulated transform,
  fold_left insert_step (map (transform_entry transform) entries) accumulated =
  fold_left
    (fun acc entry => insert_entry (transform_entry transform entry) acc)
    entries accumulated.
Proof.
  induction entries as [|entry rest IH]; intros accumulated transform.
  - reflexivity.
  - cbn [map fold_left insert_step]. apply IH.
Qed.

Theorem pretransformed_helper_equals_existing_recipe :
  forall transform total entries,
  from_binding_entries total (map (transform_entry transform) entries) =
  existing_binding_recipe transform total entries.
Proof.
  intros. unfold from_binding_entries, rebuild_entries,
    existing_binding_recipe, existing_binding_entries.
  now rewrite transformation_insertion_fusion.
Qed.

Lemma corresponding_transforms_have_identical_entries :
  forall entries first second,
  (forall key, first key = second key) ->
  map (transform_entry first) entries = map (transform_entry second) entries.
Proof.
  induction entries as [|[key count] rest IH]; intros first second H.
  - reflexivity.
  - change ((first key, count) :: map (transform_entry first) rest =
            (second key, count) :: map (transform_entry second) rest).
    rewrite H. now rewrite (IH first second H).
Qed.

(** Explicit element-transform refinement obligation, not an engine axiom. *)
Theorem corresponding_iterative_transform_preserves_existing_recipe :
  forall iterative existing total entries,
  (forall key, iterative key = existing key) ->
  from_binding_entries total (map (transform_entry iterative) entries) =
  existing_binding_recipe existing total entries.
Proof.
  intros iterative existing total entries H.
  rewrite (corresponding_transforms_have_identical_entries
    entries iterative existing H).
  apply pretransformed_helper_equals_existing_recipe.
Qed.

Theorem binding_reconstruction_retains_original_total : forall total entries,
  retained_total (from_binding_entries total entries) = total.
Proof. reflexivity. Qed.
Theorem binding_summary_uses_final_entries : forall total entries,
  stored_summary (from_binding_entries total entries) =
  summary (stored_entries (from_binding_entries total entries)).
Proof. reflexivity. Qed.
Theorem empty_binding_reconstruction : forall total,
  from_binding_entries total [] =
  {| stored_entries := []; retained_total := total; stored_summary := summary [] |}.
Proof. reflexivity. Qed.
Theorem singleton_binding_reconstruction : forall total key count,
  stored_entries (from_binding_entries total [(key, count)]) = [(key, count)].
Proof. reflexivity. Qed.

Theorem equal_identity_retains_first_diagnostic_and_last_count :
  forall id first_payload last_payload first_count last_count total,
  let first := {| identity := id; diagnostic := first_payload |} in
  let last := {| identity := id; diagnostic := last_payload |} in
  stored_entries
    (from_binding_entries total [(first, first_count); (last, last_count)]) =
  [(first, last_count)].
Proof.
  intros. subst first last. cbv [from_binding_entries rebuild_entries fold_left
    insert_step insert_entry stored_entries identity fst snd].
  now rewrite Nat.eqb_refl.
Qed.
Theorem three_colliding_entries_keep_first_key_and_final_count :
  forall id p1 p2 p3 c1 c2 c3 total,
  let k1 := {| identity := id; diagnostic := p1 |} in
  let k2 := {| identity := id; diagnostic := p2 |} in
  let k3 := {| identity := id; diagnostic := p3 |} in
  stored_entries
    (from_binding_entries total [(k1, c1); (k2, c2); (k3, c3)]) = [(k1, c3)].
Proof.
  intros. subst k1 k2 k3. cbv [from_binding_entries rebuild_entries fold_left
    insert_step insert_entry stored_entries identity fst snd].
  rewrite Nat.eqb_refl. cbn. now rewrite Nat.eqb_refl.
Qed.
Theorem distinct_identities_preserve_both_entries :
  forall first last first_count last_count total,
  identity first <> identity last ->
  stored_entries
    (from_binding_entries total [(first, first_count); (last, last_count)]) =
  [(first, first_count); (last, last_count)].
Proof.
  intros first last first_count last_count total H.
  change ((if Nat.eqb (identity last) (identity first)
           then [(first, last_count)]
           else [(first, first_count); (last, last_count)]) =
          [(first, first_count); (last, last_count)]).
  assert (HE : Nat.eqb (identity last) (identity first) = false).
  { apply Nat.eqb_neq. congruence. }
  now rewrite HE.
Qed.
End Reconstruction.
Print Assumptions transformation_insertion_fusion.
Print Assumptions pretransformed_helper_equals_existing_recipe.
Print Assumptions corresponding_transforms_have_identical_entries.
Print Assumptions corresponding_iterative_transform_preserves_existing_recipe.
Print Assumptions binding_reconstruction_retains_original_total.
Print Assumptions binding_summary_uses_final_entries.
Print Assumptions empty_binding_reconstruction.
Print Assumptions singleton_binding_reconstruction.
Print Assumptions equal_identity_retains_first_diagnostic_and_last_count.
Print Assumptions three_colliding_entries_keep_first_key_and_final_count.
Print Assumptions distinct_identities_preserve_both_entries.
End HashBagBindingReconstruction.
