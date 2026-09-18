(** Decoration of the existing DDL finishing stack. The constructors remain
    parameters: their erasure equations are discharged by the actual text and
    closed wire-list constructors, not inferred for arbitrary callbacks.
    These transport laws concern values and single-use slots, not resource
    charging, allocator behavior, or termination of foreign implementations. *)
From Stdlib Require Import List Arith.
Import ListNotations.

Definition take_slot {A} (index : nat) (slots : list (option A))
    : option (A * list (option A)) :=
  match nth_error slots index with
  | Some (Some value) =>
      Some (value, firstn index slots ++ None :: skipn (S index) slots)
  | _ => None
  end.

Definition assemble_suffix {A} (build : list A -> A) (count : nat)
    (values : list A) : option (list A) :=
  if count <=? length values then
    let start := length values - count in
    Some (firstn start values ++ [build (skipn start values)])
  else None.

Section Erasure.
Context {A B : Type} (erase : A -> B).

Theorem push_erases_exactly : forall value values,
  map erase (values ++ [value]) = map erase values ++ [erase value].
Proof. intros. rewrite map_app. reflexivity. Qed.

Theorem take_slot_erases_exactly : forall index slots,
  option_map (fun result => (erase (fst result),
    map (option_map erase) (snd result))) (take_slot index slots) =
  take_slot index (map (option_map erase) slots).
Proof.
  intros index slots. unfold take_slot. rewrite nth_error_map.
  destruct (nth_error slots index) as [[value|]|];
    cbn [option_map fst snd]; try reflexivity.
  rewrite map_app, firstn_map, skipn_map. reflexivity.
Qed.

Theorem assemble_suffix_erases_exactly : forall build_a build_b,
  (forall children, erase (build_a children) = build_b (map erase children)) ->
  forall count values,
  option_map (map erase) (assemble_suffix build_a count values) =
  assemble_suffix build_b count (map erase values).
Proof.
  intros build_a build_b H count values. unfold assemble_suffix.
  rewrite length_map. destruct (count <=? length values); cbn; try reflexivity.
  rewrite map_app. cbn [map].
  rewrite H, firstn_map, skipn_map. reflexivity.
Qed.

Theorem text_constructor_erases_exactly : forall (Text : Type)
    (build_a : Text -> A) (build_b : Text -> B),
  (forall text, erase (build_a text) = build_b text) ->
  forall text values,
  map erase (values ++ [build_a text]) = map erase values ++ [build_b text].
Proof. intros Text build_a build_b H text values. rewrite push_erases_exactly, H. reflexivity. Qed.
End Erasure.

Print Assumptions push_erases_exactly.
Print Assumptions take_slot_erases_exactly.
Print Assumptions assemble_suffix_erases_exactly.
Print Assumptions text_constructor_erases_exactly.
