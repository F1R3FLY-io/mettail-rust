(** Borrowed action-slot correspondence for the actual DDL JoinPieces source.

    Core normalize.rs already matches Separated -> Collection as one semantic
    collection slot and keeps the outer separator/nonempty behavior. Core's
    syntax_slot_names and schema collect_core_slots likewise descend through
    Separated. The action provider only borrows that immediate inner slot;
    it does not normalize/rewrite the grammar or rerun a classifier.

    Existing flat Collection admission remains unchanged. Exactly one direct
    wrapper is added. Keyed, mismatched, mapped/nested/noncollection slots stay
    refused. The original reduction plan and collection-drain action retain
    their argument position/category/kind and untouched source syntax.
    These finite interface laws do not prove collection recognition or parsing.
*)
From Stdlib Require Import Bool.
Module OwnedSeparatedCollectionSlot.
Section Slots.
Context {Category Kind Separator Plan : Type}.
Record Payload := { category : Category; kind : Kind; keyed : bool }.
Inductive Slot :=
| Collection (payload : Payload)
| Separated (separator : Separator) (source : Slot)
| Other.
Definition original_view slot :=
  match slot with Collection payload => Some payload | _ => None end.
Definition borrowed_view slot :=
  match slot with
  | Separated _ (Collection payload) => Some payload
  | _ => original_view slot
  end.
Definition admit (same_category : Category -> bool) (same_kind : Kind -> bool) slot :=
  match borrowed_view slot with
  | Some payload => negb (keyed payload) && same_category (category payload) && same_kind (kind payload)
  | None => false
  end.
Definition carry_source_and_plan (slot : Slot) (plan : Plan) := (slot, plan).
Theorem existing_direct_slot_is_unchanged : forall payload,
  borrowed_view (Collection payload) = original_view (Collection payload).
Proof. reflexivity. Qed.
Theorem direct_separated_slot_has_same_payload : forall separator payload,
  borrowed_view (Separated separator (Collection payload)) = Some payload.
Proof. reflexivity. Qed.
Theorem source_wrapper_and_plan_are_not_rewritten : forall separator payload plan,
  carry_source_and_plan (Separated separator (Collection payload)) plan =
  (Separated separator (Collection payload), plan).
Proof. reflexivity. Qed.
Theorem category_and_kind_checks_are_unchanged : forall cat_match kind_match separator payload,
  admit cat_match kind_match (Separated separator (Collection payload)) =
  admit cat_match kind_match (Collection payload).
Proof. reflexivity. Qed.
Theorem keyed_slot_stays_refused : forall cat_match kind_match separator cat k,
  admit cat_match kind_match (Separated separator (Collection {| category := cat; kind := k; keyed := true |})) = false.
Proof. reflexivity. Qed.
Theorem nested_wrapper_is_not_flattened : forall separator other source,
  borrowed_view (Separated separator (Separated other source)) = None.
Proof. reflexivity. Qed.
Theorem noncollection_wrapper_stays_refused : forall separator,
  borrowed_view (Separated separator Other) = None.
Proof. reflexivity. Qed.
End Slots.
Print Assumptions existing_direct_slot_is_unchanged.
Print Assumptions direct_separated_slot_has_same_payload.
Print Assumptions source_wrapper_and_plan_are_not_rewritten.
Print Assumptions category_and_kind_checks_are_unchanged.
Print Assumptions keyed_slot_stays_refused.
Print Assumptions nested_wrapper_is_not_flattened.
Print Assumptions noncollection_wrapper_stays_refused.
End OwnedSeparatedCollectionSlot.
