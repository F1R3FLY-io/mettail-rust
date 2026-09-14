(** Actual Map callback segments, using original source traces and raw dialogue.
    Category equality is decidable because generated categories have finite
    declared IDs/names. The decision procedure below is explicit proof input;
    it is not a runtime branch. Eqdep_dec derives same-index dependent-pair
    injection from that decision, without a proof-irrelevance or Eqdep axiom.
    Callback tags need not be injective: the existing typed owner payload,
    not a physical function-pointer identity, determines the category.
    Term/payload equality is not assumed decidable. No new executor, source
    grammar, comparison function, or whole-Map result premise is introduced. *)
From Stdlib Require Import List Logic.Eqdep_dec.
From RhoBridge Require Import GeneratedMapSourceOwnership GeneratedCollectionOwnerFrame
  GeneratedMapOwnerTraversal GeneratedMapCoreDeterminism GeneratedAdmittedMapDialogue.
Import ListNotations.
Import GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.
Import GeneratedCollectionOwnerFrame.GeneratedCollectionOwnerFrame.

Module GeneratedMapActualSegment.
Section OriginalTypedPayload.
Context {Cat : Type}.
Variable category_eq_dec : forall left right : Cat, {left = right} + {left <> right}.
Variable Term : Cat -> Type.
Local Notation RawState :=
  (fun category : Cat => @GeneratedMapCoreSource.GeneratedMapCoreSource.RawMapState (Term category) (Term category)).
Local Notation Owned := (@owned_map Cat Term).
Local Notation Core := (@MapCore Cat Term).
Local Notation Owner := (@MapOwner Cat Term).
Local Notation Cells := (@State Cat Term).
Local Notation take_owner := (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.take_owner Core).

Theorem equal_original_owner_payloads_have_the_same_category :
  forall left_category right_category left_buffers right_buffers
    (left_raw : RawState left_category) (right_raw : RawState right_category),
  Owned left_category left_buffers left_raw = Owned right_category right_buffers right_raw ->
  left_category = right_category.
Proof.
  intros left_category right_category left_buffers right_buffers left_raw right_raw SAME.
  pose proof (f_equal
    (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.core_state Core) SAME) as PACKED.
  exact (f_equal (@projT1 Cat (fun category => RawState category)) PACKED).
Qed.

Theorem equal_same_category_owners_have_the_exact_same_native_state :
  forall category left_buffers right_buffers (left_raw right_raw : RawState category),
  Owned category left_buffers left_raw = Owned category right_buffers right_raw ->
  left_raw = right_raw.
Proof.
  intros category left_buffers right_buffers left_raw right_raw SAME.
  pose proof (f_equal
    (@AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.core_state Core) SAME) as PACKED.
  exact (@inj_pair2_eq_dec Cat category_eq_dec (fun category => RawState category)
    category left_raw right_raw PACKED).
Qed.

Theorem the_taken_owner_is_the_original_complete_stored_payload :
  forall owner tag (before : Cells) returned emptied category buffers (raw : RawState category),
  nth_error before owner = Some (Some (tag, Owned category buffers raw)) ->
  take_owner owner tag before = Some (returned, emptied) ->
  returned = Owned category buffers raw.
Proof.
  intros owner tag before returned emptied category buffers raw STORED TAKE.
  pose proof (proj1 (successful_take_moves_the_original_payload_and_empties_its_cell
    owner tag before returned emptied TAKE)) as FOUND.
  rewrite STORED in FOUND. injection FOUND as PAYLOAD. symmetry. exact PAYLOAD.
Qed.
End OriginalTypedPayload.

Print Assumptions equal_original_owner_payloads_have_the_same_category.
Print Assumptions equal_same_category_owners_have_the_exact_same_native_state.
Print Assumptions the_taken_owner_is_the_original_complete_stored_payload.
End GeneratedMapActualSegment.
