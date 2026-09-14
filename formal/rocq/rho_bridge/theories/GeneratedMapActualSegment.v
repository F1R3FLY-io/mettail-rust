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
Variable maximum : nat.
Variable alias : forall category, Term category -> Term category -> bool.
Variable category_callback : Cat -> nat.
Variable lookup : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  option { category : Cat & (Term category * Term category)%type }.
Local Notation SourceCore := (@core_source Cat Term maximum alias category_callback lookup).
Local Notation RawResume := GeneratedMapCoreSource.GeneratedMapCoreSource.RawResume.
Local Notation RawReply := GeneratedMapCoreSource.GeneratedMapCoreSource.RawReply.
Local Notation RawRequests := GeneratedMapCoreSource.GeneratedMapCoreSource.Requests.
Local Notation RawCompletes := GeneratedMapCoreSource.GeneratedMapCoreSource.Completes.
Local Notation RawPrimary := GeneratedMapCoreSource.GeneratedMapCoreSource.PrimaryRequest.
Local Notation RawSecondary := GeneratedMapCoreSource.GeneratedMapCoreSource.SecondaryRequest.
Local Notation Requests := GeneratedChildTraversal.GeneratedChildTraversal.Requests.
Local Notation Completes := GeneratedChildTraversal.GeneratedChildTraversal.Completes.
Local Notation Primary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary.
Local Notation Secondary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary.
Local Notation pair_at := (GeneratedSourceRowComparison.GeneratedSourceRowComparison.pair_at Term lookup).

(** The adapter restores precisely the typed pair carried by the raw request.
    This relation contains no expected comparison or completed-child result. *)
Definition original_reply_binding category
    (native_reply : @RawReply (Term category) (Term category))
    (emitted : GeneratedChildTraversal.GeneratedChildTraversal.CoreReply) : Prop :=
  match native_reply, emitted with
  | RawRequests (RawPrimary lhs rhs), Requests Primary position => pair_at category position lhs rhs
  | RawRequests (RawSecondary lhs rhs), Requests Secondary position => pair_at category position lhs rhs
  | RawCompletes result, Completes actual => result = actual
  | _, _ => False end.

Theorem an_actual_callback_uses_the_exact_stored_typed_native_state :
  forall owner callback input before emitted events after,
  SourceCore owner callback input before emitted events after ->
  forall category buffers (raw : RawState category),
  nth_error before owner = Some (Some (callback, Owned category buffers raw)) ->
  callback = category_callback category /\
  exists native_reply native_after,
    @RawResume (Term category) (Term category) (alias category) (alias category) maximum
      raw input native_reply native_after /\
    original_reply_binding category native_reply emitted /\
    match native_reply with
    | RawRequests _ => exists next_buffers,
        nth_error after owner = Some (Some (callback, Owned category next_buffers native_after))
    | RawCompletes _ => nth_error after owner = Some None end.
Proof.
  intros owner callback input before emitted events after SOURCE.
  destruct SOURCE as [category owner input before emptied after buffers next_buffers raw next_raw left right position TAKE RAW PAIR REFILL
    |category owner input before emptied after buffers next_buffers raw next_raw left right position TAKE RAW PAIR REFILL
    |category owner input before emptied after buffers next_buffers raw next_raw result TAKE RAW DONE];
    intros original_category original_buffers original_raw STORED.
  all: pose proof (the_taken_owner_is_the_original_complete_stored_payload
    owner (category_callback category) before (Owned category buffers raw) emptied
    original_category original_buffers original_raw STORED TAKE) as OWNER.
  all: pose proof (equal_original_owner_payloads_have_the_same_category
    category original_category buffers original_buffers raw original_raw OWNER) as CATEGORY.
  all: subst original_category.
  all: pose proof (equal_same_category_owners_have_the_exact_same_native_state
    category buffers original_buffers raw original_raw OWNER) as NATIVE.
  all: subst original_raw.
  - split; [reflexivity|]. exists (RawRequests (RawPrimary left right)), next_raw.
    split; [exact RAW|]. split; [exact PAIR|]. exists next_buffers.
    eapply successful_write_contains_exactly_the_tagged_payload; exact REFILL.
  - split; [reflexivity|]. exists (RawRequests (RawSecondary left right)), next_raw.
    split; [exact RAW|]. split; [exact PAIR|]. exists next_buffers.
    eapply successful_write_contains_exactly_the_tagged_payload; exact REFILL.
  - change (Some emptied = Some after) in DONE. injection DONE as <-.
    split; [reflexivity|]. exists (RawCompletes result), next_raw.
    split; [exact RAW|]. split; [reflexivity|].
    exact (proj1 (proj2 (successful_take_moves_the_original_payload_and_empties_its_cell
      owner (category_callback category) before (Owned category buffers raw) emptied TAKE))).
Qed.
End OriginalTypedPayload.

Print Assumptions equal_original_owner_payloads_have_the_same_category.
Print Assumptions equal_same_category_owners_have_the_exact_same_native_state.
Print Assumptions the_taken_owner_is_the_original_complete_stored_payload.
Print Assumptions an_actual_callback_uses_the_exact_stored_typed_native_state.
End GeneratedMapActualSegment.
