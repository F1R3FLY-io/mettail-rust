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

Import GeneratedChildTraversal.GeneratedChildTraversal.
Import AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.

(** These expressions select the existing driver entry constructors; they do
    not define another execution relation or manufacture a callback result. *)
Definition callback_entry_task owner callback (input : option comparison) :=
  match input with None => Start owner callback | Some _ => Resume owner callback end.
Definition callback_entry_mode (input : option comparison) :=
  match input with None => Run | Some ordering => completion_mode ordering end.

Section ExistingCallbackEntry.
Context {SourceState : Type}.
Variable arm_source :
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  SourceState -> HandlerExit -> list Observation -> SourceState -> Prop.
Variable callback_source : nat -> nat -> option comparison -> SourceState ->
  CoreReply -> list Observation -> SourceState -> Prop.
Variable discard_source : Task -> SourceState -> SourceState -> Prop.
Local Notation Trace := (@ChildTraversal SourceState arm_source callback_source discard_source).

Theorem an_actual_callback_entry_exposes_its_original_call_and_continuation :
  forall owner callback input count before events result after,
  Trace [] count (callback_entry_mode input) [callback_entry_task owner callback input]
    before events result after ->
  exists reply core_events next later_count later_events,
    callback_source owner callback input before reply core_events next /\
    Trace [] later_count (reply_mode reply) (reply_prefix owner callback reply)
      next later_events result after /\
    count = S later_count /\
    events = resume_observations owner input core_events reply ++ later_events.
Proof.
  intros owner callback input count before events result after TRACE.
  destruct input as [[| |]|];
    cbn [callback_entry_mode callback_entry_task completion_mode] in TRACE.
  all: inversion TRACE as [| |later_count mode head rest state first_events
      next_mode prefix next later_events actual last STEP TAIL]; subst.
  all: rewrite !app_nil_r in STEP.
  all: inversion STEP; subst; cbn [not_resume] in *; try discriminate.
  all: rewrite !app_nil_r in *.
  all: do 5 eexists; repeat split; try reflexivity; eassumption.
Qed.
End ExistingCallbackEntry.

Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedSourceRowComparison.GeneratedSourceRowComparison.

Section OriginalRequestedChild.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variables maximum owner_ceiling : nat.
Variable category_callback : Cat -> nat.
Variables uid_digest binder_digest : nat -> nat.
Local Notation Position := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Variable signature : Cat -> list (@Row Cat).
Variable observe : forall category, Term category -> SourceObservation signature Term category.
Variable alias : forall category, Term category -> Term category -> bool.
Local Notation Cells := (@State Cat Term).
Local Notation owned_map := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.owned_map Cat Term).
Local Notation OriginalArm := (@GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.arm_source
  Cat Term maximum owner_ceiling category_callback uid_digest binder_digest lookup signature observe).
Local Notation OriginalCore := (@core_source Cat Term maximum alias category_callback lookup).
Local Notation OriginalDiscard := (@GeneratedMapSourceOwnership.GeneratedMapSourceOwnership.discard_source Cat Term).
Local Notation Trace := (@ChildTraversal Cells OriginalArm OriginalCore OriginalDiscard).
Local Notation RawState :=
  (fun category : Cat => @GeneratedMapCoreSource.GeneratedMapCoreSource.RawMapState (Term category) (Term category)).
Local Notation RawRequest := GeneratedMapCoreSource.GeneratedMapCoreSource.RawRequest.
Local Notation RawRequests := GeneratedMapCoreSource.GeneratedMapCoreSource.Requests.
Variable children : Cat -> Ordered.
Variable next : forall category, Term category -> option (carrier (children category)).
Local Notation AnswerCertificate :=
  (fun category => @GeneratedAdmittedMapDialogue.GeneratedAdmittedMapDialogue.original_answer_has_projected_operands
    (Term category) (Term category) (children category) (children category) (next category) (next category)).
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  next category left = Some left_key -> next category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = comparison_function (children category) left_key right_key.

(** The answer is justified for these original operands, including pairs from
    within one sorting roster. Parked-state preservation is derived from the
    original move discipline, not included in the child induction premise. *)
Theorem an_original_requested_child_returns_its_certified_answer_and_exact_parked_payload :
  forall category owner callback position role
    (request : @RawRequest (Term category) (Term category)) answer
    (raw : RawState category) buffers count before events result after,
  original_reply_binding Term lookup category (RawRequests request) (Requests role position) ->
  AnswerCertificate category (request, answer) ->
  nth_error before owner = Some (Some (callback, owned_map category buffers raw)) ->
  Trace [Resume owner callback] count Run [child_task position] before events result after ->
  result = answer /\
  nth_error after owner = Some (Some (callback, owned_map category buffers raw)).
Proof.
  intros category owner callback position role request answer raw buffers count before events result after
    BINDING CERTIFICATE STORED CHILD.
  assert (ISOLATED : Trace [] count Run [child_task position] before events result after).
  { eapply finite_child_traversal_strips_to_a_genuine_isolated_trace; exact CHILD. }
  split.
  - destruct request, role; cbn [original_reply_binding] in BINDING; try contradiction;
      destruct CERTIFICATE as [left_key [right_key [LEFT [RIGHT ANSWER]]]];
      cbn [fst snd] in ANSWER;
      rewrite <- ANSWER; eapply lower_height_completed_child; eassumption.
  - eapply GeneratedMapOwnerTraversal.GeneratedMapOwnerTraversal.a_completed_child_retains_its_exact_parent_resume_payload
      with (outer := []) (prefix := [child_task position]); [exact CHILD| |exact STORED].
    change (NoDup [owner] /\ Forall (live_owner before) [owner]).
    split.
    + constructor; [intro ABSENT; inversion ABSENT|constructor].
    + constructor; [exists callback, (owned_map category buffers raw); exact STORED|constructor].
Qed.
Variable category_eq_dec : forall lhs rhs : Cat, {lhs = rhs} + {lhs <> rhs}.
Local Notation RawDialogue := GeneratedMapCoreSource.GeneratedMapCoreSource.RawDialogue.
Local Notation Ingress := GeneratedMapCoreSource.GeneratedMapCoreSource.Ingress.
Local Notation ReturnReply := GeneratedMapCoreSource.GeneratedMapCoreSource.ReturnReply.
Local Notation RawCompletes := GeneratedMapCoreSource.GeneratedMapCoreSource.Completes.

(** The retained dialogue is advanced only by the actual completed child.
    First-return determinism identifies the precise returned native payload;
    the preceding child theorem preserves that payload until its Resume. *)
Theorem an_actual_map_segment_follows_its_retained_original_dialogue :
  forall category answers input (raw raw_final : RawState category) expected
    owner callback buffers count before events result after,
  @RawDialogue (Term category) (Term category) (alias category) (alias category) maximum
    (Ingress input) raw answers (ReturnReply (RawCompletes expected)) raw_final ->
  Forall (AnswerCertificate category) answers ->
  nth_error before owner = Some (Some (callback, owned_map category buffers raw)) ->
  Trace [] count (callback_entry_mode input) [callback_entry_task owner callback input]
    before events result after ->
  result = expected.
Proof.
  intros category answers. induction answers as [|[request answer] rest IH];
    intros input raw raw_final expected owner callback buffers count before events result after
      DIALOGUE CERTIFICATE STORED TRAVERSAL.
  all: destruct (@an_actual_callback_entry_exposes_its_original_call_and_continuation
    Cells OriginalArm OriginalCore OriginalDiscard owner callback input count before events result after TRAVERSAL)
    as [reply [core_events [callback_after [remaining [later_events [CALL [CONT [COUNT EVENTS]]]]]]]].
  all: destruct (@an_actual_callback_uses_the_exact_stored_typed_native_state
    Cat category_eq_dec Term maximum alias category_callback lookup
    owner callback input before reply core_events callback_after CALL category buffers raw STORED)
    as [CALLBACK [native_reply [native_after [RAW [BINDING CELL]]]]].
  all: pose proof
    (GeneratedMapCoreDeterminism.GeneratedMapCoreDeterminism.actual_resume_keeps_the_exact_retained_dialogue_frontier
      (alias category) (alias category) maximum _ _ _ _ _ DIALOGUE _ _ RAW) as FRONTIER.
  - destruct FRONTIER as [RETURN FINAL]. subst native_reply.
    destruct reply as [role position|ordering]; cbn [original_reply_binding] in BINDING; try contradiction.
    subst ordering. destruct expected; inversion CONT; reflexivity.
  - destruct FRONTIER as [RETURN DIALOGUE_TAIL]. subst native_reply.
    assert (REQUESTED : exists role position, reply = Requests role position).
    { destruct request, reply; cbn [original_reply_binding] in BINDING; try contradiction;
        do 2 eexists; reflexivity. }
    destruct REQUESTED as [role [position ->]].
    destruct CELL as [next_buffers STORED_NEXT].
    apply Forall_cons_iff in CERTIFICATE as [HEAD TAIL].
    destruct (@running_child_trace_splits_before_its_untouched_frame
      Cells OriginalArm OriginalCore OriginalDiscard remaining
      [child_task position] [Resume owner callback] callback_after later_events result after CONT)
      as [child_count [continuation_count [child_result [middle [child_events [continuation_events
        [CHILD [CONTINUE [COUNTS SPLIT_EVENTS]]]]]]]]].
    destruct (an_original_requested_child_returns_its_certified_answer_and_exact_parked_payload
      category owner callback position role request answer native_after next_buffers
      child_count callback_after child_events child_result middle BINDING HEAD STORED_NEXT CHILD)
      as [ANSWER RESTORED]. subst child_result.
    eapply IH; [exact DIALOGUE_TAIL|exact TAIL|exact RESTORED|exact CONTINUE].
Qed.
Hypothesis original_alias_identity : forall category (lhs rhs : Term category),
  alias category lhs rhs = true -> lhs = rhs.
Local Notation initial_map := GeneratedMapCoreSource.GeneratedMapCoreSource.initial_map.

(** This is the initial Map field certificate consumed by the original row
    batch theorem. The dialogue and every requested answer are constructed
    from successful original projections, not supplied as a result premise. *)
Theorem an_actual_original_map_start_returns_its_projected_map_comparison :
  forall category owner buffers left right left_key right_key count before events result after,
  length left <= maximum -> length right <= maximum ->
  project_base Term uid_digest binder_digest children next (MapPairs category) left = Some left_key ->
  project_base Term uid_digest binder_digest children next (MapPairs category) right = Some right_key ->
  nth_error before owner = Some (Some (category_callback category,
    owned_map category buffers (initial_map maximum left right (length left) (length right)))) ->
  Trace [] count Run [Start owner (category_callback category)] before events result after ->
  result = comparison_function (base_order children (MapPairs category)) left_key right_key.
Proof.
  intros category owner buffers left right left_key right_key count before events result after
    LEFT_BOUND RIGHT_BOUND LEFT RIGHT STORED TRAVERSAL.
  destruct (successful_map_projection_keeps_original_pairing_before_canonicalization
    Term uid_digest binder_digest children next category left left_key LEFT)
    as [left_keys [LEFT_PAIRS LEFT_CANONICAL]].
  destruct (successful_map_projection_keeps_original_pairing_before_canonicalization
    Term uid_digest binder_digest children next category right right_key RIGHT)
    as [right_keys [RIGHT_PAIRS RIGHT_CANONICAL]].
  destruct (@GeneratedAdmittedMapDialogue.GeneratedAdmittedMapDialogue.successful_original_map_projections_construct_a_certified_raw_dialogue
    (Term category) (Term category) (children category) (children category) (next category) (next category)
    (alias category) (alias category) (original_alias_identity category) (original_alias_identity category)
    maximum left right left_keys right_keys left_key right_key LEFT_BOUND RIGHT_BOUND
    LEFT_PAIRS RIGHT_PAIRS LEFT_CANONICAL RIGHT_CANONICAL)
    as [answers [raw_final [DIALOGUE CERTIFICATE]]].
  eapply an_actual_map_segment_follows_its_retained_original_dialogue
    with (category := category) (answers := answers) (input := None) (raw_final := raw_final);
    [exact DIALOGUE|exact CERTIFICATE|exact STORED|exact TRAVERSAL].
Qed.
End OriginalRequestedChild.

Print Assumptions equal_original_owner_payloads_have_the_same_category.
Print Assumptions equal_same_category_owners_have_the_exact_same_native_state.
Print Assumptions the_taken_owner_is_the_original_complete_stored_payload.
Print Assumptions an_actual_callback_uses_the_exact_stored_typed_native_state.
Print Assumptions an_actual_callback_entry_exposes_its_original_call_and_continuation.
Print Assumptions an_original_requested_child_returns_its_certified_answer_and_exact_parked_payload.
Print Assumptions an_actual_map_segment_follows_its_retained_original_dialogue.
Print Assumptions an_actual_original_map_start_returns_its_projected_map_comparison.
End GeneratedMapActualSegment.
