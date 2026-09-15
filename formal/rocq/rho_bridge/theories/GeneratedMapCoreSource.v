(** Comparator-free successful source control for CollectionCmpPda entries.

    Source: runtime/src/collection_cmp_pda.rs, resume_with, request_item_comparison,
    request_secondary_or_accept, accept_term_comparison, accept_item_comparison,
    current_left/right, advance_equal_run, and MergeSortPda step/accept/reset_run.
    The records below project the existing Box payload. Control labels denote
    positions in its existing call stack; they are not additional stored fields,
    an owner registry, a runtime interpreter, or a replacement sorting recipe.

    Raw control has no key comparator, class view, or expected-result oracle.
    In particular every Ordering is accepted at a pending secondary request or
    waiting merge accept. The separate proof section recovers certified pair
    behavior only after the actual answers have been established by child
    traversal. Primary Equal may request Secondary without copying a record.

    Entry payloads supply their optional secondary and original repetitions;
    Map is the present-secondary, unit-repetition specialization. Original totals
    remain stored and exhaustion compares those totals: no normalization or
    source-enumeration completeness follows from this projection. The two
    remaining counters are still represented, including left initialization
    before discovering that the right roster is exhausted.

    Payload projections describe already constructed entries. Association
    with a repeated-item producer requires its successful construction laws,
    including positive repetitions. Arbitrary projections here do not prove
    acceptance of zero counts, termination, or successful policy admission.

    This file concerns successful native control. Protocol errors, admission,
    overflow, owned-slot inventory and refusal cleanup retain their existing
    committed models. A raw relation with no successful derivation for invalid
    ingress is not an assertion that the implementation silently accepts it.
    Box-in-task interpretation and parked-owner noninterference must use those
    ownership laws; task-list frame preservation alone does not prove them.

    The lifting theorems construct a complete raw source dialogue from the
    existing sequenced MapEvents witness through actual copies, reset/swap,
    scratch release and phase changes. Each dialogue exposes its first return
    and exact response continuation without crossing a return internally.
    First-return determinism and association with the actual generated
    traversal, reached parked Box and lower-height child-answer theorem remain
    separate obligations. No completed-core hypothesis replaces this lifting.
    Source association of these projections with Rust is a source audit, not
    a theorem about Rust compilation, arbitrary callbacks, or allocator work. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import MergeSortPdaCursor MergeSortPdaNativeRun
  NativeMapRunSuspension CollectionPairAndUnitLexResults
  AdmittedGeneratedCollectionScheduling.
From RuntimeGrammar Require Import SemanticComparisonLaws.
Import ListNotations.
Import MergeSortPdaCursor.MergeSortPdaCursor.

Module GeneratedMapCoreSource.

Section MergeControl.
Context {Entry : Type}.

Record RawMergeState := {
  merge_source : list Entry;
  merge_target : option (list Entry);
  merge_width : nat;
  merge_cursor : Cursor;
  merge_waiting : bool;
  merge_done : bool
}.

Definition merge_state source target width cursor waiting done : RawMergeState :=
  {| merge_source := source; merge_target := target; merge_width := width;
     merge_cursor := cursor; merge_waiting := waiting; merge_done := done |}.

Definition initial_merge maximum source :=
  merge_state source None 1 (reset_cursor maximum (length source) 0 1)
    false (length source <? 2).

Definition merge_set_target state target :=
  merge_state (merge_source state) target (merge_width state)
    (merge_cursor state) (merge_waiting state) (merge_done state).

Definition merge_set_waiting state waiting :=
  merge_state (merge_source state) (merge_target state) (merge_width state)
    (merge_cursor state) waiting (merge_done state).

Definition merge_after_copy state cursor target :=
  merge_state (merge_source state) (Some target) (merge_width state)
    cursor false (merge_done state).

(** Source updates start=end before the pass-boundary test. On a final swap
    it breaks WITHOUT resetting the other cursor fields. Their dead values
    are preserved here; valid_cursor is not imposed on this terminal record. *)
Definition cursor_after_run cursor :=
  {| run_start := run_end cursor; run_middle := run_middle cursor;
     run_end := run_end cursor; left_index := left_index cursor;
     right_index := right_index cursor; output_index := output_index cursor |}.

Definition merge_after_run maximum state completed :=
  let source := merge_source state in
  let cursor := merge_cursor state in
  let width := merge_width state in
  if run_end cursor <? length source then
    merge_state source (Some completed) width
      (reset_cursor maximum (length source) (run_end cursor) width) false false
  else
    let next_width := saturated_double maximum width in
    if length completed <=? next_width then
      merge_state completed (Some source) next_width (cursor_after_run cursor) false true
    else
      merge_state completed (Some source) next_width
        (reset_cursor maximum (length completed) 0 next_width) false false.

Definition raw_merge_accept state ordering : option RawMergeState :=
  if merge_waiting state then
    match merge_target state with
    | None => None
    | Some target =>
      match copy_record (accept_side ordering) (merge_cursor state)
          (merge_source state) target with
      | None => None
      | Some (cursor, next) => Some (merge_after_copy state cursor next)
      end
    end
  else None.

Inductive RawMergeSilent (maximum : nat) : RawMergeState -> RawMergeState -> Prop :=
| MergeAllocatesScratch : forall state,
    merge_waiting state = false -> merge_done state = false ->
    merge_target state = None ->
    RawMergeSilent maximum state (merge_set_target state (Some (merge_source state)))
| MergeLeftTail : forall state target next_cursor next,
    merge_waiting state = false -> merge_done state = false ->
    merge_target state = Some target ->
    can_copy FromLeft (merge_cursor state) ->
    ~ can_copy FromRight (merge_cursor state) ->
    copy_record FromLeft (merge_cursor state) (merge_source state) target =
      Some (next_cursor, next) ->
    RawMergeSilent maximum state (merge_after_copy state next_cursor next)
| MergeRightTail : forall state target next_cursor next,
    merge_waiting state = false -> merge_done state = false ->
    merge_target state = Some target ->
    ~ can_copy FromLeft (merge_cursor state) ->
    can_copy FromRight (merge_cursor state) ->
    copy_record FromRight (merge_cursor state) (merge_source state) target =
      Some (next_cursor, next) ->
    RawMergeSilent maximum state (merge_after_copy state next_cursor next)
| MergeEndsRun : forall state target,
    merge_waiting state = false -> merge_done state = false ->
    merge_target state = Some target ->
    ~ can_copy FromLeft (merge_cursor state) ->
    ~ can_copy FromRight (merge_cursor state) ->
    RawMergeSilent maximum state (merge_after_run maximum state target).

Inductive RawMergeReply := MergeRequests (lhs rhs : Entry) | MergeCompletes.

Inductive RawMergeStep (maximum : nat) :
    RawMergeState -> RawMergeReply -> RawMergeState -> Prop :=
| MergeStepDone : forall state,
    merge_waiting state = false -> merge_done state = true ->
    RawMergeStep maximum state MergeCompletes state
| MergeStepRequests : forall state target lhs rhs,
    merge_waiting state = false -> merge_done state = false ->
    merge_target state = Some target ->
    MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest
      (merge_source state) (merge_cursor state) lhs rhs ->
    RawMergeStep maximum state (MergeRequests lhs rhs) (merge_set_waiting state true)
| MergeStepInternal : forall state middle reply next,
    RawMergeSilent maximum state middle -> RawMergeStep maximum middle reply next ->
    RawMergeStep maximum state reply next.

Theorem arbitrary_waiting_response_copies_its_selected_side :
  forall source target width cursor done ordering next,
  copy_record (accept_side ordering) cursor source target =
    Some (advance (accept_side ordering) cursor, next) ->
  raw_merge_accept (merge_state source (Some target) width cursor true done) ordering =
    Some (merge_state source (Some next) width
      (advance (accept_side ordering) cursor) false done).
Proof.
  intros source target width cursor done ordering next COPY.
  unfold raw_merge_accept, merge_state.
  cbn [merge_waiting merge_target merge_cursor merge_source].
  rewrite COPY. reflexivity.
Qed.

Theorem no_pending_merge_does_not_accept_a_response : forall state ordering,
  merge_waiting state = false -> raw_merge_accept state ordering = None.
Proof. intros state ordering WAIT. unfold raw_merge_accept. now rewrite WAIT. Qed.

Theorem successful_raw_accept_keeps_source_and_width : forall state ordering next,
  raw_merge_accept state ordering = Some next ->
  merge_source next = merge_source state /\ merge_width next = merge_width state /\
  merge_waiting next = false.
Proof.
  intros state ordering next ACCEPT. unfold raw_merge_accept in ACCEPT.
  destruct (merge_waiting state); [|discriminate].
  destruct (merge_target state) as [target|]; [|discriminate].
  destruct (copy_record (accept_side ordering) (merge_cursor state)
    (merge_source state) target) as [[cursor items]|]; [|discriminate].
  inversion ACCEPT; subst next. repeat split; reflexivity.
Qed.

Theorem nonfinal_run_reset_uses_the_actual_absolute_end :
  forall maximum state target,
  run_end (merge_cursor state) < length (merge_source state) ->
  merge_after_run maximum state target =
    merge_state (merge_source state) (Some target) (merge_width state)
      (reset_cursor maximum (length (merge_source state))
        (run_end (merge_cursor state)) (merge_width state)) false false.
Proof.
  intros maximum state target LIVE. unfold merge_after_run.
  rewrite (proj2 (Nat.ltb_lt _ _) LIVE). reflexivity.
Qed.

Theorem final_swap_preserves_the_unreset_dead_cursor :
  forall maximum state target,
  length (merge_source state) <= run_end (merge_cursor state) ->
  length target <= saturated_double maximum (merge_width state) ->
  merge_after_run maximum state target =
    merge_state target (Some (merge_source state))
      (saturated_double maximum (merge_width state))
      (cursor_after_run (merge_cursor state)) false true.
Proof.
  intros maximum state target END FINISH. unfold merge_after_run.
  rewrite (proj2 (Nat.ltb_ge _ _) END), (proj2 (Nat.leb_le _ _) FINISH).
  reflexivity.
Qed.
End MergeControl.

Inductive RawPhase := Lead | SortLeft | SortRight | Lexicographic | Done.
Inductive RawDestination := ToLeftSort | ToRightSort | ToLexicographic.

Section MapControl.
Context {Key Value : Type}.
Local Notation Entry := (Key * Value)%type.

Inductive RawPending :=
| PendingPrimary (lhs rhs : Entry) (destination : RawDestination)
| PendingSecondary (destination : RawDestination).

Record RawMapState := {
  map_left : @RawMergeState Entry;
  map_right : @RawMergeState Entry;
  map_phase : RawPhase;
  map_pending : option RawPending;
  map_lead : comparison;
  map_left_total : nat; map_right_total : nat;
  map_left_index : nat; map_right_index : nat;
  map_left_remaining : nat; map_right_remaining : nat
}.

Definition map_state left_sort right_sort phase pending lead lt rt li ri lr rr :=
  {| map_left := left_sort; map_right := right_sort; map_phase := phase;
     map_pending := pending; map_lead := lead;
     map_left_total := lt; map_right_total := rt;
     map_left_index := li; map_right_index := ri;
     map_left_remaining := lr; map_right_remaining := rr |}.

Definition initial_collection maximum left_items right_items lead left_total right_total :=
  map_state (initial_merge maximum left_items) (initial_merge maximum right_items)
    Lead None lead left_total right_total 0 0 0 0.

Definition initial_map maximum left_items right_items left_total right_total :=
  initial_collection maximum left_items right_items Eq left_total right_total.

Theorem map_initialization_is_the_unit_specialization :
  forall maximum left_items right_items left_total right_total,
  initial_map maximum left_items right_items left_total right_total =
    map_state (initial_merge maximum left_items) (initial_merge maximum right_items)
      Lead None Eq left_total right_total 0 0 0 0.
Proof. reflexivity. Qed.

Definition set_pending state pending :=
  map_state (map_left state) (map_right state) (map_phase state) pending (map_lead state)
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).
Definition set_phase state phase :=
  map_state (map_left state) (map_right state) phase (map_pending state) (map_lead state)
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).
Definition set_left state left_sort :=
  map_state left_sort (map_right state) (map_phase state) (map_pending state) (map_lead state)
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).
Definition set_right state right_sort :=
  map_state (map_left state) right_sort (map_phase state) (map_pending state) (map_lead state)
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).
Definition set_lead state ordering :=
  map_state (map_left state) (map_right state) Lead (map_pending state) ordering
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).
Definition set_lex state li ri lr rr :=
  map_state (map_left state) (map_right state) (map_phase state) (map_pending state) (map_lead state)
    (map_left_total state) (map_right_total state) li ri lr rr.

(** current_left/right restore the fetched original repetition count only
    when its remaining counter is zero. The existing Map entrypoints remain
    unit-count wrappers; neither this helper nor its caller invents a count. *)
Definition initialize_left_remaining_with count state :=
  set_lex state (map_left_index state) (map_right_index state)
    (if map_left_remaining state =? 0 then count else map_left_remaining state)
    (map_right_remaining state).
Definition initialize_both_remaining_with left_count right_count state :=
  set_lex state (map_left_index state) (map_right_index state)
    (if map_left_remaining state =? 0 then left_count else map_left_remaining state)
    (if map_right_remaining state =? 0 then right_count else map_right_remaining state).
Definition initialize_left_remaining state := initialize_left_remaining_with 1 state.
Definition initialize_both_remaining state := initialize_both_remaining_with 1 1 state.

Theorem counted_left_restoration_is_original : forall state,
  initialize_left_remaining state =
    set_lex state (map_left_index state) (map_right_index state)
      (if map_left_remaining state =? 0 then 1 else map_left_remaining state)
      (map_right_remaining state).
Proof. reflexivity. Qed.

Theorem counted_both_restoration_is_original : forall state,
  initialize_both_remaining state =
    set_lex state (map_left_index state) (map_right_index state)
      (if map_left_remaining state =? 0 then 1 else map_left_remaining state)
      (if map_right_remaining state =? 0 then 1 else map_right_remaining state).
Proof. reflexivity. Qed.

Theorem counted_left_restoration_exposes_the_original_counter : forall count state,
  map_left_remaining (initialize_left_remaining_with count state) =
    (if map_left_remaining state =? 0 then count else map_left_remaining state) /\
  map_right_remaining (initialize_left_remaining_with count state) =
    map_right_remaining state.
Proof. intros. split; reflexivity. Qed.

Theorem counted_both_restoration_exposes_the_original_counters :
  forall left_count right_count state,
  map_left_remaining (initialize_both_remaining_with left_count right_count state) =
    (if map_left_remaining state =? 0 then left_count else map_left_remaining state) /\
  map_right_remaining (initialize_both_remaining_with left_count right_count state) =
    (if map_right_remaining state =? 0 then right_count else map_right_remaining state).
Proof. intros. split; reflexivity. Qed.

Definition advance_equal state :=
  let consumed := Nat.min (map_left_remaining state) (map_right_remaining state) in
  let lr := map_left_remaining state - consumed in
  let rr := map_right_remaining state - consumed in
  set_lex state
    (if lr =? 0 then S (map_left_index state) else map_left_index state)
    (if rr =? 0 then S (map_right_index state) else map_right_index state) lr rr.

(** This projection connects the existing raw-state update to the shared
    min/subtract/zero-test operation without introducing a second algorithm. *)
Definition raw_lex_cursor state :
    CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.UnitLexCursor :=
  {| CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.lex_left_index := map_left_index state;
     CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.lex_right_index := map_right_index state;
     CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.lex_left_remaining := map_left_remaining state;
     CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.lex_right_remaining := map_right_remaining state |}.

Theorem raw_equal_advance_reuses_existing_count_operation : forall state,
  raw_lex_cursor (advance_equal state) =
    CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.advance_equal_counts
      (raw_lex_cursor state).
Proof. reflexivity. Qed.

End MapControl.

(** Selection mirrors request_secondary_or_accept: absence is ordered before
    presence, while two present operands use only the original alias guard. *)
Inductive SecondarySelection (Secondary : Type) :=
| SecondaryAccept (ordering : comparison)
| SecondaryCompare (lhs rhs : Secondary).
Arguments SecondaryAccept {Secondary} _.
Arguments SecondaryCompare {Secondary} _ _.

Definition select_secondary {Secondary : Type} (alias : Secondary -> Secondary -> bool)
    (lhs rhs : option Secondary) : SecondarySelection Secondary :=
  match lhs, rhs with
  | None, None => SecondaryAccept Eq
  | None, Some _ => SecondaryAccept Lt
  | Some _, None => SecondaryAccept Gt
  | Some lhs, Some rhs =>
      if alias lhs rhs then SecondaryAccept Eq else SecondaryCompare lhs rhs
  end.

Theorem secondary_absence_accepts_equal : forall Secondary alias,
  @select_secondary Secondary alias None None = SecondaryAccept Eq.
Proof. reflexivity. Qed.
Theorem secondary_absence_precedes_presence : forall Secondary alias rhs,
  @select_secondary Secondary alias None (Some rhs) = SecondaryAccept Lt.
Proof. reflexivity. Qed.
Theorem secondary_presence_follows_absence : forall Secondary alias lhs,
  @select_secondary Secondary alias (Some lhs) None = SecondaryAccept Gt.
Proof. reflexivity. Qed.
Theorem secondary_original_alias_accepts_equal : forall Secondary alias lhs rhs,
  alias lhs rhs = true ->
  @select_secondary Secondary alias (Some lhs) (Some rhs) = SecondaryAccept Eq.
Proof. intros. cbn. now rewrite H. Qed.
Theorem secondary_original_nonalias_requests_originals : forall Secondary alias lhs rhs,
  alias lhs rhs = false ->
  @select_secondary Secondary alias (Some lhs) (Some rhs) = SecondaryCompare lhs rhs.
Proof. intros. cbn. now rewrite H. Qed.
Theorem present_secondary_selection_is_the_original_map_branch :
  forall Secondary alias lhs rhs,
  @select_secondary Secondary alias (Some lhs) (Some rhs) =
    if alias lhs rhs then SecondaryAccept Eq else SecondaryCompare lhs rhs.
Proof. reflexivity. Qed.

Section RequestTypes.
Context {Key Value : Type}.
Inductive RawRequest := PrimaryRequest (lhs rhs : Key) | SecondaryRequest (lhs rhs : Value).
Inductive RawReply := Requests (request : RawRequest) | Completes (ordering : comparison).
End RequestTypes.

Section PayloadControl.
Context {Key Value Secondary : Type}.
Local Notation Entry := (Key * Value)%type.
Local Notation State := (@RawMapState Key Value).

(** The payload remains in its original merge entries and pending pair. Only
    the callback operand type is independent of that payload. These are call
    locations, not additional runtime Box fields. *)
Inductive RawPayloadControl :=
| Ingress (input : option comparison)
| PhaseLoop
| RequestItem (destination : RawDestination) (lhs rhs : Entry)
| RequestSecondary (destination : RawDestination) (lhs rhs : Entry)
| AcceptItem (destination : RawDestination) (ordering : comparison)
| ReturnReply (reply : @RawReply Key Secondary).

Variable payload_secondary : Value -> option Secondary.
Variable payload_repetitions : Value -> nat.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Variable maximum : nat.

Inductive RawPayloadCoreStep : RawPayloadControl -> State -> RawPayloadControl -> State -> Prop :=
| IngressInitial : forall state,
    map_pending state = None -> RawPayloadCoreStep (Ingress None) state PhaseLoop state
| IngressPrimaryEqual : forall state lhs rhs destination,
    map_pending state = Some (PendingPrimary lhs rhs destination) ->
    RawPayloadCoreStep (Ingress (Some Eq)) state (RequestSecondary destination lhs rhs)
      (set_pending state None)
| IngressPrimaryDecisive : forall state lhs rhs destination ordering,
    map_pending state = Some (PendingPrimary lhs rhs destination) -> ordering <> Eq ->
    RawPayloadCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
      (set_pending state None)
| IngressSecondary : forall state destination ordering,
    map_pending state = Some (PendingSecondary destination) ->
    RawPayloadCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
      (set_pending state None)
| LoopEqualLead : forall state,
    map_phase state = Lead -> map_lead state = Eq ->
    RawPayloadCoreStep PhaseLoop state PhaseLoop (set_phase state SortLeft)
| LoopDecisiveLead : forall state,
    map_phase state = Lead -> map_lead state <> Eq ->
    RawPayloadCoreStep PhaseLoop state (ReturnReply (Completes (map_lead state))) (set_phase state Done)
| LoopLeftRequest : forall state lhs rhs next,
    map_phase state = SortLeft ->
    RawMergeStep maximum (map_left state) (MergeRequests lhs rhs) next ->
    RawPayloadCoreStep PhaseLoop state (RequestItem ToLeftSort lhs rhs) (set_left state next)
| LoopRightRequest : forall state lhs rhs next,
    map_phase state = SortRight ->
    RawMergeStep maximum (map_right state) (MergeRequests lhs rhs) next ->
    RawPayloadCoreStep PhaseLoop state (RequestItem ToRightSort lhs rhs) (set_right state next)
| LoopLeftDone : forall state next,
    map_phase state = SortLeft -> RawMergeStep maximum (map_left state) MergeCompletes next ->
    RawPayloadCoreStep PhaseLoop state PhaseLoop
      (set_phase (set_left state (merge_set_target next None)) SortRight)
| LoopRightDone : forall state next,
    map_phase state = SortRight -> RawMergeStep maximum (map_right state) MergeCompletes next ->
    RawPayloadCoreStep PhaseLoop state PhaseLoop
      (set_phase (set_right state (merge_set_target next None)) Lexicographic)
| LoopLeftExhausted : forall state,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = None ->
    RawPayloadCoreStep PhaseLoop state
      (ReturnReply (Completes (Nat.compare (map_left_total state) (map_right_total state))))
      (set_phase state Done)
| LoopRightExhausted : forall state lhs,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = Some lhs ->
    nth_error (merge_source (map_right state)) (map_right_index state) = None ->
    RawPayloadCoreStep PhaseLoop state
      (ReturnReply (Completes (Nat.compare (map_left_total state) (map_right_total state))))
      (set_phase (initialize_left_remaining_with (payload_repetitions (snd lhs)) state) Done)
| LoopLexRequest : forall state lhs rhs,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = Some lhs ->
    nth_error (merge_source (map_right state)) (map_right_index state) = Some rhs ->
    RawPayloadCoreStep PhaseLoop state (RequestItem ToLexicographic lhs rhs)
      (initialize_both_remaining_with (payload_repetitions (snd lhs))
        (payload_repetitions (snd rhs)) state)
| RequestAliasedPrimary : forall state destination lhs rhs,
    key_alias (fst lhs) (fst rhs) = true ->
    RawPayloadCoreStep (RequestItem destination lhs rhs) state
      (RequestSecondary destination lhs rhs) state
| RequestFreshPrimary : forall state destination lhs rhs,
    key_alias (fst lhs) (fst rhs) = false ->
    RawPayloadCoreStep (RequestItem destination lhs rhs) state
      (ReturnReply (Requests (PrimaryRequest (fst lhs) (fst rhs))))
      (set_pending state (Some (PendingPrimary lhs rhs destination)))
| RequestSelectedSecondary : forall state destination lhs rhs ordering,
    select_secondary secondary_alias (payload_secondary (snd lhs))
      (payload_secondary (snd rhs)) = SecondaryAccept ordering ->
    RawPayloadCoreStep (RequestSecondary destination lhs rhs) state
      (AcceptItem destination ordering) state
| RequestComparedSecondary : forall state destination lhs rhs lhs_secondary rhs_secondary,
    select_secondary secondary_alias (payload_secondary (snd lhs))
      (payload_secondary (snd rhs)) = SecondaryCompare lhs_secondary rhs_secondary ->
    RawPayloadCoreStep (RequestSecondary destination lhs rhs) state
      (ReturnReply (Requests (SecondaryRequest lhs_secondary rhs_secondary)))
      (set_pending state (Some (PendingSecondary destination)))
| AcceptLeft : forall state ordering next,
    raw_merge_accept (map_left state) ordering = Some next ->
    RawPayloadCoreStep (AcceptItem ToLeftSort ordering) state PhaseLoop (set_left state next)
| AcceptRight : forall state ordering next,
    raw_merge_accept (map_right state) ordering = Some next ->
    RawPayloadCoreStep (AcceptItem ToRightSort ordering) state PhaseLoop (set_right state next)
| AcceptLexEqual : forall state,
    RawPayloadCoreStep (AcceptItem ToLexicographic Eq) state PhaseLoop (advance_equal state)
| AcceptLexDecisive : forall state ordering,
    ordering <> Eq ->
    RawPayloadCoreStep (AcceptItem ToLexicographic ordering) state PhaseLoop (set_lead state ordering).

Inductive RawPayloadCorePath : RawPayloadControl -> State -> RawPayloadControl -> State -> Prop :=
| CorePathRefl : forall control state, RawPayloadCorePath control state control state
| CorePathMore : forall control state middle middle_state last next,
    RawPayloadCoreStep control state middle middle_state ->
    RawPayloadCorePath middle middle_state last next ->
    RawPayloadCorePath control state last next.

Definition RawPayloadResume state input reply next :=
  RawPayloadCorePath (Ingress input) state (ReturnReply reply) next.

Theorem raw_payload_secondary_ingress_accepts_every_ordering : forall state destination ordering,
  map_pending state = Some (PendingSecondary destination) ->
  RawPayloadCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
    (set_pending state None).
Proof. intros. now apply IngressSecondary. Qed.

Theorem primary_equal_does_not_mutate_either_sort : forall (state : State),
  map_left (set_pending state None) = map_left state /\
  map_right (set_pending state None) = map_right state.
Proof. intro state. split; reflexivity. Qed.

Theorem raw_payload_core_paths_compose : forall first state middle middle_state last next,
  RawPayloadCorePath first state middle middle_state ->
  RawPayloadCorePath middle middle_state last next -> RawPayloadCorePath first state last next.
Proof.
  intros first state middle middle_state last next PATH REST.
  induction PATH; [exact REST|]. eapply CorePathMore; eauto.
Qed.

Theorem every_raw_payload_core_step_preserves_original_totals :
  forall control state next_control next,
  RawPayloadCoreStep control state next_control next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof. intros control state next_control next STEP. destruct STEP; split; reflexivity. Qed.

Theorem every_raw_payload_resume_preserves_original_totals : forall state input reply next,
  RawPayloadResume state input reply next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof.
  intros state input reply next PATH. unfold RawPayloadResume in PATH.
  induction PATH; [split; reflexivity|].
  destruct (every_raw_payload_core_step_preserves_original_totals _ _ _ _ H) as [L R].
  destruct IHPATH as [LN RN]. split; congruence.
Qed.

End PayloadControl.

Section MapCompatibility.
Context {Key Value : Type}.
(** Map remains the present-secondary, unit-repetition specialization of the
    single source relation. No second transition relation is retained. *)
Definition RawControl := @RawPayloadControl Key Value Value.
Variables key_alias : Key -> Key -> bool.
Variables value_alias : Value -> Value -> bool.
Variable maximum : nat.
Definition RawCoreStep := @RawPayloadCoreStep Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum.
Definition RawCorePath := @RawPayloadCorePath Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum.
Definition RawResume := @RawPayloadResume Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum.

Theorem RequestAliasedSecondary : forall state destination lhs rhs,
  value_alias (snd lhs) (snd rhs) = true ->
  RawCoreStep (RequestSecondary destination lhs rhs) state (AcceptItem destination Eq) state.
Proof. intros. apply RequestSelectedSecondary. now apply secondary_original_alias_accepts_equal. Qed.
Theorem RequestFreshSecondary : forall state destination lhs rhs,
  value_alias (snd lhs) (snd rhs) = false ->
  RawCoreStep (RequestSecondary destination lhs rhs) state
    (ReturnReply (Requests (SecondaryRequest (snd lhs) (snd rhs))))
    (set_pending state (Some (PendingSecondary destination))).
Proof. intros. apply RequestComparedSecondary. now apply secondary_original_nonalias_requests_originals. Qed.

Theorem raw_secondary_ingress_accepts_every_ordering : forall state destination ordering,
  map_pending state = Some (PendingSecondary destination) ->
  RawCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
    (set_pending state None).
Proof. intros. now apply IngressSecondary. Qed.

Theorem raw_core_paths_compose : forall first state middle middle_state last next,
  RawCorePath first state middle middle_state ->
  RawCorePath middle middle_state last next -> RawCorePath first state last next.
Proof. exact (@raw_payload_core_paths_compose Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum). Qed.

Theorem every_raw_core_step_preserves_original_totals :
  forall control state next_control next,
  RawCoreStep control state next_control next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof. exact (@every_raw_payload_core_step_preserves_original_totals Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum). Qed.

Theorem every_raw_resume_preserves_original_totals : forall state input reply next,
  RawResume state input reply next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof. exact (@every_raw_payload_resume_preserves_original_totals Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum). Qed.

Theorem unit_equal_advance_updates_both_original_indices : forall (state : @RawMapState Key Value),
  map_left_remaining state = 1 -> map_right_remaining state = 1 ->
  map_left_index (advance_equal state) = S (map_left_index state) /\
  map_right_index (advance_equal state) = S (map_right_index state) /\
  map_left_remaining (advance_equal state) = 0 /\
  map_right_remaining (advance_equal state) = 0.
Proof.
  intros state L R. unfold advance_equal. rewrite L, R.
  repeat split; reflexivity.
Qed.
End MapCompatibility.

(** Raw answer blocks forget the comparison-result equations in the existing
    PairProtocol, but retain its exact native aliases, order and early exit.
    The equivalence below proves that matching ACTUAL answers restores the
    existing protocol; it does not constrain the raw source to predicted ones. *)
Section PairRefinement.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Local Notation Role := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Role.
Local Notation Primary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary.
Local Notation Secondary := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary.
Local Notation Answer := CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.Answer.

Inductive RawSecondaryExchange (lhs rhs : Value) : list Answer -> comparison -> Prop :=
| RawSecondaryAlias : value_alias lhs rhs = true -> RawSecondaryExchange lhs rhs [] Eq
| RawSecondaryAnswered : forall ordering,
    value_alias lhs rhs = false ->
    RawSecondaryExchange lhs rhs [(Secondary, ordering)] ordering.
Inductive RawPairExchange (lhs rhs : Key * Value) : list Answer -> comparison -> Prop :=
| RawPrimaryAlias : forall answers ordering,
    key_alias (fst lhs) (fst rhs) = true ->
    RawSecondaryExchange (snd lhs) (snd rhs) answers ordering ->
    RawPairExchange lhs rhs answers ordering
| RawPrimaryDecisive : forall ordering,
    key_alias (fst lhs) (fst rhs) = false -> ordering <> Eq ->
    RawPairExchange lhs rhs [(Primary, ordering)] ordering
| RawPrimaryEqual : forall answers ordering,
    key_alias (fst lhs) (fst rhs) = false ->
    RawSecondaryExchange (snd lhs) (snd rhs) answers ordering ->
    RawPairExchange lhs rhs ((Primary, Eq) :: answers) ordering.

Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Definition actual_answer_matches (lhs rhs : Key * Value) (answer : Answer) :=
  match fst answer with
  | Primary => key_compare (fst lhs) (fst rhs) = snd answer
  | Secondary => value_compare (snd lhs) (snd rhs) = snd answer
  end.
Local Notation PP :=
  (@CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.PairProtocol
    Key Value key_compare value_compare key_alias value_alias).
Local Notation SP :=
  (@CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.SecondaryProtocol
    Value value_compare value_alias).

Lemma original_secondary_protocol_erases_to_raw : forall lhs rhs answers ordering,
  SP lhs rhs answers ordering -> RawSecondaryExchange lhs rhs answers ordering.
Proof. intros lhs rhs answers ordering PROTOCOL. destruct PROTOCOL; constructor; assumption. Qed.

Theorem original_pair_protocol_erases_to_raw : forall lhs rhs answers ordering,
  PP lhs rhs answers ordering -> RawPairExchange lhs rhs answers ordering.
Proof.
  intros lhs rhs answers ordering PROTOCOL. destruct PROTOCOL.
  - eapply RawPrimaryAlias; [eassumption|]. now apply original_secondary_protocol_erases_to_raw.
  - apply RawPrimaryDecisive; assumption.
  - eapply RawPrimaryEqual; [eassumption|]. now apply original_secondary_protocol_erases_to_raw.
Qed.

Lemma matching_raw_secondary_restores_original_protocol : forall lhs rhs answers ordering,
  RawSecondaryExchange (snd lhs) (snd rhs) answers ordering ->
  Forall (actual_answer_matches lhs rhs) answers ->
  SP (snd lhs) (snd rhs) answers ordering.
Proof.
  intros lhs rhs answers ordering RAW MATCH. destruct RAW.
  - constructor. assumption.
  - inversion MATCH as [|answer rest HEAD TAIL].
    apply CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.SecondaryAnswered;
      [assumption|exact HEAD].
Qed.

Theorem matching_actual_raw_answers_restore_the_original_pair_protocol :
  forall lhs rhs answers ordering,
  RawPairExchange lhs rhs answers ordering ->
  Forall (actual_answer_matches lhs rhs) answers -> PP lhs rhs answers ordering.
Proof.
  intros lhs rhs answers ordering RAW MATCH. destruct RAW.
  - eapply CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.PairPrimaryAlias;
      [eassumption|]. eapply matching_raw_secondary_restores_original_protocol; eassumption.
  - inversion MATCH as [|answer rest HEAD TAIL].
    apply CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.PairPrimaryDecisive;
      [assumption|exact HEAD|assumption].
  - inversion MATCH as [|answer rest HEAD TAIL].
    eapply CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.PairPrimaryEqual;
      [eassumption|exact HEAD|].
    eapply matching_raw_secondary_restores_original_protocol; eassumption.
Qed.

Hypothesis key_alias_sound : forall x y, key_alias x y = true -> key_compare x y = Eq.
Hypothesis value_alias_sound : forall x y, value_alias x y = true -> value_compare x y = Eq.
Local Notation PC :=
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare).
Local Notation NC := (fun (lhs rhs : Key * Value) (_ : unit) => (Some (PC lhs rhs), tt)).

Theorem matching_actual_raw_pair_returns_key_then_value : forall lhs rhs answers ordering,
  RawPairExchange lhs rhs answers ordering -> Forall (actual_answer_matches lhs rhs) answers ->
  ordering = PC lhs rhs.
Proof.
  intros lhs rhs answers ordering RAW MATCH.
  eapply CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.pair_request_accept_returns_key_then_value.
  - exact key_alias_sound.
  - exact value_alias_sound.
  - eapply matching_actual_raw_answers_restore_the_original_pair_protocol; eassumption.
Qed.

(** This is the precise local physical bridge: the same supplied response
    is used by raw accept and by the existing NativeCopyStep. No result is
    chosen by the raw relation. Relating the constructed whole dialogue to an
    actual generated traversal still requires the completed child's
    lower-height factor theorem to establish the matching-answer hypothesis. *)
Theorem matching_raw_pair_accepts_the_existing_indexed_copy :
  forall source target width cursor done lhs rhs answers ordering next,
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest source cursor lhs rhs ->
  RawPairExchange lhs rhs answers ordering -> Forall (actual_answer_matches lhs rhs) answers ->
  copy_record (accept_side ordering) cursor source target =
    Some (advance (accept_side ordering) cursor, next) ->
  raw_merge_accept (merge_state source (Some target) width cursor true done) ordering =
    Some (merge_state source (Some next) width (advance (accept_side ordering) cursor) false done) /\
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeCopyStep NC source
    cursor target tt (advance (accept_side ordering) cursor) next tt.
Proof.
  intros source target width cursor done lhs rhs answers ordering next REQUEST RAW MATCH COPY.
  split.
  - now apply arbitrary_waiting_response_copies_its_selected_side.
  - eapply MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeAccepted.
    + exact REQUEST.
    + pose proof (matching_actual_raw_pair_returns_key_then_value
        lhs rhs answers ordering RAW MATCH) as RESULT.
      change ((Some (PC lhs rhs), tt) = (Some ordering, tt)). now rewrite RESULT.
    + exact COPY.
Qed.
End PairRefinement.

(** A dialogue is a sequence of ACTUAL source invocations, cut only at a
    ReturnReply. Its response list records what the caller supplied; it has no
    comparison function. In particular this definition neither predicts nor
    checks a response. A native witness is related to it only by the lifting
    lemmas below. *)
Section PayloadDialogues.
Context {Key Value Secondary : Type}.
Variable payload_secondary : Value -> option Secondary.
Variable payload_repetitions : Value -> nat.
Variable key_alias : Key -> Key -> bool.
Variable secondary_alias : Secondary -> Secondary -> bool.
Variable maximum : nat.
Local Notation Path := (@RawPayloadCorePath Key Value Secondary
  payload_secondary payload_repetitions key_alias secondary_alias maximum).
Local Notation Exchange := ((@RawRequest Key Secondary) * comparison)%type.

Inductive RawPayloadDialogue :
    @RawPayloadControl Key Value Secondary -> @RawMapState Key Value -> list Exchange ->
    @RawPayloadControl Key Value Secondary -> @RawMapState Key Value -> Prop :=
| DialogueQuiet : forall control state last next,
    Path control state last next ->
    RawPayloadDialogue control state [] last next
| DialogueAnswer : forall control state request parked ordering answers last next,
    Path control state (ReturnReply (Requests request)) parked ->
    RawPayloadDialogue (Ingress (Some ordering)) parked answers last next ->
    RawPayloadDialogue control state ((request, ordering) :: answers) last next.
End PayloadDialogues.

Section RawDialogues.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.
Local Notation Path := (@RawCorePath Key Value key_alias value_alias maximum).
Local Notation Step := (@RawCoreStep Key Value key_alias value_alias maximum).
Local Notation Exchange := ((@RawRequest Key Value) * comparison)%type.

Definition RawDialogue := @RawPayloadDialogue Key Value Value
  (@Some Value) (fun _ => 1) key_alias value_alias maximum.

Lemma raw_dialogue_prepend_path : forall first state middle parked answers last next,
  Path first state middle parked ->
  RawDialogue middle parked answers last next ->
  RawDialogue first state answers last next.
Proof.
  intros first state middle parked answers last next PREFIX DIALOGUE.
  destruct DIALOGUE.
  - apply DialogueQuiet. eapply raw_core_paths_compose; eassumption.
  - eapply DialogueAnswer; [|eassumption].
    eapply raw_core_paths_compose; eassumption.
Qed.

Lemma raw_dialogues_compose : forall first state middle parked prefix last next suffix
    final_control final_state,
  RawDialogue first state prefix middle parked ->
  RawDialogue middle parked suffix final_control final_state ->
  last = final_control -> next = final_state ->
  RawDialogue first state (prefix ++ suffix) last next.
Proof.
  intros first state middle parked prefix last next suffix final_control final_state
    PREFIX SUFFIX LAST NEXT. subst last next.
  induction PREFIX.
  - cbn. eapply raw_dialogue_prepend_path; eassumption.
  - cbn. eapply DialogueAnswer; [eassumption|]. now apply IHPREFIX.
Qed.

Theorem returned_reply_has_no_internal_successor : forall reply state control next,
  ~ Step (ReturnReply reply) state control next.
Proof. intros reply state control next STEP. inversion STEP. Qed.

Theorem a_path_cannot_cross_its_first_return : forall reply state last next,
  Path (ReturnReply reply) state last next ->
  last = ReturnReply reply /\ next = state.
Proof.
  intros reply state last next PATH. inversion PATH; subst.
  - split; reflexivity.
  - exfalso. eapply returned_reply_has_no_internal_successor; eassumption.
Qed.

Theorem nonempty_dialogue_exposes_its_exact_first_resume :
  forall control state request ordering remaining last next,
  RawDialogue control state ((request, ordering) :: remaining) last next ->
  exists parked,
    Path control state (ReturnReply (Requests request)) parked /\
    RawDialogue (Ingress (Some ordering)) parked remaining last next.
Proof.
  intros control state request ordering remaining last next DIALOGUE.
  inversion DIALOGUE; subst. eexists. split; eassumption.
Qed.

(** Pending is taken, not cloned, by ingress. Clearing the just-created
    pending slot restores the same complete payload, including both sort
    buffers and every lexicographic counter. *)
Lemma clearing_the_just_created_pending_restores_the_payload :
  forall (state : @RawMapState Key Value) pending,
  map_pending state = None ->
  set_pending (set_pending state (Some pending)) None = state.
Proof.
  intros state pending NONE. destruct state.
  cbn [map_pending] in NONE. cbn [set_pending]. subst. reflexivity.
Qed.

Local Notation Primary :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary.
Local Notation Secondary :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary.
Local Notation Answer :=
  CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.Answer.

Definition requested_answers (lhs rhs : Key * Value) (answers : list Answer) : list Exchange :=
  map (fun answer =>
    ((match fst answer with
      | Primary => PrimaryRequest (fst lhs) (fst rhs)
      | Secondary => SecondaryRequest (snd lhs) (snd rhs)
      end), snd answer)) answers.

Lemma raw_secondary_exchange_constructs_the_source_dialogue :
  forall lhs rhs answers ordering destination state,
  RawSecondaryExchange value_alias (snd lhs) (snd rhs) answers ordering ->
  map_pending state = None ->
  RawDialogue (RequestSecondary destination lhs rhs) state
    (requested_answers lhs rhs answers) (AcceptItem destination ordering) state.
Proof.
  intros lhs rhs answers ordering destination state EXCHANGE NONE.
  destruct EXCHANGE.
  - apply DialogueQuiet. eapply CorePathMore.
    + apply RequestAliasedSecondary. exact H.
    + constructor.
  - cbn [requested_answers].
    eapply DialogueAnswer with
      (parked := set_pending state (Some (PendingSecondary destination))).
    + eapply CorePathMore.
      * apply RequestFreshSecondary. exact H.
      * constructor.
    + apply DialogueQuiet.
      rewrite <- (clearing_the_just_created_pending_restores_the_payload
        state (PendingSecondary destination) NONE) at 2.
      eapply CorePathMore.
      * apply IngressSecondary. reflexivity.
      * constructor.
Qed.

Theorem raw_pair_exchange_constructs_the_source_dialogue :
  forall lhs rhs answers ordering destination state,
  RawPairExchange key_alias value_alias lhs rhs answers ordering ->
  map_pending state = None ->
  RawDialogue (RequestItem destination lhs rhs) state
    (requested_answers lhs rhs answers) (AcceptItem destination ordering) state.
Proof.
  intros lhs rhs answers ordering destination state EXCHANGE NONE.
  destruct EXCHANGE.
  - eapply raw_dialogue_prepend_path.
    + eapply CorePathMore; [apply RequestAliasedPrimary; exact H|constructor].
    + eapply raw_secondary_exchange_constructs_the_source_dialogue; eassumption.
  - cbn [requested_answers].
    eapply DialogueAnswer with
      (parked := set_pending state (Some (PendingPrimary lhs rhs destination))).
    + eapply CorePathMore; [apply RequestFreshPrimary; exact H|constructor].
    + apply DialogueQuiet.
      rewrite <- (clearing_the_just_created_pending_restores_the_payload
        state (PendingPrimary lhs rhs destination) NONE) at 2.
      eapply CorePathMore; [eapply IngressPrimaryDecisive; [reflexivity|exact H0]|constructor].
  - cbn [requested_answers].
    eapply DialogueAnswer with
      (parked := set_pending state (Some (PendingPrimary lhs rhs destination))).
    + eapply CorePathMore; [apply RequestFreshPrimary; exact H|constructor].
    + eapply raw_dialogue_prepend_path with
        (middle := RequestSecondary destination lhs rhs)
        (parked := set_pending
          (set_pending state (Some (PendingPrimary lhs rhs destination))) None).
      * eapply CorePathMore; [apply IngressPrimaryEqual; reflexivity|constructor].
      * rewrite (clearing_the_just_created_pending_restores_the_payload
          state (PendingPrimary lhs rhs destination) NONE).
        eapply raw_secondary_exchange_constructs_the_source_dialogue; eassumption.
Qed.
End RawDialogues.

(** The merge trace projects the existing nested step/accept calls. A silent
    transition is an original tail copy, scratch allocation, or run/pass
    boundary. An exchange is an original ready request followed by arbitrary
    answers and an actual indexed accept. This is not another merge sorter:
    both transitions use the already defined source operations. *)
Section NativeRunDialogueLift.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.
Local Notation Entry := (Key * Value)%type.
Local Notation Answer :=
  CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.Answer.
Local Notation Block := (Entry * Entry * list Answer)%type.

Inductive RawMergeTrace : @RawMergeState Entry -> list Block ->
    @RawMergeState Entry -> Prop :=
| MergeTraceDone : forall state, RawMergeTrace state [] state
| MergeTraceSilent : forall state middle blocks final,
    RawMergeSilent maximum state middle ->
    RawMergeTrace middle blocks final ->
    RawMergeTrace state blocks final
| MergeTraceExchange : forall state lhs rhs waiting answers ordering middle blocks final,
    RawMergeStep maximum state (MergeRequests lhs rhs) waiting ->
    RawPairExchange key_alias value_alias lhs rhs answers ordering ->
    raw_merge_accept waiting ordering = Some middle ->
    RawMergeTrace middle blocks final ->
    RawMergeTrace state ((lhs, rhs, answers) :: blocks) final.

Lemma raw_merge_traces_compose : forall first middle prefix last suffix,
  RawMergeTrace first prefix middle -> RawMergeTrace middle suffix last ->
  RawMergeTrace first (prefix ++ suffix) last.
Proof.
  intros first middle prefix last suffix PREFIX SUFFIX.
  induction PREFIX.
  - exact SUFFIX.
  - eapply MergeTraceSilent; [eassumption|]. now apply IHPREFIX.
  - cbn. eapply MergeTraceExchange; try eassumption. now apply IHPREFIX.
Qed.

Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Import NativeMapRunSuspension.NativeMapRunSuspension.

Definition event_pair_blocks (events : list (@NativeEvent Key Value)) : list Block :=
  flat_map (fun event =>
    match event with
    | PairAnswers _ lhs rhs answers => [(lhs, rhs, answers)]
    | _ => []
    end) events.

Lemma event_pair_blocks_append : forall first rest,
  event_pair_blocks (first ++ rest) =
  event_pair_blocks first ++ event_pair_blocks rest.
Proof. intros. apply flat_map_app. Qed.

Theorem native_copy_events_construct_the_actual_raw_merge_trace :
  forall destination source cursor target after_cursor next events width,
  CopyEvents key_compare value_compare key_alias value_alias
    destination source cursor target after_cursor next events ->
  RawMergeTrace (merge_state source (Some target) width cursor false false)
    (event_pair_blocks events)
    (merge_state source (Some next) width after_cursor false false).
Proof.
  intros destination source cursor target after_cursor next events width EVENTS.
  destruct EVENTS as
    [cursor target next lhs rhs answers decision REQUEST PAIR COPY
    |cursor target next LIVE END COPY|cursor target next END LIVE COPY].
  - cbn [event_pair_blocks pair_events].
    eapply MergeTraceExchange with
      (waiting := merge_state source (Some target) width cursor true false)
      (middle := merge_state source (Some next) width
        (advance (accept_side decision) cursor) false false)
      (ordering := decision).
    + apply MergeStepRequests with (target := target); try reflexivity. exact REQUEST.
    + eapply original_pair_protocol_erases_to_raw. exact PAIR.
    + apply arbitrary_waiting_response_copies_its_selected_side. exact COPY.
    + constructor.
  - cbn [event_pair_blocks].
    eapply MergeTraceSilent; [|constructor].
    eapply MergeLeftTail with (target := target); try reflexivity.
    + exact LIVE.
    + change (~ can_copy FromRight cursor). unfold can_copy. lia.
    + exact COPY.
  - cbn [event_pair_blocks].
    eapply MergeTraceSilent; [|constructor].
    eapply MergeRightTail with (target := target); try reflexivity.
    + change (~ can_copy FromLeft cursor). unfold can_copy. lia.
    + exact LIVE.
    + exact COPY.
Qed.

Theorem native_run_events_construct_the_actual_raw_merge_trace :
  forall destination source count cursor target final_cursor final_target events width,
  RunEvents key_compare value_compare key_alias value_alias
    destination source count cursor target final_cursor final_target events ->
  RawMergeTrace (merge_state source (Some target) width cursor false false)
    (event_pair_blocks events)
    (merge_state source (Some final_target) width final_cursor false false).
Proof.
  intros destination source count cursor target final_cursor final_target events width EVENTS.
  induction EVENTS as [cursor target EL ER|
    count cursor target middle next final_cursor final_target first rest COPY RUN IH].
  - constructor.
  - rewrite event_pair_blocks_append. eapply raw_merge_traces_compose.
    + eapply native_copy_events_construct_the_actual_raw_merge_trace; exact COPY.
    + exact IH.
Qed.

Lemma native_run_events_end_at_both_exhausted_counters :
  forall destination source count cursor target final_cursor final_target events,
  RunEvents key_compare value_compare key_alias value_alias
    destination source count cursor target final_cursor final_target events ->
  left_index final_cursor = run_middle final_cursor /\
  right_index final_cursor = run_end final_cursor.
Proof.
  intros destination source count cursor target final_cursor final_target events EVENTS.
  induction EVENTS; auto.
Qed.

Lemma native_pass_event_start_is_bounded :
  forall destination width source start target final_target events,
  PassEvents key_compare value_compare key_alias value_alias
    destination maximum width source start target final_target events ->
  start <= length source.
Proof.
  intros destination width source start target final_target events EVENTS.
  destruct EVENTS; lia.
Qed.

(** Stop immediately BEFORE the final run-boundary action. This retains the
    real last cursor, which the final swap deliberately does not reset. *)
Theorem native_nonempty_pass_events_construct_the_actual_raw_merge_trace :
  forall destination width source start target final_target events,
  PassEvents key_compare value_compare key_alias value_alias
    destination maximum width source start target final_target events ->
  start < length source ->
  exists final_cursor,
    RawMergeTrace
      (merge_state source (Some target) width
        (reset_cursor maximum (length source) start width) false false)
      (event_pair_blocks events)
      (merge_state source (Some final_target) width final_cursor false false) /\
    run_end final_cursor = length source /\
    left_index final_cursor = run_middle final_cursor /\
    right_index final_cursor = run_end final_cursor.
Proof.
  intros destination width source start target final_target events EVENTS.
  induction EVENTS as [target|
    start target count final_cursor next final_target first rest LIVE RUN PASS IH];
    intros NONEMPTY.
  - lia.
  - pose proof (native_run_events_end_at_both_exhausted_counters
      destination source count (reset_cursor maximum (length source) start width)
      target final_cursor next first RUN) as [EL ER].
    pose proof (native_pass_event_start_is_bounded
      destination width source (run_end final_cursor) next final_target rest PASS) as BOUND.
    destruct (Nat.lt_ge_cases (run_end final_cursor) (length source)) as [MORE|FINISHED].
    + destruct (IH MORE) as [last [TAIL [END [LL RR]]]].
      exists last. split; [|auto].
      change (RawMergeTrace
        (merge_state source (Some target) width
          (reset_cursor maximum (length source) start width) false false)
        (event_pair_blocks (first ++ rest))
        (merge_state source (Some final_target) width last false false)).
      rewrite event_pair_blocks_append.
      eapply raw_merge_traces_compose.
      * eapply native_run_events_construct_the_actual_raw_merge_trace. exact RUN.
      * eapply MergeTraceSilent with
          (middle := merge_after_run maximum
            (merge_state source (Some next) width final_cursor false false) next).
        -- eapply MergeEndsRun with (target := next); try reflexivity.
           ++ change (~ can_copy FromLeft final_cursor). unfold can_copy. lia.
           ++ change (~ can_copy FromRight final_cursor). unfold can_copy. lia.
        -- rewrite nonfinal_run_reset_uses_the_actual_absolute_end by exact MORE.
           exact TAIL.
    + assert (END : run_end final_cursor = length source) by lia.
      inversion PASS; subst; [|lia].
      exists final_cursor. split; [|auto].
      change (event_pair_blocks
        (RunBoundary destination maximum width source start target :: first ++ []))
        with (event_pair_blocks (first ++ [])).
      rewrite app_nil_r.
      eapply native_run_events_construct_the_actual_raw_merge_trace. exact RUN.
Qed.
(** The source boundary test decides whether the saved final cursor is dead
    or a reset cursor is required. This lemma does not reset the final one. *)
Theorem native_outer_events_construct_the_actual_raw_merge_trace :
  forall destination count width source scratch output final_scratch events,
  OuterEvents key_compare value_compare key_alias value_alias
    destination maximum count width source scratch output final_scratch events ->
  forall cursor,
  (width < length source ->
    cursor = reset_cursor maximum (length source) 0 width) ->
  exists final_width final_cursor,
    RawMergeTrace
      (merge_state source scratch width cursor false (length source <=? width))
      (event_pair_blocks events)
      (merge_state output final_scratch final_width final_cursor false true).
Proof.
  intros destination count width source scratch output final_scratch events EVENTS.
  induction EVENTS as [width source scratch FINISHED|
    count width source scratch completed output final_scratch first rest LIVE PASS OUTER IH];
    intros cursor CURSOR.
  - exists width, cursor.
    rewrite (proj2 (Nat.leb_le _ _) FINISHED). constructor.
  - rewrite (CURSOR LIVE), (proj2 (Nat.leb_gt _ _) LIVE).
    destruct (native_nonempty_pass_events_construct_the_actual_raw_merge_trace
      destination width source 0 (MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.scratch_payload
        source scratch) completed first PASS ltac:(lia))
      as [last_cursor [PASS_TRACE [END [EL ER]]]].
    set (next_width := saturated_double maximum width).
    set (next_cursor :=
      if length completed <=? next_width then cursor_after_run last_cursor
      else reset_cursor maximum (length completed) 0 next_width).
    assert (NEXT_CURSOR : next_width < length completed ->
      next_cursor = reset_cursor maximum (length completed) 0 next_width).
    { intros LIVE_NEXT. unfold next_cursor.
      now rewrite (proj2 (Nat.leb_gt _ _) LIVE_NEXT). }
    destruct (IH next_cursor NEXT_CURSOR) as [final_width [final_cursor TAIL]].
    exists final_width, final_cursor.
    change (event_pair_blocks (ScratchBoundary destination source scratch :: first ++
      SwappedBuffers destination maximum width source completed :: rest))
      with (event_pair_blocks (first ++
        SwappedBuffers destination maximum width source completed :: rest)).
    rewrite event_pair_blocks_append.
    change (event_pair_blocks
      (SwappedBuffers destination maximum width source completed :: rest))
      with (event_pair_blocks rest).
    assert (ALLOCATED :
      RawMergeTrace
        (merge_state source scratch width
          (reset_cursor maximum (length source) 0 width) false false)
        (event_pair_blocks first)
        (merge_state source (Some completed) width last_cursor false false)).
    { destruct scratch as [target|].
      - exact PASS_TRACE.
      - eapply MergeTraceSilent; [|exact PASS_TRACE].
        apply MergeAllocatesScratch; reflexivity. }
    eapply raw_merge_traces_compose; [exact ALLOCATED|].
    eapply MergeTraceSilent with
      (middle := merge_after_run maximum
        (merge_state source (Some completed) width last_cursor false false) completed).
    + eapply MergeEndsRun with (target := completed); try reflexivity.
      * change (~ can_copy FromLeft last_cursor). unfold can_copy. lia.
      * change (~ can_copy FromRight last_cursor). unfold can_copy. lia.
    + unfold merge_after_run.
      cbn [merge_state merge_source merge_cursor merge_width].
      rewrite END, Nat.ltb_irrefl.
      fold next_width. fold next_width in TAIL. unfold next_cursor in TAIL.
      destruct (length completed <=? next_width); exact TAIL.
Qed.

Theorem native_initial_sort_events_construct_the_actual_raw_merge_trace :
  forall destination count source output final_scratch events,
  OuterEvents key_compare value_compare key_alias value_alias
    destination maximum count 1 source None output final_scratch events ->
  exists final_width final_cursor,
    RawMergeTrace (initial_merge maximum source) (event_pair_blocks events)
      (merge_state output final_scratch final_width final_cursor false true).
Proof.
  intros destination count source output final_scratch events EVENTS.
  destruct (native_outer_events_construct_the_actual_raw_merge_trace
    destination count 1 source None output final_scratch events EVENTS
    (reset_cursor maximum (length source) 0 1) ltac:(intros; reflexivity))
    as [final_width [final_cursor TRACE]].
  exists final_width, final_cursor. unfold initial_merge.
  replace (length source <? 2) with (length source <=? 1).
  - exact TRACE.
  - destruct (length source) as [|[|n]]; reflexivity.
Qed.
End NativeRunDialogueLift.

Section NativeLexDialogueLift.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Import NativeMapRunSuspension.NativeMapRunSuspension.
Local Notation Dialogue := (@RawDialogue Key Value key_alias value_alias maximum).
Local Notation Entry := (Key * Value)%type.

Definition event_requested_answers (events : list (@NativeEvent Key Value)) :=
  flat_map (fun event =>
    match event with
    | PairAnswers _ lhs rhs answers => requested_answers lhs rhs answers
    | _ => []
    end) events.

Lemma event_requested_answers_append : forall first rest,
  event_requested_answers (first ++ rest) =
    event_requested_answers first ++ event_requested_answers rest.
Proof. intros. apply flat_map_app. Qed.

Definition unit_lex_payload (left_sort right_sort : @RawMergeState Entry) index :=
  map_state left_sort right_sort Lexicographic None Eq
    (length (merge_source left_sort)) (length (merge_source right_sort))
    index index 0 0.

Lemma raw_dialogue_append : forall first state middle parked prefix suffix last next,
  Dialogue first state prefix middle parked ->
  Dialogue middle parked suffix last next ->
  Dialogue first state (prefix ++ suffix) last next.
Proof.
  intros. eapply raw_dialogues_compose; [eassumption|eassumption|reflexivity|reflexivity].
Qed.

(** LexEvents is the existing unit-pair walk, not a comparison-result oracle.
    Its PairProtocols are erased to arbitrary-response source dialogues. The
    caller's lower-height theorem is still needed to prove those are the
    responses actually supplied during generated traversal. *)
Theorem native_unit_lex_events_construct_the_actual_raw_dialogue :
  forall lhs rhs index count result events,
  LexEvents key_compare value_compare key_alias value_alias
    lhs rhs index count result events ->
  forall left_sort right_sort,
  merge_source left_sort = lhs -> merge_source right_sort = rhs ->
  exists final,
    Dialogue PhaseLoop (unit_lex_payload left_sort right_sort index)
      (event_requested_answers events) (ReturnReply (Completes result)) final.
Proof.
  intros lhs rhs index count result events EVENTS.
  induction EVENTS as [index END|index lhs_entry LEFT END|
    index count lhs_entry rhs_entry answers result rest LEFT RIGHT PAIR LEX IH|
    index lhs_entry rhs_entry answers result LEFT RIGHT PAIR DEC];
    intros left_sort right_sort SOURCE_LEFT SOURCE_RIGHT.
  - eexists. apply DialogueQuiet. eapply CorePathMore.
    + apply LoopLeftExhausted; [reflexivity|].
      cbn [unit_lex_payload map_state map_left map_left_index]. now rewrite SOURCE_LEFT.
    + cbn [unit_lex_payload map_state map_left_total map_right_total].
      rewrite SOURCE_LEFT, SOURCE_RIGHT. constructor.
  - eexists. apply DialogueQuiet. eapply CorePathMore.
    + eapply LoopRightExhausted with (lhs := lhs_entry); [reflexivity| |].
      * cbn [unit_lex_payload map_state map_left map_left_index]. now rewrite SOURCE_LEFT.
      * cbn [unit_lex_payload map_state map_right map_right_index]. now rewrite SOURCE_RIGHT.
    + cbn [unit_lex_payload map_state map_left_total map_right_total].
      rewrite SOURCE_LEFT, SOURCE_RIGHT. constructor.
  - destruct (IH left_sort right_sort SOURCE_LEFT SOURCE_RIGHT) as [final TAIL].
    exists final.
    change (event_requested_answers
      (pair_events (AtLexPair lhs rhs index) lhs_entry rhs_entry answers ++
        AdvancedUnitLex lhs rhs index :: rest))
      with (requested_answers lhs_entry rhs_entry answers ++ event_requested_answers rest).
    eapply raw_dialogue_prepend_path with
      (middle := RequestItem ToLexicographic lhs_entry rhs_entry)
      (parked := initialize_both_remaining (unit_lex_payload left_sort right_sort index)).
    + eapply CorePathMore.
      * eapply LoopLexRequest with (lhs := lhs_entry) (rhs := rhs_entry); [reflexivity| |].
        -- cbn [unit_lex_payload map_state map_left map_left_index]. rewrite SOURCE_LEFT. exact LEFT.
        -- cbn [unit_lex_payload map_state map_right map_right_index]. rewrite SOURCE_RIGHT. exact RIGHT.
      * constructor.
    + eapply raw_dialogue_append with
        (middle := AcceptItem ToLexicographic Eq)
        (parked := initialize_both_remaining (unit_lex_payload left_sort right_sort index)).
      * apply raw_pair_exchange_constructs_the_source_dialogue; [|reflexivity].
        eapply original_pair_protocol_erases_to_raw. exact PAIR.
      * eapply raw_dialogue_prepend_path with
          (middle := PhaseLoop)
          (parked := advance_equal
            (initialize_both_remaining (unit_lex_payload left_sort right_sort index))).
        -- eapply CorePathMore; [apply AcceptLexEqual|constructor].
        -- exact TAIL.
  - exists (set_phase (set_lead
      (initialize_both_remaining (unit_lex_payload left_sort right_sort index)) result) Done).
    change (event_requested_answers
      (pair_events (AtLexPair lhs rhs index) lhs_entry rhs_entry answers ++ [LexLeadDone result]))
      with (requested_answers lhs_entry rhs_entry answers ++ []).
    rewrite app_nil_r.
    eapply raw_dialogue_prepend_path with
      (middle := RequestItem ToLexicographic lhs_entry rhs_entry)
      (parked := initialize_both_remaining (unit_lex_payload left_sort right_sort index)).
    + eapply CorePathMore.
      * eapply LoopLexRequest with (lhs := lhs_entry) (rhs := rhs_entry); [reflexivity| |].
        -- cbn [unit_lex_payload map_state map_left map_left_index]. rewrite SOURCE_LEFT. exact LEFT.
        -- cbn [unit_lex_payload map_state map_right map_right_index]. rewrite SOURCE_RIGHT. exact RIGHT.
      * constructor.
    + rewrite <- app_nil_r at 1.
      eapply raw_dialogue_append with
        (middle := AcceptItem ToLexicographic result)
        (parked := initialize_both_remaining (unit_lex_payload left_sort right_sort index)).
      * apply raw_pair_exchange_constructs_the_source_dialogue; [|reflexivity].
        eapply original_pair_protocol_erases_to_raw. exact PAIR.
      * apply DialogueQuiet. eapply CorePathMore.
        -- apply AcceptLexDecisive. exact DEC.
        -- eapply CorePathMore.
           ++ apply LoopDecisiveLead; [reflexivity|exact DEC].
           ++ constructor.
Qed.
End NativeLexDialogueLift.

(** Absorb silent merge work into the same original step invocation. There is
    no additional Map-loop transition for this work in the Rust source. *)
Section MergeBoxEmbedding.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.
Local Notation Path := (@RawCorePath Key Value key_alias value_alias maximum).
Local Notation Dialogue := (@RawDialogue Key Value key_alias value_alias maximum).
Local Notation Trace := (@RawMergeTrace Key Value key_alias value_alias maximum).

Lemma left_merge_silent_prefixes_the_same_invocation :
  forall original first middle reply final,
  map_phase original = SortLeft ->
  RawMergeSilent maximum first middle ->
  Path PhaseLoop (set_left original middle) (ReturnReply reply) final ->
  Path PhaseLoop (set_left original first) (ReturnReply reply) final.
Proof.
  intros original first middle reply final PHASE SILENT PATH.
  inversion PATH as [control state|
    control state middle_control middle_state last next FIRST REST]; subst.
  inversion FIRST; subst; cbn [map_state map_phase map_left set_left] in *; try congruence.
  - eapply CorePathMore with
      (middle := RequestItem ToLeftSort lhs rhs)
      (middle_state := set_left original next).
    + eapply LoopLeftRequest with (state := set_left original first) (next := next).
      * exact PHASE.
      * eapply MergeStepInternal; [exact SILENT|exact H0].
    + exact REST.
  - match goal with
    | FINISH : RawMergeStep maximum middle MergeCompletes ?after |- _ =>
      eapply CorePathMore with
        (middle := PhaseLoop)
        (middle_state := set_phase
          (set_left original (merge_set_target after None)) SortRight);
      [eapply LoopLeftDone with (state := set_left original first) (next := after);
        [exact PHASE|eapply MergeStepInternal; [exact SILENT|exact FINISH]]
      |exact REST]
    end.
Qed.

Lemma right_merge_silent_prefixes_the_same_invocation :
  forall original first middle reply final,
  map_phase original = SortRight ->
  RawMergeSilent maximum first middle ->
  Path PhaseLoop (set_right original middle) (ReturnReply reply) final ->
  Path PhaseLoop (set_right original first) (ReturnReply reply) final.
Proof.
  intros original first middle reply final PHASE SILENT PATH.
  inversion PATH as [control state|
    control state middle_control middle_state last next FIRST REST]; subst.
  inversion FIRST; subst; cbn [map_state map_phase map_right set_right] in *; try congruence.
  - match goal with
    | REQUEST : RawMergeStep maximum middle (MergeRequests ?lhs ?rhs) ?after |- _ =>
      eapply CorePathMore with
        (middle := RequestItem ToRightSort lhs rhs)
        (middle_state := set_right original after);
      [eapply LoopRightRequest with (state := set_right original first) (next := after);
        [exact PHASE|eapply MergeStepInternal; [exact SILENT|exact REQUEST]]
      |exact REST]
    end.
  - match goal with
    | FINISH : RawMergeStep maximum middle MergeCompletes ?after |- _ =>
      eapply CorePathMore with
        (middle := PhaseLoop)
        (middle_state := set_phase
          (set_right original (merge_set_target after None)) Lexicographic);
      [eapply LoopRightDone with (state := set_right original first) (next := after);
        [exact PHASE|eapply MergeStepInternal; [exact SILENT|exact FINISH]]
      |exact REST]
    end.
Qed.

Definition selected_sort_phase (is_left : bool) := if is_left then SortLeft else SortRight.
Definition selected_sort_destination (is_left : bool) :=
  if is_left then ToLeftSort else ToRightSort.
Definition install_sort (is_left : bool) (state : @RawMapState Key Value)
    (sort : @RawMergeState (Key * Value)) :=
  if is_left then set_left state sort else set_right state sort.

Lemma selected_merge_silent_prefixes_the_same_dialogue :
  forall is_left original first middle answers reply final,
  map_phase original = selected_sort_phase is_left ->
  RawMergeSilent maximum first middle ->
  Dialogue PhaseLoop (install_sort is_left original middle) answers (ReturnReply reply) final ->
  Dialogue PhaseLoop (install_sort is_left original first) answers (ReturnReply reply) final.
Proof.
  intros is_left original first middle answers reply final PHASE SILENT DIALOGUE.
  inversion DIALOGUE as [control state last next PATH|
    control state request parked ordering more_answers last next PATH REST]; subst.
  - apply DialogueQuiet. destruct is_left.
    + eapply left_merge_silent_prefixes_the_same_invocation; eassumption.
    + eapply right_merge_silent_prefixes_the_same_invocation; eassumption.
  - eapply DialogueAnswer; [|exact REST]. destruct is_left.
    + eapply left_merge_silent_prefixes_the_same_invocation; eassumption.
    + eapply right_merge_silent_prefixes_the_same_invocation; eassumption.
Qed.

Lemma selected_merge_request_enters_the_same_pair_control :
  forall is_left original first lhs rhs waiting,
  map_phase original = selected_sort_phase is_left ->
  RawMergeStep maximum first (MergeRequests lhs rhs) waiting ->
  Path PhaseLoop (install_sort is_left original first)
    (RequestItem (selected_sort_destination is_left) lhs rhs)
    (install_sort is_left original waiting).
Proof.
  intros is_left original first lhs rhs waiting PHASE REQUEST.
  destruct is_left; eapply CorePathMore; [|constructor| |constructor].
  - eapply LoopLeftRequest with (state := set_left original first) (next := waiting);
      [exact PHASE|exact REQUEST].
  - eapply LoopRightRequest with (state := set_right original first) (next := waiting);
      [exact PHASE|exact REQUEST].
Qed.

Lemma selected_merge_accept_returns_to_the_same_box :
  forall is_left original waiting ordering after,
  raw_merge_accept waiting ordering = Some after ->
  Path (AcceptItem (selected_sort_destination is_left) ordering)
    (install_sort is_left original waiting) PhaseLoop (install_sort is_left original after).
Proof.
  intros is_left original waiting ordering after ACCEPT.
  destruct is_left; eapply CorePathMore; [|constructor| |constructor].
  - apply AcceptLeft with (state := set_left original waiting) (next := after). exact ACCEPT.
  - apply AcceptRight with (state := set_right original waiting) (next := after). exact ACCEPT.
Qed.

Definition block_requested_answers
    (blocks : list ((Key * Value) * (Key * Value) *
      list CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.Answer)) :=
  flat_map (fun block =>
    let '(lhs, rhs, answers) := block in requested_answers lhs rhs answers) blocks.

(** This continuation transformer supplies source invocations from the merge
    trace; the continuation is an actual subsequent dialogue, not a result
    premise or an assumption that the sort succeeded. Pending remains None
    between blocks, so a new request cannot overwrite a previous request. *)
Theorem raw_merge_trace_constructs_the_enclosing_box_dialogue :
  forall first blocks after,
  Trace first blocks after ->
  forall is_left original suffix reply final,
  map_phase original = selected_sort_phase is_left ->
  map_pending original = None ->
  Dialogue PhaseLoop (install_sort is_left original after) suffix (ReturnReply reply) final ->
  Dialogue PhaseLoop (install_sort is_left original first)
    (block_requested_answers blocks ++ suffix) (ReturnReply reply) final.
Proof.
  intros first blocks after TRACE.
  induction TRACE as [state|
    state middle blocks final_sort SILENT TRACE IH|
    state lhs rhs waiting answers ordering middle blocks final_sort REQUEST PAIR ACCEPT TRACE IH];
    intros is_left original suffix reply final PHASE NONE CONTINUATION.
  - exact CONTINUATION.
  - eapply selected_merge_silent_prefixes_the_same_dialogue; [exact PHASE|exact SILENT|].
    eapply IH; eassumption.
  - cbn [block_requested_answers flat_map]. rewrite <- app_assoc.
    eapply raw_dialogue_prepend_path.
    + eapply selected_merge_request_enters_the_same_pair_control;
        [exact PHASE|exact REQUEST].
    + eapply raw_dialogues_compose with
        (middle := AcceptItem (selected_sort_destination is_left) ordering)
        (parked := install_sort is_left original waiting).
      * apply raw_pair_exchange_constructs_the_source_dialogue; [exact PAIR|].
        destruct is_left; exact NONE.
      * eapply raw_dialogue_prepend_path.
        -- apply selected_merge_accept_returns_to_the_same_box. exact ACCEPT.
        -- eapply IH; eassumption.
      * reflexivity.
      * reflexivity.
Qed.
End MergeBoxEmbedding.

Section CompleteMapDialogueLift.
Context {Key Value : Type}.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Import NativeMapRunSuspension.NativeMapRunSuspension.
Local Notation Dialogue := (@RawDialogue Key Value key_alias value_alias maximum).

Lemma native_event_blocks_retain_exactly_the_requested_answers :
  forall events : list (@NativeEvent Key Value),
  block_requested_answers (event_pair_blocks events) = event_requested_answers events.
Proof.
  induction events as [|event events IH]; [reflexivity|].
  destruct event; try exact IH.
  change (requested_answers p p0 l ++
    block_requested_answers (event_pair_blocks events) =
    requested_answers p p0 l ++ event_requested_answers events).
  now rewrite IH.
Qed.

(** The length premises below are physical buffer facts, not successful-core
    premises. They relate the source's original unit totals to its sorted
    buffers, and are obtained from the existing native outer-pass theorem in
    the corollary that follows. *)
Theorem sequenced_map_events_construct_the_complete_raw_dialogue :
  forall left_input right_input left_output right_output result events,
  MapEvents key_compare value_compare key_alias value_alias maximum
    left_input right_input left_output right_output result events ->
  length left_output = length left_input ->
  length right_output = length right_input ->
  exists final,
    Dialogue (Ingress None)
      (initial_map maximum left_input right_input (length left_input) (length right_input))
      (event_requested_answers events) (ReturnReply (Completes result)) final.
Proof.
  intros left_input right_input left_output right_output result events EVENTS LEFT_LENGTH RIGHT_LENGTH.
  destruct EVENTS as [lc ls rc rs count left_events right_events lex_events LEFT RIGHT LEX].
  destruct (@native_initial_sort_events_construct_the_actual_raw_merge_trace
    Key Value key_alias value_alias maximum key_compare value_compare
    InLeftSort lc left_input left_output ls left_events LEFT)
    as [left_width [left_cursor LEFT_TRACE]].
  destruct (@native_initial_sort_events_construct_the_actual_raw_merge_trace
    Key Value key_alias value_alias maximum key_compare value_compare
    InRightSort rc right_input right_output rs right_events RIGHT)
    as [right_width [right_cursor RIGHT_TRACE]].
  set (left_done := merge_state left_output ls left_width left_cursor false true).
  set (right_done := merge_state right_output rs right_width right_cursor false true).
  set (left_released := merge_set_target left_done None).
  set (right_released := merge_set_target right_done None).
  destruct (@native_unit_lex_events_construct_the_actual_raw_dialogue
    Key Value key_alias value_alias maximum key_compare value_compare
    left_output right_output 0 count result lex_events LEX
    left_released right_released ltac:(reflexivity) ltac:(reflexivity))
    as [final LEX_DIALOGUE].
  exists final.
  set (right_original :=
    map_state left_released (initial_merge maximum right_input) SortRight None Eq
      (length left_input) (length right_input) 0 0 0 0).
  assert (RIGHT_CONTINUATION :
    Dialogue PhaseLoop (install_sort false right_original right_done)
      (event_requested_answers lex_events) (ReturnReply (Completes result)) final).
  { eapply raw_dialogue_prepend_path with
      (middle := PhaseLoop)
      (parked := set_phase
        (set_right right_original right_released) Lexicographic).
    - eapply CorePathMore.
      + eapply LoopRightDone; [reflexivity|].
        apply MergeStepDone; reflexivity.
      + constructor.
    - unfold right_original, left_released, right_released, left_done, right_done in *.
      unfold unit_lex_payload in LEX_DIALOGUE.
      cbn [merge_state merge_source merge_set_target] in LEX_DIALOGUE.
      rewrite LEFT_LENGTH, RIGHT_LENGTH in LEX_DIALOGUE.
      exact LEX_DIALOGUE. }
  assert (RIGHT_DIALOGUE :
    Dialogue PhaseLoop right_original
      (block_requested_answers (event_pair_blocks right_events) ++
        event_requested_answers lex_events)
      (ReturnReply (Completes result)) final).
  { eapply raw_merge_trace_constructs_the_enclosing_box_dialogue with
      (is_left := false) (original := right_original) (after := right_done).
    - exact RIGHT_TRACE.
    - reflexivity.
    - reflexivity.
    - exact RIGHT_CONTINUATION. }
  set (left_original :=
    map_state (initial_merge maximum left_input) (initial_merge maximum right_input)
      SortLeft None Eq (length left_input) (length right_input) 0 0 0 0).
  assert (LEFT_CONTINUATION :
    Dialogue PhaseLoop (install_sort true left_original left_done)
      (block_requested_answers (event_pair_blocks right_events) ++
        event_requested_answers lex_events)
      (ReturnReply (Completes result)) final).
  { eapply raw_dialogue_prepend_path with (middle := PhaseLoop) (parked := right_original).
    - eapply CorePathMore.
      + eapply LoopLeftDone; [reflexivity|].
        apply MergeStepDone; reflexivity.
      + constructor.
    - exact RIGHT_DIALOGUE. }
  assert (LEFT_DIALOGUE :
    Dialogue PhaseLoop left_original
      (block_requested_answers (event_pair_blocks left_events) ++
       (block_requested_answers (event_pair_blocks right_events) ++
        event_requested_answers lex_events))
      (ReturnReply (Completes result)) final).
  { eapply raw_merge_trace_constructs_the_enclosing_box_dialogue with
      (is_left := true) (original := left_original) (after := left_done).
    - exact LEFT_TRACE.
    - reflexivity.
    - reflexivity.
    - exact LEFT_CONTINUATION. }
  repeat rewrite native_event_blocks_retain_exactly_the_requested_answers in LEFT_DIALOGUE.
  unfold event_requested_answers.
  repeat first [ rewrite flat_map_app | progress (cbn [flat_map]) ].
  rewrite app_nil_r.
  eapply raw_dialogue_prepend_path; [|exact LEFT_DIALOGUE].
  eapply CorePathMore; [apply IngressInitial; reflexivity|].
  eapply CorePathMore; [apply LoopEqualLead; reflexivity|constructor].
Qed.

Hypothesis key_alias_sound : forall x y, key_alias x y = true -> key_compare x y = Eq.
Hypothesis value_alias_sound : forall x y, value_alias x y = true -> value_compare x y = Eq.

Lemma native_initial_outer_events_preserve_the_original_unit_total :
  forall destination count source output scratch events,
  length source <= maximum ->
  OuterEvents key_compare value_compare key_alias value_alias
    destination maximum count 1 source None output scratch events ->
  length output = length source.
Proof.
  intros destination count source output scratch events BOUND EVENTS.
  pose proof (@sequenced_outer_events_forget_to_the_same_native_outer
    Key Value key_compare value_compare key_alias value_alias
    key_alias_sound value_alias_sound destination maximum count 1 source None output scratch events EVENTS)
    as NATIVE.
  destruct (@MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.actual_buffer_lifecycle_projects_to_the_existing_outer_trace
    (Key * Value) unit
    (fun lhs rhs (_ : unit) =>
      (Some (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare
        key_compare value_compare lhs rhs), tt))
    maximum count 1 source None tt output scratch tt NATIVE ltac:(lia) BOUND I)
    as [TRACE [LENGTH SCRATCH]].
  exact LENGTH.
Qed.

Theorem bounded_native_map_events_construct_the_complete_raw_dialogue :
  forall left_input right_input left_output right_output result events,
  length left_input <= maximum -> length right_input <= maximum ->
  MapEvents key_compare value_compare key_alias value_alias maximum
    left_input right_input left_output right_output result events ->
  exists final,
    Dialogue (Ingress None)
      (initial_map maximum left_input right_input (length left_input) (length right_input))
      (event_requested_answers events) (ReturnReply (Completes result)) final.
Proof.
  intros left_input right_input left_output right_output result events LEFT_BOUND RIGHT_BOUND EVENTS.
  eapply sequenced_map_events_construct_the_complete_raw_dialogue; [exact EVENTS| |].
  - destruct EVENTS.
    eapply native_initial_outer_events_preserve_the_original_unit_total; eassumption.
  - destruct EVENTS.
    eapply native_initial_outer_events_preserve_the_original_unit_total; eassumption.
Qed.
End CompleteMapDialogueLift.

End GeneratedMapCoreSource.

Print Assumptions GeneratedMapCoreSource.arbitrary_waiting_response_copies_its_selected_side.
Print Assumptions GeneratedMapCoreSource.no_pending_merge_does_not_accept_a_response.
Print Assumptions GeneratedMapCoreSource.successful_raw_accept_keeps_source_and_width.
Print Assumptions GeneratedMapCoreSource.nonfinal_run_reset_uses_the_actual_absolute_end.
Print Assumptions GeneratedMapCoreSource.final_swap_preserves_the_unreset_dead_cursor.
Print Assumptions GeneratedMapCoreSource.raw_secondary_ingress_accepts_every_ordering.
Print Assumptions GeneratedMapCoreSource.primary_equal_does_not_mutate_either_sort.
Print Assumptions GeneratedMapCoreSource.raw_core_paths_compose.
Print Assumptions GeneratedMapCoreSource.every_raw_core_step_preserves_original_totals.
Print Assumptions GeneratedMapCoreSource.every_raw_resume_preserves_original_totals.
Print Assumptions GeneratedMapCoreSource.unit_equal_advance_updates_both_original_indices.
Print Assumptions GeneratedMapCoreSource.original_secondary_protocol_erases_to_raw.
Print Assumptions GeneratedMapCoreSource.original_pair_protocol_erases_to_raw.
Print Assumptions GeneratedMapCoreSource.matching_raw_secondary_restores_original_protocol.
Print Assumptions GeneratedMapCoreSource.matching_actual_raw_answers_restore_the_original_pair_protocol.
Print Assumptions GeneratedMapCoreSource.matching_actual_raw_pair_returns_key_then_value.
Print Assumptions GeneratedMapCoreSource.matching_raw_pair_accepts_the_existing_indexed_copy.
Print Assumptions GeneratedMapCoreSource.raw_dialogue_prepend_path.
Print Assumptions GeneratedMapCoreSource.raw_dialogues_compose.
Print Assumptions GeneratedMapCoreSource.returned_reply_has_no_internal_successor.
Print Assumptions GeneratedMapCoreSource.a_path_cannot_cross_its_first_return.
Print Assumptions GeneratedMapCoreSource.nonempty_dialogue_exposes_its_exact_first_resume.
Print Assumptions GeneratedMapCoreSource.clearing_the_just_created_pending_restores_the_payload.
Print Assumptions GeneratedMapCoreSource.raw_secondary_exchange_constructs_the_source_dialogue.
Print Assumptions GeneratedMapCoreSource.raw_pair_exchange_constructs_the_source_dialogue.
Print Assumptions GeneratedMapCoreSource.raw_merge_traces_compose.
Print Assumptions GeneratedMapCoreSource.native_copy_events_construct_the_actual_raw_merge_trace.
Print Assumptions GeneratedMapCoreSource.native_run_events_construct_the_actual_raw_merge_trace.
Print Assumptions GeneratedMapCoreSource.native_run_events_end_at_both_exhausted_counters.
Print Assumptions GeneratedMapCoreSource.native_pass_event_start_is_bounded.
Print Assumptions GeneratedMapCoreSource.native_nonempty_pass_events_construct_the_actual_raw_merge_trace.
Print Assumptions GeneratedMapCoreSource.native_outer_events_construct_the_actual_raw_merge_trace.
Print Assumptions GeneratedMapCoreSource.native_initial_sort_events_construct_the_actual_raw_merge_trace.
Print Assumptions GeneratedMapCoreSource.native_unit_lex_events_construct_the_actual_raw_dialogue.
Print Assumptions GeneratedMapCoreSource.left_merge_silent_prefixes_the_same_invocation.
Print Assumptions GeneratedMapCoreSource.right_merge_silent_prefixes_the_same_invocation.
Print Assumptions GeneratedMapCoreSource.selected_merge_silent_prefixes_the_same_dialogue.
Print Assumptions GeneratedMapCoreSource.selected_merge_request_enters_the_same_pair_control.
Print Assumptions GeneratedMapCoreSource.selected_merge_accept_returns_to_the_same_box.
Print Assumptions GeneratedMapCoreSource.raw_merge_trace_constructs_the_enclosing_box_dialogue.
Print Assumptions GeneratedMapCoreSource.native_event_blocks_retain_exactly_the_requested_answers.
Print Assumptions GeneratedMapCoreSource.sequenced_map_events_construct_the_complete_raw_dialogue.
Print Assumptions GeneratedMapCoreSource.native_initial_outer_events_preserve_the_original_unit_total.
Print Assumptions GeneratedMapCoreSource.bounded_native_map_events_construct_the_complete_raw_dialogue.
Print Assumptions GeneratedMapCoreSource.counted_left_restoration_is_original.
Print Assumptions GeneratedMapCoreSource.counted_both_restoration_is_original.
Print Assumptions GeneratedMapCoreSource.counted_left_restoration_exposes_the_original_counter.
Print Assumptions GeneratedMapCoreSource.counted_both_restoration_exposes_the_original_counters.
Print Assumptions GeneratedMapCoreSource.raw_equal_advance_reuses_existing_count_operation.
Print Assumptions GeneratedMapCoreSource.map_initialization_is_the_unit_specialization.
Print Assumptions GeneratedMapCoreSource.secondary_absence_accepts_equal.
Print Assumptions GeneratedMapCoreSource.secondary_absence_precedes_presence.
Print Assumptions GeneratedMapCoreSource.secondary_presence_follows_absence.
Print Assumptions GeneratedMapCoreSource.secondary_original_alias_accepts_equal.
Print Assumptions GeneratedMapCoreSource.secondary_original_nonalias_requests_originals.
Print Assumptions GeneratedMapCoreSource.present_secondary_selection_is_the_original_map_branch.
Print Assumptions GeneratedMapCoreSource.raw_payload_secondary_ingress_accepts_every_ordering.
Print Assumptions GeneratedMapCoreSource.raw_payload_core_paths_compose.
Print Assumptions GeneratedMapCoreSource.every_raw_payload_core_step_preserves_original_totals.
Print Assumptions GeneratedMapCoreSource.every_raw_payload_resume_preserves_original_totals.
Print Assumptions GeneratedMapCoreSource.RequestAliasedSecondary.
Print Assumptions GeneratedMapCoreSource.RequestFreshSecondary.
