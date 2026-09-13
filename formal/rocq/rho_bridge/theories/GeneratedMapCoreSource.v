(** Comparator-free successful source control for CollectionCmpPda Map pairs.

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

    Map producers supply paired entries with unit repetitions. Original totals
    remain stored and exhaustion compares those totals: no normalization or
    source-enumeration completeness follows from this projection. The two
    remaining counters are still represented, including left initialization
    before discovering that the right roster is exhausted.

    This file concerns successful native control. Protocol errors, admission,
    overflow, owned-slot inventory and refusal cleanup retain their existing
    committed models. A raw relation with no successful derivation for invalid
    ingress is not an assertion that the implementation silently accepts it.
    Box-in-task interpretation and parked-owner noninterference must use those
    ownership laws; task-list frame preservation alone does not prove them.

    The local response/copy laws here do not yet assert a whole Map segment
    theorem. The remaining connective proof is an induction that projects the
    existing sequenced MapEvents witness to RawResume paths through silent
    copies, reset/swap and phase changes, retaining its arbitrary-prefix answer
    frontier. No completed-core hypothesis is substituted for that induction.
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

Definition initial_map maximum left_items right_items left_total right_total :=
  map_state (initial_merge maximum left_items) (initial_merge maximum right_items)
    Lead None Eq left_total right_total 0 0 0 0.

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

Definition initialize_left_remaining state :=
  set_lex state (map_left_index state) (map_right_index state)
    (if map_left_remaining state =? 0 then 1 else map_left_remaining state)
    (map_right_remaining state).
Definition initialize_both_remaining state :=
  set_lex state (map_left_index state) (map_right_index state)
    (if map_left_remaining state =? 0 then 1 else map_left_remaining state)
    (if map_right_remaining state =? 0 then 1 else map_right_remaining state).
Definition advance_equal state :=
  let consumed := Nat.min (map_left_remaining state) (map_right_remaining state) in
  let lr := map_left_remaining state - consumed in
  let rr := map_right_remaining state - consumed in
  set_lex state
    (if lr =? 0 then S (map_left_index state) else map_left_index state)
    (if rr =? 0 then S (map_right_index state) else map_right_index state) lr rr.

Inductive RawRequest := PrimaryRequest (lhs rhs : Key) | SecondaryRequest (lhs rhs : Value).
Inductive RawReply := Requests (request : RawRequest) | Completes (ordering : comparison).

(** These are existing call-stack locations, not fields added to the Box. *)
Inductive RawControl :=
| Ingress (input : option comparison)
| PhaseLoop
| RequestItem (destination : RawDestination) (lhs rhs : Entry)
| RequestSecondary (destination : RawDestination) (lhs rhs : Entry)
| AcceptItem (destination : RawDestination) (ordering : comparison)
| ReturnReply (reply : RawReply).

Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Variable maximum : nat.

Inductive RawCoreStep : RawControl -> RawMapState -> RawControl -> RawMapState -> Prop :=
| IngressInitial : forall state,
    map_pending state = None -> RawCoreStep (Ingress None) state PhaseLoop state
| IngressPrimaryEqual : forall state lhs rhs destination,
    map_pending state = Some (PendingPrimary lhs rhs destination) ->
    RawCoreStep (Ingress (Some Eq)) state (RequestSecondary destination lhs rhs)
      (set_pending state None)
| IngressPrimaryDecisive : forall state lhs rhs destination ordering,
    map_pending state = Some (PendingPrimary lhs rhs destination) -> ordering <> Eq ->
    RawCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
      (set_pending state None)
| IngressSecondary : forall state destination ordering,
    map_pending state = Some (PendingSecondary destination) ->
    RawCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
      (set_pending state None)
| LoopEqualLead : forall state,
    map_phase state = Lead -> map_lead state = Eq ->
    RawCoreStep PhaseLoop state PhaseLoop (set_phase state SortLeft)
| LoopDecisiveLead : forall state,
    map_phase state = Lead -> map_lead state <> Eq ->
    RawCoreStep PhaseLoop state (ReturnReply (Completes (map_lead state))) (set_phase state Done)
| LoopLeftRequest : forall state lhs rhs next,
    map_phase state = SortLeft ->
    RawMergeStep maximum (map_left state) (MergeRequests lhs rhs) next ->
    RawCoreStep PhaseLoop state (RequestItem ToLeftSort lhs rhs) (set_left state next)
| LoopRightRequest : forall state lhs rhs next,
    map_phase state = SortRight ->
    RawMergeStep maximum (map_right state) (MergeRequests lhs rhs) next ->
    RawCoreStep PhaseLoop state (RequestItem ToRightSort lhs rhs) (set_right state next)
| LoopLeftDone : forall state next,
    map_phase state = SortLeft -> RawMergeStep maximum (map_left state) MergeCompletes next ->
    RawCoreStep PhaseLoop state PhaseLoop
      (set_phase (set_left state (merge_set_target next None)) SortRight)
| LoopRightDone : forall state next,
    map_phase state = SortRight -> RawMergeStep maximum (map_right state) MergeCompletes next ->
    RawCoreStep PhaseLoop state PhaseLoop
      (set_phase (set_right state (merge_set_target next None)) Lexicographic)
| LoopLeftExhausted : forall state,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = None ->
    RawCoreStep PhaseLoop state
      (ReturnReply (Completes (Nat.compare (map_left_total state) (map_right_total state))))
      (set_phase state Done)
| LoopRightExhausted : forall state lhs,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = Some lhs ->
    nth_error (merge_source (map_right state)) (map_right_index state) = None ->
    RawCoreStep PhaseLoop state
      (ReturnReply (Completes (Nat.compare (map_left_total state) (map_right_total state))))
      (set_phase (initialize_left_remaining state) Done)
| LoopLexRequest : forall state lhs rhs,
    map_phase state = Lexicographic ->
    nth_error (merge_source (map_left state)) (map_left_index state) = Some lhs ->
    nth_error (merge_source (map_right state)) (map_right_index state) = Some rhs ->
    RawCoreStep PhaseLoop state (RequestItem ToLexicographic lhs rhs)
      (initialize_both_remaining state)
| RequestAliasedPrimary : forall state destination lhs rhs,
    key_alias (fst lhs) (fst rhs) = true ->
    RawCoreStep (RequestItem destination lhs rhs) state
      (RequestSecondary destination lhs rhs) state
| RequestFreshPrimary : forall state destination lhs rhs,
    key_alias (fst lhs) (fst rhs) = false ->
    RawCoreStep (RequestItem destination lhs rhs) state
      (ReturnReply (Requests (PrimaryRequest (fst lhs) (fst rhs))))
      (set_pending state (Some (PendingPrimary lhs rhs destination)))
| RequestAliasedSecondary : forall state destination lhs rhs,
    value_alias (snd lhs) (snd rhs) = true ->
    RawCoreStep (RequestSecondary destination lhs rhs) state (AcceptItem destination Eq) state
| RequestFreshSecondary : forall state destination lhs rhs,
    value_alias (snd lhs) (snd rhs) = false ->
    RawCoreStep (RequestSecondary destination lhs rhs) state
      (ReturnReply (Requests (SecondaryRequest (snd lhs) (snd rhs))))
      (set_pending state (Some (PendingSecondary destination)))
| AcceptLeft : forall state ordering next,
    raw_merge_accept (map_left state) ordering = Some next ->
    RawCoreStep (AcceptItem ToLeftSort ordering) state PhaseLoop (set_left state next)
| AcceptRight : forall state ordering next,
    raw_merge_accept (map_right state) ordering = Some next ->
    RawCoreStep (AcceptItem ToRightSort ordering) state PhaseLoop (set_right state next)
| AcceptLexEqual : forall state,
    RawCoreStep (AcceptItem ToLexicographic Eq) state PhaseLoop (advance_equal state)
| AcceptLexDecisive : forall state ordering,
    ordering <> Eq ->
    RawCoreStep (AcceptItem ToLexicographic ordering) state PhaseLoop (set_lead state ordering).

Inductive RawCorePath : RawControl -> RawMapState -> RawControl -> RawMapState -> Prop :=
| CorePathRefl : forall control state, RawCorePath control state control state
| CorePathMore : forall control state middle middle_state last next,
    RawCoreStep control state middle middle_state ->
    RawCorePath middle middle_state last next ->
    RawCorePath control state last next.

Definition RawResume state input reply next :=
  RawCorePath (Ingress input) state (ReturnReply reply) next.

Theorem raw_secondary_ingress_accepts_every_ordering : forall state destination ordering,
  map_pending state = Some (PendingSecondary destination) ->
  RawCoreStep (Ingress (Some ordering)) state (AcceptItem destination ordering)
    (set_pending state None).
Proof. intros. now apply IngressSecondary. Qed.

Theorem primary_equal_does_not_mutate_either_sort : forall state,
  map_left (set_pending state None) = map_left state /\
  map_right (set_pending state None) = map_right state.
Proof. intro state. split; reflexivity. Qed.

Theorem raw_core_paths_compose : forall first state middle middle_state last next,
  RawCorePath first state middle middle_state ->
  RawCorePath middle middle_state last next -> RawCorePath first state last next.
Proof.
  intros first state middle middle_state last next PATH REST.
  induction PATH; [exact REST|]. eapply CorePathMore; eauto.
Qed.

Theorem every_raw_core_step_preserves_original_totals :
  forall control state next_control next,
  RawCoreStep control state next_control next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof. intros control state next_control next STEP. destruct STEP; split; reflexivity. Qed.

Theorem every_raw_resume_preserves_original_totals : forall state input reply next,
  RawResume state input reply next ->
  map_left_total next = map_left_total state /\ map_right_total next = map_right_total state.
Proof.
  intros state input reply next PATH. unfold RawResume in PATH.
  induction PATH; [split; reflexivity|].
  destruct (every_raw_core_step_preserves_original_totals _ _ _ _ H) as [L R].
  destruct IHPATH as [LN RN]. split; congruence.
Qed.

Theorem unit_equal_advance_updates_both_original_indices : forall state,
  map_left_remaining state = 1 -> map_right_remaining state = 1 ->
  map_left_index (advance_equal state) = S (map_left_index state) /\
  map_right_index (advance_equal state) = S (map_right_index state) /\
  map_left_remaining (advance_equal state) = 0 /\
  map_right_remaining (advance_equal state) = 0.
Proof.
  intros state L R. unfold advance_equal. rewrite L, R.
  repeat split; reflexivity.
Qed.
End MapControl.

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
    chosen by the raw relation. The future whole-spine proof must establish
    this hypothesis from the completed child's lower-height factor theorem. *)
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
