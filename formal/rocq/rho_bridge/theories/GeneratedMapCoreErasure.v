(** Erasure of proof-only annotations from the EXISTING raw Map control.
    Erasure changes only carried operands. It retains original cursor values,
    widths, counts, pending destinations, buffer option shapes, control labels
    and supplied comparison answers. No comparator, fallback class, new
    executor or runtime storage is introduced.

    Later control lifting requires only compatibility of the original alias
    predicates with operand erasure, not injectivity or a semantic-result
    premise. These equalities describe the same successful source operations
    under a change of operand representation. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import GeneratedMapCoreSource MergeSortPdaCursor
  MergeSortPdaNativeRun.
Import ListNotations.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import MergeSortPdaCursor.MergeSortPdaCursor.

Module GeneratedMapCoreErasure.

Section MergeErasure.
Context {SourceEntry TargetEntry : Type}.
Variable erase : SourceEntry -> TargetEntry.

Definition erase_merge (state : @RawMergeState SourceEntry) : @RawMergeState TargetEntry :=
  merge_state (map erase (merge_source state))
    (option_map (map erase) (merge_target state))
    (merge_width state) (merge_cursor state) (merge_waiting state) (merge_done state).

Definition erase_merge_reply (reply : @RawMergeReply SourceEntry) : @RawMergeReply TargetEntry :=
  match reply with MergeRequests lhs rhs => MergeRequests (erase lhs) (erase rhs)
    | MergeCompletes => MergeCompletes end.

Theorem overwrite_erasure : forall index value items,
  overwrite index (erase value) (map erase items) =
    option_map (map erase) (overwrite index value items).
Proof.
  induction index as [|index IH]; intros value [|head rest];
    cbn [overwrite map]; try reflexivity.
  rewrite IH. destruct (overwrite index value rest); reflexivity.
Qed.

Theorem copy_record_erasure : forall side cursor source target,
  copy_record side cursor (map erase source) (map erase target) =
    option_map (fun output => (fst output, map erase (snd output)))
      (copy_record side cursor source target).
Proof.
  intros side cursor source target. unfold copy_record.
  rewrite nth_error_map.
  destruct (nth_error source (selected_index side cursor)) as [value|]; [|reflexivity].
  cbn [option_map]. rewrite overwrite_erasure.
  destruct (overwrite (output_index cursor) value target); reflexivity.
Qed.

Theorem original_indexed_request_erases_to_the_same_read_positions :
  forall source cursor lhs rhs,
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest source cursor lhs rhs ->
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest
    (map erase source) cursor (erase lhs) (erase rhs).
Proof.
  intros source cursor lhs rhs [LEFT [RIGHT [READ_LEFT READ_RIGHT]]].
  split; [exact LEFT|]. split; [exact RIGHT|]. split;
    rewrite nth_error_map; [rewrite READ_LEFT|rewrite READ_RIGHT]; reflexivity.
Qed.

Theorem initial_merge_erasure : forall maximum source,
  erase_merge (initial_merge maximum source) = initial_merge maximum (map erase source).
Proof.
  intros. unfold erase_merge, initial_merge.
  cbn [merge_state merge_source merge_target merge_width merge_cursor merge_waiting merge_done].
  now rewrite length_map.
Qed.

Theorem scratch_replacement_erasure : forall state target,
  erase_merge (merge_set_target state target) =
    merge_set_target (erase_merge state) (option_map (map erase) target).
Proof. reflexivity. Qed.

Theorem waiting_flag_erasure : forall state waiting,
  erase_merge (merge_set_waiting state waiting) =
    merge_set_waiting (erase_merge state) waiting.
Proof. reflexivity. Qed.

Theorem indexed_copy_payload_erasure : forall state cursor target,
  erase_merge (merge_after_copy state cursor target) =
    merge_after_copy (erase_merge state) cursor (map erase target).
Proof. reflexivity. Qed.

Theorem original_run_boundary_erasure : forall maximum state completed,
  erase_merge (merge_after_run maximum state completed) =
    merge_after_run maximum (erase_merge state) (map erase completed).
Proof.
  intros maximum state completed. unfold merge_after_run.
  cbn [erase_merge merge_state merge_source merge_cursor merge_width].
  rewrite !length_map.
  destruct (run_end (merge_cursor state) <? length (merge_source state));
    [reflexivity|].
  destruct (length completed <=? saturated_double maximum (merge_width state)); reflexivity.
Qed.

Theorem supplied_merge_response_erasure : forall state ordering,
  raw_merge_accept (erase_merge state) ordering =
    option_map erase_merge (raw_merge_accept state ordering).
Proof.
  intros [source target width cursor waiting done] ordering.
  unfold raw_merge_accept.
  cbn [erase_merge merge_state merge_source merge_target merge_width merge_cursor merge_waiting merge_done].
  destruct waiting; [|reflexivity].
  destruct target as [target|]; [|reflexivity].
  cbn [option_map].
  rewrite copy_record_erasure.
  destruct (copy_record (accept_side ordering) cursor source target) as [[next_cursor next]|];
    reflexivity.
Qed.

Theorem silent_merge_operation_erasure : forall maximum state next,
  RawMergeSilent maximum state next ->
  RawMergeSilent maximum (erase_merge state) (erase_merge next).
Proof.
  intros maximum state next STEP. destruct STEP.
  - rewrite scratch_replacement_erasure.
    apply MergeAllocatesScratch; cbn [erase_merge merge_state merge_waiting merge_done merge_target];
      try assumption. now rewrite H1.
  - rewrite indexed_copy_payload_erasure.
    eapply MergeLeftTail with (target := map erase target);
      cbn [erase_merge merge_state merge_waiting merge_done merge_target merge_cursor merge_source];
      try assumption.
    + now rewrite H1.
    + rewrite copy_record_erasure, H4. reflexivity.
  - rewrite indexed_copy_payload_erasure.
    eapply MergeRightTail with (target := map erase target);
      cbn [erase_merge merge_state merge_waiting merge_done merge_target merge_cursor merge_source];
      try assumption.
    + now rewrite H1.
    + rewrite copy_record_erasure, H4. reflexivity.
  - rewrite original_run_boundary_erasure.
    eapply MergeEndsRun;
      cbn [erase_merge merge_state merge_waiting merge_done merge_target merge_cursor];
      try assumption. now rewrite H1.
Qed.

Theorem returned_merge_step_erasure : forall maximum state reply next,
  RawMergeStep maximum state reply next ->
  RawMergeStep maximum (erase_merge state) (erase_merge_reply reply) (erase_merge next).
Proof.
  intros maximum state reply next STEP. induction STEP.
  - apply MergeStepDone; assumption.
  - rewrite waiting_flag_erasure. cbn [erase_merge_reply].
    eapply MergeStepRequests with (target := map erase target);
      cbn [erase_merge merge_state merge_waiting merge_done merge_target merge_cursor merge_source];
      try assumption.
    + now rewrite H1.
    + now apply original_indexed_request_erases_to_the_same_read_positions.
  - eapply MergeStepInternal with (middle := erase_merge middle).
    + exact (silent_merge_operation_erasure _ _ _ H).
    + exact IHSTEP.
Qed.
End MergeErasure.

Section MapErasure.
Context {SourceKey SourceValue TargetKey TargetValue : Type}.
Variable erase_key : SourceKey -> TargetKey.
Variable erase_value : SourceValue -> TargetValue.

Definition erase_entry (entry : SourceKey * SourceValue) : TargetKey * TargetValue :=
  (erase_key (fst entry), erase_value (snd entry)).

Definition erase_pending (pending : @RawPending SourceKey SourceValue) :
    @RawPending TargetKey TargetValue :=
  match pending with
  | PendingPrimary lhs rhs destination =>
      PendingPrimary (erase_entry lhs) (erase_entry rhs) destination
  | PendingSecondary destination => PendingSecondary destination
  end.

Definition erase_request (request : @RawRequest SourceKey SourceValue) :
    @RawRequest TargetKey TargetValue :=
  match request with
  | PrimaryRequest lhs rhs => PrimaryRequest (erase_key lhs) (erase_key rhs)
  | SecondaryRequest lhs rhs => SecondaryRequest (erase_value lhs) (erase_value rhs)
  end.

Definition erase_reply (reply : @RawReply SourceKey SourceValue) :
    @RawReply TargetKey TargetValue :=
  match reply with
  | Requests request => Requests (erase_request request)
  | Completes ordering => Completes ordering
  end.

Definition erase_control (control : @RawControl SourceKey SourceValue) :
    @RawControl TargetKey TargetValue :=
  match control with
  | Ingress input => Ingress input
  | PhaseLoop => PhaseLoop
  | RequestItem destination lhs rhs =>
      RequestItem destination (erase_entry lhs) (erase_entry rhs)
  | RequestSecondary destination lhs rhs =>
      RequestSecondary destination (erase_entry lhs) (erase_entry rhs)
  | AcceptItem destination ordering => AcceptItem destination ordering
  | ReturnReply reply => ReturnReply (erase_reply reply)
  end.

Definition erase_map (state : @RawMapState SourceKey SourceValue) :
    @RawMapState TargetKey TargetValue :=
  map_state (erase_merge erase_entry (map_left state))
    (erase_merge erase_entry (map_right state)) (map_phase state)
    (option_map erase_pending (map_pending state)) (map_lead state)
    (map_left_total state) (map_right_total state)
    (map_left_index state) (map_right_index state)
    (map_left_remaining state) (map_right_remaining state).

Theorem initial_map_erasure : forall maximum lhs rhs left_total right_total,
  erase_map (initial_map maximum lhs rhs left_total right_total) =
    initial_map maximum (map erase_entry lhs) (map erase_entry rhs) left_total right_total.
Proof.
  intros. unfold initial_map, erase_map.
  cbn [map_state map_left map_right map_phase map_pending map_lead map_left_total
    map_right_total map_left_index map_right_index map_left_remaining map_right_remaining].
  now rewrite !initial_merge_erasure.
Qed.

Theorem pending_payload_erasure : forall state pending,
  erase_map (set_pending state pending) =
    set_pending (erase_map state) (option_map erase_pending pending).
Proof. reflexivity. Qed.

Theorem phase_payload_erasure : forall state phase,
  erase_map (set_phase state phase) = set_phase (erase_map state) phase.
Proof. reflexivity. Qed.

Theorem left_payload_erasure : forall state next,
  erase_map (set_left state next) = set_left (erase_map state) (erase_merge erase_entry next).
Proof. reflexivity. Qed.

Theorem right_payload_erasure : forall state next,
  erase_map (set_right state next) = set_right (erase_map state) (erase_merge erase_entry next).
Proof. reflexivity. Qed.

Theorem lead_payload_erasure : forall state ordering,
  erase_map (set_lead state ordering) = set_lead (erase_map state) ordering.
Proof. reflexivity. Qed.

Theorem lex_payload_erasure : forall state li ri lr rr,
  erase_map (set_lex state li ri lr rr) = set_lex (erase_map state) li ri lr rr.
Proof. reflexivity. Qed.

Theorem left_counter_initialization_erasure : forall state,
  erase_map (initialize_left_remaining state) = initialize_left_remaining (erase_map state).
Proof. reflexivity. Qed.

Theorem both_counter_initialization_erasure : forall state,
  erase_map (initialize_both_remaining state) = initialize_both_remaining (erase_map state).
Proof. reflexivity. Qed.

Theorem equal_run_advance_erasure : forall state,
  erase_map (advance_equal state) = advance_equal (erase_map state).
Proof. reflexivity. Qed.

Variable source_key_alias : SourceKey -> SourceKey -> bool.
Variable source_value_alias : SourceValue -> SourceValue -> bool.
Variable target_key_alias : TargetKey -> TargetKey -> bool.
Variable target_value_alias : TargetValue -> TargetValue -> bool.
Hypothesis key_alias_compatible : forall lhs rhs,
  target_key_alias (erase_key lhs) (erase_key rhs) = source_key_alias lhs rhs.
Hypothesis value_alias_compatible : forall lhs rhs,
  target_value_alias (erase_value lhs) (erase_value rhs) = source_value_alias lhs rhs.

(** Every case is a constructor of the existing successful source relation.
    Comparison answers are never recomputed during transport. *)
Theorem actual_core_step_erasure : forall maximum control state next_control next,
  @RawCoreStep SourceKey SourceValue source_key_alias source_value_alias maximum
    control state next_control next ->
  @RawCoreStep TargetKey TargetValue target_key_alias target_value_alias maximum
    (erase_control control) (erase_map state) (erase_control next_control) (erase_map next).
Proof.
  intros maximum control state next_control next STEP. destruct STEP;
    cbn [erase_control erase_reply erase_request];
    rewrite ?pending_payload_erasure, ?phase_payload_erasure,
      ?left_payload_erasure, ?right_payload_erasure, ?lead_payload_erasure,
      ?left_counter_initialization_erasure, ?both_counter_initialization_erasure,
      ?equal_run_advance_erasure, ?scratch_replacement_erasure;
    cbn [option_map erase_pending].
  - apply IngressInitial.
    change (option_map erase_pending (map_pending state) = None). now rewrite H.
  - apply IngressPrimaryEqual.
    change (option_map erase_pending (map_pending state) =
      Some (PendingPrimary (erase_entry lhs) (erase_entry rhs) destination)). now rewrite H.
  - eapply IngressPrimaryDecisive with (lhs := erase_entry lhs) (rhs := erase_entry rhs).
    + change (option_map erase_pending (map_pending state) =
        Some (PendingPrimary (erase_entry lhs) (erase_entry rhs) destination)). now rewrite H.
    + exact H0.
  - apply IngressSecondary.
    change (option_map erase_pending (map_pending state) = Some (PendingSecondary destination)).
    now rewrite H.
  - apply LoopEqualLead; assumption.
  - apply LoopDecisiveLead with (state := erase_map state); assumption.
  - eapply LoopLeftRequest; [exact H|].
    exact (returned_merge_step_erasure erase_entry _ _ _ _ H0).
  - eapply LoopRightRequest; [exact H|].
    exact (returned_merge_step_erasure erase_entry _ _ _ _ H0).
  - eapply LoopLeftDone; [exact H|].
    exact (returned_merge_step_erasure erase_entry _ _ _ _ H0).
  - eapply LoopRightDone; [exact H|].
    exact (returned_merge_step_erasure erase_entry _ _ _ _ H0).
  - apply LoopLeftExhausted with (state := erase_map state); [exact H|].
    change (nth_error (map erase_entry (merge_source (map_left state)))
      (map_left_index state) = None). now rewrite nth_error_map, H0.
  - eapply LoopRightExhausted with (state := erase_map state) (lhs := erase_entry lhs);
      [exact H| |].
    + change (nth_error (map erase_entry (merge_source (map_left state)))
        (map_left_index state) = Some (erase_entry lhs)). now rewrite nth_error_map, H0.
    + change (nth_error (map erase_entry (merge_source (map_right state)))
        (map_right_index state) = None). now rewrite nth_error_map, H1.
  - eapply LoopLexRequest; [exact H| |].
    + change (nth_error (map erase_entry (merge_source (map_left state)))
        (map_left_index state) = Some (erase_entry lhs)). now rewrite nth_error_map, H0.
    + change (nth_error (map erase_entry (merge_source (map_right state)))
        (map_right_index state) = Some (erase_entry rhs)). now rewrite nth_error_map, H1.
  - apply RequestAliasedPrimary.
    change (target_key_alias (erase_key (fst lhs)) (erase_key (fst rhs)) = true).
    now rewrite key_alias_compatible.
  - apply RequestFreshPrimary.
    change (target_key_alias (erase_key (fst lhs)) (erase_key (fst rhs)) = false).
    now rewrite key_alias_compatible.
  - apply RequestAliasedSecondary.
    change (target_value_alias (erase_value (snd lhs)) (erase_value (snd rhs)) = true).
    now rewrite value_alias_compatible.
  - apply RequestFreshSecondary.
    change (target_value_alias (erase_value (snd lhs)) (erase_value (snd rhs)) = false).
    now rewrite value_alias_compatible.
  - apply AcceptLeft.
    change (raw_merge_accept (erase_merge erase_entry (map_left state)) ordering =
      Some (erase_merge erase_entry next)). now rewrite supplied_merge_response_erasure, H.
  - apply AcceptRight.
    change (raw_merge_accept (erase_merge erase_entry (map_right state)) ordering =
      Some (erase_merge erase_entry next)). now rewrite supplied_merge_response_erasure, H.
  - apply AcceptLexEqual.
  - apply AcceptLexDecisive. exact H.
Qed.

Theorem actual_core_path_erasure : forall maximum control state last next,
  @RawCorePath SourceKey SourceValue source_key_alias source_value_alias maximum
    control state last next ->
  @RawCorePath TargetKey TargetValue target_key_alias target_value_alias maximum
    (erase_control control) (erase_map state) (erase_control last) (erase_map next).
Proof.
  intros maximum control state last next PATH. induction PATH.
  - apply CorePathRefl.
  - eapply CorePathMore.
    + exact (actual_core_step_erasure _ _ _ _ _ H).
    + exact IHPATH.
Qed.

Theorem actual_resume_erasure : forall maximum state input reply next,
  @RawResume SourceKey SourceValue source_key_alias source_value_alias maximum
    state input reply next ->
  @RawResume TargetKey TargetValue target_key_alias target_value_alias maximum
    (erase_map state) input (erase_reply reply) (erase_map next).
Proof.
  intros maximum state input reply next RESUME.
  exact (actual_core_path_erasure maximum _ _ _ _ RESUME).
Qed.

Definition erase_answer (answer : (@RawRequest SourceKey SourceValue) * comparison) :
    (@RawRequest TargetKey TargetValue) * comparison :=
  (erase_request (fst answer), snd answer).

(** The same answer sequence traverses the same first-return cuts. Erasure
    changes the requested operands, not the comparison evidence supplied by
    the caller, nor the exact retained payload at any suspension. *)
Theorem actual_raw_dialogue_erasure : forall maximum control state answers last next,
  @RawDialogue SourceKey SourceValue source_key_alias source_value_alias maximum
    control state answers last next ->
  @RawDialogue TargetKey TargetValue target_key_alias target_value_alias maximum
    (erase_control control) (erase_map state) (map erase_answer answers)
    (erase_control last) (erase_map next).
Proof.
  intros maximum control state answers last next DIALOGUE. induction DIALOGUE.
  - apply DialogueQuiet. exact (actual_core_path_erasure _ _ _ _ _ H).
  - cbn [map erase_answer fst snd]. eapply DialogueAnswer.
    + exact (actual_core_path_erasure _ _ _ _ _ H).
    + exact IHDIALOGUE.
Qed.
End MapErasure.

End GeneratedMapCoreErasure.

Print Assumptions GeneratedMapCoreErasure.overwrite_erasure.
Print Assumptions GeneratedMapCoreErasure.copy_record_erasure.
Print Assumptions GeneratedMapCoreErasure.original_indexed_request_erases_to_the_same_read_positions.
Print Assumptions GeneratedMapCoreErasure.initial_merge_erasure.
Print Assumptions GeneratedMapCoreErasure.scratch_replacement_erasure.
Print Assumptions GeneratedMapCoreErasure.waiting_flag_erasure.
Print Assumptions GeneratedMapCoreErasure.indexed_copy_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.original_run_boundary_erasure.
Print Assumptions GeneratedMapCoreErasure.supplied_merge_response_erasure.
Print Assumptions GeneratedMapCoreErasure.silent_merge_operation_erasure.
Print Assumptions GeneratedMapCoreErasure.returned_merge_step_erasure.
Print Assumptions GeneratedMapCoreErasure.initial_map_erasure.
Print Assumptions GeneratedMapCoreErasure.pending_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.phase_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.left_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.right_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.lead_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.lex_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.left_counter_initialization_erasure.
Print Assumptions GeneratedMapCoreErasure.both_counter_initialization_erasure.
Print Assumptions GeneratedMapCoreErasure.equal_run_advance_erasure.
Print Assumptions GeneratedMapCoreErasure.actual_core_step_erasure.
Print Assumptions GeneratedMapCoreErasure.actual_core_path_erasure.
Print Assumptions GeneratedMapCoreErasure.actual_resume_erasure.
Print Assumptions GeneratedMapCoreErasure.actual_raw_dialogue_erasure.
