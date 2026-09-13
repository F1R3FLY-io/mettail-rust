(** Consumed checked sorting wrapper around the existing MergeSortPda.

    Source: collection_cmp_pda.rs MergeSortPda::new/step/accept/reset_run/
    release_scratch; CheckedCollectionSortPda and its readonly result.
    New pays root2W1R before core initialization and Box allocation; existing
    new/reset each pay1. Resume pays ingress/Option dispatch1, then existing
    accept (Some) or step (None); core guards pay before waiting inspection.
    Outbound dispatch1 precedes Compare transfer or Done. Done pays existing
    release_scratch1, then extraction/Box-release/publication1.

    Readonly sorted output retains only the current source allocation. It
    never recovers CheckedCmpRoster.reserved_width: scratch may have only the
    filled width after swaps. Pop1 includes terminal None; pair projection1
    validates flat Some-secondary/unit-repetition metadata, without AST reads.

    This is ownership, gating and wrapper erasure, not another sorting model
    or a comparator/Hash theorem. Existing NativeOuter supplies final output.
    Existing take-once slots supply Rust move correspondence; Coq records are
    not linear. Allocation internals and panic recovery remain separate. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import AdmittedCollectionComparisonOwnership
  AdmittedGeneratedHashScheduling AdmittedGeneratedComparisonScheduling
  AdmittedKeyHashExecution AdmittedStructuralKeyHash
  GeneratedDummyCleanupReservation RholangInitialGraphResources
  MergeSortPdaNativeOuter.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.
Import AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.

Module AdmittedCollectionSortOwnership.

Inductive WrapperGroup := SortRoot | Ingress | StepDispatch | ExtractSource
  | SortedPop | PairProjection.
Definition wrapper_work group := match group with SortRoot => 2 | _ => 1 end.
Definition wrapper_units group := match group with SortRoot => 4 | _ => 0 end.
Definition wrapper_counts group := match group with
  | SortRoot => AdmittedKeyHashExecution.AdmittedKeyHashExecution.push_range_counts 1
  | _ => AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.work_counts 1
  end.
Theorem wrapper_groups_reuse_existing_logical_units : forall group,
  GeneratedDummyCleanupReservation.weighted
    GeneratedDummyCleanupReservation.logical_work_weight (wrapper_counts group) = wrapper_work group /\
  GeneratedDummyCleanupReservation.weighted
    GeneratedDummyCleanupReservation.logical_unit_weight (wrapper_counts group) = wrapper_units group.
Proof.
  intro group. destruct group;
    try apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.logical_work_only_projection.
  exact (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.raw_push_reservation_uses_four_units_per_record 1).
Qed.

Definition admit_wrapper {Value} group available (action : unit -> option Value) :=
  precharged_action false available (wrapper_work group) (wrapper_units group) action.
Theorem wrapper_refusal_precedes_its_action : forall Value group available
  (action : unit -> option Value),
  reserve available (wrapper_work group) (wrapper_units group) = None ->
  admit_wrapper group available action = Refused available.
Proof. intros. apply failed_precharge_is_independent_of_constructor. assumption. Qed.
Definition admit_new_root {Value} (supported : bool) available (action : unit -> option Value) :=
  if supported then admit_wrapper SortRoot available action else Refused available.
Theorem unsupported_profile_never_enters_root_action : forall Value available
  (action : unit -> option Value), admit_new_root false available action = Refused available.
Proof. reflexivity. Qed.

Inductive InputFailure := UnrequestedResult | MissingResult.
Inductive HeaderResult := EnterStep | EnterAcceptedCopy (ordering : comparison)
  | InputRejected (reason : InputFailure).
Definition inspect_waiting waiting result := match result, waiting with
  | None, false => EnterStep
  | None, true => InputRejected MissingResult
  | Some ordering, true => EnterAcceptedCopy ordering
  | Some _, false => InputRejected UnrequestedResult
  end.
(** The second1 is the existing accept-route or step-entry group, not a new
    wrapper check. EnterAcceptedCopy still owes the existing copy reservation. *)
Definition admit_resume_header waiting result available :=
  match admit_wrapper Ingress available (fun _ => Some result) with
  | Refused remaining => Refused remaining
  | Accepted remaining response => precharged_action false remaining 1 0
      (fun _ => Some (inspect_waiting waiting response))
  end.
Theorem resume_ingress_refusal_never_inspects_waiting : forall waiting result available,
  reserve available 1 0 = None ->
  admit_resume_header waiting result available = Refused available.
Proof.
  intros waiting result available H. unfold admit_resume_header, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H.
Qed.
Theorem existing_core_guard_is_paid_before_protocol_inspection :
  forall waiting result available ingress,
  reserve available 1 0 = Some ingress -> reserve ingress 1 0 = None ->
  admit_resume_header waiting result available = Refused ingress.
Proof.
  intros waiting result available ingress H1 H2.
  unfold admit_resume_header, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H1, H2.
Qed.
Theorem unrequested_result_fails_after_the_two_existing_groups :
  forall ordering available ingress guarded,
  reserve available 1 0 = Some ingress -> reserve ingress 1 0 = Some guarded ->
  admit_resume_header false (Some ordering) available =
    Accepted guarded (InputRejected UnrequestedResult).
Proof.
  intros ordering available ingress guarded H1 H2.
  unfold admit_resume_header, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H1, H2.
Qed.
Theorem missing_result_fails_after_the_two_existing_groups : forall available ingress guarded,
  reserve available 1 0 = Some ingress -> reserve ingress 1 0 = Some guarded ->
  admit_resume_header true None available = Accepted guarded (InputRejected MissingResult).
Proof.
  intros available ingress guarded H1 H2.
  unfold admit_resume_header, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H1, H2.
Qed.

Section ReadonlyOutput.
Context {Item : Type}.
Record SortedRoster := {
  sorted_source : list Item;
  sorted_allocation : Buffer
}.
Definition valid_sorted roster := buffer_valid (sorted_allocation roster) /\
  initialized_width (sorted_allocation roster) = length (sorted_source roster).
Definition extract_sorted source allocation :=
  {| sorted_source := source; sorted_allocation := allocation |}.
(** Proof-only last-element view of the one native Vec::pop. No runtime
    reverse traversal or copied roster is prescribed. *)
Definition native_pop (source : list Item) := match rev source with
  | [] => (None, [])
  | item :: rest => (Some item, rev rest)
  end.
Theorem native_pop_removes_exactly_the_last_source_entry : forall prefix item,
  native_pop (prefix ++ [item]) = (Some item, prefix).
Proof.
  intros. unfold native_pop. rewrite rev_app_distr. cbn.
  now rewrite rev_involutive.
Qed.
Theorem native_empty_pop_is_terminal : native_pop [] = (None, []).
Proof. reflexivity. Qed.
Definition admit_sorted_pop roster available :=
  admit_wrapper SortedPop available (fun _ => Some (native_pop (sorted_source roster))).
Theorem failed_pop_does_not_execute_the_native_pop : forall roster available,
  reserve available 1 0 = None -> admit_sorted_pop roster available = Refused available.
Proof. intros. apply wrapper_refusal_precedes_its_action. exact H. Qed.

Definition remaining_allocation buffer count :=
  {| allocation_id := allocation_id buffer; admitted_width := admitted_width buffer;
     initialized_width := count |}.
Theorem removing_an_entry_retains_valid_paid_storage : forall prefix item allocation,
  valid_sorted (extract_sorted (prefix ++ [item]) allocation) ->
  valid_sorted (extract_sorted prefix (remaining_allocation allocation (length prefix))) /\
  forall event, buffer_credit (remaining_allocation allocation (length prefix)) event =
                buffer_credit allocation event.
Proof.
  intros prefix item allocation [HV HL].
  change (initialized_width allocation <= admitted_width allocation) in HV.
  change (initialized_width allocation = length (prefix ++ [item])) in HL.
  rewrite length_app in HL. cbn in HL. split.
  - unfold valid_sorted, extract_sorted, remaining_allocation, buffer_valid; cbn.
    split; [lia|reflexivity].
  - intro event. reflexivity.
Qed.
Theorem readonly_result_cleanup_uses_current_source_credit : forall roster event,
  valid_sorted roster ->
  buffer_cleanup (sorted_allocation roster) event <=
  buffer_credit (sorted_allocation roster) event.
Proof. intros roster event [HV _]. now apply buffer_cleanup_is_prepaid. Qed.

(** These stages mirror target=None and then moving source out of Box.
    Cleanup ownership on either refusal is the existing terminal owner
    law: terminal_resume_returns_no_owner_handle with ResumeFailed. *)
Definition admit_done source allocation available :=
  match precharged_action false available 1 0 (fun _ => Some tt) with
  | Refused remaining => Refused remaining
  | Accepted remaining _ => admit_wrapper ExtractSource remaining
      (fun _ => Some (extract_sorted source allocation))
  end.
Theorem release_refusal_precedes_source_extraction : forall source allocation available,
  reserve available 1 0 = None -> admit_done source allocation available = Refused available.
Proof. intros. unfold admit_done, precharged_action. now rewrite H. Qed.
Theorem extraction_refusal_does_not_publish_a_sorted_owner :
  forall source allocation available released,
  reserve available 1 0 = Some released -> reserve released 1 0 = None ->
  admit_done source allocation available = Refused released.
Proof.
  intros source allocation available released H1 H2.
  unfold admit_done, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H1, H2.
Qed.
Theorem successful_done_transfers_the_exact_source_allocation :
  forall source allocation available released paid,
  reserve available 1 0 = Some released -> reserve released 1 0 = Some paid ->
  admit_done source allocation available = Accepted paid (extract_sorted source allocation).
Proof.
  intros source allocation available released paid H1 H2.
  unfold admit_done, admit_wrapper.
  cbn [wrapper_work wrapper_units precharged_action]. now rewrite H1, H2.
Qed.
Theorem final_buffer_release_partitions_existing_credit : forall source scratch event,
  inventory_credit (source :: scratch) event =
  buffer_credit source event + inventory_credit scratch event.
Proof. reflexivity. Qed.
End ReadonlyOutput.

Section PairMetadata.
Context {Primary Secondary : Type}.
Definition pair_parts (entry : @Entry Primary Secondary) :=
  match secondary entry, repetitions entry with
  | Some value, 1 => Some (primary entry, value)
  | _, _ => None
  end.
(** Accepted None denotes the subsequent InvalidCollectionInput return,
    not budget refusal and not a synthesized comparison result. *)
Definition admit_pair_parts entry available :=
  admit_wrapper PairProjection available (fun _ => Some (pair_parts entry)).
Theorem rejected_pair_projection_does_not_inspect_metadata : forall entry available,
  reserve available 1 0 = None -> admit_pair_parts entry available = Refused available.
Proof. intros. apply wrapper_refusal_precedes_its_action. exact H. Qed.
Theorem unit_pair_projection_is_exact : forall left right,
  pair_parts {| primary := left; secondary := Some right; repetitions := 1 |} = Some (left,right).
Proof. reflexivity. Qed.
Theorem unary_is_not_a_sort_pair : forall left count,
  pair_parts {| primary := left; secondary := None; repetitions := count |} = None.
Proof. intros. destruct count; reflexivity. Qed.
End PairMetadata.

Import AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Section WrapperTrace.
Context {Observation : Type}.
Definition quiet counts : @Event Observation :=
  {| event_receipt := counts; event_call := None; event_supported := true |}.
(** core contains the existing accept/step events, including scratch creation,
    every internal control/copy and requested comparison. Release follows the
    outbound Done dispatch and is therefore kept in this exact suffix. *)
Definition wrapped_resume (core : list (@Event Observation)) (completed : bool) :=
  quiet (wrapper_counts Ingress) ::
  (core ++ (quiet (wrapper_counts StepDispatch) ::
    if completed then
      [quiet (control_counts ReleaseScratch); quiet (wrapper_counts ExtractSource)]
    else [])).
Theorem silent_wrapper_keeps_the_exact_core_observations : forall core completed,
  ordinary_calls (wrapped_resume core completed) = ordinary_calls core.
Proof.
  intros core completed. unfold wrapped_resume, ordinary_calls.
  cbn [map concat quiet call_list]. rewrite map_app, concat_app.
  destruct completed; cbn [map concat quiet call_list]; now rewrite app_nil_r.
Qed.
Theorem successful_wrapper_admission_keeps_the_core_trace : forall core completed available,
  succeeded (admitted_events (wrapped_resume core completed) available) = true ->
  observed_calls (admitted_events (wrapped_resume core completed) available) = ordinary_calls core.
Proof.
  intros core completed available H.
  pose proof (admission_success_erases_to_same_native_calls
    (wrapped_resume core completed) available H) as E.
  now rewrite silent_wrapper_keeps_the_exact_core_observations in E.
Qed.
Theorem refused_wrapper_observes_only_a_core_prefix : forall core completed available,
  exists suffix, ordinary_calls core =
    observed_calls (admitted_events (wrapped_resume core completed) available) ++ suffix.
Proof.
  intros core completed available.
  destruct (every_result_is_an_original_call_prefix
    (wrapped_resume core completed) available) as [suffix E].
  exists suffix. now rewrite silent_wrapper_keeps_the_exact_core_observations in E.
Qed.
End WrapperTrace.

Section ExistingNativeResult.
Context {Item State : Type}.
Variable compare : Item -> Item -> State -> option comparison * State.
Theorem done_publication_reuses_the_existing_native_sort_result :
  forall maximum count source state output scratch last allocation available paid published,
  length source <= maximum ->
  @MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    Item State compare maximum count 1 source None state output scratch last ->
  admit_done output allocation available = Accepted paid published ->
  @SemanticResultMerge.SemanticResultMerge.sort Item State compare source state =
    (Some (sorted_source published), last).
Proof.
  intros maximum count source state output scratch last allocation available paid published HM HE HP.
  unfold admit_done in HP.
  destruct (precharged_action false available 1 0 (fun _ => Some tt))
    as [remaining|remaining released] eqn:RELEASE; [discriminate|].
  unfold admit_wrapper in HP.
  apply successful_action_constructs_only_the_paid_result in HP.
  destruct HP as [_ [BUILD _]]. cbn in BUILD.
  injection BUILD as E. subst published.
  cbn [sorted_source extract_sorted].
  exact (@MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.actual_native_sort_has_the_existing_sort_result
    Item State compare maximum count source state output scratch last HM HE).
Qed.
End ExistingNativeResult.

Print Assumptions wrapper_groups_reuse_existing_logical_units.
Print Assumptions wrapper_refusal_precedes_its_action.
Print Assumptions unsupported_profile_never_enters_root_action.
Print Assumptions resume_ingress_refusal_never_inspects_waiting.
Print Assumptions existing_core_guard_is_paid_before_protocol_inspection.
Print Assumptions unrequested_result_fails_after_the_two_existing_groups.
Print Assumptions missing_result_fails_after_the_two_existing_groups.
Print Assumptions native_pop_removes_exactly_the_last_source_entry.
Print Assumptions native_empty_pop_is_terminal.
Print Assumptions failed_pop_does_not_execute_the_native_pop.
Print Assumptions removing_an_entry_retains_valid_paid_storage.
Print Assumptions readonly_result_cleanup_uses_current_source_credit.
Print Assumptions release_refusal_precedes_source_extraction.
Print Assumptions extraction_refusal_does_not_publish_a_sorted_owner.
Print Assumptions successful_done_transfers_the_exact_source_allocation.
Print Assumptions final_buffer_release_partitions_existing_credit.
Print Assumptions rejected_pair_projection_does_not_inspect_metadata.
Print Assumptions unit_pair_projection_is_exact.
Print Assumptions unary_is_not_a_sort_pair.
Print Assumptions silent_wrapper_keeps_the_exact_core_observations.
Print Assumptions successful_wrapper_admission_keeps_the_core_trace.
Print Assumptions refused_wrapper_observes_only_a_core_prefix.
Print Assumptions done_publication_reuses_the_existing_native_sort_result.
End AdmittedCollectionSortOwnership.
