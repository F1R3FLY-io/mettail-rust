(** Typed paid rosters and owned collection-comparison admission.

    Source: runtime/src/collection_cmp_pda.rs. Existing collection and
    MergeSortPda mutations are shared by private ordinary Infallible and
    checked policies. This model concerns reservation, storage-owner transfer
    and source Compare/Done observations, not another sort engine, global
    mergesort correctness, comparator coherence or parity with a different sort.

    A private roster reserves a width, accepts a filled prefix and caches the
    checked repetition sum. Filled <= reserved is intentional: unused credits
    are conservative. This does not prove source iteration completeness or
    cover native hash-table bucket scanning. Bag's supplied lead, derived from
    stored total_count, remains separate from actual positive repetitions.
    Binding reconstruction can retain zero-count entries; checked construction
    rejects those rather than silently changing the ordinary repeated recipe.

    flat_slots(n) pays metadata 1, then 2*(n+1) NativeWork and n+1 NativeRecord
    before allocation/copy. Each record projects to four raw units. Each push
    pays control 1 before zero/width/checked-total validation; flat construction
    and eventual disposal are prepaid. Zero/full are protocol errors, not size
    overflow. Checked creation consumes two paid rosters: root Box 2W/1R,
    from-parts 1, and each merge init 1/reset 1; cached sums need no rescan.

    Scratch uses the original source.clone. CollectionCmpItem derives Clone,
    Copy; pinned core clone.rs253-261 supplies TrivialClone, Vec clone3917-3927
    forwards to alloc/slice.rs444-460, allocating and copying flat records.
    No term Clone executes. These are logical source/slot charges, not physical
    memcpy or allocator bounds. Copies create new storage occurrences even
    when pointers coincide; partial overwrites need not preserve a permutation
    of pointer values. Buffer swaps transfer credit; release consumes cleanup.

    The private non-Clone checked owner is constructed only from paid rosters,
    never arbitrary ordinary Vec/Box/core. By-value resume returns an owner
    only with Compare; Done/error disposes its paid storage. Refusal may follow
    partial core mutation: there is no rollback promise. Indexed owner slots
    model consumption before resumption. Coq records themselves are duplicable;
    Rust moves/private constructors/source-borrow validity remain explicit
    correspondence obligations. Borrowed task-shell credit is additional to
    owned machine credit, not a replacement for it.

    Every named control group costs 1W before its action except exhausted
    usize comparison 2W. MergeOuterAttempt pays the !done guard;
    MergeCompareReady pays the following readiness predicate on EVERY entered
    iteration, before the predicate. RunEnd covers start=end and the pass
    predicate; PassFinish is paid only on its taken branch. Called groups pay
    separately. Only reached guards count: no terminal guard after break.
    External requested term comparisons retain their own provider contract. *)
From Stdlib Require Import List Arith Bool Lia Sorting.Permutation.
From RhoBridge Require Import IndexedCopySlots AdmittedStructuralKeyHash
  AdmittedKeyHashExecution AdmittedGeneratedHashScheduling
  AdmittedGeneratedComparisonScheduling GeneratedBindingOutputReservation
  GeneratedDummyCleanupReservation RholangSourceScope RholangInitialGraphResources.
Import ListNotations.

Module AdmittedCollectionComparisonOwnership.
Module C := IndexedCopySlots.IndexedCopySlots.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module H := AdmittedKeyHashExecution.AdmittedKeyHashExecution.
Module G := AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.
Module A := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.
Module O := GeneratedBindingOutputReservation.GeneratedBindingOutputReservation.
Module D := GeneratedDummyCleanupReservation.

Inductive ProtocolFailure := ZeroRepetitions | RosterFull | InvalidResume.
Inductive BuildFailure := ProtocolRejected (reason : ProtocolFailure) | SizeOverflow.
Inductive BuildResult (T : Type) := Built (value : T) | Rejected (reason : BuildFailure).
Arguments Built {T} _.
Arguments Rejected {T} _.

Section TypedRosters.
Context {Primary Secondary : Type}.
(** Labels for immutable typed source borrows, not owned ASTs. *)
Record Entry := { primary : Primary; secondary : option Secondary; repetitions : nat }.
Record Roster := { reserved_width : nat; entries : list Entry; running_total : nat }.
Definition repetition_sum := fold_right (fun entry total => repetitions entry + total) 0.
Definition valid_roster roster :=
  length (entries roster) <= reserved_width roster /\
  Forall (fun entry => 0 < repetitions entry) (entries roster) /\
  running_total roster = repetition_sum (entries roster).
Definition empty_roster width := {| reserved_width := width; entries := []; running_total := 0 |}.
Definition try_push maximum roster entry :=
  if repetitions entry =? 0 then Rejected (ProtocolRejected ZeroRepetitions) else
  if length (entries roster) <? reserved_width roster then
    match checked_sum maximum (running_total roster) (repetitions entry) with
    | None => Rejected SizeOverflow
    | Some total => Built {| reserved_width := reserved_width roster;
                            entries := entries roster ++ [entry]; running_total := total |}
    end
  else Rejected (ProtocolRejected RosterFull).
Definition after_push maximum roster entry := match try_push maximum roster entry with
  | Built next => next | Rejected _ => roster end.

Lemma repetition_sum_snoc : forall prefix entry,
  repetition_sum (prefix ++ [entry]) = repetition_sum prefix + repetitions entry.
Proof.
  intro prefix. induction prefix as [|head rest IH]; intro entry.
  - cbn [repetition_sum fold_right app]. lia.
  - change (repetitions head + repetition_sum (rest ++ [entry]) =
      repetitions head + repetition_sum rest + repetitions entry).
    rewrite IH. lia.
Qed.
Theorem empty_roster_is_valid : forall width, valid_roster (empty_roster width).
Proof. intro width. unfold valid_roster, empty_roster. cbn.
  split; [lia|]. split; [constructor|reflexivity]. Qed.
Theorem successful_push_preserves_prefix_width_and_total : forall maximum roster entry next,
  valid_roster roster -> try_push maximum roster entry = Built next ->
  valid_roster next /\ reserved_width next = reserved_width roster /\
  entries next = entries roster ++ [entry] /\
  running_total next = running_total roster + repetitions entry /\ running_total next <= maximum.
Proof.
  intros maximum roster entry next [HW [HP HT]] HB. unfold try_push in HB.
  destruct (repetitions entry =? 0) eqn:HZ; [discriminate|].
  destruct (length (entries roster) <? reserved_width roster) eqn:HF; [|discriminate].
  destruct (checked_sum maximum (running_total roster) (repetitions entry)) as [total|] eqn:HS;
    [|discriminate].
  apply Nat.eqb_neq in HZ. apply Nat.ltb_lt in HF.
  apply checked_sum_success_is_exact_and_bounded in HS. inversion HB; subst next.
  unfold valid_roster. cbn [reserved_width entries running_total].
  rewrite length_app, repetition_sum_snoc. cbn [length].
  assert (HP' : Forall (fun item => 0 < repetitions item) (entries roster ++ [entry])).
  { apply Forall_app. split; [exact HP|]. constructor; [lia|constructor]. }
  repeat split; try assumption; try reflexivity; lia.
Qed.
Theorem zero_repetition_is_protocol_failure : forall maximum roster entry,
  repetitions entry = 0 -> try_push maximum roster entry = Rejected (ProtocolRejected ZeroRepetitions).
Proof. intros maximum roster entry HZ. unfold try_push. rewrite HZ. reflexivity. Qed.
Theorem full_roster_is_protocol_failure : forall maximum roster entry,
  0 < repetitions entry -> reserved_width roster <= length (entries roster) ->
  try_push maximum roster entry = Rejected (ProtocolRejected RosterFull).
Proof.
  intros maximum roster entry HP HF. unfold try_push.
  assert (HZ : (repetitions entry =? 0) = false) by (apply Nat.eqb_neq; lia).
  assert (HW : (length (entries roster) <? reserved_width roster) = false) by (apply Nat.ltb_ge; lia).
  now rewrite HZ, HW.
Qed.
Theorem rejected_push_preserves_roster : forall maximum roster entry reason,
  try_push maximum roster entry = Rejected reason -> after_push maximum roster entry = roster.
Proof. intros maximum roster entry reason HR. unfold after_push. now rewrite HR. Qed.
Definition admitted_push maximum roster entry available :=
  precharged_action false available 1 0 (fun _ => Some (try_push maximum roster entry)).
Theorem push_reservation_precedes_validation : forall maximum roster entry available,
  reserve available 1 0 = None -> admitted_push maximum roster entry available = Refused available.
Proof. intros. now apply failed_precharge_is_independent_of_constructor. Qed.
Definition core_initial_totals (_lead : comparison) left_roster right_roster :=
  (running_total left_roster, running_total right_roster).
Theorem lead_does_not_replace_roster_totals : forall lead left_roster right_roster,
  valid_roster left_roster -> valid_roster right_roster ->
  core_initial_totals lead left_roster right_roster =
    (repetition_sum (entries left_roster), repetition_sum (entries right_roster)).
Proof. intros lead left_roster right_roster [_ [_ HL]] [_ [_ HR]].
  unfold core_initial_totals. now rewrite HL, HR. Qed.
End TypedRosters.

Definition flat_counts width := H.push_range_counts (width + 1).
Theorem flat_slots_include_header_and_record_disposal : forall width,
  D.weighted D.logical_work_weight (flat_counts width) = 2 * (width + 1) /\
  D.weighted D.logical_unit_weight (flat_counts width) = 4 * (width + 1).
Proof. intros. apply G.raw_push_reservation_uses_four_units_per_record. Qed.
(** Repeated checked additions correspond to the runtime checked products. *)
Theorem checked_flat_reservation_is_exact : forall maximum width slots work units,
  checked_sum maximum width 1 = Some slots -> checked_sum maximum slots slots = Some work ->
  checked_sum maximum work work = Some units ->
  slots = width + 1 /\ work = 2 * (width + 1) /\ units = 4 * (width + 1) /\
  slots <= maximum /\ work <= maximum /\ units <= maximum.
Proof.
  intros maximum width slots work units HS HW HU.
  apply checked_sum_success_is_exact_and_bounded in HS, HW, HU. repeat split; lia.
Qed.

(** Allocated slots, not an intermediate pointer-value permutation. *)
Record Buffer := { allocation_id : nat; admitted_width : nat; initialized_width : nat }.
Definition buffer_valid buffer := initialized_width buffer <= admitted_width buffer.
Definition buffer_credit buffer := flat_counts (admitted_width buffer).
Definition buffer_cleanup buffer := H.pending_disposal_counts (initialized_width buffer + 1).
Definition inventory_credit := O.sum_counts buffer_credit.
Definition inventory_cleanup := O.sum_counts buffer_cleanup.
Theorem buffer_cleanup_is_prepaid : forall buffer event,
  buffer_valid buffer -> buffer_cleanup buffer event <= buffer_credit buffer event.
Proof.
  intros buffer event HV. unfold buffer_valid in HV.
  unfold buffer_cleanup, buffer_credit, flat_counts, H.pending_disposal_counts, H.push_range_counts. nia.
Qed.
Theorem inventory_cleanup_is_prepaid : forall buffers event,
  Forall buffer_valid buffers -> inventory_cleanup buffers event <= inventory_credit buffers event.
Proof.
  intros buffers event HV. induction HV as [|buffer rest HB HR IH].
  - reflexivity.
  - change (buffer_cleanup buffer event + inventory_cleanup rest event <=
      buffer_credit buffer event + inventory_credit rest event).
    pose proof (buffer_cleanup_is_prepaid buffer event HB). lia.
Qed.
Theorem buffer_swap_preserves_owned_credit : forall first second rest event,
  inventory_credit (first :: second :: rest) event = inventory_credit (second :: first :: rest) event.
Proof. intros. apply O.sum_counts_permutation. apply perm_swap. Qed.
Theorem release_partitions_existing_credit : forall released remaining event,
  inventory_credit (released ++ remaining) event =
    inventory_credit released event + inventory_credit remaining event.
Proof. intros. apply O.sum_counts_app. Qed.
Definition scratch_buffer fresh source :=
  {| allocation_id := fresh; admitted_width := initialized_width source;
     initialized_width := initialized_width source |}.
Theorem scratch_has_new_slot_extent : forall fresh source,
  buffer_valid (scratch_buffer fresh source) /\
  initialized_width (scratch_buffer fresh source) = initialized_width source /\
  admitted_width (scratch_buffer fresh source) = initialized_width source.
Proof. intros. repeat split; try reflexivity. apply Nat.le_refl. Qed.
Definition slot_owner (buffer : Buffer) (index : nat) := (allocation_id buffer, index).
Definition valid_inventory buffers :=
  Forall buffer_valid buffers /\ NoDup (map allocation_id buffers).
Theorem fresh_scratch_extends_unique_inventory : forall buffers fresh source,
  valid_inventory buffers -> ~ In fresh (map allocation_id buffers) ->
  valid_inventory (scratch_buffer fresh source :: buffers).
Proof.
  intros buffers fresh source [HV HU] HF. split.
  - constructor; [unfold buffer_valid, scratch_buffer; cbn; lia|exact HV].
  - cbn [map scratch_buffer allocation_id]. constructor; assumption.
Qed.
Theorem fresh_buffers_have_disjoint_slot_identities : forall first second i j,
  allocation_id first <> allocation_id second -> slot_owner first i <> slot_owner second j.
Proof. intros first second i j HD HE. unfold slot_owner in HE. inversion HE. contradiction. Qed.

Section OwnerSlots.
Context {Core : Type}.
Record Owner := { owned_buffers : list Buffer; core_state : Core }.
Definition take_owner index tag (slots : @C.Slots Owner) := C.take_slot index tag slots.
Theorem owner_handle_is_taken_once : forall index tag slots owner emptied,
  take_owner index tag slots = Some (owner, emptied) -> take_owner index tag emptied = None.
Proof.
  intros index tag slots owner emptied HT. unfold take_owner in *.
  exact (proj1 (C.take_once index tag slots owner emptied HT)).
Qed.
Inductive ResumeExit := AwaitComparison | ComparisonDone | ResumeFailed.
Definition finish_owner_transfer exit index tag next_owner (emptied : @C.Slots Owner) :=
  match exit with
  | AwaitComparison => C.write_slot tag tag next_owner index emptied
  | ComparisonDone | ResumeFailed => Some emptied
  end.
Theorem terminal_resume_returns_no_owner_handle : forall exit index tag slots owner emptied next_owner,
  take_owner index tag slots = Some (owner, emptied) -> exit <> AwaitComparison ->
  finish_owner_transfer exit index tag next_owner emptied = Some emptied /\
  take_owner index tag emptied = None.
Proof.
  intros exit index tag slots owner emptied next_owner HT HE.
  pose proof (owner_handle_is_taken_once index tag slots owner emptied HT) as HN.
  destruct exit; [contradiction|split; assumption || reflexivity|split; assumption || reflexivity].
Qed.
Theorem transferred_owner_cannot_fill_the_same_slot_twice : forall index tag owner emptied next other,
  finish_owner_transfer AwaitComparison index tag owner emptied = Some next ->
  C.write_slot tag tag other index next = None.
Proof.
  intros index tag owner emptied next other HW. unfold finish_owner_transfer in HW.
  exact (proj1 (C.write_once tag tag owner index emptied next other HW)).
Qed.
End OwnerSlots.

Inductive ControlGroup := ResumeEntry | PhaseAttempt | SortReturn | RequestPrimary
| RequestSecondary | AcceptTerm | AcceptItem | CurrentLeft | CurrentRight | EqualRun
| ExhaustedTotalCmp | MergeInit | ResetRun | MergeStepEntry | MergeOuterAttempt
| MergeCompareReady | LeftTailAttempt | RightTailAttempt | TailCopy | RunEnd
| PassFinish | MergeAcceptRoute | MergeAcceptCopy | ReleaseScratch | FromParts.
Definition control_work group := match group with ExhaustedTotalCmp => 2 | _ => 1 end.
Definition control_counts group := S.work_counts (control_work group).
Theorem control_groups_use_only_the_named_work : forall group,
  D.weighted D.logical_work_weight (control_counts group) = control_work group /\
  D.weighted D.logical_unit_weight (control_counts group) = 0.
Proof. intros. apply A.logical_work_only_projection. Qed.

(** Local facts only: exact stable-left branch and positive run advance. *)
Inductive MergeSide := LeftRun | RightRun.
Definition merge_choice ordering := match ordering with Gt => RightRun | _ => LeftRun end.
Theorem equal_merge_result_selects_left :
  merge_choice Eq = LeftRun /\ merge_choice Lt = LeftRun /\ merge_choice Gt = RightRun.
Proof. repeat split; reflexivity. Qed.
Theorem positive_equal_run_exhausts_an_entry : forall lhs rhs,
  0 < lhs -> 0 < rhs -> 0 < Nat.min lhs rhs /\
  (lhs - Nat.min lhs rhs = 0 \/ rhs - Nat.min lhs rhs = 0).
Proof.
  intros lhs rhs HL HR. destruct (Nat.le_ge_cases lhs rhs) as [HC|HC].
  - rewrite Nat.min_l by lia. lia.
  - rewrite Nat.min_r by lia. lia.
Qed.

Section SourceObservations.
Context {Primary Secondary : Type}.
Inductive Observation := ComparePrimary (lhs rhs : Primary)
| CompareSecondary (lhs rhs : Secondary) | Done (ordering : comparison).
Definition Event := @G.Event Observation.
Theorem successful_policy_erases_to_original_requests : forall (events : list Event) available,
  G.succeeded (G.admitted_events events available) = true ->
  G.observed_calls (G.admitted_events events available) = G.ordinary_calls events.
Proof. apply G.admission_success_erases_to_same_native_calls. Qed.
Theorem policy_refusal_is_an_original_observation_prefix : forall (events : list Event) available,
  exists suffix, G.ordinary_calls events = G.observed_calls (G.admitted_events events available) ++ suffix.
Proof. apply G.every_result_is_an_original_call_prefix. Qed.
Definition publish_step (events : list Event) (original : Observation) available :=
  if G.succeeded (G.admitted_events events available) then Some original else None.
Theorem refusing_resume_does_not_publish_a_step : forall events original available,
  G.succeeded (G.admitted_events events available) = false -> publish_step events original available = None.
Proof. intros events original available HF. unfold publish_step. now rewrite HF. Qed.
End SourceObservations.

Print Assumptions successful_push_preserves_prefix_width_and_total.
Print Assumptions zero_repetition_is_protocol_failure.
Print Assumptions full_roster_is_protocol_failure.
Print Assumptions rejected_push_preserves_roster.
Print Assumptions push_reservation_precedes_validation.
Print Assumptions lead_does_not_replace_roster_totals.
Print Assumptions flat_slots_include_header_and_record_disposal.
Print Assumptions checked_flat_reservation_is_exact.
Print Assumptions buffer_cleanup_is_prepaid.
Print Assumptions inventory_cleanup_is_prepaid.
Print Assumptions buffer_swap_preserves_owned_credit.
Print Assumptions release_partitions_existing_credit.
Print Assumptions scratch_has_new_slot_extent.
Print Assumptions fresh_buffers_have_disjoint_slot_identities.
Print Assumptions fresh_scratch_extends_unique_inventory.
Print Assumptions owner_handle_is_taken_once.
Print Assumptions terminal_resume_returns_no_owner_handle.
Print Assumptions transferred_owner_cannot_fill_the_same_slot_twice.
Print Assumptions control_groups_use_only_the_named_work.
Print Assumptions equal_merge_result_selects_left.
Print Assumptions positive_equal_run_exhausts_an_entry.
Print Assumptions successful_policy_erases_to_original_requests.
Print Assumptions policy_refusal_is_an_original_observation_prefix.
Print Assumptions refusing_resume_does_not_publish_a_step.
End AdmittedCollectionComparisonOwnership.
