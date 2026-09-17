(** Logical reconstruction-stage composition for runtime/src/hashbag.rs.

    This is NOT another hash table or a verification of standard-library
    instructions. The pinned library remains a source-reviewed dependency.
    Existing native models supply original candidate occurrence inclusion,
    group bounds, clean growth geometry, scan bounds and transfer counts.
    This file composes those quantities with COMPLETE typed Hash/Eq receipts.
    Those receipts include descendants and scratch; leaf-only charges cannot
    instantiate them. All equations apply separately to work, records and
    bytes, so scratch and nonconstant callback bodies are not erased.

    Occurrence IDs identify original stored records, not key equality classes
    or Arc addresses. A source association maps each ID to its actual key.
    CandidateCover supplies NoDup/inclusion for the real candidate prefix;
    resize transports the same original records. Equality orientation is
    Binding incoming.eq(stored), Clone stored.eq(incoming). A summary winner
    is a retained occurrence, never a reconstructed representative.

    Named scalar groups below are declared logical operations. Group loads
    retain their established one-group plus sixteen-byte read convention.
    Metadata inspection is spent separately through the paid runtime visitors
    and BindingCharge accumulator. Normal root destruction uses existing
    independent ownership receipts; these flat charges never replace them.
    Panic recovery, exact allocator/instruction costs and stdlib internals
    belong to the subsequent refinement milestone. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import NativeInspectionAccumulation
  RequiredHashBagBindingReservation RequiredVecBindingReservation
  NativeHashBagScanBound RholangInitialGraphResources.
Import ListNotations.

Module NativeHashBagStageCharge.
Module C := NativeInspectionAccumulation.NativeInspectionAccumulation.
Module B := RequiredHashBagBindingReservation.RequiredHashBagBindingReservation.
Module S := NativeHashBagScanBound.NativeHashBagScanBound.

Section SourceOperands.
Context {Key : Type}.
Variable key_at : nat -> Key.
Variable hash : Key -> nat.
Variable equal : Key -> Key -> nat.

Definition total (cost : nat -> nat) (ids : list nat) :=
  fold_right (fun id rest => cost id + rest) 0 ids.

Lemma total_app : forall cost left right,
  total cost (left ++ right) = total cost left + total cost right.
Proof.
  intros cost left. induction left as [|id tail IH]; intro right.
  - reflexivity.
  - change (cost id + total cost (tail ++ right) =
      (cost id + total cost tail) + total cost right).
    rewrite IH. lia.
Qed.

(** No arbitrary callback count: each selected original occurrence can
    consume its own allowance once. This instantiates CandidateCover's
    NoDup and inclusion, and retains collisions and alias multiplicities. *)
Lemma candidate_total_is_covered : forall cost selected retained,
  NoDup selected -> incl selected retained ->
  total cost selected <= total cost retained.
Proof.
  intros cost selected retained DISTINCT. revert retained.
  induction DISTINCT as [|id tail NOTIN DISTINCT IH]; intros retained INCLUDE.
  - apply Nat.le_0_l.
  - assert (MEMBER : In id retained) by (apply INCLUDE; now left).
    apply in_split in MEMBER as [before [after ->]].
    assert (REST : incl tail (before ++ after)).
    { intros x MEMBER. specialize (INCLUDE x (or_intror MEMBER)).
      apply in_app_or in INCLUDE as [LEFT|[SAME|RIGHT]].
      - apply in_or_app. now left.
      - subst x. contradiction.
      - apply in_or_app. now right. }
    specialize (IH _ REST). rewrite total_app in IH |- *.
    change (cost id + total cost tail <=
      total cost before + (cost id + total cost after)). lia.
Qed.

Lemma retained_winner_is_covered : forall id retained,
  In id retained -> hash (key_at id) <= total (fun s => hash (key_at s)) retained.
Proof.
  intros id retained MEMBER.
  pose proof (candidate_total_is_covered (fun s => hash (key_at s)) [id]
    retained) as COVER.
  assert (DISTINCT : NoDup [id]) by (constructor; [intro H; exact H|constructor]).
  assert (INCLUDE : incl [id] retained).
  { intros x [SAME|IMPOSSIBLE]; [now subst x|contradiction]. }
  specialize (COVER DISTINCT INCLUDE).
  change (hash (key_at id) + 0 <= total (fun s => hash (key_at s)) retained) in COVER.
  lia.
Qed.

Definition rehash (growth : bool) retained :=
  if growth then total (fun s => hash (key_at s)) retained else 0.
Definition binding_envelope incoming growth retained :=
  hash incoming + rehash growth retained +
  total (fun s => equal incoming (key_at s)) retained.
Definition clone_envelope incoming growth retained :=
  3 * hash incoming + rehash growth retained +
  4 * total (fun s => hash (key_at s)) retained +
  total (fun s => equal (key_at s) incoming) retained.

Theorem binding_candidate_prefix_is_covered :
  forall incoming growth retained candidates,
  NoDup candidates -> incl candidates retained ->
  hash incoming + rehash growth retained +
    total (fun s => equal incoming (key_at s)) candidates <=
  binding_envelope incoming growth retained.
Proof.
  intros. unfold binding_envelope.
  pose proof (candidate_total_is_covered (fun s => equal incoming (key_at s))
    candidates retained H H0). lia.
Qed.

(** A vacant entry hashes its incoming key twice for its summary. Occupied
    entry summary hashes the ORIGINAL winner four times, with old/new counts.
    The scalar count hashes and summary arithmetic belong to flat groups. *)
Theorem clone_vacant_is_covered : forall incoming growth retained candidates,
  NoDup candidates -> incl candidates retained ->
  hash incoming + rehash growth retained +
    total (fun s => equal (key_at s) incoming) candidates + 2 * hash incoming <=
  clone_envelope incoming growth retained.
Proof.
  intros. unfold clone_envelope.
  pose proof (candidate_total_is_covered (fun s => equal (key_at s) incoming)
    candidates retained H H0). lia.
Qed.

Theorem clone_occupied_is_covered : forall incoming growth retained candidates winner,
  NoDup candidates -> incl candidates retained -> In winner retained ->
  hash incoming + total (fun s => equal (key_at s) incoming) candidates +
    4 * hash (key_at winner) <= clone_envelope incoming growth retained.
Proof.
  intros. unfold clone_envelope.
  pose proof (candidate_total_is_covered (fun s => equal (key_at s) incoming)
    candidates retained H H0).
  pose proof (retained_winner_is_covered _ _ H1). lia.
Qed.

Definition final_summary_envelope retained :=
  2 * total (fun s => hash (key_at s)) retained.

Theorem final_summary_is_two_original_hashes : forall retained,
  total (fun s => 2 * hash (key_at s)) retained = final_summary_envelope retained.
Proof.
  intro retained. unfold final_summary_envelope.
  induction retained as [|id tail IH].
  - reflexivity.
  - change (2 * hash (key_at id) + total (fun s => 2 * hash (key_at s)) tail =
      2 * (hash (key_at id) + total (fun s => hash (key_at s)) tail)).
    rewrite IH. lia.
Qed.
End SourceOperands.

(** Flat groups. All inputs are actual source metadata or prospective clean
    geometry, obtained by PAID inspection. Native scans are already proved
    under arbitrary nonnegative event weights; this reuses their published
    4r+19q projection. q is positive, including the singleton.

    Probe groups: initialization; loads (1+16); tag matching; successful and
    exhausted mask advances; candidate projection; insertion-cache decision;
    EMPTY/return decision; cursor advance; at most one repair load. Reserving
    all groups also covers lookup-only/placement-only paths. Callback bodies
    are explicitly NOT included. This is a logical grouped-operation policy,
    not an exact instruction count for hashbrown. *)
Definition probe_flat groups candidates :=
  1 + 17 * groups + groups + (candidates + groups) + candidates +
  groups + groups + (groups - 1) + 17.

Theorem probe_flat_projection : forall groups candidates,
  0 < groups -> probe_flat groups candidates = 22 * groups + 2 * candidates + 17.
Proof. intros. unfold probe_flat. lia. Qed.

Definition retained_inspection_flat entries groups :=
  1 + S.borrowed_scan_work entries groups + (entries + 1).
Theorem retained_inspection_projection : forall entries groups,
  retained_inspection_flat entries groups = 5 * entries + 19 * groups + 2.
Proof. intros. unfold retained_inspection_flat, S.borrowed_scan_work. lia. Qed.

(** Shell and mode selection: two fixed groups; input iterator boundary:
    three groups/one record; successful advances: width. Generated container
    cleanup reuses bag_cleanup's 6+2width work and 2+width records. Native
    backing-table cleanup remains separate below. Input-vector and key-root
    ownership is already paid by the producer, including Start refusal. *)
Definition start_flat width : C.Charge :=
  {| C.base_work := 2 + 3 + width + (6 + 2 * width);
     C.records := 1 + 1 + (2 + width); C.owned_bytes := 0 |}.

(** Direct retained-table cleanup has at most six wrapper invocations,
    one fresh scan, and one destructor dispatch per stored occurrence.
    This conservatively includes the scan even when native guards skip it.
    Root destructor bodies have existing independent receipts. *)
Definition retained_cleanup_flat entries groups :=
  6 + S.borrowed_scan_work entries groups + entries.

(** Source resize: old scan, one hash-dispatch wrapper and target placement
    for each original record (the complete key Hash body is separate),
    two control writes + two pointer projections per record, tuple-byte copy,
    EMPTY initialization, and allocation/finalization/release groups.
    Target allocation BYTES are a separate storage contribution, not copy
    work; allocator internals are outside this logical policy. *)
Definition resize_flat entries old_groups new_groups buckets tuple_size :=
  S.borrowed_scan_work entries old_groups + entries * probe_flat new_groups 0 +
  entries + 4 * entries + entries * tuple_size + (buckets + 16) + 3.

Definition insert_flat (mode : B.Mode) (growth : bool) entries old_groups new_groups buckets tuple_size
    allocation_bytes : C.Charge :=
  {| C.base_work :=
       1 +
       (match mode with
        | B.BindingEntries => probe_flat new_groups entries
        | B.CloneEntries => probe_flat old_groups entries + probe_flat new_groups 0 + 4
        end) +
       (if growth then resize_flat entries old_groups new_groups buckets tuple_size else 0) +
       retained_cleanup_flat (S entries) new_groups;
     C.records := if growth then 1 else 0;
     C.owned_bytes := if growth then allocation_bytes else 0 |}.

(** A zero-count Clone still executes the reconstruction wrapper's mode and
    checked-total guard before insert_n tests the count. Keep the existing
    insertion-wrapper group and the zero-test group distinct. Start's fixed
    shell charge and the provider's metadata inspection pay neither of these
    per-insertion native groups. The incoming root's disposal is already paid
    by its producer; no Hash, Eq, probe or growth occurs on this branch. *)
Definition clone_zero_flat : C.Charge :=
  {| C.base_work := 1 + 1; C.records := 0; C.owned_bytes := 0 |}.

Theorem clone_zero_flat_projection :
  C.projected_work clone_zero_flat = 2 /\
  C.projected_units clone_zero_flat = 0.
Proof. split; reflexivity. Qed.

(** Final summary: one default/assignment group, then one fixed lane-recipe
    group and one add-to-summary group per entry; two structural Hash bodies
    per entry are supplied by final_summary_envelope instead. *)
Definition summary_flat entries groups : C.Charge :=
  {| C.base_work := S.borrowed_scan_work entries groups + 1 + 2 * entries;
     C.records := 0; C.owned_bytes := 0 |}.

(** Use the EXISTING checked BindingCharge addition. Input contributions may
    be inspected/accumulated separately; neither failed construction nor a
    later rejected reservation refunds those earlier metadata charges. *)
Definition paid_stage {A} maximum cancelled available flat callbacks
    (build : unit -> option A) :=
  match C.charge_add maximum flat callbacks with
  | None => Refused available
  | Some charge => precharged_action cancelled available
      (C.projected_work charge) (C.projected_units charge) build
  end.

Theorem stage_overflow_precedes_native_action :
  forall A maximum cancelled available flat callbacks (build : unit -> option A),
  maximum < C.projected_work flat + C.projected_work callbacks \/
  maximum < C.projected_units flat + C.projected_units callbacks ->
  paid_stage maximum cancelled available flat callbacks build = Refused available.
Proof.
  intros. unfold paid_stage.
  destruct (C.charge_add maximum flat callbacks) as [charge|] eqn:ADD; [|reflexivity].
  apply C.charge_add_success in ADD.
  unfold C.representable, C.projected_work, C.projected_units in *. exfalso. lia.
Qed.

Theorem stage_cancellation_precedes_native_action :
  forall A maximum available flat callbacks (build : unit -> option A),
  paid_stage maximum true available flat callbacks build = Refused available.
Proof.
  intros. unfold paid_stage. destruct (C.charge_add maximum flat callbacks);
    reflexivity.
Qed.

Theorem stage_budget_refusal_precedes_native_action :
  forall A maximum available flat callbacks charge (build : unit -> option A),
  C.charge_add maximum flat callbacks = Some charge ->
  reserve available (C.projected_work charge) (C.projected_units charge) = None ->
  paid_stage maximum false available flat callbacks build = Refused available.
Proof.
  intros. unfold paid_stage. rewrite H.
  now apply failed_precharge_is_independent_of_constructor.
Qed.

Theorem accepted_stage_pays_both_contributions :
  forall A maximum cancelled available flat callbacks (build : unit -> option A) paid value,
  paid_stage maximum cancelled available flat callbacks build = Accepted paid value ->
  cancelled = false /\ build tt = Some value /\
  work_left paid + C.projected_work flat + C.projected_work callbacks = work_left available /\
  units_left paid + C.projected_units flat + C.projected_units callbacks = units_left available.
Proof.
  intros. unfold paid_stage in H.
  destruct (C.charge_add maximum flat callbacks) as [charge|] eqn:ADD; [|discriminate].
  apply C.charge_add_success in ADD.
  apply successful_action_constructs_only_the_paid_result in H.
  unfold C.projected_work, C.projected_units in *. intuition lia.
Qed.

End NativeHashBagStageCharge.

Print Assumptions NativeHashBagStageCharge.candidate_total_is_covered.
Print Assumptions NativeHashBagStageCharge.binding_candidate_prefix_is_covered.
Print Assumptions NativeHashBagStageCharge.clone_vacant_is_covered.
Print Assumptions NativeHashBagStageCharge.clone_occupied_is_covered.
Print Assumptions NativeHashBagStageCharge.final_summary_is_two_original_hashes.
Print Assumptions NativeHashBagStageCharge.probe_flat_projection.
Print Assumptions NativeHashBagStageCharge.retained_inspection_projection.
Print Assumptions NativeHashBagStageCharge.clone_zero_flat_projection.
Print Assumptions NativeHashBagStageCharge.stage_overflow_precedes_native_action.
Print Assumptions NativeHashBagStageCharge.stage_cancellation_precedes_native_action.
Print Assumptions NativeHashBagStageCharge.stage_budget_refusal_precedes_native_action.
Print Assumptions NativeHashBagStageCharge.accepted_stage_pays_both_contributions.
