(** Composable, partial native append-operation bounds.

    The source inspected is node commit 9eeaa94d3041e95cc2e0268aa333a3aca75e3d2c:
    models/src/rust/utils.rs, Par::append and union;
    models/src/rust/rholang/par_children.rs, dismantle_in_place;
    models/codegen/schema.rs, the generated Clone family. The inspected
    rhoapi_term_ops.rs has SHA-256
    a833a8632ee86448b81b6a257bcac9d2140ca79c09a1933795815be6c5f47ece.
    Standard-library sort bounds retain their dependency's pinned compiler
    2e2b193f8ada105f27608b7be81c293e0d7292cb and normal-completion scope.

    Append clones left heads once, then concat clones left and right heads.
    Its owned-copy receipt is therefore twice left plus right. This file does
    not change that native implementation. It proves the following reusable
    subprofiles, not an all-inclusive native-operation tariff:

    - annotation erasure preserves the child-forest measure used by cleanup;
    - the clone's bounded native prefixes partition that same forest;
    - push, rebuild, and three debug arity recounts make at most five prefix
      visits per Par occurrence (not five CPU instructions per occurrence);
    - injection-map sort derivations compose into receipt-bounded callback
      and core-work allowances, including adjacent-key dedup comparisons;
    - byte passes and checked, atomic two-dimensional reservations compose.

    In the generated clone, Par is the cut set and CLONE_DESCEND_BUDGET is 3.
    Each driven region visits its root and up to three child levels before
    suspending the frontier. drive_with's debug Ledger asks for arity when
    adding a Combine and when popping it; combine has one further recount.
    A wholly native region omits all three. Fixed prefix count five is this
    explicit source inventory, not a multiplier for arbitrary native work.

    Nested clone_rebuild_new collects its BTreeMap keys or entries. In the
    pinned alloc/src/collections/btree/map.rs, FromIterator collects a Vec,
    invokes stable sort, then bulk_build_from_sorted_iter; its DedupSortedIter
    compares adjacent keys. Direct New::clone instead uses BTreeMap::clone.
    The sort derivations below apply only to the former path. A byte-prefix
    callback annotation counts one setup group plus examined key bytes; it is
    not an instruction-level proof of the platform's string comparison.

    Explicitly NOT covered by these subprofiles: constructor-field dispatch
    and record-loop constants, clone pool/driver storage, BTreeMap clone or
    bulk-build control, Vec/sort outer scratch, allocator internals, panic
    unwinding, or eventual returned-output ownership. Those must not be
    silently charged by interpreting the partial total below as a full debit.
    No Rust receipt plumbing or public preparation coverage is asserted. *)
From Stdlib Require Import List Arith Lia Bool.
From RhoBridge Require Import RholangTargetConstruction RholangDeepConstructionSize
  RholangConstructionCleanup RholangBoundMetadata RholangInitialGraphResources
  NativeStableSortRequestBound NativeStableSortWorkBound.
Import ListNotations.

Module NativeAppendOperationBound.
Module Requests := NativeStableSortRequestBound.NativeStableSortRequestBound.
Module SortWork := NativeStableSortWorkBound.NativeStableSortWorkBound.

(** Over-include direct New clones and empty injection maps. This bounds every
    nested collection without needing another receipt axis or a runtime scan. *)
Fixpoint native_injection_widths (value : NativeValueImage) : list nat :=
  match value with NativeValue heads _ => flat_map head_injection_widths heads end
with head_injection_widths (head : NativeHeadImage) : list nat :=
  match head with NativeHead fields children =>
    (match native_kind fields with NewHead _ _ keys => [List.length keys] | _ => [] end) ++
    flat_map native_injection_widths children
  end.

Theorem injection_widths_fit_existing_receipt_axes : forall value,
  Requests.total (native_injection_widths value) <= native_value_count NativeNameEntries value /\
  List.length (native_injection_widths value) <= native_value_count NativeHeads value.
Proof.
  fix IH 1. intros [heads summary].
  cbn [native_injection_widths native_value_count].
  induction heads as [|[fields children] rest REST]; [split; reflexivity|].
  assert (CHILDREN : Requests.total (flat_map native_injection_widths children) <=
      sum_sizes (fun child => native_value_count NativeNameEntries child) children /\
    List.length (flat_map native_injection_widths children) <=
      sum_sizes (fun child => native_value_count NativeHeads child) children).
  { induction children as [|child tail TAIL]; [split; reflexivity|].
    pose proof (IH child) as [NAMES HEADS]. cbn [flat_map].
    rewrite Requests.total_app, length_app.
    destruct TAIL. unfold sum_sizes in *. cbn [fold_right]. split; lia. }
  cbn [flat_map sum_sizes fold_right native_head_count native_local_count native_embed_count].
  rewrite Requests.total_app, length_app. destruct REST, CHILDREN.
  cbn [head_injection_widths]. rewrite Requests.total_app, length_app.
  destruct (native_kind fields); cbn [native_local_count Requests.total List.length];
    unfold sum_sizes in *; split; lia.
Qed.

(** The mixed annotation adds local byte fields but never changes children. *)
Theorem native_descendants_survive_erasure : forall value,
  native_value_count NativeDescendantPars value =
  value_owned_count DescendantPars (erase_native_value value).
Proof.
  fix IH 1. intros [heads summary].
  cbn [native_value_count erase_native_value value_owned_count].
  rewrite sum_sizes_map.
  induction heads as [|[fields children] rest REST]; [reflexivity|].
  cbn [sum_sizes fold_right native_head_count native_local_count native_embed_count
    erase_native_head head_deep_count].
  assert (LOCAL : head_owned_count DescendantPars (native_kind fields)
    (map erase_native_value children) = 0).
  { destruct (native_kind fields); reflexivity. }
  rewrite LOCAL. cbn [Nat.add]. rewrite sum_sizes_map.
  unfold sum_sizes in REST. rewrite REST. f_equal.
  clear LOCAL.
  induction children as [|child tail TAIL]; [reflexivity|].
  cbn [sum_sizes fold_right embed_count].
  unfold sum_sizes in TAIL. rewrite (IH child), TAIL. reflexivity.
Qed.

Corollary mixed_normal_cleanup_reuses_existing_machine : forall value,
  let d := native_value_count NativeDescendantPars value in
  CleanupSteps d d (rev (direct_children (erase_native_value value))).
Proof. intro value. rewrite native_descendants_survive_erasure.
  apply normal_par_drop_has_exact_descendant_worklist. Qed.

(** A depth-zero prefix visits its root and suspends its immediate children.
    Positive depth enters each child natively. These are proof measurements;
    they do not prescribe a second runtime traversal. *)
Fixpoint prefix_width (depth : nat) (value : Value) : nat :=
  match depth with
  | 0 => 1
  | S previous => 1 + sum_sizes (prefix_width previous) (direct_children value)
  end.
Fixpoint prefix_frontier (depth : nat) (value : Value) : list Value :=
  match depth with
  | 0 => direct_children value
  | S previous => flat_map (prefix_frontier previous) (direct_children value)
  end.

Lemma prefix_width_positive : forall depth value, 1 <= prefix_width depth value.
Proof. intros [|depth] value; cbn [prefix_width]; lia. Qed.

Lemma sum_sizes_additive : forall A (f g : A -> nat) items,
  sum_sizes (fun x => f x + g x) items = sum_sizes f items + sum_sizes g items.
Proof. intros A f g items. induction items; unfold sum_sizes in *;
  cbn [fold_right] in *; lia. Qed.

Theorem native_prefix_and_frontier_partition_occurrences : forall depth value,
  prefix_width depth value + forest_mass (prefix_frontier depth value) =
  S (value_owned_count DescendantPars value).
Proof.
  induction depth as [|depth IH]; intro value.
  - cbn [prefix_width prefix_frontier].
    rewrite <- value_descendants_are_the_direct_child_forest. lia.
  - cbn [prefix_width prefix_frontier]. unfold forest_mass at 1.
    rewrite sum_sizes_flat_map.
    change (1 + sum_sizes (prefix_width depth) (direct_children value) +
      sum_sizes (fun child => forest_mass (prefix_frontier depth child))
        (direct_children value) = S (value_owned_count DescendantPars value)).
    replace (1 + sum_sizes (prefix_width depth) (direct_children value) +
      sum_sizes (fun child => forest_mass (prefix_frontier depth child)) (direct_children value))
      with (1 + (sum_sizes (prefix_width depth) (direct_children value) +
        sum_sizes (fun child => forest_mass (prefix_frontier depth child)) (direct_children value))) by lia.
    rewrite <- sum_sizes_additive.
    rewrite (sum_sizes_extensional _ _
      (fun child => S (value_owned_count DescendantPars child))
      (direct_children value)) by (intros; apply IH).
    change (1 + forest_mass (direct_children value) =
      S (value_owned_count DescendantPars value)).
    rewrite <- value_descendants_are_the_direct_child_forest. lia.
Qed.

(** A completed normal clone schedule replaces a driven root by its frontier.
    Prefix visits overpay fast-path regions by retaining all three recounts.
    The driver has at most one Descend and one Combine per driven region. *)
Inductive CloneRegions (depth : nat) : nat -> nat -> list Value -> Prop :=
| CloneRegionsDone : CloneRegions depth 0 0 []
| CloneRegionsNext : forall value rest regions visits,
    CloneRegions depth regions visits (prefix_frontier depth value ++ rest) ->
    CloneRegions depth (S regions) (5 * prefix_width depth value + visits) (value :: rest).

Theorem clone_regions_cover_each_owned_occurrence : forall depth regions visits pending,
  CloneRegions depth regions visits pending ->
  regions <= forest_mass pending /\ visits = 5 * forest_mass pending.
Proof.
  intros depth regions visits pending TRACE. induction TRACE.
  - cbn [forest_mass sum_sizes fold_right]. lia.
  - destruct IHTRACE as [REGIONS VISITS].
    unfold forest_mass in REGIONS, VISITS. rewrite sum_sizes_app in REGIONS, VISITS.
    change (regions <= forest_mass (prefix_frontier depth value) + forest_mass rest) in REGIONS.
    change (visits = 5 * (forest_mass (prefix_frontier depth value) + forest_mass rest)) in VISITS.
    pose proof (native_prefix_and_frontier_partition_occurrences depth value).
    pose proof (prefix_width_positive depth value).
    change (S regions <= S (value_owned_count DescendantPars value) + forest_mass rest /\
      5 * prefix_width depth value + visits =
        5 * (S (value_owned_count DescendantPars value) + forest_mass rest)). nia.
Qed.

Corollary clone_driver_transition_count_is_bounded : forall regions visits pending,
  CloneRegions 3 regions visits pending -> 2 * regions <= 2 * forest_mass pending.
Proof. intros. apply clone_regions_cover_each_owned_occurrence in H. lia. Qed.

(** Sort runs retain the existing finite native derivation, rather than
    assuming a desired per-sort cost bound. Only injection-map widths enter
    this list; a retained name-entry receipt may conservatively include URIs. *)
Record MapSortRun := {
  map_width : nat;
  map_requests : nat;
  map_source : Requests.StableRequests map_width map_requests;
  map_fee : SortWork.Charge;
  map_work_source : SortWork.StableWork map_width map_requests map_source map_fee
}.
Definition map_widths runs := map map_width runs.
Definition map_request_bound names := 10 * names * names + 32 * names.
Definition map_core_bound names heads := 320 * names * names + 1024 * names + 1133 * heads.
Definition map_key_bound names payload := (10 * names * names + 33 * names) * (1 + payload).

Lemma map_run_request_sum : forall runs,
  sum_sizes map_requests runs <=
    10 * Requests.squares (map_widths runs) + 32 * Requests.total (map_widths runs).
Proof.
  induction runs as [|run rest IH]; [reflexivity|].
  pose proof (Requests.all_widths_request_envelope _ _ (map_source run)).
  unfold sum_sizes, map_widths in *.
  cbn [fold_right map Requests.squares Requests.total] in *. nia.
Qed.

Lemma map_run_core_sum : forall runs,
  sum_sizes (fun run => SortWork.work (map_fee run)) runs <=
    320 * Requests.squares (map_widths runs) +
    1024 * Requests.total (map_widths runs) + 1133 * List.length runs.
Proof.
  induction runs as [|run rest IH]; [reflexivity|].
  pose proof (SortWork.all_widths_have_cumulative_native_core_allowances _ _
    (map_source run) _ (map_work_source run)) as [_ [WORK _]].
  unfold SortWork.core_bound in WORK.
  unfold sum_sizes, map_widths in *.
  cbn [fold_right map Requests.squares Requests.total List.length] in *. nia.
Qed.

Theorem receipt_bounds_all_map_sort_subprofiles : forall runs names heads,
  Requests.total (map_widths runs) <= names -> List.length runs <= heads ->
  sum_sizes map_requests runs <= map_request_bound names /\
  sum_sizes (fun run => SortWork.work (map_fee run)) runs <= map_core_bound names heads /\
  sum_sizes (fun run => SortWork.records (map_fee run)) runs <= map_core_bound names heads.
Proof.
  intros runs names heads WIDTH CALLS.
  pose proof (Requests.squares_total (map_widths runs)).
  pose proof (map_run_request_sum runs). pose proof (map_run_core_sum runs).
  assert (RECORDS : sum_sizes (fun run => SortWork.records (map_fee run)) runs <=
    sum_sizes (fun run => SortWork.work (map_fee run)) runs).
  { clear -runs. induction runs as [|run rest IH]; [reflexivity|].
    pose proof (SortWork.all_widths_have_cumulative_native_core_allowances _ _
      (map_source run) _ (map_work_source run)) as [LOCAL _].
    unfold sum_sizes in *. cbn [fold_right] in *. lia. }
  unfold map_request_bound, map_core_bound. repeat split; nia.
Qed.

(** Adjacent-key dedup invokes at most one equality comparison per consumed
    pair. A callback byte-prefix annotation never examines more bytes than
    the complete retained payload receipt; repeated comparisons remain paid. *)
Theorem sort_and_dedup_key_prefix_envelope : forall names payload sort_calls dedup_calls examined,
  sort_calls <= map_request_bound names -> dedup_calls <= names ->
  examined <= (sort_calls + dedup_calls) * payload ->
  sort_calls + dedup_calls + examined <= map_key_bound names payload.
Proof. unfold map_request_bound, map_key_bound. intros. nia. Qed.

Corollary individually_bounded_key_prefixes_compose :
  forall names payload sort_calls dedup_calls prefixes,
  sort_calls <= map_request_bound names -> dedup_calls <= names ->
  List.length prefixes <= sort_calls + dedup_calls ->
  Forall (fun bytes => bytes <= payload) prefixes ->
  sort_calls + dedup_calls + Requests.total prefixes <= map_key_bound names payload.
Proof.
  intros names payload sort_calls dedup_calls prefixes SORT DEDUP COUNT LOCAL.
  pose proof (Requests.bounded_widths prefixes payload LOCAL).
  apply sort_and_dedup_key_prefix_envelope; nia.
Qed.

(** Discarded child forests have roots already included in their descendant
    receipt. Root destructors replace the corresponding loop pop. The two
    extra wrappers are the consumed left Par and the emptied right Par.
    This is the normal cleanup-control projection, not map/buffer destruction. *)
Theorem append_cleanup_forest_control : forall child_roots nested left_nested d,
  child_roots + nested + left_nested <= d ->
  nested + left_nested <= d /\
  child_roots + nested + left_nested + 2 <= d + 2 /\
  child_roots + 2 * nested + 2 * left_nested + 2 <= 2 * d + 2.
Proof. intros. lia. Qed.

Definition partial_work heads names payload inner_bytes outer_left outer_right :=
  payload + inner_bytes + outer_left + 3 * Nat.max outer_left outer_right +
  map_core_bound names heads + map_key_bound names payload.
Definition partial_units heads names payload inner_bytes outer_left outer_right :=
  payload + inner_bytes + outer_left + Nat.max outer_left outer_right + map_core_bound names heads.

Theorem partial_byte_passes_reuse_metadata_profile :
  forall heads names payload inner_bytes lhs rhs,
  partial_work heads names payload inner_bytes lhs rhs =
    payload + inner_bytes + passes_work (append_passes lhs rhs) +
    map_core_bound names heads + map_key_bound names payload /\
  partial_units heads names payload inner_bytes lhs rhs =
    payload + inner_bytes + passes_units (append_passes lhs rhs) + map_core_bound names heads.
Proof.
  intros. pose proof (append_pass_debits_cover_copy_initialization_fill_and_comparison lhs rhs).
  unfold partial_work, partial_units. lia.
Qed.

Theorem copied_owned_bytes_keep_both_append_clone_passes : forall lhs rhs,
  native_append_copy_count NativePayloadBytes lhs rhs +
  native_append_copy_count NativeMetadataBytes lhs rhs =
  2 * (native_value_count NativePayloadBytes lhs + native_value_count NativeMetadataBytes lhs) +
    native_value_count NativePayloadBytes rhs + native_value_count NativeMetadataBytes rhs.
Proof. intros. repeat rewrite native_append_copies_twice_left_once_right. lia. Qed.

(** Checked arithmetic returns no value on overflow. This natural-number
    specification concerns accepted projections, not modular arithmetic.
    Checking both complete dimensions precedes any native operation. *)
Definition checked (maximum value : nat) : option nat :=
  if value <=? maximum then Some value else None.

Theorem checked_is_exact : forall maximum value result,
  checked maximum value = Some result -> result = value /\ value <= maximum.
Proof.
  intros maximum value result. unfold checked.
  destruct (value <=? maximum) eqn:FIT.
  - intro EQ. injection EQ as EQ. subst result.
    split; [reflexivity|]. now apply Nat.leb_le.
  - discriminate.
Qed.

Theorem checked_add_requires_no_wrap : forall maximum left right result,
  checked maximum (left + right) = Some result ->
  result = left + right /\ left <= maximum /\ right <= maximum.
Proof. intros. apply checked_is_exact in H. lia. Qed.

Theorem checked_multiply_requires_no_wrap : forall maximum left right result,
  checked maximum (left * right) = Some result ->
  result = left * right /\ left * right <= maximum.
Proof. intros. now apply checked_is_exact in H. Qed.

Theorem complete_partial_reservation_is_atomic : forall available heads names payload inner_bytes lhs rhs,
  (exists next, reserve available
    (partial_work heads names payload inner_bytes lhs rhs)
    (partial_units heads names payload inner_bytes lhs rhs) = Some next) <->
  partial_work heads names payload inner_bytes lhs rhs <= work_left available /\
  partial_units heads names payload inner_bytes lhs rhs <= units_left available.
Proof. intros. apply reservation_succeeds_exactly_when_both_dimensions_fit. Qed.

Print Assumptions native_descendants_survive_erasure.
Print Assumptions injection_widths_fit_existing_receipt_axes.
Print Assumptions mixed_normal_cleanup_reuses_existing_machine.
Print Assumptions native_prefix_and_frontier_partition_occurrences.
Print Assumptions clone_regions_cover_each_owned_occurrence.
Print Assumptions clone_driver_transition_count_is_bounded.
Print Assumptions receipt_bounds_all_map_sort_subprofiles.
Print Assumptions sort_and_dedup_key_prefix_envelope.
Print Assumptions individually_bounded_key_prefixes_compose.
Print Assumptions append_cleanup_forest_control.
Print Assumptions partial_byte_passes_reuse_metadata_profile.
Print Assumptions copied_owned_bytes_keep_both_append_clone_passes.
Print Assumptions checked_is_exact.
Print Assumptions checked_add_requires_no_wrap.
Print Assumptions checked_multiply_requires_no_wrap.
Print Assumptions complete_partial_reservation_is_atomic.
End NativeAppendOperationBound.
