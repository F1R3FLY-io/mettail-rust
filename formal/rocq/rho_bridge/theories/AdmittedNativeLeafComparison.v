(** Native i64/bool/String Eq, Ne and Ord admission.

    Audited source: trusted prebuilt x86_64/64-bit core/alloc at compiler
    2e2b193f8ada105f27608b7be81c293e0d7292cb. core/cmp.rs 2183,2347,2389:
    primitive Eq/Ne overrides, integer intrinsic and bool difference/match.
    alloc/string.rs 350 derives over Vec<u8>, NOT str. Vec equality forwards
    to slices (vec/partial_eq.rs 15); Vec Ord forwards at vec/mod.rs 4391.
    core/slice/cmp.rs 19,151,323 selects byte equality/ordering; the intrinsic
    contract is core/intrinsics/mod.rs 2381-2398.

    NativeWork counts bounded source groups and admitted operand-byte positions.
    compare_bytes requires both WHOLE ranges readable and may read chunks or
    lower to memcmp. The 2*m allowance describes two LOGICAL operand ranges,
    NOT physical loads, processor instructions, libc steps or wall-clock work.
    Metadata inspection reads lengths only, then performs checked arithmetic.

    Primitive Eq/Ne/Cmp each cost 2: dispatch and bounded primitive operation.
    String Eq's six groups: derive entry, field/Vec dispatch, Vec-to-slice
    forwarding, slice length route, BytewiseEq/zero-test wrapper, intrinsic
    dispatch. Unequal lengths skip the byte primitive but keep the safe six.
    String Ne adds default-ne dispatch/negation 1; primitive Ne remains 2.
    String Ord's nine: derive entry/projection 2, Vec forwarding 1, slice
    forwarding 1, metadata/min/diff/pointers 1, intrinsic dispatch 1,
    zero-result fallback 1, scalar sign comparison 2.

    Preserve original ==, != and cmp on unchanged borrowed operands. There is
    no replacement comparator and no global Eq iff cmp==Equal law (especially
    not for later OrdVar/binder leaves). The native operation parameter below
    transports the actual result; it is NOT an arbitrary cost-bound premise.
    Reuse checked_sum and precharged_action: profile refusal precedes work,
    one metadata group precedes inspection/overflow checks, one execution
    reservation precedes the original operation. No operand copies, retained
    bytes or allocated result are modeled. Concrete source/profile and checked
    word-arithmetic correspondence remain Rust obligations. *)
From Stdlib Require Import List Arith Bool Lia ZArith.
From RhoBridge Require Import RholangSourceScope RholangInitialGraphResources
  AdmittedStructuralKeyHash GeneratedDummyCleanupReservation.
Import ListNotations.

Module AdmittedNativeLeafComparison.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module D := GeneratedDummyCleanupReservation.

Inductive Operation := OpEq | OpNe | OpCmp.
Inductive Operands :=
| IntegerOperands (left right : Z)
| BooleanOperands (left right : bool)
| StringOperands (left right : list nat).
Definition ResultType operation : Type :=
  match operation with OpEq | OpNe => bool | OpCmp => comparison end.

Definition equality_extent left right := if left =? right then left else 0.
Definition string_extent operation left right :=
  match operation with OpEq | OpNe => equality_extent left right
                     | OpCmp => Nat.min left right end.
Definition string_fixed_groups operation :=
  match operation with OpEq => 6 | OpNe => 7 | OpCmp => 9 end.
Definition string_work operation left right :=
  string_fixed_groups operation + 2 * string_extent operation left right.
Definition native_work operation operands := match operands with
  | IntegerOperands _ _ | BooleanOperands _ _ => 2
  | StringOperands left_bytes right_bytes =>
      string_work operation (length left_bytes) (length right_bytes)
  end.
Definition equality_source_groups left right :=
  1 + 1 + 1 + 1 + (if left =? right then 1 + 1 + left + right else 0).
Definition ordering_source_groups left right :=
  2 + 1 + 1 + 1 + 1 + 1 + 2 + Nat.min left right + Nat.min left right.

Theorem primitive_operations_use_two_groups : forall operation integer other boolean other_bool,
  native_work operation (IntegerOperands integer other) = 2 /\
  native_work operation (BooleanOperands boolean other_bool) = 2.
Proof. repeat split; reflexivity. Qed.
Theorem equality_native_source_groups_are_covered : forall left right,
  equality_source_groups left right <= string_work OpEq left right.
Proof.
  intros left right. unfold equality_source_groups, string_work,
    string_fixed_groups, string_extent, equality_extent.
  destruct (left =? right) eqn:HE; [apply Nat.eqb_eq in HE|]; lia.
Qed.
Theorem equal_lengths_use_both_full_logical_ranges : forall length,
  string_work OpEq length length = 6 + 2 * length.
Proof.
  intro length. unfold string_work, string_fixed_groups, string_extent, equality_extent.
  now rewrite Nat.eqb_refl.
Qed.
Theorem unequal_lengths_admit_no_byte_comparison : forall left right,
  left <> right -> equality_extent left right = 0 /\ string_work OpEq left right = 6.
Proof.
  intros left right HE. apply Nat.eqb_neq in HE.
  unfold string_work, string_fixed_groups, string_extent, equality_extent.
  rewrite HE. split; reflexivity.
Qed.
Theorem string_inequality_pays_its_extra_default_group : forall left right,
  string_work OpNe left right = string_work OpEq left right + 1 /\
  equality_source_groups left right + 1 <= string_work OpNe left right.
Proof.
  intros left right. pose proof (equality_native_source_groups_are_covered left right) as HE.
  unfold string_work, string_fixed_groups, string_extent in *. split; lia.
Qed.
Theorem ordering_native_source_groups_are_exact : forall left right,
  ordering_source_groups left right = string_work OpCmp left right.
Proof.
  intros. unfold ordering_source_groups, string_work, string_fixed_groups, string_extent. lia.
Qed.
Theorem admitted_operand_positions_fit_both_sources : forall operation left right,
  string_extent operation left right <= left /\ string_extent operation left right <= right.
Proof.
  intros operation left right. destruct operation; cbn [string_extent].
  - unfold equality_extent. destruct (left =? right) eqn:HE;
      [apply Nat.eqb_eq in HE|]; split; lia.
  - unfold equality_extent. destruct (left =? right) eqn:HE;
      [apply Nat.eqb_eq in HE|]; split; lia.
  - split; [apply Nat.le_min_l|apply Nat.le_min_r].
Qed.
Example empty_and_unequal_length_schedules :
  string_work OpEq 0 0 = 6 /\ string_work OpNe 0 0 = 7 /\
  string_work OpCmp 0 1000 = 9 /\ string_work OpEq 2 1 = 6 /\
  string_work OpCmp 2 1 = 11.
Proof. repeat split; reflexivity. Qed.

(** Checked doubling has the same condition as checked_mul(2); reuse the
    existing finite checked_sum laws instead of another integer-cost algebra.
    All nonnegative intermediate values fit whenever the final work fits. *)
Definition checked_string_work maximum operation left right :=
  let extent := string_extent operation left right in
  match checked_sum maximum extent extent with
  | None => None
  | Some positions => checked_sum maximum (string_fixed_groups operation) positions
  end.
Definition checked_native_work maximum operation operands := match operands with
  | IntegerOperands _ _ | BooleanOperands _ _ => checked_sum maximum 0 2
  | StringOperands left_bytes right_bytes =>
      checked_string_work maximum operation (length left_bytes) (length right_bytes)
  end.

Theorem checked_string_work_is_exact : forall maximum operation left right work,
  checked_string_work maximum operation left right = Some work <->
  work = string_work operation left right /\ work <= maximum.
Proof.
  intros maximum operation left right work. unfold checked_string_work.
  destruct (checked_sum maximum (string_extent operation left right)
    (string_extent operation left right)) as [positions|] eqn:HP.
  - apply checked_sum_success_is_exact_and_bounded in HP.
    rewrite checked_sum_success_is_exact_and_bounded.
    unfold string_work. lia.
  - split; [discriminate|]. intros [HW HM].
    assert (HF : checked_sum maximum (string_extent operation left right)
      (string_extent operation left right) = Some (2 * string_extent operation left right)).
    { apply checked_sum_success_is_exact_and_bounded.
      unfold string_work in HW. split; lia. }
    rewrite HF in HP. discriminate.
Qed.
Theorem checked_native_work_is_exact : forall maximum operation operands work,
  checked_native_work maximum operation operands = Some work <->
  work = native_work operation operands /\ work <= maximum.
Proof.
  intros maximum operation operands work. destruct operands; cbn [checked_native_work native_work].
  - apply checked_sum_success_is_exact_and_bounded.
  - apply checked_sum_success_is_exact_and_bounded.
  - apply checked_string_work_is_exact.
Qed.
Theorem native_work_overflow_cannot_wrap : forall maximum operation operands,
  maximum < native_work operation operands ->
  checked_native_work maximum operation operands = None.
Proof.
  intros maximum operation operands HO.
  destruct (checked_native_work maximum operation operands) as [work|] eqn:HW; [|reflexivity].
  apply checked_native_work_is_exact in HW. lia.
Qed.
Theorem comparison_execution_retains_no_owned_payload : forall operation operands,
  D.weighted D.base_work_weight (S.work_counts (native_work operation operands)) =
    native_work operation operands /\
  D.weighted D.record_weight (S.work_counts (native_work operation operands)) = 0 /\
  D.weighted D.byte_weight (S.work_counts (native_work operation operands)) = 0.
Proof. intros. apply S.work_counts_projection. Qed.

Section NativeExecution.
(** The same original method is used with immutable source operands; its type
    has no source-state output. No Eq/Ne/Ord relationship is imposed. *)
Variable execute_native : forall operation, Operands -> ResultType operation.
Definition inspect maximum operation operands available :=
  precharged_action false available 1 0
    (fun _ => checked_native_work maximum operation operands).
Definition admitted_comparison (supported : bool) maximum operation operands available :=
  if supported then
    match inspect maximum operation operands available with
    | Refused remaining => Refused remaining
    | Accepted remaining work => precharged_action false remaining work 0
        (fun _ => Some (execute_native operation operands))
    end
  else Refused available.

Theorem successful_comparison_is_original_result_and_exact_charge :
  forall supported maximum operation operands available paid result,
  admitted_comparison supported maximum operation operands available = Accepted paid result ->
  supported = true /\ result = execute_native operation operands /\
  native_work operation operands <= maximum /\
  work_left paid + 1 + native_work operation operands = work_left available /\
  units_left paid = units_left available.
Proof.
  intros supported maximum operation operands available paid result HC.
  destruct supported; [|discriminate]. unfold admitted_comparison in HC.
  destruct (inspect maximum operation operands available) as [remaining|remaining work]
    eqn:HI; [discriminate|].
  unfold inspect in HI. apply successful_action_constructs_only_the_paid_result in HI, HC.
  destruct HI as [_ [HW [HWI HUI]]], HC as [_ [HR [HWE HUE]]].
  apply checked_native_work_is_exact in HW. inversion HR; subst.
  repeat split; try reflexivity; lia.
Qed.
Theorem unsupported_profile_precedes_inspection : forall maximum operation operands available,
  admitted_comparison false maximum operation operands available = Refused available.
Proof. reflexivity. Qed.
Theorem inspection_refusal_precedes_native_comparison : forall maximum operation operands available,
  reserve available 1 0 = None ->
  admitted_comparison true maximum operation operands available = Refused available.
Proof.
  intros maximum operation operands available HR. unfold admitted_comparison, inspect.
  rewrite (failed_precharge_is_independent_of_constructor _ _ _ _ _ HR). reflexivity.
Qed.
Theorem arithmetic_refusal_keeps_metadata_charge : forall maximum operation operands available paid,
  reserve available 1 0 = Some paid -> maximum < native_work operation operands ->
  admitted_comparison true maximum operation operands available = Refused paid.
Proof.
  intros maximum operation operands available paid HR HO.
  unfold admitted_comparison, inspect.
  pose proof (native_work_overflow_cannot_wrap _ _ _ HO) as HC.
  rewrite (callback_failure_does_not_refund _ _ _ _ _ _ HR HC). reflexivity.
Qed.
Theorem execution_refusal_keeps_metadata_charge :
  forall maximum operation operands available paid work,
  inspect maximum operation operands available = Accepted paid work ->
  reserve paid work 0 = None ->
  admitted_comparison true maximum operation operands available = Refused paid.
Proof.
  intros maximum operation operands available paid work HI HR.
  unfold admitted_comparison. rewrite HI.
  now apply failed_precharge_is_independent_of_constructor.
Qed.
(** Cancellation snapshots at the two admission boundaries. These stage laws
    use the existing cancellation constructor; the noncancelled composition
    above does not model an arbitrary callback or asynchronous polling. *)
Theorem cancelled_metadata_stage_precedes_inspection :
  forall maximum operation operands available,
  precharged_action true available 1 0
    (fun _ => checked_native_work maximum operation operands) = Refused available.
Proof. intros. reflexivity. Qed.
Theorem cancelled_execution_stage_keeps_metadata_charge :
  forall maximum operation operands available paid work,
  inspect maximum operation operands available = Accepted paid work ->
  precharged_action true paid work 0
    (fun _ => Some (execute_native operation operands)) = Refused paid.
Proof. intros. reflexivity. Qed.
End NativeExecution.

Print Assumptions primitive_operations_use_two_groups.
Print Assumptions equality_native_source_groups_are_covered.
Print Assumptions equal_lengths_use_both_full_logical_ranges.
Print Assumptions unequal_lengths_admit_no_byte_comparison.
Print Assumptions string_inequality_pays_its_extra_default_group.
Print Assumptions ordering_native_source_groups_are_exact.
Print Assumptions admitted_operand_positions_fit_both_sources.
Print Assumptions empty_and_unequal_length_schedules.
Print Assumptions checked_string_work_is_exact.
Print Assumptions checked_native_work_is_exact.
Print Assumptions native_work_overflow_cannot_wrap.
Print Assumptions comparison_execution_retains_no_owned_payload.
Print Assumptions successful_comparison_is_original_result_and_exact_charge.
Print Assumptions unsupported_profile_precedes_inspection.
Print Assumptions inspection_refusal_precedes_native_comparison.
Print Assumptions arithmetic_refusal_keeps_metadata_charge.
Print Assumptions execution_refusal_keeps_metadata_charge.
Print Assumptions cancelled_metadata_stage_precedes_inspection.
Print Assumptions cancelled_execution_stage_keeps_metadata_charge.
End AdmittedNativeLeafComparison.
