(** Identity comparisons and the existing generated binder-pattern judgement.

    Source: runtime/src/binding.rs 465-498; moniker 0.5.0 unique_id.rs,
    free_var.rs 35-51, bound_var.rs 14-75, binder.rs 5, var.rs 8;
    macros/src/gen/term_ops/iterative_cmp.rs 1617-1623,1668-1682.
    Equality ignores pretty names. Bound OrdVar ordering evaluates BOTH
    field comparisons before Ordering::then. Free ordering hashes each UID
    using its own fresh DefaultHasher; this is NOT the Fx leaf schedule.

    NativeWork uses bounded source groups, not processor instructions or
    arbitrary Hasher bounds. The trusted prebuilt compiler/core profile is
    2e2b193f8ada105f27608b7be81c293e0d7292cb, x86_64/64-bit. Its fresh
    DefaultHasher/SipHasher13 path for one u32 has four input bytes, no bulk
    compression, one finish compression and three finalization rounds.
    Fresh hash groups: constructor4 + wrapper2(UID)/6(Binder) + forwarding4
    + write control4 + input bytes4 + finish11 = 29/33. The finish group
    includes the fixed native dispatch/state/round/final-XOR work. These
    are source-profile facts to match in Rust, not a compiler correctness
    theorem, hash injectivity assumption, or reusable admission receipt.

    Reuse canonical struct/enum groups D/E from the structural Hash model
    ONLY as the same arithmetic of entry/field handoff groups. Native Eq,
    Ne and Cmp remain separate original operations. No Binder Ord instance
    or Eq iff cmp==Equal law is introduced. Pattern requests refer ONLY to
    the unchanged generated single/multi binder expressions, not an exposed
    arbitrary comparator and not the scope body or task scheduler.

    Metadata is one paid constant-size group: inspect variants or lengths,
    then checked multiplication/addition. It does not inspect vector items
    or pretty strings. The execution allowance covers the native visited
    prefix; full width is reserved before the original expression. Source
    lists below are mathematical projections, never runtime allocations.
    Profile refusal, arithmetic overflow, and either failed reservation
    precede the native action. No owned payload is retained or allocated.
    Cancellation laws describe the two stage snapshots, not arbitrary
    callback behavior or asynchronous polling. FLT and generated comparison
    scheduling remain separate obligations. *)
From Stdlib Require Import List Arith Bool Lia.
From RhoBridge Require Import AdmittedNativeLeafComparison
  AdmittedStructuralKeyHash RholangSourceScope RholangInitialGraphResources
  GeneratedDummyCleanupReservation.
Import ListNotations.

Module AdmittedIdentityComparison.
Module L := AdmittedNativeLeafComparison.AdmittedNativeLeafComparison.
Module S := AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.
Module D := GeneratedDummyCleanupReservation.

Definition ne_extra (negated : bool) := if negated then 1 else 0.
Definition ordvar_eq_work (lhs rhs : S.MonikerVar) := S.struct_work
  [match lhs, rhs with
   | S.Free _ _, S.Free _ _ => S.enum_work [S.free_work]
   | S.Bound _ _ _, S.Bound _ _ _ => S.enum_work [S.bound_work]
   | _, _ => S.enum_work []
   end].
Definition fresh_sip_work wrapper := 4 + wrapper + 4 + 4 + 4 + 11.
Definition fresh_uid_work := fresh_sip_work 2.
Definition fresh_binder_work := fresh_sip_work 6.
Definition ordvar_cmp_work (lhs rhs : S.MonikerVar) :=
  match lhs, rhs with
  | S.Free _ _, S.Free _ _ => 5 + 1 + 2 * (fresh_uid_work + 1) + 2
  | S.Bound _ _ _, S.Bound _ _ _ => 5 + 4 + 4 + 1
  | _, _ => 5
  end.
Definition ordvar_work operation lhs rhs := match operation with
  | L.OpEq => ordvar_eq_work lhs rhs
  | L.OpNe => ordvar_eq_work lhs rhs + 1
  | L.OpCmp => ordvar_cmp_work lhs rhs
  end.
Definition single_pattern_work := 1 + 2 * (fresh_binder_work + 1) + 2.
(** Length route5 = hash-closure setup1 + length projection1 + usize
    comparison2 + then_with route1. Equal-arm overhead22 = continuation1
    + two Vec/slice/Iter constructions6 + zip construction/specialization4
    + map construction2 + find/check/Map::try_fold initialization3
    + terminal/completion/extraction6. Each visited pair80 = Zip::next
    routing/projections4 + map-fold/closure forwarding2 + two binder hash
    closure calls68 + u64 comparison2 + find predicate comparison2
    + check/try_fold routing2. No unvisited pair is executed. *)
Definition multi_pattern_setup := 5 + 22.
Definition multi_pattern_pair := 10 + 2 * (fresh_binder_work + 1) + 2.
Definition vector_eq_work lhs rhs :=
  7 + 11 * L.equality_extent lhs rhs.
Definition multi_pattern_work lhs rhs :=
  if lhs =? rhs then multi_pattern_setup + multi_pattern_pair * lhs else 5.

Theorem identity_branch_groups : forall identity scope index pretty,
  ordvar_eq_work (S.Free identity pretty) (S.Free identity pretty) = 14 /\
  ordvar_eq_work (S.Bound scope index pretty) (S.Bound scope index pretty) = 19 /\
  ordvar_eq_work (S.Free identity pretty) (S.Bound scope index pretty) = 7 /\
  S.binder_work = 8 /\ S.binder_work + 1 = 9.
Proof. repeat split; reflexivity. Qed.
Theorem original_ordering_branch_groups : forall identity scope index pretty,
  fresh_uid_work = 29 /\ fresh_binder_work = 33 /\
  ordvar_cmp_work (S.Free identity pretty) (S.Free identity pretty) = 68 /\
  ordvar_cmp_work (S.Bound scope index pretty) (S.Bound scope index pretty) = 14 /\
  ordvar_cmp_work (S.Free identity pretty) (S.Bound scope index pretty) = 5 /\
  single_pattern_work = 71 /\ multi_pattern_setup = 27 /\ multi_pattern_pair = 80.
Proof. repeat split; reflexivity. Qed.
Theorem default_ne_adds_one_group : forall lhs rhs,
  ordvar_work L.OpNe lhs rhs = ordvar_work L.OpEq lhs rhs + 1.
Proof. reflexivity. Qed.
Theorem equal_vector_schedules : forall width,
  vector_eq_work width width = 7 + 11 * width /\
  multi_pattern_work width width = 27 + 80 * width.
Proof.
  intro width. unfold vector_eq_work, L.equality_extent, multi_pattern_work.
  rewrite Nat.eqb_refl. split; reflexivity.
Qed.
Theorem unequal_vector_schedules : forall lhs rhs,
  lhs <> rhs -> vector_eq_work lhs rhs = 7 /\ multi_pattern_work lhs rhs = 5.
Proof.
  intros lhs rhs HE. apply Nat.eqb_neq in HE.
  unfold vector_eq_work, L.equality_extent, multi_pattern_work.
  rewrite HE. split; reflexivity.
Qed.

(** Each boolean is the original predicate's stop decision for one pair:
    failed equality or non-Equal pattern ordering. This only counts the
    visited prefix; it neither computes nor substitutes that predicate. *)
Fixpoint visited_pairs (stops : list bool) : nat := match stops with
  | [] => 0
  | stop :: rest => if stop then 1 else 1 + visited_pairs rest
  end.
Theorem visited_prefix_fits_width : forall stops,
  visited_pairs stops <= length stops.
Proof.
  intro stops. induction stops as [|stop rest IH]; cbn [visited_pairs length].
  - lia.
  - destruct stop; lia.
Qed.
Theorem native_prefix_groups_are_covered : forall stops width,
  length stops = width ->
  7 + 11 * visited_pairs stops <= vector_eq_work width width /\
  multi_pattern_setup + multi_pattern_pair * visited_pairs stops <=
    multi_pattern_work width width.
Proof.
  intros stops width HW. pose proof (visited_prefix_fits_width stops) as HP.
  destruct (equal_vector_schedules width) as [HE HC]. rewrite HE, HC.
  change (7 + 11 * visited_pairs stops <= 7 + 11 * width /\
    27 + 80 * visited_pairs stops <= 27 + 80 * width). split; lia.
Qed.

(** A closed request prevents a generic Binder ordering claim. The same
    request is passed to the actual native action after admission. *)
Inductive Request :=
| VariableRequest (operation : L.Operation) (lhs rhs : S.MonikerVar)
| BinderEquality (negated : bool) (lhs rhs : S.Binder)
| VectorEquality (negated : bool) (lhs rhs : list S.Binder)
| SinglePattern (lhs rhs : S.Binder)
| MultiPattern (lhs rhs : list S.Binder).
Definition ResultType request : Type := match request with
  | VariableRequest operation _ _ => L.ResultType operation
  | BinderEquality _ _ _ | VectorEquality _ _ _ => bool
  | SinglePattern _ _ | MultiPattern _ _ => comparison
  end.
Record Schedule := { fixed_groups : nat; pair_groups : nat; pair_width : nat }.
Definition fixed_schedule work :=
  {| fixed_groups := work; pair_groups := 0; pair_width := 0 |}.
Definition request_schedule request := match request with
  | VariableRequest operation lhs rhs => fixed_schedule (ordvar_work operation lhs rhs)
  | BinderEquality negated _ _ => fixed_schedule (8 + ne_extra negated)
  | VectorEquality negated lhs rhs =>
      {| fixed_groups := 7 + ne_extra negated; pair_groups := 11;
         pair_width := L.equality_extent (length lhs) (length rhs) |}
  | SinglePattern _ _ => fixed_schedule single_pattern_work
  | MultiPattern lhs rhs =>
      if length lhs =? length rhs then
        {| fixed_groups := multi_pattern_setup; pair_groups := multi_pattern_pair;
           pair_width := length lhs |}
      else fixed_schedule 5
  end.
Definition schedule_work schedule :=
  fixed_groups schedule + pair_groups schedule * pair_width schedule.
Definition native_work request := schedule_work (request_schedule request).

(** Nat multiplication is the mathematical product, not machine arithmetic.
    checked_sum maximum 0 product is precisely its representability test;
    Rust must use checked_mul BEFORE checked_add and the execution callback. *)
Definition checked_schedule maximum schedule :=
  match checked_sum maximum 0 (pair_groups schedule * pair_width schedule) with
  | None => None
  | Some pairs => checked_sum maximum (fixed_groups schedule) pairs
  end.
Definition checked_work maximum request :=
  checked_schedule maximum (request_schedule request).
Theorem checked_schedule_is_exact : forall maximum schedule work,
  checked_schedule maximum schedule = Some work <->
  work = schedule_work schedule /\ work <= maximum.
Proof.
  intros maximum schedule work. unfold checked_schedule.
  destruct (checked_sum maximum 0 (pair_groups schedule * pair_width schedule))
    as [pairs|] eqn:HP.
  - apply checked_sum_success_is_exact_and_bounded in HP.
    rewrite checked_sum_success_is_exact_and_bounded. unfold schedule_work. lia.
  - split; [discriminate|]. intros [HW HM].
    assert (HF : checked_sum maximum 0 (pair_groups schedule * pair_width schedule) =
      Some (pair_groups schedule * pair_width schedule)).
    { apply checked_sum_success_is_exact_and_bounded.
      unfold schedule_work in HW. split; lia. }
    rewrite HF in HP. discriminate.
Qed.
Theorem checked_work_is_exact : forall maximum request work,
  checked_work maximum request = Some work <->
  work = native_work request /\ work <= maximum.
Proof. intros. apply checked_schedule_is_exact. Qed.
Theorem overflow_cannot_wrap : forall maximum request,
  maximum < native_work request -> checked_work maximum request = None.
Proof.
  intros maximum request HO. destruct (checked_work maximum request) as [work|] eqn:HW;
    [|reflexivity]. apply checked_work_is_exact in HW. lia.
Qed.
Theorem execution_has_no_owned_payload : forall request,
  D.weighted D.base_work_weight (S.work_counts (native_work request)) = native_work request /\
  D.weighted D.record_weight (S.work_counts (native_work request)) = 0 /\
  D.weighted D.byte_weight (S.work_counts (native_work request)) = 0.
Proof. intros. apply S.work_counts_projection. Qed.

Section NativeExecution.
Variable execute_native : forall request, ResultType request.
Definition inspect maximum request available :=
  precharged_action false available 1 0 (fun _ => checked_work maximum request).
Definition admitted_identity (supported : bool) maximum request available :=
  if supported then
    match inspect maximum request available with
    | Refused remaining => Refused remaining
    | Accepted remaining work => precharged_action false remaining work 0
        (fun _ => Some (execute_native request))
    end
  else Refused available.
Theorem success_preserves_original_result_and_charge :
  forall supported maximum request available paid result,
  admitted_identity supported maximum request available = Accepted paid result ->
  supported = true /\ result = execute_native request /\
  native_work request <= maximum /\
  work_left paid + 1 + native_work request = work_left available /\
  units_left paid = units_left available.
Proof.
  intros supported maximum request available paid result HC.
  destruct supported; [|discriminate]. unfold admitted_identity in HC.
  destruct (inspect maximum request available) as [remaining|remaining work]
    eqn:HI; [discriminate|].
  unfold inspect in HI. apply successful_action_constructs_only_the_paid_result in HI, HC.
  destruct HI as [_ [HW [HWI HUI]]], HC as [_ [HR [HWE HUE]]].
  apply checked_work_is_exact in HW. inversion HR; subst.
  repeat split; try reflexivity; lia.
Qed.
Theorem unsupported_profile_precedes_inspection : forall maximum request available,
  admitted_identity false maximum request available = Refused available.
Proof. reflexivity. Qed.
Theorem inspection_refusal_precedes_native_action : forall maximum request available,
  reserve available 1 0 = None ->
  admitted_identity true maximum request available = Refused available.
Proof.
  intros maximum request available HR. unfold admitted_identity, inspect.
  rewrite (failed_precharge_is_independent_of_constructor _ _ _ _ _ HR). reflexivity.
Qed.
Theorem arithmetic_refusal_keeps_metadata_charge : forall maximum request available paid,
  reserve available 1 0 = Some paid -> maximum < native_work request ->
  admitted_identity true maximum request available = Refused paid.
Proof.
  intros maximum request available paid HR HO. unfold admitted_identity, inspect.
  pose proof (overflow_cannot_wrap _ _ HO) as HC.
  rewrite (callback_failure_does_not_refund _ _ _ _ _ _ HR HC). reflexivity.
Qed.
Theorem execution_refusal_keeps_metadata_charge : forall maximum request available paid work,
  inspect maximum request available = Accepted paid work -> reserve paid work 0 = None ->
  admitted_identity true maximum request available = Refused paid.
Proof.
  intros maximum request available paid work HI HR. unfold admitted_identity. rewrite HI.
  now apply failed_precharge_is_independent_of_constructor.
Qed.
Theorem cancelled_metadata_stage_precedes_inspection : forall maximum request available,
  precharged_action true available 1 0 (fun _ => checked_work maximum request) = Refused available.
Proof. intros. reflexivity. Qed.
Theorem cancelled_execution_stage_keeps_metadata_charge :
  forall maximum request available paid work,
  inspect maximum request available = Accepted paid work ->
  precharged_action true paid work 0 (fun _ => Some (execute_native request)) = Refused paid.
Proof. intros. reflexivity. Qed.
End NativeExecution.

Print Assumptions identity_branch_groups.
Print Assumptions original_ordering_branch_groups.
Print Assumptions default_ne_adds_one_group.
Print Assumptions equal_vector_schedules.
Print Assumptions unequal_vector_schedules.
Print Assumptions visited_prefix_fits_width.
Print Assumptions native_prefix_groups_are_covered.
Print Assumptions checked_schedule_is_exact.
Print Assumptions checked_work_is_exact.
Print Assumptions overflow_cannot_wrap.
Print Assumptions execution_has_no_owned_payload.
Print Assumptions success_preserves_original_result_and_charge.
Print Assumptions unsupported_profile_precedes_inspection.
Print Assumptions inspection_refusal_precedes_native_action.
Print Assumptions arithmetic_refusal_keeps_metadata_charge.
Print Assumptions execution_refusal_keeps_metadata_charge.
Print Assumptions cancelled_metadata_stage_precedes_inspection.
Print Assumptions cancelled_execution_stage_keeps_metadata_charge.
End AdmittedIdentityComparison.
