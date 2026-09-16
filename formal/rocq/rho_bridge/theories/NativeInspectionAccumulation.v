(** Paid accumulation into the existing BindingCharge triple.

    Source: runtime/src/binding_receipt/charge.rs. Base work excludes bytes;
    the existing reservation projection adds bytes once and weights records
    by four. The fixed-size metadata group is reserved before constructing
    the incoming charge, checking component sums, and committing the result.
    No native operation is executed or prepaid by this inspection.

    This model concerns representability and the commit boundary, not the
    correctness of caller-supplied operation costs. The mathematical maximum
    models usize::MAX; checked products/sums reject exactly when the displayed
    nonnegative expressions exceed it. No allocator or callback cost is
    inferred, and retaining an accumulator has its own caller-side allowance. *)
From Stdlib Require Import Arith Bool Lia.
From RhoBridge Require Import RholangSourceScope RholangInitialGraphResources.

Module NativeInspectionAccumulation.
Record Charge := {
  base_work : nat;
  records : nat;
  owned_bytes : nat
}.
Definition projected_work charge := base_work charge + owned_bytes charge.
Definition projected_units charge := 4 * records charge + owned_bytes charge.
Definition representable maximum charge :=
  projected_work charge <= maximum /\ projected_units charge <= maximum.

Definition charge_new maximum work count bytes :=
  if (work + bytes <=? maximum) && (4 * count + bytes <=? maximum)
  then Some {| base_work := work; records := count; owned_bytes := bytes |}
  else None.

Lemma charge_new_success : forall maximum work count bytes charge,
  charge_new maximum work count bytes = Some charge ->
  base_work charge = work /\ records charge = count /\
  owned_bytes charge = bytes /\ representable maximum charge.
Proof.
  intros maximum work count bytes charge H. unfold charge_new in H.
  destruct ((work + bytes <=? maximum) && (4 * count + bytes <=? maximum)) eqn:CHECK;
    [|discriminate].
  inversion H; subst. apply andb_true_iff in CHECK as [WORK UNITS].
  apply Nat.leb_le in WORK, UNITS.
  unfold representable, projected_work, projected_units. cbn. auto.
Qed.

Definition charge_add maximum before more :=
  match checked_sum maximum (base_work before) (base_work more),
        checked_sum maximum (records before) (records more),
        checked_sum maximum (owned_bytes before) (owned_bytes more) with
  | Some work, Some count, Some bytes => charge_new maximum work count bytes
  | _, _, _ => None
  end.

Lemma charge_add_success : forall maximum before more after,
  charge_add maximum before more = Some after ->
  base_work after = base_work before + base_work more /\
  records after = records before + records more /\
  owned_bytes after = owned_bytes before + owned_bytes more /\
  representable maximum after.
Proof.
  intros maximum before more after H. unfold charge_add in H.
  destruct (checked_sum maximum (base_work before) (base_work more)) as [work|] eqn:WORK;
    [|discriminate].
  destruct (checked_sum maximum (records before) (records more)) as [count|] eqn:COUNT;
    [|discriminate].
  destruct (checked_sum maximum (owned_bytes before) (owned_bytes more)) as [bytes|] eqn:BYTES;
    [|discriminate].
  apply checked_sum_success_is_exact_and_bounded in WORK, COUNT, BYTES.
  apply charge_new_success in H. intuition congruence.
Qed.

Definition add_parts maximum before work count bytes :=
  match charge_new maximum work count bytes with
  | None => None
  | Some more => charge_add maximum before more
  end.

Lemma charge_new_accepts_every_representable_triple : forall maximum work count bytes,
  work + bytes <= maximum -> 4 * count + bytes <= maximum ->
  charge_new maximum work count bytes =
    Some {| base_work := work; records := count; owned_bytes := bytes |}.
Proof.
  intros maximum work count bytes WORK UNITS. unfold charge_new.
  rewrite (proj2 (Nat.leb_le _ _) WORK), (proj2 (Nat.leb_le _ _) UNITS). reflexivity.
Qed.

Lemma charge_add_accepts_every_representable_sum : forall maximum before more,
  projected_work before + projected_work more <= maximum ->
  projected_units before + projected_units more <= maximum ->
  charge_add maximum before more = Some
    {| base_work := base_work before + base_work more;
       records := records before + records more;
       owned_bytes := owned_bytes before + owned_bytes more |}.
Proof.
  intros maximum before more WORK UNITS.
  unfold projected_work, projected_units in *.
  assert (W : base_work before + base_work more <= maximum) by lia.
  assert (R : records before + records more <= maximum) by lia.
  assert (B : owned_bytes before + owned_bytes more <= maximum) by lia.
  unfold charge_add, checked_sum.
  rewrite (proj2 (Nat.leb_le _ _) W), (proj2 (Nat.leb_le _ _) R),
    (proj2 (Nat.leb_le _ _) B).
  apply charge_new_accepts_every_representable_triple; lia.
Qed.

Theorem fitting_projections_always_accumulate : forall maximum before work count bytes,
  projected_work before + work + bytes <= maximum ->
  projected_units before + 4 * count + bytes <= maximum ->
  add_parts maximum before work count bytes = Some
    {| base_work := base_work before + work;
       records := records before + count;
       owned_bytes := owned_bytes before + bytes |}.
Proof.
  intros maximum before work count bytes WORK UNITS.
  unfold add_parts.
  rewrite charge_new_accepts_every_representable_triple by
    (unfold projected_work, projected_units in *; lia).
  apply charge_add_accepts_every_representable_sum;
    unfold projected_work, projected_units in *; cbn; lia.
Qed.

Theorem accumulated_parts_are_exact_and_representable :
  forall maximum before work count bytes after,
  add_parts maximum before work count bytes = Some after ->
  base_work after = base_work before + work /\
  records after = records before + count /\
  owned_bytes after = owned_bytes before + bytes /\ representable maximum after.
Proof.
  intros maximum before work count bytes after H. unfold add_parts in H.
  destruct (charge_new maximum work count bytes) as [more|] eqn:MORE; [|discriminate].
  apply charge_new_success in MORE. apply charge_add_success in H. intuition congruence.
Qed.

Definition paid_accumulation maximum before work count bytes available :=
  precharged_action false available 1 0
    (fun _ => add_parts maximum before work count bytes).

Definition committed_charge before (result : ActionResult Charge) :=
  match result with Accepted _ after => after | Refused _ => before end.

Theorem successful_inspection_charges_metadata_only :
  forall maximum before work count bytes available paid after,
  paid_accumulation maximum before work count bytes available = Accepted paid after ->
  work_left paid + 1 = work_left available /\ units_left paid = units_left available /\
  base_work after = base_work before + work /\
  records after = records before + count /\
  owned_bytes after = owned_bytes before + bytes /\ representable maximum after.
Proof.
  intros maximum before work count bytes available paid after H.
  unfold paid_accumulation in H.
  apply successful_action_constructs_only_the_paid_result in H.
  destruct H as [_ [SUM [WORK UNITS]]].
  apply accumulated_parts_are_exact_and_representable in SUM. intuition lia.
Qed.

Theorem admission_refusal_precedes_all_accumulation :
  forall maximum before work count bytes available,
  reserve available 1 0 = None ->
  paid_accumulation maximum before work count bytes available = Refused available.
Proof. intros. unfold paid_accumulation. now apply failed_precharge_is_independent_of_constructor. Qed.

Theorem arithmetic_refusal_retains_the_metadata_charge :
  forall maximum before work count bytes available paid,
  reserve available 1 0 = Some paid ->
  add_parts maximum before work count bytes = None ->
  paid_accumulation maximum before work count bytes available = Refused paid.
Proof. intros. unfold paid_accumulation. now apply callback_failure_does_not_refund. Qed.

Theorem every_refusal_keeps_the_original_accumulator : forall before paid,
  committed_charge before (Refused paid) = before.
Proof. reflexivity. Qed.

Theorem projected_overflow_cannot_produce_a_receipt :
  forall maximum before work count bytes,
  maximum < projected_work before + work + bytes \/
  maximum < projected_units before + 4 * count + bytes ->
  add_parts maximum before work count bytes = None.
Proof.
  intros maximum before work count bytes OVER.
  destruct (add_parts maximum before work count bytes) as [after|] eqn:SUM; [|reflexivity].
  apply accumulated_parts_are_exact_and_representable in SUM.
  unfold representable, projected_work, projected_units in *. exfalso. lia.
Qed.
End NativeInspectionAccumulation.

Print Assumptions NativeInspectionAccumulation.accumulated_parts_are_exact_and_representable.
Print Assumptions NativeInspectionAccumulation.fitting_projections_always_accumulate.
Print Assumptions NativeInspectionAccumulation.successful_inspection_charges_metadata_only.
Print Assumptions NativeInspectionAccumulation.admission_refusal_precedes_all_accumulation.
Print Assumptions NativeInspectionAccumulation.arithmetic_refusal_retains_the_metadata_charge.
Print Assumptions NativeInspectionAccumulation.every_refusal_keeps_the_original_accumulator.
Print Assumptions NativeInspectionAccumulation.projected_overflow_cannot_produce_a_receipt.
