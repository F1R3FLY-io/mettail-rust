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

(** BindingCharge::checked_scale checks each product, then invokes new on
    the three products. As in AdmittedIdentityComparison.checked_schedule,
    checked_sum maximum 0 product is the exact mathematical representability
    test for Rust's checked_mul; the Rust multiplication MUST be checked.
    This scales accounting data, not an assertion about any native callback. *)
Definition charge_scale maximum before factor :=
  match checked_sum maximum 0 (base_work before * factor),
        checked_sum maximum 0 (records before * factor),
        checked_sum maximum 0 (owned_bytes before * factor) with
  | Some work, Some count, Some bytes => charge_new maximum work count bytes
  | _, _, _ => None
  end.

Theorem scaled_charge_is_exact_and_representable : forall maximum before factor after,
  charge_scale maximum before factor = Some after ->
  base_work after = base_work before * factor /\
  records after = records before * factor /\
  owned_bytes after = owned_bytes before * factor /\ representable maximum after.
Proof.
  intros maximum before factor after SCALE. unfold charge_scale in SCALE.
  destruct (checked_sum maximum 0 (base_work before * factor)) as [work|] eqn:WORK;
    [|discriminate].
  destruct (checked_sum maximum 0 (records before * factor)) as [count|] eqn:COUNT;
    [|discriminate].
  destruct (checked_sum maximum 0 (owned_bytes before * factor)) as [bytes|] eqn:BYTES;
    [|discriminate].
  apply checked_sum_success_is_exact_and_bounded in WORK, COUNT, BYTES.
  apply charge_new_success in SCALE.
  destruct WORK as [WORK _], COUNT as [COUNT _], BYTES as [BYTES _].
  destruct SCALE as [SW [SR [SB FIT]]].
  split; [now rewrite SW, WORK|].
  split; [now rewrite SR, COUNT|].
  split; [now rewrite SB, BYTES|exact FIT].
Qed.

Theorem scaled_projections_count_owned_bytes_once : forall maximum before factor after,
  charge_scale maximum before factor = Some after ->
  projected_work after = projected_work before * factor /\
  projected_units after = projected_units before * factor.
Proof.
  intros maximum before factor after SCALE.
  apply scaled_charge_is_exact_and_representable in SCALE.
  destruct SCALE as [WORK [COUNT [BYTES FIT]]].
  unfold projected_work, projected_units. rewrite WORK, COUNT, BYTES. split; nia.
Qed.

Theorem fitting_scaled_projections_are_accepted : forall maximum before factor,
  projected_work before * factor <= maximum ->
  projected_units before * factor <= maximum ->
  charge_scale maximum before factor = Some
    {| base_work := base_work before * factor;
       records := records before * factor;
       owned_bytes := owned_bytes before * factor |}.
Proof.
  intros maximum before factor WORK UNITS.
  unfold projected_work, projected_units in *.
  assert (W : checked_sum maximum 0 (base_work before * factor) =
    Some (base_work before * factor)).
  { apply checked_sum_success_is_exact_and_bounded. split; nia. }
  assert (R : checked_sum maximum 0 (records before * factor) =
    Some (records before * factor)).
  { apply checked_sum_success_is_exact_and_bounded. split; nia. }
  assert (B : checked_sum maximum 0 (owned_bytes before * factor) =
    Some (owned_bytes before * factor)).
  { apply checked_sum_success_is_exact_and_bounded. split; nia. }
  unfold charge_scale. rewrite W, R, B.
  apply charge_new_accepts_every_representable_triple; nia.
Qed.

Theorem scaled_projection_overflow_is_refused : forall maximum before factor,
  maximum < projected_work before * factor \/
  maximum < projected_units before * factor -> charge_scale maximum before factor = None.
Proof.
  intros maximum before factor OVER.
  destruct (charge_scale maximum before factor) as [after|] eqn:SCALE; [|reflexivity].
  pose proof (scaled_projections_count_owned_bytes_once _ _ _ _ SCALE) as [WORK UNITS].
  apply scaled_charge_is_exact_and_representable in SCALE.
  destruct SCALE as [_ [_ [_ FIT]]]. unfold representable in FIT. exfalso. lia.
Qed.

(** The emitted helper takes raw parts. It pays one metadata group BEFORE
    both new and scale, then passes successful scaled fields to the existing
    paid_accumulation (which independently pays its own metadata group).
    Do not simplify by multiplying raw invalid parts by zero before new. *)
Definition scale_parts maximum work count bytes factor :=
  match charge_new maximum work count bytes with
  | None => None
  | Some original => charge_scale maximum original factor
  end.
Definition paid_scaled_parts maximum work count bytes factor available :=
  precharged_action false available 1 0
    (fun _ => scale_parts maximum work count bytes factor).

Theorem original_parts_refusal_survives_every_factor : forall maximum work count bytes factor,
  charge_new maximum work count bytes = None ->
  scale_parts maximum work count bytes factor = None.
Proof. intros. unfold scale_parts. now rewrite H. Qed.

Theorem successful_paid_scaling_is_exact :
  forall maximum work count bytes factor available paid scaled,
  paid_scaled_parts maximum work count bytes factor available = Accepted paid scaled ->
  work_left paid + 1 = work_left available /\ units_left paid = units_left available /\
  base_work scaled = work * factor /\ records scaled = count * factor /\
  owned_bytes scaled = bytes * factor /\ representable maximum scaled.
Proof.
  intros maximum work count bytes factor available paid scaled PAID.
  unfold paid_scaled_parts in PAID.
  apply successful_action_constructs_only_the_paid_result in PAID.
  destruct PAID as [_ [SCALE [WORK UNITS]]]. unfold scale_parts in SCALE.
  destruct (charge_new maximum work count bytes) as [original|] eqn:NEW; [|discriminate].
  apply charge_new_success in NEW.
  apply scaled_charge_is_exact_and_representable in SCALE.
  destruct NEW as [NW [NR [NB ORIGINAL]]].
  destruct SCALE as [SW [SR [SB FIT]]].
  split; [exact WORK|]. split; [lia|].
  split; [now rewrite SW, NW|]. split; [now rewrite SR, NR|].
  split; [now rewrite SB, NB|exact FIT].
Qed.

Theorem scaling_admission_refusal_precedes_arithmetic :
  forall maximum work count bytes factor available,
  reserve available 1 0 = None ->
  paid_scaled_parts maximum work count bytes factor available = Refused available.
Proof. intros. unfold paid_scaled_parts. now apply failed_precharge_is_independent_of_constructor. Qed.

Theorem scaling_arithmetic_refusal_keeps_metadata_charge :
  forall maximum work count bytes factor available paid,
  reserve available 1 0 = Some paid -> scale_parts maximum work count bytes factor = None ->
  paid_scaled_parts maximum work count bytes factor available = Refused paid.
Proof. intros. unfold paid_scaled_parts. now apply callback_failure_does_not_refund. Qed.
End NativeInspectionAccumulation.

Print Assumptions NativeInspectionAccumulation.accumulated_parts_are_exact_and_representable.
Print Assumptions NativeInspectionAccumulation.fitting_projections_always_accumulate.
Print Assumptions NativeInspectionAccumulation.successful_inspection_charges_metadata_only.
Print Assumptions NativeInspectionAccumulation.admission_refusal_precedes_all_accumulation.
Print Assumptions NativeInspectionAccumulation.arithmetic_refusal_retains_the_metadata_charge.
Print Assumptions NativeInspectionAccumulation.every_refusal_keeps_the_original_accumulator.
Print Assumptions NativeInspectionAccumulation.projected_overflow_cannot_produce_a_receipt.
Print Assumptions NativeInspectionAccumulation.scaled_charge_is_exact_and_representable.
Print Assumptions NativeInspectionAccumulation.scaled_projections_count_owned_bytes_once.
Print Assumptions NativeInspectionAccumulation.fitting_scaled_projections_are_accepted.
Print Assumptions NativeInspectionAccumulation.scaled_projection_overflow_is_refused.
Print Assumptions NativeInspectionAccumulation.original_parts_refusal_survives_every_factor.
Print Assumptions NativeInspectionAccumulation.successful_paid_scaling_is_exact.
Print Assumptions NativeInspectionAccumulation.scaling_admission_refusal_precedes_arithmetic.
Print Assumptions NativeInspectionAccumulation.scaling_arithmetic_refusal_keeps_metadata_charge.
