(** * Reporting admission work without changing its decision

    An admission body already maintains a stage-local work counter. Legacy
    callers observe only its decision; the installed adapter must also receive
    that counter on rejection. The new wrapper runs that same body once and
    exports both observations. The first theorem is parametric in the body,
    rather than assuming it computes correct admission or correct usage.

    The arithmetic layer reuses InstalledFltJudgments. Conversion consumes C;
    admission consumes A; later kernel execution reports K including A. Hence
    the continuation adds K-A, not K, and must check A <= K first. These are
    logical work laws, not byte-allocation or semantic-grade equations. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From RuntimeGrammar Require Import InstalledFltJudgments.

Module InstalledFltUsage.
Module Budget := InstalledFltJudgments.InstalledFltJudgments.

Section SameBody.
  Context {Input Decision : Type}.
  Definition legacy (body : Input -> Decision * nat) input := fst (body input).
  Definition accounted (body : Input -> Decision * nat) input := body input.

  Theorem accounted_wrapper_preserves_the_legacy_decision : forall body input,
    fst (accounted body input) = legacy body input.
  Proof. reflexivity. Qed.

  Theorem accounted_wrapper_reports_every_terminal_counter :
    forall body input decision used,
      body input = (decision, used) ->
      accounted body input = (decision, used).
  Proof. intros; exact H. Qed.
End SameBody.

Definition remaining ceiling prefix :=
  if Nat.leb prefix ceiling then Some (ceiling - prefix) else None.

Theorem stage_ceiling_preserves_the_prior_prefix :
  forall ceiling prefix allowance used,
    remaining ceiling prefix = Some allowance -> used <= allowance ->
    prefix + used <= ceiling.
Proof.
  intros ceiling prefix allowance used H Hused. unfold remaining in H.
  destruct (Nat.leb prefix ceiling) eqn:E; try discriminate.
  apply Nat.leb_le in E. inversion H; subst. lia.
Qed.

Definition absorb_kernel ceiling current admission aggregate :=
  if Nat.leb admission aggregate
  then Budget.charge_work ceiling current (aggregate - admission)
  else None.

Theorem execution_aggregate_is_charged_exactly_once :
  forall ceiling conversion admission aggregate total,
    absorb_kernel ceiling (conversion + admission) admission aggregate = Some total ->
    admission <= aggregate /\ total = conversion + aggregate /\ total <= ceiling.
Proof.
  intros ceiling conversion admission aggregate total H. unfold absorb_kernel in H.
  destruct (Nat.leb admission aggregate) eqn:E; try discriminate.
  apply Nat.leb_le in E.
  apply Budget.successful_charge_preserves_prefix_and_ceiling in H. lia.
Qed.

Theorem underreported_aggregate_is_refused : forall ceiling current admission aggregate,
  aggregate < admission -> absorb_kernel ceiling current admission aggregate = None.
Proof.
  intros. unfold absorb_kernel.
  assert (E : Nat.leb admission aggregate = false) by (apply Nat.leb_gt; lia).
  now rewrite E.
Qed.

Example admission_is_not_charged_twice : absorb_kernel 20 (4 + 3) 3 10 = Some 14.
Proof. reflexivity. Qed.

(** Logical reservation is tracked separately from allocator-reported capacity.
    A full logical buffer adds max(1, capacity) slots. The representation may
    already have physical spare capacity, but that does not affect the charge.
    These laws complement the occurrence machine's per-step work law; they do
    not assert a physical allocator capacity or recoverable heap bound. *)
Definition growth capacity := Nat.max 1 capacity.
Definition expanded_capacity capacity := capacity + growth capacity.

Theorem logical_growth_makes_room : forall length capacity,
  length <= capacity -> S length <= expanded_capacity capacity.
Proof.
  intros length capacity H. unfold expanded_capacity, growth.
  pose proof (Nat.le_max_l 1 capacity). lia.
Qed.

Theorem growth_charge_is_the_exact_new_slot_count : forall capacity width,
  expanded_capacity capacity * width = capacity * width + growth capacity * width.
Proof. intros. unfold expanded_capacity. apply Nat.mul_add_distr_r. Qed.

End InstalledFltUsage.

Print Assumptions InstalledFltUsage.accounted_wrapper_preserves_the_legacy_decision.
Print Assumptions InstalledFltUsage.accounted_wrapper_reports_every_terminal_counter.
Print Assumptions InstalledFltUsage.stage_ceiling_preserves_the_prior_prefix.
Print Assumptions InstalledFltUsage.execution_aggregate_is_charged_exactly_once.
Print Assumptions InstalledFltUsage.underreported_aggregate_is_refused.
Print Assumptions InstalledFltUsage.logical_growth_makes_room.
Print Assumptions InstalledFltUsage.growth_charge_is_the_exact_new_slot_count.
