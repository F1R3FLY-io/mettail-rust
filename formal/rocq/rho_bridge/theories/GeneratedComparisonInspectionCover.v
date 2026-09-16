(** Metadata inspection of existing generated comparison leaf fragments.

    Source: iterative_cmp.rs::eq_arm_stmts and scalar/variable Eq arms call
    native_ne and return on true. cmp_arm_stmts's eager prefix calls native_cmp
    and returns on a non-Equal result; its deferred suffix evaluates native_cmp
    while constructing Verdict tasks and DOES NOT stop that construction on a
    decisive result. Child pairs retain the existing typed category and the
    Eq/Ord interpretation selected by that source site.

    Events below are a finite projection of those ORIGINAL source actions and
    observed replies, not another AST, comparator, runtime event tape or task
    executor. SourcePrefix includes normal completion, actual guard exits and
    refusal before the next action. Inspection projects calls/jobs without
    consulting replies. Its finite continuation is therefore an upper cover,
    not a prediction that all comparisons returned false/Equal. No result is
    supplied to CollectionCmpPda. Known Eq metadata shape decisions select the
    SAME branch before projection; a deferred Ord verdict is not such a guard.

    Per-demand natural allowances are parameters for separately established
    native/child receipts; the weighted theorem proves only their additive
    transport, not their adequacy. Each coordinate can be instantiated with
    work, records or owned bytes. Source association, paid metadata inspection,
    checked arithmetic and failure-safe retention remain emitter obligations.
    Scope hash-pattern ordering needs its own sealed metadata work projection;
    Binder is not given an Ord instance here. Driver/wrapper/collection costs,
    child-job execution, callback termination, panic recovery and complete
    whole-category or HashBag provider authority are explicitly excluded. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import AdmittedGeneratedComparisonScheduling
  GeneratedComparisonFieldResults.
Import ListNotations.

Module GeneratedComparisonInspectionCover.
Module S := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.
Module F := GeneratedComparisonFieldResults.GeneratedComparisonFieldResults.

Inductive Mode := Equality | Ordering.

Section TypedSources.
Context {Category : Type} (Operand : Category -> Type).

Inductive Pair :=
| DirectedPair : forall category, Operand category -> Operand category -> Pair.

Inductive Demand :=
| NativeNe : Pair -> Demand
| NativeCmp : Pair -> Demand
| ChildPair : Mode -> Pair -> Demand.

Inductive Event :=
| NeGuard : Pair -> bool -> Event
| CmpGuard : Pair -> comparison -> Event
| DeferredCmp : Pair -> comparison -> Event
| ScheduleChild : Mode -> Pair -> Event.

Definition demand event := match event with
  | NeGuard operands _ => NativeNe operands
  | CmpGuard operands _ | DeferredCmp operands _ => NativeCmp operands
  | ScheduleChild mode operands => ChildPair mode operands
  end.
Definition stops event := match event with
  | NeGuard _ different => different
  | CmpGuard _ Eq => false
  | CmpGuard _ _ => true
  | DeferredCmp _ _ | ScheduleChild _ _ => false
  end.
Definition inspect events := map demand events.

(** A refusal is permitted before any next source action; it cannot add a
    fictitious call or erase a call that has already occurred. *)
Inductive SourcePrefix : list Event -> list Demand -> Prop :=
| PrefixDone : SourcePrefix [] []
| PrefixRefused : forall pending, SourcePrefix pending []
| PrefixGuardExit : forall event rest,
    stops event = true -> SourcePrefix (event :: rest) [demand event]
| PrefixContinues : forall event rest observed,
    stops event = false -> SourcePrefix rest observed ->
    SourcePrefix (event :: rest) (demand event :: observed).

Theorem every_actual_or_refused_prefix_has_an_inspected_suffix :
  forall events observed, SourcePrefix events observed ->
  exists unexecuted, inspect events = observed ++ unexecuted.
Proof.
  intros events observed PREFIX. induction PREFIX.
  - exists []. reflexivity.
  - exists (inspect pending). reflexivity.
  - exists (inspect rest). reflexivity.
  - destruct IHPREFIX as [unexecuted IH]. exists unexecuted.
    change (demand event :: inspect rest = (demand event :: observed) ++ unexecuted).
    cbn [app]. now rewrite IH.
Qed.

Theorem every_observed_call_or_job_keeps_its_original_typed_direction :
  forall events observed item,
  SourcePrefix events observed -> In item observed -> In item (inspect events).
Proof.
  intros events observed item PREFIX MEMBER.
  destruct (every_actual_or_refused_prefix_has_an_inspected_suffix _ _ PREFIX)
    as [rest ORIGINAL]. rewrite ORIGINAL. apply in_or_app. now left.
Qed.

Definition allowance (cost : Demand -> nat) demands :=
  fold_right (fun item total => cost item + total) 0 demands.
Lemma allowance_app : forall cost first second,
  allowance cost (first ++ second) = allowance cost first + allowance cost second.
Proof.
  intros cost first. induction first as [|item rest IH]; intro second; [reflexivity|].
  change (cost item + allowance cost (rest ++ second) =
    (cost item + allowance cost rest) + allowance cost second).
  rewrite IH. lia.
Qed.

Theorem inspection_componentwise_covers_every_execution_or_error_prefix :
  forall cost events observed,
  SourcePrefix events observed -> allowance cost observed <= allowance cost (inspect events).
Proof.
  intros cost events observed PREFIX.
  destruct (every_actual_or_refused_prefix_has_an_inspected_suffix _ _ PREFIX)
    as [rest ORIGINAL]. rewrite ORIGINAL, allowance_app. lia.
Qed.

Theorem checked_request_multiplicity_can_scale_the_same_cover :
  forall cost events observed multiplicity,
  SourcePrefix events observed ->
  multiplicity * allowance cost observed <= multiplicity * allowance cost (inspect events).
Proof.
  intros cost events observed multiplicity PREFIX.
  apply Nat.mul_le_mono_l. now apply inspection_componentwise_covers_every_execution_or_error_prefix.
Qed.

Definition change_reply ne_reply cmp_reply event := match event with
  | NeGuard operands _ => NeGuard operands ne_reply
  | CmpGuard operands _ => CmpGuard operands cmp_reply
  | DeferredCmp operands _ => DeferredCmp operands cmp_reply
  | ScheduleChild mode operands => ScheduleChild mode operands
  end.

Theorem inspection_needs_no_native_reply : forall events ne_reply cmp_reply,
  inspect (map (change_reply ne_reply cmp_reply) events) = inspect events.
Proof.
  induction events as [|event rest IH]; intros ne_reply cmp_reply; [reflexivity|].
  unfold inspect in *. cbn [map]. rewrite IH. destruct event; reflexivity.
Qed.

Theorem inequality_is_not_replaced_by_ordering : forall pair,
  demand (NeGuard pair false) = NativeNe pair /\
  demand (CmpGuard pair Eq) = NativeCmp pair /\
  NativeNe pair <> NativeCmp pair.
Proof. intro pair. repeat split; try reflexivity. discriminate. Qed.

Theorem unknown_inequality_keeps_its_inspected_continuation : forall pair reply rest,
  inspect (NeGuard pair reply :: rest) = NativeNe pair :: inspect rest.
Proof. reflexivity. Qed.

Theorem deferred_decision_does_not_short_circuit_source_construction :
  forall pair reply rest observed,
  SourcePrefix rest observed ->
  SourcePrefix (DeferredCmp pair reply :: rest) (NativeCmp pair :: observed).
Proof. intros. apply PrefixContinues; [reflexivity|assumption]. Qed.

Theorem decisive_eager_guard_can_stop_but_inspection_keeps_later_fields :
  forall pair reply rest,
  reply <> Eq -> SourcePrefix (CmpGuard pair reply :: rest) [NativeCmp pair] /\
    inspect (CmpGuard pair reply :: rest) = NativeCmp pair :: inspect rest.
Proof.
  intros pair reply rest DECISIVE. split; [|reflexivity].
  apply PrefixGuardExit. destruct reply; [contradiction|reflexivity|reflexivity].
Qed.

(** Applied only where source metadata really selects a control branch: for
    example Eq's Some/Some route versus an immediate shape-mismatch exit.
    Deferred Ord's precomputed verdict is represented by DeferredCmp instead. *)
Definition eq_shape_choice (chosen : bool) (yes no : list Event) :=
  if chosen then yes else no.

Theorem known_eq_shape_choice_is_exact_before_inspection : forall chosen yes no,
  inspect (eq_shape_choice chosen yes no) =
    if chosen then inspect yes else inspect no.
Proof. intros []; reflexivity. Qed.

Theorem known_eq_shape_prefix_is_covered_by_only_the_selected_branch :
  forall cost chosen yes no observed,
  SourcePrefix (eq_shape_choice chosen yes no) observed ->
  allowance cost observed <=
    if chosen then allowance cost (inspect yes) else allowance cost (inspect no).
Proof.
  intros cost [] yes no observed PREFIX;
    now apply inspection_componentwise_covers_every_execution_or_error_prefix.
Qed.
End TypedSources.

(** Original construction and later consultation remain distinct. These are
    the established scheduling facts, not re-proved comparison semantics. *)
Theorem deferred_native_calls_use_existing_reverse_construction_order :
  forall eager left right,
  S.construction_calls (S.cmp_construction eager [left; right]) =
    S.construction_calls eager ++ S.construction_calls right ++ S.construction_calls left.
Proof. apply S.cmp_suffix_construction_is_reverse_group_order. Qed.

Theorem consulting_a_scheduled_verdict_does_not_repeat_its_native_comparison :
  forall position result,
  S.action_calls (S.ConsultTask (S.PrecomputedVerdict position result)) = [].
Proof. apply S.consulting_precomputed_verdict_does_not_compare. Qed.

Theorem a_later_precomputed_verdict_cannot_rewrite_the_earlier_result :
  F.Consultation [Eq; Lt; Gt] Lt /\ F.fold_decisions [Eq; Lt; Gt] = Lt.
Proof. apply F.later_precomputed_verdict_cannot_override_an_earlier_field. Qed.

Print Assumptions every_actual_or_refused_prefix_has_an_inspected_suffix.
Print Assumptions every_observed_call_or_job_keeps_its_original_typed_direction.
Print Assumptions inspection_componentwise_covers_every_execution_or_error_prefix.
Print Assumptions checked_request_multiplicity_can_scale_the_same_cover.
Print Assumptions inspection_needs_no_native_reply.
Print Assumptions inequality_is_not_replaced_by_ordering.
Print Assumptions unknown_inequality_keeps_its_inspected_continuation.
Print Assumptions deferred_decision_does_not_short_circuit_source_construction.
Print Assumptions decisive_eager_guard_can_stop_but_inspection_keeps_later_fields.
Print Assumptions known_eq_shape_choice_is_exact_before_inspection.
Print Assumptions known_eq_shape_prefix_is_covered_by_only_the_selected_branch.
Print Assumptions deferred_native_calls_use_existing_reverse_construction_order.
Print Assumptions consulting_a_scheduled_verdict_does_not_repeat_its_native_comparison.
Print Assumptions a_later_precomputed_verdict_cannot_rewrite_the_earlier_result.
End GeneratedComparisonInspectionCover.
