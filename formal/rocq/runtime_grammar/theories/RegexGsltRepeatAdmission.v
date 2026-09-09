(** Finite administrative refinement of the declared repetition rules.

    RInit introduces the literal constants zero and one. RBounds admits both
    endpoints with checked add-zero. RCheckUpper is the extra source state
    between the failed lower-bound comparison and the upper-bound decision.
    Every other control state reuses RepeatState and repeat_machine_step.

    This adapter describes reachable control from RInit, not arbitrary forged
    internal Computation terms. The zero/one constants are fixed by this
    entrypoint; RegexGsltNativeAdmission separately proves the native add-one
    realization under the existing endpoint invariant. The erasure below
    concerns semantic control only. It never erases receipts or work charges,
    and does not claim the Rust/source encoder itself is extracted from Rocq. *)

From Stdlib Require Import Bool PeanoNat ZArith Lia.
From RuntimeGrammar Require Import RegexGsltMatch RegexGsltSmartMachine
  RegexGsltRepeatMachine RegexGsltNativeAdmission.

Inductive RepeatSourceState :=
| SourceRepeatInit (pattern : RegexPattern) (lower upper : Z)
| SourceRepeatBounds (pattern : RegexPattern) (lower upper : Z)
| SourceRepeatCheckUpper (pattern : RegexPattern)
    (lower upper cursor : nat) (acc : RegexPattern)
| SourceRepeatBody (state : RepeatState).

Definition repeat_source_step (state : RepeatSourceState) : option RepeatSourceState :=
  match state with
  | SourceRepeatInit pattern lower upper => Some (SourceRepeatBounds pattern lower upper)
  | SourceRepeatBounds pattern lower upper =>
      match checked_native_nat_add lower 0, checked_native_nat_add upper 0 with
      | Some admitted_lower, Some admitted_upper => Some (SourceRepeatBody
          (RepeatRequired pattern (Z.to_nat admitted_lower) (Z.to_nat admitted_upper) 0 EpsilonPattern))
      | _, _ => None
      end
  | SourceRepeatCheckUpper pattern lower upper cursor acc => Some (SourceRepeatBody
      (RepeatAtUpper (Nat.eqb cursor upper) pattern lower upper cursor acc))
  | SourceRepeatBody (RepeatAtLower false pattern lower upper cursor acc) =>
      Some (SourceRepeatCheckUpper pattern lower upper cursor acc)
  | SourceRepeatBody body => option_map SourceRepeatBody (repeat_machine_step body)
  end.

Definition erase_repeat_administration (state : RepeatSourceState) : RepeatState :=
  match state with
  | SourceRepeatInit pattern lower upper
  | SourceRepeatBounds pattern lower upper =>
      RepeatRequired pattern (Z.to_nat lower) (Z.to_nat upper) 0 EpsilonPattern
  | SourceRepeatCheckUpper pattern lower upper cursor acc =>
      RepeatAtUpper (Nat.eqb cursor upper) pattern lower upper cursor acc
  | SourceRepeatBody body => body
  end.

Definition repeat_administrative_phase (state : RepeatSourceState) : nat :=
  match state with SourceRepeatInit _ _ _ => 2
  | SourceRepeatBounds _ _ _ | SourceRepeatCheckUpper _ _ _ _ _ => 1
  | SourceRepeatBody _ => 0 end.

Lemma checked_add_zero_preserves_value : forall value result,
  checked_native_nat_add value 0 = Some result -> result = value.
Proof.
  intros value result H. unfold checked_native_nat_add in H. rewrite Z.add_0_r in H.
  destruct (native_nat value && native_nat 0 && native_nat value); inversion H; reflexivity.
Qed.

Theorem repeat_source_step_simulation : forall source target,
  repeat_source_step source = Some target ->
  repeat_machine_step (erase_repeat_administration source) = Some (erase_repeat_administration target) \/
  (erase_repeat_administration source = erase_repeat_administration target /\
   repeat_administrative_phase target < repeat_administrative_phase source).
Proof.
  intros source target H. destruct source as [pattern lower upper|pattern lower upper|
    pattern lower upper cursor acc|body].
  - inversion H; subst. right. split; [reflexivity|cbn; lia].
  - cbn [repeat_source_step] in H.
    destruct (checked_native_nat_add lower 0) as [admitted_lower|] eqn:L; [|discriminate].
    destruct (checked_native_nat_add upper 0) as [admitted_upper|] eqn:U; [|discriminate].
    apply checked_add_zero_preserves_value in L, U. subst admitted_lower admitted_upper.
    inversion H; subst. right. split; [reflexivity|cbn; lia].
  - inversion H; subst. right. split; [reflexivity|cbn; lia].
  - destruct body; try destruct equal; cbn [repeat_source_step] in H;
      try match type of H with
      | option_map _ ?step = Some _ => destruct step eqn:E
      end; inversion H; subst; left; cbn [erase_repeat_administration];
      try assumption; reflexivity.
Qed.

Inductive RepeatSourceSteps : RepeatSourceState -> RepeatSourceState -> Prop :=
| SourceStepsRefl : forall state, RepeatSourceSteps state state
| SourceStepsNext : forall source next target,
    repeat_source_step source = Some next -> RepeatSourceSteps next target ->
    RepeatSourceSteps source target.

Lemma source_steps_trans : forall source middle target,
  RepeatSourceSteps source middle -> RepeatSourceSteps middle target -> RepeatSourceSteps source target.
Proof. intros source middle target H; induction H; eauto using SourceStepsNext. Qed.

Theorem source_repeat_run_simulation : forall source target,
  RepeatSourceSteps source target ->
  RepeatSteps (erase_repeat_administration source) (erase_repeat_administration target).
Proof.
  intros source target H; induction H; [constructor|].
  destruct (repeat_source_step_simulation _ _ H) as [Hstep|[Hequal Hphase]].
  - eapply RepeatStepsNext; eassumption.
  - now rewrite Hequal.
Qed.

Lemma body_model_step_is_realized : forall source target,
  repeat_machine_step source = Some target ->
  RepeatSourceSteps (SourceRepeatBody source) (SourceRepeatBody target).
Proof.
  intros source target H. destruct source; try destruct equal.
  all: try (eapply SourceStepsNext; [cbn [repeat_source_step]; rewrite H; reflexivity|constructor]).
  - inversion H; subst. eapply SourceStepsNext; [reflexivity|].
    eapply SourceStepsNext; [reflexivity|constructor].
Qed.

Lemma body_model_run_is_realized : forall source target,
  RepeatSteps source target -> RepeatSourceSteps (SourceRepeatBody source) (SourceRepeatBody target).
Proof.
  intros source target H; induction H; [constructor|].
  eapply source_steps_trans; [apply body_model_step_is_realized; eassumption|assumption].
Qed.

Theorem admitted_source_repeat_computes_reference : forall pattern lower upper,
  native_nat lower = true -> native_nat upper = true ->
  RepeatSourceSteps (SourceRepeatInit pattern lower upper)
    (SourceRepeatBody (RepeatDone (bounded_repeat pattern (Z.to_nat lower) (Z.to_nat upper)))).
Proof.
  intros pattern lower upper L U.
  apply checked_add_zero_admits_exactly_native_naturals in L, U.
  eapply SourceStepsNext; [reflexivity|].
  eapply SourceStepsNext.
  - cbn [repeat_source_step]. rewrite L, U. reflexivity.
  - apply body_model_run_is_realized, declared_repeat_computes_reference.
Qed.

Theorem completed_source_repeat_cannot_misreport : forall pattern lower upper result,
  RepeatSourceSteps (SourceRepeatInit pattern lower upper) (SourceRepeatBody (RepeatDone result)) ->
  result = bounded_repeat pattern (Z.to_nat lower) (Z.to_nat upper).
Proof.
  intros pattern lower upper result H. apply source_repeat_run_simulation in H.
  exact (completed_repeat_cannot_misreport _ _ _ _ H).
Qed.

Theorem completed_source_repeat_requires_admitted_bounds : forall pattern lower upper result,
  RepeatSourceSteps (SourceRepeatInit pattern lower upper) (SourceRepeatBody (RepeatDone result)) ->
  native_nat lower = true /\ native_nat upper = true.
Proof.
  intros pattern lower upper result H.
  inversion H; subst. cbn [repeat_source_step] in H0. inversion H0; subst.
  inversion H1; subst. cbn [repeat_source_step] in H2.
  destruct (checked_native_nat_add lower 0) as [admitted_lower|] eqn:L; [|discriminate].
  destruct (checked_native_nat_add upper 0) as [admitted_upper|] eqn:U; [|discriminate].
  pose proof (checked_add_zero_preserves_value _ _ L) as EL.
  pose proof (checked_add_zero_preserves_value _ _ U) as EU. subst admitted_lower admitted_upper.
  split; now apply checked_add_zero_admits_exactly_native_naturals.
Qed.

Print Assumptions checked_add_zero_preserves_value.
Print Assumptions repeat_source_step_simulation.
Print Assumptions source_steps_trans.
Print Assumptions source_repeat_run_simulation.
Print Assumptions body_model_step_is_realized.
Print Assumptions body_model_run_is_realized.
Print Assumptions admitted_source_repeat_computes_reference.
Print Assumptions completed_source_repeat_cannot_misreport.
Print Assumptions completed_source_repeat_requires_admitted_bounds.
