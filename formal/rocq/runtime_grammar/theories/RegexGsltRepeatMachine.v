(** Bounded surface repetition with ascending counters and smart submachines.

    Operational control needs equality and checked increment only, matching
    the existing native intrinsic interface. There is no hidden subtraction,
    comparison, host regex evaluator or recursive repeat call in step. The
    lower bound is tested first, so equal bounds produce exact repetition;
    reaching the upper bound before the lower bound produces Fail.
    Nat models checked nonnegative counters. Native width/overflow admission
    and the literal one carried by declarations remain encoding obligations. *)

From Stdlib Require Import PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch RegexGsltSmartMachine.

Inductive RepeatState :=
| RepeatRequired (pattern : RegexPattern) (lower upper cursor : nat) (acc : RegexPattern)
| RepeatAtLower (equal : bool) (pattern : RegexPattern)
    (lower upper cursor : nat) (acc : RegexPattern)
| RepeatAtUpper (equal : bool) (pattern : RegexPattern)
    (lower upper cursor : nat) (acc : RegexPattern)
| RepeatAppendRequired (pattern : RegexPattern) (lower upper cursor : nat) (sub : SmartState)
| RepeatOptional (pattern : RegexPattern) (upper cursor : nat) (required acc : RegexPattern)
| RepeatOptionalAtUpper (equal : bool) (pattern : RegexPattern)
    (upper cursor : nat) (required acc : RegexPattern)
| RepeatOptionalProduct (pattern : RegexPattern) (upper cursor : nat)
    (required : RegexPattern) (sub : SmartState)
| RepeatOptionalAlternative (pattern : RegexPattern) (upper cursor : nat)
    (required : RegexPattern) (sub : SmartState)
| RepeatFinish (sub : SmartState)
| RepeatDone (result : RegexPattern).

Definition repeat_machine_step (state : RepeatState) : option RepeatState :=
  match state with
  | RepeatRequired pattern lower upper cursor acc =>
      Some (RepeatAtLower (Nat.eqb cursor lower) pattern lower upper cursor acc)
  | RepeatAtLower equal pattern lower upper cursor acc => Some
      (if equal then RepeatOptional pattern upper cursor acc EpsilonPattern
       else RepeatAtUpper (Nat.eqb cursor upper) pattern lower upper cursor acc)
  | RepeatAtUpper equal pattern lower upper cursor acc => Some
      (if equal then RepeatDone FailPattern
       else RepeatAppendRequired pattern lower upper cursor (ConcatStart pattern acc))
  | RepeatAppendRequired pattern lower upper cursor sub =>
      match sub with
      | SmartDone result => Some (RepeatRequired pattern lower upper (S cursor) result)
      | _ => option_map (RepeatAppendRequired pattern lower upper cursor) (smart_machine_step sub)
      end
  | RepeatOptional pattern upper cursor required acc =>
      Some (RepeatOptionalAtUpper (Nat.eqb cursor upper) pattern upper cursor required acc)
  | RepeatOptionalAtUpper equal pattern upper cursor required acc => Some
      (if equal then RepeatFinish (ConcatStart required acc)
       else RepeatOptionalProduct pattern upper cursor required (ConcatStart pattern acc))
  | RepeatOptionalProduct pattern upper cursor required sub =>
      match sub with
      | SmartDone product =>
          Some (RepeatOptionalAlternative pattern upper cursor required (AltStart EpsilonPattern product))
      | _ => option_map (RepeatOptionalProduct pattern upper cursor required) (smart_machine_step sub)
      end
  | RepeatOptionalAlternative pattern upper cursor required sub =>
      match sub with
      | SmartDone result => Some (RepeatOptional pattern upper (S cursor) required result)
      | _ => option_map (RepeatOptionalAlternative pattern upper cursor required) (smart_machine_step sub)
      end
  | RepeatFinish sub =>
      match sub with
      | SmartDone result => Some (RepeatDone result)
      | _ => option_map RepeatFinish (smart_machine_step sub)
      end
  | RepeatDone _ => None
  end.

Inductive RepeatSteps : RepeatState -> RepeatState -> Prop :=
| RepeatStepsRefl : forall state, RepeatSteps state state
| RepeatStepsNext : forall source next target,
    repeat_machine_step source = Some next -> RepeatSteps next target -> RepeatSteps source target.

Lemma repeat_steps_trans : forall source middle target,
  RepeatSteps source middle -> RepeatSteps middle target -> RepeatSteps source target.
Proof. intros source middle target Hfirst Hlast; induction Hfirst; eauto using RepeatStepsNext. Qed.

Lemma repeat_one_step : forall source target,
  repeat_machine_step source = Some target -> RepeatSteps source target.
Proof. intros; eapply RepeatStepsNext; [eassumption|constructor]. Qed.

(** These lifting premises are discharged below for each concrete wrapper;
    they are commuting step equations, not assumed implementation flags. *)
Lemma repeat_lifts_completed_smart_run : forall (wrap : SmartState -> RepeatState)
    (finish : RegexPattern -> RepeatState),
  (forall sub next, smart_machine_step sub = Some next ->
    repeat_machine_step (wrap sub) = Some (wrap next)) ->
  (forall result, repeat_machine_step (wrap (SmartDone result)) = Some (finish result)) ->
  forall fuel sub result, run_smart_machine fuel sub = Some result ->
    RepeatSteps (wrap sub) (finish result).
Proof.
  intros wrap finish Hstep Hdone fuel. induction fuel as [|fuel IH]; intros sub result H.
  - destruct sub; cbn in H; try discriminate; inversion H; subst;
      apply repeat_one_step, Hdone.
  - destruct (smart_nonterminal_progress sub) as [[value E]|[next E]].
    + subst. cbn in H. inversion H; subst. apply repeat_one_step, Hdone.
    + rewrite (smart_step_is_nonterminal _ _ E) in H.
      eapply RepeatStepsNext; [exact (Hstep _ _ E)|]. now apply IH.
Qed.

Lemma required_append_completes : forall pattern lower upper cursor acc,
  RepeatSteps (RepeatAppendRequired pattern lower upper cursor (ConcatStart pattern acc))
    (RepeatRequired pattern lower upper (S cursor) (smart_concat pattern acc)).
Proof.
  intros. eapply repeat_lifts_completed_smart_run with (fuel := 2).
  - intros sub next H; destruct sub; try discriminate;
      cbn [repeat_machine_step]; now rewrite H.
  - reflexivity.
  - apply declared_concat_computes_reference.
Qed.

Lemma optional_product_completes : forall pattern upper cursor required acc,
  RepeatSteps (RepeatOptionalProduct pattern upper cursor required (ConcatStart pattern acc))
    (RepeatOptionalAlternative pattern upper cursor required
      (AltStart EpsilonPattern (smart_concat pattern acc))).
Proof.
  intros. eapply repeat_lifts_completed_smart_run with
    (wrap := RepeatOptionalProduct pattern upper cursor required)
    (finish := fun product => RepeatOptionalAlternative pattern upper cursor required
      (AltStart EpsilonPattern product)) (fuel := 2).
  - intros sub next H; destruct sub; try discriminate;
      cbn [repeat_machine_step]; now rewrite H.
  - reflexivity.
  - apply declared_concat_computes_reference.
Qed.

Lemma optional_alternative_completes : forall pattern upper cursor required product,
  RepeatSteps (RepeatOptionalAlternative pattern upper cursor required (AltStart EpsilonPattern product))
    (RepeatOptional pattern upper (S cursor) required (smart_alt EpsilonPattern product)).
Proof.
  intros. eapply repeat_lifts_completed_smart_run with (fuel := 4).
  - intros sub next H; destruct sub; try discriminate;
      cbn [repeat_machine_step]; now rewrite H.
  - reflexivity.
  - apply declared_alt_computes_reference.
Qed.

Lemma repeat_finish_completes : forall required optional,
  RepeatSteps (RepeatFinish (ConcatStart required optional))
    (RepeatDone (smart_concat required optional)).
Proof.
  intros. eapply repeat_lifts_completed_smart_run with (fuel := 2).
  - intros sub next H; destruct sub; try discriminate;
      cbn [repeat_machine_step]; now rewrite H.
  - reflexivity.
  - apply declared_concat_computes_reference.
Qed.

Theorem required_repeat_reaches_lower : forall remaining pattern lower upper cursor acc,
  cursor + remaining = lower -> lower <= upper ->
  RepeatSteps (RepeatRequired pattern lower upper cursor acc)
    (RepeatOptional pattern upper lower
      (Nat.iter remaining (smart_concat pattern) acc) EpsilonPattern).
Proof.
  induction remaining as [|remaining IH]; intros pattern lower upper cursor acc Hsum Horder.
  - assert (E : cursor = lower) by lia. subst cursor.
    eapply RepeatStepsNext; [reflexivity|]. rewrite Nat.eqb_refl.
    apply repeat_one_step; reflexivity.
  - assert (Elow : Nat.eqb cursor lower = false) by (apply Nat.eqb_neq; lia).
    assert (Ehigh : Nat.eqb cursor upper = false) by (apply Nat.eqb_neq; lia).
    eapply RepeatStepsNext; [reflexivity|]. rewrite Elow.
    eapply RepeatStepsNext; [reflexivity|]. rewrite Ehigh.
    eapply RepeatStepsNext; [reflexivity|].
    eapply repeat_steps_trans; [apply required_append_completes|].
    rewrite Nat.iter_succ_r. apply IH; lia.
Qed.

Theorem invalid_repeat_reaches_upper_first : forall remaining pattern lower upper cursor acc,
  cursor + remaining = upper -> upper < lower ->
  RepeatSteps (RepeatRequired pattern lower upper cursor acc) (RepeatDone FailPattern).
Proof.
  induction remaining as [|remaining IH]; intros pattern lower upper cursor acc Hsum Horder.
  - assert (E : cursor = upper) by lia. subst cursor.
    assert (Elow : Nat.eqb upper lower = false) by (apply Nat.eqb_neq; lia).
    eapply RepeatStepsNext; [reflexivity|]. rewrite Elow.
    eapply RepeatStepsNext; [reflexivity|]. rewrite Nat.eqb_refl.
    apply repeat_one_step; reflexivity.
  - assert (Elow : Nat.eqb cursor lower = false) by (apply Nat.eqb_neq; lia).
    assert (Ehigh : Nat.eqb cursor upper = false) by (apply Nat.eqb_neq; lia).
    eapply RepeatStepsNext; [reflexivity|]. rewrite Elow.
    eapply RepeatStepsNext; [reflexivity|]. rewrite Ehigh.
    eapply RepeatStepsNext; [reflexivity|].
    eapply repeat_steps_trans; [apply required_append_completes|]. apply IH; lia.
Qed.

Definition optional_iteration (pattern acc : RegexPattern) :=
  smart_alt EpsilonPattern (smart_concat pattern acc).

Theorem optional_repeat_reaches_upper : forall remaining pattern upper cursor required acc,
  cursor + remaining = upper ->
  RepeatSteps (RepeatOptional pattern upper cursor required acc)
    (RepeatDone (smart_concat required (Nat.iter remaining (optional_iteration pattern) acc))).
Proof.
  induction remaining as [|remaining IH]; intros pattern upper cursor required acc Hsum.
  - assert (E : cursor = upper) by lia. subst cursor.
    eapply RepeatStepsNext; [reflexivity|]. rewrite Nat.eqb_refl.
    eapply RepeatStepsNext; [reflexivity|]. apply repeat_finish_completes.
  - assert (Ehigh : Nat.eqb cursor upper = false) by (apply Nat.eqb_neq; lia).
    eapply RepeatStepsNext; [reflexivity|]. rewrite Ehigh.
    eapply RepeatStepsNext; [reflexivity|].
    eapply repeat_steps_trans; [apply optional_product_completes|].
    eapply repeat_steps_trans; [apply optional_alternative_completes|].
    rewrite Nat.iter_succ_r. apply IH; lia.
Qed.

Lemma iteration_is_exact_repeat : forall count pattern,
  Nat.iter count (smart_concat pattern) EpsilonPattern = repeat_exactly pattern count.
Proof.
  induction count; intros; [reflexivity|].
  change (smart_concat pattern (Nat.iter count (smart_concat pattern) EpsilonPattern) =
    smart_concat pattern (repeat_exactly pattern count)).
  now rewrite IHcount.
Qed.

Lemma iteration_is_optional_repeat : forall count pattern,
  Nat.iter count (optional_iteration pattern) EpsilonPattern = repeat_at_most pattern count.
Proof.
  induction count; intros; [reflexivity|].
  change (smart_alt EpsilonPattern
    (smart_concat pattern (Nat.iter count (optional_iteration pattern) EpsilonPattern)) =
    smart_alt EpsilonPattern (smart_concat pattern (repeat_at_most pattern count))).
  now rewrite IHcount.
Qed.

Theorem declared_repeat_computes_reference : forall pattern lower upper,
  RepeatSteps (RepeatRequired pattern lower upper 0 EpsilonPattern)
    (RepeatDone (bounded_repeat pattern lower upper)).
Proof.
  intros pattern lower upper. unfold bounded_repeat.
  destruct (Nat.leb lower upper) eqn:E.
  - apply Nat.leb_le in E.
    eapply repeat_steps_trans.
    + apply required_repeat_reaches_lower with (remaining := lower); lia.
    + rewrite <- iteration_is_exact_repeat, <- iteration_is_optional_repeat.
      apply optional_repeat_reaches_upper. lia.
  - apply Nat.leb_gt in E.
    apply invalid_repeat_reaches_upper_first with (remaining := upper); lia.
Qed.

Lemma repeat_terminal_is_unique : forall source first,
  RepeatSteps source first -> repeat_machine_step first = None ->
  forall second, RepeatSteps source second -> repeat_machine_step second = None -> first = second.
Proof.
  intros source first Hfirst. induction Hfirst; intros Hterminal second Hsecond Hterminal2.
  - inversion Hsecond; subst; [reflexivity|congruence].
  - inversion Hsecond; subst; [congruence|].
    assert (next = next0) by congruence. subst next0. eapply IHHfirst; eassumption.
Qed.

Theorem completed_repeat_cannot_misreport : forall pattern lower upper result,
  RepeatSteps (RepeatRequired pattern lower upper 0 EpsilonPattern) (RepeatDone result) ->
  result = bounded_repeat pattern lower upper.
Proof.
  intros. pose proof (repeat_terminal_is_unique _ _ H eq_refl _
    (declared_repeat_computes_reference pattern lower upper) eq_refl) as E.
  now inversion E.
Qed.

(** Concrete control invariants establish that each increment is below its
    admitted upper endpoint, not merely that a Nat-valued reference terminates. *)
Definition repeat_control_valid (state : RepeatState) : Prop :=
  match state with
  | RepeatRequired _ lower upper cursor _ => cursor <= lower /\ cursor <= upper
  | RepeatAtLower equal _ lower upper cursor _ =>
      equal = Nat.eqb cursor lower /\ cursor <= lower /\ cursor <= upper
  | RepeatAtUpper equal _ lower upper cursor _ =>
      equal = Nat.eqb cursor upper /\ cursor < lower /\ cursor <= upper
  | RepeatAppendRequired _ lower upper cursor _ => cursor < lower /\ cursor < upper
  | RepeatOptional _ upper cursor _ _ => cursor <= upper
  | RepeatOptionalAtUpper equal _ upper cursor _ _ =>
      equal = Nat.eqb cursor upper /\ cursor <= upper
  | RepeatOptionalProduct _ upper cursor _ _
  | RepeatOptionalAlternative _ upper cursor _ _ => cursor < upper
  | RepeatFinish _ | RepeatDone _ => True
  end.

Theorem repeat_step_preserves_control_invariants : forall source target,
  repeat_control_valid source -> repeat_machine_step source = Some target ->
  repeat_control_valid target.
Proof.
  intros source target Hvalid Hstep. destruct source as
    [pattern lower upper cursor acc|equal pattern lower upper cursor acc|
     equal pattern lower upper cursor acc|pattern lower upper cursor sub|
     pattern upper cursor required acc|equal pattern upper cursor required acc|
     pattern upper cursor required sub|pattern upper cursor required sub|sub|result];
    cbn [repeat_control_valid] in Hvalid.
  - inversion Hstep; subst. cbn [repeat_control_valid]. tauto.
  - destruct Hvalid as [Heq [Hlow Hup]]. symmetry in Heq. destruct equal.
    + apply Nat.eqb_eq in Heq. inversion Hstep; subst. exact Hup.
    + apply Nat.eqb_neq in Heq. inversion Hstep; subst.
      cbn [repeat_control_valid]. split; [reflexivity|lia].
  - destruct Hvalid as [Heq [Hlow Hup]]. symmetry in Heq. destruct equal.
    + inversion Hstep; subst. exact I.
    + apply Nat.eqb_neq in Heq. inversion Hstep; subst. cbn [repeat_control_valid]. lia.
  - destruct sub; cbn [repeat_machine_step smart_machine_step option_map] in Hstep;
      inversion Hstep; subst; cbn [repeat_control_valid]; lia.
  - inversion Hstep; subst. cbn [repeat_control_valid]. auto.
  - destruct Hvalid as [Heq Hup]. symmetry in Heq. destruct equal.
    + inversion Hstep; subst. exact I.
    + apply Nat.eqb_neq in Heq. inversion Hstep; subst. cbn [repeat_control_valid]. lia.
  - destruct sub; cbn [repeat_machine_step smart_machine_step option_map] in Hstep;
      inversion Hstep; subst; cbn [repeat_control_valid]; lia.
  - destruct sub; cbn [repeat_machine_step smart_machine_step option_map] in Hstep;
      inversion Hstep; subst; cbn [repeat_control_valid]; lia.
  - destruct sub; cbn [repeat_machine_step smart_machine_step option_map] in Hstep;
      inversion Hstep; subst; exact I.
  - discriminate.
Qed.

Lemma repeat_steps_preserve_control_invariants : forall source target,
  RepeatSteps source target -> repeat_control_valid source -> repeat_control_valid target.
Proof.
  intros source target H. induction H; intro Hvalid; [assumption|].
  apply IHRepeatSteps. eapply repeat_step_preserves_control_invariants; eassumption.
Qed.

Theorem reachable_repeat_controls_are_valid : forall pattern lower upper state,
  RepeatSteps (RepeatRequired pattern lower upper 0 EpsilonPattern) state ->
  repeat_control_valid state.
Proof.
  intros. eapply repeat_steps_preserve_control_invariants; [eassumption|].
  cbn [repeat_control_valid]. lia.
Qed.

Theorem required_increment_fits_admitted_endpoint :
  forall pattern lower upper cursor result maximum,
  repeat_control_valid (RepeatAppendRequired pattern lower upper cursor (SmartDone result)) ->
  upper <= maximum -> S cursor <= maximum.
Proof. intros; cbn [repeat_control_valid] in *; lia. Qed.

Theorem optional_increment_fits_admitted_endpoint :
  forall pattern upper cursor required result maximum,
  repeat_control_valid (RepeatOptionalAlternative pattern upper cursor required (SmartDone result)) ->
  upper <= maximum -> S cursor <= maximum.
Proof. intros; cbn [repeat_control_valid] in *; lia. Qed.

Print Assumptions repeat_steps_trans.
Print Assumptions repeat_one_step.
Print Assumptions repeat_lifts_completed_smart_run.
Print Assumptions required_append_completes.
Print Assumptions optional_product_completes.
Print Assumptions optional_alternative_completes.
Print Assumptions repeat_finish_completes.
Print Assumptions required_repeat_reaches_lower.
Print Assumptions invalid_repeat_reaches_upper_first.
Print Assumptions optional_repeat_reaches_upper.
Print Assumptions iteration_is_exact_repeat.
Print Assumptions iteration_is_optional_repeat.
Print Assumptions declared_repeat_computes_reference.
Print Assumptions repeat_terminal_is_unique.
Print Assumptions completed_repeat_cannot_misreport.
Print Assumptions repeat_step_preserves_control_invariants.
Print Assumptions repeat_steps_preserve_control_invariants.
Print Assumptions reachable_repeat_controls_are_valid.
Print Assumptions required_increment_fits_admitted_endpoint.
Print Assumptions optional_increment_fits_admitted_endpoint.
