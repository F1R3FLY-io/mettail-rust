(** Returned field verdicts for the existing generated comparison schedule.
    Source: iterative_cmp.rs cmp_arm_stmts and generate_cmp_engine.
    Native suffix verdicts are computed during reverse construction but are
    consulted in forward field order. A category helper's Equal return may
    only mean that descendants were scheduled: it is not a completed child
    result. The child interpretation below denotes completed child results.
    The expansion lemma supplies the induction/composition interface for an
    actual child's arm. Collection completion through nearest Resume still
    needs its separate entry/list-result source projection; no Start/Resume
    implementation is replaced by an atomic helper-return assumption here.

    This file proves result algebra and successful source branch traces,
    reusing the already proved push/pop ordering and admission/publication
    laws. It does not construct another comparator, identify Eq with term
    equality, assume an order law, or certify every generated constructor.
    Constructor census/field interpretation and completed-child induction
    remain source instantiations, not consequences of list algebra. *)
From Stdlib Require Import List Arith.PeanoNat.
From RhoBridge Require Import AdmittedGeneratedComparisonScheduling AdmittedGeneratedHashScheduling.
From RuntimeGrammar Require Import SemanticComparisonLaws.
Import ListNotations.

Module GeneratedComparisonFieldResults.

Definition fold_decisions := fold_right SemanticComparisonLaws.SemanticComparisonLaws.lex Eq.

Lemma fold_decisions_app : forall first rest,
  fold_decisions (first ++ rest) =
  SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions first) (fold_decisions rest).
Proof.
  intros first. induction first as [|head tail IH]; intro rest; [reflexivity|].
  change (SemanticComparisonLaws.SemanticComparisonLaws.lex head (fold_decisions (tail ++ rest)) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (SemanticComparisonLaws.SemanticComparisonLaws.lex head (fold_decisions tail)) (fold_decisions rest)).
  rewrite IH. destruct head; reflexivity.
Qed.

Lemma folding_completed_groups_preserves_field_priority : forall groups,
  fold_decisions (concat groups) = fold_decisions (map fold_decisions groups).
Proof.
  intro groups. induction groups as [|group rest IH]; [reflexivity|].
  change (fold_decisions (group ++ concat rest) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions group) (fold_decisions (map fold_decisions rest))).
  now rewrite fold_decisions_app, IH.
Qed.

(** Eq continues; a decisive result discards the unvisited suffix. The
    source's admitted delivery/publication gate remains separate. *)
Inductive Consultation : list comparison -> comparison -> Prop :=
| ConsultEmpty : Consultation [] Eq
| ConsultEqual : forall rest result, Consultation rest result -> Consultation (Eq :: rest) result
| ConsultDecisive : forall decision rest, decision <> Eq -> Consultation (decision :: rest) decision.

Theorem completed_consultation_returns_the_lexicographic_result : forall decisions result,
  Consultation decisions result -> result = fold_decisions decisions.
Proof.
  intros decisions result HC. induction HC.
  - reflexivity.
  - exact IHHC.
  - destruct decision; [contradiction|reflexivity|reflexivity].
Qed.

Theorem completed_consultation_is_determined : forall decisions first second,
  Consultation decisions first -> Consultation decisions second -> first = second.
Proof.
  intros decisions first second HF HS.
  rewrite (completed_consultation_returns_the_lexicographic_result _ _ HF),
    (completed_consultation_returns_the_lexicographic_result _ _ HS). reflexivity.
Qed.

Theorem equal_prefix_cannot_override_the_first_decisive_result : forall prefix decision suffix,
  Forall (fun item => item = Eq) prefix -> decision <> Eq ->
  Consultation (prefix ++ decision :: suffix) decision.
Proof.
  intros prefix decision suffix HP HD. induction HP.
  - now apply ConsultDecisive.
  - subst x. cbn [app]. now apply ConsultEqual.
Qed.

Section ExistingTasks.
Variable child : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position -> comparison.
Definition task_decision task := match task with
  | AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position => child position
  | AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict _ result => result
  end.
Definition task_results tasks := map task_decision tasks.
Definition group_results groups := map (fun group => fold_decisions (task_results group)) groups.
Definition pending_result stack := fold_decisions (task_results
  (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pop_order stack)).

Lemma task_group_expansion_preserves_lexicographic_result : forall groups,
  fold_decisions (task_results (concat groups)) = fold_decisions (group_results groups).
Proof.
  intro groups. induction groups as [|group rest IH]; [reflexivity|].
  change (fold_decisions (map task_decision (group ++ concat rest)) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (task_results group)) (fold_decisions (group_results rest))).
  rewrite map_app, fold_decisions_app. change (SemanticComparisonLaws.SemanticComparisonLaws.lex
    (fold_decisions (task_results group)) (fold_decisions (task_results (concat rest))) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (task_results group)) (fold_decisions (group_results rest))).
  now rewrite IH.
Qed.

Theorem reverse_pushed_groups_return_forward_field_priority : forall stack groups,
  pending_result (stack ++ AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.deferred_pushes groups) =
  SemanticComparisonLaws.SemanticComparisonLaws.lex
    (fold_decisions (group_results groups)) (pending_result stack).
Proof.
  intros stack groups. unfold pending_result.
  rewrite AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.reverse_task_groups_still_consult_forward.
  unfold task_results. rewrite map_app, fold_decisions_app.
  change (SemanticComparisonLaws.SemanticComparisonLaws.lex
    (fold_decisions (task_results (concat groups))) (pending_result stack) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (group_results groups)) (pending_result stack)).
  now rewrite task_group_expansion_preserves_lexicographic_result.
Qed.

Inductive ArmResult (eager : list comparison)
    (groups : list (list AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.BorrowedTask))
    (stack : list AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.BorrowedTask)
    : comparison -> Prop :=
| EagerDecisive : forall result,
    Consultation eager result -> result <> Eq -> ArmResult eager groups stack result
| EagerContinues : forall result,
    Consultation eager Eq ->
    Consultation (task_results (AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.pop_order
      (stack ++ AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.deferred_pushes groups))) result ->
    ArmResult eager groups stack result.

Theorem completed_arm_returns_eager_then_forward_fields_then_pending :
  forall eager groups stack result, ArmResult eager groups stack result ->
  result = SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions eager)
    (SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (group_results groups)) (pending_result stack)).
Proof.
  intros eager groups stack result HR. destruct HR as [result HE HD|result HE HC].
  - pose proof (completed_consultation_returns_the_lexicographic_result _ _ HE) as HF.
    rewrite <- HF. destruct result; [contradiction|reflexivity|reflexivity].
  - pose proof (completed_consultation_returns_the_lexicographic_result _ _ HE) as HF.
    rewrite <- HF. change (result = SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (group_results groups)) (pending_result stack)).
    rewrite <- reverse_pushed_groups_return_forward_field_priority.
    apply completed_consultation_returns_the_lexicographic_result. exact HC.
Qed.

Theorem completed_isolated_arm_returns_its_original_field_fold :
  forall eager groups result, ArmResult eager groups [] result ->
  result = fold_decisions (eager ++ task_results (concat groups)).
Proof.
  intros eager groups result HR.
  pose proof (completed_arm_returns_eager_then_forward_fields_then_pending _ _ _ _ HR) as HF.
  rewrite fold_decisions_app, task_group_expansion_preserves_lexicographic_result.
  change (result = SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions eager)
    (SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions (group_results groups)) Eq)) in HF.
  destruct (fold_decisions (group_results groups)); exact HF.
Qed.

Theorem completed_child_expansion_preserves_its_parent_pending_result :
  forall position eager groups remaining,
  ArmResult eager groups [] (child position) ->
  fold_decisions (task_results
    (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position :: remaining)) =
  fold_decisions ((eager ++ task_results (concat groups)) ++ task_results remaining).
Proof.
  intros position eager groups remaining HR.
  pose proof (completed_isolated_arm_returns_its_original_field_fold _ _ _ HR) as HF.
  change (SemanticComparisonLaws.SemanticComparisonLaws.lex (child position)
    (fold_decisions (task_results remaining)) =
    fold_decisions ((eager ++ task_results (concat groups)) ++ task_results remaining)).
  rewrite HF. symmetry. apply fold_decisions_app.
Qed.

Theorem vec_result_is_elements_then_length_then_pending : forall stack length_verdict elements,
  pending_result (stack ++ [length_verdict] ++ rev elements) =
  SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions (task_results elements))
    (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision length_verdict) (pending_result stack)).
Proof.
  intros stack length_verdict elements. unfold pending_result.
  rewrite AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.vec_length_verdict_is_consulted_after_elements.
  unfold task_results. rewrite map_app, fold_decisions_app. reflexivity.
Qed.

Theorem scope_result_is_prefields_then_pattern_then_body_then_pending :
  forall stack prefields pattern body,
  pending_result (stack ++ [body; pattern] ++
    AdmittedGeneratedHashScheduling.AdmittedGeneratedHashScheduling.deferred_pushes prefields) =
  SemanticComparisonLaws.SemanticComparisonLaws.lex (fold_decisions (group_results prefields))
    (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision pattern)
      (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision body) (pending_result stack))).
Proof.
  intros stack prefields pattern body. unfold pending_result.
  rewrite AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.scope_pattern_verdict_precedes_body_after_prefields.
  unfold task_results. rewrite map_app, fold_decisions_app.
  change (SemanticComparisonLaws.SemanticComparisonLaws.lex
    (fold_decisions (task_results (concat prefields)))
    (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision pattern)
      (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision body) (pending_result stack))) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (fold_decisions (group_results prefields))
      (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision pattern)
        (SemanticComparisonLaws.SemanticComparisonLaws.lex (task_decision body) (pending_result stack)))).
  now rewrite task_group_expansion_preserves_lexicographic_result.
Qed.

(** This root theorem is for a completed isolated arm. Internal collection
    continuations use their existing nearest-Resume boundary, not this root
    publication rule. On refusal the pre-existing publication is None. *)
Theorem successful_root_publication_has_the_proved_field_result :
  forall eager groups original events available published,
  ArmResult eager groups [] original ->
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.publication
    events (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.OrderingVerdict original)
    available = Some (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.OrderingVerdict published) ->
  published = fold_decisions (eager ++ task_results (concat groups)).
Proof.
  intros eager groups original events available published HR HP.
  apply AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.successful_publication_is_original in HP.
  destruct HP as [SUCCESS RESULT]. inversion RESULT; subst published.
  now apply completed_isolated_arm_returns_its_original_field_fold.
Qed.
End ExistingTasks.

Theorem later_precomputed_verdict_cannot_override_an_earlier_field :
  Consultation [Eq; Lt; Gt] Lt /\ fold_decisions [Eq; Lt; Gt] = Lt.
Proof. split; [apply ConsultEqual; apply ConsultDecisive; discriminate|reflexivity]. Qed.

Print Assumptions fold_decisions_app.
Print Assumptions folding_completed_groups_preserves_field_priority.
Print Assumptions completed_consultation_returns_the_lexicographic_result.
Print Assumptions completed_consultation_is_determined.
Print Assumptions equal_prefix_cannot_override_the_first_decisive_result.
Print Assumptions task_group_expansion_preserves_lexicographic_result.
Print Assumptions reverse_pushed_groups_return_forward_field_priority.
Print Assumptions completed_arm_returns_eager_then_forward_fields_then_pending.
Print Assumptions completed_isolated_arm_returns_its_original_field_fold.
Print Assumptions completed_child_expansion_preserves_its_parent_pending_result.
Print Assumptions vec_result_is_elements_then_length_then_pending.
Print Assumptions scope_result_is_prefields_then_pattern_then_body_then_pending.
Print Assumptions successful_root_publication_has_the_proved_field_result.
Print Assumptions later_precomputed_verdict_cannot_override_an_earlier_field.
End GeneratedComparisonFieldResults.
