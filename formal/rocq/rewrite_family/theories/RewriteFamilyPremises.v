From Stdlib Require Import List Bool PeanoNat Lia.
Require Import RewriteFamilyNormalization RewriteFamilyExtraction.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization
  RewriteFamilyExtraction.RewriteFamilyExtraction.

Module RewriteFamilyPremises.

Record Request := request {
  request_family : nat;
  request_scope : list Binding;
  request_category : nat;
  request_source : nat;
  request_target : nat
}.

Inductive RunPremises (step : list Binding -> nat -> Value -> Value -> Prop) :
    list Request -> Environment -> Environment -> Prop :=
| run_empty : forall environment, RunPremises step [] environment environment
| run_cons : forall head tail initial middle final,
    PremiseExecution step (request_scope head) (request_category head)
      (request_source head) (request_target head) initial middle ->
    RunPremises step tail middle final ->
    RunPremises step (head :: tail) initial final.

Definition TransitionResults (step : list Binding -> nat -> Value -> Value -> Prop)
    requests (results : list (Value * Value)) :=
  Forall2 (fun item values =>
    step (request_scope item) (request_category item) (fst values) (snd values))
    requests results.

Definition BoundSources requests (results : list (Value * Value)) (environment : Environment) :=
  Forall2 (fun item values => environment (request_source item) = Some (fst values))
    requests results.

Definition FreshTargets requests (environment : Environment) :=
  forall item, In item requests -> environment (request_target item) = None.

Definition DisjointNames requests :=
  forall left right, In left requests -> In right requests ->
    request_source left <> request_target right.

Fixpoint write_results requests (results : list (Value * Value)) (environment : Environment) :=
  match requests, results with
  | head :: tail, (_, target) :: rest =>
      write_results tail rest (write_binding environment (request_target head) target)
  | _, _ => environment
  end.

Lemma disjoint_names_tail : forall head tail,
  DisjointNames (head :: tail) -> DisjointNames tail.
Proof. unfold DisjointNames. intros. apply H; now right. Qed.

Lemma sources_survive_target_write : forall requests results environment name value,
  (forall item, In item requests -> request_source item <> name) ->
  BoundSources requests results environment ->
  BoundSources requests results (write_binding environment name value).
Proof.
  intros requests results environment name value Hdisjoint Hbound.
  induction Hbound; constructor.
  - rewrite fresh_extension_preserves_other_bindings; [assumption|apply Hdisjoint; now left].
  - apply IHHbound. intros. apply Hdisjoint. now right.
Qed.

Lemma sources_before_target_write : forall requests results environment name value,
  (forall item, In item requests -> request_source item <> name) ->
  BoundSources requests results (write_binding environment name value) ->
  BoundSources requests results environment.
Proof.
  intros requests results. revert requests.
  induction results as [|values rest IH]; intros requests environment name value Hdisjoint Hbound.
  - inversion Hbound. constructor.
  - inversion Hbound; subst. constructor.
    + match goal with Hlookup : write_binding _ _ _ _ = _ |- _ =>
        rewrite fresh_extension_preserves_other_bindings in Hlookup;
        [exact Hlookup|apply Hdisjoint; now left] end.
    + eapply IH; [|eassumption]. intros. apply Hdisjoint. now right.
Qed.

Theorem independent_transitions_execute_in_premise_order :
  forall step requests results initial,
  NoDup (map request_target requests) -> DisjointNames requests ->
  FreshTargets requests initial ->
  TransitionResults step requests results -> BoundSources requests results initial ->
  RunPremises step requests initial (write_results requests results initial).
Proof.
  intros step requests results initial Hdistinct Hdisjoint Hfresh Hsteps.
  revert initial Hdistinct Hdisjoint Hfresh.
  induction Hsteps as [|head values tail rest Hstep Hsteps IH];
    intros initial Hdistinct Hdisjoint Hfresh Hsources.
  - constructor.
  - destruct values as [source target].
    inversion Hsources; subst. inversion Hdistinct; subst. simpl.
    econstructor.
    + econstructor; [eassumption|apply Hfresh; now left|exact Hstep].
    + apply IH.
      * assumption.
      * now apply disjoint_names_tail with head.
      * intros item Hin. rewrite fresh_extension_preserves_other_bindings.
        -- apply Hfresh. now right.
        -- intros Heq.
           match goal with Hnot : ~ In (request_target head) (map request_target tail) |- _ =>
             apply Hnot; rewrite <- Heq; now apply in_map end.
      * apply sources_survive_target_write; [|eassumption].
        intros. apply Hdisjoint; [now right|now left].
Qed.

Theorem ordered_premises_have_independent_transition_results :
  forall step requests initial final,
  DisjointNames requests -> RunPremises step requests initial final ->
  exists results,
    TransitionResults step requests results /\ BoundSources requests results initial /\
    final = write_results requests results initial.
Proof.
  intros step requests initial final Hdisjoint Hrun.
  induction Hrun as [environment|head tail initial middle final Hpremise Htail IH].
  - exists []. repeat split; constructor.
  - inversion Hpremise; subst.
    destruct (IH (disjoint_names_tail _ _ Hdisjoint)) as [rest [Hsteps [Hsources Hfinal]]].
    exists ((source, target) :: rest). split.
    + constructor; assumption.
    + split.
      * constructor; [assumption|].
        eapply sources_before_target_write; [|exact Hsources].
        intros. apply Hdisjoint; [now right|now left].
      * exact Hfinal.
Qed.

Theorem finite_family_steps_iff_ordered_existing_premises :
  forall step requests initial final,
  NoDup (map request_target requests) -> DisjointNames requests -> FreshTargets requests initial ->
  (RunPremises step requests initial final <->
    exists results,
      TransitionResults step requests results /\ BoundSources requests results initial /\
      final = write_results requests results initial).
Proof.
  intros. split.
  - now apply ordered_premises_have_independent_transition_results.
  - intros [results [Hsteps [Hsources ->]]].
    now apply independent_transitions_execute_in_premise_order.
Qed.

Theorem ordered_premises_preserve_non_target_bindings :
  forall step requests initial final name,
  RunPremises step requests initial final ->
  ~ In name (map request_target requests) -> final name = initial name.
Proof.
  intros step requests initial final name Hrun.
  induction Hrun; intros Hnot; [reflexivity|].
  rewrite IHHrun.
  - eapply transition_premise_preserves_metavariable_bindings; [exact H|].
    intros ->. apply Hnot. simpl. auto.
  - intros Hin. apply Hnot. simpl. auto.
Qed.

Theorem two_premises_remain_two_ordered_child_transitions :
  forall step first second initial final,
  RunPremises step [first; second] initial final ->
  exists middle,
    PremiseExecution step (request_scope first) (request_category first)
      (request_source first) (request_target first) initial middle /\
    PremiseExecution step (request_scope second) (request_category second)
      (request_source second) (request_target second) middle final.
Proof.
  intros. inversion H; subst.
  match goal with Htail : RunPremises _ [_] _ _ |- _ => inversion Htail; subst end.
  match goal with Hempty : RunPremises _ [] _ _ |- _ => inversion Hempty; subst end.
  eauto.
Qed.

Fixpoint result_endpoint requests (results : list (Value * Value)) family_id :=
  match requests, results with
  | head :: tail, values :: rest =>
      if Nat.eqb family_id (request_family head)
      then Some (snd values) else result_endpoint tail rest family_id
  | _, _ => None
  end.

Lemma result_writes_preserve_non_targets : forall requests results environment name,
  ~ In name (map request_target requests) ->
  write_results requests results environment name = environment name.
Proof.
  induction requests as [|head tail IH]; intros results environment name Hnot; [reflexivity|].
  destruct results as [|[source target] rest]; [reflexivity|]. simpl.
  rewrite IH.
  - apply fresh_extension_preserves_other_bindings. intros ->. apply Hnot. simpl. auto.
  - intros Hin. apply Hnot. simpl. auto.
Qed.

Lemma result_write_reads_family_endpoint :
  forall requests results environment names family_id,
  length requests = length results ->
  NoDup (map request_target requests) ->
  (forall item, In item requests -> request_target item = names (request_family item)) ->
  In family_id (map request_family requests) ->
  write_results requests results environment (names family_id) =
    result_endpoint requests results family_id.
Proof.
  induction requests as [|head tail IH]; intros results environment names family_id
    Hlength Hdistinct Hnames Hin; [contradiction|].
  destruct results as [|[source target] rest]; simpl in Hlength; [discriminate|].
  inversion Hdistinct; subst. simpl in Hin. simpl.
  destruct (Nat.eqb family_id (request_family head)) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. subst family_id.
    rewrite <- (Hnames head (or_introl eq_refl)).
    rewrite result_writes_preserve_non_targets; [apply write_binding_reads_exact_value|assumption].
  - apply IH; [lia|assumption| |].
    + intros. apply Hnames. now right.
    + destruct Hin as [Heq|Hin]; [subst; rewrite Nat.eqb_refl in Hsame; discriminate|assumption].
Qed.

Definition SourceParentStep step requests shape source_names ordinary initial input output :=
  exists results,
    TransitionResults step requests results /\ BoundSources requests results initial /\
    instantiate ordinary (fun family_id => initial (source_names family_id)) shape = Some input /\
    instantiate ordinary (result_endpoint requests results) shape = Some output.

Definition CoreParentStep step requests shape source_names target_names initial input output :=
  exists final,
    CoreMatches initial (lower source_names shape) input /\
    RunPremises step requests initial final /\
    instantiate final (fun _ => None) (lower target_names shape) = Some output.

Theorem finite_families_reconstruct_one_parent_step :
  forall step requests shape source_names target_names ordinary initial input output,
  NoDup (map request_target requests) -> DisjointNames requests -> FreshTargets requests initial ->
  (forall item, In item requests -> request_target item = target_names (request_family item)) ->
  (forall family_id, In family_id (hole_names shape) -> In family_id (map request_family requests)) ->
  (forall name, In name (ordinary_names shape) -> initial name = ordinary name) ->
  (forall name, In name (ordinary_names shape) -> ~ In name (map request_target requests)) ->
  (SourceParentStep step requests shape source_names ordinary initial input output <->
    CoreParentStep step requests shape source_names target_names initial input output).
Proof.
  intros step requests shape source_names target_names ordinary initial input output
    Hdistinct Hdisjoint Hfresh Htargetnames Hfamilies Hordinary Hordinaryfresh.
  assert (Hmatch : CoreMatches initial (lower source_names shape) input <->
    instantiate ordinary (fun family_id => initial (source_names family_id)) shape = Some input).
  { apply lowered_matching_extracts_exact_family_endpoints; auto. }
  split.
  - intros [results [Hsteps [Hsources [Hinput Houtput]]]].
    exists (write_results requests results initial). split; [now apply Hmatch|].
    split.
    + now apply independent_transitions_execute_in_premise_order.
    + rewrite lowering_preserves_instantiation with
        (ordinary := ordinary) (endpoints := result_endpoint requests results).
      * exact Houtput.
      * intros. rewrite result_writes_preserve_non_targets; auto.
      * intros. apply result_write_reads_family_endpoint; auto.
        now apply Forall2_length in Hsteps.
  - intros [final [Hinput [Hrun Houtput]]].
    destruct (ordered_premises_have_independent_transition_results _ _ _ _ Hdisjoint Hrun)
      as [results [Hsteps [Hsources Hfinal]]].
    exists results. split; [exact Hsteps|]. split; [exact Hsources|].
    split; [now apply Hmatch|]. subst final.
    rewrite lowering_preserves_instantiation with
      (ordinary := ordinary) (endpoints := result_endpoint requests results) in Houtput.
    + exact Houtput.
    + intros. rewrite result_writes_preserve_non_targets; auto.
    + intros. apply result_write_reads_family_endpoint; auto.
      now apply Forall2_length in Hsteps.
Qed.

Definition make_request authored ambient descriptor item :=
  request (occurrence_family item) (ambient ++ occurrence_introduced item)
    (family_result descriptor) (source_name authored (occurrence_family item))
    (target_name authored (occurrence_family item)).

Fixpoint build_requests authored ambient declarations items : option (list Request) :=
  match declarations with
  | [] => Some []
  | (family_id, descriptor) :: rest =>
      match find (fun item => Nat.eqb family_id (occurrence_family item)) items,
        build_requests authored ambient rest items with
      | Some item, Some requests => Some (make_request authored ambient descriptor item :: requests)
      | _, _ => None
      end
  end.

Theorem built_requests_follow_declaration_order_and_scopes :
  forall authored ambient declarations items requests,
  build_requests authored ambient declarations items = Some requests ->
  Forall2 (fun declaration result =>
    exists item,
      In item items /\ fst declaration = occurrence_family item /\
      result = make_request authored ambient (snd declaration) item)
    declarations requests.
Proof.
  intros authored ambient declarations. induction declarations as [|[family_id descriptor] rest IH];
    intros items requests Hbuild; simpl in Hbuild.
  - inversion Hbuild. constructor.
  - destruct (find (fun item => Nat.eqb family_id (occurrence_family item)) items) eqn:Hfind;
      [|discriminate].
    destruct (build_requests authored ambient rest items) eqn:Hrest; inversion Hbuild; subst.
    constructor.
    + exists o. apply find_some in Hfind. destruct Hfind as [Hin Hname].
      apply Nat.eqb_eq in Hname. auto.
    + now apply IH.
Qed.

Theorem built_requests_use_checked_occurrence_scopes :
  forall categories authored declarations ambient shape requests item,
  shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  In item requests ->
  exists occurrence descriptor,
    In occurrence (occurrences shape [] []) /\
    In (occurrence_family occurrence, descriptor) declarations /\
    FamilyWellTyped categories descriptor ambient
      (occurrence_introduced occurrence) (occurrence_arguments occurrence) /\
    item = make_request authored ambient descriptor occurrence.
Proof.
  intros categories authored declarations ambient shape requests item Hchecked Hbuild Hin.
  apply built_requests_follow_declaration_order_and_scopes in Hbuild.
  assert (Hpair : exists declaration,
    In declaration declarations /\
    exists occurrence,
      In occurrence (occurrences shape [] []) /\ fst declaration = occurrence_family occurrence /\
      item = make_request authored ambient (snd declaration) occurrence).
  { clear Hchecked. induction Hbuild as [|x y xs ys Hrelation Htail IH].
    - contradiction.
    - destruct Hin as [Heq|Hin].
      + subst item. exists x. split; [now left|exact Hrelation].
      + destruct (IH Hin) as [declaration [Hmember Hrelated]].
        exists declaration. split; [now right|exact Hrelated]. }
  destruct Hpair as [[family_id descriptor] [Hdeclared [occurrence [Hocc [Hname Hitem]]]]].
  simpl in Hname, Hitem. subst family_id.
  destruct (accepted_occurrence_has_exact_scoped_family _ _ _ _ _ Hchecked Hocc)
    as [actual [Hlookup [Hactual Htyped]]].
  assert (Hunique : NoDup (map fst declarations)).
  { eapply accepted_shape_has_unique_declarations; eauto. }
  assert (Hequal : descriptor = actual).
  { clear - Hdeclared Hactual Hunique.
    induction declarations as [|[name value] rest IH]; [contradiction|].
    inversion Hunique; subst. destruct Hdeclared as [Heq|Hdeclared];
      destruct Hactual as [Hother|Hactual].
    - congruence.
    - inversion Heq; subst. exfalso.
      match goal with Hnot : ~ In _ (map fst rest) |- _ =>
        apply Hnot; apply in_map with (f := @fst nat Family) in Hactual; exact Hactual end.
    - inversion Hother; subst. exfalso.
      match goal with Hnot : ~ In _ (map fst rest) |- _ =>
        apply Hnot; apply in_map with (f := @fst nat Family) in Hdeclared; exact Hdeclared end.
    - now apply IH. }
  subst actual. exists occurrence, descriptor. auto.
Qed.

End RewriteFamilyPremises.

Print Assumptions RewriteFamilyPremises.independent_transitions_execute_in_premise_order.
Print Assumptions RewriteFamilyPremises.ordered_premises_have_independent_transition_results.
Print Assumptions RewriteFamilyPremises.finite_family_steps_iff_ordered_existing_premises.
Print Assumptions RewriteFamilyPremises.ordered_premises_preserve_non_target_bindings.
Print Assumptions RewriteFamilyPremises.two_premises_remain_two_ordered_child_transitions.
Print Assumptions RewriteFamilyPremises.finite_families_reconstruct_one_parent_step.
Print Assumptions RewriteFamilyPremises.built_requests_follow_declaration_order_and_scopes.
Print Assumptions RewriteFamilyPremises.built_requests_use_checked_occurrence_scopes.
