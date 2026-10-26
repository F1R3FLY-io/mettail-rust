From Stdlib Require Import List Bool PeanoNat Lia.
Require Import RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyPremises RewriteFamilyBoundary.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization
  RewriteFamilyExtraction.RewriteFamilyExtraction RewriteFamilyPremises.RewriteFamilyPremises
  RewriteFamilyBoundary.RewriteFamilyBoundary.

Module RewriteFamilyAuthored.

Lemma occurrence_names_mutual :
  (forall shape path introduced,
    hole_names shape = map occurrence_family (occurrences shape path introduced)) /\
  (forall shapes path introduced index,
    hole_names_many shapes = map occurrence_family (occurrences_many shapes path introduced index)).
Proof.
  apply shape_mutual; intros; simpl; try reflexivity.
  - apply H.
  - apply H.
  - rewrite map_app. now rewrite <- H, <- H0.
Qed.

Theorem hole_names_are_exactly_checked_family_ids : forall shape,
  hole_names shape = family_ids shape.
Proof. intros. apply (proj1 occurrence_names_mutual). Qed.

Lemma checked_lookup_finds_an_occurrence : forall items family_id,
  In family_id (map occurrence_family items) ->
  exists item, find (fun item => Nat.eqb family_id (occurrence_family item)) items = Some item.
Proof.
  intros items family_id Hin.
  destruct (find (fun item => Nat.eqb family_id (occurrence_family item)) items) eqn:Hfind.
  - eauto.
  - apply in_map_iff in Hin. destruct Hin as [item [Hname Hin]].
    apply find_none with (x := item) in Hfind; [|assumption].
    rewrite Hname, Nat.eqb_refl in Hfind. discriminate.
Qed.

Lemma covered_declarations_build_requests : forall authored ambient declarations items,
  (forall family_id, In family_id (map fst declarations) ->
    In family_id (map occurrence_family items)) ->
  exists requests, build_requests authored ambient declarations items = Some requests.
Proof.
  intros authored ambient declarations. induction declarations as [|[family_id descriptor] rest IH];
    intros items Hcovered.
  - exists []. reflexivity.
  - destruct (checked_lookup_finds_an_occurrence items family_id) as [item Hitem].
    + apply Hcovered. simpl. auto.
    + destruct (IH items) as [requests Hrequests].
      * intros. apply Hcovered. simpl. auto.
      * exists (make_request authored ambient descriptor item :: requests).
        simpl. now rewrite Hitem, Hrequests.
Qed.

Theorem admitted_family_rules_always_build_requests :
  forall categories authored ambient declarations shape,
  shape_check categories declarations ambient shape = true ->
  exists requests, build_requests authored ambient declarations (occurrences shape [] []) = Some requests.
Proof.
  intros. apply covered_declarations_build_requests. intros.
  eapply accepted_shape_uses_every_declared_family; eauto.
Qed.

Theorem built_request_family_order_equals_declaration_order :
  forall authored ambient declarations items requests,
  build_requests authored ambient declarations items = Some requests ->
  map request_family requests = map fst declarations.
Proof.
  intros. apply built_requests_follow_declaration_order_and_scopes in H.
  induction H; [reflexivity|]. destruct H as [item [Hin [Hname ->]]].
  simpl. rewrite IHForall2. now rewrite Hname.
Qed.

Theorem built_requests_use_the_proved_name_allocator :
  forall authored ambient declarations items requests,
  build_requests authored ambient declarations items = Some requests ->
  Forall (fun item =>
    request_source item = source_name authored (request_family item) /\
    request_target item = target_name authored (request_family item)) requests.
Proof.
  intros. apply built_requests_follow_declaration_order_and_scopes in H.
  induction H; constructor; [|assumption].
  destruct H as [item [Hin [Hname ->]]]. split; reflexivity.
Qed.

Theorem built_request_sources_and_targets_are_disjoint :
  forall authored ambient declarations items requests,
  build_requests authored ambient declarations items = Some requests -> DisjointNames requests.
Proof.
  intros authored ambient declarations items requests Hbuild left right Hleft Hright.
  apply built_requests_use_the_proved_name_allocator in Hbuild. rewrite Forall_forall in Hbuild.
  destruct (Hbuild left Hleft) as [Hsource _]. destruct (Hbuild right Hright) as [_ Htarget].
  rewrite Hsource, Htarget. apply generated_source_and_target_names_are_disjoint.
Qed.

Theorem built_request_targets_are_unique :
  forall categories authored ambient declarations shape requests,
  shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  NoDup (map request_target requests).
Proof.
  intros categories authored ambient declarations shape requests Hchecked Hbuild.
  pose proof (built_request_family_order_equals_declaration_order _ _ _ _ _ Hbuild) as Horder.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  assert (Hmap : map request_target requests = map (target_name authored) (map request_family requests)).
  { clear - Hnames. induction Hnames; [reflexivity|].
    destruct H as [_ Htarget]. simpl. now rewrite Htarget, IHHnames. }
  rewrite Hmap, Horder. apply injective_map_preserves_distinctness.
  - intros left right. apply generated_target_names_are_injective.
  - eapply accepted_shape_has_unique_declarations; eauto.
Qed.

Definition source_overlay (prior : Environment) requests (sources : Environment) : Environment :=
  fun name =>
    match find (fun item => Nat.eqb name (request_source item)) requests with
    | Some item => sources (request_family item)
    | None => prior name
    end.

Theorem source_overlay_reads_the_declared_endpoint :
  forall authored ambient declarations items requests prior sources item,
  build_requests authored ambient declarations items = Some requests ->
  In item requests ->
  source_overlay prior requests sources (request_source item) = sources (request_family item).
Proof.
  intros authored ambient declarations items requests prior sources item Hbuild Hin.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames. unfold source_overlay.
  destruct (find (fun candidate => Nat.eqb (request_source item) (request_source candidate)) requests)
    as [found|] eqn:Hfind.
  - apply find_some in Hfind. destruct Hfind as [Hfound Hsame]. apply Nat.eqb_eq in Hsame.
    destruct (Hnames item Hin) as [Hitemsource _].
    destruct (Hnames found Hfound) as [Hfoundsource _].
    rewrite Hitemsource, Hfoundsource in Hsame.
    apply generated_source_names_are_injective in Hsame. now rewrite Hsame.
  - apply find_none with (x := item) in Hfind; [|assumption].
    now rewrite Nat.eqb_refl in Hfind.
Qed.

Theorem source_overlay_preserves_every_authored_binding :
  forall authored ambient declarations items requests prior sources name,
  build_requests authored ambient declarations items = Some requests ->
  In name authored -> source_overlay prior requests sources name = prior name.
Proof.
  intros authored ambient declarations items requests prior sources name Hbuild Hin.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames. unfold source_overlay.
  destruct (find (fun item => Nat.eqb name (request_source item)) requests) as [found|] eqn:Hfind;
    [|reflexivity].
  apply find_some in Hfind. destruct Hfind as [Hfound Hsame]. apply Nat.eqb_eq in Hsame.
  destruct (Hnames found Hfound) as [Hsource _]. rewrite Hsource in Hsame. subst name.
  exfalso. now apply (generated_source_avoids_authored_names authored (request_family found)).
Qed.

Theorem source_overlay_keeps_generated_targets_fresh :
  forall authored ambient declarations items requests prior sources family_id,
  build_requests authored ambient declarations items = Some requests -> SupportedBy authored prior ->
  source_overlay prior requests sources (target_name authored family_id) = None.
Proof.
  intros authored ambient declarations items requests prior sources family_id Hbuild Hsupport.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames. unfold source_overlay.
  destruct (find (fun item => Nat.eqb (target_name authored family_id) (request_source item)) requests)
    as [found|] eqn:Hfind.
  - apply find_some in Hfind. destruct Hfind as [Hfound Hsame]. apply Nat.eqb_eq in Hsame.
    destruct (Hnames found Hfound) as [Hsource _]. rewrite Hsource in Hsame.
    exfalso. apply (generated_source_and_target_names_are_disjoint authored (request_family found) family_id).
    now symmetry.
  - now apply (proj2 (generated_names_are_fresh_in_supported_environment authored prior family_id Hsupport)).
Qed.

Theorem source_overlay_satisfies_existing_premise_freshness :
  forall authored ambient declarations items requests prior sources,
  build_requests authored ambient declarations items = Some requests -> SupportedBy authored prior ->
  FreshTargets requests (source_overlay prior requests sources).
Proof.
  intros authored ambient declarations items requests prior sources Hbuild Hsupport item Hin.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames. destruct (Hnames item Hin) as [_ Htarget]. rewrite Htarget.
  eapply source_overlay_keeps_generated_targets_fresh; eauto.
Qed.

Fixpoint endpoint_by_ids ids (results : list (Value * Value)) (projection : Value * Value -> Value) family_id :=
  match ids, results with
  | head :: tail, values :: rest =>
      if Nat.eqb family_id head then Some (projection values)
      else endpoint_by_ids tail rest projection family_id
  | _, _ => None
  end.

Definition declared_endpoint declarations results projection :=
  endpoint_by_ids (map (@fst nat Family) declarations) results projection.

Lemma request_result_is_endpoint_by_family_ids : forall requests results family_id,
  result_endpoint requests results family_id =
    endpoint_by_ids (map request_family requests) results snd family_id.
Proof.
  induction requests as [|head tail IH]; intros results family_id; destruct results; simpl;
    try reflexivity.
  destruct (Nat.eqb family_id (request_family head)); [reflexivity|apply IH].
Qed.

Theorem declaration_endpoints_equal_constructed_request_endpoints :
  forall authored ambient declarations items requests results family_id,
  build_requests authored ambient declarations items = Some requests ->
  declared_endpoint declarations results snd family_id = result_endpoint requests results family_id.
Proof.
  intros. rewrite request_result_is_endpoint_by_family_ids.
  unfold declared_endpoint. now rewrite (built_request_family_order_equals_declaration_order _ _ _ _ _ H).
Qed.

Lemma unique_occurrence_ids_identify_the_same_occurrence : forall items left right,
  NoDup (map occurrence_family items) -> In left items -> In right items ->
  occurrence_family left = occurrence_family right -> left = right.
Proof.
  induction items as [|head tail IH]; intros left right Hdistinct Hleft Hright Hsame;
    [contradiction|].
  inversion Hdistinct; subst. destruct Hleft as [<-|Hleft]; destruct Hright as [<-|Hright].
  - reflexivity.
  - exfalso. match goal with Hnot : ~ In (occurrence_family head) (map occurrence_family tail) |- _ =>
      apply Hnot; rewrite Hsame; now apply in_map end.
  - exfalso. match goal with Hnot : ~ In (occurrence_family head) (map occurrence_family tail) |- _ =>
      apply Hnot; rewrite <- Hsame; now apply in_map end.
  - now apply IH.
Qed.

Definition DeclaredTransition (step : list Binding -> nat -> Value -> Value -> Prop)
    ambient items (declaration : nat * Family) (values : Value * Value) :=
  exists item,
    In item items /\ fst declaration = occurrence_family item /\
    step (ambient ++ occurrence_introduced item) (family_result (snd declaration))
      (fst values) (snd values).

Definition DeclaredTransitions step ambient items declarations results :=
  Forall2 (DeclaredTransition step ambient items) declarations results.

Lemma one_declared_transition_equals_its_constructed_request :
  forall step authored ambient items declaration result values,
  NoDup (map occurrence_family items) ->
  (exists item, In item items /\ fst declaration = occurrence_family item /\
    result = make_request authored ambient (snd declaration) item) ->
  (DeclaredTransition step ambient items declaration values <->
    step (request_scope result) (request_category result) (fst values) (snd values)).
Proof.
  intros step authored ambient items declaration result values Hdistinct
    [item [Hin [Hname ->]]]. split.
  - intros [other [Hother [Hothername Hstep]]].
    assert (Hequal : item = other).
    { eapply unique_occurrence_ids_identify_the_same_occurrence; eauto. congruence. }
    subst other. exact Hstep.
  - intros Hstep. exists item. auto.
Qed.

Theorem declaration_transitions_equal_constructed_request_transitions :
  forall categories step authored ambient declarations shape requests results,
  shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  (DeclaredTransitions step ambient (occurrences shape [] []) declarations results <->
    TransitionResults step requests results).
Proof.
  intros categories step authored ambient declarations shape requests results Hchecked Hbuild.
  pose proof (accepted_shape_has_unique_family_occurrences _ _ _ _ Hchecked) as Hdistinct.
  unfold family_ids in Hdistinct.
  apply built_requests_follow_declaration_order_and_scopes in Hbuild.
  clear Hchecked. revert results.
  induction Hbuild as [|declaration result declarations requests Hrelation Hrest IH]; intros results.
  - split; intros H; inversion H; constructor.
  - destruct results as [|values tail].
    + split; intros H; inversion H.
    + pose proof (one_declared_transition_equals_its_constructed_request step authored ambient
        (occurrences shape [] []) declaration result values Hdistinct Hrelation) as Hhead.
      split; intros H; inversion H; subst; constructor.
      * apply Hhead. assumption.
      * apply IH. assumption.
      * apply Hhead. assumption.
      * apply IH. assumption.
Qed.

Lemma instantiation_agreement_mutual :
  (forall shape ordinary first second,
    (forall family_id, In family_id (hole_names shape) -> first family_id = second family_id) ->
    instantiate ordinary first shape = instantiate ordinary second shape) /\
  (forall shapes ordinary first second,
    (forall family_id, In family_id (hole_names_many shapes) -> first family_id = second family_id) ->
    instantiates ordinary first shapes = instantiates ordinary second shapes).
Proof.
  apply shape_mutual; intros; simpl in *; try reflexivity.
  - now rewrite H with (second := second).
  - now rewrite H with (second := second).
  - apply H. auto.
  - rewrite H with (second := second), H0 with (second := second); try reflexivity;
      intros; apply H1; apply in_or_app; auto.
Qed.

Lemma family_endpoint_at_pair : forall ids results projection family_id values,
  NoDup ids -> In (family_id, values) (combine ids results) ->
  endpoint_by_ids ids results projection family_id = Some (projection values).
Proof.
  induction ids as [|head tail IH]; intros results projection family_id values Hdistinct Hin;
    destruct results as [|first rest]; simpl in Hin; try contradiction.
  inversion Hdistinct; subst. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. simpl. now rewrite Nat.eqb_refl.
  - simpl. destruct (Nat.eqb family_id head) eqn:Hsame.
    + apply Nat.eqb_eq in Hsame. subst family_id. exfalso.
      match goal with Hnot : ~ In head tail |- _ => apply Hnot end.
      now apply in_combine_l in Hin.
    + now apply IH.
Qed.

Lemma forall2_from_pair_membership : forall (A B : Type) (relation : A -> B -> Prop) left right,
  length left = length right ->
  (forall x y, In (x, y) (combine left right) -> relation x y) -> Forall2 relation left right.
Proof.
  intros A B relation left. induction left as [|head tail IH]; intros right Hlength Hmembers;
    destruct right as [|value rest]; simpl in Hlength; try discriminate; constructor.
  - apply Hmembers. simpl. auto.
  - apply IH; [lia|]. intros. apply Hmembers. simpl. auto.
Qed.

Lemma pair_membership_maps_request_ids : forall requests (results : list (Value * Value)) item values,
  In (item, values) (combine requests results) ->
  In (request_family item, values) (combine (map request_family requests) results).
Proof.
  induction requests as [|head tail IH]; intros results item values Hin;
    destruct results; simpl in *; try contradiction.
  destruct Hin as [Heq|Hin]; [inversion Heq; subst; now left|right; now apply IH].
Qed.

Lemma declared_results_bind_every_source :
  forall categories authored ambient declarations shape requests results prior,
  shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  length declarations = length results ->
  BoundSources requests results
    (source_overlay prior requests (declared_endpoint declarations results fst)).
Proof.
  intros categories authored ambient declarations shape requests results prior Hchecked Hbuild Hlength.
  pose proof (built_request_family_order_equals_declaration_order _ _ _ _ _ Hbuild) as Horder.
  unfold BoundSources. apply forall2_from_pair_membership.
  - apply (f_equal (@length nat)) in Horder. rewrite !length_map in Horder. lia.
  - intros item values Hin.
    rewrite source_overlay_reads_the_declared_endpoint with
      (authored := authored) (ambient := ambient) (declarations := declarations)
      (items := occurrences shape [] []); [|exact Hbuild|now apply in_combine_l in Hin].
    unfold declared_endpoint. rewrite <- Horder. apply family_endpoint_at_pair.
    + rewrite Horder. eapply accepted_shape_has_unique_declarations; eauto.
    + now apply pair_membership_maps_request_ids.
Qed.

Lemma bound_sources_determine_source_endpoints :
  forall requests results initial names family_id,
  BoundSources requests results initial ->
  (forall item, In item requests -> request_source item = names (request_family item)) ->
  In family_id (map request_family requests) ->
  endpoint_by_ids (map request_family requests) results fst family_id = initial (names family_id).
Proof.
  intros requests results initial names family_id Hbound.
  induction Hbound as [|item values requests results Hlookup Htail IH]; intros Hnames Hin;
    [contradiction|].
  simpl. destruct (Nat.eqb family_id (request_family item)) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. subst family_id.
    rewrite <- (Hnames item (or_introl eq_refl)). now symmetry.
  - apply IH.
    + intros. apply Hnames. now right.
    + simpl in Hin. destruct Hin as [Heq|Hin]; [subst; rewrite Nat.eqb_refl in Hsame; discriminate|assumption].
Qed.

Lemma overlay_reads_each_family_source :
  forall authored ambient declarations items requests prior sources family_id,
  build_requests authored ambient declarations items = Some requests ->
  In family_id (map request_family requests) ->
  source_overlay prior requests sources (source_name authored family_id) = sources family_id.
Proof.
  intros authored ambient declarations items requests prior sources family_id Hbuild Hin.
  apply in_map_iff in Hin. destruct Hin as [item [<- Hin]].
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames. destruct (Hnames item Hin) as [Hsource _]. rewrite <- Hsource.
  eapply source_overlay_reads_the_declared_endpoint; eauto.
Qed.

Definition AuthoredParentStep step ambient declarations shape prior left right input output :=
  exists results,
    DeclaredTransitions step ambient (occurrences shape [] []) declarations results /\
    interpret prior (declared_endpoint declarations results fst)
      (declared_endpoint declarations results snd) left = Some input /\
    interpret prior (declared_endpoint declarations results fst)
      (declared_endpoint declarations results snd) right = Some output.

Theorem authored_family_steps_iff_existing_core_rules :
  forall categories step authored ambient declarations shape prior left right requests input output,
  extract_pair left right = Some shape ->
  shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  SupportedBy authored prior ->
  (forall name, In name (ordinary_names shape) -> In name authored) ->
  (AuthoredParentStep step ambient declarations shape prior left right input output <->
    exists sources,
      CoreParentStep step requests shape (source_name authored) (target_name authored)
        (source_overlay prior requests sources) input output).
Proof.
  intros categories step authored ambient declarations shape prior left right requests input output
    Hextract Hchecked Hbuild Hsupport Hauthored.
  pose proof (built_request_family_order_equals_declaration_order _ _ _ _ _ Hbuild) as Horder.
  pose proof (built_requests_use_the_proved_name_allocator _ _ _ _ _ Hbuild) as Hnames.
  rewrite Forall_forall in Hnames.
  assert (Hcoverage : forall family_id, In family_id (hole_names shape) ->
    In family_id (map request_family requests)).
  { intros family_id Hin. rewrite Horder. eapply accepted_shape_has_no_undeclared_family; eauto.
    now rewrite <- hole_names_are_exactly_checked_family_ids. }
  assert (Hcore : forall sources,
    SourceParentStep step requests shape (source_name authored) prior
      (source_overlay prior requests sources) input output <->
    CoreParentStep step requests shape (source_name authored) (target_name authored)
      (source_overlay prior requests sources) input output).
  { intros sources. apply finite_families_reconstruct_one_parent_step.
    - eapply built_request_targets_are_unique; eauto.
    - eapply built_request_sources_and_targets_are_disjoint; eauto.
    - eapply source_overlay_satisfies_existing_premise_freshness; eauto.
    - intros item Hin. exact (proj2 (Hnames item Hin)).
    - exact Hcoverage.
    - intros name Hin. eapply source_overlay_preserves_every_authored_binding; eauto.
    - intros name Hin Htarget. apply in_map_iff in Htarget.
      destruct Htarget as [item [<- Hitem]]. destruct (Hnames item Hitem) as [_ Hname].
      rewrite Hname in Hin.
      apply (generated_target_avoids_authored_names authored (request_family item)). now apply Hauthored. }
  apply extraction_exactly_preserves_both_authored_sides in Hextract as [Hleft Hright].
  subst left right. split.
  - intros [results [Htransitions [Hinput Houtput]]].
    exists (declared_endpoint declarations results fst). apply Hcore.
    exists results. split.
    + eapply declaration_transitions_equal_constructed_request_transitions; eauto.
    + split.
      * eapply declared_results_bind_every_source; eauto. now apply Forall2_length in Htransitions.
      * split.
        -- rewrite (proj1 interpretation_of_rendering_mutual) in Hinput.
           rewrite (proj1 instantiation_agreement_mutual) with
             (second := declared_endpoint declarations results fst).
           ++ exact Hinput.
           ++ intros. eapply overlay_reads_each_family_source; eauto.
        -- rewrite (proj1 interpretation_of_rendering_mutual) in Houtput.
           rewrite (proj1 instantiation_agreement_mutual) with
             (second := declared_endpoint declarations results snd).
           ++ exact Houtput.
           ++ intros. symmetry. eapply declaration_endpoints_equal_constructed_request_endpoints; eauto.
  - intros [sources Hrun]. apply Hcore in Hrun.
    destruct Hrun as [results [Htransitions [Hbound [Hinput Houtput]]]].
    exists results. split.
    + eapply declaration_transitions_equal_constructed_request_transitions; eauto.
    + split; rewrite (proj1 interpretation_of_rendering_mutual).
      * rewrite (proj1 instantiation_agreement_mutual) with
          (second := fun family_id => source_overlay prior requests sources (source_name authored family_id)).
        -- exact Hinput.
        -- intros family_id Hin. unfold declared_endpoint. rewrite <- Horder.
           apply bound_sources_determine_source_endpoints; auto.
           intros item Hitem. exact (proj1 (Hnames item Hitem)).
      * rewrite (proj1 instantiation_agreement_mutual) with
          (second := result_endpoint requests results).
        -- exact Houtput.
        -- intros. eapply declaration_endpoints_equal_constructed_request_endpoints; eauto.
Qed.

End RewriteFamilyAuthored.

Print Assumptions RewriteFamilyAuthored.hole_names_are_exactly_checked_family_ids.
Print Assumptions RewriteFamilyAuthored.admitted_family_rules_always_build_requests.
Print Assumptions RewriteFamilyAuthored.built_request_family_order_equals_declaration_order.
Print Assumptions RewriteFamilyAuthored.built_requests_use_the_proved_name_allocator.
Print Assumptions RewriteFamilyAuthored.built_request_sources_and_targets_are_disjoint.
Print Assumptions RewriteFamilyAuthored.built_request_targets_are_unique.
Print Assumptions RewriteFamilyAuthored.source_overlay_reads_the_declared_endpoint.
Print Assumptions RewriteFamilyAuthored.source_overlay_preserves_every_authored_binding.
Print Assumptions RewriteFamilyAuthored.source_overlay_keeps_generated_targets_fresh.
Print Assumptions RewriteFamilyAuthored.source_overlay_satisfies_existing_premise_freshness.
Print Assumptions RewriteFamilyAuthored.declaration_endpoints_equal_constructed_request_endpoints.
Print Assumptions RewriteFamilyAuthored.declaration_transitions_equal_constructed_request_transitions.
Print Assumptions RewriteFamilyAuthored.authored_family_steps_iff_existing_core_rules.
