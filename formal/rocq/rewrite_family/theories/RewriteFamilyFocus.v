From Stdlib Require Import List Bool PeanoNat Lia.
Require Import RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyPremises RewriteFamilyBoundary RewriteFamilyAuthored.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization
  RewriteFamilyExtraction.RewriteFamilyExtraction RewriteFamilyPremises.RewriteFamilyPremises
  RewriteFamilyBoundary.RewriteFamilyBoundary RewriteFamilyAuthored.RewriteFamilyAuthored.

Module RewriteFamilyFocus.

Theorem value_sort_is_unique : forall signature literal_types scope value first second,
  TypedValue signature literal_types scope value first ->
  TypedValue signature literal_types scope value second -> first = second.
Proof.
  intros signature literal_types scope value first second Hfirst. revert second.
  induction Hfirst; intros second Hsecond; inversion Hsecond; subst; try congruence.
  f_equal. eauto.
Qed.

Theorem typed_plugging_decomposes_into_context_and_endpoint :
  forall context signature literal_types scope endpoint result,
  TypedValue signature literal_types scope (plug context endpoint) result ->
  exists hole_sort,
    TypedContext signature literal_types scope hole_sort context result /\
    TypedValue signature literal_types (scope ++ introduced_scope context) endpoint hole_sort.
Proof.
  induction context as [|label before inside IH after|binders inside IH];
    intros signature literal_types scope endpoint result Htyped; simpl in Htyped.
  - exists result. split; [constructor|now rewrite app_nil_r].
  - inversion Htyped; subst.
    match goal with Hchildren : Forall2 _ (before ++ _ :: after) _ |- _ =>
      apply Forall2_app_inv_l in Hchildren;
      destruct Hchildren as [before_sorts [remainder [Hbefore [Hrest Heq]]]];
      inversion Hrest; subst end.
    match goal with Hinside : TypedValue _ _ _ (plug inside endpoint) _ |- _ =>
      apply IH in Hinside; destruct Hinside as [hole_sort [Hcontext Hendpoint]] end.
    exists hole_sort. split; [econstructor; eassumption|exact Hendpoint].
  - inversion Htyped; subst.
    match goal with Hinside : TypedValue _ _ _ (plug inside endpoint) _ |- _ =>
      apply IH in Hinside; destruct Hinside as [hole_sort [Hcontext Hendpoint]] end.
    exists hole_sort. split; [econstructor; eassumption|].
    simpl. now rewrite app_assoc.
Qed.

Theorem typed_child_step_preserves_parent_sort :
  forall signature literal_types scope context source target category result step,
  TypedValue signature literal_types scope (plug context source) result ->
  OpenStep signature literal_types step (scope ++ introduced_scope context) category source target ->
  TypedValue signature literal_types scope (plug context target) result.
Proof.
  intros signature literal_types scope context source target category result step Hparent
    [Hsource [Hstep Htarget]].
  apply typed_plugging_decomposes_into_context_and_endpoint in Hparent.
  destruct Hparent as [hole_sort [Hcontext Hendpoint]].
  assert (Hsort : hole_sort = Category category).
  { eapply value_sort_is_unique; eauto. }
  subst hole_sort. eapply typed_context_plugging_preserves_endpoint_type; eauto.
Qed.

Record Location := location {
  location_family : nat;
  location_arguments : list Binding;
  location_scope : list Binding
}.

Definition extend_location binders item :=
  location (location_family item) (location_arguments item) (binders ++ location_scope item).

Fixpoint locate (shape : Shape) (path : list nat) : option Location :=
  match shape, path with
  | QHole family_id arguments, [] => Some (location family_id arguments [])
  | QNode _ children, index :: rest => locate_many children index rest
  | QBind binders body, 0 :: rest => option_map (extend_location binders) (locate body rest)
  | _, _ => None
  end
with locate_many (shapes : Shapes) (index : nat) (path : list nat) : option Location :=
  match shapes, index with
  | QMore head _, 0 => locate head path
  | QMore _ tail, S remaining => locate_many tail remaining path
  | _, _ => None
  end.

Fixpoint focus (ordinary endpoints : Environment) (shape : Shape) (path : list nat) : option Context :=
  match shape, path with
  | QHole _ _, [] => Some Hole
  | QNode label children, index :: rest =>
      match focus_many ordinary endpoints children index rest with
      | Some (before, inside, after) => Some (NodeContext label before inside after)
      | None => None
      end
  | QBind binders body, 0 :: rest => option_map (BinderContext binders) (focus ordinary endpoints body rest)
  | _, _ => None
  end
with focus_many (ordinary endpoints : Environment) (shapes : Shapes) (index : nat) (path : list nat) :
    option (list Value * Context * list Value) :=
  match shapes, index with
  | QMore head tail, 0 =>
      match focus ordinary endpoints head path, instantiates ordinary endpoints tail with
      | Some inside, Some after => Some ([], inside, after)
      | _, _ => None
      end
  | QMore head tail, S remaining =>
      match instantiate ordinary endpoints head, focus_many ordinary endpoints tail remaining path with
      | Some before, Some (prefix, inside, after) => Some (before :: prefix, inside, after)
      | _, _ => None
      end
  | _, _ => None
  end.

Lemma focus_reconstructs_mutual :
  (forall shape ordinary endpoints path context item endpoint,
    locate shape path = Some item ->
    focus ordinary endpoints shape path = Some context ->
    endpoints (location_family item) = Some endpoint ->
    instantiate ordinary endpoints shape = Some (plug context endpoint) /\
    introduced_scope context = location_scope item) /\
  (forall shapes ordinary endpoints index path before context after item endpoint,
    locate_many shapes index path = Some item ->
    focus_many ordinary endpoints shapes index path = Some (before, context, after) ->
    endpoints (location_family item) = Some endpoint ->
    instantiates ordinary endpoints shapes = Some (before ++ plug context endpoint :: after) /\
    introduced_scope context = location_scope item).
Proof.
  apply shape_mutual.
  - intros name ordinary endpoints path context item endpoint Hloc. destruct path; discriminate.
  - intros reference ordinary endpoints path context item endpoint Hloc. destruct path; discriminate.
  - intros label children IH ordinary endpoints path context item endpoint Hloc Hfocus Hvalue.
    destruct path as [|index rest]; [discriminate|]. simpl in Hloc, Hfocus.
    destruct (focus_many ordinary endpoints children index rest) as [[[before inside] after]|] eqn:Hchildren;
      inversion Hfocus; subst.
    destruct (IH _ _ _ _ _ _ _ _ _ Hloc Hchildren Hvalue) as [Hvalues Hscope].
    simpl. split; [now rewrite Hvalues|exact Hscope].
  - intros binders body IH ordinary endpoints path context item endpoint Hloc Hfocus Hvalue.
    destruct path as [|index rest]; [discriminate|]. destruct index; [|discriminate].
    simpl in Hloc, Hfocus. destruct (locate body rest) as [child|] eqn:Hchild; [|discriminate].
    destruct (focus ordinary endpoints body rest) as [inside|] eqn:Hinside; inversion Hfocus; subst.
    inversion Hloc; subst. simpl in Hvalue.
    destruct (IH _ _ _ _ _ _ Hchild Hinside Hvalue) as [Hbody Hscope].
    simpl. split; [now rewrite Hbody|now rewrite Hscope].
  - intros family_id arguments ordinary endpoints path context item endpoint Hloc Hfocus Hvalue.
    destruct path; [|discriminate]. inversion Hloc; inversion Hfocus; subst.
    simpl in *. auto.
  - intros ordinary endpoints index path before context after item endpoint Hloc.
    destruct index; discriminate.
  - intros head IHhead tail IHtail ordinary endpoints index path before context after item endpoint
      Hloc Hfocus Hvalue. destruct index as [|index]; simpl in Hloc, Hfocus.
    + destruct (focus ordinary endpoints head path) as [inside|] eqn:Hinside; [|discriminate].
      destruct (instantiates ordinary endpoints tail) as [values|] eqn:Htail; inversion Hfocus; subst.
      destruct (IHhead _ _ _ _ _ _ Hloc Hinside Hvalue) as [Hhead Hscope].
      simpl. split; [now rewrite Hhead, Htail|exact Hscope].
    + destruct (instantiate ordinary endpoints head) as [value|] eqn:Hhead; [|discriminate].
      destruct (focus_many ordinary endpoints tail index path) as [[[prefix inside] suffix]|] eqn:Htail;
        inversion Hfocus; subst.
      destruct (IHtail _ _ _ _ _ _ _ _ _ Hloc Htail Hvalue) as [Hvalues Hscope].
      simpl. split; [now rewrite Hhead, Hvalues|exact Hscope].
Qed.

Theorem focused_family_uses_the_existing_single_hole_context :
  forall shape ordinary endpoints path context item endpoint,
  locate shape path = Some item -> focus ordinary endpoints shape path = Some context ->
  endpoints (location_family item) = Some endpoint ->
  instantiate ordinary endpoints shape = Some (plug context endpoint) /\
  introduced_scope context = location_scope item.
Proof. apply (proj1 focus_reconstructs_mutual). Qed.

Lemma located_paths_are_leaves_mutual :
  (forall shape path extension item other,
    locate shape path = Some item -> locate shape (path ++ extension) = Some other -> extension = []) /\
  (forall shapes index path extension item other,
    locate_many shapes index path = Some item ->
    locate_many shapes index (path ++ extension) = Some other -> extension = []).
Proof.
  apply shape_mutual.
  - intros name path extension item other Hloc. destruct path; discriminate.
  - intros reference path extension item other Hloc. destruct path; discriminate.
  - intros label children IH path extension item other Hloc Hlong.
    destruct path as [|index rest]; [discriminate|]. simpl in *. eauto.
  - intros binders body IH path extension item other Hloc Hlong.
    destruct path as [|index rest]; [discriminate|]. destruct index; [|discriminate].
    simpl in *. destruct (locate body rest) eqn:Hshort; [|discriminate].
    destruct (locate body (rest ++ extension)) eqn:Hextension; [|discriminate]. eauto.
  - intros family_id arguments path extension item other Hloc Hlong.
    destruct path; [|discriminate]. destruct extension; [reflexivity|discriminate].
  - intros index path extension item other Hloc. destruct index; discriminate.
  - intros head IHhead tail IHtail index path extension item other Hloc Hlong.
    destruct index; simpl in *; eauto.
Qed.

Theorem family_occurrence_paths_do_not_overlap : forall shape path extension item other,
  locate shape path = Some item -> locate shape (path ++ extension) = Some other -> extension = [].
Proof. apply (proj1 located_paths_are_leaves_mutual). Qed.

Theorem family_occurrence_path_has_one_location : forall shape path first second,
  locate shape path = Some first -> locate shape path = Some second -> first = second.
Proof. intros. congruence. Qed.

Lemma collected_occurrences_locate_mutual :
  (forall shape prefix introduced item,
    In item (occurrences shape prefix introduced) ->
    exists relative found,
      occurrence_path item = prefix ++ relative /\ locate shape relative = Some found /\
      occurrence_family item = location_family found /\
      occurrence_arguments item = location_arguments found /\
      occurrence_introduced item = introduced ++ location_scope found) /\
  (forall shapes prefix introduced start item,
    In item (occurrences_many shapes prefix introduced start) ->
    exists offset relative found,
      occurrence_path item = prefix ++ (start + offset) :: relative /\
      locate_many shapes offset relative = Some found /\
      occurrence_family item = location_family found /\
      occurrence_arguments item = location_arguments found /\
      occurrence_introduced item = introduced ++ location_scope found).
Proof.
  apply shape_mutual.
  - intros. contradiction.
  - intros. contradiction.
  - intros label children IH prefix introduced item Hin.
    destruct (IH prefix introduced 0 item Hin) as
      [offset [relative [found [Hpath [Hloc [Hfamily [Hargs Hscope]]]]]]].
    exists (offset :: relative), found. simpl in *. auto.
  - intros binders body IH prefix introduced item Hin.
    destruct (IH (prefix ++ [0]) (introduced ++ binders) item Hin) as
      [relative [found [Hpath [Hloc [Hfamily [Hargs Hscope]]]]]].
    exists (0 :: relative), (extend_location binders found).
    split.
    + rewrite Hpath, <- app_assoc. reflexivity.
    + simpl. rewrite Hloc. split; [reflexivity|]. simpl. repeat split; try assumption.
      now rewrite app_assoc.
  - intros family_id arguments prefix introduced item Hin.
    destruct Hin as [<-|Hin]; [|contradiction].
    exists [], (location family_id arguments []). simpl. now rewrite !app_nil_r.
  - intros. contradiction.
  - intros head IHhead tail IHtail prefix introduced start item Hin.
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (IHhead (prefix ++ [start]) introduced item Hin) as
        [relative [found [Hpath [Hloc [Hfamily [Hargs Hscope]]]]]].
      exists 0, relative, found. rewrite Nat.add_0_r. simpl. repeat split; try assumption.
      rewrite Hpath, <- app_assoc. reflexivity.
    + destruct (IHtail prefix introduced (S start) item Hin) as
        [offset [relative [found [Hpath [Hloc [Hfamily [Hargs Hscope]]]]]]].
      exists (S offset), relative, found. rewrite Nat.add_succ_r. simpl in *. auto.
Qed.

Theorem each_collected_occurrence_has_its_recorded_path_and_scope : forall shape item,
  In item (occurrences shape [] []) ->
  locate shape (occurrence_path item) = Some
    (location (occurrence_family item) (occurrence_arguments item) (occurrence_introduced item)).
Proof.
  intros shape item Hin.
  destruct (proj1 collected_occurrences_locate_mutual shape [] [] item Hin) as
    [relative [[family_id arguments introduced] [Hpath [Hloc [Hfamily [Hargs Hscope]]]]]].
  simpl in *. now rewrite Hpath, Hfamily, Hargs, Hscope.
Qed.

Theorem collected_family_paths_do_not_overlap : forall shape left right extension,
  In left (occurrences shape [] []) -> In right (occurrences shape [] []) ->
  occurrence_path right = occurrence_path left ++ extension -> extension = [].
Proof.
  intros shape left right extension Hleft Hright Hpath.
  apply each_collected_occurrence_has_its_recorded_path_and_scope in Hleft.
  apply each_collected_occurrence_has_its_recorded_path_and_scope in Hright.
  rewrite Hpath in Hright.
  exact (family_occurrence_paths_do_not_overlap shape (occurrence_path left) extension _ _ Hleft Hright).
Qed.

Theorem collected_family_path_determines_the_complete_occurrence : forall shape left right,
  In left (occurrences shape [] []) -> In right (occurrences shape [] []) ->
  occurrence_path left = occurrence_path right -> left = right.
Proof.
  intros shape [lf la lp ls] [rf ra rp rs] Hleft Hright Hpath. simpl in Hpath. subst rp.
  apply each_collected_occurrence_has_its_recorded_path_and_scope in Hleft.
  apply each_collected_occurrence_has_its_recorded_path_and_scope in Hright.
  simpl in *. rewrite Hleft in Hright. inversion Hright. reflexivity.
Qed.

Lemma focus_exists_for_instantiated_shape_mutual :
  (forall shape ordinary endpoints path item parent,
    locate shape path = Some item -> instantiate ordinary endpoints shape = Some parent ->
    exists context, focus ordinary endpoints shape path = Some context) /\
  (forall shapes ordinary endpoints index path item parents,
    locate_many shapes index path = Some item -> instantiates ordinary endpoints shapes = Some parents ->
    exists before context after, focus_many ordinary endpoints shapes index path = Some (before, context, after)).
Proof.
  apply shape_mutual.
  - intros name ordinary endpoints path item parent Hloc. destruct path; discriminate.
  - intros reference ordinary endpoints path item parent Hloc. destruct path; discriminate.
  - intros label children IH ordinary endpoints path item parent Hloc Hparent.
    destruct path as [|index rest]; [discriminate|]. simpl in Hloc, Hparent.
    destruct (instantiates ordinary endpoints children) as [values|] eqn:Hvalues; [|discriminate].
    destruct (IH _ _ _ _ _ _ Hloc Hvalues) as [before [inside [after Hfocus]]].
    exists (NodeContext label before inside after). simpl. now rewrite Hfocus.
  - intros binders body IH ordinary endpoints path item parent Hloc Hparent.
    destruct path as [|index rest]; [discriminate|]. destruct index; [|discriminate].
    simpl in Hloc, Hparent. destruct (locate body rest) as [child|] eqn:Hchild; [|discriminate].
    destruct (instantiate ordinary endpoints body) as [value|] eqn:Hvalue; [|discriminate].
    destruct (IH _ _ _ _ _ Hchild Hvalue) as [inside Hfocus].
    exists (BinderContext binders inside). simpl. now rewrite Hfocus.
  - intros family_id arguments ordinary endpoints path item parent Hloc Hparent.
    destruct path; [exists Hole; reflexivity|discriminate].
  - intros ordinary endpoints index path item parents Hloc. destruct index; discriminate.
  - intros head IHhead tail IHtail ordinary endpoints index path item parents Hloc Hparents.
    simpl in Hparents.
    destruct (instantiate ordinary endpoints head) as [value|] eqn:Hhead; [|discriminate].
    destruct (instantiates ordinary endpoints tail) as [values|] eqn:Htail; [|discriminate].
    destruct index as [|index]; simpl in Hloc.
    + destruct (IHhead _ _ _ _ _ Hloc Hhead) as [inside Hfocus].
      exists [], inside, values. simpl. now rewrite Hfocus, Htail.
    + destruct (IHtail _ _ _ _ _ _ Hloc Htail) as [before [inside [after Hfocus]]].
      exists (value :: before), inside, after. simpl. now rewrite Hhead, Hfocus.
Qed.

Theorem every_instantiated_occurrence_has_a_single_hole_focus :
  forall shape ordinary endpoints item parent,
  In item (occurrences shape [] []) -> instantiate ordinary endpoints shape = Some parent ->
  exists context, focus ordinary endpoints shape (occurrence_path item) = Some context.
Proof.
  intros. eapply (proj1 focus_exists_for_instantiated_shape_mutual); [|eassumption].
  now apply each_collected_occurrence_has_its_recorded_path_and_scope.
Qed.

Lemma located_family_is_a_hole_mutual :
  (forall shape path item, locate shape path = Some item ->
    In (location_family item) (hole_names shape)) /\
  (forall shapes index path item, locate_many shapes index path = Some item ->
    In (location_family item) (hole_names_many shapes)).
Proof.
  apply shape_mutual.
  - intros name path item Hloc. destruct path; discriminate.
  - intros reference path item Hloc. destruct path; discriminate.
  - intros label children IH path item Hloc. destruct path; [discriminate|]. simpl. eauto.
  - intros binders body IH path item Hloc.
    destruct path as [|index rest]; [discriminate|]. destruct index; [|discriminate].
    simpl in Hloc. destruct (locate body rest) as [child|] eqn:Hchild; inversion Hloc; subst.
    simpl. now apply IH in Hchild.
  - intros family_id arguments path item Hloc. destruct path; [|discriminate].
    inversion Hloc; subst. simpl. auto.
  - intros index path item Hloc. destruct index; discriminate.
  - intros head IHhead tail IHtail index path item Hloc.
    destruct index; simpl in *; apply in_or_app; [left; eauto|right; eauto].
Qed.

Lemma distinct_app_has_no_shared_member : forall (left right : list nat) item,
  NoDup (left ++ right) -> In item left -> ~ In item right.
Proof.
  induction left as [|head tail IH]; intros right item Hdistinct Hin; [contradiction|].
  inversion Hdistinct; subst. destruct Hin as [<-|Hin].
  - intros Hright. match goal with Hnot : ~ In head (tail ++ right) |- _ =>
      apply Hnot; apply in_or_app; now right end.
  - eauto.
Qed.

Lemma absent_family_update_keeps_instantiation : forall shape ordinary endpoints family_id value,
  ~ In family_id (hole_names shape) ->
  instantiate ordinary (write_binding endpoints family_id value) shape = instantiate ordinary endpoints shape.
Proof.
  intros. apply (proj1 instantiation_agreement_mutual). intros.
  apply fresh_extension_preserves_other_bindings. intros ->. contradiction.
Qed.

Lemma absent_family_update_keeps_instantiations : forall shapes ordinary endpoints family_id value,
  ~ In family_id (hole_names_many shapes) ->
  instantiates ordinary (write_binding endpoints family_id value) shapes = instantiates ordinary endpoints shapes.
Proof.
  intros. apply (proj2 instantiation_agreement_mutual). intros.
  apply fresh_extension_preserves_other_bindings. intros ->. contradiction.
Qed.

Lemma focused_context_survives_endpoint_update_mutual :
  (forall shape ordinary endpoints path context item value,
    NoDup (hole_names shape) -> locate shape path = Some item ->
    focus ordinary endpoints shape path = Some context ->
    focus ordinary (write_binding endpoints (location_family item) value) shape path = Some context) /\
  (forall shapes ordinary endpoints index path before context after item value,
    NoDup (hole_names_many shapes) -> locate_many shapes index path = Some item ->
    focus_many ordinary endpoints shapes index path = Some (before, context, after) ->
    focus_many ordinary (write_binding endpoints (location_family item) value) shapes index path =
      Some (before, context, after)).
Proof.
  apply shape_mutual.
  - intros name ordinary endpoints path context item value Hdistinct Hloc. destruct path; discriminate.
  - intros reference ordinary endpoints path context item value Hdistinct Hloc. destruct path; discriminate.
  - intros label children IH ordinary endpoints path context item value Hdistinct Hloc Hfocus.
    destruct path as [|index rest]; [discriminate|]. simpl in *.
    destruct (focus_many ordinary endpoints children index rest) as [[[before inside] after]|] eqn:Hchildren;
      inversion Hfocus; subst.
    now rewrite (IH _ _ _ _ _ _ _ _ _ Hdistinct Hloc Hchildren).
  - intros binders body IH ordinary endpoints path context item value Hdistinct Hloc Hfocus.
    destruct path as [|index rest]; [discriminate|]. destruct index; [|discriminate]. simpl in *.
    destruct (locate body rest) as [child|] eqn:Hchild; inversion Hloc; subst. simpl.
    destruct (focus ordinary endpoints body rest) as [inside|] eqn:Hinside; inversion Hfocus; subst.
    now rewrite (IH _ _ _ _ _ _ Hdistinct Hchild Hinside).
  - intros family_id arguments ordinary endpoints path context item value Hdistinct Hloc Hfocus.
    destruct path; [exact Hfocus|discriminate].
  - intros ordinary endpoints index path before context after item value Hdistinct Hloc.
    destruct index; discriminate.
  - intros head IHhead tail IHtail ordinary endpoints index path before context after item value
      Hdistinct Hloc Hfocus. simpl in Hdistinct.
    pose proof (NoDup_app_remove_r _ _ Hdistinct) as Hhead_unique.
    pose proof (NoDup_app_remove_l _ _ Hdistinct) as Htail_unique.
    destruct index as [|index]; simpl in Hloc, Hfocus; simpl.
    + pose proof (proj1 located_family_is_a_hole_mutual _ _ _ Hloc) as Hin.
      destruct (focus ordinary endpoints head path) as [inside|] eqn:Hinside; [|discriminate].
      destruct (instantiates ordinary endpoints tail) as [values|] eqn:Htail; inversion Hfocus; subst.
      rewrite (IHhead _ _ _ _ _ _ Hhead_unique Hloc Hinside).
      rewrite absent_family_update_keeps_instantiations.
      * now rewrite Htail.
      * eapply distinct_app_has_no_shared_member; eauto.
    + pose proof (proj2 located_family_is_a_hole_mutual _ _ _ _ Hloc) as Hin.
      destruct (instantiate ordinary endpoints head) as [head_value|] eqn:Hhead; [|discriminate].
      destruct (focus_many ordinary endpoints tail index path) as [[[prefix inside] suffix]|] eqn:Htail;
        inversion Hfocus; subst.
      rewrite (IHtail _ _ _ _ _ _ _ _ _ Htail_unique Hloc Htail).
      rewrite absent_family_update_keeps_instantiation.
      * now rewrite Hhead.
      * intros Hmember. eapply distinct_app_has_no_shared_member; eauto.
Qed.

Theorem updating_a_unique_family_is_single_hole_plugging :
  forall shape ordinary endpoints path context item value,
  NoDup (hole_names shape) -> locate shape path = Some item ->
  focus ordinary endpoints shape path = Some context ->
  instantiate ordinary (write_binding endpoints (location_family item) value) shape = Some (plug context value) /\
  introduced_scope context = location_scope item.
Proof.
  intros shape ordinary endpoints path context item value Hdistinct Hloc Hfocus.
  pose proof (proj1 focused_context_survives_endpoint_update_mutual
    shape ordinary endpoints path context item value Hdistinct Hloc Hfocus) as Hupdated.
  eapply focused_family_uses_the_existing_single_hole_context; [exact Hloc|exact Hupdated|].
  apply write_binding_reads_exact_value.
Qed.

Theorem typed_family_endpoint_update_preserves_parent_type :
  forall categories declarations signature literal_types ambient shape ordinary endpoints item source target
    category parent result step,
  shape_check categories declarations ambient shape = true ->
  In item (occurrences shape [] []) ->
  endpoints (occurrence_family item) = Some source ->
  instantiate ordinary endpoints shape = Some parent ->
  TypedValue signature literal_types ambient parent result ->
  OpenStep signature literal_types step (ambient ++ occurrence_introduced item) category source target ->
  exists updated,
    instantiate ordinary (write_binding endpoints (occurrence_family item) target) shape = Some updated /\
    TypedValue signature literal_types ambient updated result.
Proof.
  intros categories declarations signature literal_types ambient shape ordinary endpoints item source target
    category parent result step Hchecked Hin Hsource Hparent Htyped Hstep.
  pose proof (each_collected_occurrence_has_its_recorded_path_and_scope _ _ Hin) as Hloc.
  destruct (every_instantiated_occurrence_has_a_single_hole_focus _ _ _ _ _ Hin Hparent)
    as [context Hfocus].
  pose proof (focused_family_uses_the_existing_single_hole_context _ _ _ _ _ _ _ Hloc Hfocus Hsource)
    as [Hplug Hscope].
  simpl in Hscope. rewrite Hparent in Hplug. inversion Hplug; subst parent.
  assert (Hdistinct : NoDup (hole_names shape)).
  { rewrite hole_names_are_exactly_checked_family_ids.
    eapply accepted_shape_has_unique_family_occurrences; eauto. }
  exists (plug context target). split.
  - apply (proj1 (updating_a_unique_family_is_single_hole_plugging
      shape ordinary endpoints (occurrence_path item) context
      (location (occurrence_family item) (occurrence_arguments item) (occurrence_introduced item))
      target Hdistinct Hloc Hfocus)).
  - eapply typed_child_step_preserves_parent_sort; [exact Htyped|].
    rewrite Hscope. exact Hstep.
Qed.

Definition BoundDeclaredSources (declarations : list (nat * Family)) (results : list (Value * Value)) (endpoints : Environment) :=
  Forall2 (fun declaration values => endpoints (fst declaration) = Some (fst values)) declarations results.

Fixpoint apply_endpoint_results (declarations : list (nat * Family)) (results : list (Value * Value))
    (endpoints : Environment) :=
  match declarations, results with
  | (family_id, _) :: rest, (_, target) :: tail =>
      apply_endpoint_results rest tail (write_binding endpoints family_id target)
  | _, _ => endpoints
  end.

Lemma declared_sources_survive_an_unrelated_update :
  forall declarations results endpoints family_id value,
  ~ In family_id (map (@fst nat Family) declarations) ->
  BoundDeclaredSources declarations results endpoints ->
  BoundDeclaredSources declarations results (write_binding endpoints family_id value).
Proof.
  intros declarations results endpoints family_id value Hnot Hbound.
  induction Hbound; constructor.
  - rewrite fresh_extension_preserves_other_bindings; [assumption|].
    intros Heq. apply Hnot. simpl. now left.
  - apply IHHbound. intros Hin. apply Hnot. simpl. now right.
Qed.

Lemma declared_endpoint_writes_preserve_unmentioned_families :
  forall declarations results endpoints family_id,
  ~ In family_id (map (@fst nat Family) declarations) ->
  apply_endpoint_results declarations results endpoints family_id = endpoints family_id.
Proof.
  induction declarations as [|[head descriptor] rest IH]; intros results endpoints family_id Hnot;
    destruct results as [|[source target] tail]; try reflexivity. simpl.
  rewrite IH.
  - apply fresh_extension_preserves_other_bindings. intros ->. apply Hnot. simpl. auto.
  - intros Hin. apply Hnot. simpl. auto.
Qed.

Lemma declared_endpoint_writes_read_each_result :
  forall declarations results endpoints family_id,
  length declarations = length results -> NoDup (map (@fst nat Family) declarations) ->
  In family_id (map fst declarations) ->
  apply_endpoint_results declarations results endpoints family_id = declared_endpoint declarations results snd family_id.
Proof.
  induction declarations as [|[head descriptor] rest IH]; intros results endpoints family_id Hlength Hdistinct Hin;
    [contradiction|].
  destruct results as [|[source target] tail]; [discriminate|].
  inversion Hdistinct; subst. simpl in Hlength, Hin. unfold declared_endpoint. simpl.
  destruct (Nat.eqb family_id head) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. subst family_id.
    rewrite declared_endpoint_writes_preserve_unmentioned_families; [apply write_binding_reads_exact_value|assumption].
  - apply IH; [lia|assumption|].
    destruct Hin as [Heq|Hin]; [subst; rewrite Nat.eqb_refl in Hsame; discriminate|assumption].
Qed.

Lemma pair_membership_maps_declaration_ids :
  forall (declarations : list (nat * Family)) (results : list (Value * Value)) declaration values,
  In (declaration, values) (combine declarations results) ->
  In (fst declaration, values) (combine (map fst declarations) results).
Proof.
  induction declarations as [|head tail IH]; intros results declaration values Hin;
    destruct results; simpl in *; try contradiction.
  destruct Hin as [Heq|Hin]; [inversion Heq; subst; now left|right; now apply IH].
Qed.

Lemma declaration_sources_bind_the_original_endpoints : forall declarations results,
  NoDup (map (@fst nat Family) declarations) -> length declarations = length results ->
  BoundDeclaredSources declarations results (declared_endpoint declarations results fst).
Proof.
  intros declarations results Hdistinct Hlength. apply forall2_from_pair_membership; [assumption|].
  intros declaration values Hin. unfold declared_endpoint. apply family_endpoint_at_pair; [assumption|].
  now apply pair_membership_maps_declaration_ids.
Qed.

Theorem finite_declared_endpoint_updates_preserve_parent_type :
  forall categories complete_declarations signature literal_types ambient shape ordinary
    declarations results endpoints parent result step,
  shape_check categories complete_declarations ambient shape = true ->
  DeclaredTransitions (OpenStep signature literal_types step) ambient (occurrences shape [] []) declarations results ->
  NoDup (map (@fst nat Family) declarations) -> BoundDeclaredSources declarations results endpoints ->
  instantiate ordinary endpoints shape = Some parent -> TypedValue signature literal_types ambient parent result ->
  exists updated,
    instantiate ordinary (apply_endpoint_results declarations results endpoints) shape = Some updated /\
    TypedValue signature literal_types ambient updated result.
Proof.
  intros categories complete_declarations signature literal_types ambient shape ordinary
    declarations results endpoints parent result step Hchecked Htransitions.
  revert endpoints parent.
  induction Htransitions as [|[family_id descriptor] [source target] declarations results Hstep Hsteps IH];
    intros endpoints parent Hdistinct Hbound Hparent Htyped.
  - exists parent. auto.
  - inversion Hdistinct; subst. inversion Hbound; subst.
    destruct Hstep as [item [Hin [Hfamily Htransition]]]. simpl in Hfamily, Htransition. subst family_id.
    assert (Hsource : endpoints (occurrence_family item) = Some source) by assumption.
    destruct (typed_family_endpoint_update_preserves_parent_type categories complete_declarations
      signature literal_types ambient shape ordinary endpoints item source target
      (family_result descriptor) parent result step Hchecked Hin Hsource Hparent Htyped Htransition)
      as [updated [Hupdated Hupdated_type]].
    simpl. apply IH with updated; try assumption.
    apply declared_sources_survive_an_unrelated_update; assumption.
Qed.

Theorem authored_open_family_steps_preserve_parent_type :
  forall categories declarations signature literal_types ambient shape ordinary left right input output result step,
  extract_pair left right = Some shape -> shape_check categories declarations ambient shape = true ->
  AuthoredParentStep (OpenStep signature literal_types step) ambient declarations shape ordinary left right input output ->
  TypedValue signature literal_types ambient input result ->
  TypedValue signature literal_types ambient output result.
Proof.
  intros categories declarations signature literal_types ambient shape ordinary left right input output result step
    Hextract Hchecked [results [Hsteps [Hinput Houtput]]] Htyped.
  apply extraction_exactly_preserves_both_authored_sides in Hextract as [-> ->].
  rewrite (proj1 interpretation_of_rendering_mutual) in Hinput, Houtput.
  pose proof (accepted_shape_has_unique_declarations _ _ _ _ Hchecked) as Hdistinct.
  assert (Hlength : length declarations = length results) by (now apply Forall2_length in Hsteps).
  pose proof (declaration_sources_bind_the_original_endpoints declarations results Hdistinct Hlength) as Hbound.
  destruct (finite_declared_endpoint_updates_preserve_parent_type categories declarations
    signature literal_types ambient shape ordinary declarations results
    (declared_endpoint declarations results fst) input result step
    Hchecked Hsteps Hdistinct Hbound Hinput Htyped) as [updated [Hupdated Hupdated_type]].
  rewrite (proj1 instantiation_agreement_mutual) with
    (second := declared_endpoint declarations results snd) in Hupdated.
  - rewrite Houtput in Hupdated. inversion Hupdated; subst. exact Hupdated_type.
  - intros family_id Hin. apply declared_endpoint_writes_read_each_result; try assumption.
    eapply accepted_shape_has_no_undeclared_family; eauto.
    now rewrite <- hole_names_are_exactly_checked_family_ids.
Qed.

Theorem normalized_open_family_rules_preserve_parent_type :
  forall categories step authored ambient declarations shape prior left right requests input output signature literal_types result sources,
  extract_pair left right = Some shape -> shape_check categories declarations ambient shape = true ->
  build_requests authored ambient declarations (occurrences shape [] []) = Some requests ->
  SupportedBy authored prior -> (forall name, In name (ordinary_names shape) -> In name authored) ->
  CoreParentStep (OpenStep signature literal_types step) requests shape (source_name authored) (target_name authored)
    (source_overlay prior requests sources) input output ->
  TypedValue signature literal_types ambient input result ->
  TypedValue signature literal_types ambient output result.
Proof.
  intros categories step authored ambient declarations shape prior left right requests input output signature literal_types result sources
    Hextract Hchecked Hbuild Hsupport Hnames Hcore Htyped.
  eapply authored_open_family_steps_preserve_parent_type; [exact Hextract|exact Hchecked| |exact Htyped].
  apply (proj2 (authored_family_steps_iff_existing_core_rules categories
    (OpenStep signature literal_types step) authored ambient declarations shape prior left right requests input output
    Hextract Hchecked Hbuild Hsupport Hnames)).
  now exists sources.
Qed.

Definition edge_eligible enabled (evidence : option nat * option nat) :=
  enabled && match evidence with
  | (Some left_sort, Some right_sort) => Nat.eqb left_sort right_sort
  | _ => false
  end.

Fixpoint path_eligible enabled evidence :=
  match evidence with
  | [] => enabled
  | edge :: rest => path_eligible (edge_eligible enabled edge) rest
  end.

Definition MatchingSortEvidence (evidence : option nat * option nat) :=
  exists sort, fst evidence = Some sort /\ snd evidence = Some sort.

Lemma edge_eligibility_is_exact : forall enabled evidence,
  edge_eligible enabled evidence = true <-> enabled = true /\ MatchingSortEvidence evidence.
Proof.
  intros enabled [left right]. unfold edge_eligible, MatchingSortEvidence. simpl.
  rewrite andb_true_iff. destruct left as [left|], right as [right|]; simpl.
  - rewrite Nat.eqb_eq. split.
    + intros [H ->]. split; [assumption|exists right; auto].
    + intros [H [sort [Hl Hr]]]. inversion Hl; inversion Hr; subst. auto.
  - split; intros [H E]; [discriminate|destruct E as [sort [_ E]]; discriminate].
  - split; intros [H E]; [discriminate|destruct E as [sort [E _]]; discriminate].
  - split; intros [H E]; [discriminate|destruct E as [sort [E _]]; discriminate].
Qed.

Theorem path_eligibility_requires_matching_sort_evidence : forall evidence enabled,
  path_eligible enabled evidence = true <-> enabled = true /\ Forall MatchingSortEvidence evidence.
Proof.
  induction evidence as [|edge rest IH]; intros enabled; simpl.
  - split; intros; [split; [assumption|constructor]|tauto].
  - rewrite IH, edge_eligibility_is_exact. split.
    + intros [[Henabled Hedge] Hrest]. split; [assumption|constructor; assumption].
    + intros [Henabled Hall]. inversion Hall; subst. auto.
Qed.

Theorem disabled_context_disables_all_descendants : forall evidence,
  path_eligible false evidence = false.
Proof.
  intros. destruct (path_eligible false evidence) eqn:H; [|reflexivity].
  apply path_eligibility_requires_matching_sort_evidence in H. destruct H. discriminate.
Qed.

Theorem sibling_eligibility_uses_the_unchanged_parent : forall parent first second,
  edge_eligible parent second = true ->
  nth_error (map (edge_eligible parent) [first; second]) 1 = Some true.
Proof. intros. simpl. now rewrite H. Qed.

Definition admit_path {A : Type} enabled evidence (value : A) :=
  if path_eligible enabled evidence then Some value else None.

Theorem eligible_paths_preserve_the_existing_normalized_result :
  forall (A : Type) evidence (value : A),
  Forall MatchingSortEvidence evidence -> admit_path true evidence value = Some value.
Proof.
  intros. unfold admit_path.
  assert (path_eligible true evidence = true) by (apply path_eligibility_requires_matching_sort_evidence; auto).
  now rewrite H0.
Qed.

Theorem root_projection_needs_no_parent_edge : forall (A : Type) (value : A),
  admit_path true [] value = Some value.
Proof. reflexivity. Qed.

Theorem admitted_typed_child_step_preserves_parent_sort :
  forall signature literal_types scope context source target category result step evidence output,
  admit_path true evidence target = Some output ->
  TypedValue signature literal_types scope (plug context source) result ->
  OpenStep signature literal_types step (scope ++ introduced_scope context) category source target ->
  Forall MatchingSortEvidence evidence /\
  TypedValue signature literal_types scope (plug context output) result.
Proof.
  intros signature literal_types scope context source target category result step evidence output Hadmit Hparent Hstep.
  unfold admit_path in Hadmit. destruct (path_eligible true evidence) eqn:Hpath; [|discriminate].
  inversion Hadmit; subst. split.
  - apply path_eligibility_requires_matching_sort_evidence in Hpath. tauto.
  - eapply typed_child_step_preserves_parent_sort; eauto.
Qed.

End RewriteFamilyFocus.

Print Assumptions RewriteFamilyFocus.value_sort_is_unique.
Print Assumptions RewriteFamilyFocus.typed_plugging_decomposes_into_context_and_endpoint.
Print Assumptions RewriteFamilyFocus.typed_child_step_preserves_parent_sort.
Print Assumptions RewriteFamilyFocus.focused_family_uses_the_existing_single_hole_context.
Print Assumptions RewriteFamilyFocus.family_occurrence_paths_do_not_overlap.
Print Assumptions RewriteFamilyFocus.family_occurrence_path_has_one_location.
Print Assumptions RewriteFamilyFocus.each_collected_occurrence_has_its_recorded_path_and_scope.
Print Assumptions RewriteFamilyFocus.collected_family_paths_do_not_overlap.
Print Assumptions RewriteFamilyFocus.collected_family_path_determines_the_complete_occurrence.
Print Assumptions RewriteFamilyFocus.every_instantiated_occurrence_has_a_single_hole_focus.
Print Assumptions RewriteFamilyFocus.updating_a_unique_family_is_single_hole_plugging.
Print Assumptions RewriteFamilyFocus.typed_family_endpoint_update_preserves_parent_type.
Print Assumptions RewriteFamilyFocus.finite_declared_endpoint_updates_preserve_parent_type.
Print Assumptions RewriteFamilyFocus.authored_open_family_steps_preserve_parent_type.
Print Assumptions RewriteFamilyFocus.normalized_open_family_rules_preserve_parent_type.
Print Assumptions RewriteFamilyFocus.path_eligibility_requires_matching_sort_evidence.
Print Assumptions RewriteFamilyFocus.disabled_context_disables_all_descendants.
Print Assumptions RewriteFamilyFocus.sibling_eligibility_uses_the_unchanged_parent.
Print Assumptions RewriteFamilyFocus.eligible_paths_preserve_the_existing_normalized_result.
Print Assumptions RewriteFamilyFocus.root_projection_needs_no_parent_edge.
Print Assumptions RewriteFamilyFocus.admitted_typed_child_step_preserves_parent_sort.
