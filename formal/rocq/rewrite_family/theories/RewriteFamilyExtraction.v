From Stdlib Require Import List Bool PeanoNat Lia Sorting.Permutation.
Require Import RewriteFamilyNormalization.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization.

Module RewriteFamilyExtraction.

Inductive Side := Source | Target.

Inductive Surface :=
| SMeta (name : nat)
| SBound (reference : Binding)
| SNode (label : nat) (children : Surfaces)
| SBind (binders : list Binding) (body : Surface)
| SProjection (side : Side) (family_id : nat) (arguments : list Binding)
with Surfaces :=
| SEmpty
| SMore (head : Surface) (tail : Surfaces).

Inductive Shape :=
| QMeta (name : nat)
| QBound (reference : Binding)
| QNode (label : nat) (children : Shapes)
| QBind (binders : list Binding) (body : Shape)
| QHole (family_id : nat) (arguments : list Binding)
with Shapes :=
| QEmpty
| QMore (head : Shape) (tail : Shapes).

Scheme surface_mut := Induction for Surface Sort Prop
with surfaces_mut := Induction for Surfaces Sort Prop.
Combined Scheme surface_mutual from surface_mut, surfaces_mut.

Scheme shape_mut := Induction for Shape Sort Prop
with shapes_mut := Induction for Shapes Sort Prop.
Combined Scheme shape_mutual from shape_mut, shapes_mut.

Definition binding_eq_dec : forall left right : Binding, {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition bindings_eq_dec := list_eq_dec binding_eq_dec.

Fixpoint extract_pair (left right : Surface) {struct left} : option Shape :=
  match left, right with
  | SMeta left_name, SMeta right_name =>
      if Nat.eq_dec left_name right_name then Some (QMeta left_name) else None
  | SBound left_reference, SBound right_reference =>
      if binding_eq_dec left_reference right_reference
      then Some (QBound left_reference) else None
  | SNode left_label left_children, SNode right_label right_children =>
      if Nat.eq_dec left_label right_label
      then option_map (QNode left_label) (extract_pairs left_children right_children)
      else None
  | SBind left_binders left_body, SBind right_binders right_body =>
      if bindings_eq_dec left_binders right_binders
      then option_map (QBind left_binders) (extract_pair left_body right_body)
      else None
  | SProjection Source left_family left_arguments,
    SProjection Target right_family right_arguments =>
      if Nat.eq_dec left_family right_family
      then if bindings_eq_dec left_arguments right_arguments
        then Some (QHole left_family left_arguments) else None
      else None
  | _, _ => None
  end
with extract_pairs (left right : Surfaces) {struct left} : option Shapes :=
  match left, right with
  | SEmpty, SEmpty => Some QEmpty
  | SMore left_head left_tail, SMore right_head right_tail =>
      match extract_pair left_head right_head, extract_pairs left_tail right_tail with
      | Some head, Some tail => Some (QMore head tail)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint render (side : Side) (shape : Shape) : Surface :=
  match shape with
  | QMeta name => SMeta name
  | QBound reference => SBound reference
  | QNode label children => SNode label (renders side children)
  | QBind binders body => SBind binders (render side body)
  | QHole family_id arguments => SProjection side family_id arguments
  end
with renders (side : Side) (shapes : Shapes) : Surfaces :=
  match shapes with
  | QEmpty => SEmpty
  | QMore head tail => SMore (render side head) (renders side tail)
  end.

Lemma extraction_sound_mutual :
  (forall left right shape, extract_pair left right = Some shape ->
    left = render Source shape /\ right = render Target shape) /\
  (forall left right shapes, extract_pairs left right = Some shapes ->
    left = renders Source shapes /\ right = renders Target shapes).
Proof.
  apply surface_mutual.
  - intros name right shape H.
    destruct right as [rn|rb|rl rc|rbs rb|rs rf ra]; simpl in H; try discriminate.
    destruct (Nat.eq_dec name rn); inversion H; subst. auto.
  - intros reference right shape H.
    destruct right as [rn|rb|rl rc|rbs rb|rs rf ra]; simpl in H; try discriminate.
    destruct (binding_eq_dec reference rb); inversion H; subst. auto.
  - intros label children IH right shape H.
    destruct right as [rn|rb|rl rc|rbs rb|rs rf ra]; simpl in H; try discriminate.
    destruct (Nat.eq_dec label rl); [subst rl|discriminate].
    destruct (extract_pairs children rc) eqn:Hchildren; inversion H; subst.
    apply IH in Hchildren. destruct Hchildren as [-> ->]. auto.
  - intros binders body IH right shape H.
    destruct right as [rn|rb|rl rc|rbs rb|rs rf ra]; simpl in H; try discriminate.
    destruct (bindings_eq_dec binders rbs); [subst rbs|discriminate].
    destruct (extract_pair body rb) eqn:Hbody; inversion H; subst.
    apply IH in Hbody. destruct Hbody as [-> ->]. auto.
  - intros side family_id arguments right shape H.
    destruct right as [rn|rb|rl rc|rbs rb|rs rf ra]; destruct side; simpl in H; try discriminate.
    destruct rs; simpl in H; try discriminate.
    destruct (Nat.eq_dec family_id rf); [subst rf|discriminate].
    destruct (bindings_eq_dec arguments ra); inversion H; subst. auto.
  - intros right shapes H. destruct right; inversion H; subst. auto.
  - intros head IHhead tail IHtail right shapes H.
    destruct right as [|rh rt]; simpl in H; try discriminate.
    destruct (extract_pair head rh) eqn:Hhead; try discriminate.
    destruct (extract_pairs tail rt) eqn:Htail; inversion H; subst.
    apply IHhead in Hhead. apply IHtail in Htail.
    destruct Hhead as [-> ->]. destruct Htail as [-> ->]. auto.
Qed.

Lemma extraction_complete_mutual :
  (forall shape, extract_pair (render Source shape) (render Target shape) = Some shape) /\
  (forall shapes, extract_pairs (renders Source shapes) (renders Target shapes) = Some shapes).
Proof.
  apply shape_mutual; simpl; intros.
  - destruct (Nat.eq_dec name name); congruence.
  - destruct (binding_eq_dec reference reference); congruence.
  - destruct (Nat.eq_dec label label); [now rewrite H|congruence].
  - destruct (bindings_eq_dec binders binders); [now rewrite H|congruence].
  - destruct (Nat.eq_dec family_id family_id); [|congruence].
    destruct (bindings_eq_dec arguments arguments); congruence.
  - reflexivity.
  - now rewrite H, H0.
Qed.

Theorem extraction_exactly_preserves_both_authored_sides : forall left right shape,
  extract_pair left right = Some shape <->
  left = render Source shape /\ right = render Target shape.
Proof.
  intros. split.
  - apply (proj1 extraction_sound_mutual).
  - intros [-> ->]. apply (proj1 extraction_complete_mutual).
Qed.

Theorem extraction_preserves_constructor_arity : forall label left right shape,
  extract_pair (SNode label left) (SNode label right) = Some shape ->
  exists children, shape = QNode label children /\
    left = renders Source children /\ right = renders Target children.
Proof.
  intros. apply extraction_exactly_preserves_both_authored_sides in H.
  destruct H as [Hleft Hright]. destruct shape; simpl in Hleft; try discriminate.
  inversion Hleft. subst. inversion Hright. subst. eauto.
Qed.

Theorem extraction_rejects_changed_ordinary_metavariable : forall left right,
  left <> right -> extract_pair (SMeta left) (SMeta right) = None.
Proof. intros. simpl. destruct (Nat.eq_dec left right); congruence. Qed.

Theorem extraction_rejects_changed_lexical_arguments : forall family_id left right,
  left <> right ->
  extract_pair (SProjection Source family_id left) (SProjection Target family_id right) = None.
Proof.
  intros. simpl. destruct (Nat.eq_dec family_id family_id); [|congruence].
  destruct (bindings_eq_dec left right); congruence.
Qed.

Fixpoint instantiate (ordinary endpoints : Environment) (shape : Shape) : option Value :=
  match shape with
  | QMeta name => ordinary name
  | QBound reference => Some (Bound reference)
  | QNode label children => option_map (Node label) (instantiates ordinary endpoints children)
  | QBind binders body => option_map (Bind binders) (instantiate ordinary endpoints body)
  | QHole family_id _ => endpoints family_id
  end
with instantiates (ordinary endpoints : Environment) (shapes : Shapes) : option (list Value) :=
  match shapes with
  | QEmpty => Some []
  | QMore head tail =>
      match instantiate ordinary endpoints head, instantiates ordinary endpoints tail with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Fixpoint interpret (ordinary sources targets : Environment) (surface : Surface) : option Value :=
  match surface with
  | SMeta name => ordinary name
  | SBound reference => Some (Bound reference)
  | SNode label children => option_map (Node label) (interprets ordinary sources targets children)
  | SBind binders body => option_map (Bind binders) (interpret ordinary sources targets body)
  | SProjection Source family_id _ => sources family_id
  | SProjection Target family_id _ => targets family_id
  end
with interprets (ordinary sources targets : Environment) (surfaces : Surfaces) : option (list Value) :=
  match surfaces with
  | SEmpty => Some []
  | SMore head tail =>
      match interpret ordinary sources targets head, interprets ordinary sources targets tail with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Lemma interpretation_of_rendering_mutual :
  (forall shape ordinary sources targets side,
    interpret ordinary sources targets (render side shape) =
    instantiate ordinary (match side with Source => sources | Target => targets end) shape) /\
  (forall shapes ordinary sources targets side,
    interprets ordinary sources targets (renders side shapes) =
    instantiates ordinary (match side with Source => sources | Target => targets end) shapes).
Proof.
  apply shape_mutual; intros; simpl; try reflexivity.
  - now rewrite H.
  - now rewrite H.
  - destruct side; reflexivity.
  - now rewrite H, H0.
Qed.

Theorem extraction_commutes_with_ordinary_instantiation :
  forall left right shape ordinary sources targets,
  extract_pair left right = Some shape ->
  interpret ordinary sources targets left = instantiate ordinary sources shape /\
  interpret ordinary sources targets right = instantiate ordinary targets shape.
Proof.
  intros. apply extraction_exactly_preserves_both_authored_sides in H.
  destruct H as [-> ->]. split; apply (proj1 interpretation_of_rendering_mutual).
Qed.

Record Occurrence := occurrence {
  occurrence_family : nat;
  occurrence_arguments : list Binding;
  occurrence_path : list nat;
  occurrence_introduced : list Binding
}.

Fixpoint occurrences (shape : Shape) path introduced : list Occurrence :=
  match shape with
  | QMeta _ | QBound _ => []
  | QNode _ children => occurrences_many children path introduced 0
  | QBind binders body => occurrences body (path ++ [0]) (introduced ++ binders)
  | QHole family_id arguments => [occurrence family_id arguments path introduced]
  end
with occurrences_many (shapes : Shapes) path introduced index : list Occurrence :=
  match shapes with
  | QEmpty => []
  | QMore head tail =>
      occurrences head (path ++ [index]) introduced ++
      occurrences_many tail path introduced (S index)
  end.

Definition family_ids shape := map occurrence_family (occurrences shape [] []).

Fixpoint lookup_family name (declarations : list (nat * Family)) :=
  match declarations with
  | [] => None
  | (candidate, descriptor) :: rest =>
      if Nat.eqb name candidate then Some descriptor else lookup_family name rest
  end.

Fixpoint distinct_names (names : list nat) :=
  match names with
  | [] => true
  | name :: rest => negb (existsb (Nat.eqb name) rest) && distinct_names rest
  end.

Lemma distinct_names_spec : forall names,
  distinct_names names = true <-> NoDup names.
Proof.
  induction names as [|name rest IH]; simpl.
  - split; intros; constructor.
  - rewrite andb_true_iff, negb_true_iff, IH.
    split.
    + intros [Hnot Hrest]. constructor; [|assumption]. intros Hin.
      apply category_member_spec in Hin. congruence.
    + intros Hnodup. inversion Hnodup as [|? ? Hnot Hrest]. split; [|assumption].
      destruct (existsb (Nat.eqb name) rest) eqn:Hmember; [|reflexivity].
      apply category_member_spec in Hmember. contradiction.
Qed.

Definition occurrence_check categories declarations ambient item :=
  match lookup_family (occurrence_family item) declarations with
  | None => false
  | Some descriptor => family_check categories descriptor ambient
      (occurrence_introduced item) (occurrence_arguments item)
  end.

Definition shape_check categories declarations ambient shape :=
  distinct_names (map fst declarations) &&
  distinct_names (family_ids shape) &&
  forallb (fun name => existsb (Nat.eqb name) (family_ids shape)) (map fst declarations) &&
  forallb (occurrence_check categories declarations ambient) (occurrences shape [] []).

Lemma lookup_family_is_declared : forall declarations name descriptor,
  lookup_family name declarations = Some descriptor -> In (name, descriptor) declarations.
Proof.
  induction declarations as [|[candidate value] rest IH]; intros; simpl in H; [discriminate|].
  destruct (Nat.eqb name candidate) eqn:Heq.
  - apply Nat.eqb_eq in Heq. inversion H. subst. now left.
  - right. eauto.
Qed.

Theorem accepted_shape_has_unique_family_occurrences : forall categories declarations ambient shape,
  shape_check categories declarations ambient shape = true -> NoDup (family_ids shape).
Proof.
  intros. unfold shape_check in H. rewrite !andb_true_iff in H.
  apply distinct_names_spec. tauto.
Qed.

Theorem accepted_shape_has_unique_declarations : forall categories declarations ambient shape,
  shape_check categories declarations ambient shape = true -> NoDup (map fst declarations).
Proof.
  intros. unfold shape_check in H. rewrite !andb_true_iff in H.
  apply distinct_names_spec. tauto.
Qed.

Theorem accepted_shape_uses_every_declared_family :
  forall categories declarations ambient shape name,
  shape_check categories declarations ambient shape = true ->
  In name (map fst declarations) -> In name (family_ids shape).
Proof.
  intros categories declarations ambient shape name Hcheck Hin.
  unfold shape_check in Hcheck. rewrite !andb_true_iff in Hcheck.
  destruct Hcheck as [[[_ _] Hcoverage] _].
  rewrite forallb_forall in Hcoverage. apply category_member_spec. now apply Hcoverage.
Qed.

Theorem accepted_occurrence_has_exact_scoped_family :
  forall categories declarations ambient shape item,
  shape_check categories declarations ambient shape = true ->
  In item (occurrences shape [] []) ->
  exists descriptor,
    lookup_family (occurrence_family item) declarations = Some descriptor /\
    In (occurrence_family item, descriptor) declarations /\
    FamilyWellTyped categories descriptor ambient
      (occurrence_introduced item) (occurrence_arguments item).
Proof.
  intros categories declarations ambient shape item Hcheck Hin.
  unfold shape_check in Hcheck. rewrite !andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hoccurrences]. rewrite forallb_forall in Hoccurrences.
  specialize (Hoccurrences item Hin). unfold occurrence_check in Hoccurrences.
  destruct (lookup_family (occurrence_family item) declarations) as [descriptor|] eqn:Hlookup;
    [|discriminate].
  exists descriptor. split; [reflexivity|]. split.
  - now apply lookup_family_is_declared.
  - now apply family_check_is_exact.
Qed.

Theorem accepted_shape_has_no_undeclared_family :
  forall categories declarations ambient shape name,
  shape_check categories declarations ambient shape = true ->
  In name (family_ids shape) -> In name (map fst declarations).
Proof.
  intros categories declarations ambient shape name Hcheck Hin.
  unfold family_ids in Hin. apply in_map_iff in Hin.
  destruct Hin as [item [<- Hin]].
  destruct (accepted_occurrence_has_exact_scoped_family _ _ _ _ _ Hcheck Hin)
    as [descriptor [_ [Hdeclared _]]].
  apply in_map with (f := @fst nat Family) in Hdeclared. exact Hdeclared.
Qed.

Theorem two_families_may_share_an_introduced_binder :
  shape_check [0]
    [(0, family [0] 0); (1, family [0] 0)] []
    (QBind [binding 0 0]
      (QNode 0 (QMore (QHole 0 [binding 0 0])
        (QMore (QHole 1 [binding 0 0]) QEmpty)))) = true.
Proof. reflexivity. Qed.

Theorem unrelated_ambient_binder_is_not_required_as_an_argument :
  shape_check [0] [(0, family [0] 0)] [binding 1 0]
    (QBind [binding 0 0] (QHole 0 [binding 0 0])) = true.
Proof. reflexivity. Qed.

Theorem extraction_has_unique_shape : forall left right first second,
  extract_pair left right = Some first ->
  extract_pair left right = Some second -> first = second.
Proof. intros. congruence. Qed.

Theorem accepted_family_roster_is_exact : forall categories declarations ambient shape,
  shape_check categories declarations ambient shape = true ->
  Permutation (family_ids shape) (map fst declarations).
Proof.
  intros. apply NoDup_Permutation.
  - eapply accepted_shape_has_unique_family_occurrences; eauto.
  - eapply accepted_shape_has_unique_declarations; eauto.
  - intros name. split.
    + eapply accepted_shape_has_no_undeclared_family; eauto.
    + eapply accepted_shape_uses_every_declared_family; eauto.
Qed.

Fixpoint ordinary_names (shape : Shape) : list nat :=
  match shape with
  | QMeta name => [name]
  | QBound _ | QHole _ _ => []
  | QNode _ children => ordinary_names_many children
  | QBind _ body => ordinary_names body
  end
with ordinary_names_many (shapes : Shapes) : list nat :=
  match shapes with
  | QEmpty => []
  | QMore head tail => ordinary_names head ++ ordinary_names_many tail
  end.

Fixpoint hole_names (shape : Shape) : list nat :=
  match shape with
  | QMeta _ | QBound _ => []
  | QHole family_id _ => [family_id]
  | QNode _ children => hole_names_many children
  | QBind _ body => hole_names body
  end
with hole_names_many (shapes : Shapes) : list nat :=
  match shapes with
  | QEmpty => []
  | QMore head tail => hole_names head ++ hole_names_many tail
  end.

Fixpoint lower (names : nat -> nat) (shape : Shape) : Shape :=
  match shape with
  | QMeta name => QMeta name
  | QBound reference => QBound reference
  | QNode label children => QNode label (lower_many names children)
  | QBind binders body => QBind binders (lower names body)
  | QHole family_id _ => QMeta (names family_id)
  end
with lower_many (names : nat -> nat) (shapes : Shapes) : Shapes :=
  match shapes with
  | QEmpty => QEmpty
  | QMore head tail => QMore (lower names head) (lower_many names tail)
  end.

Lemma lowering_instantiation_mutual :
  (forall shape names ordinary endpoints combined unused,
    (forall name, In name (ordinary_names shape) -> combined name = ordinary name) ->
    (forall family_id, In family_id (hole_names shape) ->
      combined (names family_id) = endpoints family_id) ->
    instantiate combined unused (lower names shape) = instantiate ordinary endpoints shape) /\
  (forall shapes names ordinary endpoints combined unused,
    (forall name, In name (ordinary_names_many shapes) -> combined name = ordinary name) ->
    (forall family_id, In family_id (hole_names_many shapes) ->
      combined (names family_id) = endpoints family_id) ->
    instantiates combined unused (lower_many names shapes) = instantiates ordinary endpoints shapes).
Proof.
  apply shape_mutual.
  - intros. simpl. apply H. simpl. auto.
  - intros. reflexivity.
  - intros label children IH names ordinary endpoints combined unused Hordinary Hholes.
    simpl in *. now rewrite IH with (ordinary := ordinary) (endpoints := endpoints).
  - intros binders body IH names ordinary endpoints combined unused Hordinary Hholes.
    simpl in *. now rewrite IH with (ordinary := ordinary) (endpoints := endpoints).
  - intros family_id arguments names ordinary endpoints combined unused Hordinary Hholes.
    simpl. apply Hholes. simpl. auto.
  - intros. reflexivity.
  - intros head IHhead tail IHtail names ordinary endpoints combined unused Hordinary Hholes.
    simpl in *. rewrite IHhead with (ordinary := ordinary) (endpoints := endpoints).
    + rewrite IHtail with (ordinary := ordinary) (endpoints := endpoints); [reflexivity| |].
      * intros. apply Hordinary. apply in_or_app. auto.
      * intros. apply Hholes. apply in_or_app. auto.
    + intros. apply Hordinary. apply in_or_app. auto.
    + intros. apply Hholes. apply in_or_app. auto.
Qed.

Theorem lowering_preserves_instantiation :
  forall shape names ordinary endpoints combined unused,
  (forall name, In name (ordinary_names shape) -> combined name = ordinary name) ->
  (forall family_id, In family_id (hole_names shape) ->
    combined (names family_id) = endpoints family_id) ->
  instantiate combined unused (lower names shape) = instantiate ordinary endpoints shape.
Proof. apply (proj1 lowering_instantiation_mutual). Qed.

Lemma lowering_removes_holes_mutual :
  (forall shape names, hole_names (lower names shape) = []) /\
  (forall shapes names, hole_names_many (lower_many names shapes) = []).
Proof.
  apply shape_mutual; intros; simpl; try reflexivity.
  - apply H.
  - apply H.
  - now rewrite H, H0.
Qed.

Theorem lowering_removes_every_family_projection : forall shape names,
  hole_names (lower names shape) = [].
Proof. apply (proj1 lowering_removes_holes_mutual). Qed.

Definition fresh_base authored := S (fold_right Nat.max 0 authored).
Definition source_name authored family_id := fresh_base authored + 2 * family_id.
Definition target_name authored family_id := S (source_name authored family_id).

Theorem generated_source_avoids_authored_names : forall authored family_id,
  ~ In (source_name authored family_id) authored.
Proof.
  intros authored family_id Hin. apply member_bounded_by_maximum in Hin.
  unfold source_name, fresh_base in Hin. lia.
Qed.

Theorem generated_target_avoids_authored_names : forall authored family_id,
  ~ In (target_name authored family_id) authored.
Proof.
  intros authored family_id Hin. apply member_bounded_by_maximum in Hin.
  unfold target_name, source_name, fresh_base in Hin. lia.
Qed.

Theorem generated_source_names_are_injective : forall authored left right,
  source_name authored left = source_name authored right -> left = right.
Proof. intros. unfold source_name in H. lia. Qed.

Theorem generated_target_names_are_injective : forall authored left right,
  target_name authored left = target_name authored right -> left = right.
Proof. intros. unfold target_name, source_name in H. lia. Qed.

Theorem generated_source_and_target_names_are_disjoint : forall authored left right,
  source_name authored left <> target_name authored right.
Proof. intros. unfold source_name, target_name. unfold source_name. lia. Qed.

Inductive CoreMatches (environment : Environment) : Shape -> Value -> Prop :=
| matches_meta : forall name value,
    environment name = Some value -> CoreMatches environment (QMeta name) value
| matches_bound : forall reference,
    CoreMatches environment (QBound reference) (Bound reference)
| matches_node : forall label children values,
    CoreMatchesMany environment children values ->
    CoreMatches environment (QNode label children) (Node label values)
| matches_bind : forall binders body value,
    CoreMatches environment body value ->
    CoreMatches environment (QBind binders body) (Bind binders value)
with CoreMatchesMany (environment : Environment) : Shapes -> list Value -> Prop :=
| matches_empty : CoreMatchesMany environment QEmpty []
| matches_more : forall head tail value values,
    CoreMatches environment head value ->
    CoreMatchesMany environment tail values ->
    CoreMatchesMany environment (QMore head tail) (value :: values).

Lemma core_matching_instantiation_mutual :
  (forall shape environment value,
    CoreMatches environment shape value <->
    instantiate environment (fun _ => None) shape = Some value) /\
  (forall shapes environment values,
    CoreMatchesMany environment shapes values <->
    instantiates environment (fun _ => None) shapes = Some values).
Proof.
  apply shape_mutual.
  - intros. simpl. split.
    + intros H. inversion H. assumption.
    + constructor. assumption.
  - intros. simpl. split.
    + intros H. inversion H. reflexivity.
    + intros H. inversion H. constructor.
  - intros label children IH environment value. simpl. split.
    + intros H. inversion H; subst.
      match goal with Hchildren : CoreMatchesMany _ _ _ |- _ =>
        apply IH in Hchildren; now rewrite Hchildren end.
    + destruct (instantiates environment (fun _ => None) children) eqn:Hchildren;
        intros H; inversion H; subst.
      constructor. now apply IH.
  - intros binders body IH environment value. simpl. split.
    + intros H. inversion H; subst.
      match goal with Hbody : CoreMatches _ _ _ |- _ =>
        apply IH in Hbody; now rewrite Hbody end.
    + destruct (instantiate environment (fun _ => None) body) eqn:Hbody;
        intros H; inversion H; subst.
      constructor. now apply IH.
  - intros. simpl. split; intros H; [inversion H|discriminate].
  - intros. simpl. split; intros H; inversion H; subst; constructor.
  - intros head IHhead tail IHtail environment values. simpl. split.
    + intros H. inversion H; subst.
      match goal with Hhead : CoreMatches _ _ _, Htail : CoreMatchesMany _ _ _ |- _ =>
        apply IHhead in Hhead; apply IHtail in Htail; now rewrite Hhead, Htail end.
    + destruct (instantiate environment (fun _ => None) head) eqn:Hhead; [|discriminate].
      destruct (instantiates environment (fun _ => None) tail) eqn:Htail; [|discriminate].
      intros H. inversion H; subst. constructor; [now apply IHhead|now apply IHtail].
Qed.

Theorem lowered_matching_extracts_exact_family_endpoints :
  forall shape names ordinary endpoints combined value,
  (forall name, In name (ordinary_names shape) -> combined name = ordinary name) ->
  (forall family_id, In family_id (hole_names shape) ->
    combined (names family_id) = endpoints family_id) ->
  (CoreMatches combined (lower names shape) value <->
    instantiate ordinary endpoints shape = Some value).
Proof.
  intros. rewrite (proj1 core_matching_instantiation_mutual).
  now rewrite lowering_preserves_instantiation with (ordinary := ordinary) (endpoints := endpoints).
Qed.

End RewriteFamilyExtraction.

Print Assumptions RewriteFamilyExtraction.extraction_exactly_preserves_both_authored_sides.
Print Assumptions RewriteFamilyExtraction.extraction_preserves_constructor_arity.
Print Assumptions RewriteFamilyExtraction.extraction_rejects_changed_ordinary_metavariable.
Print Assumptions RewriteFamilyExtraction.extraction_rejects_changed_lexical_arguments.
Print Assumptions RewriteFamilyExtraction.extraction_commutes_with_ordinary_instantiation.
Print Assumptions RewriteFamilyExtraction.accepted_shape_has_unique_family_occurrences.
Print Assumptions RewriteFamilyExtraction.accepted_shape_has_unique_declarations.
Print Assumptions RewriteFamilyExtraction.accepted_shape_uses_every_declared_family.
Print Assumptions RewriteFamilyExtraction.accepted_occurrence_has_exact_scoped_family.
Print Assumptions RewriteFamilyExtraction.accepted_shape_has_no_undeclared_family.
Print Assumptions RewriteFamilyExtraction.two_families_may_share_an_introduced_binder.
Print Assumptions RewriteFamilyExtraction.unrelated_ambient_binder_is_not_required_as_an_argument.
Print Assumptions RewriteFamilyExtraction.extraction_has_unique_shape.
Print Assumptions RewriteFamilyExtraction.accepted_family_roster_is_exact.
Print Assumptions RewriteFamilyExtraction.lowering_preserves_instantiation.
Print Assumptions RewriteFamilyExtraction.lowering_removes_every_family_projection.
Print Assumptions RewriteFamilyExtraction.generated_source_avoids_authored_names.
Print Assumptions RewriteFamilyExtraction.generated_target_avoids_authored_names.
Print Assumptions RewriteFamilyExtraction.generated_source_names_are_injective.
Print Assumptions RewriteFamilyExtraction.generated_target_names_are_injective.
Print Assumptions RewriteFamilyExtraction.generated_source_and_target_names_are_disjoint.
Print Assumptions RewriteFamilyExtraction.lowered_matching_extracts_exact_family_endpoints.
