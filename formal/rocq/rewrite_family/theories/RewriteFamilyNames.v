From Stdlib Require Import List Bool PeanoNat Lia Arith.Compare_dec.
Require Import RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyBoundary.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization
  RewriteFamilyExtraction.RewriteFamilyExtraction RewriteFamilyBoundary.RewriteFamilyBoundary.

Module RewriteFamilyNames.

Section AuthoredCensus.

Variable binder_spelling : Binding -> nat.
Variable family_spelling : nat -> nat.

Fixpoint surface_names (surface : Surface) : list nat :=
  match surface with
  | SMeta name => [name]
  | SBound reference => [binder_spelling reference]
  | SNode _ children => surfaces_names children
  | SBind binders body => map binder_spelling binders ++ surface_names body
  | SProjection _ family_id arguments => family_spelling family_id :: map binder_spelling arguments
  end
with surfaces_names (surfaces : Surfaces) : list nat :=
  match surfaces with
  | SEmpty => []
  | SMore head tail => surface_names head ++ surfaces_names tail
  end.

Inductive SurfaceMentions (name : nat) : Surface -> Prop :=
| MentionsMeta : SurfaceMentions name (SMeta name)
| MentionsBound : forall reference,
    name = binder_spelling reference -> SurfaceMentions name (SBound reference)
| MentionsNode : forall label children,
    SurfacesMention name children -> SurfaceMentions name (SNode label children)
| MentionsBinder : forall binders body,
    In name (map binder_spelling binders) -> SurfaceMentions name (SBind binders body)
| MentionsBody : forall binders body,
    SurfaceMentions name body -> SurfaceMentions name (SBind binders body)
| MentionsFamily : forall side family_id arguments,
    name = family_spelling family_id -> SurfaceMentions name (SProjection side family_id arguments)
| MentionsArgument : forall side family_id arguments,
    In name (map binder_spelling arguments) ->
    SurfaceMentions name (SProjection side family_id arguments)
with SurfacesMention (name : nat) : Surfaces -> Prop :=
| MentionsHead : forall head tail,
    SurfaceMentions name head -> SurfacesMention name (SMore head tail)
| MentionsTail : forall head tail,
    SurfacesMention name tail -> SurfacesMention name (SMore head tail).

Lemma surface_census_exact_mutual :
  (forall surface name, In name (surface_names surface) <-> SurfaceMentions name surface) /\
  (forall surfaces name, In name (surfaces_names surfaces) <-> SurfacesMention name surfaces).
Proof.
  apply surface_mutual; simpl; intros.
  - split.
    + intros [<-|Hfalse]; [constructor|contradiction].
    + intros Hmention. inversion Hmention. auto.
  - split.
    + intros [<-|Hfalse]; [constructor; reflexivity|contradiction].
    + intros Hmention. inversion Hmention; subst. auto.
  - rewrite H. split; [constructor; assumption|].
    intros Hmention. inversion Hmention. assumption.
  - rewrite in_app_iff, H. split.
    + intros [Hin|Hin]; [apply MentionsBinder|apply MentionsBody]; assumption.
    + intros Hmention. inversion Hmention; subst; auto.
  - split.
    + intros [<-|Hin]; [apply MentionsFamily; reflexivity|apply MentionsArgument; assumption].
    + intros Hmention. inversion Hmention; subst; auto.
  - split; [contradiction|intros Hmention; inversion Hmention].
  - rewrite in_app_iff, H, H0. split.
    + intros [Hin|Hin]; [apply MentionsHead|apply MentionsTail]; assumption.
    + intros Hmention. inversion Hmention; subst; auto.
Qed.

Theorem authored_pattern_census_is_exact : forall surface name,
  In name (surface_names surface) <-> SurfaceMentions name surface.
Proof. apply (proj1 surface_census_exact_mutual). Qed.

Theorem authored_census_includes_unused_binder_names : forall binders body name,
  In name (map binder_spelling binders) -> In name (surface_names (SBind binders body)).
Proof. intros. simpl. apply in_app_iff. auto. Qed.

Definition complete_names context left right premise_names :=
  context ++ surface_names left ++ surface_names right ++ premise_names.

Theorem whole_rule_census_covers_each_component : forall context left right premises name,
  In name (complete_names context left right premises) <->
  In name context \/ SurfaceMentions name left \/ SurfaceMentions name right \/ In name premises.
Proof.
  intros. unfold complete_names. rewrite !in_app_iff, !authored_pattern_census_is_exact.
  tauto.
Qed.

End AuthoredCensus.

Definition binder_name := source_name.

Theorem encoded_binder_names_avoid_all_authored_names : forall authored identity,
  ~ In (binder_name authored identity) authored.
Proof. apply generated_source_avoids_authored_names. Qed.

Theorem encoded_binder_names_are_injective : forall authored left right,
  binder_name authored left = binder_name authored right -> left = right.
Proof. apply generated_source_names_are_injective. Qed.

Theorem distinct_occurrences_keep_distinct_encoded_names : forall authored identities,
  NoDup identities -> NoDup (map (binder_name authored) identities).
Proof.
  intros. apply injective_map_preserves_distinctness; [|assumption].
  unfold Injective. apply encoded_binder_names_are_injective.
Qed.

Definition names_after_binders authored identities := authored ++ map (binder_name authored) identities.

Theorem generated_endpoints_avoid_encoded_binders : forall authored identities family_id identity,
  In identity identities ->
  source_name (names_after_binders authored identities) family_id <> binder_name authored identity /\
  target_name (names_after_binders authored identities) family_id <> binder_name authored identity.
Proof.
  intros. assert (Hin : In (binder_name authored identity) (names_after_binders authored identities)).
  { unfold names_after_binders. apply in_app_iff. right. now apply in_map. }
  split; intros Heq.
  - apply (generated_source_avoids_authored_names (names_after_binders authored identities) family_id).
    now rewrite Heq.
  - apply (generated_target_avoids_authored_names (names_after_binders authored identities) family_id).
    now rewrite Heq.
Qed.

Theorem encoded_names_preserve_family_admission :
  forall authored categories descriptor ambient introduced arguments,
  family_check categories descriptor ambient introduced arguments = true <->
  family_check categories descriptor
    (map (rename_binding (binder_name authored)) ambient)
    (map (rename_binding (binder_name authored)) introduced)
    (map (rename_binding (binder_name authored)) arguments) = true.
Proof.
  intros. apply injective_lexical_renaming_preserves_family_admission.
  unfold Injective. apply encoded_binder_names_are_injective.
Qed.

Fixpoint slot_for (name : nat) (roster : list nat) : option nat :=
  match roster with
  | [] => None
  | head :: tail =>
      if Nat.eqb name head then Some 0 else option_map S (slot_for name tail)
  end.

Theorem resolved_slot_contains_the_requested_name : forall roster name slot,
  slot_for name roster = Some slot -> nth_error roster slot = Some name.
Proof.
  induction roster as [|head tail IH]; intros name slot Hslot; simpl in Hslot; [discriminate|].
  destruct (Nat.eqb name head) eqn:Heq.
  - apply Nat.eqb_eq in Heq. inversion Hslot; subst. reflexivity.
  - destruct (slot_for name tail) eqn:Htail; inversion Hslot; subst. simpl. now apply IH.
Qed.

Theorem slot_resolution_succeeds_exactly_for_present_names : forall roster name,
  (exists slot, slot_for name roster = Some slot) <-> In name roster.
Proof.
  induction roster as [|head tail IH]; intros name; simpl.
  - split; [intros [slot Hslot]; discriminate|contradiction].
  - destruct (Nat.eqb name head) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. split; [auto|intros; exists 0; reflexivity].
    + apply Nat.eqb_neq in Heq. rewrite <- IH. split.
      * intros [slot Hslot]. destruct (slot_for name tail) eqn:Htail; [right; eauto|discriminate].
      * intros [Hhead|[slot Hslot]]; [congruence|].
        exists (S slot). now rewrite Hslot.
Qed.

Theorem different_names_cannot_share_a_resolved_slot : forall roster left right slot,
  slot_for left roster = Some slot -> slot_for right roster = Some slot -> left = right.
Proof.
  intros. apply resolved_slot_contains_the_requested_name in H.
  apply resolved_slot_contains_the_requested_name in H0. congruence.
Qed.

Theorem append_preserves_every_existing_slot : forall roster suffix name slot,
  slot_for name roster = Some slot -> slot_for name (roster ++ suffix) = Some slot.
Proof.
  induction roster as [|head tail IH]; intros suffix name slot Hslot; simpl in *; [discriminate|].
  destruct (Nat.eqb name head); [assumption|].
  destruct (slot_for name tail) eqn:Htail; inversion Hslot; subst.
  now rewrite (IH suffix name n Htail).
Qed.

Theorem appending_a_fresh_name_assigns_the_next_slot : forall roster name,
  ~ In name roster -> slot_for name (roster ++ [name]) = Some (length roster).
Proof.
  induction roster as [|head tail IH]; intros name Hfresh; simpl in *.
  - now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb name head) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hfresh. auto.
    + rewrite IH; [reflexivity|tauto].
Qed.

Definition intern_name name roster :=
  match slot_for name roster with
  | Some slot => (roster, slot)
  | None => (roster ++ [name], length roster)
  end.

Theorem interning_returns_a_slot_for_the_requested_name : forall name roster after slot,
  intern_name name roster = (after, slot) -> slot_for name after = Some slot.
Proof.
  intros name roster after slot Hintern. unfold intern_name in Hintern.
  destruct (slot_for name roster) eqn:Hslot; inversion Hintern; subst; [assumption|].
  apply appending_a_fresh_name_assigns_the_next_slot. intros Hin.
  apply slot_resolution_succeeds_exactly_for_present_names in Hin.
  destruct Hin as [found Hfound]. congruence.
Qed.

Theorem interning_preserves_all_prior_slots : forall name roster after slot old prior,
  intern_name name roster = (after, slot) -> slot_for old roster = Some prior ->
  slot_for old after = Some prior.
Proof.
  intros name roster after slot old prior Hintern Hprior. unfold intern_name in Hintern.
  destruct (slot_for name roster); inversion Hintern; subst; [assumption|].
  now apply append_preserves_every_existing_slot.
Qed.

Theorem interning_preserves_unique_name_rosters : forall name roster after slot,
  NoDup roster -> intern_name name roster = (after, slot) -> NoDup after.
Proof.
  intros name roster after slot Hdistinct Hintern. unfold intern_name in Hintern.
  destruct (slot_for name roster) eqn:Hslot; inversion Hintern; subst; [assumption|].
  apply NoDup_app. repeat split; try assumption.
  - constructor; [simpl; tauto|constructor].
  - intros item Hin Hlast. simpl in Hlast. destruct Hlast as [<-|Hfalse]; [|contradiction].
    apply slot_resolution_succeeds_exactly_for_present_names in Hin.
    destruct Hin as [found Hfound]. congruence.
Qed.

Theorem encoded_binder_slots_cannot_collapse : forall authored roster left right left_slot right_slot,
  slot_for (binder_name authored left) roster = Some left_slot ->
  slot_for (binder_name authored right) roster = Some right_slot ->
  left <> right -> left_slot <> right_slot.
Proof.
  intros authored roster left right left_slot right_slot Hleft Hright Hdifferent Heq.
  subst right_slot. apply Hdifferent. apply encoded_binder_names_are_injective with authored.
  eapply different_names_cannot_share_a_resolved_slot; eauto.
Qed.

Inductive SlotRole := InputRole | BinderRole | OtherRole (tag : nat).

Record TypedSlot := typed_slot {
  slot_name : nat;
  slot_sort : nat;
  slot_role : SlotRole
}.

Definition append_fresh_typed_slot categories capacity name category role roster :=
  if lt_dec (length roster) capacity then
    if in_dec Nat.eq_dec name (map slot_name roster) then None else
      if in_dec Nat.eq_dec category categories then
        Some (roster ++ [typed_slot name category role], length roster)
      else None
  else None.

Theorem fresh_typed_allocation_has_exact_admission :
  forall categories capacity name category role roster,
  append_fresh_typed_slot categories capacity name category role roster =
    Some (roster ++ [typed_slot name category role], length roster) <->
  length roster < capacity /\ ~ In name (map slot_name roster) /\ In category categories.
Proof.
  intros. unfold append_fresh_typed_slot.
  destruct (lt_dec (length roster) capacity);
    destruct (in_dec Nat.eq_dec name (map slot_name roster));
    destruct (in_dec Nat.eq_dec category categories); intuition discriminate.
Qed.

Theorem fresh_typed_allocation_preserves_every_existing_slot :
  forall categories capacity name category role roster after index prior previous,
  append_fresh_typed_slot categories capacity name category role roster = Some (after, index) ->
  nth_error roster prior = Some previous -> nth_error after prior = Some previous.
Proof.
  intros categories capacity name category role roster after index prior previous Happend Hprior.
  unfold append_fresh_typed_slot in Happend.
  destruct (lt_dec _ _); [|discriminate].
  destruct (in_dec Nat.eq_dec name _); [discriminate|].
  destruct (in_dec Nat.eq_dec category _); inversion Happend; subst.
  rewrite nth_error_app1; [assumption|].
  apply nth_error_Some. congruence.
Qed.

Theorem fresh_typed_allocation_retains_requested_sort_and_role :
  forall categories capacity name category role roster after index,
  append_fresh_typed_slot categories capacity name category role roster = Some (after, index) ->
  nth_error after index = Some (typed_slot name category role).
Proof.
  intros categories capacity name category role roster after index Happend.
  unfold append_fresh_typed_slot in Happend.
  destruct (lt_dec _ _); [|discriminate].
  destruct (in_dec Nat.eq_dec name _); [discriminate|].
  destruct (in_dec Nat.eq_dec category _); inversion Happend; subst.
  rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Theorem full_slot_capacity_refuses_fresh_allocation :
  forall categories capacity name category role roster,
  capacity <= length roster ->
  append_fresh_typed_slot categories capacity name category role roster = None.
Proof. intros. unfold append_fresh_typed_slot. destruct (lt_dec _ _); [lia|reflexivity]. Qed.

Definition slot_role_eq_dec : forall left right : SlotRole, {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition constrain_typed_input category requested old :=
  if Nat.eq_dec category (slot_sort old) then
    match slot_role old, requested with
    | InputRole, _ => Some (typed_slot (slot_name old) category requested)
    | BinderRole, InputRole => Some old
    | previous, _ => if slot_role_eq_dec previous requested then Some old else None
    end
  else None.

Theorem existing_binder_references_keep_the_binder_role : forall name category,
  constrain_typed_input category InputRole (typed_slot name category BinderRole) =
    Some (typed_slot name category BinderRole).
Proof. intros. unfold constrain_typed_input. simpl. destruct (Nat.eq_dec _ _); congruence. Qed.

Theorem existing_inputs_use_the_requested_role : forall name category role,
  constrain_typed_input category role (typed_slot name category InputRole) =
    Some (typed_slot name category role).
Proof. intros. unfold constrain_typed_input. simpl. destruct (Nat.eq_dec _ _); congruence. Qed.

Theorem conflicting_slot_sorts_are_refused : forall name existing requested role wanted,
  existing <> requested ->
  constrain_typed_input requested wanted (typed_slot name existing role) = None.
Proof. intros. unfold constrain_typed_input. simpl. destruct (Nat.eq_dec _ _); congruence. Qed.

Definition spelling_is_unique spelling identities identity :=
  forallb (fun other => negb (Nat.eqb (spelling other) (spelling identity)) ||
    Nat.eqb other identity) identities.

Lemma spelling_uniqueness_is_exact : forall spelling identities identity,
  spelling_is_unique spelling identities identity = true <->
  forall other, In other identities -> spelling other = spelling identity -> other = identity.
Proof.
  intros. unfold spelling_is_unique. rewrite forallb_forall. split.
  - intros Hunique other Hin Heq. specialize (Hunique other Hin).
    rewrite Heq, Nat.eqb_refl in Hunique. simpl in Hunique. now apply Nat.eqb_eq.
  - intros Hunique other Hin. destruct (Nat.eqb (spelling other) (spelling identity)) eqn:Heq;
      simpl; [|reflexivity].
    apply Nat.eqb_eq. apply Hunique; [assumption|now apply Nat.eqb_eq].
Qed.

Definition selective_name authored spelling identities identity :=
  if spelling_is_unique spelling identities identity then spelling identity
  else binder_name authored identity.

Theorem selective_encoding_preserves_unique_binder_spellings :
  forall authored spelling identities identity,
  (forall other, In other identities -> spelling other = spelling identity -> other = identity) ->
  selective_name authored spelling identities identity = spelling identity.
Proof.
  intros. apply spelling_uniqueness_is_exact in H. unfold selective_name. now rewrite H.
Qed.

Theorem repeated_spellings_require_distinct_encoded_names :
  forall authored spelling identities left right,
  In left identities -> In right identities -> left <> right -> spelling left = spelling right ->
  selective_name authored spelling identities left = binder_name authored left /\
  selective_name authored spelling identities right = binder_name authored right.
Proof.
  intros authored spelling identities left right Hleft Hright Hdifferent Hsame.
  assert (Hnotleft : spelling_is_unique spelling identities left = false).
  { destruct (spelling_is_unique spelling identities left) eqn:Hunique; [|reflexivity].
    rewrite spelling_uniqueness_is_exact in Hunique. exfalso. apply Hdifferent.
    symmetry. apply Hunique; auto. }
  assert (Hnotright : spelling_is_unique spelling identities right = false).
  { destruct (spelling_is_unique spelling identities right) eqn:Hunique; [|reflexivity].
    rewrite spelling_uniqueness_is_exact in Hunique. exfalso. apply Hdifferent.
    apply Hunique; auto. }
  unfold selective_name. now rewrite Hnotleft, Hnotright.
Qed.

Theorem selective_encoding_is_injective_on_the_binder_roster :
  forall authored spelling identities,
  (forall identity, In identity identities -> In (spelling identity) authored) ->
  forall left right, In left identities -> In right identities ->
  selective_name authored spelling identities left = selective_name authored spelling identities right ->
  left = right.
Proof.
  intros authored spelling identities Hcensus left right Hleft Hright Heq.
  unfold selective_name in Heq.
  destruct (spelling_is_unique spelling identities left) eqn:Huniqueleft;
    destruct (spelling_is_unique spelling identities right) eqn:Huniqueright.
  - rewrite spelling_uniqueness_is_exact in Huniqueright. now apply Huniqueright.
  - exfalso. apply (encoded_binder_names_avoid_all_authored_names authored right).
    rewrite <- Heq. now apply Hcensus.
  - exfalso. apply (encoded_binder_names_avoid_all_authored_names authored left).
    rewrite Heq. now apply Hcensus.
  - now apply encoded_binder_names_are_injective in Heq.
Qed.

Theorem preserved_authored_alias_has_no_new_binder_collision :
  forall authored spelling identities identity name,
  In name authored -> selective_name authored spelling identities identity = name ->
  spelling_is_unique spelling identities identity = true /\ spelling identity = name.
Proof.
  intros authored spelling identities identity name Hin Heq.
  unfold selective_name in Heq. destruct (spelling_is_unique _ _ _) eqn:Hunique; [auto|].
  exfalso. apply (encoded_binder_names_avoid_all_authored_names authored identity). now rewrite Heq.
Qed.

Definition external_names_are_clear spelling identities external :=
  forallb (fun identity => spelling_is_unique spelling identities identity ||
    negb (existsb (Nat.eqb (spelling identity)) external)) identities.

Theorem accepted_external_references_keep_their_exact_binder_names :
  forall authored spelling identities external identity,
  external_names_are_clear spelling identities external = true ->
  In identity identities -> In (spelling identity) external ->
  selective_name authored spelling identities identity = spelling identity.
Proof.
  intros authored spelling identities external identity Hclear Hin Hexternal.
  unfold external_names_are_clear in Hclear. apply forallb_forall with (x := identity) in Hclear;
    [|assumption].
  apply category_member_spec in Hexternal. rewrite Hexternal in Hclear. simpl in Hclear.
  rewrite orb_false_r in Hclear. unfold selective_name. now rewrite Hclear.
Qed.

Theorem ambiguous_external_references_are_refused :
  forall spelling identities external left right,
  In left identities -> In right identities -> left <> right -> spelling left = spelling right ->
  In (spelling left) external -> external_names_are_clear spelling identities external = false.
Proof.
  intros spelling identities external left right Hleft Hright Hdifferent Hsame Hexternal.
  destruct (external_names_are_clear spelling identities external) eqn:Hclear; [|reflexivity].
  unfold external_names_are_clear in Hclear. apply forallb_forall with (x := left) in Hclear;
    [|assumption].
  apply category_member_spec in Hexternal. rewrite Hexternal, orb_false_r in Hclear.
  rewrite spelling_uniqueness_is_exact in Hclear. exfalso. apply Hdifferent.
  symmetry. apply Hclear; auto.
Qed.

Theorem selective_encoded_binders_have_distinct_compiler_slots :
  forall authored spelling identities roster left right left_slot right_slot,
  (forall identity, In identity identities -> In (spelling identity) authored) ->
  In left identities -> In right identities -> left <> right ->
  slot_for (selective_name authored spelling identities left) roster = Some left_slot ->
  slot_for (selective_name authored spelling identities right) roster = Some right_slot ->
  left_slot <> right_slot.
Proof.
  intros authored spelling identities roster left right left_slot right_slot
    Hcensus Hleft Hright Hdifferent Hleftslot Hrightslot Heq. subst right_slot.
  apply Hdifferent. eapply selective_encoding_is_injective_on_the_binder_roster; eauto.
  eapply different_names_cannot_share_a_resolved_slot; eauto.
Qed.

End RewriteFamilyNames.

Print Assumptions RewriteFamilyNames.authored_pattern_census_is_exact.
Print Assumptions RewriteFamilyNames.authored_census_includes_unused_binder_names.
Print Assumptions RewriteFamilyNames.whole_rule_census_covers_each_component.
Print Assumptions RewriteFamilyNames.encoded_binder_names_avoid_all_authored_names.
Print Assumptions RewriteFamilyNames.encoded_binder_names_are_injective.
Print Assumptions RewriteFamilyNames.distinct_occurrences_keep_distinct_encoded_names.
Print Assumptions RewriteFamilyNames.generated_endpoints_avoid_encoded_binders.
Print Assumptions RewriteFamilyNames.encoded_names_preserve_family_admission.
Print Assumptions RewriteFamilyNames.resolved_slot_contains_the_requested_name.
Print Assumptions RewriteFamilyNames.slot_resolution_succeeds_exactly_for_present_names.
Print Assumptions RewriteFamilyNames.different_names_cannot_share_a_resolved_slot.
Print Assumptions RewriteFamilyNames.append_preserves_every_existing_slot.
Print Assumptions RewriteFamilyNames.appending_a_fresh_name_assigns_the_next_slot.
Print Assumptions RewriteFamilyNames.interning_returns_a_slot_for_the_requested_name.
Print Assumptions RewriteFamilyNames.interning_preserves_all_prior_slots.
Print Assumptions RewriteFamilyNames.interning_preserves_unique_name_rosters.
Print Assumptions RewriteFamilyNames.encoded_binder_slots_cannot_collapse.
Print Assumptions RewriteFamilyNames.fresh_typed_allocation_has_exact_admission.
Print Assumptions RewriteFamilyNames.fresh_typed_allocation_preserves_every_existing_slot.
Print Assumptions RewriteFamilyNames.fresh_typed_allocation_retains_requested_sort_and_role.
Print Assumptions RewriteFamilyNames.full_slot_capacity_refuses_fresh_allocation.
Print Assumptions RewriteFamilyNames.existing_binder_references_keep_the_binder_role.
Print Assumptions RewriteFamilyNames.existing_inputs_use_the_requested_role.
Print Assumptions RewriteFamilyNames.conflicting_slot_sorts_are_refused.
Print Assumptions RewriteFamilyNames.selective_encoding_preserves_unique_binder_spellings.
Print Assumptions RewriteFamilyNames.repeated_spellings_require_distinct_encoded_names.
Print Assumptions RewriteFamilyNames.selective_encoding_is_injective_on_the_binder_roster.
Print Assumptions RewriteFamilyNames.preserved_authored_alias_has_no_new_binder_collision.
Print Assumptions RewriteFamilyNames.accepted_external_references_keep_their_exact_binder_names.
Print Assumptions RewriteFamilyNames.ambiguous_external_references_are_refused.
Print Assumptions RewriteFamilyNames.selective_encoded_binders_have_distinct_compiler_slots.
