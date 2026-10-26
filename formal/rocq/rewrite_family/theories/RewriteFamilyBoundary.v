From Stdlib Require Import List Bool PeanoNat Lia.
Require Import RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyPremises.
Import ListNotations RewriteFamilyNormalization.RewriteFamilyNormalization
  RewriteFamilyExtraction.RewriteFamilyExtraction RewriteFamilyPremises.RewriteFamilyPremises.

Module RewriteFamilyBoundary.

Inductive RulePremise := AuthoredPremise (payload : nat) | FamilyPremise (item : Request).

Record Rule := rule {
  rule_identity : nat;
  rule_ordinary_context : list (nat * nat);
  rule_families : list (nat * Family);
  rule_left : Surface;
  rule_right : Surface;
  rule_premises : list RulePremise;
  rule_authored_names : list nat
}.

Definition normalize_rule categories ambient original :=
  match rule_families original with
  | [] => Some original
  | _ :: _ =>
      match extract_pair (rule_left original) (rule_right original) with
      | None => None
      | Some shape =>
          if shape_check categories (rule_families original) ambient shape then
            match build_requests (rule_authored_names original) ambient
              (rule_families original) (occurrences shape [] []) with
            | None => None
            | Some generated => Some (rule (rule_identity original)
                (rule_ordinary_context original ++
                  map (fun item => (request_source item, request_category item)) generated) []
                (render Source (lower (source_name (rule_authored_names original)) shape))
                (render Target (lower (target_name (rule_authored_names original)) shape))
                (rule_premises original ++ map FamilyPremise generated)
                (rule_authored_names original))
            end
          else None
      end
  end.

Theorem ordinary_rules_keep_exact_identity : forall categories ambient original,
  rule_families original = [] -> normalize_rule categories ambient original = Some original.
Proof. intros. unfold normalize_rule. now rewrite H. Qed.

Theorem ordinary_rules_may_have_different_sides :
  normalize_rule [] [] (rule 0 [] [] (SMeta 0) (SMeta 1) [] [0; 1]) =
    Some (rule 0 [] [] (SMeta 0) (SMeta 1) [] [0; 1]).
Proof. reflexivity. Qed.

Theorem normalized_rules_have_no_family_declarations : forall categories ambient original normalized,
  normalize_rule categories ambient original = Some normalized -> rule_families normalized = [].
Proof.
  intros categories ambient original normalized Hnormalized. unfold normalize_rule in Hnormalized.
  destruct (rule_families original) eqn:Hfamilies.
  - inversion Hnormalized; subst. exact Hfamilies.
  - destruct (extract_pair _ _) eqn:Hextract; [|discriminate].
    destruct (shape_check _ _ _ _) eqn:Hcheck; [|discriminate].
    destruct (build_requests _ _ _ _) eqn:Hbuild; inversion Hnormalized. reflexivity.
Qed.

Theorem normalization_is_idempotent : forall categories ambient original normalized,
  normalize_rule categories ambient original = Some normalized ->
  normalize_rule categories ambient normalized = Some normalized.
Proof.
  intros. apply ordinary_rules_keep_exact_identity.
  eapply normalized_rules_have_no_family_declarations; eauto.
Qed.

Theorem normalization_preserves_existing_rule_data : forall categories ambient original normalized,
  normalize_rule categories ambient original = Some normalized ->
  rule_identity normalized = rule_identity original /\
  rule_authored_names normalized = rule_authored_names original /\
  exists generated,
    rule_ordinary_context normalized = rule_ordinary_context original ++
      map (fun item => (request_source item, request_category item)) generated /\
    rule_premises normalized = rule_premises original ++ map FamilyPremise generated.
Proof.
  intros categories ambient original normalized Hnormalized. unfold normalize_rule in Hnormalized.
  destruct (rule_families original) eqn:Hfamilies.
  - inversion Hnormalized; subst. repeat split. exists []. now rewrite !app_nil_r.
  - destruct (extract_pair _ _) eqn:Hextract; [|discriminate].
    destruct (shape_check _ _ _ _) eqn:Hcheck; [|discriminate].
    destruct (build_requests _ _ _ _) eqn:Hbuild; inversion Hnormalized; subst.
    repeat split. exists l0. split; reflexivity.
Qed.

Definition publish_normalization categories ambient before original after :=
  match normalize_rule categories ambient original with
  | None => before ++ original :: after
  | Some normalized => before ++ normalized :: after
  end.

Theorem failed_normalization_keeps_the_entire_rule_store :
  forall categories ambient before original after,
  normalize_rule categories ambient original = None ->
  publish_normalization categories ambient before original after = before ++ original :: after.
Proof. intros. unfold publish_normalization. now rewrite H. Qed.

Theorem successful_normalization_changes_only_the_selected_rule :
  forall categories ambient before original after normalized,
  normalize_rule categories ambient original = Some normalized ->
  publish_normalization categories ambient before original after = before ++ normalized :: after.
Proof. intros. unfold publish_normalization. now rewrite H. Qed.

Fixpoint normalize_rules categories ambient originals :=
  match originals with
  | [] => Some []
  | head :: tail =>
      match normalize_rule categories ambient head, normalize_rules categories ambient tail with
      | Some normalized, Some rest => Some (normalized :: rest)
      | _, _ => None
      end
  end.

Definition publish_rules categories ambient originals :=
  match normalize_rules categories ambient originals with
  | Some normalized => normalized
  | None => originals
  end.

Theorem a_failed_batch_preserves_every_original_rule : forall categories ambient originals,
  normalize_rules categories ambient originals = None ->
  publish_rules categories ambient originals = originals.
Proof. intros. unfold publish_rules. now rewrite H. Qed.

Theorem successful_batch_has_a_checked_result_for_every_rule :
  forall categories ambient originals normalized,
  normalize_rules categories ambient originals = Some normalized ->
  Forall2 (fun original result => normalize_rule categories ambient original = Some result)
    originals normalized.
Proof.
  intros categories ambient originals. induction originals as [|head tail IH];
    intros normalized Hbatch; simpl in Hbatch.
  - inversion Hbatch. constructor.
  - destruct (normalize_rule categories ambient head) eqn:Hhead; [|discriminate].
    destruct (normalize_rules categories ambient tail) eqn:Htail; inversion Hbatch; subst.
    constructor; [exact Hhead|now apply IH].
Qed.

Definition SupportedBy (names : list nat) (environment : Environment) :=
  forall name value, environment name = Some value -> In name names.

Theorem generated_names_are_fresh_in_supported_environment :
  forall authored environment family_id,
  SupportedBy authored environment ->
  environment (source_name authored family_id) = None /\
  environment (target_name authored family_id) = None.
Proof.
  intros authored environment family_id Hsupport. split.
  - destruct (environment (source_name authored family_id)) eqn:Hlookup; [|reflexivity].
    exfalso. apply (generated_source_avoids_authored_names authored family_id).
    now apply Hsupport with v.
  - destruct (environment (target_name authored family_id)) eqn:Hlookup; [|reflexivity].
    exfalso. apply (generated_target_avoids_authored_names authored family_id).
    now apply Hsupport with v.
Qed.

Definition resolve_appended spelling scope := resolve_lexical spelling (rev scope).

Theorem appended_scope_resolves_the_nearest_binder :
  forall spelling identity category scope,
  resolve_appended spelling (scope ++ [named_binding spelling (binding identity category)]) =
    Some (binding identity category).
Proof.
  intros. unfold resolve_appended. rewrite rev_app_distr. simpl.
  apply nearest_lexical_binder_wins.
Qed.

Theorem leaving_a_binder_restores_outer_resolution : forall spelling outer introduced,
  resolve_appended spelling (removelast (outer ++ [introduced])) =
    resolve_appended spelling outer.
Proof. intros. now rewrite removelast_last. Qed.

Theorem appended_scope_retains_the_outer_binder_identity :
  forall spelling outer_identity inner_identity category scope,
  outer_identity <> inner_identity ->
  resolve_appended spelling
    (scope ++ [named_binding spelling (binding outer_identity category);
      named_binding spelling (binding inner_identity category)]) = Some (binding inner_identity category) /\
  resolve_appended spelling
    (scope ++ [named_binding spelling (binding outer_identity category)]) = Some (binding outer_identity category).
Proof.
  intros. split.
  - unfold resolve_appended. rewrite rev_app_distr. simpl. now rewrite Nat.eqb_refl.
  - apply appended_scope_resolves_the_nearest_binder.
Qed.

Definition Injective (rename : nat -> nat) := forall left right,
  rename left = rename right -> left = right.

Lemma renamed_binding_is_injective : forall rename,
  Injective rename -> forall left right,
  rename_binding rename left = rename_binding rename right -> left = right.
Proof.
  intros rename Hinjective [li lc] [ri rc] Hsame.
  unfold rename_binding in Hsame. simpl in Hsame. inversion Hsame.
  apply Hinjective in H0. now subst.
Qed.

Lemma injective_map_preserves_distinctness : forall rename names,
  Injective rename -> (NoDup (map rename names) <-> NoDup names).
Proof.
  intros rename names Hinjective. split; [apply NoDup_map_inv|].
  intros Hdistinct. induction Hdistinct; simpl; constructor; [|assumption].
  intros Hin. apply in_map_iff in Hin. destruct Hin as [other [Heq Hin]].
  apply Hinjective in Heq. subst other. contradiction.
Qed.

Lemma renamed_binding_membership_is_exact : forall rename item items,
  Injective rename ->
  (In (rename_binding rename item) (map (rename_binding rename) items) <-> In item items).
Proof.
  intros. split.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [other [Heq Hin]].
    apply renamed_binding_is_injective in Heq; [now subst|assumption].
  - apply in_map.
Qed.

Lemma renamed_binding_categories_are_unchanged : forall rename items,
  map binder_category (map (rename_binding rename) items) = map binder_category items.
Proof. intros. rewrite map_map. reflexivity. Qed.

Lemma renamed_scope_distinctness_is_exact : forall rename items,
  Injective rename ->
  (NoDup (map binder_identity (map (rename_binding rename) items)) <->
    NoDup (map binder_identity items)).
Proof.
  intros. rewrite map_map.
  change (NoDup (map (fun item => rename (binder_identity item)) items) <->
    NoDup (map binder_identity items)).
  rewrite <- map_map. now apply injective_map_preserves_distinctness.
Qed.

Theorem injective_lexical_renaming_preserves_family_admission :
  forall rename categories descriptor ambient introduced arguments,
  Injective rename ->
  (family_check categories descriptor ambient introduced arguments = true <->
    family_check categories descriptor
      (map (rename_binding rename) ambient) (map (rename_binding rename) introduced)
      (map (rename_binding rename) arguments) = true).
Proof.
  intros rename categories descriptor ambient introduced arguments Hinjective.
  rewrite !family_check_is_exact. unfold FamilyWellTyped.
  rewrite renamed_binding_categories_are_unchanged, <- map_app,
    !renamed_scope_distinctness_is_exact by assumption.
  split.
  - intros [Hcategories [Htypes [Hargs [Hscope [Hcoverage Hdistinct]]]]].
    repeat split; try assumption.
    + intros item Hin. apply in_map_iff in Hin. destruct Hin as [original [<- Hin]].
      apply in_map. now apply Hscope.
    + intros item Hin. apply in_map_iff in Hin. destruct Hin as [original [<- Hin]].
      apply in_map. now apply Hcoverage.
  - intros [Hcategories [Htypes [Hargs [Hscope [Hcoverage Hdistinct]]]]].
    repeat split; try assumption.
    + intros item Hin. apply (renamed_binding_membership_is_exact rename item _ Hinjective).
      apply Hscope. now apply in_map.
    + intros item Hin. apply (renamed_binding_membership_is_exact rename item _ Hinjective).
      apply Hcoverage. now apply in_map.
Qed.

End RewriteFamilyBoundary.

Print Assumptions RewriteFamilyBoundary.ordinary_rules_keep_exact_identity.
Print Assumptions RewriteFamilyBoundary.ordinary_rules_may_have_different_sides.
Print Assumptions RewriteFamilyBoundary.normalized_rules_have_no_family_declarations.
Print Assumptions RewriteFamilyBoundary.normalization_is_idempotent.
Print Assumptions RewriteFamilyBoundary.normalization_preserves_existing_rule_data.
Print Assumptions RewriteFamilyBoundary.failed_normalization_keeps_the_entire_rule_store.
Print Assumptions RewriteFamilyBoundary.successful_normalization_changes_only_the_selected_rule.
Print Assumptions RewriteFamilyBoundary.a_failed_batch_preserves_every_original_rule.
Print Assumptions RewriteFamilyBoundary.successful_batch_has_a_checked_result_for_every_rule.
Print Assumptions RewriteFamilyBoundary.generated_names_are_fresh_in_supported_environment.
Print Assumptions RewriteFamilyBoundary.appended_scope_resolves_the_nearest_binder.
Print Assumptions RewriteFamilyBoundary.leaving_a_binder_restores_outer_resolution.
Print Assumptions RewriteFamilyBoundary.appended_scope_retains_the_outer_binder_identity.
Print Assumptions RewriteFamilyBoundary.injective_lexical_renaming_preserves_family_admission.
