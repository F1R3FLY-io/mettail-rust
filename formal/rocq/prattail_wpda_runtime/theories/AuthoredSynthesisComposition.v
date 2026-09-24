(** Owned-adapter composition, not another synthesis/normalization controller.

    Concrete source obligations: grammar_core_bridge.rs appends productions in
    RuleSpec occurrence order, including auxiliary collection rules appended by
    the macro bridge. The caller retains the exact original production-occurrence
    roster before that augmentation; missing authored handles must not be used as
    a filtering heuristic. authored_declarations.rs validates Core/header/bindings
    and accepts an explicitly ordered rule roster.
    macros/wpda_codegen/tables.rs enumerates INSIDE each category bucket. Such a
    local ordinal is not a Core ProductionId. Equal authored handles may occur
    in distinct productions with different metadata; those occurrences remain
    distinct after normalization and grouping.

    The proposed Rust payload has only current RuleId and User(occurrence) versus
    Synthetic provenance. No recipe, source AST, cloned Production or synthetic
    ProductionId is stored in it. The source Core is borrowed immutably; the one
    session and caller policy are consumed/rebuilt only on success. The model's
    owner also includes worker-private rows, which need not be adapter fields.

    Synthetic observation below is a mathematical reader projection. Its local
    obligations are precise: old payload observations survive a checked arena
    extension; a successful materializer's returned handle reads the supplied
    original recipe. AuthoredSyntheticMaterialization supplies the actual typed
    append/name/parameter/syntax reader laws. This file does not claim arbitrary
    Rust identifier admission from strings or decoder/semantic-image parity.

    Existing SyntheticRuleAdmission proves the concrete source schedule and
    source-event fold. We instantiate its actual-owner publication theorem;
    no completed rows are chosen externally. Each callback's LOCAL concrete
    row relation below must be discharged by the eventual adapter. Successful
    observation results (first-var, source metadata, labels/binder predicates)
    must be the original helper observations, not guesses or cached classifiers.

    The single policy is opaque because GrammarLimits is not a compilation-work
    policy. Every wrapper forwards its incoming policy value and returns only
    the nested operation's returned value. The existing admission model's debit
    counter is ghost accounting, not permission for a second runtime budget or
    reset. A production caller still owes finite source staging/one initial
    store-copy admission and charges nested helper/materializer sites. No RSS,
    universal allocator, full descriptor or installed-parser cutover claim.
*)
From Stdlib Require Import List String Arith Lia.
From PrattailWpdaRuntime Require Import SyntheticRuleProjection SyntheticRuleAdmission
  AuthoredRuleStoreProjection AuthoredRuleTransportProjection
  AuthoredNormalizationMaterialization AuthoredSyntheticMaterialization.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredSynthesisComposition.
Module P := SyntheticRuleProjection.SyntheticRuleProjection.
Module W := SyntheticRuleAdmission.SyntheticRuleAdmission.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module N := AuthoredNormalizationMaterialization.AuthoredNormalizationMaterialization.
Module M := AuthoredSyntheticMaterialization.AuthoredSyntheticMaterialization.
Definition RuleId := A.Handle A.RuleTag.

Inductive Origin := UserOccurrence (global_index : nat) | SyntheticOrigin.
Record Payload := { current_rule : RuleId; origin : Origin }.
Definition replace_current payload next := {| current_rule := next; origin := origin payload |}.
Definition SyntheticPayload id := {| current_rule := id; origin := SyntheticOrigin |}.

Section SourceAndOwner.
Context {Metadata Policy : Type}.
Record Production := { authored : option RuleId; metadata : Metadata }.
Record Source := { source_arena : list A.Node; productions : list Production }.
Record Owner := {
  source : Source;
  session : N.Session;
  policy : Policy;
  private_rows : list (list Payload)
}.
Definition start core initial_policy category_count :=
  {| source := core; session := N.consume (source_arena core); policy := initial_policy;
     private_rows := repeat [] category_count |}.

(** A production occurrence, never an arena-wide enumeration of Rule nodes.
    Missing associations and wrong tags refuse; duplicate handles do not. *)
Definition checked_user core index := match nth_error (productions core) index with
| None => None
| Some production => match authored production with
  | None => None
  | Some id => match N.original_rule (N.consume (source_arena core)) id with
    | None => None
    | Some _ => Some {| current_rule := id; origin := UserOccurrence index |}
    end
  end end.
Definition original_roster core occurrences := map (checked_user core) occurrences.
Definition source_metadata core payload := match origin payload with
| UserOccurrence index => option_map metadata (nth_error (productions core) index)
| SyntheticOrigin => None end.
Definition bucket_payload (rows : list (list Payload)) category_index local_index :=
  match nth_error rows category_index with None => None | Some row => nth_error row local_index end.
Definition bucket_metadata core rows category_index local_index :=
  match bucket_payload rows category_index local_index with
  | None => None | Some payload => source_metadata core payload end.

Theorem admitted_user_retains_exact_source_occurrence : forall core index payload,
  checked_user core index = Some payload ->
  origin payload = UserOccurrence index /\
  exists production, nth_error (productions core) index = Some production /\
    authored production = Some (current_rule payload) /\
    source_metadata core payload = Some (metadata production).
Proof.
  intros core index payload H; unfold checked_user in H.
  destruct (nth_error (productions core) index) as [production|] eqn:At; [|discriminate].
  destruct (authored production) as [id|] eqn:Id; [|discriminate].
  destruct (N.original_rule (N.consume (source_arena core)) id); [|discriminate].
  inversion H; subst. split; [reflexivity|]. exists production; repeat split; auto.
  unfold source_metadata; cbn; now rewrite At.
Qed.
Theorem original_roster_keeps_order_and_duplicates : forall core occurrences position,
  nth_error (original_roster core occurrences) position =
    option_map (checked_user core) (nth_error occurrences position).
Proof. intros; apply A.map_nth_exact. Qed.
Theorem selected_occurrence_without_authored_rule_is_refused : forall core index production,
  nth_error (productions core) index = Some production -> authored production = None ->
  checked_user core index = None.
Proof. intros; unfold checked_user; now rewrite H, H0. Qed.
Theorem equal_authored_handles_do_not_merge_occurrences : forall core left right a b,
  checked_user core left = Some a -> checked_user core right = Some b ->
  left <> right -> a <> b.
Proof.
  intros core left right a b L R Different Equal; subst b.
  destruct (admitted_user_retains_exact_source_occurrence core left L) as [Left _].
  destruct (admitted_user_retains_exact_source_occurrence core right R) as [Right _].
  rewrite Left in Right; inversion Right; contradiction.
Qed.
Theorem replacing_current_preserves_origin_and_all_source_metadata : forall core payload id,
  origin (replace_current payload id) = origin payload /\
  source_metadata core (replace_current payload id) = source_metadata core payload.
Proof. intros; split; reflexivity. Qed.
Theorem local_ordinal_selects_payload_not_global_production :
  forall core rows category_index local_index payload global_index,
  bucket_payload rows category_index local_index = Some payload ->
  origin payload = UserOccurrence global_index ->
  bucket_metadata core rows category_index local_index =
    option_map metadata (nth_error (productions core) global_index).
Proof. intros; unfold bucket_metadata; rewrite H; unfold source_metadata; now rewrite H0. Qed.
Theorem synthetic_payload_has_no_fabricated_production : forall core id,
  source_metadata core (SyntheticPayload id) = None.
Proof. reflexivity. Qed.

Definition SessionExtends before after :=
  N.original_len after = N.original_len before /\
  exists suffix, N.private_store after = N.private_store before ++ suffix.
Theorem original_normalizer_commit_extends_session :
  forall before entries paid reserved original params syntax after id,
  N.publish_commit before entries paid reserved original params syntax = Some (after, id) ->
  SessionExtends before after.
Proof.
  intros; apply N.successful_session_preserves_original_bound_and_entire_prefix in H.
  destruct H as [Bound [Prefix _]].
  split; [exact Bound|eexists; exact Prefix].
Qed.
Theorem original_synthetic_commit_extends_same_session :
  forall before entries paid reserved label category items params syntax after id,
  M.publish_fresh before entries paid reserved label category items params syntax = Some (after, id) ->
  SessionExtends before after.
Proof.
  intros; apply M.successful_fresh_commit_preserves_original_bound_and_prefix in H.
  destruct H as [Bound Prefix].
  split; [exact Bound|eexists; exact Prefix].
Qed.
Theorem session_extension_composes_without_source_copy : forall a b c,
  SessionExtends a b -> SessionExtends b c -> SessionExtends a c.
Proof.
  intros a b c [B [x X]] [C [y Y]]. split; [congruence|].
  exists (x ++ y). rewrite Y, X. now rewrite app_assoc.
Qed.
Theorem every_prior_typed_node_survives_extension : forall before after index node,
  SessionExtends before after -> nth_error (N.private_store before) index = Some node ->
  nth_error (N.private_store after) index = Some node.
Proof.
  intros before after index node [_ [suffix ->]] At.
  rewrite nth_error_app1; [exact At|]. apply nth_error_Some. now rewrite At.
Qed.

(** Actual consuming-call wrappers. The operation receives the existing session
    and policy; no other state can be substituted. Only success rebuilds owner.
    Private rows are subsequently updated by the original shared worker. *)
Definition rebuild before after next_policy :=
  {| source := source before; session := after; policy := next_policy;
     private_rows := private_rows before |}.
Definition normalize_owned
    (call : N.Session -> RuleId -> Policy -> option (N.Session * RuleId * Policy)) before payload :=
  match origin payload with
  | SyntheticOrigin => None
  | UserOccurrence _ => match call (session before) (current_rule payload) (policy before) with
    | None => None
    | Some (after, id, next_policy) => Some (rebuild before after next_policy, replace_current payload id)
    end end.
Definition materialize_owned
    (call : N.Session -> P.Recipe -> Policy -> option (N.Session * RuleId * Policy)) before recipe :=
  match call (session before) recipe (policy before) with
  | None => None
  | Some (after, id, next_policy) => Some (rebuild before after next_policy, SyntheticPayload id)
  end.
Theorem normalization_forwards_one_policy_and_changes_only_current_handle :
  forall call before payload occurrence after id next_policy,
  origin payload = UserOccurrence occurrence ->
  call (session before) (current_rule payload) (policy before) = Some (after, id, next_policy) ->
  normalize_owned call before payload = Some (rebuild before after next_policy, replace_current payload id) /\
  policy (rebuild before after next_policy) = next_policy /\
  source (rebuild before after next_policy) = source before /\
  origin (replace_current payload id) = UserOccurrence occurrence.
Proof. intros; split; [unfold normalize_owned; now rewrite H, H0|]. repeat split; auto. Qed.
Theorem materialization_forwards_same_policy_and_tags_synthetic :
  forall call before recipe after id next_policy,
  call (session before) recipe (policy before) = Some (after, id, next_policy) ->
  materialize_owned call before recipe = Some (rebuild before after next_policy, SyntheticPayload id) /\
  policy (rebuild before after next_policy) = next_policy /\
  source (rebuild before after next_policy) = source before.
Proof. intros; split; [unfold materialize_owned; now rewrite H|]. split; reflexivity. Qed.
Theorem failed_normalization_exposes_no_owner_or_payload : forall call before payload occurrence,
  origin payload = UserOccurrence occurrence ->
  call (session before) (current_rule payload) (policy before) = None ->
  normalize_owned call before payload = None.
Proof. intros; unfold normalize_owned; now rewrite H, H0. Qed.
Theorem failed_materialization_exposes_no_owner_or_payload : forall call before recipe,
  call (session before) recipe (policy before) = None -> materialize_owned call before recipe = None.
Proof. intros; unfold materialize_owned; now rewrite H. Qed.

Section Observation.
Variable read_recipe : list A.Node -> RuleId -> P.Recipe.
Definition observe_payload arena payload : W.Stored := match origin payload with
| UserOccurrence occurrence => P.OriginalHandle occurrence
| SyntheticOrigin => P.Synthetic (read_recipe arena (current_rule payload)) end.
Definition observe owner := P.map_rows (observe_payload (N.private_store (session owner))) (private_rows owner).
Definition prior_observations_preserved before after := forall payload,
  In payload (List.concat (private_rows before)) ->
  observe_payload (N.private_store (session after)) payload =
    observe_payload (N.private_store (session before)) payload.
Definition CurrentHandleUpdate before after :=
  origin after = origin before /\
  (origin before = SyntheticOrigin -> current_rule after = current_rule before).
Lemma current_handle_update_preserves_observation : forall old_arena new_arena before after,
  CurrentHandleUpdate before after ->
  observe_payload new_arena before = observe_payload old_arena before ->
  observe_payload new_arena after = observe_payload old_arena before.
Proof.
  intros old_arena new_arena before after [Origin Handle] Stable.
  rewrite <- Stable. unfold observe_payload. rewrite Origin.
  destruct (origin before) eqn:Kind; [reflexivity|]. now rewrite (Handle eq_refl).
Qed.
Lemma current_handle_updates_preserve_row : forall old_arena new_arena left right,
  Forall2 CurrentHandleUpdate left right ->
  (forall payload, In payload left -> observe_payload new_arena payload = observe_payload old_arena payload) ->
  map (observe_payload new_arena) right = map (observe_payload old_arena) left.
Proof.
  intros old_arena new_arena left right Updates; induction Updates; intros Stable; cbn; [reflexivity|].
  f_equal.
  - eapply current_handle_update_preserves_observation; [exact H|apply Stable; now left].
  - apply IHUpdates; intros; apply Stable; now right.
Qed.
Lemma current_handle_updates_preserve_rows : forall old_arena new_arena left right,
  Forall2 (Forall2 CurrentHandleUpdate) left right ->
  (forall payload, In payload (List.concat left) -> observe_payload new_arena payload = observe_payload old_arena payload) ->
  P.map_rows (observe_payload new_arena) right = P.map_rows (observe_payload old_arena) left.
Proof.
  intros old_arena new_arena left right Updates; induction Updates; intros Stable; cbn [P.map_rows map]; [reflexivity|].
  f_equal.
  - apply current_handle_updates_preserve_row; [exact H|]. intros payload Member.
    apply Stable; cbn; apply in_or_app; now left.
  - apply IHUpdates; intros payload Member. apply Stable; cbn; apply in_or_app; now right.
Qed.
Lemma prior_observations_preserve_existing_rows : forall before after,
  prior_observations_preserved before after ->
  P.map_rows (observe_payload (N.private_store (session after))) (private_rows before) = observe before.
Proof.
  intros before after Stable; unfold P.map_rows, observe, P.map_rows.
  apply map_ext_in; intros row Row. apply map_ext_in; intros payload Member.
  apply Stable. apply in_concat. exists row; auto.
Qed.
Lemma user_normalization_does_not_change_semantic_occurrence : forall arena payload id occurrence,
  origin payload = UserOccurrence occurrence ->
  observe_payload arena (replace_current payload id) = observe_payload arena payload.
Proof. intros; unfold observe_payload, replace_current; cbn; now rewrite H. Qed.

(** Local row operations at the nine callback boundaries, not expected final
    rows. Insertions are exactly existing push_at and checked last_slot.
    Normalize/observations retain the projected row sequence; normalization's
    current-handle replacement law above explains why semantic User handles are
    stable even though the actual owned arena changes. Materialization must read
    back the recipe at its returned handle, not supply arbitrary output rows. *)
Variable categories : list string.
Variable user_category : nat -> string.
Definition LocalCallbackRows site before after :=
  match site with
  | W.Call (W.CloneUser occurrence) => exists payload index,
      checked_user (source before) occurrence = Some payload /\
      P.last_slot (user_category occurrence) categories = Some index /\
      private_rows after = P.push_at index payload (private_rows before) /\
      prior_observations_preserved before after
  | W.Call (W.Materialize recipe) => exists id index,
      P.last_slot (P.category recipe) categories = Some index /\
      read_recipe (N.private_store (session after)) id = recipe /\
      private_rows after = P.push_at index (SyntheticPayload id) (private_rows before) /\
      prior_observations_preserved before after
  | W.Call (W.NormalizeUser _) =>
      Forall2 (Forall2 CurrentHandleUpdate) (private_rows before) (private_rows after) /\
      prior_observations_preserved before after
  | _ => private_rows after = private_rows before /\ prior_observations_preserved before after
  end.
Theorem local_callback_rows_refine_existing_row_effect : forall site before after,
  LocalCallbackRows site before after ->
  observe after = W.callback_row_effect categories user_category (observe before) site.
Proof.
  intros site before after Correspond.
  assert (Unchanged : private_rows after = private_rows before ->
    prior_observations_preserved before after -> observe after = observe before).
  { intros Rows Stable. unfold observe at 1; rewrite Rows. now apply prior_observations_preserve_existing_rows. }
  destruct site; try (destruct Correspond as [Rows Stable]; now apply Unchanged).
  destruct callback; try (destruct Correspond as [Rows Stable]; now apply Unchanged).
  - destruct Correspond as [payload [index [Admitted [Slot [Rows Stable]]]]].
    apply admitted_user_retains_exact_source_occurrence in Admitted.
    destruct Admitted as [Origin _].
    unfold observe at 1; rewrite Rows, P.map_rows_push.
    rewrite (prior_observations_preserve_existing_rows Stable).
    unfold observe_payload; rewrite Origin.
    unfold W.callback_row_effect, P.view_user_step, P.append_view; now rewrite Slot.
  - destruct Correspond as [Updates Stable].
    unfold observe. eapply current_handle_updates_preserve_rows; [exact Updates|exact Stable].
  - destruct Correspond as [id [index [Slot [Read [Rows Stable]]]]].
    unfold observe at 1; rewrite Rows, P.map_rows_push.
    rewrite (prior_observations_preserve_existing_rows Stable).
    cbn [observe_payload SyntheticPayload origin current_rule]. rewrite Read.
    unfold W.callback_row_effect, P.append_view; now rewrite Slot.
Qed.

Section RunComposition.
Context {Error : Type}.
Variable cost : W.Event -> nat.
Variable reserved : W.Event -> bool.
Variable perform : W.Event -> Owner -> Owner + Error.
Theorem actual_owned_success_publishes_original_rows :
  forall first_var lower declarations users binders before after remaining next trace,
  (forall site a b, perform site a = inl b -> LocalCallbackRows site a b) ->
  observe before = repeat [] (List.length categories) ->
  W.run cost reserved perform
    (W.events (W.schedule categories user_category first_var lower declarations users binders)) before remaining =
    W.Finished after next trace ->
  W.publish observe (W.run cost reserved perform
    (W.events (W.schedule categories user_category first_var lower declarations users binders)) before remaining) =
  inl (after, @P.view_driver nat nat lower (fun h => h) (fun h => h) user_category first_var
    categories declarations users binders (repeat [] (List.length categories))).
Proof.
  intros first_var lower declarations users binders before after remaining next trace Local Empty Run.
  eapply W.successful_source_schedule_publishes_original_rows; [|exact Empty|exact Run].
  intros; apply local_callback_rows_refine_existing_row_effect. eapply Local; exact H.
Qed.
Theorem failed_owned_run_publishes_no_session_policy_or_rows : forall failure trace,
  @W.publish Owner Error observe (W.Stopped failure trace) = inr failure.
Proof. reflexivity. Qed.

(** Source/prefix preservation composes through the SAME admitted run. This is
    a local invariant obligation on each actual callback, not a chosen final
    owner. Synthetic/name appends use the session-extension laws above. *)
Theorem successful_run_preserves_source_and_original_prefix :
  (forall site a b, perform site a = inl b ->
    source b = source a /\ SessionExtends (session a) (session b)) ->
  forall sites before remaining after next trace,
  W.run cost reserved perform sites before remaining = W.Finished after next trace ->
  source after = source before /\ SessionExtends (session before) (session after).
Proof.
  intros Local sites; induction sites as [|site rest IH]; intros before remaining after next trace Run; cbn in Run.
  - inversion Run; subst. split; [reflexivity|]. split; [reflexivity|exists []; now rewrite app_nil_r].
  - destruct (ReconstructionWorkBudget.debit remaining (cost site)) as [middle|]; [|discriminate].
    destruct (reserved site); [|discriminate].
    destruct (perform site before) as [current|error] eqn:Call; [|discriminate].
    destruct (W.run cost reserved perform rest current middle) as [final last visited|failure visited] eqn:Tail;
      [|discriminate].
    destruct (Local site before current Call) as [Source First].
    destruct (IH current middle final last visited Tail) as [Rest Next].
    inversion Run; subst. split; [congruence|eapply session_extension_composes_without_source_copy; eauto].
Qed.
End RunComposition.
End Observation.
End SourceAndOwner.

Print Assumptions admitted_user_retains_exact_source_occurrence.
Print Assumptions original_roster_keeps_order_and_duplicates.
Print Assumptions selected_occurrence_without_authored_rule_is_refused.
Print Assumptions equal_authored_handles_do_not_merge_occurrences.
Print Assumptions replacing_current_preserves_origin_and_all_source_metadata.
Print Assumptions local_ordinal_selects_payload_not_global_production.
Print Assumptions synthetic_payload_has_no_fabricated_production.
Print Assumptions original_normalizer_commit_extends_session.
Print Assumptions original_synthetic_commit_extends_same_session.
Print Assumptions session_extension_composes_without_source_copy.
Print Assumptions every_prior_typed_node_survives_extension.
Print Assumptions normalization_forwards_one_policy_and_changes_only_current_handle.
Print Assumptions materialization_forwards_same_policy_and_tags_synthetic.
Print Assumptions failed_normalization_exposes_no_owner_or_payload.
Print Assumptions failed_materialization_exposes_no_owner_or_payload.
Print Assumptions user_normalization_does_not_change_semantic_occurrence.
Print Assumptions current_handle_update_preserves_observation.
Print Assumptions current_handle_updates_preserve_rows.
Print Assumptions local_callback_rows_refine_existing_row_effect.
Print Assumptions actual_owned_success_publishes_original_rows.
Print Assumptions failed_owned_run_publishes_no_session_policy_or_rows.
Print Assumptions successful_run_preserves_source_and_original_prefix.
End AuthoredSynthesisComposition.
