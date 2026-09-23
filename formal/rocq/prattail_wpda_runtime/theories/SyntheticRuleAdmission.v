(** Source-site admission for the EXISTING synthetic-rule worker.

    Source checkpoint: da854cb7, prattail/src/wpda_rule_analysis/synthetic.rs.
    This file does not define a second recipe builder or parser. Rows and all
    six recipe families are those of SyntheticRuleProjection. The additional
    mathematical trace names the original effect/allocation sites; Rust must
    execute these checks inline, NOT construct or execute a precomputed plan.

    Observation functions below describe successful original callbacks. Their
    values are not permission to evaluate callbacks early: the trace fixes the
    reached calls, and its interpreter stops at the first failed admission or
    callback. Boolean callbacks must agree with the observations when successful.
    The separate fallible-any law states this premise explicitly. Callback
    materialization correspondence remains the existing projection obligation.

    Units are caller chosen finite logical work/string/vector obligations, not
    physical capacity, RSS, allocator, Unicode or arbitrary callback CPU bounds.
    UserInput/TypeInput staging is a caller obligation outside this worker.
    Copies/moves of already-owned collection metadata are distinguished below.
    The session is a consumed private value; only full success publishes it and
    the completed rows. Trace prefixes are mathematical evidence, not an exposed
    partial owner or partial result API.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import SyntheticRuleProjection ReconstructionWorkBudget
  AuthoredNormalizationMaterialization.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module SyntheticRuleAdmission.
Module P := SyntheticRuleProjection.SyntheticRuleProjection.
Module M := AuthoredNormalizationMaterialization.AuthoredNormalizationMaterialization.

Definition Stored := @P.Stored nat.
Definition Rows := list (list Stored).
Inductive Phase := Users | Normalize | Native | Collections | Variables | BinderNames | Pairs | Lambdas.
Inductive Callback :=
| CloneUser (handle : nat) | NormalizeUser (payload : Stored)
| FirstItemIsVar (payload : Stored) | Materialize (recipe : P.Recipe)
| HasLiteralBlock (declaration : P.CategoryView)
| LiteralLabel (declaration : P.CategoryView)
| CollectionMetadata (declaration : P.CategoryView)
| VarLabel (declaration : P.CategoryView) | DeclaresBinder.
Inductive Event :=
| CategoryIndexSlots (count : nat) | CategoryIndexEntry (index : nat) (name : string)
| BucketSlots (count : nat) | Visit (phase : Phase)
| CategoryLookup (name : string) | RowSlot (index : nat)
| StringCopy (text : string) | TrimOpen (declaration : P.CategoryView)
| Lowercase (text : string) | Format (prefix body suffix : string)
| RecipeSlots (items params syntax : nat)
| BinderNameSlots (upper_bound : nat) | VectorKindClone
| Call (callback : Callback).

Definition copies (texts : list string) := map StringCopy texts.
Definition invoke callback := [Call callback].
Definition emit index recipe := [RowSlot index; Call (Materialize recipe)].

(** [probe_prefix] is the successful .any() call trace, not a cached predicate
    array. It stops at the first true payload in the CURRENT category row. *)
Fixpoint probe_prefix (first_var : Stored -> bool) row := match row with
| [] => []
| payload :: rest => Call (FirstItemIsVar payload) ::
    if first_var payload then [] else probe_prefix first_var rest end.

Section FallibleAny.
Context {Error : Type}.
Variable inspect : Stored -> bool + Error.
Fixpoint try_any row : (bool + Error) * list Stored := match row with
| [] => (inl false, [])
| payload :: rest => match inspect payload with
  | inr error => (inr error, [payload])
  | inl true => (inl true, [payload])
  | inl false => let '(answer, visited) := try_any rest in
      (answer, payload :: visited)
  end end.
Theorem any_first_error_stops_before_suffix : forall payload rest error,
  inspect payload = inr error -> try_any (payload :: rest) = (inr error, [payload]).
Proof. intros; cbn; now rewrite H. Qed.
Theorem any_first_true_stops_before_suffix : forall payload rest,
  inspect payload = inl true -> try_any (payload :: rest) = (inl true, [payload]).
Proof. intros; cbn; now rewrite H. Qed.
Theorem any_success_preserves_original_short_circuit : forall first_var,
  (forall payload, inspect payload = inl (first_var payload)) -> forall row,
  fst (try_any row) = inl (existsb first_var row) /\
  map (fun payload => Call (FirstItemIsVar payload)) (snd (try_any row)) =
    probe_prefix first_var row.
Proof.
  intros first_var Exact row; induction row as [|payload rest IH]; cbn; [auto|].
  rewrite Exact. destruct (first_var payload); cbn; [auto|].
  destruct (try_any rest) as [answer visited]; cbn in *.
  destruct IH as [Answer Trace]; split; [exact Answer|now rewrite Trace].
Qed.
End FallibleAny.

(** Only traces are new. Each row transformation delegates to the original
    projection operation, so recipes/normalization are not redefined here. *)
Record Schedule := { rows : Rows; events : list Event }.
Definition advance (step : Rows -> Rows) sites state :=
  {| rows := step (rows state); events := events state ++ sites |}.
Definition instrument {Input} (step : Rows -> Input -> Rows)
    (sites : Rows -> Input -> list Event) state input :=
  advance (fun previous => step previous input) (sites (rows state) input) state.
Lemma instrumented_fold_erases : forall Input (step : Rows -> Input -> Rows) sites inputs state,
  rows (fold_left (instrument step sites) inputs state) = fold_left step inputs (rows state).
Proof.
  intros Input step sites inputs; induction inputs; intros state; cbn; [reflexivity|].
  rewrite IHinputs. reflexivity.
Qed.
Lemma instrumented_fold_trace_extends : forall Input (step : Rows -> Input -> Rows) sites inputs state,
  exists suffix, events (fold_left (instrument step sites) inputs state) = events state ++ suffix.
Proof.
  intros Input step sites inputs; induction inputs; intros state; cbn.
  - exists []; now rewrite app_nil_r.
  - destruct (IHinputs (instrument step sites state a)) as [suffix H].
    exists (sites (rows state) a ++ suffix). rewrite H. cbn. now rewrite app_assoc.
Qed.

Section SourceSites.
Variable categories : list string.
Variable user_category : nat -> string.
Variable normalized_first_var : nat -> bool.
Variable lower_name : string -> string.
Definition first_var := @P.view_first_var nat nat (fun h => h) (fun h => h) normalized_first_var.
Definition user_step := @P.view_user_step nat nat (fun h => h) user_category categories.
Definition native_step := @P.view_native_step nat categories.
Definition collection_step := @P.view_collection_step nat categories.
Definition var_step := @P.view_var_step nat nat (fun h => h) (fun h => h) normalized_first_var categories.
Definition pair_step := @P.view_pair_step nat lower_name categories.
Definition lam_step := @P.view_lam_step nat categories.

Definition user_sites (_ : Rows) handle :=
  [Visit Users; CategoryLookup (user_category handle)] ++
  match P.last_slot (user_category handle) categories with
  | None => [] | Some index => [RowSlot index; Call (CloneUser handle)] end.
Definition normalization_sites grouped := flat_map
  (fun row => Visit Normalize :: flat_map
    (fun payload => [Visit Normalize; Call (NormalizeUser payload)]) row) grouped.
Definition native_sites (_ : Rows) declaration :=
  Visit Native :: if P.view_data declaration then [] else
  CategoryLookup (P.view_name declaration) ::
  match P.last_slot (P.view_name declaration) categories with
  | None => [] | Some index => match P.view_collection declaration with
    | Some _ => [] | None => Call (HasLiteralBlock declaration) ::
      match P.view_literal_label declaration with
      | None => [] | Some label =>
        invoke (LiteralLabel declaration) ++
        [RecipeSlots 1 0 0; StringCopy (P.view_name declaration); StringCopy (P.view_name declaration)] ++
        emit index (P.recipe_native (P.view_name declaration) label)
      end end end.
Definition collection_sites (_ : Rows) declaration :=
  Visit Collections :: if P.view_data declaration then [] else
  CategoryLookup (P.view_name declaration) ::
  match P.last_slot (P.view_name declaration) categories with
  | None => [] | Some index => match P.view_collection declaration with
    | None => [] | Some observation =>
      invoke (CollectionMetadata declaration) ++ [TrimOpen declaration;
        RecipeSlots 0 1 (if P.split_open observation then 4 else 3)] ++
      (if P.split_open observation then copies ["("] else []) ++
      copies ["elems"; P.view_name declaration; "elems"] ++
      emit index (P.recipe_collection (P.view_name declaration) observation)
    end end.
Definition var_sites previous declaration :=
  Visit Variables :: if P.view_data declaration then [] else
  CategoryLookup (P.view_name declaration) ::
  match P.last_slot (P.view_name declaration) categories with
  | None => [] | Some index =>
    probe_prefix first_var (nth index previous []) ++
    if existsb first_var (nth index previous []) then [] else
      invoke (VarLabel declaration) ++
      [RecipeSlots 1 0 0; StringCopy (P.view_name declaration); StringCopy (P.view_name declaration)] ++
      emit index (P.recipe_var (P.view_name declaration) (P.view_var_label declaration))
  end.

(** The five prelude strings are produced before Apply. The vector-kind clone
    belongs to MApply, after Apply's materializer has succeeded. No second
    lowercase, label formatting or metadata-string copy is introduced. *)
Definition pair_prelude dom :=
  [Visit Pairs; Lowercase dom; Format "$" (lower_name dom) "";
   Format "$$" (lower_name dom) "("; Format "Apply" dom ""; Format "MApply" dom ""].
Definition apply_sites index home dom :=
  [RecipeSlots 0 2 6] ++ copies [home; "f"; home; "x"; dom; "("; "f"; ","; "x"; ")"] ++
  emit index (P.recipe_apply home dom (lower_name dom)).
Definition mapply_sites index home dom :=
  [RecipeSlots 0 2 5] ++ copies [home; "f"; home; "xs"] ++
  [VectorKindClone] ++ copies [dom; "f"; ","; "xs"; ","; ")"] ++
  emit index (P.recipe_mapply home dom (lower_name dom)).
Definition pair_sites index home dom :=
  pair_prelude dom ++ apply_sites index home dom ++ mapply_sites index home dom.
Definition pairs_sites names := flat_map (fun home =>
  [Visit Pairs; CategoryLookup home] ++ match P.last_slot home categories with
  | None => [] | Some index => flat_map (pair_sites index home) names end) names.
Definition lam_sites home := [Visit Lambdas; CategoryLookup home] ++
  match P.last_slot home categories with
  | None => [] | Some index =>
    [Format "Lam" home ""; RecipeSlots 0 1 6] ++
    copies [home; "x"; "p"; home; home; "^"; "x"; "."; "{"; "p"; "}"] ++
    emit index (P.recipe_lam home) end.
Definition binder_sites declarations :=
  [BinderNameSlots (List.length declarations)] ++
  flat_map (fun declaration => Visit BinderNames ::
    if P.view_data declaration then [] else [StringCopy (P.view_name declaration)]) declarations ++
  pairs_sites (P.view_names declarations) ++
  flat_map lam_sites (P.view_names declarations).
Definition initial_schedule :=
  {| rows := repeat [] (List.length categories);
     events := [CategoryIndexSlots (List.length categories)] ++
       map (fun indexed => CategoryIndexEntry (fst indexed) (snd indexed))
         (combine (seq 0 (List.length categories)) categories) ++
       [BucketSlots (List.length categories)] |}.
Definition grouped_schedule users := fold_left (instrument user_step user_sites) users initial_schedule.
Definition normalized_schedule users := let grouped := grouped_schedule users in
  advance (fun previous => previous) (normalization_sites (rows grouped)) grouped.
Definition generated_schedule declarations users :=
  let native := fold_left (instrument native_step native_sites) declarations (normalized_schedule users) in
  let collections := fold_left (instrument collection_step collection_sites) declarations native in
  fold_left (instrument var_step var_sites) declarations collections.
Definition schedule declarations users (has_binders : bool) :=
  let generated := generated_schedule declarations users in
  advance (fun previous => if has_binders then
    fold_left lam_step (P.view_names declarations)
      (fold_left pair_step (P.pairs (P.view_names declarations)) previous) else previous)
    ([Call DeclaresBinder] ++ if has_binders then binder_sites declarations else []) generated.

Theorem all_clones_precede_grouped_normalization : forall users,
  events (normalized_schedule users) = events (grouped_schedule users) ++
    normalization_sites (rows (grouped_schedule users)).
Proof. reflexivity. Qed.
Theorem unused_literal_probe_is_not_a_native_gate : forall previous declaration index,
  P.view_data declaration = false -> P.last_slot (P.view_name declaration) categories = Some index ->
  P.view_collection declaration = None -> P.view_literal_label declaration = None ->
  native_sites previous declaration = [Visit Native; CategoryLookup (P.view_name declaration); Call (HasLiteralBlock declaration)].
Proof. intros; unfold native_sites; now rewrite H, H0, H1, H2. Qed.
Theorem current_bucket_drives_var_callback_prefix : forall previous declaration index,
  P.view_data declaration = false -> P.last_slot (P.view_name declaration) categories = Some index ->
  exists suffix, var_sites previous declaration =
    [Visit Variables; CategoryLookup (P.view_name declaration)] ++
      probe_prefix first_var (nth index previous []) ++ suffix.
Proof. intros; unfold var_sites; rewrite H, H0; eexists; reflexivity. Qed.
Theorem pair_prelude_then_apply_then_mapply : forall index home dom,
  pair_sites index home dom = pair_prelude dom ++ apply_sites index home dom ++ mapply_sites index home dom.
Proof. reflexivity. Qed.
Theorem all_pairs_precede_separate_lambda_pass : forall declarations,
  exists prefix, binder_sites declarations = prefix ++ pairs_sites (P.view_names declarations) ++
    flat_map lam_sites (P.view_names declarations).
Proof.
  intros; unfold binder_sites.
  exists ([BinderNameSlots (List.length declarations)] ++
    flat_map (fun declaration => Visit BinderNames ::
      if P.view_data declaration then [] else [StringCopy (P.view_name declaration)]) declarations).
  now rewrite app_assoc.
Qed.
Theorem absent_home_skips_pair_body_not_domain_roster : forall home names,
  P.last_slot home categories = None ->
  pairs_sites (home :: names) = [Visit Pairs; CategoryLookup home] ++
    flat_map (fun other => [Visit Pairs; CategoryLookup other] ++
      match P.last_slot other categories with
      | None => [] | Some index => flat_map (pair_sites index other) (home :: names) end) names.
Proof. intros; unfold pairs_sites; cbn; now rewrite H. Qed.

(** Erasing instrumentation gives exactly the already-proved driver. Its
    original_empty_start_ordered_materialization theorem supplies source AST
    payload equality, including grouped normalization without idempotence. *)
Theorem source_schedule_erases_to_existing_driver : forall declarations users binders,
  rows (schedule declarations users binders) =
  @P.view_driver nat nat lower_name (fun h => h) (fun h => h) user_category normalized_first_var
    categories declarations users binders (repeat [] (List.length categories)).
Proof.
  intros. unfold schedule, generated_schedule, normalized_schedule, grouped_schedule.
  cbn [advance rows]. rewrite !instrumented_fold_erases.
  cbn [advance rows]. rewrite !instrumented_fold_erases. reflexivity.
Qed.
End SourceSites.

(** A callback boundary includes its immediate successful insertion into the
    private bucket. These are the EXISTING append operations, not a new recipe
    interpreter. NormalizeUser is identity only in the semantic Stored view:
    OriginalHandle denotes its original normalized payload under P.materialize.
    It is not identity on the concrete owned store or an early normalization.
    All non-insertion events must preserve this row observation. *)
Definition callback_row_effect categories user_category previous site :=
  match site with
  | Call (CloneUser handle) =>
      @P.view_user_step nat nat (fun h => h) user_category categories previous handle
  | Call (Materialize recipe) =>
      @P.append_view nat categories (P.category recipe) (P.Synthetic recipe) previous
  | _ => previous
  end.

(** Concrete source-site/row relation, discharged below. Only the subsequent
    per-callback owner projection is an adapter correspondence premise. *)
Definition SourceRowsCorrespond categories user_category first_var lower declarations users binders :=
  fold_left (callback_row_effect categories user_category)
    (events (schedule categories user_category first_var lower declarations users binders))
    (repeat [] (List.length categories)) =
  rows (schedule categories user_category first_var lower declarations users binders).

Section EventBlocks.
Variable categories : list string.
Variable user_category : nat -> string.
Variable first : nat -> bool.
Variable lower : string -> string.
Definition effect := callback_row_effect categories user_category.
Definition execute sites previous := fold_left effect sites previous.
Lemma execute_app : forall left right previous,
  execute (left ++ right) previous = execute right (execute left previous).
Proof. intros; apply fold_left_app. Qed.
Lemma copies_no_row_effect : forall texts previous, execute (copies texts) previous = previous.
Proof. induction texts; intros; cbn [copies map execute fold_left effect callback_row_effect]; auto. Qed.
Lemma probes_no_row_effect : forall predicate payloads previous,
  execute (probe_prefix predicate payloads) previous = previous.
Proof.
  intros predicate payloads; induction payloads; intros; cbn [probe_prefix execute fold_left effect callback_row_effect];
    [reflexivity|]. destruct (predicate a); cbn; auto.
Qed.
Lemma emit_row_effect : forall index recipe previous,
  execute (emit index recipe) previous =
    @P.append_view nat categories (P.category recipe) (P.Synthetic recipe) previous.
Proof. reflexivity. Qed.
Lemma user_block_effect : forall previous handle,
  execute (user_sites categories user_category previous handle) previous =
    user_step categories user_category previous handle.
Proof.
  intros; unfold user_sites, user_step, P.view_user_step, P.append_view.
  destruct (P.last_slot (user_category handle) categories) eqn:E;
    cbn [execute fold_left effect callback_row_effect P.view_user_step P.append_view app]; rewrite ?E.
  all: try reflexivity.
  unfold P.view_user_step, P.append_view. now rewrite E.
Qed.
Lemma normalization_no_row_effect : forall grouped previous,
  execute (normalization_sites grouped) previous = previous.
Proof.
  induction grouped as [|row rest IH]; intros previous; [reflexivity|].
  cbn [normalization_sites flat_map]. rewrite execute_app.
  assert (Row : forall state, execute (Visit Normalize :: flat_map
    (fun payload => [Visit Normalize; Call (NormalizeUser payload)]) row) state = state).
  { induction row; intros; cbn [flat_map execute fold_left effect callback_row_effect app]; auto.
    exact (IHrow state).
  }
  rewrite Row. apply IH.
Qed.
Lemma native_block_effect : forall previous declaration,
  execute (native_sites categories previous declaration) previous = native_step categories previous declaration.
Proof.
  intros previous [name data literal collection variable].
  unfold native_sites, native_step, P.view_native_step; cbn.
  destruct data; [reflexivity|]. destruct (P.last_slot name categories) eqn:E.
  - destruct collection; [reflexivity|]. destruct literal; [|reflexivity].
    cbn [invoke emit execute fold_left effect callback_row_effect P.append_view P.recipe_native P.recipe P.category].
    rewrite ?E. reflexivity.
  - destruct collection; [reflexivity|]. destruct literal; [|reflexivity].
    unfold P.append_view; now rewrite E.
Qed.
Lemma collection_block_effect : forall previous declaration,
  execute (collection_sites categories previous declaration) previous = collection_step categories previous declaration.
Proof.
  intros previous [name data literal collection variable].
  unfold collection_sites, collection_step, P.view_collection_step; cbn.
  destruct data; [reflexivity|]. destruct (P.last_slot name categories) eqn:E.
  - destruct collection as [observation|]; [|reflexivity].
    destruct (P.split_open observation); cbn [invoke copies map emit execute fold_left effect callback_row_effect P.append_view P.recipe_collection P.recipe P.category]; rewrite ?E; reflexivity.
  - destruct collection; [|reflexivity]. unfold P.append_view; now rewrite E.
Qed.
Lemma var_block_effect : forall previous declaration,
  execute (var_sites categories first previous declaration) previous = var_step categories first previous declaration.
Proof.
  intros previous [name data literal collection variable].
  unfold var_sites, var_step, P.view_var_step; cbn.
  destruct data; [reflexivity|]. destruct (P.last_slot name categories) eqn:E; [|reflexivity].
  change (execute (probe_prefix (first_var first) (nth n previous []) ++
    (if existsb (first_var first) (nth n previous []) then [] else
      invoke (VarLabel {| P.view_name := name; P.view_data := false; P.view_literal_label := literal;
        P.view_collection := collection; P.view_var_label := variable |}) ++
      [RecipeSlots 1 0 0; StringCopy name; StringCopy name] ++ emit n (P.recipe_var name variable))) previous =
    if existsb (first_var first) (nth n previous []) then previous else
      P.push_at n (P.Synthetic (P.recipe_var name variable)) previous).
  rewrite execute_app, probes_no_row_effect.
  destruct (existsb (first_var first) (nth n previous [])); [reflexivity|].
  cbn [invoke emit execute fold_left effect callback_row_effect app].
  unfold P.append_view; cbn [P.recipe_var P.recipe P.category]. now rewrite E.
Qed.
Lemma pair_block_effect : forall index home dom previous,
  execute (pair_sites lower index home dom) previous = pair_step categories lower previous (home, dom).
Proof.
  intros. unfold pair_sites, pair_prelude, apply_sites, mapply_sites.
  repeat rewrite execute_app. rewrite !copies_no_row_effect.
  cbn [execute fold_left effect callback_row_effect]. rewrite !emit_row_effect.
  reflexivity.
Qed.
Lemma lambda_block_effect : forall home previous,
  execute (lam_sites categories home) previous = lam_step categories previous home.
Proof.
  intros; unfold lam_sites, lam_step, P.view_lam_step.
  destruct (P.last_slot home categories) eqn:E.
  - rewrite !execute_app, copies_no_row_effect, emit_row_effect. reflexivity.
  - cbn [execute fold_left effect callback_row_effect]. unfold P.append_view. now rewrite E.
Qed.
Lemma flat_blocks_effect : forall Input (sites : Input -> list Event) step,
  (forall input previous, execute (sites input) previous = step previous input) ->
  forall inputs previous, execute (flat_map sites inputs) previous = fold_left step inputs previous.
Proof.
  intros Input sites step Exact inputs; induction inputs; intros previous; cbn [flat_map fold_left]; [reflexivity|].
  rewrite execute_app, Exact. apply IHinputs.
Qed.
Lemma home_pair_block_effect : forall home domains previous,
  execute ([Visit Pairs; CategoryLookup home] ++ match P.last_slot home categories with
    | None => [] | Some index => flat_map (pair_sites lower index home) domains end) previous =
  fold_left (pair_step categories lower) (map (fun dom => (home, dom)) domains) previous.
Proof.
  intros home domains previous; destruct (P.last_slot home categories) eqn:E.
  - change (execute (flat_map (pair_sites lower n home) domains) previous =
      fold_left (pair_step categories lower) (map (fun dom => (home, dom)) domains) previous).
    rewrite (flat_blocks_effect (pair_sites lower n home)
      (fun state dom => pair_step categories lower state (home, dom))) by apply pair_block_effect.
    revert previous; induction domains; intros; cbn [map fold_left]; auto.
  - cbn [execute fold_left effect callback_row_effect].
    induction domains; cbn [map fold_left]; [reflexivity|].
    unfold pair_step, P.view_pair_step, P.append_view. rewrite ?E. exact IHdomains.
Qed.
Lemma pairs_block_effect : forall names previous,
  execute (pairs_sites categories lower names) previous =
    fold_left (pair_step categories lower) (P.pairs names) previous.
Proof.
  intros names previous; unfold pairs_sites, P.pairs.
  assert (General : forall homes domains state,
    execute (flat_map (fun home => [Visit Pairs; CategoryLookup home] ++
      match P.last_slot home categories with
      | None => [] | Some index => flat_map (pair_sites lower index home) domains end) homes) state =
    fold_left (pair_step categories lower)
      (flat_map (fun home => map (fun dom => (home, dom)) domains) homes) state).
  { intros homes; induction homes; intros domains state; cbn [flat_map]; [reflexivity|].
    rewrite execute_app, home_pair_block_effect, fold_left_app. apply IHhomes. }
  apply General.
Qed.
Lemma binder_names_no_row_effect : forall declarations previous,
  execute ([BinderNameSlots (List.length declarations)] ++ flat_map
    (fun declaration => Visit BinderNames :: if P.view_data declaration then [] else
      [StringCopy (P.view_name declaration)]) declarations) previous = previous.
Proof.
  intros declarations previous. change (execute (flat_map
    (fun declaration => Visit BinderNames :: if P.view_data declaration then [] else
      [StringCopy (P.view_name declaration)]) declarations) previous = previous).
  induction declarations; cbn [flat_map]; [reflexivity|].
  rewrite execute_app. destruct (P.view_data a); cbn [execute fold_left effect callback_row_effect]; exact IHdeclarations.
Qed.
Lemma binder_block_effect : forall declarations previous,
  execute (binder_sites categories lower declarations) previous =
    fold_left (lam_step categories) (P.view_names declarations)
      (fold_left (pair_step categories lower) (P.pairs (P.view_names declarations)) previous).
Proof.
  intros; unfold binder_sites. rewrite app_assoc.
  rewrite execute_app, binder_names_no_row_effect, execute_app, pairs_block_effect.
  apply flat_blocks_effect. apply lambda_block_effect.
Qed.
Lemma instrumented_fold_source_effect : forall Input step sites,
  (forall previous input, execute (sites previous input) previous = step previous input) ->
  forall inputs state initial, execute (events state) initial = rows state ->
  execute (events (fold_left (@instrument Input step sites) inputs state)) initial =
    rows (fold_left (@instrument Input step sites) inputs state).
Proof.
  intros Input step sites Exact inputs; induction inputs; intros state initial Invariant; [exact Invariant|].
  cbn [fold_left]. apply IHinputs. cbn [instrument advance events rows].
  rewrite execute_app, Invariant. apply Exact.
Qed.
Lemma initial_events_no_row_effect : forall previous,
  execute (events (initial_schedule categories)) previous = previous.
Proof.
  intros; unfold initial_schedule; cbn [events]. rewrite !execute_app.
  assert (Entries : forall indexed state,
    execute (map (fun entry : nat * string => CategoryIndexEntry (fst entry) (snd entry)) indexed) state = state).
  { induction indexed; intros; cbn [map execute fold_left effect callback_row_effect]; auto. }
  rewrite Entries. reflexivity.
Qed.
Theorem concrete_source_events_have_original_row_effect : forall declarations users binders,
  SourceRowsCorrespond categories user_category first lower declarations users binders.
Proof.
  intros; unfold SourceRowsCorrespond.
  change (execute (events (schedule categories user_category first lower declarations users binders))
    (repeat [] (List.length categories)) = rows (schedule categories user_category first lower declarations users binders)).
  assert (Grouped : execute (events (grouped_schedule categories user_category users))
    (repeat [] (List.length categories)) = rows (grouped_schedule categories user_category users)).
  { unfold grouped_schedule. apply instrumented_fold_source_effect; [apply user_block_effect|apply initial_events_no_row_effect]. }
  assert (Normalized : execute (events (normalized_schedule categories user_category users))
    (repeat [] (List.length categories)) = rows (normalized_schedule categories user_category users)).
  { unfold normalized_schedule; cbn [advance events rows]. rewrite execute_app, Grouped. apply normalization_no_row_effect. }
  assert (Generated : execute (events (generated_schedule categories user_category first declarations users))
    (repeat [] (List.length categories)) = rows (generated_schedule categories user_category first declarations users)).
  { unfold generated_schedule. apply instrumented_fold_source_effect; [apply var_block_effect|].
    apply instrumented_fold_source_effect; [apply collection_block_effect|].
    apply instrumented_fold_source_effect; [apply native_block_effect|exact Normalized]. }
  unfold schedule; cbn [advance events rows]. rewrite execute_app, Generated.
  destruct binders; cbn [execute fold_left effect callback_row_effect]; [apply binder_block_effect|reflexivity].
Qed.
End EventBlocks.

(** Reuse the existing checked debit algebra. A policy gives each reached
    source site a finite charge; allocation failure and typed callback failure
    remain distinct. No result variant contains a partial owner on failure. *)
Section CheckedExecution.
Context {Owner Error : Type}.
Variable cost : Event -> nat.
Variable reserved : Event -> bool.
Variable perform : Event -> Owner -> Owner + Error.
Inductive Failure := Unpaid (site : Event) | Allocation (site : Event) | CallbackFailed (error : Error).
Inductive Outcome := Finished (owner : Owner) (remaining : nat) (visited : list Event)
  | Stopped (failure : Failure) (visited : list Event).
Definition prepend site outcome := match outcome with
| Finished owner remaining visited => Finished owner remaining (site :: visited)
| Stopped failure visited => Stopped failure (site :: visited) end.
Fixpoint run sites owner remaining := match sites with
| [] => Finished owner remaining []
| site :: rest => match debit remaining (cost site) with
  | None => Stopped (Unpaid site) [site]
  | Some next => if reserved site then match perform site owner with
      | inl updated => prepend site (run rest updated next)
      | inr error => Stopped (CallbackFailed error) [site]
      end else Stopped (Allocation site) [site]
  end end.
Definition visited outcome := match outcome with Finished _ _ trace | Stopped _ trace => trace end.
Definition publish (observe : Owner -> Rows) outcome : (Owner * Rows) + Failure := match outcome with
| Finished owner _ _ => inl (owner, observe owner)
| Stopped failure _ => inr failure end.
Theorem unpaid_site_runs_no_callback_or_suffix : forall site rest owner remaining,
  debit remaining (cost site) = None -> run (site :: rest) owner remaining = Stopped (Unpaid site) [site].
Proof. intros; cbn; now rewrite H. Qed.
Theorem unreserved_site_runs_no_callback_or_suffix : forall site rest owner remaining next,
  debit remaining (cost site) = Some next -> reserved site = false ->
  run (site :: rest) owner remaining = Stopped (Allocation site) [site].
Proof. intros; cbn; now rewrite H, H0. Qed.
Theorem callback_error_runs_no_suffix : forall site rest owner remaining next error,
  debit remaining (cost site) = Some next -> reserved site = true -> perform site owner = inr error ->
  run (site :: rest) owner remaining = Stopped (CallbackFailed error) [site].
Proof. intros; cbn; now rewrite H, H0, H1. Qed.
Theorem every_outcome_visits_only_a_source_prefix : forall sites owner remaining,
  exists suffix, sites = visited (run sites owner remaining) ++ suffix.
Proof.
  induction sites as [|site rest IH]; intros owner remaining; cbn.
  - exists []; reflexivity.
  - destruct (debit remaining (cost site)) as [next|]; [|exists rest; reflexivity].
    destruct (reserved site); [|exists rest; reflexivity].
    destruct (perform site owner) as [updated|error]; [|exists rest; reflexivity].
    destruct (IH updated next) as [suffix H]. exists suffix.
    destruct (run rest updated next); cbn in *; now rewrite H.
Qed.
Theorem successful_run_has_complete_trace_and_exact_debit : forall sites owner remaining updated next trace,
  run sites owner remaining = Finished updated next trace ->
  trace = sites /\ debit_all remaining (map cost sites) = Some next.
Proof.
  induction sites as [|site rest IH]; intros owner remaining updated next trace H; cbn in H.
  - inversion H; subst; auto.
  - destruct (debit remaining (cost site)) as [middle|] eqn:D; [|discriminate].
    destruct (reserved site); [|discriminate].
    destruct (perform site owner) as [current|error]; [|discriminate].
    destruct (run rest current middle) as [final last seen|failure seen] eqn:R; [|discriminate].
    destruct (IH current middle final last seen R) as [Trace Debit]. inversion H; subst.
    split; [reflexivity|cbn; now rewrite D, Debit].
Qed.
Theorem successful_run_conserves_caller_units : forall sites owner remaining updated next trace,
  run sites owner remaining = Finished updated next trace ->
  next + total_charge (map cost sites) = remaining.
Proof.
  intros. destruct (@successful_run_has_complete_trace_and_exact_debit sites owner remaining updated next trace H) as [_ Debit].
  eapply successful_sequence_has_exact_total_cost; exact Debit.
Qed.
Theorem positive_sites_bound_completed_work : forall sites owner remaining updated next trace,
  Forall (fun site => 0 < cost site) sites ->
  run sites owner remaining = Finished updated next trace -> List.length sites <= remaining.
Proof.
  intros. destruct (@successful_run_has_complete_trace_and_exact_debit sites owner remaining updated next trace H0) as [_ Debit].
  assert (Positive : Forall (fun amount => 0 < amount) (map cost sites)).
  { apply Forall_map; exact H. }
  pose proof (positive_control_steps_are_bounded_by_the_initial_budget (map cost sites) remaining next Positive Debit) as Bound.
  now rewrite length_map in Bound.
Qed.
Theorem failure_publishes_neither_owner_nor_rows : forall observe failure trace,
  publish observe (Stopped failure trace) = inr failure.
Proof. reflexivity. Qed.

(** Compositional state refinement: every successful callback/site transitions
    the SAME consumed owner. There is no externally supplied completed row
    value in the conclusion or publication operation. *)
Theorem successful_run_projects_callback_fold : forall (observe : Owner -> Rows) effect,
  (forall site before after, perform site before = inl after ->
    observe after = effect (observe before) site) ->
  forall sites owner remaining updated next trace,
  run sites owner remaining = Finished updated next trace ->
  observe updated = fold_left effect sites (observe owner).
Proof.
  intros observe effect Correspond sites; induction sites as [|site rest IH];
    intros owner remaining updated next trace H; cbn in H.
  - inversion H; reflexivity.
  - destruct (debit remaining (cost site)) as [middle|] eqn:D; [|discriminate].
    destruct (reserved site); [|discriminate].
    destruct (perform site owner) as [current|error] eqn:C; [|discriminate].
    destruct (run rest current middle) as [final last seen|failure seen] eqn:R; [|discriminate].
    pose proof (IH current middle final last seen R) as Projected. inversion H; subst. rewrite Projected.
    cbn. now rewrite (Correspond site owner current C).
Qed.
Theorem successful_source_schedule_publishes_original_rows :
  forall observe categories user_category first_var lower declarations users binders owner remaining updated next trace,
  (forall site before after, perform site before = inl after ->
    observe after = callback_row_effect categories user_category (observe before) site) ->
  observe owner = repeat [] (List.length categories) ->
  run (events (schedule categories user_category first_var lower declarations users binders)) owner remaining =
    Finished updated next trace ->
  publish observe
    (run (events (schedule categories user_category first_var lower declarations users binders)) owner remaining) =
  inl (updated, @P.view_driver nat nat lower (fun h => h) (fun h => h) user_category first_var
    categories declarations users binders (repeat [] (List.length categories))).
Proof.
  intros observe categories user_category first_var lower declarations users binders owner remaining updated next trace
    Correspond Initial Run.
  pose proof (concrete_source_events_have_original_row_effect categories user_category first_var lower declarations users binders) as Source.
  pose proof (@successful_run_projects_callback_fold observe (callback_row_effect categories user_category)
    Correspond (events (schedule categories user_category first_var lower declarations users binders))
    owner remaining updated next trace Run) as Actual.
  rewrite Initial in Actual. unfold SourceRowsCorrespond in Source.
  assert (Result : observe updated = rows (schedule categories user_category first_var lower declarations users binders)).
  { etransitivity; [exact Actual|exact Source]. }
  rewrite source_schedule_erases_to_existing_driver in Result.
  rewrite Run; cbn [publish]. now rewrite Result.
Qed.
End CheckedExecution.

(** Composition with the existing consumed normalizer: a failed terminal
    materialization yields no replacement session/handle. The synthesis adapter
    propagates that typed error at NormalizeUser; it must not retain a vacant,
    dummy, cloned or sticky-error owner and continue executing later sites. *)
Theorem failed_owned_normalization_retains_no_published_session :
  forall session entries admitted reserved original params syntax,
  M.append_paid admitted reserved (M.private_store session)
    (M.commit_batch (List.length (M.private_store session)) original params syntax) = None ->
  M.publish_commit session entries admitted reserved original params syntax = None.
Proof. apply M.failed_commit_returns_no_session_or_handle. Qed.

Print Assumptions any_first_error_stops_before_suffix.
Print Assumptions any_first_true_stops_before_suffix.
Print Assumptions any_success_preserves_original_short_circuit.
Print Assumptions instrumented_fold_erases.
Print Assumptions instrumented_fold_trace_extends.
Print Assumptions all_clones_precede_grouped_normalization.
Print Assumptions unused_literal_probe_is_not_a_native_gate.
Print Assumptions current_bucket_drives_var_callback_prefix.
Print Assumptions pair_prelude_then_apply_then_mapply.
Print Assumptions all_pairs_precede_separate_lambda_pass.
Print Assumptions absent_home_skips_pair_body_not_domain_roster.
Print Assumptions source_schedule_erases_to_existing_driver.
Print Assumptions concrete_source_events_have_original_row_effect.
Print Assumptions unpaid_site_runs_no_callback_or_suffix.
Print Assumptions unreserved_site_runs_no_callback_or_suffix.
Print Assumptions callback_error_runs_no_suffix.
Print Assumptions every_outcome_visits_only_a_source_prefix.
Print Assumptions successful_run_has_complete_trace_and_exact_debit.
Print Assumptions successful_run_conserves_caller_units.
Print Assumptions positive_sites_bound_completed_work.
Print Assumptions failure_publishes_neither_owner_nor_rows.
Print Assumptions successful_run_projects_callback_fold.
Print Assumptions successful_source_schedule_publishes_original_rows.
Print Assumptions failed_owned_normalization_retains_no_published_session.
End SyntheticRuleAdmission.
