(** Borrowed retained-declaration view for the ORIGINAL shared descriptors.

    Target: prattail/wpda_rule_analysis/authored_declarations.rs beside the
    existing AuthoredRuleReader. Rust construction reuses Core.validate and
    AuthoredRuleReader::new, requires a present header and final bindings, and
    checks every supplied original Rule handle before the census worker.
    Missing source metadata is refusal, never an available empty language.

    This model does not reimplement Core validation. Its validation-result
    parameters are the results of those existing checks; separate lemmas reuse
    the actual store/header/binding predicates at their lookup boundaries.
    Source name payloads below are borrowed validated names, not new strings.
    Total row/name functions denote reads ONLY on checked caller rosters; no
    out-of-range default is proposed for Rust. Header native tags are the
    existing opaque model payload, interpreted by the existing closed enum.

    Census uses original Rule IDs, declared types, and GLOBAL source token
    indices. Native declaration lookup uses the same global indices. Guest
    mode tokens remain borrowed index slices. Name equality classes control
    mode matching; spelling controls opener matching and output rendering.
    No qualified execution-token name, carrier, decoder, or evaluator is used
    as a substitute for these authored observations.

    Maps here denote shallow observation sequences, not production allocation
    or a reconstructed AST. Original worker definitions/theorems are imported.
    The small induction for native handles establishes only map/lookup
    substitution, not another election algorithm. Generic constructor rows are
    delegated unchanged; there is no new pattern enum or formatter policy.

    Category role uses the existing producer law admits_variables = !is_data.
    Checked final indices do not independently prove source provenance or
    semantic/native-value parity. Supplied rule order is a caller boundary;
    no heuristic derives original rules from labels or synthetic productions.
    Full synthesis normalization, native label/element observations and its
    lazy helper refinements remain outside this slice.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import AuthoredRuleStoreProjection
  AuthoredRuleCaptureProjection AuthoredDeclarationsProjection
  AuthoredDeclarationBindingProjection CategoryCensusProjection
  NativeFirstDescriptorProjection GuestModeDescriptorProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredDeclarationReaderProjection.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.
Module D := AuthoredDeclarationsProjection.AuthoredDeclarationsProjection.
Module B := AuthoredDeclarationBindingProjection.AuthoredDeclarationBindingProjection.
Module Q := CategoryCensusProjection.CategoryCensusProjection.
Module N := NativeFirstDescriptorProjection.NativeFirstDescriptorProjection.
Module G := GuestModeDescriptorProjection.GuestModeDescriptorProjection.

Definition admit_view (core_valid original_reader_valid : bool)
    (header : option D.Header) (bindings : option B.Bindings) :=
  if core_valid then if original_reader_valid then
    match header, bindings with Some h, Some b => Some (h,b) | _,_ => None end
  else None else None.
Theorem absent_header_is_not_empty_source : forall cv rv bindings,
  admit_view cv rv None bindings = None.
Proof. intros [] []; reflexivity. Qed.
Theorem view_requires_both_original_validation_results : forall cv rv header bindings view,
  admit_view cv rv header bindings = Some view ->
  cv = true /\ rv = true /\ header = Some (fst view) /\ bindings = Some (snd view).
Proof.
  intros [] [] [header|] [bindings|] view H; try discriminate.
  inversion H; repeat split; reflexivity.
Qed.
Definition rules_valid arena (rules : list (A.Handle A.RuleTag)) :=
  forallb (fun rule => A.reference_valid arena (A.edge rule)) rules.
Theorem checked_rule_roster_has_actual_rule_nodes : forall arena rules rule,
  rules_valid arena rules = true -> In rule rules ->
  exists target, nth_error arena (A.index rule) = Some target /\
    A.node_tag target = A.RuleTag /\ A.index rule < List.length arena.
Proof.
  intros arena rules rule Checked Member; unfold rules_valid in Checked.
  apply forallb_forall with (x := rule) in Checked; [|exact Member].
  apply A.reference_valid_sound in Checked; exact Checked.
Qed.
Definition census_if_rules_valid {X : Type} arena rules
    (operation : list (A.Handle A.RuleTag) -> X) :=
  if rules_valid arena rules then Some (operation rules) else None.
Theorem unchecked_rule_roster_never_calls_worker : forall X arena rules (worker : _ -> X),
  rules_valid arena rules = false -> census_if_rules_valid arena rules worker = None.
Proof. intros; unfold census_if_rules_valid; rewrite H; reflexivity. Qed.
Theorem admitted_rule_order_and_multiplicity_are_unchanged :
  forall X arena rules (worker : _ -> X), rules_valid arena rules = true ->
  census_if_rules_valid arena rules worker = Some (worker rules).
Proof. intros; unfold census_if_rules_valid; rewrite H; reflexivity. Qed.

Definition resolve_tokens header indices :=
  C.map_checked (fun index => nth_error (D.tokens header) index) indices.
Theorem resolved_rosters_use_exact_indexed_source_rows : forall header indices rows,
  resolve_tokens header indices = Some rows ->
  List.length rows = List.length indices /\
  forall position index, nth_error indices position = Some index ->
  exists row, nth_error rows position = Some row /\ nth_error (D.tokens header) index = Some row.
Proof.
  intros header indices rows Checked; split.
  - eapply C.map_checked_length; exact Checked.
  - intros; eapply C.map_checked_index; eauto.
Qed.
Theorem validated_header_roster_indices_are_in_range : forall header index,
  B.canonical_roster_valid header = true -> In index (B.source_roster header) ->
  index < List.length (D.tokens header).
Proof.
  intros header index Checked Member.
  apply B.canonical_roster_checker_implies_source_partition in Checked.
  destruct Checked as [_ Complete]; apply Complete; exact Member.
Qed.

Section Fields.
Variable name : A.Handle A.NameTag -> A.NamePayload.
Variable category_row : nat -> D.CategoryDeclaration.
Variable token_row : nat -> D.TokenDeclaration.
Variable rule_row : nat -> A.RulePayload.
Variable decode_kind : nat -> N.NativeKind.

Definition spelling handle := A.spelling (name handle).
Definition present {X} (value : option X) := match value with Some _ => true | None => false end.
Definition census_source : Q.SourceStore :=
  {| Q.rule_at := fun id => {| Q.source_category := spelling (A.category (rule_row id));
                              Q.source_label := spelling (A.label (rule_row id)) |};
     Q.type_at := fun id => {| Q.source_name := spelling (D.category_name (category_row id));
                              Q.source_collection := present (D.category_collection (category_row id));
                              Q.source_native := present (D.category_native (category_row id));
                              Q.source_data_marker := false |};
     Q.token_at := fun id => {| Q.source_from_literals := D.token_from_literals (token_row id);
                               Q.source_token_category := option_map spelling (D.token_category (token_row id)) |} |}.
Definition census_reader : Q.Accessors :=
  {| Q.rule_category := fun id => spelling (A.category (rule_row id));
     Q.rule_label := fun id => spelling (A.label (rule_row id));
     Q.type_name := fun id => spelling (D.category_name (category_row id));
     Q.has_collection := fun id => present (D.category_collection (category_row id));
     Q.has_native := fun id => present (D.category_native (category_row id));
     Q.from_literals := fun id => D.token_from_literals (token_row id);
     Q.token_category := fun id => option_map spelling (D.token_category (token_row id)) |}.
Theorem concrete_census_callbacks_are_original_field_observations :
  census_reader = Q.project_accessors census_source.
Proof. reflexivity. Qed.
Theorem owned_census_reuses_five_original_passes_and_trace : forall rules types global_tokens,
  Q.shared_census census_reader rules types global_tokens =
  Q.source_census census_source rules types global_tokens.
Proof.
  intros; rewrite concrete_census_callbacks_are_original_field_observations.
  apply Q.five_pass_census_preserves_order_identity_and_observations.
Qed.

Definition native_value tag : N.Native :=
  {| N.native_kind := decode_kind tag; N.static_type_payload := 0 |}.
Definition native_category id : N.Category :=
  {| N.category_id := id; N.category_name := spelling (D.category_name (category_row id));
     N.native := option_map native_value (D.category_native (category_row id)) |}.
Definition native_token id : N.Token :=
  {| N.token_id := id; N.from_literals := D.token_from_literals (token_row id);
     N.has_rust_code := D.token_has_evaluation (token_row id);
     N.token_category := option_map spelling (D.token_category (token_row id));
     N.opaque_payload := id |}.
Definition native_reader : N.Reader nat nat :=
  {| N.read_category_id := fun id => id;
     N.read_category_name := fun id => spelling (D.category_name (category_row id));
     N.read_native := fun id => option_map native_value (D.category_native (category_row id));
     N.read_token_id := fun id => id;
     N.read_from_literals := fun id => D.token_from_literals (token_row id);
     N.read_rust_code_presence := fun id => D.token_has_evaluation (token_row id);
     N.read_token_category := fun id => option_map spelling (D.token_category (token_row id)) |}.
Lemma native_eligible_field_projection : forall target id,
  N.shared_eligible native_reader target id = N.source_eligible target (native_token id).
Proof. reflexivity. Qed.
Theorem native_declared_lookup_preserves_selected_source_id_and_trace : forall target indices,
  N.map_answer native_token (N.shared_declared native_reader target indices) =
  N.source_declared target (map native_token indices).
Proof.
  intros target indices; induction indices as [|id rest IH]; cbn; [reflexivity|].
  rewrite native_eligible_field_projection.
  destruct (N.source_eligible target (native_token id)) as [eligible events].
  destruct eligible; cbn; [reflexivity|].
  rewrite <- IH. unfold N.map_answer, N.prefix_trace; reflexivity.
Qed.
Theorem native_family_lookup_reuses_original_election_and_trace : forall target categories tokens,
  N.shared_family native_reader target categories tokens =
  N.source_family target (map native_category categories) (map native_token tokens).
Proof.
  intros target categories; induction categories as [|id rest IH]; intros tokens; cbn; [reflexivity|].
  destruct (String.eqb (spelling (D.category_name (category_row id))) target); [|rewrite IH; reflexivity].
  destruct (D.category_native (category_row id)) as [kind|]; cbn; [|reflexivity].
  destruct (N.family_for (decode_kind kind)); [reflexivity|].
  rewrite <- native_declared_lookup_preserves_selected_source_id_and_trace.
  unfold N.map_answer; destruct (N.shared_declared native_reader target tokens) as [[id'|] trace]; reflexivity.
Qed.
Theorem selected_native_token_identity_is_not_final_lexer_id : forall id,
  N.token_id (native_token id) = id /\ N.opaque_payload (native_token id) = id.
Proof. intros; split; reflexivity. Qed.

Definition matches_open value open := String.eqb (A.spelling value) open.
Definition same_name lhs rhs := Nat.eqb (A.equality_class lhs) (A.equality_class rhs).
Definition guest_token id : @G.SourceToken A.NamePayload :=
  {| G.token_name := name (D.token_name (token_row id));
     G.token_push := option_map name (D.token_push (token_row id)) |}.
Definition guest_mode row : @G.SourceMode A.NamePayload :=
  {| G.mode_name := name (D.mode_name row);
     G.mode_tokens := map guest_token (D.mode_source_tokens row) |}.
Definition guest_token_view id : @G.TokenView A.NamePayload :=
  {| G.observed_name := name (D.token_name (token_row id));
     G.observed_push := option_map name (D.token_push (token_row id)) |}.
Definition guest_mode_view row : @G.ModeView A.NamePayload :=
  {| G.observed_mode_name := name (D.mode_name row);
     G.observed_tokens := map guest_token_view (D.mode_source_tokens row) |}.
Lemma guest_index_views_preserve_raw_payloads : forall indices,
  map guest_token_view indices = map G.project_token (map guest_token indices).
Proof. intros; rewrite map_map; reflexivity. Qed.
Lemma guest_mode_views_preserve_source_rosters : forall rows,
  map guest_mode_view rows = map G.project_mode (map guest_mode rows).
Proof.
  intros rows; rewrite map_map; apply map_ext; intros row.
  unfold guest_mode_view, G.project_mode, guest_mode; cbn.
  rewrite map_map; reflexivity.
Qed.
Theorem guest_lookup_uses_original_order_equalities_and_duplicates : forall open globals modes,
  G.shared_derive matches_open same_name A.spelling open
    (map guest_token_view globals) (map guest_mode_view modes) =
  G.source_derive matches_open same_name A.spelling open
    (map guest_token globals) (map guest_mode modes).
Proof.
  intros; rewrite guest_index_views_preserve_raw_payloads, guest_mode_views_preserve_source_rosters.
  apply G.original_guest_descriptor_relocation.
Qed.
End Fields.

Theorem stored_name_equality_is_class_not_occurrence : forall arena left right lhs rhs,
  A.name_payload arena left = Some lhs -> A.name_payload arena right = Some rhs ->
  A.names_equal arena left right = Some (Nat.eqb (A.equality_class lhs) (A.equality_class rhs)).
Proof. intros; unfold A.names_equal; rewrite H, H0; reflexivity. Qed.
Example guest_spelling_and_source_equality_are_independent :
  same_name {| A.spelling := "Left"; A.equality_class := 3 |}
            {| A.spelling := "Right"; A.equality_class := 3 |} = true /\
  same_name {| A.spelling := "Same"; A.equality_class := 3 |}
            {| A.spelling := "Same"; A.equality_class := 4 |} = false.
Proof. split; reflexivity. Qed.
Theorem native_constructor_rows_and_schedule_are_unchanged : forall P
    (constructors : N.Constructors P) cat family kind context,
  N.shared_rows constructors cat family kind context =
    N.project_rows constructors (N.source_rows cat family kind context) /\
  N.calls (N.shared_rows constructors cat family kind context) =
    N.calls (N.source_rows cat family kind context).
Proof.
  intros; split; [apply N.original_rows_constructor_substitution|
    apply N.constructor_callback_trace_preserved].
Qed.

Definition category_target bindings position := nth_error (B.category_ids bindings) position.
Definition token_target bindings position := nth_error (B.token_ids bindings) position.
Definition mode_target bindings position := nth_error (B.mode_ids bindings) position.
Definition is_data_at (admits_variables : list bool) bindings position :=
  match category_target bindings position with
  | None => None | Some id => option_map negb (nth_error admits_variables id) end.
Theorem missing_category_binding_cannot_guess_role : forall roles bindings position,
  category_target bindings position = None -> is_data_at roles bindings position = None.
Proof. intros; unfold is_data_at; rewrite H; reflexivity. Qed.
Theorem role_projection_reuses_existing_producer_relation : forall roles bindings position target is_data,
  category_target bindings position = Some target ->
  nth_error roles target = Some (negb is_data) ->
  is_data_at roles bindings position = Some is_data.
Proof. intros; unfold is_data_at; rewrite H, H0; cbn; rewrite Bool.negb_involutive; reflexivity. Qed.
Theorem final_token_binding_reuses_checked_mode_membership : forall core mode id,
  B.token_in_mode core mode id = true ->
  nth_error (B.core_token_modes core) id = Some mode /\
  exists members, nth_error (B.core_mode_members core) mode = Some members /\ In id members.
Proof. apply B.accepted_token_has_actual_mode_and_membership. Qed.

Print Assumptions absent_header_is_not_empty_source.
Print Assumptions view_requires_both_original_validation_results.
Print Assumptions checked_rule_roster_has_actual_rule_nodes.
Print Assumptions unchecked_rule_roster_never_calls_worker.
Print Assumptions admitted_rule_order_and_multiplicity_are_unchanged.
Print Assumptions resolved_rosters_use_exact_indexed_source_rows.
Print Assumptions validated_header_roster_indices_are_in_range.
Print Assumptions owned_census_reuses_five_original_passes_and_trace.
Print Assumptions native_declared_lookup_preserves_selected_source_id_and_trace.
Print Assumptions native_family_lookup_reuses_original_election_and_trace.
Print Assumptions selected_native_token_identity_is_not_final_lexer_id.
Print Assumptions guest_lookup_uses_original_order_equalities_and_duplicates.
Print Assumptions stored_name_equality_is_class_not_occurrence.
Print Assumptions guest_spelling_and_source_equality_are_independent.
Print Assumptions native_constructor_rows_and_schedule_are_unchanged.
Print Assumptions missing_category_binding_cannot_guess_role.
Print Assumptions role_projection_reuses_existing_producer_relation.
Print Assumptions final_token_binding_reuses_checked_mode_membership.
End AuthoredDeclarationReaderProjection.
