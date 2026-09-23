(** Narrow bridge from ORIGINAL synthetic recipes to the EXISTING owned
    normalization session's name index, parameter/syntax batches and append.

    Rust correspondence: synthetic.rs::SyntheticParam/SyntheticRule;
    macros/wpda_codegen/synthetic.rs::materialize_synthetic_rule;
    authored_normalization.rs::{intern,base,materialize_param,materialize_syntax}.
    This file does not construct another grammar arena, normalizer or scheduler.

    Existing category handles bypass lookup. In the SAME materialize_param arm,
    synthetic category strings resolve AFTER the parameter's name (and for
    abstraction AFTER binder/body, domain then codomain), BEFORE the existing
    fixed base/type/parameter append sequence. base(NameId) remains unchanged;
    resolving inside base would interleave a domain Type before codomain name
    enrollment and would NOT match this model. Existing inputs resolve to their
    identical handles without events, preserving original normalization order.
    Resolving categories before the parameter name would change validation
    order. Resolution below invokes the existing
    enrollment operation, not an arbitrary chosen successful state or handle.
    Ordered name traces describe those lookup sites, not allocator events.

    The existing normalizer's consuming public API remains unchanged. The
    fallible synthesis adapter consumes itself, destructures its session/policy,
    invokes a consuming session method, and reconstructs only on success. There
    is no dummy arena, Option-take placeholder, mutable error session or sticky
    error. The terminal publication below exposes no session on failure.

    Full source callback correspondence still requires the original category ->
    parameters -> label -> legacy items -> syntax schedule, fixed defaults,
    and admitted identifier/name profile. The static materializer invokes
    Ident::new; the checked name index proves spelling/class consistency, NOT
    arbitrary Unicode or Rust-identifier validity. Those are explicit source
    admission obligations, not inferred from a successfully appended Name.
    Native/Var helper validation already occurred at its original worker site.
    Resource events and first-failure scheduling belong to the separate fallible
    worker model. This model reuses checked append and does not prove physical
    allocation bounds or equivalence of arbitrary callback side effects.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import SyntheticRuleProjection
  AuthoredNormalizationMaterialization AuthoredRuleStoreProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredSyntheticMaterialization.
Module S := SyntheticRuleProjection.SyntheticRuleProjection.
Module N := AuthoredNormalizationMaterialization.AuthoredNormalizationMaterialization.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Definition NameId := A.Handle A.NameTag.

Inductive CategoryName := Existing (id : NameId) | Spelling (text : string).
Inductive ParameterInput :=
| SimpleInput (name : string) (category : CategoryName)
| AbstractionInput (binder body : string) (domain codomain : CategoryName)
| CollectionInput (name : string) (kind : S.CollectionKind) (element : CategoryName).

Definition normalized_input recipe := match recipe with
| N.SimpleRecipe name category => SimpleInput name (Existing category)
| N.AbstractionRecipe binder body domain codomain =>
    AbstractionInput binder body (Existing domain) (Existing codomain)
| N.CollectionRecipe name kind element => CollectionInput name kind (Existing element)
end.
Definition synthetic_input recipe := match recipe with
| S.Simple name (S.Base category) => Some (SimpleInput name (Spelling category))
| S.Simple name (S.Collection kind element) =>
    Some (CollectionInput name kind (Spelling element))
| S.Abstraction binder body (S.Arrow domain codomain) =>
    Some (AbstractionInput binder body (Spelling domain) (Spelling codomain))
| _ => None end.

Theorem synthetic_parameter_embedding_keeps_original_fields :
  forall name category kind element binder body domain codomain,
  synthetic_input (S.Simple name (S.Base category)) = Some (SimpleInput name (Spelling category)) /\
  synthetic_input (S.Simple name (S.Collection kind element)) =
    Some (CollectionInput name kind (Spelling element)) /\
  synthetic_input (S.Abstraction binder body (S.Arrow domain codomain)) =
    Some (AbstractionInput binder body (Spelling domain) (Spelling codomain)).
Proof. repeat split; reflexivity. Qed.

Definition Step (T : Type) := (option (N.State * T) * list string)%type.
Definition done {T} st (value : T) : Step T := (Some (st, value), []).

Section Resolution.
Variable lookup_paid : bool.
Variable admit : string -> nat -> bool.
Variable reserved : bool.

Definition run_name {T} input st (next : N.State -> NameId -> Step T) : Step T :=
  match input with
  | Existing id => next st id
  | Spelling text =>
      match N.enroll_after_lookup lookup_paid admit reserved text st with
      | None => (None, [text])
      | Some (after, id) => let '(result, trace) := next after id in
                           (result, text :: trace)
      end
  end.

Definition resolve_parameter input st : Step N.ResolvedParam :=
  match input with
  | SimpleInput name category =>
      run_name (Spelling name) st (fun st name_id =>
      run_name category st (fun st category_id =>
      done st (N.ResolvedSimple name_id category_id)))
  | AbstractionInput binder body domain codomain =>
      run_name (Spelling binder) st (fun st binder_id =>
      run_name (Spelling body) st (fun st body_id =>
      run_name domain st (fun st domain_id =>
      run_name codomain st (fun st codomain_id =>
      done st (N.ResolvedAbstraction binder_id body_id domain_id codomain_id)))))
  | CollectionInput name kind element =>
      run_name (Spelling name) st (fun st name_id =>
      run_name element st (fun st element_id =>
      done st (N.ResolvedCollection name_id kind element_id)))
  end.

Definition resolve_syntax recipe st : Step N.ResolvedSyntax :=
  match recipe with
  | S.Literal text => done st (N.ResolvedLiteral text)
  | S.Param name => run_name (Spelling name) st
      (fun st id => done st (N.ResolvedParamRef id))
  | S.Sep name separator => run_name (Spelling name) st
      (fun st id => done st (N.ResolvedSep id separator))
  end.
Definition resolve_legacy recipe st : Step A.LegacyPayload :=
  match recipe with
  | S.CategoryItem name => run_name (Spelling name) st
      (fun st id => done st (A.Nonterminal id A.Category))
  | S.VarItem name => run_name (Spelling name) st
      (fun st id => done st (A.Nonterminal id A.Var))
  end.

Theorem existing_category_is_exact_identity_without_lookup : forall T st id next,
  @run_name T (Existing id) st next = next st id.
Proof. reflexivity. Qed.
Theorem original_simple_resolution_has_no_category_lookup : forall name category st,
  resolve_parameter (normalized_input (N.SimpleRecipe name category)) st =
  run_name (Spelling name) st (fun after id => done after (N.ResolvedSimple id category)).
Proof. reflexivity. Qed.
Theorem original_abstraction_resolution_keeps_only_binder_body_lookups :
  forall binder body domain codomain st,
  resolve_parameter (normalized_input (N.AbstractionRecipe binder body domain codomain)) st =
  run_name (Spelling binder) st (fun next binder_id =>
  run_name (Spelling body) next (fun after body_id =>
  done after (N.ResolvedAbstraction binder_id body_id domain codomain))).
Proof. reflexivity. Qed.
Theorem original_collection_resolution_has_no_element_lookup : forall name kind element st,
  resolve_parameter (normalized_input (N.CollectionRecipe name kind element)) st =
  run_name (Spelling name) st (fun after id => done after (N.ResolvedCollection id kind element)).
Proof. reflexivity. Qed.

Theorem synthetic_simple_resolves_name_before_category : forall name category before middle after n c,
  N.enroll_after_lookup lookup_paid admit reserved name before = Some (middle, n) ->
  N.enroll_after_lookup lookup_paid admit reserved category middle = Some (after, c) ->
  resolve_parameter (SimpleInput name (Spelling category)) before =
    (Some (after, N.ResolvedSimple n c), [name; category]).
Proof. intros; unfold resolve_parameter, run_name; rewrite H, H0; reflexivity. Qed.
Theorem synthetic_collection_resolves_name_before_element : forall name kind element before middle after n e,
  N.enroll_after_lookup lookup_paid admit reserved name before = Some (middle, n) ->
  N.enroll_after_lookup lookup_paid admit reserved element middle = Some (after, e) ->
  resolve_parameter (CollectionInput name kind (Spelling element)) before =
    (Some (after, N.ResolvedCollection n kind e), [name; element]).
Proof. intros; unfold resolve_parameter, run_name; rewrite H, H0; reflexivity. Qed.
Theorem synthetic_abstraction_resolves_binder_body_domain_codomain :
  forall binder body domain codomain s0 s1 s2 s3 s4 b p d c,
  N.enroll_after_lookup lookup_paid admit reserved binder s0 = Some (s1, b) ->
  N.enroll_after_lookup lookup_paid admit reserved body s1 = Some (s2, p) ->
  N.enroll_after_lookup lookup_paid admit reserved domain s2 = Some (s3, d) ->
  N.enroll_after_lookup lookup_paid admit reserved codomain s3 = Some (s4, c) ->
  resolve_parameter (AbstractionInput binder body (Spelling domain) (Spelling codomain)) s0 =
    (Some (s4, N.ResolvedAbstraction b p d c), [binder; body; domain; codomain]).
Proof. intros; unfold resolve_parameter, run_name; rewrite H, H0, H1, H2; reflexivity. Qed.
Theorem failed_name_does_not_call_continuation : forall T text st next,
  N.enroll_after_lookup lookup_paid admit reserved text st = None ->
  @run_name T (Spelling text) st next = (None, [text]).
Proof. intros; unfold run_name; now rewrite H. Qed.
Theorem failed_domain_preserves_attempt_order_and_skips_codomain :
  forall binder body domain codomain s0 s1 s2 b p,
  N.enroll_after_lookup lookup_paid admit reserved binder s0 = Some (s1, b) ->
  N.enroll_after_lookup lookup_paid admit reserved body s1 = Some (s2, p) ->
  N.enroll_after_lookup lookup_paid admit reserved domain s2 = None ->
  resolve_parameter (AbstractionInput binder body (Spelling domain) (Spelling codomain)) s0 =
    (None, [binder; body; domain]).
Proof. intros; unfold resolve_parameter, run_name; rewrite H, H0, H1; reflexivity. Qed.
Theorem literal_syntax_reuses_existing_nonallocating_payload : forall text st,
  resolve_syntax (S.Literal text) st = (Some (st, N.ResolvedLiteral text), []) /\
  N.syntax_batch (N.ResolvedLiteral text) = [].
Proof. split; reflexivity. Qed.
Theorem separator_resolution_keeps_original_source_none : forall name separator before after id,
  N.enroll_after_lookup lookup_paid admit reserved name before = Some (after, id) ->
  resolve_syntax (S.Sep name separator) before =
    (Some (after, N.ResolvedSep id separator), [name]) /\
  N.syntax_batch (N.ResolvedSep id separator) = [A.OperationNode (A.Sep id separator None)].
Proof. intros; split; [unfold resolve_syntax, run_name; now rewrite H|reflexivity]. Qed.
Theorem native_and_var_legacy_kinds_are_not_reclassified : forall name before after id,
  N.enroll_after_lookup lookup_paid admit reserved name before = Some (after, id) ->
  resolve_legacy (S.CategoryItem name) before = (Some (after, A.Nonterminal id A.Category), [name]) /\
  resolve_legacy (S.VarItem name) before = (Some (after, A.Nonterminal id A.Var), [name]).
Proof. intros; split; unfold resolve_legacy, run_name; now rewrite H. Qed.
End Resolution.

Theorem spelling_resolution_reuses_checked_name_evidence : forall admit reserved text before after id,
  N.Profile (N.names before) -> N.IndexReads (N.arena before) (N.names before) ->
  N.ClassesFit (N.names before) ->
  N.enroll_after_lookup true admit reserved text before = Some (after, id) ->
  N.Profile (N.names after) /\ N.IndexReads (N.arena after) (N.names after) /\
  N.ClassesFit (N.names after) /\
  exists payload, A.name_payload (N.arena after) id = Some payload /\ A.spelling payload = text.
Proof. intros; eapply N.generated_enrollment_preserves_profile_reads_width_and_exact_spelling; eauto. Qed.
Theorem existing_parameter_batch_and_reader_are_reused : forall paid reserved prefix recipe result,
  N.append_paid paid reserved prefix (N.parameter_batch (List.length prefix) recipe) = Some result ->
  A.parameter result (N.parameter_handle (List.length prefix) recipe) =
    Some (A.read_param (N.parameter_payload (List.length prefix) recipe)).
Proof. apply N.parameter_materialization_is_read_by_existing_reader. Qed.

(** Fresh finalization differs from normalization only in the supplied fields
    and optional presence. It appends no dummy original Rule. The mathematical
    batch uses the existing checked append; Rust reserves/appends at each site. *)
Definition present {T} (value : option T) := match value with None => 0 | Some _ => 1 end.
Definition fresh_rule start label category items
    (params : option (list (A.Handle A.ParamTag))) (syntax : option (list A.SyntaxPayload)) :=
  {| A.label := label; A.category := category; A.legacy_items := items;
     A.term_context := option_map (fun _ => A.Ref start) params;
     A.syntax_pattern := option_map (fun _ => A.Ref (start + present params)) syntax |}.
Definition fresh_batch start label category items params syntax :=
  (match params with None => [] | Some values => [A.ParamsNode values] end) ++
  (match syntax with None => [] | Some values => [A.SyntaxNode values] end) ++
  [A.RuleNode (fresh_rule start label category items params syntax)].
Definition fresh_handle start (params : option (list (A.Handle A.ParamTag)))
    (syntax : option (list A.SyntaxPayload)) : A.Handle A.RuleTag :=
  A.Ref (start + present params + present syntax).

Theorem native_and_var_have_no_optional_sequences : forall home label,
  S.params (S.recipe_native home label) = None /\ S.syntax (S.recipe_native home label) = None /\
  S.params (S.recipe_var home label) = None /\ S.syntax (S.recipe_var home label) = None.
Proof. repeat split; reflexivity. Qed.
Theorem native_and_var_terminal_commit_allocates_only_rule : forall start label category items,
  fresh_batch start label category items None None =
  [A.RuleNode {| A.label := label; A.category := category; A.legacy_items := items;
    A.term_context := None; A.syntax_pattern := None |}].
Proof. reflexivity. Qed.
Theorem empty_present_sequences_are_not_absent : forall start label category items,
  fresh_batch start label category items (Some []) (Some []) =
  [A.ParamsNode []; A.SyntaxNode [];
   A.RuleNode {| A.label := label; A.category := category; A.legacy_items := items;
    A.term_context := Some (A.Ref start); A.syntax_pattern := Some (A.Ref (start + 1)) |}].
Proof. reflexivity. Qed.
Theorem old_normalization_commit_is_exact_some_some_instance : forall start original params syntax,
  fresh_batch start (A.label original) (A.category original) (A.legacy_items original)
    (Some params) (Some syntax) = N.commit_batch start original params syntax.
Proof. reflexivity. Qed.
Theorem terminal_rule_is_after_every_present_sequence : forall start label category items params syntax,
  nth_error (fresh_batch start label category items params syntax)
    (present params + present syntax) = Some (A.RuleNode (fresh_rule start label category items params syntax)).
Proof. intros; destruct params, syntax; reflexivity. Qed.
Theorem successful_fresh_commit_exposes_existing_rule_reader :
  forall paid reserved prefix label category items params syntax result,
  N.append_paid paid reserved prefix
    (fresh_batch (List.length prefix) label category items params syntax) = Some result ->
  A.authored_rule result (fresh_handle (List.length prefix) params syntax) =
    Some (A.read_rule (fresh_rule (List.length prefix) label category items params syntax), map A.read_legacy items).
Proof.
  intros; apply N.paid_batch_is_exact_existing_checked_append in H; destruct H as [_ [_ ->]].
  unfold A.authored_rule, fresh_handle; cbn [A.index].
  replace (List.length prefix + present params + present syntax)
    with (List.length prefix + (present params + present syntax)) by lia.
  rewrite N.batch_position with (node := A.RuleNode (fresh_rule (List.length prefix) label category items params syntax)).
  - reflexivity.
  - apply terminal_rule_is_after_every_present_sequence.
Qed.

Definition publish_fresh session entries paid reserved label category items params syntax :=
  match N.append_paid paid reserved (N.private_store session)
    (fresh_batch (List.length (N.private_store session)) label category items params syntax) with
  | None => None
  | Some nodes => Some
      ({| N.private_store := nodes; N.original_len := N.original_len session; N.name_index := Some entries |},
       fresh_handle (List.length (N.private_store session)) params syntax)
  end.
Theorem failed_fresh_commit_exposes_no_session_or_handle :
  forall session entries paid reserved label category items params syntax,
  N.append_paid paid reserved (N.private_store session)
    (fresh_batch (List.length (N.private_store session)) label category items params syntax) = None ->
  publish_fresh session entries paid reserved label category items params syntax = None.
Proof. intros; unfold publish_fresh; now rewrite H. Qed.
Theorem successful_fresh_commit_preserves_original_bound_and_prefix :
  forall session entries paid reserved label category items params syntax next id,
  publish_fresh session entries paid reserved label category items params syntax = Some (next, id) ->
  N.original_len next = N.original_len session /\
  N.private_store next = N.private_store session ++
    fresh_batch (List.length (N.private_store session)) label category items params syntax.
Proof.
  intros; unfold publish_fresh in H.
  destruct (N.append_paid paid reserved (N.private_store session)
    (fresh_batch (List.length (N.private_store session)) label category items params syntax)) as [nodes|] eqn:E;
    [|discriminate].
  apply N.paid_batch_is_exact_existing_checked_append in E; destruct E as [_ [_ Nodes]].
  inversion H; subst; split; reflexivity.
Qed.
Theorem existing_normalize_publication_is_unchanged : forall session entries paid reserved original params syntax,
  publish_fresh session entries paid reserved (A.label original) (A.category original)
    (A.legacy_items original) (Some params) (Some syntax) =
  N.publish_commit session entries paid reserved original params syntax.
Proof.
  intros; unfold publish_fresh, N.publish_commit.
  rewrite old_normalization_commit_is_exact_some_some_instance.
  unfold fresh_handle, N.commit_handle; cbn [present].
  replace (List.length (N.private_store session) + 1 + 1)
    with (List.length (N.private_store session) + 2) by lia.
  reflexivity.
Qed.

Print Assumptions synthetic_parameter_embedding_keeps_original_fields.
Print Assumptions existing_category_is_exact_identity_without_lookup.
Print Assumptions original_simple_resolution_has_no_category_lookup.
Print Assumptions original_abstraction_resolution_keeps_only_binder_body_lookups.
Print Assumptions original_collection_resolution_has_no_element_lookup.
Print Assumptions synthetic_simple_resolves_name_before_category.
Print Assumptions synthetic_collection_resolves_name_before_element.
Print Assumptions synthetic_abstraction_resolves_binder_body_domain_codomain.
Print Assumptions failed_name_does_not_call_continuation.
Print Assumptions failed_domain_preserves_attempt_order_and_skips_codomain.
Print Assumptions literal_syntax_reuses_existing_nonallocating_payload.
Print Assumptions separator_resolution_keeps_original_source_none.
Print Assumptions native_and_var_legacy_kinds_are_not_reclassified.
Print Assumptions spelling_resolution_reuses_checked_name_evidence.
Print Assumptions existing_parameter_batch_and_reader_are_reused.
Print Assumptions native_and_var_have_no_optional_sequences.
Print Assumptions native_and_var_terminal_commit_allocates_only_rule.
Print Assumptions empty_present_sequences_are_not_absent.
Print Assumptions old_normalization_commit_is_exact_some_some_instance.
Print Assumptions terminal_rule_is_after_every_present_sequence.
Print Assumptions successful_fresh_commit_exposes_existing_rule_reader.
Print Assumptions failed_fresh_commit_exposes_no_session_or_handle.
Print Assumptions successful_fresh_commit_preserves_original_bound_and_prefix.
Print Assumptions existing_normalize_publication_is_unchanged.
End AuthoredSyntheticMaterialization.
