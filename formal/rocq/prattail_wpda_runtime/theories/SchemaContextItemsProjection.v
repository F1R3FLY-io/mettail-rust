(** Runtime schema context-items adapter and capture-budget composition.

    Rust target: mettail-elab/src/schema/authored_capture.rs.
    Judgement Rule shallow observation invokes the EXISTING
    try_convert_term_context_to_items_with once. BNF copying and the normalized
    context Option are unchanged. No traversal, normalizer, parser, or recursive
    source reconstruction is introduced here.

    SourceType/parameter vocabulary is reused from the checked authored capture
    and original converter models. Runtime schema Collection(Map,k,Some(v))
    corresponds to ExistingType(SMapType k v); unary collections remain
    SCollection. Keyed PathMap remains RuntimeKeyedPathMap, NOT MapType; this
    converter has no matching shallow probe for it. Its separate owned-reader
    unsupported admission is not changed or proved away.

    R,N,E,Q,B retain their capture meanings. W is one capture-wide cumulative
    logical event charge: visit/frame/item=1, binding=2. R+E+Q+W must fit the
    existing item cap. Each generated legacy item adds one E and one Q, but no
    node. Collection separator copies use the existing string gate before
    construction; item names remain borrowed handles and are copied/charged by
    ordinary Name capture later. Original binding outputs are constructed under
    the same paid schedule, then discarded after successful conversion.

    Finite event lists below are proof observations, never allocated runtime
    preflight rosters. Existing ContextItemsAdmission is instantiated with
    name-byte cost zero; its collection charge splits into W and actual copied
    separator bytes B. Machine ceilings/canonical caps are parameters, supplied
    by the existing runtime constants. This is a conservative retained-domain
    logical-work bound, not canonical admission equivalence, instruction count,
    physical allocation/RSS, or arbitrary-reader termination.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import
  TermContextItemsProjection ContextItemsAdmission AuthoredRuntimeCaptureAdmission
  AuthoredRuleStoreProjection SchemaAuthoredContextProjection.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.
Set Implicit Arguments.

Module SchemaContextItemsProjection.
Module C := TermContextItemsProjection.TermContextItemsProjection.
Module I := ContextItemsAdmission.ContextItemsAdmission.
Module R := AuthoredRuntimeCaptureAdmission.AuthoredRuntimeCaptureAdmission.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module S := SchemaAuthoredContextProjection.SchemaAuthoredContextProjection.

(** Exact source embedding: no newly invented source AST vocabulary. *)
Definition context_type identity (source : A.SourceType) : C.SourceType :=
  match source with
  | A.ExistingType ty => match ty with
    | A.B.SBase name => C.Base name
    | A.B.SCollection kind element => C.Collection kind element
    | A.B.SMapType key value => C.MapType key value
    | A.B.SArrow domain codomain => C.Arrow domain codomain
    | A.B.STypeOther _ => C.Other identity end
  | A.ExistingMultiBinder inner => C.MultiBinder inner
  | A.RuntimeKeyedPathMap _ _ => C.Other identity
  end.

Definition schema_probes (types : nat -> A.SourceType) : C.Probes :=
  {| C.base_name := fun ty => match types ty with
       A.ExistingType (A.B.SBase name) => Some name | _ => None end;
     C.collection := fun ty => match types ty with
       A.ExistingType (A.B.SCollection kind element) => Some (kind, element) | _ => None end;
     C.map_type := fun ty => match types ty with
       A.ExistingType (A.B.SMapType key value) => Some (key, value) | _ => None end;
     C.arrow := fun ty => match types ty with
       A.ExistingType (A.B.SArrow domain codomain) => Some (domain, codomain) | _ => None end;
     C.multi_binder := fun ty => match types ty with
       A.ExistingMultiBinder inner => Some inner | _ => None end |}.

Definition source_view terms types equal classify hash_map : C.Source :=
  {| C.terms := terms; C.types := fun ty => context_type ty (types ty);
     C.names_equal := equal; C.nonterminal_kind := classify; C.hash_map_kind := hash_map |}.

Theorem shallow_probe_projection_is_exact : forall terms types equal classify hash_map ty,
  let original := C.project_types (source_view terms types equal classify hash_map) in
  let shared := schema_probes types in
  C.base_name original ty = C.base_name shared ty /\
  C.collection original ty = C.collection shared ty /\
  C.map_type original ty = C.map_type shared ty /\
  C.arrow original ty = C.arrow shared ty /\
  C.multi_binder original ty = C.multi_binder shared ty.
Proof.
  intros; cbn. destruct (types ty) as [source|inner|key value];
    [destruct source| |]; cbn; repeat split; reflexivity.
Qed.

Theorem schema_finite_converter_execution_reuses_original : forall fuel terms types equal classify hash_map st,
  C.run fuel (C.shared_step (source_view terms types equal classify hash_map)) st =
  C.run fuel (C.source_step (source_view terms types equal classify hash_map)) st.
Proof. intros; apply C.every_finite_execution_preserves_outputs_bindings_and_order. Qed.

Theorem keyed_pathmap_is_not_silently_a_map : forall identity key value,
  context_type identity (A.RuntimeKeyedPathMap key value) = C.Other identity.
Proof. reflexivity. Qed.

Definition realize_item (kind : nat -> A.NonterminalKind)
    (collection : nat -> A.S.CollectionKind) item : A.LegacyPayload :=
  match item with
  | C.NT name tag => A.Nonterminal (A.Ref name) (kind tag)
  | C.Binder name => A.Binder (A.Ref name)
  | C.Coll tag name separator =>
      A.LegacyCollection (collection tag) (A.Ref name) separator None None
  end.

Theorem each_generated_item_has_one_original_name_edge : forall kind collection item,
  List.length (A.legacy_edges (realize_item kind collection item)) = 1.
Proof. intros kind collection []; reflexivity. Qed.

Theorem generated_collection_keeps_exact_separator_and_no_delimiters :
  forall kind collection tag name separator,
  realize_item kind collection (C.Coll tag name separator) =
  A.LegacyCollection (collection tag) (A.Ref name) separator None None.
Proof. reflexivity. Qed.

Definition work_charge event := match event with
| C.ReadParam _ | C.EnterOptional _ | C.MakeNT _ | C.MakeBinder _ | C.MakeCollection _ _ _ => 1
| C.AddBinding _ _ => 2 | _ => 0 end.
Definition item_charge event := match event with
| C.MakeNT _ | C.MakeBinder _ | C.MakeCollection _ _ _ => 1 | _ => 0 end.
Definition separator_charge event := match event with
| C.MakeCollection _ _ separator => String.length separator | _ => 0 end.

Theorem borrowed_name_instantiation_splits_work_and_copy_bytes : forall event,
  I.event_charge (fun _ => 0) event = work_charge event + separator_charge event.
Proof. intros []; cbn; lia. Qed.

Lemma spent_app : forall charge first second,
  I.spent charge (first ++ second) = I.spent charge first + I.spent charge second.
Proof. intros charge first; induction first; intros; cbn; [reflexivity|rewrite IHfirst; lia]. Qed.

Theorem aggregate_rules_do_not_reset_conversion_work : forall first second,
  I.spent work_charge (first ++ second) =
  I.spent work_charge first + I.spent work_charge second.
Proof. apply spent_app. Qed.

Theorem every_parameter_occurrence_is_charged : forall events,
  I.parameter_visits events <= I.spent work_charge events.
Proof.
  induction events as [|event rest IH]; [cbn; lia|].
  destruct event; cbn [I.parameter_visits I.spent work_charge]; lia.
Qed.

Theorem repeated_parameter_identity_is_not_free : forall handle count,
  I.spent work_charge (repeat (C.ReadParam handle) count) = count.
Proof. intros; induction count; cbn; congruence. Qed.

Theorem discarded_bindings_still_cost_original_construction : forall binder body,
  work_charge (C.AddBinding binder body) = 2.
Proof. reflexivity. Qed.

Record Ledger := {
  roots : nat; nodes : nat; edges : nat; slots : nat; bytes : nat; work : nat
}.
Definition extended_valid word node_cap item_cap st :=
  match R.checked_total word [roots st; edges st; slots st; work st] with
  | None => false
  | Some total => (nodes st <=? word) && (nodes st <=? node_cap) && (total <=? item_cap)
  end.
Definition advance st event copied :=
  {| roots := roots st; nodes := nodes st;
     edges := edges st + item_charge event; slots := slots st + item_charge event;
     bytes := copied; work := work st + work_charge event |}.

(** Callback admission result only. It does not claim rollback of the private
    original string counter after aggregate string refusal. No failed counter
    state or private partially constructed Rule is published. *)
Definition admit_event word node_cap item_cap single total st event : option Ledger :=
  let candidate := advance st event (bytes st) in
  if extended_valid word node_cap item_cap candidate then
    match event with
    | C.MakeCollection _ _ separator =>
      match R.original_string_gate word single total (bytes st) (String.length separator) with
      | (Some _, copied) => Some (advance st event copied)
      | (None, _) => None end
    | _ => Some candidate end
  else None.

Theorem admitted_extended_totals_are_bounded : forall word nc ic st,
  extended_valid word nc ic st = true ->
  nodes st <= word /\ nodes st <= nc /\
  roots st + edges st + slots st + work st <= word /\
  roots st + edges st + slots st + work st <= ic.
Proof.
  intros word nc ic st H; unfold extended_valid in H.
  destruct (R.checked_total word [roots st; edges st; slots st; work st]) as [total|] eqn:E;
    [|discriminate].
  apply R.checked_total_exact_and_bounded in E; cbn in E.
  repeat rewrite andb_true_iff in H. destruct H as [[N Capped] Items].
  apply Nat.leb_le in N, Capped, Items. lia.
Qed.

Theorem extended_admission_implies_original_capture_domain : forall word nc ic st,
  extended_valid word nc ic st = true ->
  R.admit_sizes word nc ic (roots st) (nodes st) (edges st) (slots st) = true.
Proof.
  intros word nc ic st H.
  pose proof (@admitted_extended_totals_are_bounded word nc ic st H) as [NW [NC [IW IC]]].
  unfold R.admit_sizes.
  assert (Checked : R.checked_total word [roots st; edges st; slots st] =
    Some (roots st + (edges st + (slots st + 0)))).
  { apply R.checked_total_accepts_exactly_fitting_components; cbn; lia. }
  rewrite Checked. repeat rewrite andb_true_iff. repeat split; apply Nat.leb_le; lia.
Qed.

Theorem callback_preserves_single_precharged_rule_node : forall word nc ic single total st event next,
  admit_event word nc ic single total st event = Some next ->
  nodes next = nodes st /\ roots next = roots st /\
  edges next = edges st + item_charge event /\
  slots next = slots st + item_charge event /\
  work next = work st + work_charge event.
Proof.
  intros word nc ic single total st event next H.
  unfold admit_event in H.
  destruct (extended_valid word nc ic (advance st event (bytes st))); [|discriminate].
  destruct event; try (inversion H; subst; repeat split; reflexivity).
  destruct (R.original_string_gate word single total (bytes st) (String.length separator))
    as [[[]|] copied] eqn:E; [|discriminate].
  inversion H; subst; repeat split; reflexivity.
Qed.

Theorem collection_copy_is_prepaid_by_original_string_gate :
  forall word nc ic single total st tag name separator next,
  admit_event word nc ic single total st (C.MakeCollection tag name separator) = Some next ->
  bytes next = bytes st + String.length separator /\
  String.length separator <= single /\ bytes next <= word /\ bytes next <= total.
Proof.
  intros word nc ic single total st tag name separator next H.
  unfold admit_event in H.
  destruct (extended_valid word nc ic (advance st (C.MakeCollection tag name separator) (bytes st)));
    [|discriminate].
  destruct (R.original_string_gate word single total (bytes st) (String.length separator))
    as [[[]|] copied] eqn:E; [|discriminate].
  inversion H; subst; cbn.
  apply R.string_success_has_exact_size in E; exact E.
Qed.

Definition admitted_constructor {X} word nc ic single total st event (make : unit -> X) :=
  match admit_event word nc ic single total st event with
  | Some next => Some (next, make tt) | None => None end.

Theorem refusal_precedes_constructor_result : forall X word nc ic single total st event
  (make : unit -> X),
  admit_event word nc ic single total st event = None ->
  admitted_constructor word nc ic single total st event make = None.
Proof. intros; unfold admitted_constructor; now rewrite H. Qed.

Theorem successful_event_retains_checked_totals : forall word nc ic single total st event next,
  admit_event word nc ic single total st event = Some next ->
  extended_valid word nc ic next = true.
Proof.
  intros word nc ic single total st event next H; unfold admit_event in H.
  destruct (extended_valid word nc ic (advance st event (bytes st))) eqn:Gate;
    [|discriminate].
  destruct event; try (inversion H; subst; exact Gate).
  destruct (R.original_string_gate word single total (bytes st) (String.length separator))
    as [[[]|] copied] eqn:E; [|discriminate].
  inversion H; subst; exact Gate.
Qed.

(** Relation over the callbacks of one or several original finite executions;
    this is not a new runtime worker or an allocated event list. *)
Inductive PaidEvents word nc ic single total : Ledger -> list C.Event -> Ledger -> Prop :=
| PaidEmpty st : PaidEvents word nc ic single total st [] st
| PaidNext st next final event rest :
    admit_event word nc ic single total st event = Some next ->
    PaidEvents word nc ic single total next rest final ->
    PaidEvents word nc ic single total st (event :: rest) final.

Theorem paid_events_have_exact_content_and_work : forall word nc ic single total st events final,
  PaidEvents word nc ic single total st events final ->
  nodes final = nodes st /\ roots final = roots st /\
  edges final = edges st + I.spent item_charge events /\
  slots final = slots st + I.spent item_charge events /\
  work final = work st + I.spent work_charge events.
Proof.
  intros word nc ic single total st events final Paid; induction Paid.
  - cbn; repeat split; lia.
  - pose proof (@callback_preserves_single_precharged_rule_node
      word nc ic single total st event next H) as Step.
    destruct Step as [N [R0 [E [Q W]]]].
    destruct IHPaid as [IN [IR [IE [IQ IW]]]].
    cbn; repeat split; lia.
Qed.

Theorem paid_parameter_occurrences_obey_aggregate_cap :
  forall word nc ic single total st events final,
  PaidEvents word nc ic single total st events final ->
  extended_valid word nc ic final = true ->
  I.parameter_visits events + work st <= ic.
Proof.
  intros word nc ic single total st events final Paid Valid.
  pose proof (@paid_events_have_exact_content_and_work
    word nc ic single total st events final Paid) as Exact.
  pose proof (@admitted_extended_totals_are_bounded word nc ic final Valid) as Bound.
  pose proof (every_parameter_occurrence_is_charged events) as Visits.
  destruct Exact as [_ [_ [_ [_ W]]]]; destruct Bound as [_ [_ [_ Cap]]]; lia.
Qed.

(** All-or-error output composition, not a second traversal. Allocation failure
    is represented by None just like callback refusal. Binding values belong to
    the successful original Buffer before this caller projects its item field. *)
Definition rule_items kind collection form bnf (conversion : option C.Buffer) :=
  match form with
  | S.Bnf => Some bnf
  | S.Judgement => option_map (fun out => map (realize_item kind collection) (C.items out)) conversion
  end.
Theorem refused_judgement_does_not_publish_partial_items : forall kind collection bnf,
  rule_items kind collection S.Judgement bnf None = None.
Proof. reflexivity. Qed.
Theorem successful_judgement_uses_original_converted_items : forall kind collection bnf out,
  rule_items kind collection S.Judgement bnf (Some out) =
    Some (map (realize_item kind collection) (C.items out)).
Proof. reflexivity. Qed.
Theorem bnf_items_do_not_run_or_depend_on_conversion : forall kind collection bnf conversion,
  rule_items kind collection S.Bnf bnf conversion = Some bnf.
Proof. reflexivity. Qed.
Theorem normalized_judgement_context_is_unchanged : forall (params : list nat),
  S.retained_context S.Judgement params = Some params.
Proof. reflexivity. Qed.
Theorem empty_and_nonempty_bnf_presence_are_unchanged : forall (first : nat) (rest : list nat),
  S.retained_context S.Bnf (@nil nat) = None /\
  S.retained_context S.Bnf (first :: rest) = Some (first :: rest).
Proof. intros; split; reflexivity. Qed.

Print Assumptions shallow_probe_projection_is_exact.
Print Assumptions schema_finite_converter_execution_reuses_original.
Print Assumptions keyed_pathmap_is_not_silently_a_map.
Print Assumptions each_generated_item_has_one_original_name_edge.
Print Assumptions generated_collection_keeps_exact_separator_and_no_delimiters.
Print Assumptions borrowed_name_instantiation_splits_work_and_copy_bytes.
Print Assumptions aggregate_rules_do_not_reset_conversion_work.
Print Assumptions every_parameter_occurrence_is_charged.
Print Assumptions repeated_parameter_identity_is_not_free.
Print Assumptions discarded_bindings_still_cost_original_construction.
Print Assumptions admitted_extended_totals_are_bounded.
Print Assumptions extended_admission_implies_original_capture_domain.
Print Assumptions callback_preserves_single_precharged_rule_node.
Print Assumptions collection_copy_is_prepaid_by_original_string_gate.
Print Assumptions refusal_precedes_constructor_result.
Print Assumptions successful_event_retains_checked_totals.
Print Assumptions paid_events_have_exact_content_and_work.
Print Assumptions paid_parameter_occurrences_obey_aggregate_cap.
Print Assumptions refused_judgement_does_not_publish_partial_items.
Print Assumptions successful_judgement_uses_original_converted_items.
Print Assumptions bnf_items_do_not_run_or_depend_on_conversion.
Print Assumptions normalized_judgement_context_is_unchanged.
Print Assumptions empty_and_nonempty_bnf_presence_are_unchanged.
End SchemaContextItemsProjection.
