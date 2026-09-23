(** Retained source facts for the ORIGINAL literal and collection helpers.

    Extends AuthoredDeclarationsProjection, not the capture controller. Source
    observations are explicit data: unavailable differs from known absence.
    Macro observations are the existing shallow byte/native/element probes on
    LangType.native_type AFTER original parser normalization. Their source laws
    remain callback obligations; no new syn parser or generic-argument walker is
    modeled here. A clone-returning element probe may use a prepaid temporary
    Ident roster kept alive for capture; it must preserve original Ident Eq.

    Canonical scalar width/aliases come from validated raw Carrier observations,
    before BuiltinCarrier erases width. Extern is positive CanonicalOpaque, not
    a fabricated Other string or parsed URN. Canonical collection labels bypass
    native labeling; their element is the current validated Carrier.key, after
    composition/export renaming, never a duplicated pre-rename string. Existing
    NativeKind, collection delimiters, token/mode rosters and final binding IDs
    are unchanged. Native-value parity remains outside this source projection.

    Category capture order is name THEN known-present element, followed by the
    next category. Existing token/mode roots follow unchanged. The same capture
    worklist, checked root resolution and Name equality table are reused. A
    missing observation is not coerced to None and does not globally invalidate
    a store; availability is inspected only at the original selected helper site.

    Added logical work is prepaid before the three shallow source probes; an
    upper bound of three units per category is explicit, not instruction cost.
    The added root count is charged before root roster growth. Other spelling
    copies use the existing string gate; captured Name copies remain charged by
    the existing capture source, not twice by the header. No extra inline-field
    vector slots or invented arena nodes are charged. This is not an allocator,
    hashing or total source-adapter resource proof.

    Planned wire obligations: GrammarCore5 / LanguageCore6 / structural value7
    reject previous exact versions; canonical encoding retains every field.
    The structural commitment laws below are NOT hash injectivity or a proof of
    an implemented codec. Actual Serde/postcard/closed-value integration and
    regression tests must instantiate this boundary before activation.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import AuthoredDeclarationsProjection
  SchemaDeclarationCaptureProjection CanonicalOpaqueLabelProjection
  AuthoredRuntimeCaptureAdmission SchemaContextItemsProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.
Set Implicit Arguments.

Module AuthoredNativeObservationsProjection.
Module D := AuthoredDeclarationsProjection.AuthoredDeclarationsProjection.
Module A := D.A.
Module C := D.C.
Module S := SchemaDeclarationCaptureProjection.SchemaDeclarationCaptureProjection.
Module L := CanonicalOpaqueLabelProjection.CanonicalOpaqueLabelProjection.
Module P := L.P.
Module B := SchemaContextItemsProjection.SchemaContextItemsProjection.
Module R := AuthoredRuntimeCaptureAdmission.AuthoredRuntimeCaptureAdmission.

Inductive SourceObservation (T : Type) := Unavailable | Known (value : T).
Arguments Unavailable {T}.
Arguments Known {T} _.
Record Observations (Name : Type) := {
  byte_observation : SourceObservation bool;
  literal_observation : SourceObservation (option L.LiteralNativeObservation);
  element_observation : SourceObservation (option Name)
}.
Arguments byte_observation {Name} _.
Arguments literal_observation {Name} _.
Arguments element_observation {Name} _.
Definition absent {Name} : Observations Name :=
  {| byte_observation := Known false; literal_observation := Known None;
     element_observation := Known None |}.
Definition element_roots (facts : Observations (A.Handle A.NameTag)) :=
  match element_observation facts with
  | Known (Some element) => [A.edge element]
  | Known None | Unavailable => [] end.

Theorem availability_is_not_semantic_absence : forall Name,
  @Unavailable (option Name) <> Known None.
Proof. discriminate. Qed.
Theorem known_present_element_is_a_name_root : forall byte literal element,
  element_roots {| byte_observation := byte; literal_observation := literal;
    element_observation := Known (Some element) |} = [(A.NameTag, A.index element)].
Proof. reflexivity. Qed.

Section MacroProducer.
Context {Native Name : Type}.
Variable byte_probe : Native -> bool.
Variable native_probe : Native -> P.NativeType.
Variable element_probe : Native -> option Name.
Definition macro_observations native : Observations Name := match native with
| None => absent
| Some source => {| byte_observation := Known (byte_probe source);
    literal_observation := Known (Some (L.ExactNativeType (native_probe source)));
    element_observation := Known (element_probe source) |} end.
Theorem macro_projection_retains_exact_original_probe_results : forall source,
  byte_observation (macro_observations (Some source)) = Known (byte_probe source) /\
  literal_observation (macro_observations (Some source)) =
    Known (Some (L.ExactNativeType (native_probe source))) /\
  element_observation (macro_observations (Some source)) = Known (element_probe source).
Proof. repeat split; reflexivity. Qed.
Theorem macro_absence_does_not_invent_native_classification :
  macro_observations None = absent.
Proof. reflexivity. Qed.
Theorem captured_macro_label_inputs_preserve_original_selection : forall source,
  L.selected_label (byte_probe source) (L.ExactNativeType (native_probe source)) =
  P.selected_label (byte_probe source) (native_probe source).
Proof. intros; apply L.exact_selection_reuses_original_match. Qed.
End MacroProducer.

Definition scalar_native symbol :=
  if String.eqb symbol "BigRat" then P.CanonicalBigRat
  else if String.eqb symbol "Fixed" then P.CanonicalFixedPoint
  else P.original_from_type_str symbol.
Definition schema_observations carrier : Observations string := match carrier with
| None => absent
| Some (S.Scalar symbol) =>
    {| byte_observation := Known false;
       literal_observation := Known (Some (L.ExactNativeType (scalar_native symbol)));
       element_observation := Known None |}
| Some (S.Collection _ key _) =>
    {| byte_observation := Unavailable; literal_observation := Unavailable;
       element_observation := Known (Some key) |}
| Some (S.Extern _) =>
    {| byte_observation := Known false;
       literal_observation := Known (Some L.CanonicalOpaque);
       element_observation := Known None |} end.
Theorem all_original_scalar_widths_and_aliases_are_retained :
  map scalar_native S.scalar_symbols =
  [P.Int8; P.Int16; P.Int32; P.Int64; P.Int128; P.Isize;
   P.UInt8; P.UInt16; P.UInt32; P.UInt64; P.UInt128; P.Usize;
   P.Float32; P.Float64; P.BoolType; P.Str; P.Str; P.CanonicalBigInt;
   P.CanonicalBigRat; P.CanonicalFixedPoint].
Proof. vm_compute; reflexivity. Qed.
Theorem aliases_do_not_change_original_native_type_classifier :
  scalar_native "BigRat" = P.CanonicalBigRat /\
  scalar_native "Fixed" = P.CanonicalFixedPoint /\
  P.original_from_type_str "BigRat" = P.Other "BigRat" /\
  P.original_from_type_str "Fixed" = P.Other "Fixed".
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem extern_is_positive_opaque_not_an_other_string : forall urn,
  schema_observations (Some (S.Extern urn)) =
  {| byte_observation := Known false;
     literal_observation := Known (Some L.CanonicalOpaque);
     element_observation := Known None |}.
Proof. reflexivity. Qed.
Theorem collection_keeps_first_key_not_second_value : forall kind key value,
  element_observation (schema_observations (Some (S.Collection kind key value))) = Known (Some key) /\
  literal_observation (schema_observations (Some (S.Collection kind key value))) = Unavailable.
Proof. repeat split; reflexivity. Qed.

(** Mirrors the existing rename_category update of Collection.key/value. *)
Definition rename_name from to value := if String.eqb value from then to else value.
Definition rename_carrier from to carrier := match carrier with
| S.Collection kind key value => S.Collection kind (rename_name from to key)
    (option_map (rename_name from to) value)
| other => other end.
Theorem capture_reads_current_renamed_key : forall from to kind key value,
  element_observation (schema_observations (Some (rename_carrier from to (S.Collection kind key value)))) =
  Known (Some (rename_name from to key)).
Proof. reflexivity. Qed.
Theorem renamed_source_does_not_rewrite_scalar_type_or_extern_urn : forall from to symbol urn,
  rename_carrier from to (S.Scalar symbol) = S.Scalar symbol /\
  rename_carrier from to (S.Extern urn) = S.Extern urn.
Proof. repeat split; reflexivity. Qed.

Record Category := { base : D.CategoryDeclaration; observations : Observations (A.Handle A.NameTag) }.
Definition category_roots row := [A.edge (D.category_name (base row))] ++ element_roots (observations row).
Record Header := {
  categories : list Category; tokens : list D.TokenDeclaration;
  globals : list nat; modes : list D.ModeDeclaration
}.
Definition erase header : D.Header :=
  {| D.categories := map base (categories header); D.tokens := tokens header;
     D.global_source_tokens := globals header; D.modes := modes header |}.
Definition names header := flat_map category_roots (categories header) ++
  flat_map D.token_names (tokens header) ++ map (fun row => A.edge (D.mode_name row)) (modes header).
Definition roots rules header := rules ++ names header.
Definition extra_count header := List.length (flat_map (fun row => element_roots (observations row)) (categories header)).

Theorem element_occurs_immediately_after_its_category : forall row rest element,
  element_observation (observations row) = Known (Some element) ->
  flat_map category_roots (row :: rest) =
    A.edge (D.category_name (base row)) :: A.edge element :: flat_map category_roots rest.
Proof. intros; cbn; unfold category_roots, element_roots; rewrite H; reflexivity. Qed.
Lemma category_root_length : forall rows,
  List.length (flat_map category_roots rows) = List.length rows +
    List.length (flat_map (fun row => element_roots (observations row)) rows).
Proof.
  induction rows as [|row rest IH]; [reflexivity|].
  change (List.length (category_roots row ++ flat_map category_roots rest) =
    S (List.length rest) + List.length (element_roots (observations row) ++
      flat_map (fun row => element_roots (observations row)) rest)).
  rewrite !length_app, IH; unfold category_roots at 1.
  rewrite length_app; cbn; lia.
Qed.
Theorem extra_root_count_is_exact : forall header,
  List.length (names header) = List.length (D.declaration_names (erase header)) + extra_count header.
Proof.
  intros; unfold names, D.declaration_names, erase, extra_count; cbn.
  repeat rewrite length_app; repeat rewrite length_map; rewrite category_root_length; lia.
Qed.
Theorem original_rule_positions_are_unchanged : forall rules header index edge,
  nth_error rules index = Some edge -> nth_error (roots rules header) index = Some edge.
Proof.
  intros; unfold roots; rewrite nth_error_app1; [exact H|].
  apply nth_error_Some; rewrite H; discriminate.
Qed.
Theorem existing_capture_returns_the_extended_ordered_roster :
  forall graph admit rules header st nodes ids,
  C.Step graph admit (roots rules header) st (C.Complete nodes ids) ->
  List.length ids = List.length (roots rules header) /\
  forall index edge, nth_error (roots rules header) index = Some edge ->
    exists target, nth_error ids index = Some target /\ C.memo st edge = Some (C.Ready target).
Proof. intros; eapply C.returned_roots_keep_order_and_multiplicity; exact H. Qed.
Theorem existing_finite_capture_invariant_needs_no_new_controller :
  forall graph admit rules header count after,
  C.FiniteRun graph admit (roots rules header) (C.initial (roots rules header)) count after ->
  A.ValidArena (C.arena after) /\ C.ReadyTyped (C.arena after) (C.memo after).
Proof.
  intros; destruct (@C.finite_capture_postorder_and_typed_store _ _ _ _ _ H)
    as [Valid [_ [Typed _]]]; auto.
Qed.
Definition names_valid arena header := forallb (A.reference_valid arena) (names header).
Theorem checked_extended_roots_have_actual_tags : forall arena header reference,
  names_valid arena header = true -> In reference (names header) ->
  exists target, nth_error arena (snd reference) = Some target /\
    A.node_tag target = fst reference /\ snd reference < List.length arena.
Proof.
  intros arena header reference Valid Member; unfold names_valid in Valid.
  apply forallb_forall with (x := reference) in Valid; [|exact Member].
  apply A.reference_valid_sound; exact Valid.
Qed.

(** The actual name occurrence mapping, including checked failure, not a new
    capture walk. Literal/native/string payloads are moved without alteration. *)
Definition remap_element (resolve : C.Resolver)
    (value : SourceObservation (option (A.Handle A.NameTag)))
    : option (SourceObservation (option (A.Handle A.NameTag))) := match value with
| Unavailable => Some Unavailable
| Known None => Some (Known None)
| Known (Some id) => match resolve (A.edge id) with
    | None => None | Some target => Some (Known (Some (A.Ref target))) end end.
Definition remap_category (resolve : C.Resolver) row :=
  C.bind (resolve (A.edge (D.category_name (base row)))) (fun name =>
  C.bind (remap_element resolve (element_observation (observations row))) (fun element =>
  Some {| base := {| D.category_name := A.Ref name;
    D.category_native := D.category_native (base row);
    D.category_collection := D.category_collection (base row) |};
    observations := {| byte_observation := byte_observation (observations row);
      literal_observation := literal_observation (observations row);
      element_observation := element |} |})).
Theorem remap_retains_unavailable_and_known_absence_separately : forall resolve,
  remap_element resolve Unavailable = Some Unavailable /\
  remap_element resolve (Known None) = Some (Known None).
Proof. repeat split; reflexivity. Qed.
Theorem present_element_cannot_survive_failed_resolution : forall resolve element,
  resolve (A.edge element) = None -> remap_element resolve (Known (Some element)) = None.
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem remap_moves_all_nonname_payloads_exactly : forall resolve before after,
  remap_category resolve before = Some after ->
  D.category_native (base after) = D.category_native (base before) /\
  D.category_collection (base after) = D.category_collection (base before) /\
  byte_observation (observations after) = byte_observation (observations before) /\
  literal_observation (observations after) = literal_observation (observations before).
Proof.
  intros resolve before after H; unfold remap_category in H.
  destruct (resolve (A.edge (D.category_name (base before)))); cbn in H; [|discriminate].
  destruct (remap_element resolve (element_observation (observations before))); cbn in H; [|discriminate].
  inversion H; subst; repeat split; reflexivity.
Qed.
Theorem remap_has_exact_original_name_then_element_order : forall resolve before after,
  remap_category resolve before = Some after ->
  C.map_checked resolve (category_roots before) = Some (map snd (category_roots after)).
Proof.
  intros resolve [old facts] after H; destruct old as [name native collection];
    destruct facts as [byte literal element]; unfold remap_category in H; cbn in H.
  destruct (resolve (A.edge name)) as [target|] eqn:N; cbn in H; [|discriminate].
  destruct element as [|[element|]]; cbn in H.
  - inversion H; subst; cbn; rewrite N; reflexivity.
  - destruct (resolve (A.edge element)) as [resolved|] eqn:E; cbn in H; [|discriminate].
    inversion H; subst; cbn; rewrite N, E; reflexivity.
  - inversion H; subst; cbn; rewrite N; reflexivity.
Qed.

(** Inline facts allocate no added vector roster. R is exact; W prepays a
    fixed upper bound before source probes, including skipped optional probes. *)
Definition observation_work category_count := 3 * category_count.
Definition advance st added_roots additional_work : B.Ledger :=
  {| B.roots := B.roots st + added_roots; B.nodes := B.nodes st;
     B.edges := B.edges st; B.slots := B.slots st; B.bytes := B.bytes st;
     B.work := B.work st + additional_work |}.
Definition prepay word nc ic st added_roots additional_work :=
  let next := advance st added_roots additional_work in
  if B.extended_valid word nc ic next then Some next else None.
Definition probe_after_paid {T} word nc ic st category_count (probe : unit -> T) :=
  match prepay word nc ic st 0 (observation_work category_count) with
  | None => None | Some paid => Some (paid, probe tt) end.
Theorem refused_probe_payment_has_no_observation_result : forall T word nc ic st count (probe : unit -> T),
  prepay word nc ic st 0 (observation_work count) = None ->
  probe_after_paid word nc ic st count probe = None.
Proof. intros; unfold probe_after_paid; rewrite H; reflexivity. Qed.
Theorem exact_additional_root_payment : forall st header,
  B.roots (advance st (extra_count header) 0) = B.roots st + extra_count header /\
  B.nodes (advance st (extra_count header) 0) = B.nodes st /\
  B.edges (advance st (extra_count header) 0) = B.edges st /\
  B.slots (advance st (extra_count header) 0) = B.slots st /\
  B.bytes (advance st (extra_count header) 0) = B.bytes st.
Proof. repeat split; reflexivity. Qed.
Theorem paid_extension_keeps_existing_aggregate_capture_domain : forall word nc ic st roots work next,
  prepay word nc ic st roots work = Some next ->
  B.roots next + B.edges next + B.slots next + B.work next <= ic /\
  R.admit_sizes word nc ic (B.roots next) (B.nodes next) (B.edges next) (B.slots next) = true.
Proof.
  intros word nc ic st added work next H; unfold prepay in H;
    destruct (B.extended_valid word nc ic (advance st added work)) eqn:E; [|discriminate].
  inversion H; subst; split.
  - pose proof (@B.admitted_extended_totals_are_bounded _ _ _ _ E); tauto.
  - apply B.extended_admission_implies_original_capture_domain; exact E.
Qed.
Theorem header_and_observation_work_accumulate : forall counts oldroots st count,
  B.work (advance (S.prepaid counts oldroots st) 0 (observation_work count)) =
  B.work st + S.extra_work counts + observation_work count.
Proof. reflexivity. Qed.
Definition other_payload_copy {T} word single total used spelling (copy : unit -> T) :=
  R.copy_after_string_gate word single total used (String.length spelling) copy.
Theorem other_spelling_refusal_precedes_owned_copy : forall T word single total used spelling next (copy : unit -> T),
  R.original_string_gate word single total used (String.length spelling) = (None, next) ->
  other_payload_copy word single total used spelling copy = None.
Proof. intros; unfold other_payload_copy; eapply R.refused_string_has_no_copied_result; exact H. Qed.
Theorem accepted_other_string_has_exact_aggregate_bytes : forall word single total used spelling next,
  R.original_string_gate word single total used (String.length spelling) = (Some tt, next) ->
  next = used + String.length spelling /\ String.length spelling <= single /\ next <= word /\ next <= total.
Proof. intros; eapply R.string_success_has_exact_size; exact H. Qed.

(** Exact-format gate contract; implementation must bump all three constants
    and domain strings and preserve canonical re-encoding checks together. *)
Definition current_versions grammar language wire :=
  Nat.eqb grammar 5 && Nat.eqb language 6 && Nat.eqb wire 7.
Theorem preceding_exact_formats_are_rejected :
  current_versions 4 6 7 = false /\ current_versions 5 5 7 = false /\
  current_versions 5 6 6 = false /\ current_versions 5 6 7 = true.
Proof. repeat split; reflexivity. Qed.
Definition semantic_fields (other : nat) (header : Header) := (other, header).
Theorem commitment_input_cannot_erase_observations : forall other first second,
  semantic_fields other first = semantic_fields other second -> first = second.
Proof. intros; inversion H; reflexivity. Qed.

Print Assumptions availability_is_not_semantic_absence.
Print Assumptions known_present_element_is_a_name_root.
Print Assumptions macro_projection_retains_exact_original_probe_results.
Print Assumptions captured_macro_label_inputs_preserve_original_selection.
Print Assumptions all_original_scalar_widths_and_aliases_are_retained.
Print Assumptions aliases_do_not_change_original_native_type_classifier.
Print Assumptions extern_is_positive_opaque_not_an_other_string.
Print Assumptions collection_keeps_first_key_not_second_value.
Print Assumptions capture_reads_current_renamed_key.
Print Assumptions renamed_source_does_not_rewrite_scalar_type_or_extern_urn.
Print Assumptions element_occurs_immediately_after_its_category.
Print Assumptions extra_root_count_is_exact.
Print Assumptions original_rule_positions_are_unchanged.
Print Assumptions existing_capture_returns_the_extended_ordered_roster.
Print Assumptions existing_finite_capture_invariant_needs_no_new_controller.
Print Assumptions checked_extended_roots_have_actual_tags.
Print Assumptions remap_retains_unavailable_and_known_absence_separately.
Print Assumptions present_element_cannot_survive_failed_resolution.
Print Assumptions remap_moves_all_nonname_payloads_exactly.
Print Assumptions remap_has_exact_original_name_then_element_order.
Print Assumptions refused_probe_payment_has_no_observation_result.
Print Assumptions exact_additional_root_payment.
Print Assumptions paid_extension_keeps_existing_aggregate_capture_domain.
Print Assumptions header_and_observation_work_accumulate.
Print Assumptions other_spelling_refusal_precedes_owned_copy.
Print Assumptions accepted_other_string_has_exact_aggregate_bytes.
Print Assumptions preceding_exact_formats_are_rejected.
Print Assumptions commitment_input_cannot_erase_observations.
End AuthoredNativeObservationsProjection.
