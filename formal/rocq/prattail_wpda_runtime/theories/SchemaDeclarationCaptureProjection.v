(** Canonical schema declaration observations and producer-site binding.

    Sources: mettail-elab/src/schema.rs::decode_type, decode_carrier,
    LanguageSchema::lower and add_token; the existing core declaration capture,
    literal-name selector and binding builder. This is a shallow adapter model,
    NOT another grammar decoder, capture controller, parser or evaluator.

    Carrier keeps the rich closed collection/extern payload. The independent
    optional native observation uses the original twenty-kind classifier.
    Canonical BigRat/Fixed symbols project to the existing canonical kinds;
    the original Rust last-segment classifier remains unchanged. Collection
    and extern presence projects to Other in this scoped opaque observation.
    No arbitrary registered Rust wrapper equivalence, native value/decoder,
    suffix/error parity or Rust-path/fingerprint reconstruction follows.
    The FIPS III.4.2 paragraph requiring six extra NativeKind variants needs a
    focused amendment to describe this separation; it is not evidence that
    the original classifier already implements that richer alphabet.

    Finite accepted source data is the domain: invalid raw Carrier forms remain
    the existing decoder's refusal. Names below are schema strings; runtime
    String equality is not asserted equal to arbitrary macro Ident equality.
    Headers retain explicit globals then literals then ordered mode tokens;
    execution still appends literals then globals then mode tokens. Actual
    append receipts, not computed names or guessed IDs, fill binding slots.

    Header/remap/builder vectors are prepaid cumulative logical contents. R
    counts combined capture roots, N actual observed nodes, E arena reference
    fields, Q vector contents, B copied bytes, W finite source observation work.
    Selector comparisons are prepaid before calling the shared selector once.
    This is not instruction/allocator/RSS accounting or an assertion that the
    retained-domain admission equals canonical input admission. Existing
    capture/controller and context-event proofs are reused without new fuel.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import NativeKindProjection LiteralNameProjection
  AuthoredDeclarationsProjection AuthoredDeclarationBindingProjection
  SchemaContextItemsProjection AuthoredRuntimeCaptureAdmission ReconstructionWorkBudget.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.
Set Implicit Arguments.

Module SchemaDeclarationCaptureProjection.
Module K := NativeKindProjection.NativeKindProjection.
Module N := K.N.
Module L := LiteralNameProjection.LiteralNameProjection.
Module D := AuthoredDeclarationsProjection.AuthoredDeclarationsProjection.
Module B := AuthoredDeclarationBindingProjection.AuthoredDeclarationBindingProjection.
Module S := SchemaContextItemsProjection.SchemaContextItemsProjection.
Module R := AuthoredRuntimeCaptureAdmission.AuthoredRuntimeCaptureAdmission.

(** Only immediate accepted Carrier fields, not a reconstructed semantic AST. *)
Inductive CarrierObservation :=
| Scalar (symbol : string)
| Collection (kind : nat) (key : string) (value : option string)
| Extern (urn : string).
Definition scalar_symbols :=
  ["i8"; "i16"; "i32"; "i64"; "i128"; "isize";
   "u8"; "u16"; "u32"; "u64"; "u128"; "usize";
   "f32"; "f64"; "bool"; "str"; "String"; "BigInt"; "BigRat"; "Fixed"].
Definition scalar_native symbol :=
  if String.eqb symbol "BigRat" then N.CanonicalBigRat
  else if String.eqb symbol "Fixed" then N.CanonicalFixedPoint
  else K.original_segment_match symbol.
Definition native_observation carrier : option K.Kind :=
  match carrier with
  | None => None
  | Some (Scalar symbol) => Some (scalar_native symbol)
  | Some (Collection _ _ _) | Some (Extern _) => Some N.Other
  end.
Theorem all_accepted_scalar_observations :
  map scalar_native scalar_symbols =
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize;
   N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize;
   N.Float32; N.Float64; N.BoolKind; N.Str; N.Str; N.CanonicalBigInt;
   N.CanonicalBigRat; N.CanonicalFixedPoint].
Proof. vm_compute; reflexivity. Qed.
Theorem aliases_do_not_change_original_classifier :
  scalar_native "BigRat" = N.CanonicalBigRat /\
  scalar_native "Fixed" = N.CanonicalFixedPoint /\
  K.original_segment_match "BigRat" = N.Other /\
  K.original_segment_match "Fixed" = N.Other.
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem non_alias_uses_original_classifier : forall symbol,
  symbol <> "BigRat" -> symbol <> "Fixed" ->
  scalar_native symbol = K.original_segment_match symbol.
Proof.
  intros symbol Rat Fixed; unfold scalar_native.
  destruct (String.eqb symbol "BigRat") eqn:E;
    [apply String.eqb_eq in E; contradiction|].
  destruct (String.eqb symbol "Fixed") eqn:F;
    [apply String.eqb_eq in F; contradiction|reflexivity].
Qed.
Theorem absent_and_opaque_are_distinct : forall kind key value urn,
  native_observation None = None /\
  native_observation (Some (Collection kind key value)) = Some N.Other /\
  native_observation (Some (Extern urn)) = Some N.Other.
Proof. intros; repeat split; reflexivity. Qed.

Record Category := {
  occurrence : nat; category_name : string;
  carrier : option CarrierObservation;
  collection : option D.CollectionDeclaration
}.
Definition retain_category row := (row, native_observation (carrier row)).
Theorem native_projection_does_not_erase_carrier_or_delimiters : forall row,
  carrier (fst (retain_category row)) = carrier row /\
  collection (fst (retain_category row)) = collection row.
Proof. intros; split; reflexivity. Qed.
Definition selector_category row : @L.Category string :=
  {| L.source_id := occurrence row; L.source_name := category_name row;
     L.source_native := native_observation (carrier row) |}.
Definition selector_reader : @L.Reader string Category :=
  {| L.category_id := occurrence; L.category_name := category_name;
     L.category_native := fun row => native_observation (carrier row) |}.
Definition borrowed_name_constructors : @L.Constructors string string :=
  {| L.clone_original := fun original => original;
     L.construct_standard := fun variant _ => variant |}.

Lemma find_schema_categories : forall original categories,
  let found := L.shared_find String.eqb selector_reader original categories in
  L.source_find String.eqb original (map selector_category categories) =
  (option_map selector_category (fst found), snd found).
Proof.
  intros original categories; induction categories as [|row rest IH]; cbn.
  - reflexivity.
  - destruct (String.eqb (category_name row) original); [reflexivity|].
    rewrite IH. destruct (L.shared_find String.eqb selector_reader original rest); reflexivity.
Qed.
Theorem shared_literal_selector_receives_exact_schema_observations :
  forall original categories,
  L.shared_select String.eqb selector_reader borrowed_name_constructors original categories =
  (L.interpret borrowed_name_constructors
     (fst (L.source_select String.eqb original (map selector_category categories))),
   snd (L.source_select String.eqb original (map selector_category categories))).
Proof.
  intros; unfold L.shared_select, L.source_select; rewrite find_schema_categories.
  destruct (L.shared_find String.eqb selector_reader original categories)
    as [[row|] trace]; cbn; [|reflexivity].
  destruct (native_observation (carrier row)) as [kind|]; [|reflexivity].
  destruct (K.standard_token_variant kind); reflexivity.
Qed.
Definition literal_name original categories :=
  fst (L.shared_select String.eqb selector_reader borrowed_name_constructors original categories).
Definition compared_count original categories :=
  List.length (snd (L.shared_find String.eqb selector_reader original categories)).
Theorem selector_comparison_trace_is_prepaid : forall original categories,
  compared_count original categories <= 2 * List.length categories.
Proof.
  intros original categories; unfold compared_count.
  induction categories as [|row rest IH]; cbn; [lia|].
  destruct (String.eqb (category_name row) original); cbn; [lia|].
  destruct (L.shared_find String.eqb selector_reader original rest) as [found trace] eqn:E.
  cbn in IH |- *. lia.
Qed.
(** Two events per actual comparison; the budget charges one comparison unit.
    The constructors above return borrowed strings: only Name capture copies. *)

Record Token := {
  token_name : string; token_category : option string;
  has_evaluation : bool; token_push : option string
}.
Record TokenObservation := {
  observed_name : string; observed_category : option string;
  from_literals : bool; observed_evaluation : bool; observed_push : option string
}.
Definition explicit_token row :=
  {| observed_name := token_name row; observed_category := token_category row;
     from_literals := false; observed_evaluation := has_evaluation row;
     observed_push := token_push row |}.
Definition literal_token categories category :=
  {| observed_name := literal_name category categories; observed_category := Some category;
     from_literals := true; observed_evaluation := true; observed_push := None |}.
Theorem literal_only_renames_name_not_source_category : forall categories category,
  observed_category (literal_token categories category) = Some category /\
  from_literals (literal_token categories category) = true /\
  observed_evaluation (literal_token categories category) = true /\
  observed_push (literal_token categories category) = None.
Proof. intros; repeat split; reflexivity. Qed.
Theorem explicit_flags_and_optional_names_are_not_defaulted : forall row,
  observed_name (explicit_token row) = token_name row /\
  observed_category (explicit_token row) = token_category row /\
  observed_evaluation (explicit_token row) = has_evaluation row /\
  observed_push (explicit_token row) = token_push row /\
  from_literals (explicit_token row) = false.
Proof. intros; repeat split; reflexivity. Qed.

(** Source positions are independent of lowered token spelling and IDs.
    mode_rows is the concatenation of the unchanged ordered nested mode loops.
    The implicit Identifier is already in prior; synthetic terminals follow. *)
Section Roster.
Context {Row : Type}.
Definition source_roster (globals literals mode_rows : list Row) := globals ++ literals ++ mode_rows.
Definition execution_roster (globals literals mode_rows : list Row) := literals ++ globals ++ mode_rows.
Lemma nth_at_offset : forall (prefix suffix : list Row) index,
  nth_error (prefix ++ suffix) (List.length prefix + index) = nth_error suffix index.
Proof.
  intros; rewrite nth_error_app2 by lia.
  replace (List.length prefix + index - List.length prefix) with index by lia; reflexivity.
Qed.
Theorem explicit_row_keeps_source_slot_but_follows_literals : forall globals literals modes index row,
  nth_error globals index = Some row ->
  nth_error (source_roster globals literals modes) index = Some row /\
  nth_error (execution_roster globals literals modes) (List.length literals + index) = Some row.
Proof.
  intros globals literals modes index row Read.
  assert (Bound : index < List.length globals).
  { apply nth_error_Some; rewrite Read; discriminate. }
  unfold source_roster, execution_roster; split.
  - rewrite nth_error_app1 by exact Bound; exact Read.
  - rewrite nth_at_offset, nth_error_app1 by exact Bound; exact Read.
Qed.
Theorem literal_row_follows_source_globals_but_executes_first : forall globals literals modes index row,
  nth_error literals index = Some row ->
  nth_error (source_roster globals literals modes) (List.length globals + index) = Some row /\
  nth_error (execution_roster globals literals modes) index = Some row.
Proof.
  intros globals literals modes index row Read.
  assert (Bound : index < List.length literals).
  { apply nth_error_Some; rewrite Read; discriminate. }
  unfold source_roster, execution_roster; split.
  - rewrite nth_at_offset, nth_error_app1 by exact Bound; exact Read.
  - rewrite nth_error_app1 by exact Bound; exact Read.
Qed.
Theorem mode_rows_follow_both_global_blocks : forall globals literals modes index,
  nth_error (source_roster globals literals modes)
    (List.length globals + (List.length literals + index)) = nth_error modes index /\
  nth_error (execution_roster globals literals modes)
    (List.length literals + (List.length globals + index)) = nth_error modes index.
Proof. intros; unfold source_roster, execution_roster; split; repeat rewrite nth_at_offset; reflexivity. Qed.
End Roster.

Definition direct_receipt id := {| B.direct := id; B.typed_literal := None |}.
Theorem receipt_retains_actual_append_id : forall (prior : list nat) mode,
  nth_error (prior ++ [mode]) (B.direct (direct_receipt (List.length prior))) = Some mode /\
  B.typed_literal (direct_receipt (List.length prior)) = None.
Proof. intros; split; [apply B.append_site_returns_the_new_final_id|reflexivity]. Qed.
Theorem source_position_write_uses_actual_receipt : forall slots position id result,
  B.write_once slots position (direct_receipt id) = Some result ->
  nth_error result position = Some (Some (direct_receipt id)) /\
  List.length result = List.length slots.
Proof.
  intros; split; [eapply B.write_once_assigns_exact_requested_position|
    eapply B.write_once_preserves_roster_length]; eauto.
Qed.
Theorem completed_schema_rows_have_no_auxiliary_route : forall receipts,
  map B.typed_literal (map direct_receipt receipts) = repeat None (List.length receipts).
Proof. induction receipts; cbn; congruence. Qed.

(** Logical contents of the actual existing allocations, including temporary
    builder/finalization vectors. Moving index vectors/strings is not copying. *)
Record Counts := { cats : nat; globals : nat; literals : nat; mode_tokens : nat; modes : nat }.
Definition tokens counts := globals counts + literals counts + mode_tokens counts.
Definition initial_header_slots counts :=
  cats counts + tokens counts + (globals counts + literals counts) + modes counts + mode_tokens counts.
Definition remapped_header_slots counts := cats counts + tokens counts + modes counts.
Definition pending_slots counts := cats counts + 2 * tokens counts + modes counts.
Definition finish_slots counts := pending_slots counts + tokens counts.
Definition slot_phases counts :=
  [initial_header_slots counts; remapped_header_slots counts; pending_slots counts; finish_slots counts].
Definition extra_slots counts := total_charge (slot_phases counts).
Definition header_row_work counts := cats counts + tokens counts + modes counts.
Definition selector_work counts := cats counts * literals counts.
Definition extra_work counts := header_row_work counts + selector_work counts.
Definition header_counts_match counts header :=
  List.length (D.categories header) = cats counts /\
  List.length (D.tokens header) = tokens counts /\
  List.length (D.global_source_tokens header) = globals counts + literals counts /\
  List.length (D.modes header) = modes counts /\
  total_charge (map (fun mode => List.length (D.mode_source_tokens mode)) (D.modes header)) =
    mode_tokens counts.
Definition actual_header_slots header :=
  List.length (D.categories header) + List.length (D.tokens header) +
  List.length (D.global_source_tokens header) + List.length (D.modes header) +
  total_charge (map (fun mode => List.length (D.mode_source_tokens mode)) (D.modes header)).
Theorem header_counts_are_actual_vector_contents : forall counts header,
  header_counts_match counts header -> actual_header_slots header = initial_header_slots counts.
Proof.
  intros counts header [Cats [Tokens [Globals [Modes Nested]]]].
  unfold actual_header_slots, initial_header_slots; rewrite Cats, Tokens, Globals, Modes, Nested.
  reflexivity.
Qed.
Theorem binding_pending_counts_match_actual_builder : forall counts header,
  header_counts_match counts header ->
  List.length (B.pending_categories (B.initial header)) +
  List.length (B.pending_direct (B.initial header)) +
  List.length (B.pending_auxiliary (B.initial header)) +
  List.length (B.pending_modes (B.initial header)) = pending_slots counts.
Proof.
  intros counts header [Cats [Tokens [Globals [Modes Nested]]]].
  change (List.length (repeat (@None nat) (List.length (D.categories header))) +
    List.length (repeat (@None nat) (List.length (D.tokens header))) +
    List.length (repeat (@None (option nat)) (List.length (D.tokens header))) +
    List.length (repeat (@None nat) (List.length (D.modes header))) = pending_slots counts).
  repeat rewrite repeat_length.
  unfold pending_slots; rewrite Cats, Tokens, Modes; lia.
Qed.
Definition prepaid counts additional_roots st : S.Ledger :=
  {| S.roots := S.roots st + additional_roots; S.nodes := S.nodes st;
     S.edges := S.edges st; S.slots := S.slots st + extra_slots counts;
     S.bytes := S.bytes st; S.work := S.work st + extra_work counts |}.
Definition prepay word nc ic counts additional_roots st :=
  let next := prepaid counts additional_roots st in
  if S.extended_valid word nc ic next then Some next else None.
Theorem exact_allocation_phase_content_sum : forall counts,
  extra_slots counts = initial_header_slots counts + remapped_header_slots counts +
    2 * pending_slots counts + tokens counts.
Proof. intros; unfold extra_slots, slot_phases, finish_slots; cbn; lia. Qed.
Theorem header_charge_does_not_fabricate_nodes_edges_or_name_copies : forall counts roots st,
  S.nodes (prepaid counts roots st) = S.nodes st /\
  S.edges (prepaid counts roots st) = S.edges st /\
  S.bytes (prepaid counts roots st) = S.bytes st.
Proof. intros; repeat split; reflexivity. Qed.
Theorem successful_prepayment_is_aggregate_checked : forall word nc ic counts roots st next,
  prepay word nc ic counts roots st = Some next ->
  S.nodes next <= nc /\
  S.roots next + S.edges next + S.slots next + S.work next <= word /\
  S.roots next + S.edges next + S.slots next + S.work next <= ic.
Proof.
  intros word nc ic counts roots st next Paid; unfold prepay in Paid.
  destruct (S.extended_valid word nc ic (prepaid counts roots st)) eqn:E; [|discriminate].
  inversion Paid; subst next.
  pose proof (@S.admitted_extended_totals_are_bounded word nc ic (prepaid counts roots st) E).
  tauto.
Qed.
Theorem prepayment_preserves_existing_capture_admission : forall word nc ic counts roots st next,
  prepay word nc ic counts roots st = Some next ->
  R.admit_sizes word nc ic (S.roots next) (S.nodes next) (S.edges next) (S.slots next) = true.
Proof.
  intros word nc ic counts roots st next Paid; unfold prepay in Paid.
  destruct (S.extended_valid word nc ic (prepaid counts roots st)) eqn:E; [|discriminate].
  inversion Paid; subst; apply S.extended_admission_implies_original_capture_domain; exact E.
Qed.
Theorem context_events_add_to_not_reset_header_work : forall counts roots st event copied,
  S.work (S.advance (prepaid counts roots st) event copied) =
    S.work st + extra_work counts + S.work_charge event.
Proof. reflexivity. Qed.
Theorem every_literal_comparison_bound_is_prepaid : forall counts,
  total_charge (repeat (cats counts) (literals counts)) = selector_work counts.
Proof.
  intros counts; unfold selector_work.
  induction (literals counts); cbn; [lia|rewrite IHn; lia].
Qed.

(** The combined header name roster is the existing D.capture_roots. The
    adapter pays collection string copies with R.original_string_gate before
    constructing header payloads; they are moved by remapping. *)
Theorem existing_roots_preserve_rule_positions : forall rules header position reference,
  nth_error rules position = Some reference ->
  nth_error (D.capture_roots rules header) position = Some reference.
Proof. apply D.rule_roots_keep_their_original_positions. Qed.
Theorem actual_combined_root_count : forall rules header,
  List.length (D.capture_roots rules header) =
  List.length rules + List.length (D.declaration_names header).
Proof. intros; unfold D.capture_roots; apply app_length. Qed.
Definition publish_if_paid word nc ic counts roots st arena header core pending :=
  match prepay word nc ic counts roots st with
  | None => None | Some _ => B.publish arena header core pending end.
Theorem admission_refusal_publishes_no_header_or_bindings :
  forall word nc ic counts roots st arena header core pending,
  prepay word nc ic counts roots st = None ->
  publish_if_paid word nc ic counts roots st arena header core pending = None.
Proof. intros; unfold publish_if_paid; rewrite H; reflexivity. Qed.
Theorem successful_publication_reuses_complete_checked_binding_boundary :
  forall word nc ic counts roots st arena header core pending published bindings,
  publish_if_paid word nc ic counts roots st arena header core pending = Some (published, bindings) ->
  published = header /\ B.finish header pending = Some bindings /\
  B.validate_bindings arena header core bindings = true.
Proof.
  intros word nc ic counts roots st arena header core pending published bindings Done.
  unfold publish_if_paid in Done; destruct (prepay word nc ic counts roots st); [|discriminate].
  eapply B.successful_publication_is_complete_and_checked; exact Done.
Qed.

Print Assumptions all_accepted_scalar_observations.
Print Assumptions aliases_do_not_change_original_classifier.
Print Assumptions non_alias_uses_original_classifier.
Print Assumptions absent_and_opaque_are_distinct.
Print Assumptions native_projection_does_not_erase_carrier_or_delimiters.
Print Assumptions shared_literal_selector_receives_exact_schema_observations.
Print Assumptions selector_comparison_trace_is_prepaid.
Print Assumptions literal_only_renames_name_not_source_category.
Print Assumptions explicit_flags_and_optional_names_are_not_defaulted.
Print Assumptions explicit_row_keeps_source_slot_but_follows_literals.
Print Assumptions literal_row_follows_source_globals_but_executes_first.
Print Assumptions mode_rows_follow_both_global_blocks.
Print Assumptions receipt_retains_actual_append_id.
Print Assumptions source_position_write_uses_actual_receipt.
Print Assumptions completed_schema_rows_have_no_auxiliary_route.
Print Assumptions exact_allocation_phase_content_sum.
Print Assumptions header_counts_are_actual_vector_contents.
Print Assumptions binding_pending_counts_match_actual_builder.
Print Assumptions header_charge_does_not_fabricate_nodes_edges_or_name_copies.
Print Assumptions successful_prepayment_is_aggregate_checked.
Print Assumptions prepayment_preserves_existing_capture_admission.
Print Assumptions context_events_add_to_not_reset_header_work.
Print Assumptions every_literal_comparison_bound_is_prepaid.
Print Assumptions existing_roots_preserve_rule_positions.
Print Assumptions actual_combined_root_count.
Print Assumptions admission_refusal_publishes_no_header_or_bindings.
Print Assumptions successful_publication_reuses_complete_checked_binding_boundary.
End SchemaDeclarationCaptureProjection.
