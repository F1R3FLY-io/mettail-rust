(** Exact relocation boundary for the ORIGINAL prefix.rs helpers
    insert_unified_descriptor and record_initiating_rule_rows.

    Source: 3ed600ed, macros/src/gen/runtime/wpda_codegen/prefix.rs.
    Frozen direct-call Rust baselines: unified_prefix_descriptor_baselines.rs.

    BUCKET SOURCE LEDGER
      1. Format pattern; then format an existing guard, or use the empty string.
      2. Query the ordered map by this PAIR of strings. Only an absent map key
         appends a cloned key to the separate first-insertion-order vector.
      3. Entry lookup retains ALL first pattern/guard payload fields, creating
         an empty bucket only if absent. Append the descriptor without dedup.
    Payload and Descriptor below are arbitrary types. Their full values move
    unchanged; no grammar syntax, token normalization or descriptor classifier
    is modeled or introduced. The same formatter is supplied on both sides;
    concrete TokenStream::to_string implementation is not proved here. Thus
    None and Some(empty tokens) collide exactly when their rendered keys do,
    while the first Option payload remains distinguishable. Parentheses and
    other delimiters remain part of the original formatter's key string.

    INITIATING-ROW SOURCE LEDGER
      1. Lookup disposition by rule index.
      2. GroupFirst alone looks up members. Missing members returns ONE error
         carrying category/rule, before any member is recorded. Existing rows
         from earlier calls remain unchanged. Some [] succeeds with no rows.
      3. Existing members are visited in source order, including duplicates;
         EACH calls the existing ForkEmissionAccumulatorProjection transition
         with the SAME supplied category, static position and bucket tag.
      4. GroupRest does no member lookup and records nothing. No disposition
         records exactly the rule itself, ignoring any stray members entry.
    The original three GroupFirst payload indices are not read by this helper.
    SourceView is a shallow two-tag observation, not another factoring model.
    The error is a data observation; the macro's unchanged diagnostic formatter
    and compile_error quotation render it. Sequence composition below continues
    after each call, retaining errors in call order: it does NOT invent a global
    abort/rollback, and proves preservation of already-accumulated prefix rows.

    Scope: source/accessor correspondence for these two helpers and their finite
    call sequences, map contents/order, callback observation order, all existing
    accumulator collision semantics, and typed-refusal routing. Naturals stand
    for already-supplied u16 indices/positions; neither helper does arithmetic
    or narrows integers. Bucket list lengths use mathematical naturals; Rust's
    original allocation/capacity preconditions remain external. No theorem here
    proves allocation, Clone/Drop timing, arbitrary effectful formatter/reader
    lawfulness, Rust extraction, prefix discovery or static-ordinal selection.
    The branch caller still determines the static position. Election remains
    inert by reuse of the existing accumulator's emitted_value theorem.
*)
From Stdlib Require Import List String Bool Arith.
From Stdlib Require Import FSets.FMapAVL FSets.FMapFacts Structures.OrderedTypeEx.
From PrattailWpdaRuntime Require Import ForkEmissionAccumulatorProjection.
Import ListNotations.
Set Implicit Arguments.

Module UnifiedPrefixDescriptorProjection.
Module FE := ForkEmissionAccumulatorProjection.ForkEmissionAccumulatorProjection.
Module BucketKey := PairOrderedType String_as_OT String_as_OT.
Module BucketMaps := FMapAVL.Make BucketKey.
Module BucketFacts := WFacts_fun BucketKey BucketMaps.

Section Buckets.
Context {Payload Descriptor : Type}.

Record Bucket := {
  pattern_payload : Payload;
  guard_payload : option Payload;
  descriptors : list Descriptor
}.
Record BucketState := {
  buckets : BucketMaps.t Bucket;
  first_key_order : list BucketKey.t
}.
Definition bucket_state entries order :=
  {| buckets := entries; first_key_order := order |}.
Record Insertion := {
  incoming_pattern : Payload;
  incoming_guard : option Payload;
  incoming_descriptor : Descriptor
}.
Inductive BucketEvent :=
| FormatPattern | FormatGuard
| ContainsBucket (key : BucketKey.t)
| EntryBucket (key : BucketKey.t)
| CreateBucket | AppendDescriptor.

Definition original_key (format : Payload -> string) pattern guard :=
  (format pattern, match guard with Some value => format value | None => EmptyString end).
Record Formatter := { format_payload : Payload -> string }.
Definition source_formatter format := {| format_payload := format |}.
Definition accessor_key reader pattern guard :=
  (format_payload reader pattern,
   match guard with Some value => format_payload reader value | None => EmptyString end).
Definition format_trace (guard : option Payload) :=
  FormatPattern :: match guard with Some _ => [FormatGuard] | None => [] end.

(** This is the concrete original contains/entry/push body, NOT an assumed
    equivalence between arbitrary bucket algorithms. Stdlib ordered-map
    operations observe BTreeMap without claiming its internal tree shape. *)
Definition insert_at_key key insertion state :=
  let order := if BucketMaps.mem key (buckets state)
    then first_key_order state else (first_key_order state ++ [key])%list in
  let previous := BucketMaps.find key (buckets state) in
  let entry := match previous with
    | Some old => old
    | None => {| pattern_payload := incoming_pattern insertion;
                 guard_payload := incoming_guard insertion; descriptors := [] |}
    end in
  let extended := {| pattern_payload := pattern_payload entry;
    guard_payload := guard_payload entry;
    descriptors := (descriptors entry ++ [incoming_descriptor insertion])%list |} in
  (bucket_state (BucketMaps.add key extended (buckets state)) order,
   [ContainsBucket key; EntryBucket key] ++
   match previous with Some _ => [AppendDescriptor] | None => [CreateBucket; AppendDescriptor] end)%list.

Definition original_insert format insertion state :=
  let key := original_key format (incoming_pattern insertion) (incoming_guard insertion) in
  let '(after, events) := insert_at_key key insertion state in
  (after, (format_trace (incoming_guard insertion) ++ events)%list).
Definition shared_insert reader insertion state :=
  let key := accessor_key reader (incoming_pattern insertion) (incoming_guard insertion) in
  let '(after, events) := insert_at_key key insertion state in
  (after, (format_trace (incoming_guard insertion) ++ events)%list).

Theorem exact_bucket_source_accessor_step : forall format insertion state,
  shared_insert (source_formatter format) insertion state = original_insert format insertion state.
Proof. reflexivity. Qed.

Fixpoint insert_sequence insertions state
  (step : Insertion -> BucketState -> BucketState * list BucketEvent) :=
  match insertions with
  | [] => (state, [])
  | insertion :: rest =>
      let '(next, events) := step insertion state in
      let '(after, later) := insert_sequence rest next step in
      (after, (events ++ later)%list)
  end.
Theorem finite_bucket_sequence_preserves_maps_order_and_events : forall format insertions state,
  insert_sequence insertions state (shared_insert (source_formatter format)) =
  insert_sequence insertions state (original_insert format).
Proof. reflexivity. Qed.

Theorem existing_key_does_not_append_order : forall key insertion state,
  BucketMaps.mem key (buckets state) = true ->
  first_key_order (fst (insert_at_key key insertion state)) = first_key_order state.
Proof. intros; unfold insert_at_key; rewrite H; destruct (BucketMaps.find key (buckets state)); reflexivity. Qed.
Theorem absent_key_appends_exactly_once : forall key insertion state,
  BucketMaps.mem key (buckets state) = false ->
  first_key_order (fst (insert_at_key key insertion state)) = (first_key_order state ++ [key])%list.
Proof. intros; unfold insert_at_key; rewrite H; destruct (BucketMaps.find key (buckets state)); reflexivity. Qed.
Theorem existing_bucket_preserves_first_payload_and_appends : forall key insertion state old,
  BucketMaps.find key (buckets state) = Some old ->
  BucketMaps.find key (buckets (fst (insert_at_key key insertion state))) =
    Some {| pattern_payload := pattern_payload old; guard_payload := guard_payload old;
      descriptors := (descriptors old ++ [incoming_descriptor insertion])%list |}.
Proof.
  intros; unfold insert_at_key; rewrite H; cbn.
  apply BucketFacts.add_eq_o; split; reflexivity.
Qed.
Theorem absent_entry_constructs_original_payload : forall key insertion state,
  BucketMaps.find key (buckets state) = None ->
  BucketMaps.find key (buckets (fst (insert_at_key key insertion state))) =
    Some {| pattern_payload := incoming_pattern insertion; guard_payload := incoming_guard insertion;
      descriptors := [incoming_descriptor insertion] |}.
Proof.
  intros; unfold insert_at_key; rewrite H; cbn.
  apply BucketFacts.add_eq_o; split; reflexivity.
Qed.
Theorem other_bucket_entries_are_unchanged : forall key query insertion state,
  ~ BucketKey.eq key query ->
  BucketMaps.find query (buckets (fst (insert_at_key key insertion state))) =
  BucketMaps.find query (buckets state).
Proof.
  intros; unfold insert_at_key; destruct (BucketMaps.find key (buckets state)); cbn;
  apply BucketFacts.add_neq_o; assumption.
Qed.
Theorem absent_guard_does_not_invoke_guard_formatter :
  format_trace None = [FormatPattern].
Proof. reflexivity. Qed.
Theorem empty_guard_collision_keeps_distinct_input_payloads : forall format pattern empty,
  format empty = EmptyString ->
  original_key format pattern None = original_key format pattern (Some empty).
Proof. intros; unfold original_key; now rewrite H. Qed.
End Buckets.

Inductive SourceDisposition :=
| SourceGroupFirst (spine_id body_src_idx weight_rule_idx : nat)
| SourceGroupRest.
Inductive DispositionView := ViewGroupFirst | ViewGroupRest.
Definition observe_disposition disposition := match disposition with
| SourceGroupFirst _ _ _ => ViewGroupFirst | SourceGroupRest => ViewGroupRest end.
Record Source := {
  source_disposition : nat -> option SourceDisposition;
  source_members : nat -> option (list nat)
}.
Record Reader := {
  read_disposition : nat -> option DispositionView;
  read_members : nat -> option (list nat)
}.
Definition source_reader source :=
  {| read_disposition := fun rule => option_map observe_disposition (source_disposition source rule);
     read_members := source_members source |}.
Record Invocation := {
  category_index : nat;
  rule_index : nat;
  static_position : nat;
  diagnostic_bucket : string
}.
Record MissingMembers := { missing_category : nat; missing_rule : nat }.
Definition missing_members invocation :=
  {| missing_category := category_index invocation; missing_rule := rule_index invocation |}.
Inductive RowEvent :=
| ReadDisposition (rule : nat)
| ReadMembers (rule : nat)
| RecordMember (member : nat)
| RefuseMissingMembers.
Record RowResult := {
  after_rows : FE.Accumulator;
  refusal : option MissingMembers;
  row_events : list RowEvent
}.
Definition result state error events :=
  {| after_rows := state; refusal := error; row_events := events |}.
Definition member_observation invocation member :=
  {| FE.observed_key := (category_index invocation, member);
     FE.incoming_ordinal := static_position invocation;
     FE.incoming_tag := diagnostic_bucket invocation |}.
Fixpoint record_members invocation members state := match members with
| [] => state
| member :: rest => record_members invocation rest
    (FE.record_site2_row (member_observation invocation member) state)
end.
Definition group_first_result invocation members state := match members with
| None => result state (Some (missing_members invocation))
    [ReadMembers (rule_index invocation); RefuseMissingMembers]
| Some values => result (record_members invocation values state) None
    (ReadMembers (rule_index invocation) :: List.map RecordMember values)
end.
Definition prepend_disposition_event invocation outcome :=
  result (after_rows outcome) (refusal outcome)
    (ReadDisposition (rule_index invocation) :: row_events outcome).
Definition ordinary_result invocation state :=
  result (FE.record_site2_row (member_observation invocation (rule_index invocation)) state)
    None [RecordMember (rule_index invocation)].

Definition original_initiating source invocation state :=
  prepend_disposition_event invocation
    (match source_disposition source (rule_index invocation) with
     | Some (SourceGroupFirst _ _ _) =>
         group_first_result invocation (source_members source (rule_index invocation)) state
     | Some SourceGroupRest => result state None []
     | None => ordinary_result invocation state
     end).
Definition shared_initiating reader invocation state :=
  prepend_disposition_event invocation
    (match read_disposition reader (rule_index invocation) with
     | Some ViewGroupFirst =>
         group_first_result invocation (read_members reader (rule_index invocation)) state
     | Some ViewGroupRest => result state None []
     | None => ordinary_result invocation state
     end).
Theorem exact_initiating_source_accessor_step : forall source invocation state,
  shared_initiating (source_reader source) invocation state = original_initiating source invocation state.
Proof.
  intros; unfold shared_initiating, source_reader; cbn.
  unfold original_initiating.
  destruct (source_disposition source (rule_index invocation)) as [[a b c|]|]; reflexivity.
Qed.

(** The caller renders one error only for Some; opaque rendering is shared,
    preserving the original message's category/rule arguments and quote site. *)
Definition quote_refusal {Token : Type} (compile_error : MissingMembers -> Token) outcome :=
  match refusal outcome with Some error => [compile_error error] | None => [] end.
Theorem missing_members_preserves_entire_accumulated_prefix : forall invocation state,
  after_rows (group_first_result invocation None state) = state.
Proof. reflexivity. Qed.
Theorem missing_members_quotes_one_error_at_this_call : forall Token
  (compile_error : MissingMembers -> Token) invocation state,
  quote_refusal compile_error (group_first_result invocation None state) =
    [compile_error (missing_members invocation)].
Proof. reflexivity. Qed.
Theorem empty_group_is_success_without_leader_row : forall invocation state,
  group_first_result invocation (Some []) state =
  result state None [ReadMembers (rule_index invocation)].
Proof. reflexivity. Qed.
Theorem group_rest_does_not_read_members : forall source invocation state,
  source_disposition source (rule_index invocation) = Some SourceGroupRest ->
  original_initiating source invocation state =
    result state None [ReadDisposition (rule_index invocation)].
Proof. intros; unfold original_initiating; rewrite H; reflexivity. Qed.
Theorem undispositioned_rule_records_only_itself : forall source invocation state,
  source_disposition source (rule_index invocation) = None ->
  original_initiating source invocation state =
    result (FE.record_site2_row (member_observation invocation (rule_index invocation)) state)
      None [ReadDisposition (rule_index invocation); RecordMember (rule_index invocation)].
Proof. intros; unfold original_initiating; rewrite H; reflexivity. Qed.
Theorem member_order_and_duplicates_are_not_normalized : forall invocation members state,
  row_events (group_first_result invocation (Some members) state) =
    ReadMembers (rule_index invocation) :: List.map RecordMember members.
Proof. reflexivity. Qed.
Theorem member_observation_preserves_static_position_and_tag : forall invocation member,
  FE.incoming_ordinal (member_observation invocation member) = static_position invocation /\
  FE.incoming_tag (member_observation invocation member) = diagnostic_bucket invocation /\
  FE.observed_key (member_observation invocation member) = (category_index invocation, member).
Proof. intros; repeat split; reflexivity. Qed.
Theorem record_members_reuses_existing_accumulator : forall invocation members state,
  record_members invocation members state = FE.original_accumulator
    (FE.original_record_sequence (List.map (member_observation invocation) members)
      {| FE.original_accumulator := state |}).
Proof.
  intros invocation members; induction members as [|member rest IH]; intros state;
  cbn [record_members List.map FE.original_record_sequence FE.original_record];
  [reflexivity | apply IH].
Qed.

Fixpoint initiating_sequence invocations state
  (step : Invocation -> FE.Accumulator -> RowResult) := match invocations with
| [] => (state, [], [])
| invocation :: rest =>
    let outcome := step invocation state in
    let '(after, errors, events) := initiating_sequence rest (after_rows outcome) step in
    (after, (refusal outcome :: errors), (row_events outcome ++ events)%list)
end.
Theorem finite_calls_preserve_prefix_rows_refusals_and_read_order : forall source invocations state,
  initiating_sequence invocations state (shared_initiating (source_reader source)) =
  initiating_sequence invocations state (original_initiating source).
Proof.
  intros source invocations; induction invocations as [|invocation rest IH]; intros state;
  [reflexivity|].
  cbn [initiating_sequence]. rewrite exact_initiating_source_accessor_step.
  rewrite IH. reflexivity.
Qed.
Theorem source_accessor_preserves_single_compile_error_routing : forall Token
  (compile_error : MissingMembers -> Token) source invocation state,
  quote_refusal compile_error (shared_initiating (source_reader source) invocation state) =
  quote_refusal compile_error (original_initiating source invocation state).
Proof. intros; rewrite exact_initiating_source_accessor_step; reflexivity. Qed.
Theorem derived_rows_do_not_activate_election : forall invocation members state site key,
  FE.emitted_value (record_members invocation members state) site key =
  FE.emitted_value state site key.
Proof. reflexivity. Qed.

Print Assumptions exact_bucket_source_accessor_step.
Print Assumptions finite_bucket_sequence_preserves_maps_order_and_events.
Print Assumptions existing_key_does_not_append_order.
Print Assumptions absent_key_appends_exactly_once.
Print Assumptions existing_bucket_preserves_first_payload_and_appends.
Print Assumptions absent_entry_constructs_original_payload.
Print Assumptions other_bucket_entries_are_unchanged.
Print Assumptions absent_guard_does_not_invoke_guard_formatter.
Print Assumptions empty_guard_collision_keeps_distinct_input_payloads.
Print Assumptions exact_initiating_source_accessor_step.
Print Assumptions missing_members_preserves_entire_accumulated_prefix.
Print Assumptions missing_members_quotes_one_error_at_this_call.
Print Assumptions empty_group_is_success_without_leader_row.
Print Assumptions group_rest_does_not_read_members.
Print Assumptions undispositioned_rule_records_only_itself.
Print Assumptions member_order_and_duplicates_are_not_normalized.
Print Assumptions member_observation_preserves_static_position_and_tag.
Print Assumptions record_members_reuses_existing_accumulator.
Print Assumptions finite_calls_preserve_prefix_rows_refusals_and_read_order.
Print Assumptions source_accessor_preserves_single_compile_error_routing.
Print Assumptions derived_rows_do_not_activate_election.
End UnifiedPrefixDescriptorProjection.
