(** Exact scheduling/callback relocation of the original discover_members and
    build_prefix_bp_map loops. This is not a second grammar classifier.

    Discovery interface: the original borrowed Rule payload and rule order,
    categories, owner-category index, existing prefix-BP map, plus three lazy
    operations: atomic classification observed as four cases, binder
    classification, and leading authored literal. Atomic observation is a
    MATCH ON THE EXISTING RESULT, not recognition from lowered syntax.
    The original macro classifier is still called, including internal callbacks
    on ignored result kinds. No new Clone/Copy/equality requirement on Rule.

    Discovery source ledger:
    - Cast each rule_i to u16 BEFORE its atomic call. CrossCatPrefixUnary skips;
      NullaryLiteralRun appends its trailing literals immediately (all guards
      None, kind Nullary, total_positions=items.len, body=None, coords=[]);
      CrossCatProjection skips. All other results alone call binder.
    - Binder None skips before reading leading syntax. Binder Some alone reads
      the leading literal; absent/nonliteral/empty syntax yields None. Only this
      binder path tests trigger == "(". Nullary success bypasses that gate.
    - For another literal trigger, run the imported initial-body helper FIRST.
      Only a returned name calls category lookup; missing/unresolved names fall
      back to the supplied owner category. An explicit but undeclared body does
      not restart nested search. Then run the imported binder_items helper.
    - Append its FULL returned item prefix/truncation and the ORIGINAL complete
      positions.len, kind Binder, cast rule index, body Some(index), coords=[].
      A helper fuel stop is explicit and stops the remaining rule suffix; it is
      not converted into a successful empty member or rejected classifier.
    - Member order is successful-rule order, not trigger bucket order. The outer
      partition's bucketing/cast-exclusion remains PrefixFactoringProjection.

    BP scheduling interface: original per-category borrowed rule rows, the
    existing table preparation, unary eligibility, lazy accepted-rule metadata
    (category spelling and explicit prefix BP), and existing compute_prefix_bp.
    The unary helper already lives in mettail_ast::grammar_shapes, and the BP
    computation already lives in prattail::binding_power. Neither is rederived.
    Prepare the table ONCE, even for no categories, before creating/using the
    empty map. Visit categories then rules in authored per_cat order. Test unary
    eligibility before category conversion or prefix_bp observation; compute BP
    before inserting at the cast owner (cat_i,rule_i). A later equal cast key
    overwrites its value; an ineligible later rule does not erase an old value.
    The immutable lookup function below models HashMap contents, not allocation,
    iteration order, or retained shadow entries. No grammar AST is reconstructed.

    The source and shared executions use the SAME callback state transformers.
    This proves concrete scheduling and helper composition, not callback internals
    or their panics. AtomicClassifierProjection's theorem is directly reused
    below after its result observation. BinderRuleProjection supplies the exact
    BinderShape through PrefixMemberDescriptorRelocation; its classifier theorem
    remains that separate boundary, not an assumed Option-callback theorem here.
    Both helper entry correspondence theorems are applied at actual call sites.

    Mathematical rule indices are cast modulo 65536; no bounds admission is
    inserted. Existing descriptor/map fields retain their Rust u16/u8 domains,
    and vectors/indices must fit usize. Fuel only instruments the two existing
    explicit helper loops, whose termination is not re-proved here. Returned
    borrow owners are proof occurrence identities, not new Rust objects. Full
    output/effect prefixes are compared, not allocator, Drop, formatting, borrow
    checking, panic/unwind, Rust extraction, or whole-parser equivalence.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import PrefixMemberDescriptorRelocation AtomicClassifierProjection.
Import ListNotations.
Set Implicit Arguments.

Module PrefixDiscoveryProjection.
Module H := PrefixMemberDescriptorRelocation.PrefixMemberDescriptorRelocation.
Module F := FactoringTreeRelocation.FactoringTreeRelocation.
Module B := BinderRuleProjection.BinderRuleProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.
Module I := InfixClassifierProjection.InfixClassifierProjection.

Definition index_cast index := index mod 65536.
Inductive AtomicObservation :=
| CrossPrefix | NullaryRun (trigger : string) (trailing_literals : list string)
| CrossProjection | OtherAtomic.
Definition observe_atomic {L} (descriptor : @A.Descriptor L) := match descriptor with
| A.CrossCatPrefixUnary _ _ _ => CrossPrefix
| A.NullaryLiteralRun trigger trailing _ => NullaryRun trigger trailing
| A.CrossCatProjection _ _ => CrossProjection
| _ => OtherAtomic end.

(** Existing atomic theorem applies to this exact post-classification view,
    including its internal callback state and trace, without new recognition. *)
Section AtomicReuse.
Context {L S : Type}.
Definition atomic_readback (result : @A.Observation L S) :=
  (observe_atomic (A.descriptor result), A.final_state result, A.callback_trace result).
Theorem imported_atomic_result_observation_preserves_callbacks :
  forall rule items (unary : S -> option A.Unary * S)
    (literal : string -> S -> option L * S) state,
  atomic_readback (A.view_atomic (I.project_rule rule) (List.map A.project_legacy items) unary literal state) =
  atomic_readback (A.source_atomic rule items unary literal state).
Proof. intros; rewrite A.complete_atomic_projection_and_callback_observation; reflexivity. Qed.
End AtomicReuse.

Inductive Mode := Original | Relocated.
Definition initial_body_call mode fuel env owner shape := match mode with
| Original => H.original_initial_body fuel env owner shape
| Relocated => H.relocated_initial_body fuel env owner shape end.
Definition binder_items_call mode fuel env positions := match mode with
| Original => H.original_binder_items fuel env positions
| Relocated => H.relocated_binder_items fuel env positions end.
Theorem imported_initial_body_call_correspondence : forall fuel env owner shape,
  initial_body_call Relocated fuel env owner shape = initial_body_call Original fuel env owner shape.
Proof. intros; apply H.initial_body_entry_relocation. Qed.
Theorem imported_items_call_correspondence : forall fuel env positions,
  binder_items_call Relocated fuel env positions = binder_items_call Original fuel env positions.
Proof. intros; apply H.binder_items_entry_relocation. Qed.

Section Discovery.
Context {Rule State : Type}.
Record DiscoveryCallbacks := {
  atomic : Rule -> State -> AtomicObservation * State;
  binder : Rule -> State -> option B.BinderShape * State;
  leading_literal : Rule -> State -> option string * State
}.
Inductive DiscoveryEvent :=
| AtomicCall (rule_idx : nat) (rule : Rule)
| BinderCall (rule : Rule)
| LeadingLiteralCall (rule : Rule)
| InitialBodyCall (result : H.Outcome)
| BodyCategoryLookup (name : string)
| BinderItemsCall (result : H.Outcome).
Record DiscoveryProgress := {
  members : list (string * F.CandidateMember);
  discovery_state : State; discovery_trace : list DiscoveryEvent
}.
Definition discovery_progress out state trace :=
 {| members := out; discovery_state := state; discovery_trace := trace |}.
Definition after_discovery_callback progress state event :=
  discovery_progress (members progress) state (discovery_trace progress ++ [event])%list.
Definition discovery_event progress event :=
  after_discovery_callback progress (discovery_state progress) event.
Definition append_member progress trigger member :=
  discovery_progress (members progress ++ [(trigger,member)])%list
    (discovery_state progress) (discovery_trace progress).
Inductive DiscoveryStop :=
| InitialBodyDidNotReturn (result : H.Outcome)
| BinderItemsDidNotReturn (result : H.Outcome).
Inductive DiscoveryResult :=
| Discovered (progress : DiscoveryProgress)
| DiscoveryStopped (reason : DiscoveryStop) (progress : DiscoveryProgress).

Definition nullary_member rule_idx trailing :=
  let items := List.map (fun text => F.Literal text None) trailing in
 {| F.candidate_kind := F.Nullary; F.candidate_rule := rule_idx; F.candidate_items := items;
    F.candidate_truncated := false; F.candidate_total_positions := List.length items;
    F.candidate_body_src_idx := None; F.candidate_mixfix_coords := [] |}.
Definition binder_member rule_idx shape items truncated body :=
 {| F.candidate_kind := F.Binder; F.candidate_rule := rule_idx; F.candidate_items := items;
    F.candidate_truncated := truncated; F.candidate_total_positions := List.length (B.positions shape);
    F.candidate_body_src_idx := Some body; F.candidate_mixfix_coords := [] |}.
Definition member_environment names category rule_idx bp :=
 {| H.categories := names; H.owner_category := category; H.owner_rule := rule_idx; H.prefix_bp_map := bp |}.

Definition finish_binder_member mode item_fuel env shape trigger body progress :=
  let result := binder_items_call mode item_fuel env (B.positions shape) in
  let called := discovery_event progress (BinderItemsCall result) in
  match result with
  | H.ItemResult items truncated _ => Discovered (append_member called trigger
      (binder_member (H.owner_rule env) shape items truncated body))
  | other => DiscoveryStopped (BinderItemsDidNotReturn other) called end.
Theorem finish_binder_member_correspondence : forall item_fuel env shape trigger body progress,
  finish_binder_member Relocated item_fuel env shape trigger body progress =
  finish_binder_member Original item_fuel env shape trigger body progress.
Proof. intros; unfold finish_binder_member; rewrite imported_items_call_correspondence; reflexivity. Qed.

Definition derive_binder_member mode body_fuel item_fuel env owner shape trigger progress :=
  let result := initial_body_call mode body_fuel env owner shape in
  let called := discovery_event progress (InitialBodyCall result) in
  match result with
  | H.NameResult name _ _ =>
      let '(body, after_lookup) := match name with
      | None => (H.owner_category env, called)
      | Some name =>
          let looked_up := discovery_event called (BodyCategoryLookup (H.name_text name)) in
          (match H.lookup_src_idx (H.name_text name) (H.categories env) with
           | Some category => category | None => H.owner_category env end, looked_up) end in
      finish_binder_member mode item_fuel env shape trigger body after_lookup
  | other => DiscoveryStopped (InitialBodyDidNotReturn other) called end.
Theorem derive_binder_member_correspondence : forall body_fuel item_fuel env owner shape trigger progress,
  derive_binder_member Relocated body_fuel item_fuel env owner shape trigger progress =
  derive_binder_member Original body_fuel item_fuel env owner shape trigger progress.
Proof.
  intros; unfold derive_binder_member; rewrite imported_initial_body_call_correspondence.
  destruct (initial_body_call Original body_fuel env owner shape) as [configuration|name pending trace|items truncated trace];
    try reflexivity.
  destruct name; apply finish_binder_member_correspondence.
Qed.

Definition discover_rule mode callbacks body_fuel item_fuel names category bp index rule progress :=
  let rule_idx := index_cast index in
  let '(observation, state) := atomic callbacks rule (discovery_state progress) in
  let called := after_discovery_callback progress state (AtomicCall rule_idx rule) in
  match observation with
  | CrossPrefix => Discovered called
  | NullaryRun trigger trailing => Discovered (append_member called trigger (nullary_member rule_idx trailing))
  | CrossProjection => Discovered called
  | OtherAtomic =>
      let '(shape, state) := binder callbacks rule (discovery_state called) in
      let bound := after_discovery_callback called state (BinderCall rule) in
      match shape with
      | None => Discovered bound
      | Some shape =>
          let '(trigger, state) := leading_literal callbacks rule (discovery_state bound) in
          let observed := after_discovery_callback bound state (LeadingLiteralCall rule) in
          match trigger with
          | None => Discovered observed
          | Some trigger => if String.eqb trigger "(" then Discovered observed
            else derive_binder_member mode body_fuel item_fuel
              (member_environment names category rule_idx bp) index shape trigger observed
          end
      end end.
Theorem discover_rule_callback_and_helper_correspondence :
  forall callbacks body_fuel item_fuel names category bp index rule progress,
  discover_rule Relocated callbacks body_fuel item_fuel names category bp index rule progress =
  discover_rule Original callbacks body_fuel item_fuel names category bp index rule progress.
Proof.
  intros; unfold discover_rule.
  destruct (atomic callbacks rule (discovery_state progress)) as [observation state].
  destruct observation; try reflexivity.
  cbn [after_discovery_callback discovery_progress discovery_state].
  destruct (binder callbacks rule state) as [shape state']; destruct shape as [shape|]; try reflexivity.
  cbn [after_discovery_callback discovery_progress discovery_state].
  destruct (leading_literal callbacks rule state') as [trigger state'']; destruct trigger as [trigger|]; try reflexivity.
  destruct (String.eqb trigger "("); [reflexivity|apply derive_binder_member_correspondence].
Qed.
Fixpoint discover_rules mode callbacks body_fuel item_fuel names category bp index rules progress :=
  match rules with
  | [] => Discovered progress
  | rule :: rest => match discover_rule mode callbacks body_fuel item_fuel names category bp index rule progress with
      | Discovered next => discover_rules mode callbacks body_fuel item_fuel names category bp (S index) rest next
      | stopped => stopped end end.
Theorem ordered_discovery_preserves_members_and_effect_prefix :
  forall rules callbacks body_fuel item_fuel names category bp index progress,
  discover_rules Relocated callbacks body_fuel item_fuel names category bp index rules progress =
  discover_rules Original callbacks body_fuel item_fuel names category bp index rules progress.
Proof.
  induction rules as [|rule rest IH]; intros; cbn [discover_rules]; [reflexivity|].
  rewrite discover_rule_callback_and_helper_correspondence.
  destruct (discover_rule Original callbacks body_fuel item_fuel names category bp index rule progress); auto.
Qed.
Definition discover_members mode callbacks body_fuel item_fuel names category bp rules state :=
  discover_rules mode callbacks body_fuel item_fuel names category bp 0 rules
    (discovery_progress [] state []).
Theorem original_discover_members_entry_correspondence :
  forall callbacks body_fuel item_fuel names category bp rules state,
  discover_members Relocated callbacks body_fuel item_fuel names category bp rules state =
  discover_members Original callbacks body_fuel item_fuel names category bp rules state.
Proof. intros; apply ordered_discovery_preserves_members_and_effect_prefix. Qed.

Theorem nullary_success_bypasses_binder_leading_and_parenthesis_gate :
  forall mode callbacks body_fuel item_fuel names category bp index rule progress trigger trailing state,
  atomic callbacks rule (discovery_state progress) = (NullaryRun trigger trailing,state) ->
  discover_rule mode callbacks body_fuel item_fuel names category bp index rule progress =
  Discovered (append_member
    (after_discovery_callback progress state (AtomicCall (index_cast index) rule)) trigger
    (nullary_member (index_cast index) trailing)).
Proof. intros; unfold discover_rule; now rewrite H. Qed.
Theorem nullary_and_binder_total_positions_use_original_distinct_sources :
  forall rule_idx trailing shape items truncated body,
  F.candidate_total_positions (nullary_member rule_idx trailing) = List.length trailing /\
  F.candidate_total_positions (binder_member rule_idx shape items truncated body) = List.length (B.positions shape).
Proof. intros; split; [apply length_map|reflexivity]. Qed.
Theorem helper_stop_preserves_member_prefix : forall mode item_fuel env shape trigger body progress result,
  binder_items_call mode item_fuel env (B.positions shape) = H.Continue result ->
  finish_binder_member mode item_fuel env shape trigger body progress =
  DiscoveryStopped (BinderItemsDidNotReturn (H.Continue result))
    (discovery_event progress (BinderItemsCall (H.Continue result))).
Proof. intros; unfold finish_binder_member; now rewrite H. Qed.
End Discovery.

(** HashMap lookup semantics only; original insert overwrites the old value.
    The loop never iterates the resulting map. *)
Definition bp_key_eqb (left right : nat * nat) :=
  Nat.eqb (fst left) (fst right) && Nat.eqb (snd left) (snd right).
Definition bp_insert key value (map : H.PrefixBpMap) : H.PrefixBpMap :=
  fun query => if bp_key_eqb key query then Some value else map query.
Definition empty_bp_map : H.PrefixBpMap := fun _ => None.
Theorem bp_insert_overwrites_same_key : forall map key first last,
  bp_insert key last (bp_insert key first map) key = Some last.
Proof. intros map [cat rule] first last; unfold bp_insert, bp_key_eqb; cbn [fst snd]; rewrite !Nat.eqb_refl; reflexivity. Qed.

Section PrefixBpScheduling.
Context {Rule Table State : Type}.
Record BpCallbacks := {
  prepare_table : State -> Table * State;
  unary_eligible : Rule -> State -> bool * State;
  prefix_metadata : Rule -> State -> (string * option nat) * State;
  compute_prefix_bp : string -> option nat -> Table -> State -> nat * State
}.
Inductive BpEvent :=
| PrepareTable
| UnaryEligibility (category_ordinal rule_ordinal : nat) (rule : Rule)
| ReadPrefixMetadata (rule : Rule)
| ComputePrefixBp (category : string) (explicit : option nat)
| InsertPrefixBp (category_idx rule_idx value : nat).
Record BpProgress := {
  bp_map : H.PrefixBpMap; bp_state : State; bp_trace : list BpEvent
}.
Definition bp_progress map state trace := {| bp_map := map; bp_state := state; bp_trace := trace |}.
Definition bp_callback progress state event :=
  bp_progress (bp_map progress) state (bp_trace progress ++ [event])%list.
Definition bp_rule_core callbacks table category_ordinal rule_ordinal rule progress :=
  let '(eligible, state) := unary_eligible callbacks rule (bp_state progress) in
  let tested := bp_callback progress state (UnaryEligibility category_ordinal rule_ordinal rule) in
  if eligible then
    let '((category, explicit), state) := prefix_metadata callbacks rule (bp_state tested) in
    let observed := bp_callback tested state (ReadPrefixMetadata rule) in
    let '(value, state) := compute_prefix_bp callbacks category explicit table (bp_state observed) in
    let computed := bp_callback observed state (ComputePrefixBp category explicit) in
    let key := (index_cast category_ordinal,index_cast rule_ordinal) in
    bp_progress (bp_insert key value (bp_map computed)) (bp_state computed)
      (bp_trace computed ++ [InsertPrefixBp (fst key) (snd key) value])%list
  else tested.
Definition bp_rule mode callbacks table category_ordinal rule_ordinal rule progress := match mode with
| Original => bp_rule_core callbacks table category_ordinal rule_ordinal rule progress
| Relocated => bp_rule_core callbacks table category_ordinal rule_ordinal rule progress end.
Fixpoint bp_rules mode callbacks table category_ordinal rule_ordinal rules progress := match rules with
| [] => progress
| rule :: rest => bp_rules mode callbacks table category_ordinal (S rule_ordinal) rest
    (bp_rule mode callbacks table category_ordinal rule_ordinal rule progress) end.
Theorem bp_rule_list_preserves_lazy_schedule : forall rules callbacks table category_ordinal rule_ordinal progress,
  bp_rules Relocated callbacks table category_ordinal rule_ordinal rules progress =
  bp_rules Original callbacks table category_ordinal rule_ordinal rules progress.
Proof.
  induction rules as [|rule rest IH]; intros; cbn [bp_rules]; [reflexivity|].
  apply IH.
Qed.
Fixpoint bp_categories mode callbacks table category_ordinal rows progress := match rows with
| [] => progress
| rules :: rest => bp_categories mode callbacks table (S category_ordinal) rest
    (bp_rules mode callbacks table category_ordinal 0 rules progress) end.
Theorem bp_categories_preserve_authored_order_and_overwrites : forall rows callbacks table category_ordinal progress,
  bp_categories Relocated callbacks table category_ordinal rows progress =
  bp_categories Original callbacks table category_ordinal rows progress.
Proof.
  induction rows as [|rules rest IH]; intros; cbn [bp_categories]; [reflexivity|].
  rewrite bp_rule_list_preserves_lazy_schedule; apply IH.
Qed.
Definition build_prefix_bp_map mode callbacks rows state :=
  let '(table, state) := prepare_table callbacks state in
  bp_categories mode callbacks table 0 rows (bp_progress empty_bp_map state [PrepareTable]).
Theorem original_bp_map_entry_correspondence : forall callbacks rows state,
  build_prefix_bp_map Relocated callbacks rows state = build_prefix_bp_map Original callbacks rows state.
Proof.
  intros; unfold build_prefix_bp_map; destruct (prepare_table callbacks state).
  apply bp_categories_preserve_authored_order_and_overwrites.
Qed.
Theorem table_is_prepared_even_for_no_categories : forall mode callbacks state table prepared,
  prepare_table callbacks state = (table,prepared) ->
  build_prefix_bp_map mode callbacks [] state = bp_progress empty_bp_map prepared [PrepareTable].
Proof. intros; unfold build_prefix_bp_map; now rewrite H. Qed.
Theorem ineligible_rule_reads_neither_metadata_nor_bp :
  forall mode callbacks table cat index rule progress state,
  unary_eligible callbacks rule (bp_state progress) = (false,state) ->
  bp_rule mode callbacks table cat index rule progress =
  bp_callback progress state (UnaryEligibility cat index rule).
Proof. intros; destruct mode; unfold bp_rule, bp_rule_core; now rewrite H. Qed.
Theorem ineligible_rule_cannot_erase_a_previous_value :
  forall mode callbacks table cat index rule progress state key,
  unary_eligible callbacks rule (bp_state progress) = (false,state) ->
  bp_map (bp_rule mode callbacks table cat index rule progress) key = bp_map progress key.
Proof.
  intros.
  (* The returned callback state is absent from the rewritten left-hand side;
     supply it explicitly rather than asking rewrite to infer that witness. *)
  rewrite ineligible_rule_reads_neither_metadata_nor_bp with (state := state) by exact H.
  reflexivity.
Qed.
End PrefixBpScheduling.

Print Assumptions imported_atomic_result_observation_preserves_callbacks.
Print Assumptions imported_initial_body_call_correspondence.
Print Assumptions imported_items_call_correspondence.
Print Assumptions discover_rule_callback_and_helper_correspondence.
Print Assumptions ordered_discovery_preserves_members_and_effect_prefix.
Print Assumptions original_discover_members_entry_correspondence.
Print Assumptions nullary_success_bypasses_binder_leading_and_parenthesis_gate.
Print Assumptions nullary_and_binder_total_positions_use_original_distinct_sources.
Print Assumptions helper_stop_preserves_member_prefix.
Print Assumptions bp_insert_overwrites_same_key.
Print Assumptions bp_rule_list_preserves_lazy_schedule.
Print Assumptions bp_categories_preserve_authored_order_and_overwrites.
Print Assumptions original_bp_map_entry_correspondence.
Print Assumptions table_is_prepared_even_for_no_categories.
Print Assumptions ineligible_rule_reads_neither_metadata_nor_bp.
Print Assumptions ineligible_rule_cannot_erase_a_previous_value.

End PrefixDiscoveryProjection.
