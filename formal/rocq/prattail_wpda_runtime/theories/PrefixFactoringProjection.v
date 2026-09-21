(** Exact source/callback boundary for the prefix factoring partition.

    Source: macros/src/gen/runtime/wpda_codegen/factoring.rs,
    build_prefix_factoring_with and emission_partition's disabled branch.
    The Rust transfer replaces ONLY discover_members and
    cast_machinery_participates call sites with closure calls. Rule payloads
    remain the original borrowed per-category rows; discovered descriptors and
    every result below are owned. No AST reconstruction or alternative grouping
    algorithm is involved. Paired bucket lists below model the original parallel
    order/member vectors; they preserve first occurrence, not sorted order.

    Ledger:
    - The macro wrapper constructs prefix_bp_map once, even for no categories.
      The enabled emission branch delegates before this construction, so it
      does not build the map twice. The prepared metadata is captured by the
      discovery closure. Discovery occurs once for EACH category, including an
      empty row, before any bucket of that category is examined.
    - cat_i is cast modulo 65536 before discovery. Discovery's owned result is
      bucketed by leading literal, keeping first-seen bucket/member order.
    - Enabled exclusions visit BUCKET order, then member order. The original
      rules[member.rule_idx as usize] lookup happens BEFORE the cast helper;
      that helper happens BEFORE the empty-items test. Do not precompute cast
      answers in rule order. A failed index prevents that callback and suffix.
    - Root partition uses full SpineItem equality. A lone root part becomes a
      singleton before metadata collection or tree construction. Other parts
      record member indices in order and deduplicate body_src_idx in encounter
      order: the Rust BTreeSet supplies membership, NOT sorted output.
    - The SAME original tree builder runs before either group refusal gate.
      Its diagnostics survive an InteriorAccept or NonUniformBodySrc result;
      InteriorAccept wins when both conditions hold. Leaf-count diagnostics do
      not prevent group insertion. An all-nullary group uses the owning category.
    - IDs count eligible groups only, over bucket/group discovery order. The
      original u16 base+ordinal occurs before group push; ordinal += 1 follows.
      The recovery and u16 ceiling diagnostics occur AFTER all category buckets,
      in that order. Category push drains the refusal sink with mem::take.
    - Disabled execution discovers/buckets the same members, assigns
      FactoringDisabled to EVERY member, and performs no cast lookup/callback,
      tree construction, or ceiling checks. Empty categories remain present.

    Scope: this is a concrete transcription and closure/module substitution
    proof. Callback implementations are the SAME state transformers in both
    executions, not certified functions. Callback events carry original rule
    payloads; no equality/Clone/Copy assumption on Rule is needed. Preparing
    metadata is modeled explicitly, but its internal helper behavior is outside
    scope. Index faults are explicit. Existing tree fuel exhaustion is explicit,
    not a fabricated category result. Naturals represent original machine
    integers; arithmetic_ok records the executed u16 additions and the usize
    leaf-count sum. Its summands are nonnegative, so bounding the final count
    also bounds every intermediate count. Inherited tree arithmetic/debug
    domains are retained. Returning Rust correspondence
    is restricted to that domain; no panic/release-wrap equivalence or runtime
    pre-admission theorem is claimed. Callback panics/unwinding, allocation,
    lifecycle, formatting internals and termination are outside scope.

    Refusal constructors retain all variable format arguments. The Rust source
    transfer must retain the original text and formatter. The theorem preserves
    complete modeled progress/effect prefixes, including diagnostic local state;
    it does not assert that Rust returns those locals after a failure.

    Direct reuse: FactoringTreeRelocation's concrete finite executor and its
    relocation theorem are imported at the tree call. The older synthetic
    ordered-callback proof supplies a composition pattern only: its recipe-
    materializer lemmas are NOT applied to these different callback types.
    No outer grammar eligibility/accounting theorem is claimed here.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import FactoringTreeRelocation.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module PrefixFactoringProjection.
Module F := FactoringTreeRelocation.FactoringTreeRelocation.

Definition SPINE_RULE_BASE := 63488. (* 0xF800, original constant *)
Definition u16_max := 65535.
Definition category_cast index := index mod 65536.

Inductive SingletonReason :=
| LoneRootChild | CastMachinery | EmptySequence | FactoringDisabled
| PartialSliceCohort.
Record SingletonMember := { singleton_rule : nat; singleton_reason : SingletonReason }.
Inductive IneligibleReason :=
| InteriorAccept (accepting_rule_idxs : list nat)
| NonUniformBodySrc (body_src_idxs : list nat)
| NonUniformResultSrc (result_src_idxs : list nat)
| OperandAbsorbableDivergence (texts : list string)
| MultiOperandSharedSpine.
Record IneligibleGroup := { ineligible_reason : IneligibleReason; member_rule_idxs : list nat }.
Record SpineGroup := {
  spine_id : nat; body_src_idx : nat; roots : list F.SpineTree
}.
Inductive Refusal :=
| TreeRefusal (event : F.Refusal)
| LeafCountMismatch (category : nat) (trigger : string) (leaf_count member_count : nat)
| RecoveryCollision (category ordinal ending recovery_base : nat)
| RuleIndexCeiling (category ending : nat).
Record FactoringBucket := {
  leading_literal : string; cohort_size : nat; groups : list SpineGroup;
  ineligible : list IneligibleGroup; singletons : list SingletonMember
}.
Record CategoryFactoring := {
  category_src_idx : nat; buckets : list FactoringBucket; category_refusals : list Refusal
}.

(** The two original first-position searches and indexed vector updates,
    represented as ordered pairs to retain their parallel-vector invariant. *)
Definition TriggerBuckets := list (string * list F.CandidateMember).
Fixpoint insert_trigger trigger member (entries : TriggerBuckets) : TriggerBuckets :=
  match entries with
  | [] => [(trigger, [member])]
  | (key, members) :: rest =>
      if String.eqb key trigger then (key, (members ++ [member])%list) :: rest
      else (key, members) :: insert_trigger trigger member rest
  end.
Definition bucket_members members :=
  fold_left (fun entries entry => insert_trigger (fst entry) (snd entry) entries) members [].
Definition root_parts members :=
  fold_left (fun parts member =>
    match F.candidate_items member with
    | item :: _ => F.add_to_parts item member parts
    | [] => parts (* unreachable after the original empty-sequence exclusion *)
    end) members [].
Fixpoint unique_body_sources members seen := match members with
| [] => []
| member :: rest => match F.candidate_body_src_idx member with
    | None => unique_body_sources rest seen
    | Some body => if existsb (Nat.eqb body) seen then unique_body_sources rest seen
      else body :: unique_body_sources rest (body :: seen)
    end end.
Fixpoint tree_leaf_count tree := match tree with
| F.Leaf _ _ => 1
| F.Interior _ children =>
    (fix count nodes := match nodes with
     | [] => 0 | child :: rest => tree_leaf_count child + count rest end) children
end.
Definition forest_leaf_count forest := fold_left (fun count tree => count + tree_leaf_count tree) forest 0.

Theorem same_trigger_keeps_bucket_position : forall trigger member members rest,
  insert_trigger trigger member ((trigger, members) :: rest) =
  (trigger, (members ++ [member])%list) :: rest.
Proof. intros; cbn [insert_trigger]; rewrite String.eqb_refl; reflexivity. Qed.
Theorem new_trigger_appends : forall entries trigger member,
  Forall (fun entry => String.eqb (fst entry) trigger = false) entries ->
  insert_trigger trigger member entries = (entries ++ [(trigger, [member])])%list.
Proof.
  induction entries as [|[key members] rest IH]; intros trigger member H; [reflexivity|].
  inversion H as [|entry tail Hkey Hrest]; subst.
  cbn [insert_trigger fst] in *. rewrite Hkey, IH; auto.
Qed.
Theorem body_sources_keep_first_occurrence : forall member rest body seen,
  F.candidate_body_src_idx member = Some body -> existsb (Nat.eqb body) seen = false ->
  unique_body_sources (member :: rest) seen = body :: unique_body_sources rest (body :: seen).
Proof. intros; cbn [unique_body_sources]; now rewrite H, H0. Qed.

Inductive Mode := Original | Relocated.
Definition restore_tree_outcome outcome := match outcome with
| F.RelocatedContinue state => F.OriginalContinue
    {| F.original_configuration := F.relocated_configuration state |}
| F.RelocatedFinished forest after => F.OriginalFinished forest after
| F.RelocatedFailed reason state => F.OriginalFailed reason
    {| F.original_configuration := F.relocated_configuration state |}
end.
Lemma restore_tree_relocation : forall result,
  restore_tree_outcome (F.relocate_outcome result) = result.
Proof. intros [[configuration]|forest after|reason [configuration]]; reflexivity. Qed.
Definition tree_call mode fuel usize_max stance item members :=
  let initial := F.initial 1 item members [] [] in
  match mode with
  | Original => F.original_execute fuel usize_max stance initial
  | Relocated => restore_tree_outcome
      (F.relocated_execute fuel usize_max stance (F.relocate initial)) end.
Theorem imported_tree_call_correspondence : forall fuel usize_max stance item members,
  tree_call Relocated fuel usize_max stance item members =
  tree_call Original fuel usize_max stance item members.
Proof.
  intros; unfold tree_call. rewrite F.finite_execution_preserves_full_forest_and_effect_prefix.
  apply restore_tree_relocation.
Qed.

Section OriginalCallbacks.
Context {Rule Metadata State : Type}.
Record Adapter := {
  prepare_prefix_map : State -> Metadata * State;
  discover : Metadata -> nat -> list Rule -> State -> list (string * F.CandidateMember) * State;
  cast_participates : Rule -> State -> bool * State
}.
Inductive CallbackEvent :=
| PreparePrefixMap
| DiscoverCategory (category : nat) (original_rules : list Rule)
| CastMember (category index : nat) (original_rule : Rule).
Record Effects := {
  callback_state : State; callback_trace : list CallbackEvent;
  arithmetic_ok : bool; debug_ok : bool
}.
Definition after_callback e state event :=
 {| callback_state := state; callback_trace := (callback_trace e ++ [event])%list;
    arithmetic_ok := arithmetic_ok e; debug_ok := debug_ok e |}.
Definition check_u16 value e :=
 {| callback_state := callback_state e; callback_trace := callback_trace e;
    arithmetic_ok := arithmetic_ok e && Nat.leb value u16_max; debug_ok := debug_ok e |}.
Definition check_usize limit value e :=
 {| callback_state := callback_state e; callback_trace := callback_trace e;
    arithmetic_ok := arithmetic_ok e && Nat.leb value limit; debug_ok := debug_ok e |}.
Record Progress := {
  completed_categories : list CategoryFactoring;
  completed_buckets : list FactoringBucket;
  current_groups : list SpineGroup;
  current_ineligible : list IneligibleGroup;
  current_singletons : list SingletonMember;
  next_spine_ordinal : nat;
  refusals : list Refusal;
  effect : Effects
}.
Definition with_effect p e :=
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := current_groups p; current_ineligible := current_ineligible p;
    current_singletons := current_singletons p; next_spine_ordinal := next_spine_ordinal p;
    refusals := refusals p; effect := e |}.
Definition with_refusals p messages :=
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := current_groups p; current_ineligible := current_ineligible p;
    current_singletons := current_singletons p; next_spine_ordinal := next_spine_ordinal p;
    refusals := messages; effect := effect p |}.
Definition append_singleton p rule reason :=
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := current_groups p; current_ineligible := current_ineligible p;
    current_singletons := (current_singletons p ++
      [{| singleton_rule := rule; singleton_reason := reason |}])%list;
    next_spine_ordinal := next_spine_ordinal p; refusals := refusals p; effect := effect p |}.
Definition append_ineligible p indices reason :=
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := current_groups p; current_ineligible := (current_ineligible p ++
      [{| member_rule_idxs := indices; ineligible_reason := reason |}])%list;
    current_singletons := current_singletons p; next_spine_ordinal := next_spine_ordinal p;
    refusals := refusals p; effect := effect p |}.
Definition start_bucket p :=
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := []; current_ineligible := []; current_singletons := [];
    next_spine_ordinal := next_spine_ordinal p; refusals := refusals p; effect := effect p |}.
Definition finish_bucket p trigger count :=
 {| completed_categories := completed_categories p; completed_buckets := (completed_buckets p ++
      [{| leading_literal := trigger; cohort_size := count; groups := current_groups p;
          ineligible := current_ineligible p; singletons := current_singletons p |}])%list;
    current_groups := []; current_ineligible := []; current_singletons := [];
    next_spine_ordinal := next_spine_ordinal p; refusals := refusals p; effect := effect p |}.
Definition finish_category p category :=
 {| completed_categories := (completed_categories p ++
      [{| category_src_idx := category; buckets := completed_buckets p;
          category_refusals := refusals p |}])%list;
    completed_buckets := []; current_groups := []; current_ineligible := [];
    current_singletons := []; next_spine_ordinal := 0; refusals := []; effect := effect p |}.
Definition initial state :=
 {| completed_categories := []; completed_buckets := []; current_groups := [];
    current_ineligible := []; current_singletons := []; next_spine_ordinal := 0;
    refusals := []; effect := {| callback_state := state; callback_trace := [];
                                arithmetic_ok := true; debug_ok := true |} |}.

Inductive StopReason :=
| RuleIndexFault (category : nat) (member : F.CandidateMember)
| TreeExhausted (configuration : F.Configuration)
| TreeFault (reason : F.Fault) (configuration : F.Configuration).
Inductive RunResult := Ran (progress : Progress) | Stopped (reason : StopReason) (progress : Progress).
Inductive ExclusionResult :=
| Excluded (groupable : list F.CandidateMember) (progress : Progress)
| ExclusionFault (member : F.CandidateMember) (progress : Progress).

(** No precomputed cast table: the original indexed lookup and helper occur
    here, once per bucket member, before inspecting that member's item list. *)
Fixpoint exclude_members adapter category rules members p := match members with
| [] => Excluded [] p
| member :: rest => match nth_error rules (F.candidate_rule member) with
  | None => ExclusionFault member p
  | Some rule =>
      let '(participates, state) := cast_participates adapter rule (callback_state (effect p)) in
      let called := with_effect p (after_callback (effect p) state
        (CastMember category (F.candidate_rule member) rule)) in
      let '(keep, updated) := if participates then
        (false, append_singleton called (F.candidate_rule member) CastMachinery)
        else match F.candidate_items member with
        | [] => (false, append_singleton called (F.candidate_rule member) EmptySequence)
        | _ :: _ => (true, called) end in
      match exclude_members adapter category rules rest updated with
      | Excluded retained after => Excluded (if keep then member :: retained else retained) after
      | ExclusionFault failed after => ExclusionFault failed after end
  end end.
Theorem missing_rule_stops_before_cast : forall adapter category rules member rest p,
  nth_error rules (F.candidate_rule member) = None ->
  exclude_members adapter category rules (member :: rest) p = ExclusionFault member p.
Proof. intros; cbn [exclude_members]; now rewrite H. Qed.
Theorem cast_wins_over_empty_sequence : forall adapter category rules member rest p rule state,
  nth_error rules (F.candidate_rule member) = Some rule ->
  cast_participates adapter rule (callback_state (effect p)) = (true, state) ->
  exclude_members adapter category rules (member :: rest) p =
  exclude_members adapter category rules rest
    (append_singleton (with_effect p (after_callback (effect p) state
      (CastMember category (F.candidate_rule member) rule))) (F.candidate_rule member) CastMachinery).
Proof.
  intros; cbn [exclude_members]; rewrite H, H0.
  destruct (exclude_members adapter category rules rest
    (append_singleton (with_effect p (after_callback (effect p) state
      (CastMember category (F.candidate_rule member) rule))) (F.candidate_rule member) CastMachinery)); reflexivity.
Qed.

Definition merge_tree_effects p tree_effect :=
  let e := effect p in
  with_refusals
    (with_effect p {| callback_state := callback_state e; callback_trace := callback_trace e;
      arithmetic_ok := arithmetic_ok e && F.arithmetic_ok tree_effect;
      debug_ok := debug_ok e && F.debug_ok tree_effect |})
    (refusals p ++ List.map TreeRefusal (F.refusals tree_effect))%list.
Definition append_group p body forest :=
  let id := SPINE_RULE_BASE + next_spine_ordinal p in
  let before_push := check_u16 id (effect p) in
  let updated_ordinal := S (next_spine_ordinal p) in
 {| completed_categories := completed_categories p; completed_buckets := completed_buckets p;
    current_groups := (current_groups p ++
      [{| spine_id := id; body_src_idx := body; roots := forest |}])%list;
    current_ineligible := current_ineligible p; current_singletons := current_singletons p;
    next_spine_ordinal := updated_ordinal; refusals := refusals p;
    effect := check_u16 updated_ordinal before_push |}.
Definition process_group mode tree_fuel usize_max stance category trigger item members p :=
  match members with
  | [member] => Ran (append_singleton p (F.candidate_rule member) LoneRootChild)
  | _ =>
      let indices := List.map F.candidate_rule members in
      let bodies := unique_body_sources members [] in
      match tree_call mode tree_fuel usize_max stance item members with
      | F.OriginalContinue suspended =>
          Stopped (TreeExhausted (F.original_configuration suspended))
            (merge_tree_effects p (F.effects (F.original_configuration suspended)))
      | F.OriginalFailed reason failed =>
          Stopped (TreeFault reason (F.original_configuration failed))
            (merge_tree_effects p (F.effects (F.original_configuration failed)))
      | F.OriginalFinished forest tree_effect =>
          let after_tree := merge_tree_effects p tree_effect in
          match F.interior_accepts tree_effect with
          | _ :: _ => Ran (append_ineligible after_tree indices (InteriorAccept (F.interior_accepts tree_effect)))
          | [] => if Nat.ltb 1 (List.length bodies) then
              Ran (append_ineligible after_tree indices (NonUniformBodySrc bodies))
            else
              let leaves := forest_leaf_count forest in
              let counted := with_effect after_tree (check_usize usize_max leaves (effect after_tree)) in
              let checked := if Nat.eqb leaves (List.length indices) then counted else
                with_refusals counted (refusals counted ++
                  [LeafCountMismatch category trigger leaves (List.length indices)])%list in
              let body := match bodies with [] => category | first :: _ => first end in
              Ran (append_group checked body forest)
          end
      end
  end.
Theorem group_callsite_correspondence : forall tree_fuel usize_max stance category trigger item members p,
  process_group Relocated tree_fuel usize_max stance category trigger item members p =
  process_group Original tree_fuel usize_max stance category trigger item members p.
Proof.
  intros; unfold process_group.
  destruct members as [|first [|second rest]]; try reflexivity;
    rewrite imported_tree_call_correspondence; reflexivity.
Qed.
Fixpoint process_groups mode tree_fuel usize_max stance category trigger parts p := match parts with
| [] => Ran p
| (item, members) :: rest =>
    match process_group mode tree_fuel usize_max stance category trigger item members p with
    | Ran updated => process_groups mode tree_fuel usize_max stance category trigger rest updated
    | Stopped reason failed => Stopped reason failed end end.
Theorem groups_preserve_complete_progress : forall parts tree_fuel usize_max stance category trigger p,
  process_groups Relocated tree_fuel usize_max stance category trigger parts p =
  process_groups Original tree_fuel usize_max stance category trigger parts p.
Proof.
  induction parts as [|[item members] rest IH]; intros; cbn [process_groups]; [reflexivity|].
  rewrite group_callsite_correspondence.
  destruct (process_group Original tree_fuel usize_max stance category trigger item members p); auto.
Qed.
Definition process_bucket mode adapter tree_fuel usize_max stance category rules trigger members p :=
  match exclude_members adapter category rules members (start_bucket p) with
  | ExclusionFault member failed => Stopped (RuleIndexFault category member) failed
  | Excluded groupable after_exclusions =>
      match process_groups mode tree_fuel usize_max stance category trigger
        (root_parts groupable) after_exclusions with
      | Ran after_groups => Ran (finish_bucket after_groups trigger (List.length members))
      | Stopped reason failed => Stopped reason failed end end.
Theorem bucket_callback_and_output_correspondence : forall adapter tree_fuel usize_max stance category rules trigger members p,
  process_bucket Relocated adapter tree_fuel usize_max stance category rules trigger members p =
  process_bucket Original adapter tree_fuel usize_max stance category rules trigger members p.
Proof.
  intros; unfold process_bucket.
  destruct (exclude_members adapter category rules members (start_bucket p)); [|reflexivity].
  rewrite groups_preserve_complete_progress; reflexivity.
Qed.
Fixpoint process_buckets mode adapter tree_fuel usize_max stance category rules entries p := match entries with
| [] => Ran p
| (trigger, members) :: rest =>
    match process_bucket mode adapter tree_fuel usize_max stance category rules trigger members p with
    | Ran updated => process_buckets mode adapter tree_fuel usize_max stance category rules rest updated
    | Stopped reason failed => Stopped reason failed end end.
Theorem buckets_preserve_callback_schedule : forall entries adapter tree_fuel usize_max stance category rules p,
  process_buckets Relocated adapter tree_fuel usize_max stance category rules entries p =
  process_buckets Original adapter tree_fuel usize_max stance category rules entries p.
Proof.
  induction entries as [|[trigger members] rest IH]; intros; cbn [process_buckets]; [reflexivity|].
  rewrite bucket_callback_and_output_correspondence.
  destruct (process_bucket Original adapter tree_fuel usize_max stance category rules trigger members p); auto.
Qed.

Definition check_category_limits recovery_base category p :=
  let ending := SPINE_RULE_BASE + next_spine_ordinal p in
  let recovery_checked := if Nat.leb recovery_base ending then
    with_refusals p (refusals p ++
      [RecoveryCollision category (next_spine_ordinal p) ending recovery_base])%list else p in
  if Nat.leb u16_max ending then with_refusals recovery_checked
    (refusals recovery_checked ++ [RuleIndexCeiling category ending])%list else recovery_checked.
Definition process_category mode adapter metadata tree_fuel usize_max stance recovery_base index rules p :=
  let category := category_cast index in
  let '(members, state) := discover adapter metadata category rules (callback_state (effect p)) in
  let called := with_effect p (after_callback (effect p) state (DiscoverCategory category rules)) in
  match process_buckets mode adapter tree_fuel usize_max stance category rules (bucket_members members) called with
  | Ran updated => Ran (finish_category (check_category_limits recovery_base category updated) category)
  | Stopped reason failed => Stopped reason failed end.
Theorem category_discovery_and_refusal_correspondence : forall adapter metadata tree_fuel usize_max stance recovery_base index rules p,
  process_category Relocated adapter metadata tree_fuel usize_max stance recovery_base index rules p =
  process_category Original adapter metadata tree_fuel usize_max stance recovery_base index rules p.
Proof. intros; unfold process_category; destruct (discover adapter metadata (category_cast index) rules (callback_state (effect p))); rewrite buckets_preserve_callback_schedule; reflexivity. Qed.
Fixpoint process_categories mode adapter metadata tree_fuel usize_max stance recovery_base index rows p := match rows with
| [] => Ran p
| rules :: rest =>
    match process_category mode adapter metadata tree_fuel usize_max stance recovery_base index rules p with
    | Ran updated => process_categories mode adapter metadata tree_fuel usize_max stance recovery_base (S index) rest updated
    | Stopped reason failed => Stopped reason failed end end.
Theorem categories_preserve_owned_outputs_and_effect_prefix : forall rows adapter metadata tree_fuel usize_max stance recovery_base index p,
  process_categories Relocated adapter metadata tree_fuel usize_max stance recovery_base index rows p =
  process_categories Original adapter metadata tree_fuel usize_max stance recovery_base index rows p.
Proof.
  induction rows as [|rules rest IH]; intros; cbn [process_categories]; [reflexivity|].
  rewrite category_discovery_and_refusal_correspondence.
  destruct (process_category Original adapter metadata tree_fuel usize_max stance recovery_base index rules p); auto.
Qed.

(** The disabled original loop has no rule lookup and no cast/tree parameter. *)
Definition disabled_bucket entry :=
 {| leading_literal := fst entry; cohort_size := List.length (snd entry);
    groups := []; ineligible := [];
    singletons := List.map (fun member =>
      {| singleton_rule := F.candidate_rule member; singleton_reason := FactoringDisabled |}) (snd entry) |}.
Fixpoint disabled_categories adapter metadata index rows p := match rows with
| [] => p
| rules :: rest =>
    let category := category_cast index in
    let '(members, state) := discover adapter metadata category rules (callback_state (effect p)) in
    let called := after_callback (effect p) state (DiscoverCategory category rules) in
    let updated :=
      {| completed_categories := (completed_categories p ++
          [{| category_src_idx := category; buckets := List.map disabled_bucket (bucket_members members);
              category_refusals := [] |}])%list;
         completed_buckets := []; current_groups := []; current_ineligible := [];
         current_singletons := []; next_spine_ordinal := 0; refusals := []; effect := called |} in
    disabled_categories adapter metadata (S index) rest updated
end.
Definition build_prefix_factoring_with mode adapter tree_fuel usize_max stance recovery_base rows state :=
  let '(metadata, prepared) := prepare_prefix_map adapter state in
  let p := initial state in
  process_categories mode adapter metadata tree_fuel usize_max stance recovery_base 0 rows
    (with_effect p (after_callback (effect p) prepared PreparePrefixMap)).
Definition disabled_partition adapter rows state :=
  let '(metadata, prepared) := prepare_prefix_map adapter state in
  let p := initial state in
  disabled_categories adapter metadata 0 rows
    (with_effect p (after_callback (effect p) prepared PreparePrefixMap)).
Definition emission_partition (enabled : bool) mode adapter tree_fuel usize_max stance recovery_base rows state :=
  if enabled then build_prefix_factoring_with mode adapter tree_fuel usize_max stance recovery_base rows state
  else Ran (disabled_partition adapter rows state).

Theorem enabled_partition_source_correspondence : forall adapter tree_fuel usize_max stance recovery_base rows state,
  build_prefix_factoring_with Relocated adapter tree_fuel usize_max stance recovery_base rows state =
  build_prefix_factoring_with Original adapter tree_fuel usize_max stance recovery_base rows state.
Proof.
  intros; unfold build_prefix_factoring_with; destruct (prepare_prefix_map adapter state).
  apply categories_preserve_owned_outputs_and_effect_prefix.
Qed.
Theorem enabled_and_disabled_source_correspondence : forall enabled adapter tree_fuel usize_max stance recovery_base rows state,
  emission_partition enabled Relocated adapter tree_fuel usize_max stance recovery_base rows state =
  emission_partition enabled Original adapter tree_fuel usize_max stance recovery_base rows state.
Proof. intros []; cbn [emission_partition]; intros; [apply enabled_partition_source_correspondence|reflexivity]. Qed.
Theorem disabled_does_not_consult_cast : forall prepare discovery cast_left cast_right rows state,
  disabled_partition {| prepare_prefix_map := prepare; discover := discovery; cast_participates := cast_left |} rows state =
  disabled_partition {| prepare_prefix_map := prepare; discover := discovery; cast_participates := cast_right |} rows state.
Proof.
  intros prepare discovery cast_left cast_right rows state; unfold disabled_partition.
  cbn [prepare_prefix_map]; destruct (prepare state) as [metadata prepared].
  generalize 0, (with_effect (initial state)
    (after_callback (effect (initial state)) prepared PreparePrefixMap)).
  induction rows as [|rules rest IH]; intros index p; cbn [disabled_categories discover]; [reflexivity|].
  destruct (discovery metadata (category_cast index) rules (callback_state (effect p))); apply IH.
Qed.
Theorem disabled_bucket_is_identity_partition : forall trigger members,
  groups (disabled_bucket (trigger, members)) = [] /\
  ineligible (disabled_bucket (trigger, members)) = [] /\
  List.map singleton_rule (singletons (disabled_bucket (trigger, members))) = List.map F.candidate_rule members /\
  Forall (fun singleton => singleton_reason singleton = FactoringDisabled)
    (singletons (disabled_bucket (trigger, members))).
Proof.
  intros; cbn [disabled_bucket fst snd groups ineligible singletons].
  repeat split; try reflexivity.
  - rewrite map_map; reflexivity.
  - apply Forall_forall; intros singleton Hin. apply in_map_iff in Hin.
    destruct Hin as [member [Heq _]]; subst; reflexivity.
Qed.
Definition result_progress result := match result with Ran p | Stopped _ p => p end.
Definition returning_domain result := match result with
| Ran p => arithmetic_ok (effect p) && debug_ok (effect p) | Stopped _ _ => false end.
Corollary faithful_returning_partition_is_preserved : forall enabled adapter tree_fuel usize_max stance recovery_base rows state,
  returning_domain (emission_partition enabled Original adapter tree_fuel usize_max stance recovery_base rows state) = true ->
  emission_partition enabled Relocated adapter tree_fuel usize_max stance recovery_base rows state =
  emission_partition enabled Original adapter tree_fuel usize_max stance recovery_base rows state.
Proof. intros; apply enabled_and_disabled_source_correspondence. Qed.
Corollary category_refusal_strings_preserved : forall enabled adapter tree_fuel usize_max stance recovery_base rows state
    (render : Refusal -> string),
  List.map (fun category => List.map render (category_refusals category))
    (completed_categories (result_progress
      (emission_partition enabled Relocated adapter tree_fuel usize_max stance recovery_base rows state))) =
  List.map (fun category => List.map render (category_refusals category))
    (completed_categories (result_progress
      (emission_partition enabled Original adapter tree_fuel usize_max stance recovery_base rows state))).
Proof. intros; rewrite enabled_and_disabled_source_correspondence; reflexivity. Qed.
End OriginalCallbacks.

Print Assumptions imported_tree_call_correspondence.
Print Assumptions missing_rule_stops_before_cast.
Print Assumptions cast_wins_over_empty_sequence.
Print Assumptions group_callsite_correspondence.
Print Assumptions buckets_preserve_callback_schedule.
Print Assumptions categories_preserve_owned_outputs_and_effect_prefix.
Print Assumptions enabled_partition_source_correspondence.
Print Assumptions enabled_and_disabled_source_correspondence.
Print Assumptions disabled_does_not_consult_cast.
Print Assumptions disabled_bucket_is_identity_partition.
Print Assumptions faithful_returning_partition_is_preserved.
Print Assumptions category_refusal_strings_preserved.

End PrefixFactoringProjection.
