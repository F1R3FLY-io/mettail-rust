(** Exact source-observation relocation of the ORIGINAL prefix bucket driver.

    Boundary: emit_prefix_arms_for_category, from cross_cat_infix_sources through
    its second projection pass; emission of transitions remains outside scope.
    Two rule rosters remain distinct: global authored rules feed the cross-source
    scan and unchanged helper callbacks; indexed rules feed both local passes.
    This model does not replace any atomic, binder, FIRST, native, BP, category
    census, guest-opener or identifier analysis. Those are the SAME original
    callbacks in both runs. Atomic-row construction and ordered bucket insertion
    compose their already-proved original/shared implementations directly.

    Schedule: global category filter -> infix callback -> category census -> BP
    table -> sorted unique sources -> result leading literals -> cross-LHS rows
    -> local pass one -> delayed atomic flush -> local pass two. Pass two calls
    classification again, without caching. Binder body lookup occurs before the
    first syntax observation; '(' is rejected only on the binder-literal path.
    Leading Ident wins over leading category. Category-leading rows require a
    resolved source and exclude same-category led BEFORE requesting FIRST.
    Cross-unary/body fallback is the owner; cross-LHS/projection fallback is 0.
    Compatibility checks retain gate -> variable -> source-only -> home-var
    short-circuit order for EACH projection FIRST row, not once per source.

    State and trace include every callback invocation and preserve arbitrary
    callback state transitions. Pure source fields have explicit observation
    events; unchanged helper internals are not newly certified here. Source
    names use original spelling equality at these driver sites. The ordered set
    models the value of HashSet -> enumeration -> sort, not its hash/tree layout.
    FIRST rows, atomic rows, guards and descriptors retain order and duplicates.
    Bucket keys retain the existing formatter and first-payload policy.

    Natural owner/rule values stand for supplied u16 values; source positions
    use the existing modulo-65536 cast. No new rejection, allocation limit,
    failure-to-empty policy, parser algorithm, semantic pruning theorem or
    whole-parser correctness claim is introduced. Lists instrument finite Rust
    loops, not recursive Rust. Allocation, Clone/Drop effects, formatter
    internals, helper nontermination/panic and emitted transition semantics are
    outside this finite successful-call source correspondence.
*)
From Stdlib Require Import List String Bool Arith.
From Stdlib Require Import FSets.FSetAVL Structures.OrderedTypeEx.
From PrattailWpdaRuntime Require Import AtomicPrefixDescriptorProjection
  UnifiedPrefixDescriptorProjection PrefixMemberDescriptorRelocation.
Import ListNotations.
Set Implicit Arguments.

Module OriginalPrefixBucketDriverProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.
Module F := OriginalFirstSetProjection.OriginalFirstSetProjection.
Module P := AtomicPrefixDescriptorProjection.AtomicPrefixDescriptorProjection.
Module U := UnifiedPrefixDescriptorProjection.UnifiedPrefixDescriptorProjection.
Module B := BinderRuleProjection.BinderRuleProjection.
Module H := PrefixMemberDescriptorRelocation.PrefixMemberDescriptorRelocation.
Module Sources := FSetAVL.Make String_as_OT.

Section Driver.
Context {Rule Literal Pattern Table State : Type}.

Record SourceRule := {
  original_rule : @F.SourceRule Rule;
  explicit_prefix_bp : option nat
}.
Definition rule_payload mode rule := F.payload mode (original_rule rule).
Definition rule_category mode rule := F.category mode (original_rule rule).
Definition rule_head mode rule := F.syntax_head mode (original_rule rule).
(* F's existing FIRST-only head projection omits the close field. This
   accessor reads that SAME source occurrence when the guest branch asks for
   it, after nested-openers. Its otherwise-empty value is unreachable at that
   call site; the following lemma establishes the occurrence correlation. *)
Definition guest_close rule := match F.source_syntax (original_rule rule) with
| Some (F.SourceGuest _ close :: _) => close
| _ => EmptyString end.
Lemma guest_close_is_from_the_selected_source_node : forall payload category legacy bp open close rest,
  guest_close {| original_rule := {| F.source_payload := payload; F.source_category := category;
    F.source_syntax := Some (F.SourceGuest open close :: rest); F.source_legacy := legacy |};
    explicit_prefix_bp := bp |} = close.
Proof. reflexivity. Qed.

(** Exactly the three fields read after the original infix classifier. *)
Record InfixObservation := {
  infix_source : string; infix_result : string; infix_cross : bool
}.
Record Callbacks := {
  infix : Rule -> State -> option InfixObservation * State;
  category_census : State -> list string * State;
  bp_table : State -> Table * State;
  leading_literals : string -> State -> list string * State;
  first_set : string -> State -> list (@F.FirstToken Pattern) * State;
  atomic : Rule -> State -> @A.Descriptor Literal * State;
  binder : Rule -> State -> option B.BinderShape * State;
  initial_body : B.BinderShape -> State -> option string * State;
  prefix_bp : string -> option nat -> Table -> State -> nat * State;
  led_left_bp : Rule -> string -> Table -> State -> option nat * State;
  nested_openers : string -> State -> list string * State;
  source_var_only : string -> State -> bool * State;
  home_var : string -> State -> bool * State;
  row_constructors : @P.Callbacks Literal Pattern State;
  formatter : Pattern -> string
}.
Inductive Phase := FirstPass | SecondPass.
Inductive Event :=
| RuleCategory (rule : Rule)
| InfixCall (rule : Rule)
| CensusCall | BpTableCall | SortedSources (names : list string)
| LeadingCall (category : string) | FirstCall (category : string)
| AtomicCall (phase : Phase) (rule : Rule)
| AtomicRows (events : list (@P.Event Literal))
| BinderCall (rule : Rule) | InitialBodyCall
| CategoryIndex (name : string)
| SyntaxFirst (rule : Rule) | PrefixMetadata (rule : Rule)
| PrefixBpCall (source : string) | LedCall (rule : Rule)
| QuoteCall (predicate : F.Predicate)
| NestedOpenersCall (open : string) | GuestClose (rule : Rule)
| SourceVarOnlyCall (source : string) | HomeVarCall (result : string)
| BucketCall (events : list U.BucketEvent)
| DelayedAtomicAppend (count : nat) | AtomicFlush.

Record Progress := {
  output : @U.BucketState Pattern (P.Unified Pattern);
  deferred : list (P.AtomicRow Pattern);
  effects : State;
  trace : list Event
}.
Definition progress out pending state events :=
 {| output := out; deferred := pending; effects := state; trace := events |}.
Definition event e p := progress (output p) (deferred p) (effects p) (trace p ++ [e]).
Definition invoke {X} (call : State -> X * State) e p :=
  let '(answer,next) := call (effects p) in
  (answer, progress (output p) (deferred p) next (trace p ++ [e])).

Definition insert mode cb pattern guard descriptor p :=
  let incoming := {| U.incoming_pattern := pattern; U.incoming_guard := guard;
                     U.incoming_descriptor := descriptor |} in
  let '(out,events) := match mode with
    | F.Original => U.original_insert (formatter cb) incoming (output p)
    | F.Relocated => U.shared_insert (U.source_formatter (formatter cb)) incoming (output p)
    end in
  progress out (deferred p) (effects p) (trace p ++ [BucketCall events]).
Lemma insert_projection : forall cb pattern guard descriptor p,
  insert F.Relocated cb pattern guard descriptor p = insert F.Original cb pattern guard descriptor p.
Proof. intros; unfold insert; rewrite U.exact_bucket_source_accessor_step; reflexivity. Qed.

Definition quote_insert mode cb predicate descriptor p :=
  let '(row,next) := invoke (P.quote (row_constructors cb) predicate) (QuoteCall predicate) p in
  insert mode cb (fst row) (snd row) descriptor next.
Lemma quote_insert_projection : forall cb predicate descriptor p,
  quote_insert F.Relocated cb predicate descriptor p = quote_insert F.Original cb predicate descriptor p.
Proof. intros; unfold quote_insert; destruct (invoke _ _ _) as [row next]; apply insert_projection. Qed.

Fixpoint scan_sources mode cb result rules sources p := match rules with
| [] => (sources,p)
| rule :: rest =>
    let observed := event (RuleCategory (rule_payload mode rule)) p in
    if String.eqb (rule_category mode rule) result then
      let '(info,called) := invoke (infix cb (rule_payload mode rule))
        (InfixCall (rule_payload mode rule)) observed in
      let sources := match info with
      | Some info => if infix_cross info then
          if negb (String.eqb (infix_source info) (infix_result info))
          then Sources.add (infix_source info) sources else sources
        else sources
      | None => sources end in
      scan_sources mode cb result rest sources called
    else scan_sources mode cb result rest sources observed
end.
Lemma scan_sources_projection : forall cb result rules sources p,
  scan_sources F.Relocated cb result rules sources p = scan_sources F.Original cb result rules sources p.
Proof.
  intros cb result rules; induction rules as [|rule rest IH]; intros; [reflexivity|].
  cbn [scan_sources rule_payload rule_category].
  destruct (String.eqb _ _); [destruct (invoke _ _ _) as [info called]|]; apply IH.
Qed.

Definition category_index categories name p :=
  (H.lookup_src_idx name categories, event (CategoryIndex name) p).
Definition fallback (owner : nat) index := match index with Some value => value | None => owner end.
Definition sigil leads (row : @F.FirstToken Pattern) := match F.leading_literal row with
| None => false | Some text => existsb (String.eqb text) leads end.
Fixpoint cross_rows mode cb source leads rows p := match rows with
| [] => p
| row :: rest => cross_rows mode cb source leads rest
    (insert mode cb (F.pattern row) (F.guard row) (P.CrossCatLhs source (sigil leads row)) p)
end.
Lemma cross_rows_projection : forall cb source leads rows p,
  cross_rows F.Relocated cb source leads rows p = cross_rows F.Original cb source leads rows p.
Proof. intros cb source leads rows; induction rows; intros; cbn [cross_rows]; [reflexivity|].
  rewrite insert_projection; apply IHrows. Qed.
Fixpoint cross_sources mode cb categories leads sources p := match sources with
| [] => p
| source :: rest =>
    let '(index,p) := category_index categories source p in
    let '(rows,p) := invoke (first_set cb source) (FirstCall source) p in
    cross_sources mode cb categories leads rest (cross_rows mode cb (fallback 0 index) leads rows p)
end.
Lemma cross_sources_projection : forall cb categories leads sources p,
  cross_sources F.Relocated cb categories leads sources p = cross_sources F.Original cb categories leads sources p.
Proof. intros cb categories leads sources; induction sources; intros; cbn [cross_sources]; [reflexivity|].
  destruct (category_index _ _ _) as [index p1]; destruct (invoke _ _ _) as [rows p2].
  rewrite cross_rows_projection; apply IHsources. Qed.

Definition atomic_rows mode cb shape state := match mode with
| F.Original => P.source_rows (row_constructors cb) shape state
| F.Relocated => P.shared_rows (row_constructors cb) shape state end.
Lemma atomic_rows_projection : forall cb shape state,
  atomic_rows F.Relocated cb shape state = atomic_rows F.Original cb shape state.
Proof. intros; apply P.original_callback_rows_and_trace. Qed.
Definition append_atomic mode cb owner index shape p :=
  let rows := atomic_rows mode cb shape (effects p) in
  let attached := P.attach_rows owner index (P.pairs rows) in
  progress (output p) (deferred p ++ attached) (P.row_state rows)
    (trace p ++ [AtomicRows (P.trace rows); DelayedAtomicAppend (List.length attached)]).
Lemma append_atomic_projection : forall cb owner index shape p,
  append_atomic F.Relocated cb owner index shape p = append_atomic F.Original cb owner index shape p.
Proof. intros; unfold append_atomic; rewrite atomic_rows_projection; reflexivity. Qed.

Fixpoint category_rows mode cb index source rows p := match rows with
| [] => p
| row :: rest => category_rows mode cb index source rest
    (insert mode cb (F.pattern row) (F.guard row) (P.LeadingCategory index source) p)
end.
Lemma category_rows_projection : forall cb index source rows p,
  category_rows F.Relocated cb index source rows p = category_rows F.Original cb index source rows p.
Proof. intros cb index source rows; induction rows; intros; cbn [category_rows]; [reflexivity|].
  rewrite insert_projection; apply IHrows. Qed.

Definition binder_branch mode cb categories table result owner index rule shape p :=
  let '(body,p) := invoke (initial_body cb shape) InitialBodyCall p in
  let '(body,p) := match body with
    | None => (owner,p)
    | Some name => let '(position,p) := category_index categories name p in (fallback owner position,p)
    end in
  let p := event (SyntaxFirst (rule_payload mode rule)) p in
  match rule_head mode rule with
  | Some (Some (F.Literal trigger)) =>
      if String.eqb trigger "(" then p
      else quote_insert mode cb (F.Fixed trigger) (P.BinderPrefix index body) p
  | Some (Some (F.Token kind)) =>
      quote_insert mode cb (F.CaptureName kind) (P.LeadingTokenKindCapture index body kind) p
  | Some (Some (F.Guest open)) =>
      let '(nested,p) := invoke (nested_openers cb open) (NestedOpenersCall open) p in
      let p := event (GuestClose (rule_payload mode rule)) p in
      quote_insert mode cb (F.GuestOpen open)
        (P.LeadingGuestBody index body open nested (guest_close rule)) p
  | Some (Some F.Param) => match B.shape_leading_ident_capture shape with
      | Some _ => quote_insert mode cb F.Ident (P.LeadingTokenKindCapture index body "Ident") p
      | None => match B.shape_leading_category shape with
        | None => p
        | Some source => let '(position,p) := category_index categories source p in
          match position with
          | None => p
          | Some source_index =>
            let '(led,p) := invoke (led_left_bp cb (rule_payload mode rule) result table)
              (LedCall (rule_payload mode rule)) p in
            match led with
            | Some _ => p
            | None => let '(rows,p) := invoke (first_set cb source) (FirstCall source) p in
              category_rows mode cb index source_index rows p
            end
          end
        end
      end
  | _ => p
  end.
Lemma binder_branch_projection : forall cb categories table result owner index rule shape p,
  binder_branch F.Relocated cb categories table result owner index rule shape p =
  binder_branch F.Original cb categories table result owner index rule shape p.
Proof.
  intros; unfold binder_branch, rule_payload, rule_head.
  rewrite !F.payload_projection, F.syntax_head_projection.
  destruct (invoke _ _ _) as [[body|] p1];
    repeat match goal with
    | |- context[category_index ?cs ?name ?state] => destruct (category_index cs name state) as [position next]
    end;
    repeat match goal with
    | |- context[match ?x with _ => _ end] => destruct x
    end;
    try rewrite quote_insert_projection;
    try rewrite category_rows_projection; reflexivity.
Qed.

Definition pass_one_rule mode cb categories table result owner indexed p :=
  let '(index,rule) := indexed in
  let '(shape,p) := invoke (atomic cb (rule_payload mode rule))
    (AtomicCall FirstPass (rule_payload mode rule)) p in
  let p := append_atomic mode cb owner index shape p in
  match shape with
  | A.CrossCatPrefixUnary trigger source _ =>
      let '(position,p) := category_index categories source p in
      let p := event (PrefixMetadata (rule_payload mode rule)) p in
      let '(bp,p) := invoke (prefix_bp cb source (explicit_prefix_bp rule) table) (PrefixBpCall source) p in
      quote_insert mode cb (F.Fixed trigger)
        (P.CrossCatPrefixUnary index (fallback owner position) bp) p
  | A.NullaryLiteralRun trigger _ _ =>
      quote_insert mode cb (F.Fixed trigger) (P.NullaryLiteralRun index) p
  | A.CrossCatProjection _ _ => p
  | _ => let '(shape,p) := invoke (binder cb (rule_payload mode rule))
          (BinderCall (rule_payload mode rule)) p in
      match shape with
      | None => p
      | Some shape => binder_branch mode cb categories table result owner index rule shape p
      end
  end.
Lemma pass_one_rule_projection : forall cb categories table result owner indexed p,
  pass_one_rule F.Relocated cb categories table result owner indexed p =
  pass_one_rule F.Original cb categories table result owner indexed p.
Proof.
  intros cb categories table result owner [index rule] p.
  unfold pass_one_rule, rule_payload; rewrite !F.payload_projection.
  destruct (invoke _ _ _) as [shape p1]; rewrite append_atomic_projection.
  destruct shape; cbn -[quote_insert binder_branch invoke category_index append_atomic];
    repeat match goal with
    | |- context[match ?x with _ => _ end] => destruct x
    end;
    try rewrite quote_insert_projection;
    try rewrite binder_branch_projection; reflexivity.
Qed.
Fixpoint pass_one mode cb categories table result owner rules p := match rules with
| [] => p
| rule :: rest => pass_one mode cb categories table result owner rest
    (pass_one_rule mode cb categories table result owner rule p)
end.
Lemma pass_one_projection : forall cb categories table result owner rules p,
  pass_one F.Relocated cb categories table result owner rules p =
  pass_one F.Original cb categories table result owner rules p.
Proof. intros cb categories table result owner rules; induction rules; intros; cbn [pass_one]; [reflexivity|].
  rewrite pass_one_rule_projection; apply IHrules. Qed.

Fixpoint flush_rows mode cb rows p := match rows with
| [] => p
| row :: rest => flush_rows mode cb rest
    (insert mode cb (P.pattern row) (P.guard row) (P.Atomic row) (event AtomicFlush p))
end.
Lemma flush_rows_projection : forall cb rows p,
  flush_rows F.Relocated cb rows p = flush_rows F.Original cb rows p.
Proof. intros cb rows; induction rows; intros; cbn [flush_rows]; [reflexivity|].
  rewrite insert_projection; apply IHrows. Qed.
Definition flush mode cb p :=
  flush_rows mode cb (deferred p) (progress (output p) [] (effects p) (trace p)).
Lemma flush_projection : forall cb p, flush F.Relocated cb p = flush F.Original cb p.
Proof. intros; apply flush_rows_projection. Qed.

Definition suppress cb (enabled : bool) result source (row : @F.FirstToken Pattern) p :=
  if enabled then if F.variable_contribution row then
    let '(source_only,p) := invoke (source_var_only cb source) (SourceVarOnlyCall source) p in
    if source_only then invoke (home_var cb result) (HomeVarCall result) p else (false,p)
  else (false,p) else (false,p).
Lemma disabled_gate_does_no_work : forall cb result source row p,
  suppress cb false result source row p = (false,p).
Proof. reflexivity. Qed.
Lemma literal_row_does_no_compatibility_work : forall cb enabled result source row p,
  F.variable_contribution row = false -> suppress cb enabled result source row p = (false,p).
Proof. intros; unfold suppress; rewrite H; destruct enabled; reflexivity. Qed.
Lemma nonexclusive_source_never_reads_home : forall cb result source row p p1,
  F.variable_contribution row = true ->
  invoke (source_var_only cb source) (SourceVarOnlyCall source) p = (false,p1) ->
  suppress cb true result source row p = (false,p1).
Proof. intros; unfold suppress; rewrite H,H0; reflexivity. Qed.

Fixpoint projection_rows mode cb enabled result source index source_index rows p := match rows with
| [] => p
| row :: rest => let '(skip,p) := suppress cb enabled result source row p in
    let p := if skip then p else
      insert mode cb (F.pattern row) (F.guard row) (P.CrossCatProjection index source_index) p in
    projection_rows mode cb enabled result source index source_index rest p
end.
Lemma projection_rows_projection : forall cb enabled result source index source_index rows p,
  projection_rows F.Relocated cb enabled result source index source_index rows p =
  projection_rows F.Original cb enabled result source index source_index rows p.
Proof. intros cb enabled result source index source_index rows; induction rows; intros; cbn [projection_rows]; [reflexivity|].
  destruct (suppress _ _ _ _ _ _) as [skip next]; destruct skip;
    try rewrite insert_projection; apply IHrows. Qed.
Definition pass_two_rule mode cb enabled categories result indexed p :=
  let '(index,rule) := indexed in
  let '(shape,p) := invoke (atomic cb (rule_payload mode rule))
    (AtomicCall SecondPass (rule_payload mode rule)) p in
  match shape with
  | A.CrossCatProjection source _ =>
      let '(position,p) := category_index categories source p in
      let '(rows,p) := invoke (first_set cb source) (FirstCall source) p in
      projection_rows mode cb enabled result source index (fallback 0 position) rows p
  | _ => p
  end.
Lemma pass_two_rule_projection : forall cb enabled categories result indexed p,
  pass_two_rule F.Relocated cb enabled categories result indexed p =
  pass_two_rule F.Original cb enabled categories result indexed p.
Proof.
  intros cb enabled categories result [index rule] p.
  unfold pass_two_rule, rule_payload; rewrite F.payload_projection.
  destruct (invoke _ _ _) as [shape next]; destruct shape; try reflexivity.
  destruct (category_index _ _ _) as [position p1]; destruct (invoke _ _ _) as [rows p2].
  apply projection_rows_projection.
Qed.
Fixpoint pass_two mode cb enabled categories result rules p := match rules with
| [] => p
| rule :: rest => pass_two mode cb enabled categories result rest
    (pass_two_rule mode cb enabled categories result rule p)
end.
Lemma pass_two_projection : forall cb enabled categories result rules p,
  pass_two F.Relocated cb enabled categories result rules p =
  pass_two F.Original cb enabled categories result rules p.
Proof. intros cb enabled categories result rules; induction rules; intros; cbn [pass_two]; [reflexivity|].
  rewrite pass_two_rule_projection; apply IHrules. Qed.

Definition driver mode cb enabled result owner global indexed state :=
  let empty := progress (U.bucket_state (U.BucketMaps.empty _) []) [] state [] in
  let '(sources,p) := scan_sources mode cb result global Sources.empty empty in
  let '(categories,p) := invoke (category_census cb) CensusCall p in
  let '(table,p) := invoke (bp_table cb) BpTableCall p in
  let sources := Sources.elements sources in
  let p := event (SortedSources sources) p in
  let '(leads,p) := invoke (leading_literals cb result) (LeadingCall result) p in
  let p := cross_sources mode cb categories leads sources p in
  let p := pass_one mode cb categories table result owner indexed p in
  let p := flush mode cb p in
  pass_two mode cb enabled categories result indexed p.

Theorem complete_original_driver_source_projection : forall cb enabled result owner global indexed state,
  driver F.Relocated cb enabled result owner global indexed state =
  driver F.Original cb enabled result owner global indexed state.
Proof.
  intros; unfold driver; rewrite scan_sources_projection.
  destruct (scan_sources _ _ _ _ _ _) as [sources p0].
  destruct (invoke _ _ _) as [categories p1].
  destruct (invoke _ _ _) as [table p2].
  destruct (invoke _ _ _) as [leads p3].
  rewrite cross_sources_projection, pass_one_projection, flush_projection, pass_two_projection.
  reflexivity.
Qed.

Theorem missing_index_fallbacks_remain_distinct : forall owner,
  fallback owner None = owner /\ fallback 0 None = 0.
Proof. intros; split; reflexivity. Qed.
Theorem no_local_rules_does_not_skip_global_pass : forall mode cb enabled result owner global state,
  driver mode cb enabled result owner global [] state =
  let empty := progress (U.bucket_state (U.BucketMaps.empty _) []) [] state [] in
  let '(sources,p) := scan_sources mode cb result global Sources.empty empty in
  let '(categories,p) := invoke (category_census cb) CensusCall p in
  let '(table,p) := invoke (bp_table cb) BpTableCall p in
  let names := Sources.elements sources in
  let '(leads,p) := invoke (leading_literals cb result) (LeadingCall result) (event (SortedSources names) p) in
  flush mode cb (cross_sources mode cb categories leads names p).
Proof. reflexivity. Qed.

End Driver.

Print Assumptions insert_projection.
Print Assumptions guest_close_is_from_the_selected_source_node.
Print Assumptions scan_sources_projection.
Print Assumptions cross_sources_projection.
Print Assumptions append_atomic_projection.
Print Assumptions binder_branch_projection.
Print Assumptions pass_one_projection.
Print Assumptions flush_projection.
Print Assumptions disabled_gate_does_no_work.
Print Assumptions literal_row_does_no_compatibility_work.
Print Assumptions nonexclusive_source_never_reads_home.
Print Assumptions pass_two_projection.
Print Assumptions complete_original_driver_source_projection.
Print Assumptions missing_index_fallbacks_remain_distinct.
Print Assumptions no_local_rules_does_not_skip_global_pass.
End OriginalPrefixBucketDriverProjection.
