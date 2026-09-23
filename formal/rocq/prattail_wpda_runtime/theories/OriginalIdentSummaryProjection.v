(** Exact source-observation relocation for the three ORIGINAL prefix helpers:
    result_has_home_var_reading, ident_first_categories, and
    source_ident_first_is_var_only. Source rules/readers and the atomic descriptor
    are reused from OriginalFirstSetProjection, not recognized again.

    Home-variable reading first requires a declaration, then short-circuits an
    authored scan on ANY first legacy Var; only if absent does it read !is_data.
    The identifier closure instead seeds every non-data declaration and exact
    AtomicDescriptor::VarRule results. These are deliberately distinct predicates.
    It classifies each authored rule once, expands patterned literals with the
    ORIGINAL FirstSet helper, and tests guard absence BEFORE formatting and the
    ORIGINAL substring test contains("Ident"). Neither a semantic predicate nor
    a new token taxonomy replaces that formatter convention.

    Reverse-map vectors preserve order/duplicates. Sets/maps below are extensional
    finite contents with ordered bucket payloads. HashSet enumeration is supplied
    as the SAME opaque enumeration operation in both runs; it is NOT sorted or
    replaced by list insertion order. Fuel compares finite queue states even for
    interrupted traversals. No assertion about arbitrary enumeration completeness
    or termination is needed for this source-substitution theorem.

    Var-only analysis eagerly computes that closure, groups ALL authored rules in
    source order, then uses explicit frames (category,next_rule). The cursor is
    incremented BEFORE inspecting its rule. First legacy Var and Terminal skip;
    a same-category first Category skips BEFORE purity. Purity runs three passes:
    count non-Terminals, then all(Category|Terminal), then all(!Terminal), with
    exact short-circuiting. This happens even when the target is not Ident-first.
    Only a pure Ident-first edge inserts visited; revisits skip, new edges push.
    Non-pure Ident-first rejects immediately. The fallback accepts ONLY a present
    first syntax Literal, including for unsupported/builtin legacy items.

    The theorem compares every finite result, callback state, queue/frame/cursor,
    visited state, and observation trace under exact borrowed projection. It does
    not certify that these existing summaries completely describe a language,
    justify any downstream pruning, certify native helpers/string formatting,
    or prove Rust allocation, hashing, Drop/unwind, usize overflow, or extraction.
    Existing finite indices must fit Rust usize. List recursion below models
    finite Rust loops; the implementation must retain its explicit worklists.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import OriginalFirstSetProjection.
Import ListNotations.
Set Implicit Arguments.

Module OriginalIdentSummaryProjection.
Module F := OriginalFirstSetProjection.OriginalFirstSetProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.

Definition member name names := existsb (String.eqb name) names.
Definition insert name names := if member name names then names else List.app names [name].
Fixpoint bucket_get {T} name (buckets : list (string * list T)) := match buckets with
| [] => [] | (key,values) :: rest => if String.eqb key name then values else bucket_get name rest end.
Fixpoint bucket_push {T} name value (buckets : list (string * list T)) := match buckets with
| [] => [(name,[value])]
| (key,values) :: rest => if String.eqb key name
    then (key,List.app values [value]) :: rest else (key,values) :: bucket_push name value rest end.

Section Rules.
Context {Rule : Type}.
Definition legacy_items mode (rule : @F.SourceRule Rule) := match mode with
| F.Original => map A.project_legacy (F.source_legacy rule)
| F.Relocated => F.view_legacy (F.project_rule rule) end.
Lemma legacy_items_projection : forall rule,
  legacy_items F.Relocated rule = legacy_items F.Original rule.
Proof. reflexivity. Qed.

Inductive Event :=
| FindDeclaration (name : string) | ReadData (declaration : nat)
| ReadCategory (rule : Rule) | ReadLegacyFirst (rule : Rule) | ReadSyntaxFirst (rule : Rule)
| AtomicCall (rule : Rule) | PatternedCall | FormatPattern
| ClosurePop (name : string) | GroupRule (rule : Rule)
| FrameRule (name : string) (index : nat)
| CountItem (index : nat) | AllowedItem (index : nat) | NonterminalItem (index : nat)
| VisitedInsert (name : string).

Fixpoint user_var mode name rules events : bool * list Event := match rules with
| [] => (false,events)
| rule :: rest =>
    let events := List.app events [ReadCategory (F.payload mode rule)] in
    if String.eqb (F.category mode rule) name then
      let events := List.app events [ReadLegacyFirst (F.payload mode rule)] in
      match F.legacy_head mode rule with
      | Some (A.NonTerminal A.VarKind _) => (true,events)
      | _ => user_var mode name rest events end
    else user_var mode name rest events end.
Lemma user_var_projection : forall rules name events,
  user_var F.Relocated name rules events = user_var F.Original name rules events.
Proof. induction rules; intros; cbn [user_var]; [reflexivity|].
  rewrite F.payload_projection, F.category_projection.
  destruct (String.eqb (F.category F.Original a) name); [rewrite F.legacy_head_projection|];
    try destruct (F.legacy_head F.Original a) as [[text|kind name'|]|];
    try destruct kind; auto. Qed.
Definition home_var mode declarations rules name :=
  let events := [FindDeclaration name] in
  match F.find_category mode name declarations with
  | None => (false,events)
  | Some c => let '(found,events) := user_var mode name rules events in
      if found then (true,events) else
      (negb (F.category_data c),List.app events [ReadData (F.category_payload c)]) end.
Theorem home_variable_source_projection : forall declarations rules name,
  home_var F.Relocated declarations rules name = home_var F.Original declarations rules name.
Proof. intros; unfold home_var; rewrite F.first_declaration_projection.
  destruct (F.find_category F.Original name declarations); [rewrite user_var_projection|]; reflexivity. Qed.

Definition declaration_name mode c := match mode with
| F.Original => F.declaration_name c | F.Relocated => F.category_name (F.project_category c) end.
Definition declaration_data mode c := match mode with
| F.Original => F.declaration_data c | F.Relocated => F.category_data (F.project_category c) end.
Fixpoint seeds mode declarations reached := match declarations with
| [] => reached | c :: rest => seeds mode rest
    (if declaration_data mode c then reached else insert (declaration_name mode c) reached) end.
Lemma seeds_projection : forall declarations reached,
  seeds F.Relocated declarations reached = seeds F.Original declarations reached.
Proof. induction declarations; intros; cbn [seeds declaration_data declaration_name F.project_category
  F.category_data F.category_name]; [reflexivity|apply IHdeclarations]. Qed.

Section Summary.
Context {LiteralPayload Pattern State : Type}.
Definition Callbacks := @F.Callbacks Rule LiteralPayload Pattern State.
Record Summary := {
  reached : list string; reverse : list (string * list string);
  summary_state : State; summary_trace : list Event
}.
Definition summary names edges state events :=
 {| reached := names; reverse := edges; summary_state := state; summary_trace := events |}.
Definition summary_event s e := summary (reached s) (reverse s) (summary_state s)
  (List.app (summary_trace s) [e]).
Definition seed_name s name := summary (insert name (reached s)) (reverse s)
  (summary_state s) (summary_trace s).
Definition add_edge s source target := summary (reached s) (bucket_push source target (reverse s))
  (summary_state s) (summary_trace s).
Fixpoint patterned_has_ident (callbacks : Callbacks) (contains_ident : string -> bool)
  (pairs : list (Pattern * option Pattern)) events := match pairs with
| [] => (false,events)
| (pattern,guard) :: rest => match guard with
  | Some _ => patterned_has_ident callbacks contains_ident rest events
  | None => let events := List.app events [FormatPattern] in
      if contains_ident (F.format callbacks pattern) then (true,events)
      else patterned_has_ident callbacks contains_ident rest events end end.

Definition scan_rule mode (callbacks : Callbacks) contains_ident rule s :=
  let category := F.category mode rule in
  let s := summary_event s (ReadCategory (F.payload mode rule)) in
  let '(shape,state) := F.atomic callbacks (F.payload mode rule) (summary_state s) in
  let s := summary (reached s) (reverse s) state (List.app (summary_trace s) [AtomicCall (F.payload mode rule)]) in
  match shape with
  | A.VarRule _ => seed_name s category
  | A.LiteralPatterned literal =>
      let '(pairs,state) := F.patterned_first callbacks literal (summary_state s) in
      let '(has_ident,events) := patterned_has_ident callbacks contains_ident pairs
        (List.app (summary_trace s) [PatternedCall]) in
      let s := summary (reached s) (reverse s) state events in
      if has_ident then seed_name s category else s
  | A.CrossCatProjection source _ => add_edge s source category
  | A.NonAtomic =>
      let s := summary_event s (ReadSyntaxFirst (F.payload mode rule)) in
      match F.syntax_head mode rule with
      | Some (Some F.Param) =>
          let s := summary_event s (ReadLegacyFirst (F.payload mode rule)) in
          match F.legacy_head mode rule with
          | Some (A.NonTerminal A.CategoryKind source) =>
              if String.eqb source category then s else add_edge s source category
          | _ => s end
      | _ => s end
  | _ => s end.
Lemma scan_rule_projection : forall callbacks contains_ident rule s,
  scan_rule F.Relocated callbacks contains_ident rule s = scan_rule F.Original callbacks contains_ident rule s.
Proof. intros; unfold scan_rule; rewrite !F.category_projection, !F.payload_projection.
  destruct (F.atomic callbacks _ _) as [shape state]; destruct shape; try reflexivity.
  rewrite F.syntax_head_projection, F.legacy_head_projection; reflexivity. Qed.
Fixpoint scan_rules mode callbacks contains_ident rules s := match rules with
| [] => s | rule :: rest => scan_rules mode callbacks contains_ident rest
    (scan_rule mode callbacks contains_ident rule s) end.
Lemma scan_rules_projection : forall rules callbacks contains_ident s,
  scan_rules F.Relocated callbacks contains_ident rules s = scan_rules F.Original callbacks contains_ident rules s.
Proof. induction rules; intros; cbn [scan_rules]; [reflexivity|].
  rewrite scan_rule_projection, IHrules; reflexivity. Qed.

Record ClosureProgress := { closure_summary : Summary; pending : list string }.
Definition closure_progress s queue := {| closure_summary := s; pending := queue |}.
Fixpoint visit_targets targets p := match targets with
| [] => p | target :: rest =>
    let s := closure_summary p in
    visit_targets rest (if member target (reached s) then p else
      closure_progress (seed_name s target) (List.app (pending p) [target])) end.
Inductive ClosureOutcome := ClosureDone (p : ClosureProgress) | ClosureStopped (p : ClosureProgress).
Fixpoint close fuel p := match pending p with
| [] => ClosureDone p | source :: rest => match fuel with
  | 0 => ClosureStopped p
  | S fuel => let s := summary_event (closure_summary p) (ClosurePop source) in
      close fuel (visit_targets (bucket_get source (reverse s)) (closure_progress s rest)) end end.
Definition summarize mode fuel callbacks contains_ident enumerate declarations rules state :=
  let s := scan_rules mode callbacks contains_ident rules
    (summary (seeds mode declarations []) [] state []) in
  close fuel (closure_progress s (enumerate (reached s))).
Theorem identifier_closure_source_projection : forall fuel callbacks contains_ident enumerate declarations rules state,
  summarize F.Relocated fuel callbacks contains_ident enumerate declarations rules state =
  summarize F.Original fuel callbacks contains_ident enumerate declarations rules state.
Proof. intros; unfold summarize; rewrite seeds_projection, scan_rules_projection; reflexivity. Qed.

(** The exact THREE purity passes, with visited indices in source order. *)
Definition is_terminal item := match item with A.Terminal _ => true | _ => false end.
Definition allowed item := match item with A.Terminal _ | A.NonTerminal A.CategoryKind _ => true | _ => false end.
Fixpoint all_items (predicate : A.LegacyItem -> bool) (items : list A.LegacyItem)
  (index : nat) (make_event : nat -> Event) : bool * list Event := match items with
| [] => (true,[])
| item :: rest => if predicate item then
    let '(ok,events) := all_items predicate rest (S index) make_event in
    (ok,make_event index :: events)
  else (false,[make_event index]) end.
Definition purity mode rule :=
  let items := legacy_items mode rule in
  let events := map CountItem (seq 0 (List.length items)) in
  if Nat.eqb (List.length (filter (fun item => negb (is_terminal item)) items)) 1 then
    let '(ok,second) := all_items allowed items 0 AllowedItem in
    if ok then let '(ok,third) := all_items (fun item => negb (is_terminal item)) items 0 NonterminalItem in
      (ok,List.app events (List.app second third))
    else (false,List.app events second)
  else (false,events).
Lemma purity_projection : forall rule, purity F.Relocated rule = purity F.Original rule.
Proof. intros; unfold purity; rewrite legacy_items_projection; reflexivity. Qed.

Fixpoint group_rules mode rules buckets events := match rules with
| [] => (buckets,events)
| rule :: rest => group_rules mode rest (bucket_push (F.category mode rule) rule buckets)
    (List.app events [GroupRule (F.payload mode rule)]) end.
Lemma group_rules_projection : forall rules buckets events,
  group_rules F.Relocated rules buckets events = group_rules F.Original rules buckets events.
Proof. induction rules; intros; cbn [group_rules]; [reflexivity|].
  rewrite F.category_projection, F.payload_projection; apply IHrules. Qed.
Record Frame := { frame_category : string; next_rule : nat }.
Record Frames := { stack : list Frame; visited : list string; frame_trace : list Event }.
Definition frames todo seen events := {| stack := todo; visited := seen; frame_trace := events |}.
Definition frame_event p e := frames (stack p) (visited p) (List.app (frame_trace p) [e]).
Inductive FrameStep := Continue (p : Frames) | Reject (p : Frames).

Definition examine mode name rule ident_first p :=
  let p := frame_event p (ReadLegacyFirst (F.payload mode rule)) in
  match F.legacy_head mode rule with
  | Some (A.NonTerminal A.VarKind _) => Continue p
  | _ => let p := frame_event p (ReadLegacyFirst (F.payload mode rule)) in
      match F.legacy_head mode rule with
      | Some (A.Terminal _) | Some (A.NonTerminal A.VarKind _) => Continue p
      | Some (A.NonTerminal A.CategoryKind target) =>
          if String.eqb target name then Continue p else
          let '(pure,events) := purity mode rule in
          let p := frames (stack p) (visited p) (List.app (frame_trace p) events) in
          if member target ident_first then
            if pure then
              let p := frame_event p (VisitedInsert target) in
              if member target (visited p) then Continue p else
              Continue (frames ({| frame_category := target; next_rule := 0 |} :: stack p)
                (insert target (visited p)) (frame_trace p))
            else Reject p
          else Continue p
      | _ => let p := frame_event p (ReadSyntaxFirst (F.payload mode rule)) in
          match F.syntax_head mode rule with
          | Some (Some (F.Literal _)) => Continue p | _ => Reject p end end end.
Lemma examine_projection : forall name rule ident_first p,
  examine F.Relocated name rule ident_first p = examine F.Original name rule ident_first p.
Proof. intros; unfold examine; rewrite !F.payload_projection, !F.legacy_head_projection,
  purity_projection, F.syntax_head_projection; reflexivity. Qed.

Inductive FramesOutcome := AllVarOnly (p : Frames) | NotVarOnly (p : Frames) | FramesStopped (p : Frames).
Fixpoint walk_frames mode fuel buckets ident_first p := match stack p with
| [] => AllVarOnly p
| frame :: rest => match fuel with
  | 0 => FramesStopped p
  | S fuel => match nth_error (bucket_get (frame_category frame) buckets) (next_rule frame) with
    | None => walk_frames mode fuel buckets ident_first (frames rest (visited p) (frame_trace p))
    | Some rule =>
        let advanced := {| frame_category := frame_category frame; next_rule := S (next_rule frame) |} in
        let p := frames (advanced :: rest) (visited p)
          (List.app (frame_trace p) [FrameRule (frame_category frame) (next_rule frame)]) in
        match examine mode (frame_category frame) rule ident_first p with
        | Reject p => NotVarOnly p | Continue p => walk_frames mode fuel buckets ident_first p end end end end.
Theorem finite_frame_source_projection : forall fuel buckets ident_first p,
  walk_frames F.Relocated fuel buckets ident_first p = walk_frames F.Original fuel buckets ident_first p.
Proof. induction fuel; intros; cbn [walk_frames]; destruct (stack p) as [|frame rest]; try reflexivity.
  destruct (nth_error (bucket_get (frame_category frame) buckets) (next_rule frame)) as [rule|];
    [rewrite examine_projection; destruct (examine F.Original _ _ _ _); [apply IHfuel|reflexivity]|apply IHfuel]. Qed.

Inductive VarOnlyOutcome :=
| SummaryInterrupted (p : ClosureProgress)
| VarOnlyResult (s : Summary) (result : FramesOutcome).
Definition var_only mode closure_fuel frame_fuel callbacks contains_ident enumerate declarations rules source state :=
  match summarize mode closure_fuel callbacks contains_ident enumerate declarations rules state with
  | ClosureStopped p => SummaryInterrupted p
  | ClosureDone p =>
      let s := closure_summary p in
      let '(buckets,events) := group_rules mode rules [] (summary_trace s) in
      VarOnlyResult s (walk_frames mode frame_fuel buckets (reached s)
        (frames [{| frame_category := source; next_rule := 0 |}] [source] events)) end.
Theorem complete_finite_source_substitution : forall closure_fuel frame_fuel callbacks contains_ident enumerate declarations rules source state,
  var_only F.Relocated closure_fuel frame_fuel callbacks contains_ident enumerate declarations rules source state =
  var_only F.Original closure_fuel frame_fuel callbacks contains_ident enumerate declarations rules source state.
Proof. intros; unfold var_only; rewrite identifier_closure_source_projection.
  destruct (summarize F.Original _ _ _ _ _ _ _) as [p|p]; [|reflexivity].
  rewrite group_rules_projection.
  destruct (group_rules F.Original _ _ _) as [buckets events].
  rewrite finite_frame_source_projection; reflexivity. Qed.
Theorem closure_exhaustion_is_not_a_boolean : forall callbacks contains_ident enumerate declarations rules source state frame_fuel p,
  summarize F.Original 0 callbacks contains_ident enumerate declarations rules state = ClosureStopped p ->
  var_only F.Original 0 frame_fuel callbacks contains_ident enumerate declarations rules source state = SummaryInterrupted p.
Proof. intros; unfold var_only; rewrite H; reflexivity. Qed.
Theorem frame_exhaustion_preserves_cursor : forall mode buckets ident_first p frame rest,
  stack p = frame :: rest -> walk_frames mode 0 buckets ident_first p = FramesStopped p.
Proof. intros; cbn [walk_frames]; rewrite H; reflexivity. Qed.
End Summary.
End Rules.

Print Assumptions legacy_items_projection.
Print Assumptions user_var_projection.
Print Assumptions home_variable_source_projection.
Print Assumptions seeds_projection.
Print Assumptions scan_rule_projection.
Print Assumptions scan_rules_projection.
Print Assumptions identifier_closure_source_projection.
Print Assumptions purity_projection.
Print Assumptions group_rules_projection.
Print Assumptions examine_projection.
Print Assumptions finite_frame_source_projection.
Print Assumptions complete_finite_source_substitution.
Print Assumptions closure_exhaustion_is_not_a_boolean.
Print Assumptions frame_exhaustion_preserves_cursor.
End OriginalIdentSummaryProjection.
