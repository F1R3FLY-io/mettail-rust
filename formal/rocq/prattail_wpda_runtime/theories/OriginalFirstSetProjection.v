(** Source-observation refinement for the ORIGINAL prefix.rs FIRST traversal.

    This is an extraction proof, not a new FIRST algorithm or a proof that the
    existing FIRST approximation is complete. The source loop is represented
    once; Original reads source fields and Relocated reads their independently
    defined borrowed projections. Correspondence is proved at each observation,
    then composed through the unchanged loop and helper calls.

    Exact source ledger (prefix.rs::category_leading_literals, first_set_of_category,
    collect_first_set): FIFO queue, visited-on-pop before all observations; three
    separate first-declaration lookups (native, variable, collection); native
    pairs then synthetic Var then declared collection opener then authored rules.
    The native callback owns the ORIGINAL native-presence/family/kind/FirstSet
    helper block, including its internal lookups. No native taxonomy is invented.
    The collection callback is Rust trim_end_matches('('), removing ALL trailing
    opening parentheses; its exact string operation is imported unchanged.

    User-Var detection short-circuits on ANY first legacy Var item in a matching
    rule, not just a classified VarRule. Atomic classification is called once per
    matching rule. Its existing Descriptor is imported unchanged. NonAtomic only
    looks at present first syntax: literal, parameter, token kind, guest opener.
    Only the parameter case calls binder; only a missing binder leading category
    reads legacy Category fallback. This branch excludes self-edges; classified
    projections enqueue self-edges and visited cuts them later. Undeclared names
    still scan rules. Leading-literal collection uses legacy fallback ONLY for
    absent syntax, never present-empty or present-nonliteral syntax.

    Pattern payloads are opaque. The eight predicate requests represent the
    original quotation cases, NOT semantic token equivalence. Stable dedup uses
    precisely (pattern.to_string, guard.to_string or empty), keeping the first
    COMPLETE row, including guard Option, leading literal and variable flag.
    Source/shared use the same formatter and helper callbacks. Typed runtime
    predicates still require a backend correspondence; no Rust-token reparsing.

    Trace covers outer lookups, short-circuit rule observations, helper calls,
    queue pops, quotation construction, and formatting. Callback state is retained
    exactly. Fuel instruments category pops only and returns the full unfinished
    state, never a successful empty result. Inner list recursion models the
    existing finite Rust iteration, not an implementation using recursion.
    Imported helper internals, Rust allocation/Drop/unwind, arbitrary callback
    lawfulness, unbounded termination, parser soundness/completeness and runtime
    cutover are outside this projection theorem. Source identifiers below are
    their existing spelling observations; no identifier-equality law is inferred.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import AtomicClassifierProjection.
Import ListNotations.
Set Implicit Arguments.

Module OriginalFirstSetProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.
Module I := InfixClassifierProjection.InfixClassifierProjection.

Inductive Mode := Original | Relocated.
Inductive SourceSyntax :=
| SourceLiteral (text : string) | SourceParam (name : string)
| SourceToken (name capture : string) | SourceGuest (open close : string)
| SourceOther (opaque : nat).
Inductive SyntaxHead :=
| Literal (text : string) | Param | Token (name : string)
| Guest (open : string) | Other.
Definition project_syntax syntax := match syntax with
| SourceLiteral text => Literal text | SourceParam _ => Param
| SourceToken name _ => Token name | SourceGuest open _ => Guest open
| SourceOther _ => Other end.

Section Rules.
Context {Rule : Type}.
Record SourceRule := {
  source_payload : Rule; source_category : string;
  source_syntax : option (list SourceSyntax);
  source_legacy : list A.SourceLegacy
}.
Record RuleView := {
  view_payload : Rule; view_category : string;
  view_syntax : option (list SyntaxHead); view_legacy : list A.LegacyItem
}.
Definition project_rule rule :=
 {| view_payload := source_payload rule; view_category := source_category rule;
    view_syntax := option_map (map project_syntax) (source_syntax rule);
    view_legacy := map A.project_legacy (source_legacy rule) |}.
Definition syntax_head mode rule : option (option SyntaxHead) := match mode with
| Original => option_map (fun syntax => option_map project_syntax (hd_error syntax)) (source_syntax rule)
| Relocated => option_map (@hd_error SyntaxHead) (view_syntax (project_rule rule)) end.
Definition legacy_head mode rule := match mode with
| Original => option_map A.project_legacy (hd_error (source_legacy rule))
| Relocated => hd_error (view_legacy (project_rule rule)) end.
Definition category mode rule := match mode with
| Original => source_category rule | Relocated => view_category (project_rule rule) end.
Definition payload mode rule := match mode with
| Original => source_payload rule | Relocated => view_payload (project_rule rule) end.

Lemma syntax_head_projection : forall rule,
  syntax_head Relocated rule = syntax_head Original rule.
Proof. intros [r c [syntax|] legacy]; cbn; [destruct syntax|]; reflexivity. Qed.
Lemma legacy_head_projection : forall rule,
  legacy_head Relocated rule = legacy_head Original rule.
Proof. intros [r c syntax [|item rest]]; reflexivity. Qed.
Lemma category_projection : forall rule, category Relocated rule = category Original rule.
Proof. reflexivity. Qed.
Lemma payload_projection : forall rule, payload Relocated rule = payload Original rule.
Proof. reflexivity. Qed.
End Rules.

Record SourceCategory := {
  declaration_name : string; declaration_payload : nat;
  declaration_data : bool; declaration_open : option string
}.
Record CategoryView := {
  category_name : string; category_payload : nat;
  category_data : bool; category_open : option string
}.
Definition project_category c :=
 {| category_name := declaration_name c; category_payload := declaration_payload c;
    category_data := declaration_data c; category_open := declaration_open c |}.
Fixpoint source_find name declarations := match declarations with
| [] => None | c :: rest => if String.eqb (declaration_name c) name
    then Some (project_category c) else source_find name rest end.
Fixpoint view_find name declarations := match declarations with
| [] => None | c :: rest => if String.eqb (category_name c) name
    then Some c else view_find name rest end.
Definition find_category mode name declarations := match mode with
| Original => source_find name declarations
| Relocated => view_find name (map project_category declarations) end.
Lemma first_declaration_projection : forall declarations name,
  find_category Relocated name declarations = find_category Original name declarations.
Proof. induction declarations as [|c rest IH]; intros name; unfold find_category in *;
  cbn [map view_find source_find project_category category_name]; [reflexivity|].
  destruct (String.eqb (declaration_name c) name); [reflexivity|apply IH]. Qed.

Inductive Predicate :=
| Fixed (text : string) | Ident | Integer | Boolean | StringToken | Float
| CaptureName (name : string) | GuestOpen (name : string).
Inductive LookupPurpose := NativeSeed | VariableSeed | CollectionSeed.

Section Traversal.
Context {Rule LiteralPayload Pattern State : Type}.
Record FirstToken := {
  pattern : Pattern; guard : option Pattern;
  leading_literal : option string; variable_contribution : bool
}.
Record Callbacks := {
  native_first : nat -> string -> State -> list (Pattern * option Pattern) * State;
  atomic : Rule -> State -> @A.Descriptor LiteralPayload * State;
  patterned_first : LiteralPayload -> State -> list (Pattern * option Pattern) * State;
  binder_leading : Rule -> State -> option string * State;
  predicate_parts : Predicate -> State -> (Pattern * option Pattern) * State;
  trim_open : string -> string;
  format : Pattern -> string
}.
Inductive Event :=
| Pop (name : string) | Lookup (purpose : LookupPurpose) (name : string)
| RuleCategory (rule : Rule) | LegacyFirst (rule : Rule) | SyntaxFirst (rule : Rule)
| NativeCall (declaration : nat) (name : string) | AtomicCall (rule : Rule)
| PatternedCall | BinderCall (rule : Rule) | QuoteCall (predicate : Predicate)
| FormatPattern | FormatGuard.
Record Progress := {
  pending : list string; visited : list string; rows : list FirstToken;
  callback_state : State; trace : list Event
}.
Definition progress queue seen out state events :=
 {| pending := queue; visited := seen; rows := out; callback_state := state; trace := events |}.
Definition event p e := progress (pending p) (visited p) (rows p)
  (callback_state p) (trace p ++ [e]).
Definition after_callback p state e := progress (pending p) (visited p) (rows p)
  state (trace p ++ [e]).
Definition append_rows p out := progress (pending p) (visited p) (rows p ++ out)
  (callback_state p) (trace p).
Definition enqueue p name := progress (pending p ++ [name]) (visited p) (rows p)
  (callback_state p) (trace p).
Definition literal_rows pairs := map (fun pair =>
 {| pattern := fst pair; guard := snd pair; leading_literal := None;
    variable_contribution := false |}) pairs.
Definition emit callbacks p predicate :=
  let '(parts,state) := predicate_parts callbacks predicate (callback_state p) in
  append_rows (after_callback p state (QuoteCall predicate))
   [{| pattern := fst parts; guard := snd parts;
       leading_literal := match predicate with Fixed text => Some text | _ => None end;
       variable_contribution := match predicate with Ident => true | _ => false end |}].

Fixpoint has_user_var mode name rules p : bool * Progress := match rules with
| [] => (false,p)
| rule :: rest =>
    let observed := event p (RuleCategory (payload mode rule)) in
    if String.eqb (category mode rule) name then
      let observed := event observed (LegacyFirst (payload mode rule)) in
      match legacy_head mode rule with
      | Some (A.NonTerminal A.VarKind _) => (true,observed)
      | _ => has_user_var mode name rest observed end
    else has_user_var mode name rest observed end.
Lemma user_var_projection : forall rules name p,
  has_user_var Relocated name rules p = has_user_var Original name rules p.
Proof. induction rules; intros; cbn [has_user_var]; [reflexivity|].
  rewrite payload_projection, category_projection.
  destruct (String.eqb (category Original a) name); [rewrite legacy_head_projection|];
    try destruct (legacy_head Original a) as [[text|kind name'|]|];
    try destruct kind; auto. Qed.

Definition seed mode callbacks declarations rules name p :=
  let p := event p (Lookup NativeSeed name) in
  let p := match find_category mode name declarations with
  | None => p | Some c =>
      let '(pairs,state) := native_first callbacks (category_payload c) name (callback_state p) in
      append_rows (after_callback p state (NativeCall (category_payload c) name)) (literal_rows pairs) end in
  let p := event p (Lookup VariableSeed name) in
  let p := match find_category mode name declarations with
  | Some c => if category_data c then p else
      let '(present,p) := has_user_var mode name rules p in
      if present then p else emit callbacks p Ident
  | None => p end in
  let p := event p (Lookup CollectionSeed name) in
  match find_category mode name declarations with
  | Some c => match category_open c with
      | Some open => emit callbacks p (Fixed (trim_open callbacks open)) | None => p end
  | None => p end.
Lemma seed_projection : forall callbacks declarations rules name p,
  seed Relocated callbacks declarations rules name p = seed Original callbacks declarations rules name p.
Proof. intros; unfold seed; rewrite !first_declaration_projection.
  destruct (find_category Original name declarations) as [c|]; [|reflexivity].
  destruct (native_first callbacks (category_payload c) name _) as [pairs state].
  destruct (category_data c); [reflexivity|]. rewrite user_var_projection; reflexivity. Qed.

Definition non_atomic mode callbacks name rule p :=
  let p := event p (SyntaxFirst (payload mode rule)) in
  match syntax_head mode rule with
  | Some (Some (Literal text)) => emit callbacks p (Fixed text)
  | Some (Some Param) =>
      let '(leading,state) := binder_leading callbacks (payload mode rule) (callback_state p) in
      let p := after_callback p state (BinderCall (payload mode rule)) in
      let '(leading,p) := match leading with
      | Some source => (Some source,p)
      | None => (match legacy_head mode rule with
          | Some (A.NonTerminal A.CategoryKind source) => Some source | _ => None end,
          event p (LegacyFirst (payload mode rule))) end in
      match leading with Some source => if String.eqb source name then p else enqueue p source
      | None => p end
  | Some (Some (Token name)) => emit callbacks p (CaptureName name)
  | Some (Some (Guest name)) => emit callbacks p (GuestOpen name)
  | _ => p end.
Lemma non_atomic_projection : forall callbacks name rule p,
  non_atomic Relocated callbacks name rule p = non_atomic Original callbacks name rule p.
Proof. intros; unfold non_atomic; rewrite !payload_projection, syntax_head_projection,
  legacy_head_projection; reflexivity. Qed.

Definition rule_step mode callbacks name rule p :=
  let p := event p (RuleCategory (payload mode rule)) in
  if String.eqb (category mode rule) name then
    let '(shape,state) := atomic callbacks (payload mode rule) (callback_state p) in
    let p := after_callback p state (AtomicCall (payload mode rule)) in
    match shape with
    | A.LiteralPatterned literal =>
        let '(pairs,state) := patterned_first callbacks literal (callback_state p) in
        append_rows (after_callback p state PatternedCall) (literal_rows pairs)
    | A.TerminalKeyword text _ => emit callbacks p (Fixed text)
    | A.VarRule _ => emit callbacks p Ident
    | A.LiteralInteger => emit callbacks p Integer
    | A.LiteralBoolean => emit callbacks p Boolean
    | A.LiteralString => emit callbacks p StringToken
    | A.LiteralFloat => emit callbacks p Float
    | A.CrossCatProjection source _ => enqueue p source
    | A.CrossCatPrefixUnary trigger _ _ | A.PrefixOperator trigger _
    | A.NullaryLiteralRun trigger _ _ => emit callbacks p (Fixed trigger)
    | A.NonAtomic => non_atomic mode callbacks name rule p end
  else p.
Lemma rule_step_projection : forall callbacks name rule p,
  rule_step Relocated callbacks name rule p = rule_step Original callbacks name rule p.
Proof. intros; unfold rule_step; rewrite !payload_projection, category_projection.
  destruct (String.eqb (category Original rule) name); [|reflexivity].
  destruct (atomic callbacks _ _) as [shape state]; destruct shape;
    try reflexivity; apply non_atomic_projection. Qed.
Fixpoint rule_scan mode callbacks name rules p := match rules with
| [] => p | rule :: rest => rule_scan mode callbacks name rest (rule_step mode callbacks name rule p) end.
Lemma rule_scan_projection : forall rules callbacks name p,
  rule_scan Relocated callbacks name rules p = rule_scan Original callbacks name rules p.
Proof. induction rules; intros; cbn [rule_scan]; [reflexivity|].
  rewrite rule_step_projection, IHrules; reflexivity. Qed.

Inductive Outcome := Complete (p : Progress) | Stopped (p : Progress).
Fixpoint run mode fuel callbacks declarations rules p :=
  match pending p with
  | [] => Complete p
  | name :: rest => match fuel with
    | 0 => Stopped p
    | S fuel =>
        let popped := progress rest (visited p) (rows p) (callback_state p) (trace p ++ [Pop name]) in
        if existsb (String.eqb name) (visited p) then run mode fuel callbacks declarations rules popped
        else let fresh := progress rest (visited p ++ [name]) (rows p) (callback_state p) (trace popped) in
          run mode fuel callbacks declarations rules
            (rule_scan mode callbacks name rules (seed mode callbacks declarations rules name fresh))
    end end.
Theorem finite_first_traversal_projection : forall fuel callbacks declarations rules p,
  run Relocated fuel callbacks declarations rules p = run Original fuel callbacks declarations rules p.
Proof. induction fuel; intros; cbn [run]; destruct (pending p) as [|name rest];
  try reflexivity. destruct (existsb (String.eqb name) (visited p));
  [apply IHfuel|]. rewrite seed_projection, rule_scan_projection; apply IHfuel. Qed.
Theorem exhausted_pending_is_not_success : forall callbacks declarations rules p name rest,
  pending p = name :: rest -> run Original 0 callbacks declarations rules p = Stopped p.
Proof. intros; cbn [run]; rewrite H; reflexivity. Qed.

Definition row_key callbacks row :=
 (format callbacks (pattern row), match guard row with Some g => format callbacks g | None => EmptyString end).
Definition key_eqb a b := String.eqb (fst a) (fst b) && String.eqb (snd a) (snd b).
Fixpoint retain_first callbacks seen input : list FirstToken := match input with
| [] => [] | row :: rest => let key := row_key callbacks row in
    if existsb (key_eqb key) seen then retain_first callbacks seen rest
    else row :: retain_first callbacks (seen ++ [key])%list rest end.
Definition finish callbacks outcome := match outcome with
| Stopped p => Stopped p
| Complete p => Complete (progress (pending p) (visited p) (retain_first callbacks [] (rows p))
    (callback_state p) (trace p ++ flat_map (fun row =>
      FormatPattern :: match guard row with Some _ => [FormatGuard] | None => [] end) (rows p))) end.
Theorem finite_first_entry_projection : forall fuel callbacks declarations rules p,
  finish callbacks (run Relocated fuel callbacks declarations rules p) =
  finish callbacks (run Original fuel callbacks declarations rules p).
Proof. intros; rewrite finite_first_traversal_projection; reflexivity. Qed.
Theorem duplicate_formatter_key_keeps_first_complete_payload : forall callbacks first second,
  row_key callbacks first = row_key callbacks second ->
  retain_first callbacks [] [first;second] = [first].
Proof. intros; cbn [retain_first]; rewrite <- H.
  unfold key_eqb; cbn [List.app existsb]; rewrite !String.eqb_refl; reflexivity. Qed.
Theorem stopped_output_is_not_deduplicated_or_published : forall callbacks p,
  finish callbacks (Stopped p) = Stopped p.
Proof. reflexivity. Qed.

(** Direct leading literals use a sorted set in Rust. The projection theorem
    compares the exact insertion trace; applying the same BTreeSet constructor
    consequently preserves its sorted unique result without changing policy. *)
Definition direct_leading_literal mode (rule : @SourceRule Rule) := match syntax_head mode rule with
| Some (Some (Literal text)) => Some text | Some _ => None
| None => match legacy_head mode rule with Some (A.Terminal text) => Some text | _ => None end end.
Lemma leading_literal_projection : forall rule,
  direct_leading_literal Relocated rule = direct_leading_literal Original rule.
Proof. intros; unfold direct_leading_literal; rewrite syntax_head_projection, legacy_head_projection; reflexivity. Qed.
Fixpoint leading_insertions mode name rules : list string := match rules with
| [] => [] | rule :: rest =>
    ((if String.eqb (category mode rule) name then
       match direct_leading_literal mode rule with Some text => [text] | None => [] end
     else []) ++ leading_insertions mode name rest)%list end.
Theorem category_leading_literal_insertions_projection : forall rules name,
  leading_insertions Relocated name rules = leading_insertions Original name rules.
Proof. induction rules; intros; cbn [leading_insertions]; [reflexivity|].
  rewrite category_projection, leading_literal_projection, IHrules; reflexivity. Qed.
End Traversal.

(** The actual atomic callback boundary already has a source/view proof. This
    theorem composes its full result/state/trace unchanged, not a guessed shape.
    FIRST does not prove the native-kind or binder helper internals afresh. *)
Theorem existing_atomic_classifier_callback_reused : forall L S rule items
  (unary : S -> option A.Unary * S) (literal : string -> S -> option L * S) state,
  A.view_atomic (I.project_rule rule) (map A.project_legacy items) unary literal state =
  A.source_atomic rule items unary literal state.
Proof. intros; apply A.complete_atomic_projection_and_callback_observation. Qed.

Print Assumptions syntax_head_projection.
Print Assumptions legacy_head_projection.
Print Assumptions first_declaration_projection.
Print Assumptions user_var_projection.
Print Assumptions seed_projection.
Print Assumptions non_atomic_projection.
Print Assumptions rule_step_projection.
Print Assumptions rule_scan_projection.
Print Assumptions finite_first_traversal_projection.
Print Assumptions finite_first_entry_projection.
Print Assumptions exhausted_pending_is_not_success.
Print Assumptions duplicate_formatter_key_keeps_first_complete_payload.
Print Assumptions stopped_output_is_not_deduplicated_or_published.
Print Assumptions category_leading_literal_insertions_projection.
Print Assumptions existing_atomic_classifier_callback_reused.
End OriginalFirstSetProjection.
