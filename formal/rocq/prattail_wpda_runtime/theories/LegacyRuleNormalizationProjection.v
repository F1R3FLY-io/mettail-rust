(** Original legacy-rule normalization, with a borrowed item reader and exact
    constructor adapter (task 8512). Source: ast/src/grammar.rs, function
    convert_items_to_term_context, read in full before this transcription.

    The original algorithm is retained: separate short-circuit presence gates;
    complete non-Category preflight; one forward construction loop; trailing
    binder and empty-parameter refusals; finally commit ONLY tc and sp. Both
    scans read the original item slice, preserving every occurrence. Bindings,
    original items, label/category, and opaque remaining metadata are untouched.
    Refused local prefixes are proof observations, never published rule fields.

    Source and shared item types, step definitions, scans and construction loops
    below are separate. The shared path substitutes a shallow reader and a
    constructor adapter; induction proves exact payload and operation traces.
    No normalization algorithm is assumed as an uninterpreted oracle.

    Original identifiers retain text and span identity. Generated PName n denotes
    exactly Ident::new(format!("p{}", n), Span::call_site()); ElemsName denotes
    Ident::new("elems", Span::call_site()). This is an indexed representation of
    the original formatter's result, not a new formatter or source reparse.
    CollectionKind reuses SyntheticRuleProjection's complete five-kind enum.
    Its string-only parameter model cannot express original span identity, so
    the full identifier-bearing output constructors are explicit here.

    Constructor events instrument adapter sites and exact payloads, not
    allocations or clone calls. Constructors here are infallible lawful original
    constructors; arbitrary fallible/dynamic implementations are not certified.
    Naturals model usize only on executions whose increments fit usize. The
    increment lemmas expose the one/two increment domain; overflow, allocation,
    Rust extraction, borrow checking and downstream parser behavior are outside
    this theorem. Finite input lists terminate in this model; no arbitrary
    callback/store termination or dynamic-grammar admission is claimed.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import SyntheticRuleProjection.
Import ListNotations.
Set Implicit Arguments.

Module LegacyRuleNormalizationProjection.
Module S := SyntheticRuleProjection.SyntheticRuleProjection.

Record OriginalIdent := { ident_text : string; ident_span : nat }.
Inductive Name := OriginalName (ident : OriginalIdent) | PName (index : nat) | ElemsName.
Inductive TypeExpr :=
| Base (ident : OriginalIdent)
| Arrow (domain codomain : TypeExpr)
| Collection (kind : S.CollectionKind) (element : TypeExpr).
Inductive Param := Simple (name : Name) (ty : TypeExpr)
| Abstraction (binder body : Name) (ty : TypeExpr).
Inductive Syntax := Literal (text : string) | ParamRef (name : Name)
| Sep (collection : Name) (separator : string) (source : option nat).

Inductive SourceItem :=
| STerminal (text : string)
| SCategory (ident : OriginalIdent)
| SOtherNonTerminal (ident : OriginalIdent) (kind : nat)
| SBinder (category : OriginalIdent)
| SCollection (kind : S.CollectionKind) (element : OriginalIdent)
    (separator : string) (delimiters : option (string * string)).
Inductive ItemView :=
| VTerminal (text : string)
| VCategory (ident : OriginalIdent)
| VOtherNonTerminal (ident : OriginalIdent) (kind : nat)
| VBinder (category : OriginalIdent)
| VCollection (kind : S.CollectionKind) (element : OriginalIdent)
    (separator : string) (delimiters : option (string * string)).
Definition project_item item := match item with
| STerminal text => VTerminal text
| SCategory ident => VCategory ident
| SOtherNonTerminal ident kind => VOtherNonTerminal ident kind
| SBinder category => VBinder category
| SCollection kind element separator delimiters => VCollection kind element separator delimiters end.

Record Constructors := {
  fresh_name : nat -> Name; elems_name : Name;
  make_simple : Name -> OriginalIdent -> Param;
  make_abstraction : Name -> Name -> OriginalIdent -> OriginalIdent -> Param;
  make_collection : Name -> S.CollectionKind -> OriginalIdent -> Param;
  make_literal : string -> Syntax; make_param : Name -> Syntax;
  make_sep : Name -> string -> Syntax
}.
Definition original_constructors :=
 {| fresh_name := PName; elems_name := ElemsName;
    make_simple := fun name ident => Simple name (Base ident);
    make_abstraction := fun binder body domain codomain =>
      Abstraction binder body (Arrow (Base domain) (Base codomain));
    make_collection := fun name kind element => Simple name (Collection kind (Base element));
    make_literal := Literal; make_param := ParamRef;
    make_sep := fun name separator => Sep name separator None |}.

Inductive Operation :=
| HasTermContext | HasSyntaxPattern
| InspectPreflight (handle : nat) | InspectBuild (handle : nat)
| Fresh (index : nat) | FixedElems
| ConstructSimple (name : Name) (ident : OriginalIdent)
| ConstructAbstraction (binder body : Name) (domain codomain : OriginalIdent)
| ConstructCollection (name : Name) (kind : S.CollectionKind) (element : OriginalIdent)
| ConstructLiteral (text : string) | ConstructParam (name : Name)
| ConstructSep (name : Name) (separator : string)
| CommitTermContext | CommitSyntaxPattern.
Inductive Refusal := AlreadyTermContext | AlreadySyntaxPattern | NonCategoryPreflight
| NonCategoryBuild | MissingDelimiters | TrailingBinder | NoParameters.

Record Buffer := {
  params : list Param; syntax : list Syntax; next_param : nat;
  pending : option OriginalIdent; operations : list Operation
}.
Definition buffer tc sp next binder trace :=
 {| params := tc; syntax := sp; next_param := next; pending := binder; operations := trace |}.
Inductive Step := Continue (state : Buffer) | Refuse (reason : Refusal) (state : Buffer).

(** Direct original field/constructor transcription. No shared adapter used. *)
Definition source_step item b :=
  let tc := params b in let sp := syntax b in let n := next_param b in
  let bind := pending b in let trace := operations b in
  match item with
  | STerminal text => Continue (buffer tc (sp ++ [Literal text])%list n bind
      (trace ++ [ConstructLiteral text])%list)
  | SCategory ident => match bind with
    | None => Continue (buffer (tc ++ [Simple (PName n) (Base ident)])%list
        (sp ++ [ParamRef (PName n)])%list (S n) None
        (trace ++ [Fresh n; ConstructSimple (PName n) ident; ConstructParam (PName n)])%list)
    | Some domain => Continue (buffer
        (tc ++ [Abstraction (PName n) (PName (S n)) (Arrow (Base domain) (Base ident))])%list
        (sp ++ [ParamRef (PName n); ParamRef (PName (S n))])%list (S (S n)) None
        (trace ++ [Fresh n; Fresh (S n); ConstructAbstraction (PName n) (PName (S n)) domain ident;
          ConstructParam (PName n); ConstructParam (PName (S n))])%list)
    end
  | SOtherNonTerminal _ _ => Refuse NonCategoryBuild b
  | SBinder category => Continue (buffer tc sp n (Some category) trace)
  | SCollection kind element separator delimiters => match delimiters with
    | None => Refuse MissingDelimiters b
    | Some (open, close) => Continue (buffer
        (tc ++ [Simple ElemsName (Collection kind (Base element))])%list
        (sp ++ [Literal open; Sep ElemsName separator None; Literal close])%list n bind
        (trace ++ [FixedElems; ConstructCollection ElemsName kind element;
          ConstructLiteral open; ConstructSep ElemsName separator; ConstructLiteral close])%list)
    end end.

Definition shared_step c item b :=
  let tc := params b in let sp := syntax b in let n := next_param b in
  let bind := pending b in let trace := operations b in
  match item with
  | VTerminal text => Continue (buffer tc (sp ++ [make_literal c text])%list n bind
      (trace ++ [ConstructLiteral text])%list)
  | VCategory ident =>
    let pname := fresh_name c n in
    match bind with
    | None => Continue (buffer (tc ++ [make_simple c pname ident])%list
        (sp ++ [make_param c pname])%list (S n) None
        (trace ++ [Fresh n; ConstructSimple pname ident; ConstructParam pname])%list)
    | Some domain =>
        let body := fresh_name c (S n) in
        Continue (buffer (tc ++ [make_abstraction c pname body domain ident])%list
          (sp ++ [make_param c pname; make_param c body])%list (S (S n)) None
          (trace ++ [Fresh n; Fresh (S n); ConstructAbstraction pname body domain ident;
            ConstructParam pname; ConstructParam body])%list)
    end
  | VOtherNonTerminal _ _ => Refuse NonCategoryBuild b
  | VBinder category => Continue (buffer tc sp n (Some category) trace)
  | VCollection kind element separator delimiters => match delimiters with
    | None => Refuse MissingDelimiters b
    | Some (open, close) =>
        let name := elems_name c in
        Continue (buffer (tc ++ [make_collection c name kind element])%list
          (sp ++ [make_literal c open; make_sep c name separator; make_literal c close])%list n bind
          (trace ++ [FixedElems; ConstructCollection name kind element;
            ConstructLiteral open; ConstructSep name separator; ConstructLiteral close])%list)
    end end.
Theorem item_and_constructor_substitution_exact : forall item b,
  shared_step original_constructors (project_item item) b = source_step item b.
Proof.
  intros item b; destruct item; reflexivity.
Qed.

Definition inspect_build h b := buffer (params b) (syntax b) (next_param b) (pending b)
  (operations b ++ [InspectBuild h])%list.
Fixpoint source_build (store : nat -> SourceItem) handles b := match handles with
| [] => Continue b
| h :: rest => match source_step (store h) (inspect_build h b) with
    | Continue next => source_build store rest next
    | Refuse reason stopped => Refuse reason stopped end end.
Fixpoint shared_build (reader : nat -> ItemView) c handles b := match handles with
| [] => Continue b
| h :: rest => match shared_step c (reader h) (inspect_build h b) with
    | Continue next => shared_build reader c rest next
    | Refuse reason stopped => Refuse reason stopped end end.
Theorem forward_build_preserves_payload_and_operations : forall store handles b,
  shared_build (fun h => project_item (store h)) original_constructors handles b =
  source_build store handles b.
Proof.
  intros store handles; induction handles as [|h rest IH]; intros b; cbn; [reflexivity|].
  rewrite item_and_constructor_substitution_exact.
  destruct (source_step (store h) (inspect_build h b)); [apply IH|reflexivity].
Qed.

Fixpoint source_preflight (store : nat -> SourceItem) handles : bool * list Operation :=
  match handles with
  | [] => (true, [])
  | h :: rest => match store h with
      | SOtherNonTerminal _ _ => (false, [InspectPreflight h])
      | _ => let '(accepted, trace) := source_preflight store rest in
          (accepted, InspectPreflight h :: trace) end end.
Fixpoint shared_preflight (reader : nat -> ItemView) handles : bool * list Operation :=
  match handles with
  | [] => (true, [])
  | h :: rest => match reader h with
      | VOtherNonTerminal _ _ => (false, [InspectPreflight h])
      | _ => let '(accepted, trace) := shared_preflight reader rest in
          (accepted, InspectPreflight h :: trace) end end.
Theorem preflight_preserves_refusal_and_read_order : forall store handles,
  shared_preflight (fun h => project_item (store h)) handles = source_preflight store handles.
Proof.
  intros store handles; induction handles as [|h rest IH]; cbn; [reflexivity|].
  destruct (store h); cbn; try reflexivity; rewrite IH; reflexivity.
Qed.

(** All untouched data travels as original values, never synthesized defaults.
    remaining_metadata is an opaque handle for ALL other original rule fields. *)
Record Rule := {
  label : OriginalIdent; category : OriginalIdent; items : list nat;
  bindings : list (nat * list nat); remaining_metadata : nat;
  term_context : option (list Param); syntax_pattern : option (list Syntax)
}.
Definition commit r b :=
 {| label := label r; category := category r; items := items r;
    bindings := bindings r; remaining_metadata := remaining_metadata r;
    term_context := Some (params b); syntax_pattern := Some (syntax b) |}.
Record Outcome := {
  result : Rule; refused : option Refusal; trace : list Operation
}.
Definition unchanged r reason ops := {| result := r; refused := Some reason; trace := ops |}.
Definition finish r step := match step with
| Refuse reason b => unchanged r reason (operations b)
| Continue b => match pending b with
    | Some _ => unchanged r TrailingBinder (operations b)
    | None => match params b with
        | [] => unchanged r NoParameters (operations b)
        | _ :: _ => {| result := commit r b; refused := None;
            trace := (operations b ++ [CommitTermContext; CommitSyntaxPattern])%list |}
        end end end.
Definition source_normalize store r := match term_context r with
| Some _ => unchanged r AlreadyTermContext [HasTermContext]
| None => match syntax_pattern r with
    | Some _ => unchanged r AlreadySyntaxPattern [HasTermContext; HasSyntaxPattern]
    | None => let '(accepted, pretrace) := source_preflight store (items r) in
        let ops := ([HasTermContext; HasSyntaxPattern] ++ pretrace)%list in
        if accepted then finish r (source_build store (items r) (buffer [] [] 0 None ops))
        else unchanged r NonCategoryPreflight ops end end.
Definition shared_normalize reader c r := match term_context r with
| Some _ => unchanged r AlreadyTermContext [HasTermContext]
| None => match syntax_pattern r with
    | Some _ => unchanged r AlreadySyntaxPattern [HasTermContext; HasSyntaxPattern]
    | None => let '(accepted, pretrace) := shared_preflight reader (items r) in
        let ops := ([HasTermContext; HasSyntaxPattern] ++ pretrace)%list in
        if accepted then finish r (shared_build reader c (items r) (buffer [] [] 0 None ops))
        else unchanged r NonCategoryPreflight ops end end.
Theorem original_normalization_relocated_exactly : forall store r,
  shared_normalize (fun h => project_item (store h)) original_constructors r =
  source_normalize store r.
Proof.
  intros; unfold shared_normalize, source_normalize.
  destruct (term_context r); [reflexivity|].
  destruct (syntax_pattern r); [reflexivity|].
  rewrite preflight_preserves_refusal_and_read_order.
  destruct (source_preflight store (items r)) as [accepted ops].
  destruct accepted; [rewrite forward_build_preserves_payload_and_operations|]; reflexivity.
Qed.

Theorem term_context_presence_short_circuits_all_other_reads : forall reader c r tc,
  term_context r = Some tc -> shared_normalize reader c r =
  unchanged r AlreadyTermContext [HasTermContext].
Proof. intros; unfold shared_normalize; rewrite H; reflexivity. Qed.
Theorem syntax_presence_short_circuits_item_reads : forall reader c r sp,
  term_context r = None -> syntax_pattern r = Some sp ->
  shared_normalize reader c r = unchanged r AlreadySyntaxPattern [HasTermContext; HasSyntaxPattern].
Proof. intros; unfold shared_normalize; rewrite H, H0; reflexivity. Qed.
Theorem preflight_noncategory_stops_suffix : forall reader h rest ident kind,
  reader h = VOtherNonTerminal ident kind ->
  shared_preflight reader (h :: rest) = (false, [InspectPreflight h]).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem build_nondelimited_collection_stops_suffix : forall reader c h rest kind elem sep b,
  reader h = VCollection kind elem sep None ->
  shared_build reader c (h :: rest) b = Refuse MissingDelimiters (inspect_build h b).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem finish_refusal_leaves_entire_rule_identical : forall r step reason,
  refused (finish r step) = Some reason -> result (finish r step) = r.
Proof.
  intros r [b|why b] reason H; [|reflexivity].
  unfold finish in *; destruct (pending b); [reflexivity|].
  destruct (params b); [reflexivity|discriminate].
Qed.
Definition untouched r := (label r, category r, items r, bindings r, remaining_metadata r).
Theorem finish_preserves_every_untouched_field : forall r step,
  untouched (result (finish r step)) = untouched r.
Proof.
  intros r [b|reason b]; [|reflexivity]. unfold finish.
  destruct (pending b); [reflexivity|]. destruct (params b); reflexivity.
Qed.
Theorem successful_finish_commits_both_fields : forall r b,
  pending b = None -> params b <> [] ->
  result (finish r (Continue b)) = commit r b /\
  term_context (result (finish r (Continue b))) = Some (params b) /\
  syntax_pattern (result (finish r (Continue b))) = Some (syntax b).
Proof.
  intros r b Hnone Hnonempty; unfold finish; rewrite Hnone.
  destruct (params b) eqn:E; [contradiction|].
  repeat split; cbn [result commit term_context syntax_pattern]; try rewrite E; reflexivity.
Qed.
Theorem normalization_refusal_is_atomic : forall reader c r reason,
  refused (shared_normalize reader c r) = Some reason ->
  result (shared_normalize reader c r) = r.
Proof.
  intros reader c r reason H; unfold shared_normalize in *.
  destruct (term_context r); [reflexivity|].
  destruct (syntax_pattern r); [reflexivity|].
  destruct (shared_preflight reader (items r)) as [accepted ops].
  destruct accepted; [eapply finish_refusal_leaves_entire_rule_identical; exact H|reflexivity].
Qed.
Theorem normalization_preserves_original_items_bindings_and_metadata : forall reader c r,
  untouched (result (shared_normalize reader c r)) = untouched r.
Proof.
  intros; unfold shared_normalize.
  destruct (term_context r); [reflexivity|].
  destruct (syntax_pattern r); [reflexivity|].
  destruct (shared_preflight reader (items r)) as [accepted ops].
  destruct accepted; [apply finish_preserves_every_untouched_field|reflexivity].
Qed.

Theorem later_binder_overwrites_pending : forall c earlier later b,
  shared_step c (VBinder later)
    (buffer (params b) (syntax b) (next_param b) (Some earlier) (operations b)) =
  Continue (buffer (params b) (syntax b) (next_param b) (Some later) (operations b)).
Proof. reflexivity. Qed.
Theorem literal_keeps_binder_and_counter : forall c text b,
  shared_step c (VTerminal text) b = Continue
    (buffer (params b) (syntax b ++ [make_literal c text])%list (next_param b) (pending b)
      (operations b ++ [ConstructLiteral text])%list).
Proof. reflexivity. Qed.
Theorem collection_keeps_binder_counter_and_fixed_name : forall kind elem sep open close b,
  shared_step original_constructors (VCollection kind elem sep (Some (open, close))) b =
  Continue (buffer (params b ++ [Simple ElemsName (Collection kind (Base elem))])%list
    (syntax b ++ [Literal open; Sep ElemsName sep None; Literal close])%list
    (next_param b) (pending b)
    (operations b ++ [FixedElems; ConstructCollection ElemsName kind elem;
      ConstructLiteral open; ConstructSep ElemsName sep; ConstructLiteral close])%list).
Proof. reflexivity. Qed.
Theorem simple_counter_requires_one_increment : forall n usize_max,
  n < usize_max -> S n <= usize_max.
Proof. intros; lia. Qed.
Theorem abstraction_counter_requires_two_increments : forall n usize_max,
  S n < usize_max -> S n <= usize_max /\ S (S n) <= usize_max.
Proof. intros; lia. Qed.

(** Witnesses expose constructors, span identity, overwrite and refusal effects.
    Distinct spans ensure this is stronger than name-text-only correspondence. *)
Definition ident_a := {| ident_text := "A"%string; ident_span := 11 |}.
Definition ident_b := {| ident_text := "B"%string; ident_span := 22 |}.
Definition ident_c := {| ident_text := "C"%string; ident_span := 33 |}.
Definition witness_store h := match h with
| 0 => SBinder ident_a
| 1 => SBinder ident_b
| 2 => STerminal "."%string
| 3 => SCollection S.ListKind ident_c ","%string (Some ("["%string, "]"%string))
| 4 => SCategory ident_a
| 5 => SCategory ident_c
| 6 => SCollection S.BagKind ident_b ";"%string (Some ("{"%string, "}"%string))
| 7 => SCollection S.ListKind ident_c ","%string None
| _ => SOtherNonTerminal ident_a 4 end.
Definition witness_rule handles :=
 {| label := ident_a; category := ident_b; items := handles;
    bindings := [(0, [4])]; remaining_metadata := 123;
    term_context := None; syntax_pattern := None |}.
Definition normalized handles := shared_normalize
  (fun h => project_item (witness_store h)) original_constructors (witness_rule handles).
Example overwrite_literal_collection_and_fresh_counter_witness :
  term_context (result (normalized [0; 1; 2; 3; 4; 5; 6])) = Some
    [Simple ElemsName (Collection S.ListKind (Base ident_c));
     Abstraction (PName 0) (PName 1) (Arrow (Base ident_b) (Base ident_a));
     Simple (PName 2) (Base ident_c);
     Simple ElemsName (Collection S.BagKind (Base ident_b))] /\
  syntax_pattern (result (normalized [0; 1; 2; 3; 4; 5; 6])) = Some
    [Literal "."%string; Literal "["%string; Sep ElemsName ","%string None; Literal "]"%string;
     ParamRef (PName 0); ParamRef (PName 1); ParamRef (PName 2);
     Literal "{"%string; Sep ElemsName ";"%string None; Literal "}"%string].
Proof. vm_compute; split; reflexivity. Qed.
Example delimiter_refusal_discards_existing_local_prefix :
  result (normalized [5; 7; 4]) = witness_rule [5; 7; 4] /\
  refused (normalized [5; 7; 4]) = Some MissingDelimiters.
Proof. vm_compute; split; reflexivity. Qed.
Example trailing_binder_refusal_discards_existing_local_prefix :
  result (normalized [5; 0; 2; 3]) = witness_rule [5; 0; 2; 3] /\
  refused (normalized [5; 0; 2; 3]) = Some TrailingBinder.
Proof. vm_compute; split; reflexivity. Qed.
Example pure_literals_remain_original :
  result (normalized [2; 2]) = witness_rule [2; 2] /\
  refused (normalized [2; 2]) = Some NoParameters.
Proof. vm_compute; split; reflexivity. Qed.
Example preflight_refuses_before_any_constructor :
  trace (normalized [5; 8; 4]) =
    [HasTermContext; HasSyntaxPattern; InspectPreflight 5; InspectPreflight 8] /\
  result (normalized [5; 8; 4]) = witness_rule [5; 8; 4].
Proof. vm_compute; split; reflexivity. Qed.

Print Assumptions item_and_constructor_substitution_exact.
Print Assumptions forward_build_preserves_payload_and_operations.
Print Assumptions preflight_preserves_refusal_and_read_order.
Print Assumptions original_normalization_relocated_exactly.
Print Assumptions term_context_presence_short_circuits_all_other_reads.
Print Assumptions syntax_presence_short_circuits_item_reads.
Print Assumptions preflight_noncategory_stops_suffix.
Print Assumptions build_nondelimited_collection_stops_suffix.
Print Assumptions normalization_refusal_is_atomic.
Print Assumptions normalization_preserves_original_items_bindings_and_metadata.
Print Assumptions successful_finish_commits_both_fields.
Print Assumptions later_binder_overwrites_pending.
Print Assumptions literal_keeps_binder_and_counter.
Print Assumptions collection_keeps_binder_counter_and_fixed_name.
Print Assumptions simple_counter_requires_one_increment.
Print Assumptions abstraction_counter_requires_two_increments.
End LegacyRuleNormalizationProjection.
