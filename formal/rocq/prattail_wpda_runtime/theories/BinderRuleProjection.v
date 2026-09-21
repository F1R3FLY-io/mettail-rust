(** Source correspondence for the ORIGINAL classify_binder_in and
    arrow_codomain_name in macros/src/gen/runtime/wpda_codegen/binder.rs.

    Source ledger (read against the complete original function):
    1. Missing term context, missing syntax, and empty syntax reject BEFORE
       the first-matching-category delimiter lookup. Lookup precedes the anchor
       and exact top-level Class-5 structural gates. Some [] remains distinct
       from None. Collection and Map are distinct authored type constructors.
    2. Declaration registration consumes the ORIGINAL TermParamLeaves steps.
       Optional names are inserted before leaf validation. Map bindings are
       last-wins; param_cats keeps every authored entry in preorder. Abstractions
       overwrite body_cat, OR the flags, and insert binder BEFORE body. Raw
       identifier equality for Map(Base(K), Base(V)) is separate from spelling.
    3. Leading Simple Ident captures TokenText; leading Body Ident rejects.
       Other Simple/Body categories contribute a leading term argument. Leading
       token/guest captures prepend their action only; no guest helper is called.
    4. Main syntax starts at index 1. skip_next consumes exactly the next outer
       item. Mid-rule Simple/Body Ident capture IdentText. Bare collection/list
       parameters reject. Plain binder-list Sep requires an immediate literal;
       main collection Sep is open-ended without one. kv executes BEFORE the
       main unchecked slot increment, unlike the imported optional classifier.
    5. Sourced Sep observes Map THEN Zip, tests alias length 2, left collection,
       right binder list, aliases, close, and body in that order. Name alias wins
       the first comparison. Body captures/operations/unknown parameters reject.
       At least one binder occurrence is required; no name occurrence is needed.
       Inner collection slot 0/kv None and the unused inner action vector remain
       explicit. Outer slot is allocated after body validation. Vec drain then
       BinderList are emitted, independently of the left declaration's kind.
    6. Opt checks/assigns the group counter BEFORE calling the SAME optional
       frame loop. Its finite-execution law is composed directly below, with
       shared callbacks and all effect prefixes, including rejection. Empty
       successful bodies reject after the call. No second optional recognizer.
    7. Final empty-position/capture and empty-action gates precede the arity
       cast. Every BinderShape field is represented, in original output order.

    Arithmetic: main += 1 is modeled as its ordinary mathematical increment;
    a diagnostic flag records whether every executed increment remains u8.
    action_arity is the ORIGINAL modulo-256 cast, and the flag also records
    whether the uncast action count fits. The faithful Rust claim is restricted
    to representable executions. Outside that domain Rust debug panic/release
    wrap differences are NOT certified. The flag is proof instrumentation,
    NOT an added Rust check or a proven pre-admission algorithm. Owned runtime
    exposure still requires separate admission before an overflowing operation.

    Limits: shallow readers are immutable and names/types/ops retain original
    handles. Spelling and raw identifier equality stand for the original pure
    ToString/Ident::eq observations, without normalizing or rebuilding syn.
    At the leading __tok_{} default, spelling denotes the original Ident Display
    site (Ident ToString delegates Display); Rust must retain that Display site.
    The association-list parameter map retains shadowed bindings as a lookup
    model; Rust HashMap replaces them. Equality concerns lookup, output and
    refusal/effect behavior, not internal memory, allocation or hash iteration.
    Category classification below uses the exact Ident spelling, as in the
    optional proof. Callback bodies are shared, not verified. Mathematical
    projection stores are witnesses, not allocated recursive Rust views. Fuel
    exhaustion is an explicit proof outcome, not None. No Rust extraction,
    allocation/unwind, lifetime, all-input termination, dynamic admission,
    parser-completeness or independently derived parser automaton is asserted.
*)
From Stdlib Require Import List String Bool Arith NArith Lia.
From PrattailWpdaRuntime Require Import BinderOptionalProjection TermParamReaderProjection.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module BinderRuleProjection.
Module O := BinderOptionalProjection.BinderOptionalProjection.
Module T := TermParamReaderProjection.TermParamReaderProjection.

Inductive SourceSyntax :=
| SLiteral (text : string) | SParam (name : nat)
| SToken (name : nat) (bind : option nat)
| SGuest (open close bind kind : nat) | SOp (operation : nat).
Inductive SyntaxObservation :=
| Literal (text : string) | Param (name : nat)
| Token (name : nat) (bind : option nat)
| Guest (open close bind kind : nat) | Op (operation : nat).
Definition project_syntax node := match node with
| SLiteral text => Literal text | SParam name => Param name
| SToken name bind => Token name bind | SGuest o c b k => Guest o c b k
| SOp operation => Op operation end.

(** Collection tags 0..3 denote Vec, HashBag, HashSet, HashMap respectively;
    every other authored collection tag remains distinguishable and rejected. *)
Definition vec_kind := 0.
Definition hashmap_kind := 3.
Definition accepted_collection kind := Nat.ltb kind 4.
Inductive SourceType :=
| SBase (name : nat) | SCollection (kind element : nat)
| SMapType (key value : nat) | SArrow (domain codomain : nat)
| STypeOther (opaque : nat).
Inductive TypeObservation :=
| Base (name : nat) | CollectionType (kind element : nat)
| MapType (key value : nat) | Arrow (domain codomain : nat)
| TypeOther (original : nat).
Definition project_type original ty := match ty with
| SBase name => Base name | SCollection kind element => CollectionType kind element
| SMapType key value => MapType key value | SArrow domain codomain => Arrow domain codomain
| STypeOther _ => TypeOther original end.
Inductive SourceOperation :=
| SOpt (inner : nat) | SSep (collection : nat) (separator : string) (source : option nat)
| SMap (source params body : nat) | SZip (left right : nat)
| SOperationOther (opaque : nat).
Inductive OperationObservation :=
| Opt (inner : nat) | Sep (collection : nat) (separator : string) (source : option nat)
| Map (source params body : nat) | Zip (left right : nat) | OperationOther (original : nat).
Definition project_operation original operation := match operation with
| SOpt inner => Opt inner | SSep name separator source => Sep name separator source
| SMap source params body => Map source params body | SZip lhs rhs => Zip lhs rhs
| SOperationOther _ => OperationOther original end.
Record Rule := {
  term_context : option nat; syntax_pattern : option nat;
  rule_label : nat; rule_category : nat
}.
Record SourceStore := {
  source_syntax : nat -> list SourceSyntax;
  source_operations : nat -> SourceOperation;
  source_types : nat -> SourceType;
  source_terms : T.SourceStore;
  source_names : nat -> list nat;
  source_spelling : nat -> string;
  source_ident_equal : nat -> nat -> bool;
  source_rule : Rule;
  source_categories : list (nat * option nat)
}.
Record ViewStore := {
  view_syntax : nat -> list SyntaxObservation;
  view_operations : nat -> OperationObservation;
  view_types : nat -> TypeObservation;
  view_terms : T.ViewStore;
  view_names : nat -> list nat;
  view_spelling : nat -> string;
  view_ident_equal : nat -> nat -> bool;
  view_rule : Rule;
  view_categories : list (nat * option nat)
}.
Definition project_store store :=
 {| view_syntax := fun sequence => List.map project_syntax (source_syntax store sequence);
    view_operations := fun handle => project_operation handle (source_operations store handle);
    view_types := fun handle => project_type handle (source_types store handle);
    view_terms := T.project_store (source_terms store);
    view_names := source_names store; view_spelling := source_spelling store;
    view_ident_equal := source_ident_equal store; view_rule := source_rule store;
    view_categories := source_categories store |}.
Record Reader := {
  syntax_len : nat -> nat;
  syntax_at : nat -> nat -> option SyntaxObservation;
  operation_at : nat -> OperationObservation;
  type_at : nat -> TypeObservation;
  terms : T.Reader;
  names_len : nat -> nat;
  name_at : nat -> nat -> option nat;
  spelling : nat -> string;
  ident_equal : nat -> nat -> bool;
  rule : Rule;
  categories : list (nat * option nat)
}.
Definition source_reader store :=
 {| syntax_len := fun sequence => List.length (source_syntax store sequence);
    syntax_at := fun sequence index => option_map project_syntax (nth_error (source_syntax store sequence) index);
    operation_at := fun handle => project_operation handle (source_operations store handle);
    type_at := fun handle => project_type handle (source_types store handle);
    terms := T.source_reader (source_terms store);
    names_len := fun sequence => List.length (source_names store sequence);
    name_at := fun sequence => nth_error (source_names store sequence);
    spelling := source_spelling store; ident_equal := source_ident_equal store;
    rule := source_rule store; categories := source_categories store |}.
Definition view_reader store :=
 {| syntax_len := fun sequence => List.length (view_syntax store sequence);
    syntax_at := fun sequence => nth_error (view_syntax store sequence);
    operation_at := view_operations store; type_at := view_types store;
    terms := T.view_reader (view_terms store);
    names_len := fun sequence => List.length (view_names store sequence);
    name_at := fun sequence => nth_error (view_names store sequence);
    spelling := view_spelling store; ident_equal := view_ident_equal store;
    rule := view_rule store; categories := view_categories store |}.
Theorem syntax_length_correspondence : forall store sequence,
  syntax_len (view_reader (project_store store)) sequence = syntax_len (source_reader store) sequence.
Proof. intros; cbn; apply length_map. Qed.
Theorem syntax_index_correspondence : forall store sequence index,
  syntax_at (view_reader (project_store store)) sequence index = syntax_at (source_reader store) sequence index.
Proof. intros; cbn; apply O.map_nth_exact. Qed.
Theorem opaque_operations_correspond : forall store handle,
  operation_at (view_reader (project_store store)) handle = project_operation handle (source_operations store handle).
Proof. reflexivity. Qed.
Theorem raw_type_and_identifier_observations_correspond : forall store ty left right,
  type_at (view_reader (project_store store)) ty = project_type ty (source_types store ty) /\
  ident_equal (view_reader (project_store store)) left right = source_ident_equal store left right.
Proof. intros; split; reflexivity. Qed.
Theorem absent_and_empty_authored_context_preserved : forall store,
  term_context (rule (view_reader (project_store store))) = term_context (source_rule store) /\
  syntax_pattern (rule (view_reader (project_store store))) = syntax_pattern (source_rule store) /\
  terms (view_reader (project_store store)) = T.source_reader (source_terms store).
Proof. intros; repeat split; reflexivity. Qed.

(** Direct embedding into the ALREADY VERIFIED original optional classifier.
    Map/Zip remain opaque there, just as the original optional reader requires. *)
Definition optional_syntax store node := match node with
| SLiteral text => O.SLiteral text | SParam name => O.SParam (source_spelling store name)
| SToken name bind => O.STokenKind (source_spelling store name) (option_map (source_spelling store) bind)
| SGuest o c b k => O.SGuestBody (source_spelling store o) (source_spelling store c) (source_spelling store b) k
| SOp operation => O.SOp operation end.
Definition optional_operation store handle := match source_operations store handle with
| SOpt inner => O.SOpt inner
| SSep collection separator source => O.SSep (source_spelling store collection) separator source
| _ => O.SUnsupported handle end.
Definition optional_store store : O.SourceStore :=
 {| O.source_sequences := fun sequence => List.map (optional_syntax store) (source_syntax store sequence);
    O.source_operations := optional_operation store |}.

Inductive Mode := Original | Projected.
Definition reader mode store := match mode with
| Original => source_reader store | Projected => view_reader (project_store store) end.
Definition iterator_step mode store := match mode with
| Original => T.source_step (source_terms store)
| Projected => T.reader_step (T.view_reader (T.project_store (source_terms store))) end.
Theorem imported_iterator_step_correspondence : forall store work,
  iterator_step Projected store work = iterator_step Original store work.
Proof. intros; apply T.original_step_correspondence. Qed.

Definition Parameters := list (string * O.ParamKind).
Fixpoint lookup (parameters : Parameters) name := match parameters with
| [] => None | (key, kind) :: rest => if String.eqb key name then Some kind else lookup rest name end.
Record Declarations := {
  parameter_map : Parameters; is_multi : bool; has_binder : bool;
  body_cat : option string; param_cats : list string; optional_params : list string
}.
Definition empty_declarations :=
 {| parameter_map := []; is_multi := false; has_binder := false;
    body_cat := None; param_cats := []; optional_params := [] |}.
Definition insert_optional name d :=
 {| parameter_map := parameter_map d; is_multi := is_multi d; has_binder := has_binder d;
    body_cat := body_cat d; param_cats := param_cats d;
    optional_params := if existsb (String.eqb name) (optional_params d)
      then optional_params d else name :: optional_params d |}.
Definition insert_binding name kind d :=
 {| parameter_map := (name, kind) :: parameter_map d; is_multi := is_multi d;
    has_binder := has_binder d; body_cat := body_cat d;
    param_cats := param_cats d; optional_params := optional_params d |}.
Definition append_category cat d :=
 {| parameter_map := parameter_map d; is_multi := is_multi d; has_binder := has_binder d;
    body_cat := body_cat d; param_cats := (param_cats d ++ [cat])%list;
    optional_params := optional_params d |}.
Definition set_abstraction multi cat d :=
 {| parameter_map := parameter_map d; is_multi := orb (is_multi d) multi; has_binder := true;
    body_cat := Some cat; param_cats := param_cats d; optional_params := optional_params d |}.
Theorem duplicate_binding_is_last_wins : forall d name kind,
  lookup (parameter_map (insert_binding name kind d)) name = Some kind.
Proof. intros; cbn; rewrite String.eqb_refl; reflexivity. Qed.
Theorem authored_category_entries_are_not_deduplicated : forall d first second,
  param_cats (append_category second (append_category first d)) =
  (param_cats d ++ [first; second])%list.
Proof. intros; cbn; rewrite <- app_assoc; reflexivity. Qed.

Definition arrow_codomain_name r ty := match type_at r ty with
| Arrow _ codomain => match type_at r codomain with Base name => Some (spelling r name) | _ => None end
| _ => None end.
Definition leaf_name leaf := match T.kind leaf with
| T.LSimple _ name _ | T.LGuardBody _ name => name
| T.LAbstraction _ binder _ _ | T.LMultiAbstraction _ binder _ _ => binder end.
Inductive Registration := Registered (declarations : Declarations) | RegistrationRejected (declarations : Declarations).
Definition register_simple r name ty d := match type_at r ty with
| Base ident => let cat := spelling r ident in
    Registered (insert_binding (spelling r name) (O.Simple cat) (append_category cat d))
| CollectionType kind element => match type_at r element with
    | Base ident => if accepted_collection kind then
        let cat := spelling r ident in
        Registered (insert_binding (spelling r name) (O.Collection cat kind) (append_category cat d))
      else RegistrationRejected d
    | _ => RegistrationRejected d end
| MapType key value => match type_at r key, type_at r value with
    | Base k, Base v => if ident_equal r k v then
        let cat := spelling r k in
        Registered (insert_binding (spelling r name) (O.Collection cat hashmap_kind) (append_category cat d))
      else RegistrationRejected d
    | _, _ => RegistrationRejected d end
| _ => RegistrationRejected d end.
Definition register_abstraction r multi binder body ty (in_optional : bool) d :=
  match arrow_codomain_name r ty with
  | None => RegistrationRejected d
  | Some cat =>
      let with_flags := set_abstraction multi cat d in
      let with_binder := insert_binding (spelling r binder) (if multi then O.BinderList else O.Binder) with_flags in
      let with_body := insert_binding (spelling r body) (O.Body cat) with_binder in
      Registered (if in_optional then insert_optional (spelling r body) with_body else with_body)
  end.
Definition register_leaf r leaf d :=
  let in_optional := T.is_optional leaf in
  let marked := if in_optional then insert_optional (spelling r (leaf_name leaf)) d else d in
  match T.kind leaf with
  | T.LSimple _ name ty => register_simple r name ty marked
  | T.LGuardBody _ name => Registered (insert_binding (spelling r name) O.Guard marked)
  | T.LAbstraction _ binder body ty => register_abstraction r false binder body ty in_optional marked
  | T.LMultiAbstraction _ binder body ty => register_abstraction r true binder body ty in_optional marked end.
Theorem arrow_helper_correspondence : forall store ty,
  arrow_codomain_name (reader Projected store) ty = arrow_codomain_name (reader Original store) ty.
Proof. reflexivity. Qed.
Theorem declaration_registration_correspondence : forall store leaf d,
  register_leaf (reader Projected store) leaf d = register_leaf (reader Original store) leaf d.
Proof. reflexivity. Qed.

Record DeclarationState := {
  declarations : Declarations; declaration_work : T.Work; declaration_trace : list nat
}.
Inductive DeclarationResult :=
| DeclContinue (state : DeclarationState) | DeclAccepted (state : DeclarationState)
| DeclRejected (state : DeclarationState) | DeclInvalid (state : DeclarationState).
Definition decl_state d work visits :=
 {| declarations := d; declaration_work := work; declaration_trace := visits |}.
Definition declaration_step mode store state :=
  let d := declarations state in let visits := declaration_trace state in
  match iterator_step mode store (declaration_work state) with
  | T.Done => DeclAccepted state
  | T.Continue rest seen => DeclContinue (decl_state d rest (visits ++ seen)%list)
  | T.Yield leaf rest seen =>
      match register_leaf (reader mode store) leaf d with
      | Registered updated => DeclContinue (decl_state updated rest (visits ++ seen)%list)
      | RegistrationRejected partial => DeclRejected (decl_state partial rest (visits ++ seen)%list) end
  | T.InvalidReader => DeclInvalid state end.
Fixpoint run_declarations fuel mode store state := match fuel with
| 0 => DeclContinue state
| S remaining => match declaration_step mode store state with
    | DeclContinue next => run_declarations remaining mode store next | other => other end end.
Theorem declaration_step_correspondence : forall store state,
  declaration_step Projected store state = declaration_step Original store state.
Proof.
  intros. unfold declaration_step. rewrite imported_iterator_step_correspondence.
  destruct (iterator_step Original store (declaration_work state)); reflexivity.
Qed.
Theorem declaration_preorder_state_and_failure_correspondence : forall fuel store state,
  run_declarations fuel Projected store state = run_declarations fuel Original store state.
Proof.
  induction fuel; intros; cbn [run_declarations]; [reflexivity|].
  rewrite declaration_step_correspondence.
  destruct (declaration_step Original store state); auto.
Qed.

Fixpoint declared_delimiters r cat (entries : list (nat * option nat)) := match entries with
| [] => None
| (name, delimiters) :: rest => if ident_equal r name cat then delimiters else declared_delimiters r cat rest end.
Theorem declared_delimiters_correspondence : forall entries store cat,
  declared_delimiters (reader Projected store) cat entries =
  declared_delimiters (reader Original store) cat entries.
Proof.
  induction entries as [|[name delimiters] rest IH]; intros; cbn [declared_delimiters]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Definition literal_at r sp index := match syntax_at r sp index with Some (Literal _) => true | _ => false end.
Definition plain_sep_at r sp index := match syntax_at r sp index with
| Some (Op op) => match operation_at r op with Sep _ _ None => true | _ => false end
| _ => false end.
Definition class5_excluded r tc sp :=
  if Nat.eqb (T.params_len (terms r) tc) 1 then
    match T.param_at (terms r) tc 0 with
    | Some handle => match T.param (terms r) handle with
      | T.Simple _ ty => match type_at r ty with
        | CollectionType _ _ =>
          let shape3 := Nat.eqb (syntax_len r sp) 3 && literal_at r sp 0 &&
            plain_sep_at r sp 1 && literal_at r sp 2 in
          let shape4 := Nat.eqb (syntax_len r sp) 4 && literal_at r sp 0 &&
            (match syntax_at r sp 1 with Some (Literal text) => String.eqb text "(" | _ => false end) &&
            plain_sep_at r sp 2 && literal_at r sp 3 in
          shape3 || shape4
        | _ => false end
      | _ => false end
    | None => false end
  else false.
Theorem class5_structural_gate_correspondence : forall store tc sp,
  class5_excluded (reader Projected store) tc sp = class5_excluded (reader Original store) tc sp.
Proof.
  intros. unfold class5_excluded, literal_at, plain_sep_at, reader.
  repeat rewrite syntax_length_correspondence. repeat rewrite syntax_index_correspondence.
  reflexivity.
Qed.

Record Leading := {
  leading_category : option string; leading_ident_capture : option string;
  leading_args : list O.Action; leading_capture : bool
}.
Definition no_leading := {| leading_category := None; leading_ident_capture := None;
  leading_args := []; leading_capture := false |}.
Definition token_name r name bind := match bind with Some b => spelling r b | None => "__tok_" ++ spelling r name end.
Definition leading r d node := match node with
| Literal _ => Some no_leading
| Param name => match lookup (parameter_map d) (spelling r name) with
  | Some (O.Body cat) => if String.eqb cat "Ident" then None else
      Some {| leading_category := Some cat; leading_ident_capture := None;
        leading_args := [O.ATerm cat]; leading_capture := false |}
  | Some (O.Simple cat) => if String.eqb cat "Ident" then
      Some {| leading_category := None; leading_ident_capture := Some (spelling r name);
        leading_args := [O.ATokenText (spelling r name)]; leading_capture := true |}
    else Some {| leading_category := Some cat; leading_ident_capture := None;
      leading_args := [O.ATerm cat]; leading_capture := false |}
  | _ => None end
| Token name bind => Some {| leading_category := None; leading_ident_capture := None;
    leading_args := [O.ATokenText (token_name r name bind)]; leading_capture := true |}
| Guest _ _ bind kind => Some {| leading_category := None; leading_ident_capture := None;
    leading_args := [O.AGuest (spelling r bind) kind]; leading_capture := true |}
| Op _ => None end.
Theorem leading_role_correspondence : forall store d node,
  leading (reader Projected store) d node = leading (reader Original store) d node.
Proof. reflexivity. Qed.

Record MapBody := { map_positions : list O.Position; map_args : list O.Action }.
Definition append_map_body body positions args :=
 {| map_positions := (map_positions body ++ positions)%list; map_args := (map_args body ++ args)%list |}.
Definition map_body_item r node alias_name alias_binder element separator close body := match node with
| Literal text => Some (append_map_body body [O.PLiteral text] [])
| Param name => let text := spelling r name in
    if String.eqb text alias_name then Some (append_map_body body
      [O.PParam element (Some {| O.collection_separator := separator; O.collection_close := close;
        O.collection_element := element; O.key_val_separator := None; O.slot_idx := 0%N |})] [O.ATerm element])
    else if String.eqb text alias_binder then Some (append_map_body body [O.PBinderIdent] [O.ABinderName])
    else None
| _ => None end.
Fixpoint walk_map_body remaining r sequence index alias_name alias_binder element separator close body :=
  match remaining with
  | 0 => Some body
  | S count => match syntax_at r sequence index with
      | None => None
      | Some node => match map_body_item r node alias_name alias_binder element separator close body with
          | None => None
          | Some next => walk_map_body count r sequence (S index) alias_name alias_binder element separator close next end end end.
Definition contains_binder body := existsb (fun p => match p with O.PBinderIdent => true | _ => false end) (map_positions body).
Theorem map_body_correspondence : forall remaining store sequence index alias_name alias_binder element separator close body,
  walk_map_body remaining (reader Projected store) sequence index alias_name alias_binder element separator close body =
  walk_map_body remaining (reader Original store) sequence index alias_name alias_binder element separator close body.
Proof.
  induction remaining; intros; cbn [walk_map_body]; [reflexivity|].
  unfold reader at 1. rewrite syntax_index_correspondence.
  change (syntax_at (source_reader store) sequence index) with (syntax_at (reader Original store) sequence index).
  destruct (syntax_at (reader Original store) sequence index) as [node|]; [|reflexivity].
  change (map_body_item (reader Projected store) node alias_name alias_binder element separator close body)
    with (map_body_item (reader Original store) node alias_name alias_binder element separator close body).
  destruct (map_body_item (reader Original store) node alias_name alias_binder element separator close body);
    [apply IHremaining|reflexivity].
Qed.

Record BinderShape := {
  label : string; result_cat : string; shape_leading_category : option string;
  shape_leading_ident_capture : option string; positions : list O.Position;
  shape_is_multi : bool; shape_has_binder : bool; action_arity : N;
  action_args : list O.Action; shape_body_cat : option string; shape_param_cats : list string
}.

Section Effects.
Context {State : Type}.
Variable guest_openers : string -> State -> list string * State.
Variable key_value : option nat -> nat -> State -> option string * State.

Record MainState := {
  rule_declarations : Declarations; rule_leading : Leading;
  rule_positions : list O.Position; rule_actions : list O.Action;
  effect : @O.Effects State; representable : bool
}.
Definition with_effect state e admissible :=
 {| rule_declarations := rule_declarations state; rule_leading := rule_leading state;
    rule_positions := rule_positions state; rule_actions := rule_actions state;
    effect := e; representable := admissible |}.
Definition append_main state ps args :=
 {| rule_declarations := rule_declarations state; rule_leading := rule_leading state;
    rule_positions := (rule_positions state ++ ps)%list; rule_actions := (rule_actions state ++ args)%list;
    effect := effect state; representable := representable state |}.
Definition mark_multi state :=
  let d := rule_declarations state in
 {| rule_declarations := {| parameter_map := parameter_map d; is_multi := true; has_binder := true;
      body_cat := body_cat d; param_cats := param_cats d; optional_params := optional_params d |};
    rule_leading := rule_leading state; rule_positions := rule_positions state;
    rule_actions := rule_actions state; effect := effect state; representable := representable state |}.
Definition unchecked_slot_increment state :=
  let e := effect state in
  with_effect state (O.set_slots e (N.succ (O.collection_slots e)))
    (representable state && N.ltb (O.collection_slots e) O.u8_max).

Inductive MainStep :=
| MainContinue (skip_next : bool) (state : MainState)
| MainRejected (state : MainState)
| OptionalExhausted (state : MainState) (configuration : @O.Configuration State).

Definition mid_parameter r name state :=
  let text := spelling r name in
  match lookup (parameter_map (rule_declarations state)) text with
  | Some O.Binder => MainContinue false (append_main state
      [O.PBinderList "" "" [O.PBinderIdent] None false false 0%N] [O.ABinderName])
  | Some (O.Body cat) | Some (O.Simple cat) =>
      if String.eqb cat "Ident" then MainContinue false (append_main state [O.PIdentText text] [O.AIdentText text])
      else MainContinue false (append_main state [O.PParam cat None] [O.ATerm cat])
  | Some O.Guard => MainContinue false (append_main state [O.PGuard] [O.APredicate])
  | _ => MainRejected state end.

Definition plain_separator r declared sequence index name separator state :=
  match lookup (parameter_map (rule_declarations state)) (spelling r name) with
  | Some O.BinderList => match syntax_at r sequence (S index) with
      | Some (Literal close) => MainContinue true (append_main state
          [O.PBinderList separator close [O.PBinderIdent] None true true 0%N] [O.ABinderList])
      | _ => MainRejected state end
  | Some (O.Collection element kind) =>
      let '(close, absorbs) := match syntax_at r sequence (S index) with
        | Some (Literal text) => (text, true) | _ => ("", false) end in
      let e := effect state in
      let '(pair_value, callback_state) := key_value declared kind (O.callback_state e) in
      let called := O.after_callback e callback_state (O.KeyValueCall kind (O.next_group e) (O.collection_slots e)) in
      let slot := O.collection_slots called in
      let allocated := unchecked_slot_increment (with_effect state called (representable state)) in
      MainContinue absorbs (append_main allocated
        [O.PParam element (Some {| O.collection_separator := separator; O.collection_close := close;
          O.collection_element := element; O.key_val_separator := pair_value; O.slot_idx := slot |})]
        [O.ACollection element kind])
  | _ => MainRejected state end.

(** Separate reads preserve the original Sep -> Map -> Zip gates. *)
Definition mapped_separator r sequence index source separator state :=
  match operation_at r source with
  | Map zip_source aliases body => match operation_at r zip_source with
    | Zip lhs rhs => if Nat.eqb (names_len r aliases) 2 then
        match lookup (parameter_map (rule_declarations state)) (spelling r lhs) with
        | Some (O.Collection element _) =>
            match lookup (parameter_map (rule_declarations state)) (spelling r rhs) with
            | Some O.BinderList => match name_at r aliases 0, name_at r aliases 1 with
              | Some name_alias, Some binder_alias =>
                let alias_name := spelling r name_alias in let alias_binder := spelling r binder_alias in
                match syntax_at r sequence (S index) with
                | Some (Literal close) =>
                  match walk_map_body (syntax_len r body) r body 0 alias_name alias_binder element separator close
                    {| map_positions := []; map_args := [] |} with
                  | Some inner => if contains_binder inner then
                      let slot := O.collection_slots (effect state) in
                      let allocated := unchecked_slot_increment state in
                      MainContinue true (mark_multi (append_main allocated
                        [O.PBinderList separator close (map_positions inner) (Some element) true true slot]
                        [O.ACollection element vec_kind; O.ABinderList]))
                    else MainRejected state
                  | None => MainRejected state end
                | _ => MainRejected state end
              | _, _ => MainRejected state end
            | _ => MainRejected state end
        | _ => MainRejected state end
      else MainRejected state
    | _ => MainRejected state end
  | _ => MainRejected state end.

Definition optional_execute mode store fuel declared d configuration := match mode with
| Original => @O.execute State (lookup (parameter_map d)) guest_openers (key_value declared)
    fuel (O.source_reader (optional_store store)) configuration
| Projected => @O.execute State (lookup (parameter_map d)) guest_openers (key_value declared)
    fuel (O.view_reader (O.project_store (optional_store store))) configuration end.
Theorem imported_optional_full_result_and_effects : forall store fuel declared d configuration,
  optional_execute Projected store fuel declared d configuration =
  optional_execute Original store fuel declared d configuration.
Proof. intros; apply O.finite_execution_preserves_full_result_and_effects. Qed.
Definition optional_group mode store fuel declared child state :=
  let e := effect state in let group := O.next_group e in
  match O.checked_increment O.u32_max group with
  | None => MainRejected state
  | Some updated =>
      let allocated := O.set_group e updated in
      let config := O.configure [O.empty_frame child None] allocated in
      match optional_execute mode store fuel declared (rule_declarations state) config with
      | O.Continue next => OptionalExhausted (with_effect state (O.effects next) (representable state)) next
      | O.Rejected failed => MainRejected (with_effect state (O.effects failed) (representable state))
      | O.Accepted finished ps args =>
          let after := with_effect state (O.effects finished) (representable state) in
          match ps with
          | [] => MainRejected after
          | _ :: _ => MainContinue false (append_main after
              [O.POptional ps group (O.first_token_set ps)] [O.AOptional args]) end end end.

Definition dispatch mode store optional_fuel declared sequence index node state :=
  let r := reader mode store in
  match node with
  | Literal text => MainContinue false (append_main state [O.PLiteral text] [])
  | Param name => mid_parameter r name state
  | Token name bind => let capture := token_name r name bind in
      MainContinue false (append_main state [O.PToken (spelling r name) capture] [O.ATokenText capture])
  | Guest open close bind kind =>
      let e := effect state in let '(nested, callback_state) := guest_openers (spelling r open) (O.callback_state e) in
      let called := O.after_callback e callback_state (O.GuestCall (spelling r open) (O.next_group e) (O.collection_slots e)) in
      MainContinue false (append_main (with_effect state called (representable state))
        [O.PGuest (spelling r open) nested (spelling r close) (spelling r bind)] [O.AGuest (spelling r bind) kind])
  | Op operation => match operation_at r operation with
      | Sep name separator None => plain_separator r declared sequence index name separator state
      | Sep _ separator (Some source) => mapped_separator r sequence index source separator state
      | Opt child => optional_group mode store optional_fuel declared child state
      | _ => MainRejected state end end.

Theorem main_collection_helper_and_slot_order : forall r declared sequence index name separator state element kind,
  lookup (parameter_map (rule_declarations state)) (spelling r name) = Some (O.Collection element kind) ->
  exists close absorbs pair_value callback_state,
    key_value declared kind (O.callback_state (effect state)) = (pair_value, callback_state) /\
    plain_separator r declared sequence index name separator state =
      MainContinue absorbs (append_main
        (unchecked_slot_increment (with_effect state
          (O.after_callback (effect state) callback_state
            (O.KeyValueCall kind (O.next_group (effect state)) (O.collection_slots (effect state))))
          (representable state)))
        [O.PParam element (Some {| O.collection_separator := separator; O.collection_close := close;
          O.collection_element := element; O.key_val_separator := pair_value;
          O.slot_idx := O.collection_slots (effect state) |})] [O.ACollection element kind]).
Proof.
  intros r declared sequence index name separator state element kind H.
  unfold plain_separator; rewrite H.
  destruct (key_value declared kind (O.callback_state (effect state))) as [pair_value callback_state] eqn:Hcall.
  destruct (syntax_at r sequence (S index)) as [node|]; [destruct node|];
    eexists; eexists; exists pair_value, callback_state; split; reflexivity.
Qed.

Theorem plain_separator_correspondence : forall store declared sequence index name separator state,
  plain_separator (reader Projected store) declared sequence index name separator state =
  plain_separator (reader Original store) declared sequence index name separator state.
Proof.
  intros. unfold plain_separator, reader. repeat rewrite syntax_index_correspondence. reflexivity.
Qed.
Theorem mapped_separator_correspondence : forall store sequence index source separator state,
  mapped_separator (reader Projected store) sequence index source separator state =
  mapped_separator (reader Original store) sequence index source separator state.
Proof.
  intros. unfold mapped_separator.
  change (operation_at (reader Projected store) source) with (operation_at (reader Original store) source).
  destruct (operation_at (reader Original store) source) as [inner|name sep src|zip_source aliases body|left right|opaque]; try reflexivity.
  change (operation_at (reader Projected store) zip_source) with (operation_at (reader Original store) zip_source).
  destruct (operation_at (reader Original store) zip_source) as [inner|name sep src|a b c|left right|opaque]; try reflexivity.
  change (names_len (reader Projected store) aliases) with (names_len (reader Original store) aliases).
  destruct (Nat.eqb (names_len (reader Original store) aliases) 2); [|reflexivity].
  change (spelling (reader Projected store) left) with (spelling (reader Original store) left).
  destruct (lookup (parameter_map (rule_declarations state)) (spelling (reader Original store) left)) as [kind|]; [destruct kind|]; try reflexivity.
  change (spelling (reader Projected store) right) with (spelling (reader Original store) right).
  destruct (lookup (parameter_map (rule_declarations state)) (spelling (reader Original store) right)) as [right_role|]; [destruct right_role|]; try reflexivity.
  change (name_at (reader Projected store) aliases 0) with (name_at (reader Original store) aliases 0).
  change (name_at (reader Projected store) aliases 1) with (name_at (reader Original store) aliases 1).
  destruct (name_at (reader Original store) aliases 0) as [name_alias|]; [|reflexivity].
  destruct (name_at (reader Original store) aliases 1) as [binder_alias|]; [|reflexivity].
  unfold reader at 1. rewrite syntax_index_correspondence.
  change (syntax_at (source_reader store) sequence (S index)) with (syntax_at (reader Original store) sequence (S index)).
  destruct (syntax_at (reader Original store) sequence (S index)) as [node|]; [destruct node|]; try reflexivity.
  change (spelling (reader Projected store) name_alias) with (spelling (reader Original store) name_alias).
  change (spelling (reader Projected store) binder_alias) with (spelling (reader Original store) binder_alias).
  change (syntax_len (reader Projected store) body) with (syntax_len (view_reader (project_store store)) body).
  rewrite syntax_length_correspondence. rewrite map_body_correspondence. reflexivity.
Qed.
Theorem optional_callsite_correspondence : forall store fuel declared child state,
  optional_group Projected store fuel declared child state = optional_group Original store fuel declared child state.
Proof.
  intros. unfold optional_group.
  destruct (O.checked_increment O.u32_max (O.next_group (effect state))); [|reflexivity].
  rewrite imported_optional_full_result_and_effects. reflexivity.
Qed.
Theorem dispatch_correspondence : forall store fuel declared sequence index node state,
  dispatch Projected store fuel declared sequence index node state =
  dispatch Original store fuel declared sequence index node state.
Proof.
  intros. destruct node; cbn [dispatch]; try reflexivity.
  change (operation_at (reader Projected store) operation) with (operation_at (reader Original store) operation).
  destruct (operation_at (reader Original store) operation) as [child|name separator source|a b c|left right|opaque]; try reflexivity.
  - apply optional_callsite_correspondence.
  - destruct source; [apply mapped_separator_correspondence|apply plain_separator_correspondence].
Qed.

Definition finish r state :=
  let ps := rule_positions state in let args := rule_actions state in
  if (match ps with [] => negb (leading_capture (rule_leading state)) | _ => false end)
    then None
  else match args with
  | [] => None
  | _ :: _ => Some
      {| label := spelling r (rule_label (rule r)); result_cat := spelling r (rule_category (rule r));
         shape_leading_category := leading_category (rule_leading state);
         shape_leading_ident_capture := leading_ident_capture (rule_leading state);
         positions := ps; shape_is_multi := is_multi (rule_declarations state);
         shape_has_binder := has_binder (rule_declarations state);
         action_arity := N.modulo (N.of_nat (List.length args)) 256%N;
         action_args := args; shape_body_cat := body_cat (rule_declarations state);
         shape_param_cats := param_cats (rule_declarations state) |} end.
Definition cast_representable state := representable state && N.leb (N.of_nat (List.length (rule_actions state))) O.u8_max.
Inductive WalkResult :=
| WalkAccepted (shape : BinderShape) (state : MainState)
| WalkRejected (state : MainState)
| WalkExhausted (index : nat) (skip_next : bool) (state : MainState)
| WalkOptionalExhausted (index : nat) (state : MainState) (configuration : @O.Configuration State).
Fixpoint walk fuel mode store optional_fuel declared sequence index skip_next state :=
  match fuel with
  | 0 => WalkExhausted index skip_next state
  | S remaining =>
    if Nat.eqb index (syntax_len (reader mode store) sequence) then
      match finish (reader mode store) state with
      | None => WalkRejected state
      | Some shape => WalkAccepted shape (with_effect state (effect state) (cast_representable state)) end
    else if skip_next then walk remaining mode store optional_fuel declared sequence (S index) false state
    else match syntax_at (reader mode store) sequence index with
      | None => WalkRejected state
      | Some node => match dispatch mode store optional_fuel declared sequence index node state with
        | MainContinue skip updated => walk remaining mode store optional_fuel declared sequence (S index) skip updated
        | MainRejected failed => WalkRejected failed
        | OptionalExhausted suspended configuration => WalkOptionalExhausted index suspended configuration end end end.
Theorem finite_main_walk_preserves_all_fields_and_effect_prefix : forall fuel store optional_fuel declared sequence index skip_next state,
  walk fuel Projected store optional_fuel declared sequence index skip_next state =
  walk fuel Original store optional_fuel declared sequence index skip_next state.
Proof.
  induction fuel; intros; cbn [walk]; [reflexivity|].
  change (syntax_len (reader Projected store) sequence) with (syntax_len (view_reader (project_store store)) sequence).
  rewrite syntax_length_correspondence.
  change (syntax_len (source_reader store) sequence) with (syntax_len (reader Original store) sequence).
  destruct (Nat.eqb index (syntax_len (reader Original store) sequence)); [reflexivity|].
  destruct skip_next; [apply IHfuel|].
  change (syntax_at (reader Projected store) sequence index) with (syntax_at (view_reader (project_store store)) sequence index).
  rewrite syntax_index_correspondence.
  change (syntax_at (source_reader store) sequence index) with (syntax_at (reader Original store) sequence index).
  destruct (syntax_at (reader Original store) sequence index) as [node|]; [|reflexivity].
  rewrite dispatch_correspondence.
  destruct (dispatch Original store optional_fuel declared sequence index node state); try reflexivity.
  apply IHfuel.
Qed.

Record Resolution := { resolved_category : nat; resolved_delimiters : option nat }.
Inductive Classification :=
| EarlyRejected (resolution_prefix : list Resolution) (state : State)
| DeclarationStopped (resolution_prefix : list Resolution) (state : State) (result : DeclarationResult)
| LeadingRejected (resolution_prefix : list Resolution) (state : State) (declarations : DeclarationState)
| Classified (resolution_prefix : list Resolution) (declarations : DeclarationState) (result : WalkResult).
Definition classify declaration_fuel main_fuel optional_fuel mode store initial_state :=
  let r := reader mode store in
  match term_context (rule r) with
  | None => EarlyRejected [] initial_state
  | Some tc => match syntax_pattern (rule r) with
    | None => EarlyRejected [] initial_state
    | Some sequence => if Nat.eqb (syntax_len r sequence) 0 then EarlyRejected [] initial_state else
      let category := rule_category (rule r) in
      let declared := declared_delimiters r category (categories r) in
      let resolved := [{| resolved_category := category; resolved_delimiters := declared |}] in
      match syntax_at r sequence 0 with
      | None | Some (Op _) => EarlyRejected resolved initial_state
      | Some anchor => if class5_excluded r tc sequence then EarlyRejected resolved initial_state else
          let initial_work := match T.reader_initial (terms r) tc false with Some work => work | None => [] end in
          match run_declarations declaration_fuel mode store (decl_state empty_declarations initial_work []) with
          | DeclAccepted ds => match leading r (declarations ds) anchor with
            | None => LeadingRejected resolved initial_state ds
            | Some first =>
                let start := {| rule_declarations := declarations ds; rule_leading := first;
                  rule_positions := []; rule_actions := leading_args first;
                  effect := {| O.next_group := 0%N; O.collection_slots := 0%N;
                    O.callback_state := initial_state; O.trace := [] |}; representable := true |} in
                Classified resolved ds (walk main_fuel mode store optional_fuel declared sequence 1 false start)
            end
          | other => DeclarationStopped resolved initial_state other end
      end end end.

Theorem original_main_classifier_source_correspondence : forall declaration_fuel main_fuel optional_fuel store initial_state,
  classify declaration_fuel main_fuel optional_fuel Projected store initial_state =
  classify declaration_fuel main_fuel optional_fuel Original store initial_state.
Proof.
  intros. unfold classify.
  change (term_context (rule (reader Projected store))) with (term_context (rule (reader Original store))).
  destruct (term_context (rule (reader Original store))) as [tc|]; [|reflexivity].
  change (syntax_pattern (rule (reader Projected store))) with (syntax_pattern (rule (reader Original store))).
  destruct (syntax_pattern (rule (reader Original store))) as [sequence|]; [|reflexivity].
  change (syntax_len (reader Projected store) sequence) with (syntax_len (view_reader (project_store store)) sequence).
  rewrite syntax_length_correspondence.
  change (syntax_len (source_reader store) sequence) with (syntax_len (reader Original store) sequence).
  destruct (Nat.eqb (syntax_len (reader Original store) sequence) 0); [reflexivity|].
  change (syntax_at (reader Projected store) sequence 0) with (syntax_at (view_reader (project_store store)) sequence 0).
  rewrite syntax_index_correspondence.
  change (syntax_at (source_reader store) sequence 0) with (syntax_at (reader Original store) sequence 0).
  destruct (syntax_at (reader Original store) sequence 0) as [anchor|]; [destruct anchor|];
    cbn beta iota zeta; try reflexivity.
  all: repeat rewrite declared_delimiters_correspondence; try reflexivity.
  all: rewrite class5_structural_gate_correspondence;
    destruct (class5_excluded (reader Original store) tc sequence); try reflexivity;
    change (T.reader_initial (terms (reader Projected store)) tc false)
      with (T.reader_initial (terms (reader Original store)) tc false);
    rewrite declaration_preorder_state_and_failure_correspondence;
    destruct (run_declarations declaration_fuel Original store
      (decl_state empty_declarations
        (match T.reader_initial (terms (reader Original store)) tc false with Some work => work | None => [] end) []));
    try reflexivity;
    rewrite leading_role_correspondence;
    destruct (leading (reader Original store) (declarations state) _); try reflexivity;
    rewrite finite_main_walk_preserves_all_fields_and_effect_prefix; reflexivity.
Qed.

(** Representability is a condition on THIS executed source trace, not a
    theorem that an external runtime image has been admitted in advance. *)
Definition classification_representable result := match result with
| Classified _ _ (WalkAccepted _ state) | Classified _ _ (WalkRejected state)
| Classified _ _ (WalkExhausted _ _ state) | Classified _ _ (WalkOptionalExhausted _ state _) => representable state
| _ => true end.
Theorem representable_source_execution_is_preserved : forall declaration_fuel main_fuel optional_fuel store initial_state,
  classification_representable (classify declaration_fuel main_fuel optional_fuel Original store initial_state) = true ->
  classify declaration_fuel main_fuel optional_fuel Projected store initial_state =
  classify declaration_fuel main_fuel optional_fuel Original store initial_state.
Proof. intros; apply original_main_classifier_source_correspondence. Qed.

End Effects.

Print Assumptions syntax_index_correspondence.
Print Assumptions raw_type_and_identifier_observations_correspond.
Print Assumptions imported_iterator_step_correspondence.
Print Assumptions declaration_preorder_state_and_failure_correspondence.
Print Assumptions class5_structural_gate_correspondence.
Print Assumptions map_body_correspondence.
Print Assumptions imported_optional_full_result_and_effects.
Print Assumptions main_collection_helper_and_slot_order.
Print Assumptions finite_main_walk_preserves_all_fields_and_effect_prefix.
Print Assumptions original_main_classifier_source_correspondence.
Print Assumptions representable_source_execution_is_preserved.

End BinderRuleProjection.
