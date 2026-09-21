(** Collection classifier relocation boundary.

    Source: macros/src/gen/runtime/wpda_codegen/collection.rs,
    CollectionShape and classify_collection. This is a concrete transcription
    of its bounded decision cases, not a new recognizer or parser algorithm.
    Source and view decisions below are separately defined. The shared list
    position law is reused from InfixClassifierProjection; its permissive Sep
    projection is NOT reused, because collection classification rejects Some
    source while infix classification ignores that field.

    Kind K is the existing collection kind, opaque here. Projection borrows it
    without invoking clone. Clone is modeled as a state transformer at the
    original site: after both optional lists exist and the context is exactly
    one Simple Collection with an immediate Base element, before syntax checks.
    Pair resolution is another state transformer, called once only after all
    structural checks. None is an accepted pair_separator, not rejection.

    Names and literals are exact observations, not reconstructed identifiers.
    Unsupported syntax/type/parameter payloads remain positional markers.
    The eight result fields and close-before-Sep check order are retained.
    Checks are trace events to distinguish early rejection sites; they do not
    model allocation, Rust references, unwinding, or extra callback internals.

    Source correspondence MUST retain the original pair callback expression:
    first declared type whose original Ident equals rule.category, then its
    collection_kind, then the existing kv_sep_for on THAT declared kind and
    delimiters. Neither parameter kind nor native carrier text replaces it.
    The callback algorithms, normalization, dispatch, runtime declaration order,
    and parser completeness are outside this proof. Rust differential tests and
    source review must check these remaining obligations and generic lifetimes.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import InfixClassifierProjection.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module CollectionClassifierProjection.
Module IP := InfixClassifierProjection.InfixClassifierProjection.

Section Kind.
Context {K : Type}.
Inductive SourceType :=
  | SourceBase (name : string)
  | SourceCollection (kind : K) (element : SourceType)
  | SourceOtherType (opaque : nat).
Inductive SourceParam :=
  | SourceSimple (name : string) (ty : SourceType)
  | SourceOtherParam (opaque : nat).
Inductive ParamView :=
  | SimpleCollection (name : string) (kind : K) (element_base : option string)
  | OtherParam.
Definition immediate_base ty :=
  match ty with SourceBase name => Some name | _ => None end.
Definition project_param param := match param with
  | SourceSimple name (SourceCollection kind element) =>
      SimpleCollection name kind (immediate_base element)
  | _ => OtherParam end.
Definition project_syntax syntax := match syntax with
  | IP.SourceLiteral text => IP.Literal text
  | IP.SourceParamRef name => IP.Param name
  | IP.SourceSep name separator None => IP.Sep name separator
  | _ => IP.OtherSyntax end.

Record SourceRule := {
  source_label : string;
  source_context : option (list SourceParam);
  source_pattern : option (list IP.SourceSyntax)
}.
Record RuleView := {
  view_label : string;
  view_context : option (list ParamView);
  view_pattern : option (list IP.SyntaxView)
}.
Definition project_rule rule :=
  {| view_label := source_label rule;
     view_context := option_map (map project_param) (source_context rule);
     view_pattern := option_map (map project_syntax) (source_pattern rule) |}.

Theorem optional_lists_and_label_preserved : forall rule,
  view_label (project_rule rule) = source_label rule /\
  view_context (project_rule rule) = option_map (map project_param) (source_context rule) /\
  view_pattern (project_rule rule) = option_map (map project_syntax) (source_pattern rule).
Proof. intros; repeat split; reflexivity. Qed.
Theorem parameter_positions_preserved : forall params index,
  List.length (map project_param params) = List.length params /\
  nth_error (map project_param params) index =
    option_map project_param (nth_error params index).
Proof. intros; split; [apply length_map|apply IP.map_nth_exact]. Qed.
Theorem syntax_positions_preserved : forall syntax index,
  List.length (map project_syntax syntax) = List.length syntax /\
  nth_error (map project_syntax syntax) index =
    option_map project_syntax (nth_error syntax index).
Proof. intros; split; [apply length_map|apply IP.map_nth_exact]. Qed.
Theorem source_bearing_sep_is_not_erased_to_accepted_sep : forall name sep source,
  project_syntax (IP.SourceSep name sep (Some source)) = IP.OtherSyntax.
Proof. reflexivity. Qed.
Theorem nested_element_is_not_flattened : forall name kind inner_kind element,
  project_param (SourceSimple name (SourceCollection kind (SourceCollection inner_kind element))) =
    SimpleCollection name kind None.
Proof. reflexivity. Qed.

Definition source_param_gate context : option (string * K * string) :=
  match context with
  | [SourceSimple name (SourceCollection kind (SourceBase element))] =>
      Some (name, kind, element)
  | _ => None end.
Definition view_param_gate context : option (string * K * string) :=
  match context with
  | [SimpleCollection name kind (Some element)] => Some (name, kind, element)
  | _ => None end.
Lemma param_gate_correspondence : forall context,
  view_param_gate (map project_param context) = source_param_gate context.
Proof.
  intros [|param [|second rest]]; [reflexivity| |].
  - destruct param as [name ty|opaque]; [destruct ty as [base|kind element|opaque]|];
      try reflexivity. destruct element; reflexivity.
  - destruct param as [name ty|opaque]; [destruct ty as [base|kind element|opaque]|];
      try reflexivity. destruct element; reflexivity.
Qed.

Inductive Event := CloneKind | CheckOpen | CheckParen | CheckClose | CheckSep | PairCall.
Definition source_literal syntax := match syntax with
  | IP.SourceLiteral text => Some text | _ => None end.
Definition view_literal syntax := match syntax with
  | IP.Literal text => Some text | _ => None end.
Definition source_separator name syntax := match syntax with
  | IP.SourceSep reference separator None =>
      if String.eqb reference name then Some separator else None
  | _ => None end.
Definition view_separator name syntax := match syntax with
  | IP.Sep reference separator =>
      if String.eqb reference name then Some separator else None
  | _ => None end.
Lemma literal_projection : forall syntax,
  view_literal (project_syntax syntax) = source_literal syntax.
Proof. destruct syntax; try reflexivity. destruct opaque_source; reflexivity. Qed.
Lemma separator_projection : forall name syntax,
  view_separator name (project_syntax syntax) = source_separator name syntax.
Proof. intros name syntax; destruct syntax; try reflexivity. destruct opaque_source; reflexivity. Qed.

Record SyntaxParts := {
  open_text : string; split_open : bool; close_text : string; separator_text : string
}.
Definition gate_result := (option SyntaxParts * list Event)%type.
Definition prepend_check event (result : gate_result) : gate_result :=
  (fst result, event :: snd result).
Definition source_finish open split name sep close : gate_result :=
  match source_literal close with
  | None => (None, [CheckClose])
  | Some closing => match source_separator name sep with
      | None => (None, [CheckClose; CheckSep])
      | Some separator =>
          (Some {| open_text := open; split_open := split;
                   close_text := closing; separator_text := separator |}, [CheckClose; CheckSep])
      end end.
Definition view_finish open split name sep close : gate_result :=
  match view_literal close with
  | None => (None, [CheckClose])
  | Some closing => match view_separator name sep with
      | None => (None, [CheckClose; CheckSep])
      | Some separator =>
          (Some {| open_text := open; split_open := split;
                   close_text := closing; separator_text := separator |}, [CheckClose; CheckSep])
      end end.
Lemma finish_correspondence : forall open split name sep close,
  view_finish open split name (project_syntax sep) (project_syntax close) =
  source_finish open split name sep close.
Proof. intros; unfold view_finish, source_finish; now rewrite literal_projection, separator_projection. Qed.

Definition source_syntax_gate name syntax : gate_result :=
  match syntax with
  | [open; sep; close] => match source_literal open with
      | None => (None, [CheckOpen])
      | Some text => prepend_check CheckOpen (source_finish text false name sep close) end
  | [open; paren; sep; close] => match source_literal open with
      | None => (None, [CheckOpen])
      | Some text => match source_literal paren with
          | Some token => if String.eqb token "("
              then prepend_check CheckOpen (prepend_check CheckParen
                (source_finish text true name sep close))
              else (None, [CheckOpen; CheckParen])
          | None => (None, [CheckOpen; CheckParen]) end end
  | _ => (None, []) end.
Definition view_syntax_gate name syntax : gate_result :=
  match syntax with
  | [open; sep; close] => match view_literal open with
      | None => (None, [CheckOpen])
      | Some text => prepend_check CheckOpen (view_finish text false name sep close) end
  | [open; paren; sep; close] => match view_literal open with
      | None => (None, [CheckOpen])
      | Some text => match view_literal paren with
          | Some token => if String.eqb token "("
              then prepend_check CheckOpen (prepend_check CheckParen
                (view_finish text true name sep close))
              else (None, [CheckOpen; CheckParen])
          | None => (None, [CheckOpen; CheckParen]) end end
  | _ => (None, []) end.
Theorem syntax_gate_order_correspondence : forall name syntax,
  view_syntax_gate name (map project_syntax syntax) = source_syntax_gate name syntax.
Proof.
  intros name [|a [|b [|c [|d [|e rest]]]]]; try reflexivity.
  - change ((match view_literal (project_syntax a) with
      | None => (None, [CheckOpen])
      | Some text => prepend_check CheckOpen
          (view_finish text false name (project_syntax b) (project_syntax c)) end) =
      (match source_literal a with
      | None => (None, [CheckOpen])
      | Some text => prepend_check CheckOpen (source_finish text false name b c) end)).
    rewrite literal_projection. destruct (source_literal a); [|reflexivity].
    now rewrite finish_correspondence.
  - change ((match view_literal (project_syntax a) with
      | None => (None, [CheckOpen])
      | Some text => match view_literal (project_syntax b) with
          | Some token => if String.eqb token "("
              then prepend_check CheckOpen (prepend_check CheckParen
                (view_finish text true name (project_syntax c) (project_syntax d)))
              else (None, [CheckOpen; CheckParen])
          | None => (None, [CheckOpen; CheckParen]) end end) =
      (match source_literal a with
      | None => (None, [CheckOpen])
      | Some text => match source_literal b with
          | Some token => if String.eqb token "("
              then prepend_check CheckOpen (prepend_check CheckParen
                (source_finish text true name c d))
              else (None, [CheckOpen; CheckParen])
          | None => (None, [CheckOpen; CheckParen]) end end)).
    rewrite !literal_projection. destruct (source_literal a); [|reflexivity].
    destruct (source_literal b); [|reflexivity].
    now rewrite finish_correspondence.
Qed.

Record Descriptor := {
  open_token : string; has_synth_paren : bool; close : string;
  separator : string; pair_separator : option string; element_cat : string;
  coll_kind : K; label : string
}.
Definition make_descriptor rule_label kind element parts pair :=
  {| open_token := open_text parts; has_synth_paren := split_open parts;
     close := close_text parts; separator := separator_text parts;
     pair_separator := pair; element_cat := element; coll_kind := kind; label := rule_label |}.

Section Callbacks.
Context {State : Type}.
Variable clone_kind : K -> State -> K * State.
Variable resolve_pair : State -> option string * State.
Record Observation := {
  descriptor : option Descriptor; final_state : State; trace : list Event
}.
Definition rejected state := {| descriptor := None; final_state := state; trace := [] |}.
Definition finish_classification rule_label kind element (gate : gate_result) state :=
  let '(shape, checks) := gate in match shape with
  | None => {| descriptor := None; final_state := state; trace := CloneKind :: checks |}
  | Some parts => let '(pair_value, next) := resolve_pair state in
      {| descriptor := Some (make_descriptor rule_label kind element parts pair_value);
         final_state := next; trace := CloneKind :: (checks ++ [PairCall])%list |}
  end.
Definition source_classify rule state :=
  match source_context rule with
  | None => rejected state
  | Some context => match source_pattern rule with
      | None => rejected state
      | Some syntax => match source_param_gate context with
          | None => rejected state
          | Some (name, kind, element) => let '(copied, next) := clone_kind kind state in
              finish_classification (source_label rule) copied element
                (source_syntax_gate name syntax) next
          end end end.
Definition view_classify rule state :=
  match view_context rule with
  | None => rejected state
  | Some context => match view_pattern rule with
      | None => rejected state
      | Some syntax => match view_param_gate context with
          | None => rejected state
          | Some (name, kind, element) => let '(copied, next) := clone_kind kind state in
              finish_classification (view_label rule) copied element
                (view_syntax_gate name syntax) next
          end end end.

Theorem classifier_projection_preserves_result_state_and_trace : forall rule state,
  view_classify (project_rule rule) state = source_classify rule state.
Proof.
  intros [rule_label context syntax] state.
  destruct context as [context|]; [destruct syntax as [syntax|]|]; try reflexivity.
  unfold view_classify, source_classify; cbn [project_rule view_context view_pattern view_label
    source_context source_pattern source_label option_map].
  rewrite param_gate_correspondence.
  destruct (source_param_gate context) as [[[name kind] element]|]; [|reflexivity].
  destruct (clone_kind kind state). now rewrite syntax_gate_order_correspondence.
Qed.

Theorem invalid_parameter_never_clones_or_resolves : forall rule context syntax state,
  source_context rule = Some context -> source_pattern rule = Some syntax ->
  source_param_gate context = None -> source_classify rule state = rejected state.
Proof. intros; unfold source_classify; now rewrite H, H0, H1. Qed.
Theorem absent_pattern_never_clones : forall rule state,
  source_pattern rule = None -> source_classify rule state = rejected state.
Proof. intros; unfold source_classify; destruct (source_context rule); [now rewrite H|reflexivity]. Qed.
Theorem clone_precedes_even_syntax_rejection : forall rule context syntax name kind element state copied next checks,
  source_context rule = Some context -> source_pattern rule = Some syntax ->
  source_param_gate context = Some (name, kind, element) ->
  clone_kind kind state = (copied, next) -> source_syntax_gate name syntax = (None, checks) ->
  source_classify rule state =
    {| descriptor := None; final_state := next; trace := CloneKind :: checks |}.
Proof. intros; unfold source_classify; rewrite H, H0, H1, H2, H3; reflexivity. Qed.
Theorem pair_none_is_success_and_called_once : forall rule_label kind element parts checks state next,
  resolve_pair state = (None, next) ->
  finish_classification rule_label kind element (Some parts, checks) state =
    {| descriptor := Some (make_descriptor rule_label kind element parts None);
       final_state := next; trace := CloneKind :: (checks ++ [PairCall])%list |}.
Proof. intros; unfold finish_classification; now rewrite H. Qed.
End Callbacks.
End Kind.

Print Assumptions parameter_positions_preserved.
Print Assumptions syntax_positions_preserved.
Print Assumptions source_bearing_sep_is_not_erased_to_accepted_sep.
Print Assumptions nested_element_is_not_flattened.
Print Assumptions syntax_gate_order_correspondence.
Print Assumptions classifier_projection_preserves_result_state_and_trace.
Print Assumptions invalid_parameter_never_clones_or_resolves.
Print Assumptions absent_pattern_never_clones.
Print Assumptions clone_precedes_even_syntax_rejection.
Print Assumptions pair_none_is_success_and_called_once.
End CollectionClassifierProjection.
