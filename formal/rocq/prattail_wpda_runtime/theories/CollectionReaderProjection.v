(** Shallow collection-reader adapter and lazy declaration correspondence.

    This interface model reuses CollectionClassifierProjection, including its
    original clone/check/pair-callback order. It does not define a classifier.
    Reader observations below are mathematical observations of valid immutable
    handles, not a runtime reconstruction of source syntax. Their correctness
    is a precondition discharged by the existing AST/retained-reader laws and
    differential tests. Collection kinds are opaque borrowed observations; no
    clone operation occurs in projection. Immediate Base and source-free Sep
    discrimination are precisely the existing collection projection, NOT the
    more permissive infix Sep projection.

    Declaration equality is supplied independently of spelling. Lookup finds
    the first matching declaration before inspecting its optional collection.
    Collection classification uses that declaration's kind. Binder slots use
    their own kind with the declared spelling; these are distinct operations.
    The separator callback is lazy and invoked only for map kinds. Empty text
    is a declared spelling, not an absent value.

    The owned entry requires an already validated reader and valid rule handle.
    Missing declaration header is a typed error, not an empty lookup. A single
    whole-domain admission precedes projection, classification, header scan and
    copies; no sub-operation is performed on refusal. Admission may update its
    own accounting state. This model does not derive a numeric resource bound,
    validate arbitrary readers, or prove Rust allocation/lifetime behavior.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import CollectionClassifierProjection.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module CollectionReaderProjection.
Module C := CollectionClassifierProjection.CollectionClassifierProjection.
Module I := C.IP.

Section Reader.
Context {K P S : Type}.
Variable read_param : P -> @C.SourceParam K.
Variable read_syntax : S -> I.SourceSyntax.
Record RuleHandles := {
  rule_label : string;
  context_handles : option (list P);
  syntax_handles : option (list S)
}.
Definition observed_source rule : @C.SourceRule K :=
  {| C.source_label := rule_label rule;
     C.source_context := option_map (map read_param) (context_handles rule);
     C.source_pattern := option_map (map read_syntax) (syntax_handles rule) |}.
Definition reader_projection rule : @C.RuleView K :=
  {| C.view_label := rule_label rule;
     C.view_context := option_map
       (map (fun p => C.project_param (read_param p))) (context_handles rule);
     C.view_pattern := option_map
       (map (fun s => C.project_syntax (read_syntax s))) (syntax_handles rule) |}.

Theorem reader_projection_is_original : forall rule,
  reader_projection rule = C.project_rule (observed_source rule).
Proof.
  intros [label params syntax]. destruct params as [params|];
    destruct syntax as [syntax|];
    unfold reader_projection, observed_source, C.project_rule; cbn;
    rewrite ?map_map; reflexivity.
Qed.
Theorem context_positions : forall params index,
  List.length (map (fun p => C.project_param (read_param p)) params) =
    List.length params /\
  nth_error (map (fun p => C.project_param (read_param p)) params) index =
    option_map (fun p => C.project_param (read_param p)) (nth_error params index).
Proof. intros; split; [apply length_map|apply I.map_nth_exact]. Qed.
Theorem syntax_positions : forall syntax index,
  List.length (map (fun s => C.project_syntax (read_syntax s)) syntax) =
    List.length syntax /\
  nth_error (map (fun s => C.project_syntax (read_syntax s)) syntax) index =
    option_map (fun s => C.project_syntax (read_syntax s)) (nth_error syntax index).
Proof. intros; split; [apply length_map|apply I.map_nth_exact]. Qed.
Theorem absent_context_is_not_present_empty :
  option_map (map (fun p => C.project_param (read_param p))) None <>
  option_map (map (fun p => C.project_param (read_param p))) (Some []).
Proof. discriminate. Qed.
Theorem source_sep_stays_other : forall item name separator source,
  read_syntax item = I.SourceSep name separator (Some source) ->
  C.project_syntax (read_syntax item) = I.OtherSyntax.
Proof. intros item name separator source H; rewrite H; reflexivity. Qed.
Theorem kind_is_retained_and_element_is_immediate : forall item name kind nested element,
  read_param item = C.SourceSimple name
    (C.SourceCollection kind (C.SourceCollection nested element)) ->
  C.project_param (read_param item) = C.SimpleCollection name kind None.
Proof. intros item name kind nested element H; rewrite H; reflexivity. Qed.
Theorem existing_classifier_reused : forall State
  (clone_kind : K -> State -> K * State)
  (resolve_pair : State -> option string * State) rule state,
  C.view_classify clone_kind resolve_pair (reader_projection rule) state =
  C.source_classify clone_kind resolve_pair (observed_source rule) state.
Proof.
  intros; rewrite reader_projection_is_original.
  apply C.classifier_projection_preserves_result_state_and_trace.
Qed.
End Reader.

Inductive Kind := Vec | HashBag | HashSet | HashMap | PathMap.
Definition is_map kind := match kind with HashMap | PathMap => true | _ => false end.
Definition declared_or_default declared :=
  match declared with Some text => text | None => ":" end.
Definition original_kv kind declared : option string :=
  if is_map kind then Some (declared_or_default declared) else None.

Section LazySeparator.
Context {State : Type}.
Variable declared : State -> option string * State.
Definition lazy_kv kind state : option string * State * nat :=
  if is_map kind then
    let '(spelling, next) := declared state in
    (Some (declared_or_default spelling), next, 1)
  else (None, state, 0).
Theorem lazy_kv_matches_original : forall kind state spelling next,
  declared state = (spelling, next) ->
  lazy_kv kind state =
    if is_map kind then (original_kv kind spelling, next, 1)
    else (original_kv kind spelling, state, 0).
Proof.
  intros kind state spelling next H; destruct kind;
    cbn [lazy_kv is_map original_kv]; try reflexivity; now rewrite H.
Qed.
Theorem sequence_never_calls_declared : forall kind state,
  is_map kind = false -> lazy_kv kind state = (None, state, 0).
Proof. intros kind state H; unfold lazy_kv; now rewrite H. Qed.
Theorem map_calls_declared_once : forall kind state spelling next,
  is_map kind = true -> declared state = (spelling, next) ->
  lazy_kv kind state = (Some (declared_or_default spelling), next, 1).
Proof. intros kind state spelling next H D; unfold lazy_kv; now rewrite H, D. Qed.
End LazySeparator.
Theorem empty_declared_spelling_is_preserved : forall kind,
  is_map kind = true -> original_kv kind (Some "") = Some "".
Proof. intros kind H; unfold original_kv; now rewrite H. Qed.
Theorem absent_spelling_gets_colon : forall kind,
  is_map kind = true -> original_kv kind None = Some ":".
Proof. intros kind H; unfold original_kv; now rewrite H. Qed.

Section Declarations.
Context {Name : Type}.
Variable names_equal : Name -> Name -> bool.
Record Declaration := {
  declaration_name : Name;
  declaration_collection : option (Kind * option string)
}.
Definition matching target row := names_equal (declaration_name row) target.
Definition first_collection target rows :=
  match find (matching target) rows with
  | Some row => declaration_collection row
  | None => None end.
Fixpoint source_first_collection target rows := match rows with
  | [] => None
  | row :: tail => if names_equal (declaration_name row) target
      then declaration_collection row else source_first_collection target tail
  end.
Theorem first_declaration_lookup_correspondence : forall target rows,
  first_collection target rows = source_first_collection target rows.
Proof.
  intros target rows; induction rows as [|row tail IH]; [reflexivity|].
  unfold first_collection, matching in *; cbn [find source_first_collection].
  destruct (names_equal (declaration_name row) target); [reflexivity|exact IH].
Qed.
Theorem first_match_noncollection_blocks_later : forall target row tail,
  names_equal (declaration_name row) target = true ->
  declaration_collection row = None ->
  first_collection target (row :: tail) = None.
Proof.
  intros target row tail H N; unfold first_collection, matching;
    cbn [find]; now rewrite H, N.
Qed.
Theorem nonmatching_row_does_not_block : forall target row tail,
  names_equal (declaration_name row) target = false ->
  first_collection target (row :: tail) = first_collection target tail.
Proof.
  intros target row tail H; unfold first_collection, matching;
    cbn [find]; now rewrite H.
Qed.
Definition collection_pair target rows := match first_collection target rows with
  | Some (kind, spelling) => original_kv kind spelling
  | None => None end.
Definition binder_slot_pair slot_kind target rows :=
  original_kv slot_kind
    (match first_collection target rows with
     | Some (_, spelling) => spelling | None => None end).
Theorem missing_collection_declaration_is_not_map_default : forall target rows,
  first_collection target rows = None -> collection_pair target rows = None.
Proof. intros target rows H; unfold collection_pair; now rewrite H. Qed.
Theorem collection_uses_result_kind : forall target rows kind spelling,
  first_collection target rows = Some (kind, spelling) ->
  collection_pair target rows = original_kv kind spelling.
Proof. intros target rows kind spelling H; unfold collection_pair; now rewrite H. Qed.
Theorem sequence_slot_does_not_inherit_result_map : forall target rows,
  binder_slot_pair Vec target rows = None.
Proof. reflexivity. Qed.
Theorem missing_declaration_still_defaults_map_slot : forall target rows,
  first_collection target rows = None ->
  binder_slot_pair HashMap target rows = Some ":".
Proof. intros target rows H; unfold binder_slot_pair; now rewrite H. Qed.
End Declarations.

Section Admission.
Context {Header State Result : Type}.
Inductive Outcome := MissingDeclarations | Refused | Completed (value : Result).
Inductive EntryEvent := MissingHeader | Denied | Admitted | Worker.
Variable admit : Header -> State -> bool * State.
Variable worker : Header -> State -> Result * State.
Definition owned_entry header state : Outcome * State * list EntryEvent :=
  match header with
  | None => (MissingDeclarations, state, [MissingHeader])
  | Some declarations =>
      let '(allowed, paid) := admit declarations state in
      if allowed then let '(value, final) := worker declarations paid in
        (Completed value, final, [Admitted; Worker])
      else (Refused, paid, [Denied])
  end.
Theorem missing_header_is_error_before_admission : forall state,
  owned_entry None state = (MissingDeclarations, state, [MissingHeader]).
Proof. reflexivity. Qed.
Theorem denied_has_no_worker_or_partial_result : forall header state paid,
  admit header state = (false, paid) ->
  owned_entry (Some header) state = (Refused, paid, [Denied]).
Proof. intros header state paid H; unfold owned_entry; now rewrite H. Qed.
Theorem admitted_calls_same_worker_once : forall header state paid value final,
  admit header state = (true, paid) -> worker header paid = (value, final) ->
  owned_entry (Some header) state = (Completed value, final, [Admitted; Worker]).
Proof. intros header state paid value final A W; unfold owned_entry; now rewrite A, W. Qed.
End Admission.

Print Assumptions reader_projection_is_original.
Print Assumptions context_positions.
Print Assumptions syntax_positions.
Print Assumptions absent_context_is_not_present_empty.
Print Assumptions source_sep_stays_other.
Print Assumptions kind_is_retained_and_element_is_immediate.
Print Assumptions existing_classifier_reused.
Print Assumptions lazy_kv_matches_original.
Print Assumptions sequence_never_calls_declared.
Print Assumptions map_calls_declared_once.
Print Assumptions empty_declared_spelling_is_preserved.
Print Assumptions absent_spelling_gets_colon.
Print Assumptions first_declaration_lookup_correspondence.
Print Assumptions first_match_noncollection_blocks_later.
Print Assumptions nonmatching_row_does_not_block.
Print Assumptions missing_collection_declaration_is_not_map_default.
Print Assumptions collection_uses_result_kind.
Print Assumptions sequence_slot_does_not_inherit_result_map.
Print Assumptions missing_declaration_still_defaults_map_slot.
Print Assumptions missing_header_is_error_before_admission.
Print Assumptions denied_has_no_worker_or_partial_result.
Print Assumptions admitted_calls_same_worker_once.
End CollectionReaderProjection.
