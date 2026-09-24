(** Exact reader interface for the original unary-prefix helper.

    Source: ast/src/grammar_shapes.rs::classify_unary_prefix_shape. This
    helper is not a new atomic classifier: AtomicClassifierProjection keeps
    the original atomic branch ordering and calls this helper lazily.

    Source order is context presence, syntax presence, context length, syntax
    length (short-circuited), immediate Simple parameter, parameter spelling
    copy, immediate Base type, operand spelling copy, category comparison,
    literal read and trigger copy, then final parameter comparison. In
    particular the trigger is copied even if the final parameter mismatches.
    No Optional children, collection elements or type children are traversed.

    Names/types/sequence IDs remain opaque handles. Term parameter observations
    reuse TermParamReaderProjection; no second traversal is defined. The source
    and retained readers below are mathematical views, not allocated syntax.
    Ident-to-string comparison means exact rendered spelling, including r#;
    it is not source name equality_class. Actual AST comparisons retain the
    original Ident-to-str operations, while retained names use captured spelling.

    Trace entries denote source observation/copy sites, not physical allocation
    costs. Arbitrary unlawful readers, allocation failure, resource admission,
    Rust lifetime/extraction and full parser completeness are outside this model.
    Existing atomic/legacy-item laws are composed, not reimplemented here.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import TermParamReaderProjection
  AtomicClassifierProjection InfixClassifierProjection.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module UnaryPrefixReaderProjection.
Module T := TermParamReaderProjection.TermParamReaderProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.
Module I := InfixClassifierProjection.InfixClassifierProjection.

Inductive Event := ReadContext | ReadSyntax | ContextLength | SyntaxLength
  | ParamIndex | ObserveParam | CopyParamName | ReadBase | CopyOperand
  | CompareCategory | ReadLiteral | CopyTrigger | CompareParam.
Definition Observation := (option A.Unary * list Event)%type.
Definition prepend events (observed : Observation) : Observation :=
  (fst observed, (events ++ snd observed)%list).
Definition refuse : Observation := (None, []).
Record Reader := {
  context : option nat;
  syntax : option nat;
  parameters : T.Reader;
  syntax_len : nat -> nat;
  base_name : nat -> option nat;
  spelling : nat -> string;
  category_matches : string -> bool;
  literal_at : nat -> nat -> option string;
  param_matches : nat -> nat -> string -> bool
}.

Definition run reader : Observation :=
  prepend [ReadContext] (match context reader with
  | None => refuse
  | Some tc => prepend [ReadSyntax] (match syntax reader with
    | None => refuse
    | Some sp => prepend [ContextLength]
      (if Nat.eqb (T.params_len (parameters reader) tc) 1 then
        prepend [SyntaxLength] (if Nat.eqb (syntax_len reader sp) 2 then
          prepend [ParamIndex] (match T.param_at (parameters reader) tc 0 with
          | None => refuse
          | Some handle => prepend [ObserveParam]
            (match T.param (parameters reader) handle with
            | T.Simple name ty =>
                let param_name := spelling reader name in
                prepend [CopyParamName; ReadBase] (match base_name reader ty with
                | None => refuse
                | Some operand =>
                    let operand_category := spelling reader operand in
                    prepend [CopyOperand; CompareCategory]
                      (if category_matches reader operand_category then
                        prepend [ReadLiteral] (match literal_at reader sp 0 with
                        | None => refuse
                        | Some trigger => prepend [CopyTrigger; CompareParam]
                          (if param_matches reader sp 1 param_name then
                             (Some {| A.unary_trigger := trigger;
                                      A.unary_operand := operand_category |}, [])
                           else refuse) end)
                       else refuse) end)
            | _ => refuse end) end)
        else refuse)
      else refuse) end) end).

Record Agree left right : Prop := {
  agree_context : context left = context right;
  agree_syntax : syntax left = syntax right;
  agree_param_length : forall p, T.params_len (parameters left) p = T.params_len (parameters right) p;
  agree_param_index : forall p i, T.param_at (parameters left) p i = T.param_at (parameters right) p i;
  agree_param : forall p, T.param (parameters left) p = T.param (parameters right) p;
  agree_syntax_length : forall s, syntax_len left s = syntax_len right s;
  agree_base : forall t, base_name left t = base_name right t;
  agree_spelling : forall n, spelling left n = spelling right n;
  agree_category : forall n, category_matches left n = category_matches right n;
  agree_literal : forall s i, literal_at left s i = literal_at right s i;
  agree_reference : forall s i n, param_matches left s i n = param_matches right s i n
}.
Theorem observations_preserve_result_and_copy_trace : forall left right,
  Agree left right -> run left = run right.
Proof.
  intros left right [C S PL PI P SL B N Cat L Ref].
  unfold run; rewrite C; destruct (context right) as [tc|]; [|reflexivity].
  rewrite S; destruct (syntax right) as [sp|]; [|reflexivity].
  rewrite PL; destruct (Nat.eqb (T.params_len (parameters right) tc) 1); [|reflexivity].
  rewrite SL; destruct (Nat.eqb (syntax_len right sp) 2); [|reflexivity].
  rewrite PI; destruct (T.param_at (parameters right) tc 0) as [handle|]; [|reflexivity].
  rewrite P; destruct (T.param (parameters right) handle); try reflexivity.
  rewrite N, B; destruct (base_name right ty) as [operand|]; [|reflexivity].
  rewrite N, Cat; destruct (category_matches right (spelling right operand)); [|reflexivity].
  rewrite L; destruct (literal_at right sp 0); [|reflexivity].
  now rewrite Ref.
Qed.

Inductive SourceSyntax := SLiteral (text : string) | SParam (name : nat) | SOther (opaque : nat).
Inductive SyntaxView := Literal (text : string) | Param (name : nat) | Other.
Definition project_syntax node := match node with
  | SLiteral text => Literal text | SParam name => Param name | SOther _ => Other end.
Definition source_literal nodes index := match nth_error nodes index with
  | Some (SLiteral text) => Some text | _ => None end.
Definition view_literal nodes index := match nth_error nodes index with
  | Some (Literal text) => Some text | _ => None end.
Definition source_param_matches names nodes index expected := match nth_error nodes index with
  | Some (SParam name) => String.eqb (names name) expected | _ => false end.
Definition view_param_matches names nodes index expected := match nth_error nodes index with
  | Some (Param name) => String.eqb (names name) expected | _ => false end.
Lemma literal_position_preserved : forall nodes index,
  view_literal (map project_syntax nodes) index = source_literal nodes index.
Proof.
  intros nodes index; unfold view_literal, source_literal; rewrite I.map_nth_exact.
  destruct (nth_error nodes index) as [node|]; [destruct node|]; reflexivity.
Qed.
Lemma parameter_position_and_spelling_preserved : forall names nodes index expected,
  view_param_matches names (map project_syntax nodes) index expected =
  source_param_matches names nodes index expected.
Proof.
  intros names nodes index expected; unfold view_param_matches, source_param_matches.
  rewrite I.map_nth_exact.
  destruct (nth_error nodes index) as [node|]; [destruct node|]; reflexivity.
Qed.

Record SourceStore := {
  source_terms : T.SourceStore;
  source_context : option nat;
  source_syntax : option nat;
  source_nodes : nat -> list SourceSyntax;
  source_base_name : nat -> option nat;
  source_spelling : nat -> string;
  source_category : nat
}.
Definition source_reader store :=
  {| context := source_context store; syntax := source_syntax store;
     parameters := T.source_reader (source_terms store);
     syntax_len := fun s => List.length (source_nodes store s);
     base_name := source_base_name store; spelling := source_spelling store;
     category_matches := fun text => String.eqb (source_spelling store (source_category store)) text;
     literal_at := fun s => source_literal (source_nodes store s);
     param_matches := fun s => source_param_matches (source_spelling store) (source_nodes store s) |}.
Definition retained_reader store :=
  {| context := source_context store; syntax := source_syntax store;
     parameters := T.view_reader (T.project_store (source_terms store));
     syntax_len := fun s => List.length (map project_syntax (source_nodes store s));
     base_name := source_base_name store; spelling := source_spelling store;
     category_matches := fun text => String.eqb (source_spelling store (source_category store)) text;
     literal_at := fun s => view_literal (map project_syntax (source_nodes store s));
     param_matches := fun s => view_param_matches (source_spelling store) (map project_syntax (source_nodes store s)) |}.
Theorem retained_reader_matches_original_observations : forall store,
  Agree (retained_reader store) (source_reader store).
Proof.
  intros store; constructor; intros; try reflexivity.
  - apply length_map.
  - apply literal_position_preserved.
  - apply parameter_position_and_spelling_preserved.
Qed.
Theorem retained_unary_is_original_helper : forall store,
  run (retained_reader store) = run (source_reader store).
Proof. intros; apply observations_preserve_result_and_copy_trace, retained_reader_matches_original_observations. Qed.

Theorem absent_context_does_not_read_syntax : forall reader,
  context reader = None -> run reader = (None, [ReadContext]).
Proof. intros reader H; unfold run; rewrite H; reflexivity. Qed.
Theorem absent_syntax_stops_before_lengths : forall reader tc,
  context reader = Some tc -> syntax reader = None ->
  run reader = (None, [ReadContext; ReadSyntax]).
Proof. intros reader tc C S; unfold run; rewrite C, S; reflexivity. Qed.
Theorem wrong_context_length_short_circuits_syntax_length : forall reader tc sp,
  context reader = Some tc -> syntax reader = Some sp ->
  Nat.eqb (T.params_len (parameters reader) tc) 1 = false ->
  run reader = (None, [ReadContext; ReadSyntax; ContextLength]).
Proof. intros reader tc sp C S L; unfold run; rewrite C, S, L; reflexivity. Qed.
Theorem optional_parameter_does_not_descend : forall reader tc sp handle children,
  context reader = Some tc -> syntax reader = Some sp ->
  T.params_len (parameters reader) tc = 1 -> syntax_len reader sp = 2 ->
  T.param_at (parameters reader) tc 0 = Some handle ->
  T.param (parameters reader) handle = T.Optional children ->
  run reader = (None, [ReadContext; ReadSyntax; ContextLength; SyntaxLength; ParamIndex; ObserveParam]).
Proof. intros reader tc sp handle children C S PL SL PI P; unfold run; rewrite C, S, PL, SL, PI, P; reflexivity. Qed.
Theorem trigger_is_copied_before_final_parameter_mismatch : forall reader tc sp handle name ty operand trigger,
  context reader = Some tc -> syntax reader = Some sp ->
  T.params_len (parameters reader) tc = 1 -> syntax_len reader sp = 2 ->
  T.param_at (parameters reader) tc 0 = Some handle ->
  T.param (parameters reader) handle = T.Simple name ty ->
  base_name reader ty = Some operand ->
  category_matches reader (spelling reader operand) = true ->
  literal_at reader sp 0 = Some trigger ->
  param_matches reader sp 1 (spelling reader name) = false ->
  run reader = (None,
    [ReadContext; ReadSyntax; ContextLength; SyntaxLength; ParamIndex; ObserveParam;
     CopyParamName; ReadBase; CopyOperand; CompareCategory; ReadLiteral; CopyTrigger; CompareParam]).
Proof.
  intros reader tc sp handle name ty operand trigger C S PL SL PI P B Cat L Ref.
  unfold run; rewrite C, S, PL, SL, PI, P, B, Cat, L, Ref; reflexivity.
Qed.
Theorem completed_helper_keeps_both_original_fields : forall reader tc sp handle name ty operand trigger,
  context reader = Some tc -> syntax reader = Some sp ->
  T.params_len (parameters reader) tc = 1 -> syntax_len reader sp = 2 ->
  T.param_at (parameters reader) tc 0 = Some handle ->
  T.param (parameters reader) handle = T.Simple name ty ->
  base_name reader ty = Some operand ->
  category_matches reader (spelling reader operand) = true ->
  literal_at reader sp 0 = Some trigger ->
  param_matches reader sp 1 (spelling reader name) = true ->
  fst (run reader) = Some {| A.unary_trigger := trigger; A.unary_operand := spelling reader operand |}.
Proof.
  intros reader tc sp handle name ty operand trigger C S PL SL PI P B Cat L Ref.
  unfold run; rewrite C, S, PL, SL, PI, P, B, Cat, L, Ref; reflexivity.
Qed.

(** Atomic algorithms/legacy items remain the already proved definitions. *)
Theorem legacy_item_projection_is_reused : forall items index,
  List.length (map A.project_legacy items) = List.length items /\
  nth_error (map A.project_legacy items) index = option_map A.project_legacy (nth_error items index).
Proof. apply A.legacy_projection_keeps_lengths_and_positions. Qed.
Theorem atomic_composition_uses_same_unary_result : forall L State
  (rule : I.SourceRule) items store (literal : string -> State -> option L * State) state,
  @A.view_atomic L State (I.project_rule rule) (map A.project_legacy items)
    (fun s => (fst (run (retained_reader store)), s)) literal state =
  @A.source_atomic L State rule items
    (fun s => (fst (run (source_reader store)), s)) literal state.
Proof.
  intros; rewrite retained_unary_is_original_helper.
  apply A.complete_atomic_projection_and_callback_observation.
Qed.

Print Assumptions observations_preserve_result_and_copy_trace.
Print Assumptions literal_position_preserved.
Print Assumptions parameter_position_and_spelling_preserved.
Print Assumptions retained_reader_matches_original_observations.
Print Assumptions retained_unary_is_original_helper.
Print Assumptions absent_context_does_not_read_syntax.
Print Assumptions absent_syntax_stops_before_lengths.
Print Assumptions wrong_context_length_short_circuits_syntax_length.
Print Assumptions optional_parameter_does_not_descend.
Print Assumptions trigger_is_copied_before_final_parameter_mismatch.
Print Assumptions completed_helper_keeps_both_original_fields.
Print Assumptions legacy_item_projection_is_reused.
Print Assumptions atomic_composition_uses_same_unary_result.
End UnaryPrefixReaderProjection.
