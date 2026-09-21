(** Exact observation boundary for relocating the original infix classifier.

    Source inspected before this model:
    macros/src/gen/runtime/wpda_codegen/infix.rs: classify_rule,
    classify_judgement, classify_postfix_mixfix, classify_mixfix,
    base_type_name, capture_kind_of, gen1_rep_classify_enabled;
    ast/src/types.rs: TypeExpr::is_ident_text; ast/src/grammar.rs:
    NonTerminalKind::classify and the source enum definitions.

    The source decision program reads names, flags, optional ordered lists,
    their lengths and indexed elements, Base names, Ident recognition, and
    Collection's immediate Base element. It does not inspect collection kind,
    a Sep's optional source, or nested unsupported syntax/type contents.
    The view must keep Other markers, and None must not become Some [].

    This model proves a non-lossy projection for those observations and an
    interpretation theorem for every finite adaptive decision program over
    them. Query continuations cover branching, indexed iteration, early
    returns, and building complete output records, including literal buffers,
    repetition closes, associativity and category flags. No alternative Rust
    classifier or parser algorithm is introduced here. We do NOT assert that
    the Rust classifier is extracted from this Rocq program language. The
    theorem applies to its mechanically unchanged decision program precisely
    when all source reads are the listed observations; differential tests and
    source review must establish that correspondence. In particular they must
    retain binary heterogeneous fallback, classic-before-postfix mixfix order,
    question-mark early returns, and the complete returned InfixRuleInfo.

    Names below are exact Rust identifier/string observations, not a renaming
    or declaration-order reconstruction. AST conversion to judgement form is
    the existing caller's operation and is outside this boundary. Other source
    data is represented by arbitrary opaque payloads, not silently filtered.
    No runtime completeness, GrammarCore ordering, or parser correctness claim.
*)
From Stdlib Require Import List String Bool Arith.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module InfixClassifierProjection.

Inductive SourceType :=
| SourceBase (name : string)
| SourceCollection (kind : nat) (element : SourceType)
| SourceArrow (domain codomain : SourceType)
| SourceMultiBinder (inner : SourceType)
| SourceRefined (name predicate : string) (base : SourceType)
| SourceMap (key value : SourceType).

Inductive TypeView :=
| Base (name : string)
| Collection (element_base : option string)
| OtherType.

Definition source_base ty :=
  match ty with SourceBase name => Some name | _ => None end.
Definition source_ident ty :=
  match ty with SourceBase name => String.eqb name "Ident" | _ => false end.
Definition source_element ty :=
  match ty with SourceCollection _ element => source_base element | _ => None end.
Definition source_is_collection ty :=
  match ty with SourceCollection _ _ => true | _ => false end.

Definition project_type ty :=
  match ty with
  | SourceBase name => Base name
  | SourceCollection _ element => Collection (source_base element)
  | _ => OtherType
  end.
Definition view_base ty := match ty with Base name => Some name | _ => None end.
Definition view_ident ty :=
  match ty with Base name => String.eqb name "Ident" | _ => false end.
Definition view_element ty :=
  match ty with Collection element => element | _ => None end.
Definition view_is_collection ty :=
  match ty with Collection _ => true | _ => false end.
Definition capture_name (is_ident : bool) := if is_ident then Some "Ident" else None.

Theorem all_type_observations_preserved : forall ty,
  view_base (project_type ty) = source_base ty /\
  view_ident (project_type ty) = source_ident ty /\
  view_element (project_type ty) = source_element ty /\
  view_is_collection (project_type ty) = source_is_collection ty.
Proof. destruct ty; repeat split; reflexivity. Qed.

Corollary capture_kind_preserved : forall ty,
  capture_name (view_ident (project_type ty)) = capture_name (source_ident ty).
Proof. destruct ty; reflexivity. Qed.

Theorem nested_collection_is_not_flattened : forall kind inner_kind element,
  project_type (SourceCollection kind (SourceCollection inner_kind element)) =
    Collection None /\
  view_element (project_type (SourceCollection kind (SourceCollection inner_kind element))) = None.
Proof. intros; split; reflexivity. Qed.

(** Distinguishing an unsupported parameter from a missing position is
    essential: the original filter_map is followed by an exact length guard. *)
Inductive SourceParam :=
| SourceSimple (name : string) (ty : SourceType)
| SourceOtherParam (opaque_shape : nat).
Inductive ParamView := Simple (name : string) (ty : TypeView) | OtherParam.
Definition project_param p :=
  match p with SourceSimple name ty => Simple name (project_type ty)
             | SourceOtherParam _ => OtherParam end.

Inductive SourceSyntax :=
| SourceLiteral (text : string)
| SourceParamRef (name : string)
| SourceSep (collection separator : string) (opaque_source : option nat)
| SourceOtherSyntax (opaque_shape : nat).
Inductive SyntaxView :=
| Literal (text : string)
| Param (name : string)
| Sep (collection separator : string)
| OtherSyntax.
Definition project_syntax s :=
  match s with
  | SourceLiteral text => Literal text
  | SourceParamRef name => Param name
  | SourceSep name separator _ => Sep name separator
  | SourceOtherSyntax _ => OtherSyntax
  end.

Record SourceRule := {
  source_label : string;
  source_category : string;
  source_right : bool;
  source_same_level : bool;
  source_context : option (list SourceParam);
  source_pattern : option (list SourceSyntax)
}.
Record RuleView := {
  view_label : string;
  view_category : string;
  view_right : bool;
  view_same_level : bool;
  view_context : option (list ParamView);
  view_pattern : option (list SyntaxView)
}.
Definition project_rule rule :=
  {| view_label := source_label rule; view_category := source_category rule;
     view_right := source_right rule; view_same_level := source_same_level rule;
     view_context := option_map (map project_param) (source_context rule);
     view_pattern := option_map (map project_syntax) (source_pattern rule) |}.

Lemma map_nth_exact : forall (A B : Type) (f : A -> B) xs index,
  nth_error (map f xs) index = option_map f (nth_error xs index).
Proof.
  intros A B f xs. induction xs; intros [|index]; cbn; auto.
Qed.

Theorem context_preserves_length_and_every_position : forall params index,
  List.length (map project_param params) = List.length params /\
  nth_error (map project_param params) index =
    option_map project_param (nth_error params index).
Proof. intros; split; [apply map_length | apply map_nth_exact]. Qed.

Theorem syntax_preserves_length_and_every_position : forall syntax index,
  List.length (map project_syntax syntax) = List.length syntax /\
  nth_error (map project_syntax syntax) index =
    option_map project_syntax (nth_error syntax index).
Proof. intros; split; [apply map_length | apply map_nth_exact]. Qed.

Theorem unsupported_parameter_keeps_its_position : forall params index opaque,
  nth_error params index = Some (SourceOtherParam opaque) ->
  nth_error (map project_param params) index = Some OtherParam.
Proof. intros; rewrite map_nth_exact, H; reflexivity. Qed.

Theorem unsupported_syntax_keeps_its_position : forall syntax index opaque,
  nth_error syntax index = Some (SourceOtherSyntax opaque) ->
  nth_error (map project_syntax syntax) index = Some OtherSyntax.
Proof. intros; rewrite map_nth_exact, H; reflexivity. Qed.

Theorem absent_context_is_not_an_empty_context :
  option_map (map project_param) None <> Some [].
Proof. discriminate. Qed.
Theorem empty_context_remains_present :
  option_map (map project_param) (Some []) = Some [].
Proof. reflexivity. Qed.

(** Exactly the filter_map/count rejection used by classify_judgement.
    This filtering is in the unchanged decision program, NEVER the view. *)
Fixpoint source_simple_count params :=
  match params with
  | [] => 0
  | SourceSimple _ _ :: rest => S (source_simple_count rest)
  | SourceOtherParam _ :: rest => source_simple_count rest
  end.
Fixpoint view_simple_count params :=
  match params with
  | [] => 0
  | Simple _ _ :: rest => S (view_simple_count rest)
  | OtherParam :: rest => view_simple_count rest
  end.
Lemma simple_count_preserved : forall params,
  view_simple_count (map project_param params) = source_simple_count params.
Proof. induction params as [|[name ty|opaque] rest IH]; cbn; congruence. Qed.

Theorem original_non_simple_rejection_preserved : forall params,
  Nat.eqb (view_simple_count (map project_param params))
    (List.length (map project_param params)) =
  Nat.eqb (source_simple_count params) (List.length params).
Proof. intros; rewrite simple_count_preserved, map_length; reflexivity. Qed.

(** Independent source/view observation interpreters. Parameter facts retain
    every observed type query, not a bool that assumes classifier equality. *)
Record TypeFacts := {
  fact_base : option string;
  fact_ident : bool;
  fact_element : option string;
  fact_collection : bool
}.
Inductive ParamFacts := SimpleFacts (name : string) (facts : TypeFacts) | OtherFacts.
Definition source_param_facts p :=
  match p with
  | SourceSimple name ty => SimpleFacts name
      {| fact_base := source_base ty; fact_ident := source_ident ty;
         fact_element := source_element ty; fact_collection := source_is_collection ty |}
  | SourceOtherParam _ => OtherFacts
  end.
Definition view_param_facts p :=
  match p with
  | Simple name ty => SimpleFacts name
      {| fact_base := view_base ty; fact_ident := view_ident ty;
         fact_element := view_element ty; fact_collection := view_is_collection ty |}
  | OtherParam => OtherFacts
  end.
Lemma parameter_facts_preserved : forall p,
  view_param_facts (project_param p) = source_param_facts p.
Proof. intros [name ty|opaque]; [destruct ty|]; reflexivity. Qed.

Definition optional_length {A} (xs : option (list A)) := option_map (@List.length A) xs.
Definition optional_nth {A} (xs : option (list A)) index :=
  match xs with Some xs => nth_error xs index | None => None end.

Inductive Query : Type -> Type :=
| Label : Query string
| Category : Query string
| RightAssociative : Query bool
| SharesPrevious : Query bool
| ContextLength : Query (option nat)
| PatternLength : Query (option nat)
| ParameterAt (index : nat) : Query (option ParamFacts)
| SyntaxAt (index : nat) : Query (option SyntaxView)
| RepetitionEnabled : Query bool.

(** The actual original gate has an empty exclusion list. There is no new
    category policy, filtering, or deduced declaration-order information. *)
Definition original_repeat_exclusions : list string := [].
Definition repeat_enabled category :=
  negb (existsb (String.eqb category) original_repeat_exclusions).

Definition read_source {A} (rule : SourceRule) (q : Query A) : A :=
  match q with
  | Label => source_label rule
  | Category => source_category rule
  | RightAssociative => source_right rule
  | SharesPrevious => source_same_level rule
  | ContextLength => optional_length (source_context rule)
  | PatternLength => optional_length (source_pattern rule)
  | ParameterAt index => option_map source_param_facts (optional_nth (source_context rule) index)
  | SyntaxAt index => option_map project_syntax (optional_nth (source_pattern rule) index)
  | RepetitionEnabled => repeat_enabled (source_category rule)
  end.
Definition read_view {A} (rule : RuleView) (q : Query A) : A :=
  match q with
  | Label => view_label rule
  | Category => view_category rule
  | RightAssociative => view_right rule
  | SharesPrevious => view_same_level rule
  | ContextLength => optional_length (view_context rule)
  | PatternLength => optional_length (view_pattern rule)
  | ParameterAt index => option_map view_param_facts (optional_nth (view_context rule) index)
  | SyntaxAt index => optional_nth (view_pattern rule) index
  | RepetitionEnabled => repeat_enabled (view_category rule)
  end.

Theorem every_classifier_observation_preserved : forall A (q : Query A) rule,
  read_view (project_rule rule) q = read_source rule q.
Proof.
  intros A q [label category right same context syntax]. destruct q; cbn;
    try reflexivity.
  - destruct context; cbn; [now rewrite map_length|reflexivity].
  - destruct syntax; cbn; [now rewrite map_length|reflexivity].
  - destruct context as [params|]; cbn; [|reflexivity].
    rewrite map_nth_exact. destruct (nth_error params index) as [p|]; cbn;
      [now rewrite parameter_facts_preserved|reflexivity].
  - destruct syntax; cbn; [apply map_nth_exact|reflexivity].
Qed.

(** A finite adaptive decision program: each read may choose its continuation
    from the returned observation. Thus equality covers all branches and exact
    outputs, not merely a fixed list of preselected observations. Ordinary pure
    computations on observations live in the continuation; result type R can
    be the complete Option<InfixRuleInfo>, not just a recognized/not bit. *)
Inductive Decision (R : Type) :=
| Return (result : R)
| Read {A : Type} (query : Query A) (next : A -> Decision R).
Arguments Return {R} result.
Arguments Read {R A} query next.

Fixpoint run_source {R} (rule : SourceRule) (program : Decision R) : R :=
  match program with
  | Return result => result
  | Read q next => run_source rule (next (read_source rule q))
  end.
Fixpoint run_view {R} (rule : RuleView) (program : Decision R) : R :=
  match program with
  | Return result => result
  | Read q next => run_view rule (next (read_view rule q))
  end.

Theorem unchanged_decision_program_observational_equivalence :
  forall R (program : Decision R) rule,
  run_view (project_rule rule) program = run_source rule program.
Proof.
  intros R program. induction program as [result|A query next IH]; intros rule; cbn.
  - reflexivity.
  - rewrite every_classifier_observation_preserved. apply IH.
Qed.

(** Repeated reads, differently ordered reads, and early None all fall under
    the theorem. Here the first original classify_rule gate is explicit. *)
Definition classify_rule_gate {R} (judgement : Decision (option R)) :=
  Read ContextLength (fun context =>
    Read PatternLength (fun syntax =>
      match context, syntax with
      | Some _, Some _ => judgement
      | _, _ => Return None
      end)).

Corollary original_optional_input_gate_and_result_preserved : forall R
    (judgement : Decision (option R)) rule,
  run_view (project_rule rule) (classify_rule_gate judgement) =
    run_source rule (classify_rule_gate judgement).
Proof. intros; apply unchanged_decision_program_observational_equivalence. Qed.

Theorem rule_sequence_order_preserved : forall rules index,
  List.length (map project_rule rules) = List.length rules /\
  nth_error (map project_rule rules) index =
    option_map project_rule (nth_error rules index).
Proof. intros; split; [apply map_length|apply map_nth_exact]. Qed.

Print Assumptions all_type_observations_preserved.
Print Assumptions unsupported_parameter_keeps_its_position.
Print Assumptions unsupported_syntax_keeps_its_position.
Print Assumptions original_non_simple_rejection_preserved.
Print Assumptions every_classifier_observation_preserved.
Print Assumptions unchanged_decision_program_observational_equivalence.
Print Assumptions original_optional_input_gate_and_result_preserved.
Print Assumptions rule_sequence_order_preserved.
End InfixClassifierProjection.
