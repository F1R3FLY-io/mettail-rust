(** Atomic classifier relocation: concrete source/view decision correspondence.

    Source: macros/src/gen/runtime/wpda_codegen/prefix.rs::classify_atomic
    (judgement branches followed by legacy singleton dispatch), together with
    the existing unary/literal resolver dependencies.
    The mutually exclusive list-shape patterns below spell out the original
    length checks; source and projected decisions are defined independently.

    Reuse InfixClassifierProjection for exact shallow type/syntax/parameter
    projection. Legacy kinds are copied as discriminants, never reclassified
    from names. Unsupported items retain positions; absent judgement lists
    are different from present-empty. Both-present judgement input NEVER
    falls back to legacy items, even when the unary callback returns None.

    Callbacks are state transformers so the theorem preserves not only the
    descriptor but call order, arguments, count and final callback state.
    The original classify_unary_prefix_shape and classify_literal_patterned
    remain callbacks; their algorithms/native eligibility are NOT rederived.
    Literal payload L is opaque and passed through unchanged. Wrapper strings
    are observations only: static materialization retains the original opaque
    rule.label object, not an Ident rebuilt from the descriptor's string.

    Rust source correspondence must retain all branches, map enum discriminants,
    invoke closures lazily at the proved sites, capture the original category
    Ident in the literal closure, and clone original wrapper/payload objects.
    No grammar normalization, descriptor-family completeness, runtime cutover,
    or proof of literal evaluator/unary-helper correctness is claimed here.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import InfixClassifierProjection.
Import ListNotations.
Import InfixClassifierProjection.InfixClassifierProjection.
Open Scope string_scope.
Set Implicit Arguments.

Module AtomicClassifierProjection.

Inductive LegacyKind :=
| IntegerKind | BooleanKind | StringKind | FloatKind
| VarKind | IdentKind | CategoryKind.
Inductive SourceLegacy :=
| SourceTerminal (text : string)
| SourceNonTerminal (kind : LegacyKind) (name : string) (opaque_metadata : nat)
| SourceOtherItem (opaque_shape : nat).
Inductive LegacyItem :=
| Terminal (text : string)
| NonTerminal (kind : LegacyKind) (name : string)
| OtherItem.
Definition project_legacy item :=
  match item with
  | SourceTerminal text => Terminal text
  | SourceNonTerminal kind name _ => NonTerminal kind name
  | SourceOtherItem _ => OtherItem
  end.

Theorem legacy_projection_keeps_lengths_and_positions : forall items index,
  List.length (map project_legacy items) = List.length items /\
  nth_error (map project_legacy items) index =
    option_map project_legacy (nth_error items index).
Proof. intros; split; [apply length_map|apply map_nth_exact]. Qed.

Theorem legacy_kind_is_not_name_classification : forall kind name metadata,
  project_legacy (SourceNonTerminal kind name metadata) = NonTerminal kind name.
Proof. reflexivity. Qed.

Record Unary := { unary_trigger : string; unary_operand : string }.
Inductive CallbackEvent := UnaryCall | LiteralCall (category : string).

Section Payload.
Context {L State Wrapper : Type}.

Inductive Descriptor :=
| LiteralInteger | LiteralBoolean | LiteralString | LiteralFloat
| LiteralPatterned (payload : L)
| TerminalKeyword (text label : string)
| NullaryLiteralRun (trigger : string) (trailing : list string) (label : string)
| VarRule (label : string)
| CrossCatProjection (source label : string)
| CrossCatPrefixUnary (trigger source label : string)
| PrefixOperator (trigger operand : string)
| NonAtomic.

Fixpoint source_literals syntax : option (list string) :=
  match syntax with
  | [] => Some []
  | SourceLiteral text :: rest => option_map (cons text) (source_literals rest)
  | _ => None
  end.
Fixpoint view_literals syntax : option (list string) :=
  match syntax with
  | [] => Some []
  | Literal text :: rest => option_map (cons text) (view_literals rest)
  | _ => None
  end.
Lemma literal_run_projection_exact : forall syntax,
  view_literals (map project_syntax syntax) = source_literals syntax.
Proof. induction syntax as [|[text|name|name separator origin|opaque] rest IH]; cbn; congruence. Qed.

(** Earlier judgement successes. Source patterns operate on the original
    recursive types; view patterns operate on independent shallow variants.
    In particular only the PREFIX branch rejects Ident, not projection. *)
Definition source_early label category context syntax : option Descriptor :=
  match context, syntax with
  | [], [SourceLiteral text] => Some (TerminalKeyword text label)
  | [], first :: second :: rest =>
      match source_literals (first :: second :: rest) with
      | Some (trigger :: trailing) => Some (NullaryLiteralRun trigger trailing label)
      | _ => None
      end
  | [SourceSimple name (SourceBase source)], [SourceParamRef reference] =>
      if String.eqb reference name && negb (String.eqb source category)
      then Some (CrossCatProjection source label) else None
  | [SourceSimple name ty], [SourceLiteral trigger; SourceParamRef reference] =>
      if source_ident ty then None else
      match ty with
      | SourceBase source =>
          if String.eqb reference name && negb (String.eqb source category)
          then Some (CrossCatPrefixUnary trigger source label) else None
      | _ => None
      end
  | _, _ => None
  end.

Definition view_early label category context syntax : option Descriptor :=
  match context, syntax with
  | [], [Literal text] => Some (TerminalKeyword text label)
  | [], first :: second :: rest =>
      match view_literals (first :: second :: rest) with
      | Some (trigger :: trailing) => Some (NullaryLiteralRun trigger trailing label)
      | _ => None
      end
  | [Simple name (Base source)], [Param reference] =>
      if String.eqb reference name && negb (String.eqb source category)
      then Some (CrossCatProjection source label) else None
  | [Simple name ty], [Literal trigger; Param reference] =>
      if view_ident ty then None else
      match ty with
      | Base source =>
          if String.eqb reference name && negb (String.eqb source category)
          then Some (CrossCatPrefixUnary trigger source label) else None
      | _ => None
      end
  | _, _ => None
  end.

Theorem all_early_judgement_branches_preserved : forall label category context syntax,
  view_early label category (map project_param context) (map project_syntax syntax) =
    source_early label category context syntax.
Proof.
  intros label category context syntax.
  destruct context as [|p [|p2 context]].
  - destruct syntax as [|s [|s2 syntax]]; cbn; try reflexivity.
    + destruct s; reflexivity.
    + destruct s; destruct s2; cbn; try reflexivity.
      now rewrite literal_run_projection_exact.
  - destruct p as [name ty|opaque]; try destruct ty;
      destruct syntax as [|s [|s2 [|s3 rest]]];
      try destruct s; try destruct s2; reflexivity.
  - destruct p as [name ty|opaque]; try destruct ty;
      destruct syntax as [|s [|s2 rest]];
      try destruct s; try destruct s2; reflexivity.
Qed.

Record Observation := {
  descriptor : Descriptor;
  final_state : State;
  callback_trace : list CallbackEvent
}.
Definition quiet value state :=
  {| descriptor := value; final_state := state; callback_trace := [] |}.
Definition use_unary (unary : State -> option Unary * State) state :=
  let '(result, next) := unary state in
  {| descriptor := match result with
       | Some shape => PrefixOperator (unary_trigger shape) (unary_operand shape)
       | None => NonAtomic end;
     final_state := next; callback_trace := [UnaryCall] |}.
Definition use_literal (literal : string -> State -> option L * State) category state :=
  let '(result, next) := literal category state in
  {| descriptor := match result with Some payload => LiteralPatterned payload | None => NonAtomic end;
     final_state := next; callback_trace := [LiteralCall category] |}.

(** Each legacy branch is transcribed separately, including all seven kinds,
    singleton arity, Var identity, and literal resolver's category identity. *)
Definition source_legacy label category items literal state :=
  match items with
  | [SourceTerminal text] => quiet (TerminalKeyword text label) state
  | [SourceNonTerminal kind name _] =>
      match kind with
      | IntegerKind => quiet LiteralInteger state
      | BooleanKind => quiet LiteralBoolean state
      | StringKind => quiet LiteralString state
      | FloatKind => quiet LiteralFloat state
      | VarKind => quiet (if String.eqb category name then VarRule label else NonAtomic) state
      | IdentKind => quiet NonAtomic state
      | CategoryKind => if String.eqb category name then use_literal literal name state
                        else quiet NonAtomic state
      end
  | _ => quiet NonAtomic state
  end.
Definition view_legacy label category items literal state :=
  match items with
  | [Terminal text] => quiet (TerminalKeyword text label) state
  | [NonTerminal kind name] =>
      match kind with
      | IntegerKind => quiet LiteralInteger state
      | BooleanKind => quiet LiteralBoolean state
      | StringKind => quiet LiteralString state
      | FloatKind => quiet LiteralFloat state
      | VarKind => quiet (if String.eqb category name then VarRule label else NonAtomic) state
      | IdentKind => quiet NonAtomic state
      | CategoryKind => if String.eqb category name then use_literal literal name state
                        else quiet NonAtomic state
      end
  | _ => quiet NonAtomic state
  end.

Theorem all_legacy_decisions_preserved : forall label category items literal state,
  view_legacy label category (map project_legacy items) literal state =
    source_legacy label category items literal state.
Proof.
  intros label category items literal state.
  destruct items as [|item rest]; [reflexivity|].
  destruct item; destruct rest as [|second rest]; reflexivity.
Qed.

Definition source_atomic (rule : SourceRule) items unary literal state :=
  match source_context rule, source_pattern rule with
  | Some context, Some syntax =>
      match source_early (source_label rule) (source_category rule) context syntax with
      | Some result => quiet result state
      | None => use_unary unary state
      end
  | _, _ => source_legacy (source_label rule) (source_category rule) items literal state
  end.
Definition view_atomic (rule : RuleView) items unary literal state :=
  match view_context rule, view_pattern rule with
  | Some context, Some syntax =>
      match view_early (view_label rule) (view_category rule) context syntax with
      | Some result => quiet result state
      | None => use_unary unary state
      end
  | _, _ => view_legacy (view_label rule) (view_category rule) items literal state
  end.

Theorem complete_atomic_projection_and_callback_observation : forall rule items unary literal state,
  view_atomic (project_rule rule) (map project_legacy items) unary literal state =
    source_atomic rule items unary literal state.
Proof.
  intros [label category right same context syntax] items unary literal state.
  unfold view_atomic, source_atomic; cbn.
  destruct context; destruct syntax; cbn;
    try apply all_legacy_decisions_preserved.
  now rewrite all_early_judgement_branches_preserved.
Qed.

Theorem judgement_failure_never_falls_back_to_legacy : forall rule context syntax items unary literal state next,
  source_context rule = Some context -> source_pattern rule = Some syntax ->
  source_early (source_label rule) (source_category rule) context syntax = None ->
  unary state = (None, next) ->
  source_atomic rule items unary literal state =
    {| descriptor := NonAtomic; final_state := next; callback_trace := [UnaryCall] |}.
Proof. intros; unfold source_atomic; rewrite H, H0, H1; unfold use_unary; now rewrite H2. Qed.

Theorem early_success_calls_neither_callback : forall rule context syntax result items unary literal state,
  source_context rule = Some context -> source_pattern rule = Some syntax ->
  source_early (source_label rule) (source_category rule) context syntax = Some result ->
  source_atomic rule items unary literal state = quiet result state.
Proof. intros; unfold source_atomic; now rewrite H, H0, H1. Qed.

Theorem literal_callback_preserves_opaque_payload : forall literal category state payload next,
  literal category state = (Some payload, next) ->
  use_literal literal category state =
    {| descriptor := LiteralPatterned payload; final_state := next;
       callback_trace := [LiteralCall category] |}.
Proof. intros; unfold use_literal; now rewrite H. Qed.

Theorem callbacks_never_both_run : forall rule items unary literal state,
  callback_trace (source_atomic rule items unary literal state) = [] \/
  callback_trace (source_atomic rule items unary literal state) = [UnaryCall] \/
  exists category, callback_trace (source_atomic rule items unary literal state) = [LiteralCall category].
Proof.
  intros [label category right same context syntax] items unary literal state.
  unfold source_atomic; cbn. destruct context; destruct syntax; cbn.
  { destruct (source_early label category l l0).
    - now left.
    - right; left. unfold use_unary. destruct (unary state); reflexivity. }
  all: unfold source_legacy; destruct items as [|item [|second rest]]; cbn;
    try (left; reflexivity).
  all: destruct item; cbn; try (left; reflexivity).
  all: destruct kind; cbn; try (left; reflexivity).
  all: destruct (String.eqb category name); [|left; reflexivity].
  all: right; right; exists name; unfold use_literal; destruct (literal name state); reflexivity.
Qed.

(** The static adapter does not rebuild Ident from the descriptor string.
    Wrapper-bearing variants receive the captured original object unchanged;
    literal payloads already own their original generated wrapper and eval. *)
Definition retained_wrapper (original : Wrapper) result : option Wrapper :=
  match result with
  | TerminalKeyword _ _ | NullaryLiteralRun _ _ _ | VarRule _
  | CrossCatProjection _ _ | CrossCatPrefixUnary _ _ _ => Some original
  | _ => None
  end.
Definition materialize original result := (result, retained_wrapper original result).

Theorem wrapper_identity_not_reconstructed : forall original text label,
  retained_wrapper original (TerminalKeyword text label) = Some original /\
  retained_wrapper original (VarRule label) = Some original /\
  retained_wrapper original (CrossCatProjection text label) = Some original /\
  retained_wrapper original (CrossCatPrefixUnary text text label) = Some original /\
  retained_wrapper original (NullaryLiteralRun text [] label) = Some original.
Proof. intros; repeat split; reflexivity. Qed.

Theorem materialized_atomic_result_preserved : forall rule items unary literal state original,
  materialize original (descriptor (view_atomic (project_rule rule) (map project_legacy items) unary literal state)) =
  materialize original (descriptor (source_atomic rule items unary literal state)).
Proof. intros; now rewrite complete_atomic_projection_and_callback_observation. Qed.

End Payload.
Print Assumptions legacy_projection_keeps_lengths_and_positions.
Print Assumptions all_early_judgement_branches_preserved.
Print Assumptions all_legacy_decisions_preserved.
Print Assumptions complete_atomic_projection_and_callback_observation.
Print Assumptions judgement_failure_never_falls_back_to_legacy.
Print Assumptions callbacks_never_both_run.
Print Assumptions literal_callback_preserves_opaque_payload.
Print Assumptions materialized_atomic_result_preserved.
End AtomicClassifierProjection.
