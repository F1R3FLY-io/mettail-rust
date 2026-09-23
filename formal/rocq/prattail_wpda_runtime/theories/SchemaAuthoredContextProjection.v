(** Schema-specific context observations, not arbitrary AST identity.

    Source correspondence:
    - FIPS III.6 decode_terms (lines 2327-2353) and schema::decode_term
      both decode r[context] ?? [] independently of body form.
    - Original parse_grammar_rule_new records Some(context), even empty;
      parse_grammar_rule_old records None for its context-free BNF form.
    - Runtime lower always validates parameter_descriptors, including BNF;
      lower_term_body's BNF branch ignores those descriptors. Nonempty runtime
      BNF parameters must therefore remain retained, not dropped or refused.

    The adapter projects an already decoded context, never raw map presence:
    judgement -> Some(context); BNF empty -> None; BNF nonempty -> Some(context).
    This is an observation adapter, not a parser, normalizer, classifier, or
    extension of the authored arena/capture theorem. Macro capture still reads
    the actual AST Option unchanged. Params below are arbitrary full values;
    no parameter fields, order, or duplicates are abstracted away by mapping.
*)
From Stdlib Require Import List.
Import ListNotations.

Module SchemaAuthoredContextProjection.
Inductive BodyForm := Judgement | Bnf.

Section Context.
Context {Param : Type}.

Definition decode_context (key : option (list Param)) : list Param :=
  match key with None => [] | Some params => params end.

Definition retained_context (form : BodyForm) (params : list Param)
    : option (list Param) :=
  match form, params with
  | Judgement, _ => Some params
  | Bnf, [] => None
  | Bnf, _ :: _ => Some params
  end.

Definition schema_observation form key := retained_context form (decode_context key).

(** Both raw key spellings use the original existing default. *)
Theorem absent_and_explicit_empty_decode_identically :
  decode_context None = decode_context (Some []).
Proof. reflexivity. Qed.

Theorem absent_and_explicit_empty_observe_identically : forall form,
  schema_observation form None = schema_observation form (Some []).
Proof. reflexivity. Qed.

Theorem judgement_always_has_normalized_context : forall key,
  schema_observation Judgement key = Some (decode_context key).
Proof. intros; reflexivity. Qed.

Theorem omitted_judgement_agrees_with_original_empty_parser_context :
  schema_observation Judgement None = Some [].
Proof. reflexivity. Qed.

Theorem ordinary_bnf_agrees_with_original_parser_absence :
  schema_observation Bnf None = None /\ schema_observation Bnf (Some []) = None.
Proof. split; reflexivity. Qed.

Theorem nonempty_bnf_context_is_not_dropped : forall first rest,
  schema_observation Bnf (Some (first :: rest)) = Some (first :: rest).
Proof. reflexivity. Qed.

(** Default erasure after observation recovers precisely the existing decoded
    parameter sequence. Thus validation sees the same values, in the same
    order and with the same duplicates, in both body forms. *)
Theorem observed_parameters_are_exactly_original_decoded_parameters : forall form key,
  decode_context (schema_observation form key) = decode_context key.
Proof. intros form [params|]; destruct form; cbn; try reflexivity.
  destruct params; reflexivity.
Qed.

Corollary every_parameter_position_is_unchanged : forall form key index,
  nth_error (decode_context (schema_observation form key)) index =
  nth_error (decode_context key) index.
Proof. intros. now rewrite observed_parameters_are_exactly_original_decoded_parameters. Qed.

Corollary parameter_count_is_unchanged : forall form key,
  length (decode_context (schema_observation form key)) = length (decode_context key).
Proof. intros. now rewrite observed_parameters_are_exactly_original_decoded_parameters. Qed.

Theorem nonempty_context_keeps_duplicates : forall form (param : Param),
  schema_observation form (Some [param; param]) = Some [param; param].
Proof. intros []; reflexivity. Qed.

(** Macro reader preservation is a separate contract. This correction never
    rewrites the original macro's raw Option, including programmatic ASTs. *)
Definition macro_observation (raw : option (list Param)) := raw.

Theorem macro_raw_option_is_unchanged : forall raw,
  macro_observation raw = raw.
Proof. reflexivity. Qed.

Theorem macro_absence_and_present_empty_remain_distinct :
  macro_observation None <> macro_observation (Some []).
Proof. discriminate. Qed.

Theorem runtime_default_equivalence_is_not_macro_raw_option_equivalence :
  schema_observation Judgement None = schema_observation Judgement (Some []) /\
  macro_observation None <> macro_observation (Some []).
Proof. split; [reflexivity|discriminate]. Qed.

End Context.

Print Assumptions absent_and_explicit_empty_decode_identically.
Print Assumptions absent_and_explicit_empty_observe_identically.
Print Assumptions judgement_always_has_normalized_context.
Print Assumptions omitted_judgement_agrees_with_original_empty_parser_context.
Print Assumptions ordinary_bnf_agrees_with_original_parser_absence.
Print Assumptions nonempty_bnf_context_is_not_dropped.
Print Assumptions observed_parameters_are_exactly_original_decoded_parameters.
Print Assumptions every_parameter_position_is_unchanged.
Print Assumptions parameter_count_is_unchanged.
Print Assumptions nonempty_context_keeps_duplicates.
Print Assumptions macro_raw_option_is_unchanged.
Print Assumptions macro_absence_and_present_empty_remain_distinct.
Print Assumptions runtime_default_equivalence_is_not_macro_raw_option_equivalence.
End SchemaAuthoredContextProjection.
