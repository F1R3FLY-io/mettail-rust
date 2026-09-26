(** The actual Regex source contains a nonbinding List(Text) parameter and
    direct source-free Sep. Original prattail_bridge::convert_pattern_op emits
    Collection(separator, None) for this admitted Vec shape; find_collection_info
    and kv_sep_for supply no key/value separator. No map, chained operation,
    binder, foreign syntax or collection declaration is admitted by this delta.

    The original pipeline::collect_terminals_recursive emission loop and its
    sort/dedup tail become shared. Original SyntaxItemSpec preorder and the DDL
    shallow source adapter supply the same borrowed observations. This model
    proves the finite emission/roster correspondence, not arbitrary frontend
    equivalence, the lexer, source budgets, or whole-parser correctness.
*)
From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.

Module SeparatedTerminalObservation.
Inductive Observation :=
| Terminal (text : string)
| Collection (separator : string) (key_value : option string)
| BinderCollection (separator : string)
| Sep (separator : string)
| Other.

Definition nonempty (text : string) := if String.eqb text "" then [] else [text].
Definition emit (row : Observation) :=
  match row with
  | Terminal text => [text]
  | Collection separator key_value =>
      List.app (nonempty separator) (match key_value with None => [] | Some text => [text] end)
  | BinderCollection separator | Sep separator => nonempty separator
  | Other => []
  end.
Definition collected rows := flat_map emit rows.
Definition original_nonbinding_list separator := Collection separator None.
Definition ddl_nonbinding_list separator := Collection separator None.

Theorem admitted_list_source_observation_is_original : forall separator,
  ddl_nonbinding_list separator = original_nonbinding_list separator.
Proof. reflexivity. Qed.
Theorem arbitrary_nonempty_separator_is_retained : forall separator,
  String.eqb separator "" = false ->
  emit (ddl_nonbinding_list separator) = [separator].
Proof. intros; unfold ddl_nonbinding_list, emit, nonempty; now rewrite H. Qed.
Theorem empty_separator_adds_no_terminal : emit (ddl_nonbinding_list "") = [].
Proof. reflexivity. Qed.
Theorem original_optional_key_value_presence_is_preserved : forall separator key_value,
  emit (Collection separator (Some key_value)) = List.app (nonempty separator) [key_value].
Proof. reflexivity. Qed.
Theorem terminal_empty_spelling_is_not_separator_empty_gate : emit (Terminal "") = [""].
Proof. reflexivity. Qed.
Theorem original_source_order_precedes_sort_and_dedup : forall left right,
  collected (List.app left right) = List.app (collected left) (collected right).
Proof. intros; unfold collected; apply flat_map_app. Qed.
Theorem identical_observations_use_identical_normalized_roster :
  forall (normalize : list string -> list string) original ddl,
  original = ddl -> normalize (collected original) = normalize (collected ddl).
Proof. intros; now rewrite H. Qed.
Print Assumptions admitted_list_source_observation_is_original.
Print Assumptions arbitrary_nonempty_separator_is_retained.
Print Assumptions empty_separator_adds_no_terminal.
Print Assumptions original_optional_key_value_presence_is_preserved.
Print Assumptions terminal_empty_spelling_is_not_separator_empty_gate.
Print Assumptions original_source_order_precedes_sort_and_dedup.
Print Assumptions identical_observations_use_identical_normalized_roster.
End SeparatedTerminalObservation.
