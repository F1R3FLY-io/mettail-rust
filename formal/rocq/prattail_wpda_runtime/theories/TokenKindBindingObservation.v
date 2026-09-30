(** Retaining the original token_to_kind observation, not a second lexer.

    Source correspondence obligations: the Rust writer and retained producer
    consume the SAME first-variant visitor and active hybrid token roster;
    Core IDs are recorded at existing append sites. No TokenDefinition name,
    decoder capability or regex is inspected to reconstruct a token family.
    Constant rows preserve the selected kind. BooleanPayload applies the
    original generated Token::Boolean(text == "true") expression followed by
    token_to_kind's true/false arms; it never calls a semantic host decoder.

    Missing rows remain missing and cannot acquire a guessed default. This
    finite observation law does not prove lexical-lattice parity, admission,
    resource bounds, action semantics, or whole-parser equivalence.
*)
From Stdlib Require Import List String Bool.
Import ListNotations.
Open Scope string_scope.

Module TokenKindBindingObservation.
Section Observation.
Context {Kind : Type}.
Variable true_kind false_kind : Kind.
Inductive Observation := Constant (kind : Kind) | BooleanPayload.
Definition observe (row : Observation) (text : string) : Kind :=
  match row with
  | Constant kind => kind
  | BooleanPayload => if String.eqb text "true" then true_kind else false_kind
  end.
Definition lookup (rows : list (option Observation)) id text :=
  match nth_error rows id with
  | Some (Some row) => Some (observe row text)
  | _ => None
  end.
Theorem exact_append_site_observation : forall rows id row text,
  nth_error rows id = Some (Some row) ->
  lookup rows id text = Some (observe row text).
Proof. intros; unfold lookup; now rewrite H. Qed.
Theorem absent_is_not_a_default : forall rows id text,
  nth_error rows id = Some None -> lookup rows id text = None.
Proof. intros; unfold lookup; now rewrite H. Qed.
Theorem out_of_bounds_is_not_a_default : forall rows id text,
  nth_error rows id = None -> lookup rows id text = None.
Proof. intros; unfold lookup; now rewrite H. Qed.
Theorem boolean_original_composition : forall text,
  observe BooleanPayload text =
  (if (String.eqb text "true") then true_kind else false_kind).
Proof. reflexivity. Qed.

(** The unchanged source first-variant loop emits an ordered row roster.
    Both consumers use these same rows; the model does not introduce a new
    canonicalizer or claim arbitrary different row rosters are equivalent. *)
Definition first_variant (rows : list (string * Observation)) variant :=
  find (fun row => String.eqb (fst row) variant) rows.
Definition retained_variant rows variant :=
  option_map snd (first_variant rows variant).
Theorem first_collision_preserves_selected_body : forall variant first rest,
  retained_variant ((variant, first) :: rest) variant = Some first.
Proof. intros; unfold retained_variant, first_variant; cbn; now rewrite String.eqb_refl. Qed.
Theorem shared_writer_observation : forall rows variant row text,
  first_variant rows variant = Some (variant, row) ->
  option_map (fun binding => observe binding text) (retained_variant rows variant) =
  Some (observe row text).
Proof. intros; unfold retained_variant; now rewrite H. Qed.

(** The lexer chooses one terminal kind per text before the token-kind writer
    runs. In particular, a native Boolean terminal can win over a later fixed
    grammar literal with the same text. Append-site binding must follow that
    selected kind's variant, not reconstruct Fixed(text) from the Core row. *)
Definition selected_terminal_variant (terminals : list (string * string)) text :=
  option_map snd (find (fun terminal => String.eqb (fst terminal) text) terminals).
Definition retained_terminal rows terminals text :=
  match selected_terminal_variant terminals text with
  | Some variant => retained_variant rows variant
  | None => None
  end.
Theorem selected_terminal_uses_original_writer : forall rows terminals text variant row,
  find (fun terminal => String.eqb (fst terminal) text) terminals = Some (text, variant) ->
  first_variant rows variant = Some (variant, row) ->
  option_map (fun binding => observe binding text) (retained_terminal rows terminals text) =
  Some (observe row text).
Proof.
  intros rows terminals text variant row Hterminal Hwriter.
  unfold retained_terminal, selected_terminal_variant.
  rewrite Hterminal; cbn.
  unfold retained_variant.
  now rewrite Hwriter.
Qed.
Theorem boolean_terminal_collision_uses_payload : forall rows terminals,
  option_map (fun binding => observe binding "false")
    (retained_terminal (("Boolean", BooleanPayload) :: rows)
      (("false", "Boolean") :: terminals) "false") = Some false_kind.
Proof. intros; reflexivity. Qed.
End Observation.
Print Assumptions exact_append_site_observation.
Print Assumptions absent_is_not_a_default.
Print Assumptions out_of_bounds_is_not_a_default.
Print Assumptions boolean_original_composition.
Print Assumptions first_collision_preserves_selected_body.
Print Assumptions shared_writer_observation.
Print Assumptions selected_terminal_uses_original_writer.
Print Assumptions boolean_terminal_collision_uses_payload.
End TokenKindBindingObservation.
