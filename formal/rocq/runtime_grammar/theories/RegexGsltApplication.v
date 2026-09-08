(** Application contract for the existing Regex GSLT reference semantics.

    These lemmas compose the existing scalar search and UTF-8 cursor models;
    they do not define another matcher or prove the Rust/DDL realization.
    The finite examples freeze observable application cases before that
    realization is implemented. *)

From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import
  RegexGsltMatch RegexGsltSearch RegexGsltReplace RegexGsltOracle
  SemanticIntrinsics.
Import ListNotations.
Module Utf8 := SemanticIntrinsics.SemanticIntrinsics.

Definition application_byte_span (text : Text) (span : MatchSpan) : MatchSpan :=
  {| span_start := Utf8.scalar_byte_offset text (span_start span);
     span_end := Utf8.scalar_byte_offset text (span_end span) |}.

Theorem application_search_byte_span_valid :
  forall pattern text span,
    search pattern text = Some span ->
    let bytes := application_byte_span text span in
    span_start bytes <= span_end bytes /\
    span_end bytes <= Utf8.utf8_byte_length text /\
    Utf8.utf8_boundary text (span_start bytes) /\
    Utf8.utf8_boundary text (span_end bytes).
Proof.
  intros pattern text span Hsearch.
  pose proof (search_span_is_valid pattern text span Hsearch) as [Horder Hend].
  cbn [application_byte_span].
  split.
  - now apply Utf8.scalar_byte_offset_monotone.
  - split.
    + now apply Utf8.scalar_byte_offset_bounded.
    + split; unfold Utf8.utf8_boundary.
      * exists (span_start span). split.
        -- exact (Nat.le_trans _ _ _ Horder Hend).
        -- reflexivity.
      * exists (span_end span). split; [assumption | reflexivity].
Qed.

Theorem application_ordered_spans_preserve_byte_order :
  forall text spans lower upper,
    OrderedSpans lower upper spans ->
    OrderedSpans (Utf8.scalar_byte_offset text lower)
      (Utf8.scalar_byte_offset text upper)
      (map (application_byte_span text) spans).
Proof.
  intros text spans lower upper Hspans.
  induction Hspans; cbn [map application_byte_span].
  - constructor.
  - constructor; try assumption; now apply Utf8.scalar_byte_offset_monotone.
Qed.

Theorem application_replacement_byte_spans_nonoverlapping :
  forall pattern template text output spans,
    ReplaceAllPlanSpec pattern template text 0 output spans ->
    OrderedSpans 0 (Utf8.utf8_byte_length text)
      (map (application_byte_span text) spans).
Proof.
  intros pattern template text output spans Hplan.
  pose proof
    (replace_all_spans_are_valid_and_non_overlapping
      pattern template text 0 output spans Hplan) as Hspans.
  pose proof
    (application_ordered_spans_preserve_byte_order text spans 0
      (0 + length text) Hspans) as Hbytes.
  rewrite Utf8.scalar_byte_offset_zero in Hbytes.
  change (OrderedSpans 0 (Utf8.scalar_byte_offset text (length text))
    (map (application_byte_span text) spans)) in Hbytes.
  now rewrite Utf8.scalar_byte_offset_at_length in Hbytes.
Qed.

Definition application_pattern : RegexPattern :=
  elaborate_surface
    (SurfaceConcat (SurfaceLiteral scalar_a)
      (SurfacePlus
        (SurfaceAlt (SurfaceLiteral scalar_b) (SurfaceLiteral scalar_c)))).

Example application_full_match_positive :
  full_match application_pattern [scalar_a; scalar_b; scalar_c; scalar_b] = true.
Proof. reflexivity. Qed.

Example application_full_match_negative :
  full_match application_pattern [scalar_a; scalar_x] = false.
Proof. reflexivity. Qed.

Example application_full_match_is_not_search :
  full_match application_pattern [scalar_x; scalar_a; scalar_b] = false.
Proof. reflexivity. Qed.

Example application_nullable_optional :
  nullable (elaborate_surface (SurfaceOptional (SurfaceLiteral scalar_a))) = true.
Proof. reflexivity. Qed.

Example application_derivative_plus :
  derivative scalar_a a_plus = StarPattern (LiteralPattern scalar_a).
Proof. reflexivity. Qed.

Example application_dot_includes_newline : full_match AnyPattern [10] = true.
Proof. reflexivity. Qed.

Example application_repeat_in_range :
  full_match (bounded_repeat (LiteralPattern scalar_a) 2 3)
    [scalar_a; scalar_a; scalar_a] = true.
Proof. reflexivity. Qed.

Example application_repeat_too_short :
  full_match (bounded_repeat (LiteralPattern scalar_a) 2 3) [scalar_a] = false.
Proof. reflexivity. Qed.

Example application_repeat_too_long :
  full_match (bounded_repeat (LiteralPattern scalar_a) 2 3)
    [scalar_a; scalar_a; scalar_a; scalar_a] = false.
Proof. reflexivity. Qed.

Example application_repeat_reversed_bounds :
  bounded_repeat (LiteralPattern scalar_a) 3 2 = FailPattern.
Proof. reflexivity. Qed.

Example application_alternation_is_longest_not_first :
  search_raw
    (AltPattern (LiteralPattern scalar_a)
      (ConcatPattern (LiteralPattern scalar_a) (LiteralPattern scalar_a)))
    [scalar_a; scalar_a] = Some (0, 2).
Proof. reflexivity. Qed.

Example application_search_miss : search a_plus [scalar_b; scalar_c] = None.
Proof. reflexivity. Qed.

Definition application_unicode_text : Text := [233; 955; 955; scalar_x].
Definition application_lambda_plus : RegexPattern :=
  elaborate_surface (SurfacePlus (SurfaceLiteral 955)).

Example application_unicode_search_scalar_span :
  search application_lambda_plus application_unicode_text =
    Some {| span_start := 1; span_end := 3 |}.
Proof. reflexivity. Qed.

Example application_unicode_search_byte_span :
  option_map (application_byte_span application_unicode_text)
    (search application_lambda_plus application_unicode_text) =
    Some {| span_start := 2; span_end := 6 |}.
Proof. reflexivity. Qed.

Example application_unicode_is_not_normalized :
  full_match (LiteralPattern 233) [101; 769] = false.
Proof. reflexivity. Qed.

Definition application_bracket_template : ReplacementTemplateValue :=
  ReplacementAppendValue (ReplacementLiteralValue [91])
    (ReplacementAppendValue ReplacementWholeValue
      (ReplacementLiteralValue [93])).

Example application_whole_match_replacement :
  replace_first a_plus application_bracket_template
    [scalar_b; scalar_a; scalar_a; scalar_c] =
    [scalar_b; 91; scalar_a; scalar_a; 93; scalar_c].
Proof. reflexivity. Qed.

Example application_replacement_miss :
  replace_first a_plus x_template [scalar_b; scalar_c] = [scalar_b; scalar_c].
Proof. reflexivity. Qed.

Example application_empty_unicode_progress :
  replace_all_plan 2 EpsilonPattern x_template [955] 0 =
    RegexProven
      ([scalar_x; 955; scalar_x],
       [{| span_start := 0; span_end := 0 |};
        {| span_start := 1; span_end := 1 |}]).
Proof. reflexivity. Qed.

Example application_empty_at_end_after_nonempty :
  replace_all_plan 2 (StarPattern (LiteralPattern scalar_a)) x_template
    [scalar_a] 0 =
    RegexProven
      ([scalar_x; scalar_x],
       [{| span_start := 0; span_end := 1 |};
        {| span_start := 1; span_end := 1 |}]).
Proof. reflexivity. Qed.

Example application_replacement_work_exhaustion :
  replace_all_plan 1 EpsilonPattern x_template [955] 0 =
    RegexUndetermined WorkExhausted.
Proof. reflexivity. Qed.

Example application_replacement_output_exhaustion :
  bounded_replace_all
    {| maximum_replacement_steps := 2; maximum_output_scalars := 2 |}
    EpsilonPattern x_template [955] = RegexUndetermined OutputExhausted.
Proof. reflexivity. Qed.

Print Assumptions application_search_byte_span_valid.
Print Assumptions application_ordered_spans_preserve_byte_order.
Print Assumptions application_replacement_byte_spans_nonoverlapping.
Print Assumptions application_full_match_positive.
Print Assumptions application_full_match_negative.
Print Assumptions application_full_match_is_not_search.
Print Assumptions application_nullable_optional.
Print Assumptions application_derivative_plus.
Print Assumptions application_dot_includes_newline.
Print Assumptions application_repeat_in_range.
Print Assumptions application_repeat_too_short.
Print Assumptions application_repeat_too_long.
Print Assumptions application_repeat_reversed_bounds.
Print Assumptions application_alternation_is_longest_not_first.
Print Assumptions application_search_miss.
Print Assumptions application_unicode_search_scalar_span.
Print Assumptions application_unicode_search_byte_span.
Print Assumptions application_unicode_is_not_normalized.
Print Assumptions application_whole_match_replacement.
Print Assumptions application_replacement_miss.
Print Assumptions application_empty_unicode_progress.
Print Assumptions application_empty_at_end_after_nonempty.
Print Assumptions application_replacement_work_exhaustion.
Print Assumptions application_replacement_output_exhaustion.
