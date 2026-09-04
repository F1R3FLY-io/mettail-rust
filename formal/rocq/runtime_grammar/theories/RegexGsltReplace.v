(**
  RegexGsltReplace.v

  Replacement semantics derived from the proved leftmost-longest search.
  [replace_all_plan] emits both output and a trace of absolute match spans.
  Its relational specification makes output construction, non-overlap, and
  zero-length progress explicit.  Fuel and output limits return
  [RegexUndetermined] and therefore cannot fabricate a successful result.
*)

From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch RegexGsltSearch.
Import ListNotations.

Inductive ReplacementTemplateValue : Type :=
| ReplacementEmptyValue
| ReplacementLiteralValue : Text -> ReplacementTemplateValue
| ReplacementWholeValue
| ReplacementAppendValue :
    ReplacementTemplateValue -> ReplacementTemplateValue ->
    ReplacementTemplateValue.

Fixpoint render_replacement
    (template : ReplacementTemplateValue) (matched_text : Text) : Text :=
  match template with
  | ReplacementEmptyValue => []
  | ReplacementLiteralValue literal => literal
  | ReplacementWholeValue => matched_text
  | ReplacementAppendValue lhs rhs =>
      render_replacement lhs matched_text ++
      render_replacement rhs matched_text
  end.

Definition matched_segment
    (text : Text) (start matched_length : nat) : Text :=
  firstn matched_length (skipn start text).

Definition replacement_for
    (template : ReplacementTemplateValue)
    (text : Text) (start matched_length : nat) : Text :=
  render_replacement template (matched_segment text start matched_length).

Definition replace_at
    (text : Text) (start matched_length : nat) (replacement : Text) : Text :=
  firstn start text ++ replacement ++ skipn (start + matched_length) text.

Definition replace_first
    (pattern : RegexPattern)
    (template : ReplacementTemplateValue)
    (text : Text) : Text :=
  match search_raw pattern text with
  | None => text
  | Some (start, matched_length) =>
      replace_at text start matched_length
        (replacement_for template text start matched_length)
  end.

Theorem replace_first_miss_is_identity :
  forall pattern template text,
    search_raw pattern text = None ->
    replace_first pattern template text = text.
Proof.
  intros pattern template text Hsearch.
  unfold replace_first. now rewrite Hsearch.
Qed.

Theorem replace_first_hit_has_the_specified_output :
  forall pattern template text start matched_length,
    search_raw pattern text = Some (start, matched_length) ->
    replace_first pattern template text =
      firstn start text ++
      replacement_for template text start matched_length ++
      skipn (start + matched_length) text.
Proof.
  intros pattern template text start matched_length Hsearch.
  unfold replace_first, replace_at. now rewrite Hsearch.
Qed.

Definition absolute_span
    (offset start matched_length : nat) : MatchSpan :=
  {| span_start := offset + start;
     span_end := offset + start + matched_length |}.

Fixpoint replace_all_plan
    (fuel : nat)
    (pattern : RegexPattern)
    (template : ReplacementTemplateValue)
    (text : Text)
    (offset : nat)
    : RegexDecision (Text * list MatchSpan) :=
  match fuel with
  | 0 => RegexUndetermined WorkExhausted
  | S remaining_fuel =>
      match search_raw pattern text with
      | None => RegexProven (text, [])
      | Some (start, matched_length) =>
          let replacement := replacement_for template text start matched_length in
          let span := absolute_span offset start matched_length in
          match matched_length with
          | 0 =>
              match skipn start text with
              | [] =>
                  RegexProven (firstn start text ++ replacement, [span])
              | scalar :: rest =>
                  match replace_all_plan remaining_fuel pattern template rest
                          (offset + start + 1) with
                  | RegexUndetermined reason => RegexUndetermined reason
                  | RegexProven (rest_output, rest_spans) =>
                      RegexProven
                        (firstn start text ++ replacement ++ scalar :: rest_output,
                         span :: rest_spans)
                  end
              end
          | S positive_tail =>
              let remainder := skipn (start + S positive_tail) text in
              match replace_all_plan remaining_fuel pattern template remainder
                      (offset + start + S positive_tail) with
              | RegexUndetermined reason => RegexUndetermined reason
              | RegexProven (rest_output, rest_spans) =>
                  RegexProven
                    (firstn start text ++ replacement ++ rest_output,
                     span :: rest_spans)
              end
          end
      end
  end.

Inductive ReplaceAllPlanSpec
    (pattern : RegexPattern) (template : ReplacementTemplateValue)
    : Text -> nat -> Text -> list MatchSpan -> Prop :=
| ReplaceAllNoMatch : forall text offset,
    search_raw pattern text = None ->
    ReplaceAllPlanSpec pattern template text offset text []
| ReplaceAllNonEmpty :
    forall text offset start positive_tail rest_output rest_spans,
    search_raw pattern text = Some (start, S positive_tail) ->
    ReplaceAllPlanSpec pattern template
      (skipn (start + S positive_tail) text)
      (offset + start + S positive_tail)
      rest_output rest_spans ->
    ReplaceAllPlanSpec pattern template text offset
      (firstn start text ++
       replacement_for template text start (S positive_tail) ++
       rest_output)
      (absolute_span offset start (S positive_tail) :: rest_spans)
| ReplaceAllEmptyAtEnd : forall text offset start,
    search_raw pattern text = Some (start, 0) ->
    skipn start text = [] ->
    ReplaceAllPlanSpec pattern template text offset
      (firstn start text ++ replacement_for template text start 0)
      [absolute_span offset start 0]
| ReplaceAllEmptyWithProgress :
    forall text offset start scalar rest rest_output rest_spans,
    search_raw pattern text = Some (start, 0) ->
    skipn start text = scalar :: rest ->
    ReplaceAllPlanSpec pattern template rest (offset + start + 1)
      rest_output rest_spans ->
    ReplaceAllPlanSpec pattern template text offset
      (firstn start text ++ replacement_for template text start 0 ++
       scalar :: rest_output)
      (absolute_span offset start 0 :: rest_spans).

Theorem replace_all_plan_is_sound :
  forall fuel pattern template text offset output spans,
    replace_all_plan fuel pattern template text offset =
      RegexProven (output, spans) ->
    ReplaceAllPlanSpec pattern template text offset output spans.
Proof.
  induction fuel as [| remaining_fuel IH];
    intros pattern template text offset output spans Hrun.
  - discriminate.
  - simpl in Hrun.
    destruct (search_raw pattern text) as [[start matched_length]|]
      eqn:Hsearch.
    + destruct matched_length as [| positive_tail].
      * remember (skipn start text) as suffix eqn:Hsuffix.
        destruct suffix as [| scalar rest].
        -- inversion Hrun; subst output spans.
           eapply ReplaceAllEmptyAtEnd;
             [exact Hsearch | symmetry; exact Hsuffix].
        -- destruct
             (replace_all_plan remaining_fuel pattern template rest
               (offset + start + 1))
             as [[rest_output rest_spans]|reason] eqn:Hrest;
             try discriminate.
           inversion Hrun; subst output spans.
           eapply ReplaceAllEmptyWithProgress;
             [exact Hsearch | symmetry; exact Hsuffix |].
           eapply IH. exact Hrest.
      * destruct
          (replace_all_plan remaining_fuel pattern template
            (skipn (start + S positive_tail) text)
            (offset + start + S positive_tail))
          as [[rest_output rest_spans]|reason] eqn:Hrest;
          try discriminate.
        inversion Hrun; subst output spans.
        eapply ReplaceAllNonEmpty; [exact Hsearch|].
        eapply IH. exact Hrest.
    + inversion Hrun; subst output spans.
      now apply ReplaceAllNoMatch.
Qed.

Lemma search_raw_result_fits_in_text :
  forall pattern text start matched_length,
    search_raw pattern text = Some (start, matched_length) ->
    start + matched_length <= length text.
Proof.
  intros pattern text start matched_length Hsearch.
  apply (search_candidate_fits_in_text pattern text start matched_length).
  now apply search_raw_returns_a_candidate.
Qed.

Theorem empty_match_either_finishes_or_consumes_a_scalar :
  forall pattern text start,
    search_raw pattern text = Some (start, 0) ->
    match skipn start text with
    | [] => start = length text
    | _ :: rest => length rest < length text
    end.
Proof.
  intros pattern text start Hsearch.
  pose proof (search_raw_result_fits_in_text pattern text start 0 Hsearch)
    as Hstart.
  remember (skipn start text) as suffix eqn:Hsuffix.
  destruct suffix as [| scalar rest].
  - assert (length (skipn start text) = 0) as Hlength.
    { rewrite <- Hsuffix. reflexivity. }
    rewrite length_skipn in Hlength. lia.
  - assert (length (skipn start text) = S (length rest)) as Hlength.
    { rewrite <- Hsuffix. reflexivity. }
    rewrite length_skipn in Hlength. lia.
Qed.

Inductive OrderedSpans (lower upper : nat) : list MatchSpan -> Prop :=
| OrderedSpansNil : OrderedSpans lower upper []
| OrderedSpansCons : forall span rest,
    lower <= span_start span ->
    span_start span <= span_end span ->
    span_end span <= upper ->
    OrderedSpans (span_end span) upper rest ->
    OrderedSpans lower upper (span :: rest).

Lemma ordered_spans_weaken_lower :
  forall weaker stronger upper spans,
    weaker <= stronger ->
    OrderedSpans stronger upper spans ->
    OrderedSpans weaker upper spans.
Proof.
  intros weaker stronger upper spans Hlower Hordered.
  inversion Hordered; subst; constructor; try assumption; lia.
Qed.

Theorem replace_all_spans_are_valid_and_non_overlapping :
  forall pattern template text offset output spans,
    ReplaceAllPlanSpec pattern template text offset output spans ->
    OrderedSpans offset (offset + length text) spans.
Proof.
  intros pattern template text offset output spans Hspec.
  induction Hspec.
  - constructor.
  - pose proof
      (search_raw_result_fits_in_text
        pattern text start (S positive_tail) H) as Hfits.
    constructor; simpl.
    + lia.
    + lia.
    + lia.
    + replace (offset + length text) with
        ((offset + start + S positive_tail) +
         length (skipn (start + S positive_tail) text)).
      * exact IHHspec.
      * rewrite length_skipn. lia.
  - pose proof
      (search_raw_result_fits_in_text pattern text start 0 H) as Hfits.
    constructor; simpl; try lia. constructor.
  - pose proof
      (search_raw_result_fits_in_text pattern text start 0 H) as Hfits.
    constructor; simpl; try lia.
    replace (offset + start + 0) with (offset + start) by lia.
    apply (ordered_spans_weaken_lower
      (offset + start) (offset + start + 1) (offset + length text)
      rest_spans); [lia|].
    replace (offset + length text) with
      ((offset + start + 1) + length rest).
    + exact IHHspec.
    + assert (length (skipn start text) = S (length rest)) as Hlength.
      { rewrite H0. reflexivity. }
      rewrite length_skipn in Hlength. lia.
Qed.

Theorem replace_all_plan_terminates_with_sufficient_fuel :
  forall fuel pattern template text offset,
    length text < fuel ->
    exists output spans,
      replace_all_plan fuel pattern template text offset =
        RegexProven (output, spans).
Proof.
  induction fuel as [| remaining_fuel IH];
    intros pattern template text offset Hfuel; [simpl in Hfuel; lia|].
  simpl.
  destruct (search_raw pattern text) as [[start matched_length]|]
    eqn:Hsearch.
  - pose proof
      (search_raw_result_fits_in_text
        pattern text start matched_length Hsearch) as Hfits.
    destruct matched_length as [| positive_tail].
    + remember (skipn start text) as suffix eqn:Hsuffix.
      destruct suffix as [| scalar rest].
      * eexists. eexists. reflexivity.
      * assert (length rest < remaining_fuel) as Hrest_fuel.
        { assert (length (skipn start text) = S (length rest)) as Hlength.
          { rewrite <- Hsuffix. reflexivity. }
          rewrite length_skipn in Hlength. lia. }
        destruct
          (IH pattern template rest (offset + start + 1) Hrest_fuel)
          as [rest_output [rest_spans Hrest]].
        rewrite Hrest. eexists. eexists. reflexivity.
    + assert
        (length (skipn (start + S positive_tail) text) < remaining_fuel)
        as Hrest_fuel.
      { rewrite length_skipn. lia. }
      destruct
        (IH pattern template
          (skipn (start + S positive_tail) text)
          (offset + start + S positive_tail) Hrest_fuel)
        as [rest_output [rest_spans Hrest]].
      rewrite Hrest. eexists. eexists. reflexivity.
  - eexists. eexists. reflexivity.
Qed.

Record ReplacementExecutionLimits : Type := {
  maximum_replacement_steps : nat;
  maximum_output_scalars : nat
}.

Definition bounded_replace_all
    (limits : ReplacementExecutionLimits)
    (pattern : RegexPattern)
    (template : ReplacementTemplateValue)
    (text : Text) : RegexDecision (Text * list MatchSpan) :=
  match replace_all_plan (maximum_replacement_steps limits)
          pattern template text 0 with
  | RegexUndetermined reason => RegexUndetermined reason
  | RegexProven (output, spans) =>
      if maximum_output_scalars limits <? length output
      then RegexUndetermined OutputExhausted
      else RegexProven (output, spans)
  end.

Theorem bounded_replace_all_never_fabricates_output :
  forall limits pattern template text output spans,
    bounded_replace_all limits pattern template text =
      RegexProven (output, spans) ->
    replace_all_plan (maximum_replacement_steps limits)
      pattern template text 0 = RegexProven (output, spans) /\
    length output <= maximum_output_scalars limits.
Proof.
  intros limits pattern template text output spans Hbounded.
  unfold bounded_replace_all in Hbounded.
  destruct
    (replace_all_plan (maximum_replacement_steps limits)
      pattern template text 0)
    as [[planned_output planned_spans]|reason] eqn:Hplan;
    try discriminate.
  destruct (maximum_output_scalars limits <? length planned_output)
    eqn:Houtput; try discriminate.
  inversion Hbounded; subst output spans.
  split; [reflexivity|].
  apply Nat.ltb_ge. exact Houtput.
Qed.

Definition replacement_decision_commits
    (decision : RegexDecision (Text * list MatchSpan)) : bool :=
  match decision with
  | RegexProven _ => true
  | RegexUndetermined _ => false
  end.

Theorem replacement_exhaustion_fails_closed :
  forall reason,
    replacement_decision_commits (RegexUndetermined reason) = false.
Proof. reflexivity. Qed.

Print Assumptions replace_first_hit_has_the_specified_output.
Print Assumptions replace_all_plan_is_sound.
Print Assumptions empty_match_either_finishes_or_consumes_a_scalar.
Print Assumptions replace_all_spans_are_valid_and_non_overlapping.
Print Assumptions replace_all_plan_terminates_with_sufficient_fuel.
Print Assumptions bounded_replace_all_never_fabricates_output.
Print Assumptions replacement_exhaustion_fails_closed.
