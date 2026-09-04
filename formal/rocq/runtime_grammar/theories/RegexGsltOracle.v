(**
  RegexGsltOracle.v

  Executable regression and finite exhaustive property oracles for the regex
  GSLT reference semantics.  The brute-force search oracle enumerates every
  prefix independently of [longest_prefix], while the replacement oracle
  checks the span certificate emitted by a sufficiently fuelled plan.
  Kernel proofs in the preceding modules establish the properties generally;
  these computations guard the concrete executable model.
*)

From Stdlib Require Import List PeanoNat Bool.
From RuntimeGrammar Require Import
  RegexGsltMatch RegexGsltSearch RegexGsltReplace RegexGsltRules.
Import ListNotations.

Definition scalar_a : Scalar := 97.
Definition scalar_b : Scalar := 98.
Definition scalar_c : Scalar := 99.
Definition scalar_x : Scalar := 120.

Definition a_plus : RegexPattern :=
  elaborate_surface (SurfacePlus (SurfaceLiteral scalar_a)).

Definition ab_or_ac : RegexPattern :=
  elaborate_surface
    (SurfaceConcat (SurfaceLiteral scalar_a)
      (SurfaceAlt (SurfaceLiteral scalar_b) (SurfaceLiteral scalar_c))).

Example exact_match_positive_oracle :
  full_match ab_or_ac [scalar_a; scalar_b] = true.
Proof. reflexivity. Qed.

Example exact_match_negative_oracle :
  full_match ab_or_ac [scalar_a; scalar_x] = false.
Proof. reflexivity. Qed.

Example leftmost_longest_search_oracle :
  search_raw a_plus [scalar_x; scalar_a; scalar_a; scalar_a; scalar_b] =
    Some (1, 3).
Proof. reflexivity. Qed.

Definition x_template : ReplacementTemplateValue :=
  ReplacementLiteralValue [scalar_x].

Example replace_first_oracle :
  replace_first a_plus x_template [scalar_b; scalar_a; scalar_a; scalar_c] =
    [scalar_b; scalar_x; scalar_c].
Proof. reflexivity. Qed.

Example replace_all_non_overlapping_oracle :
  replace_all_plan 5 a_plus x_template
    [scalar_a; scalar_a; scalar_b; scalar_a] 0 =
  RegexProven
    ([scalar_x; scalar_b; scalar_x],
     [{| span_start := 0; span_end := 2 |};
      {| span_start := 3; span_end := 4 |}]).
Proof. reflexivity. Qed.

Example replace_all_empty_match_progress_oracle :
  replace_all_plan 3 EpsilonPattern x_template [scalar_a; scalar_b] 0 =
  RegexProven
    ([scalar_x; scalar_a; scalar_x; scalar_b; scalar_x],
     [{| span_start := 0; span_end := 0 |};
      {| span_start := 1; span_end := 1 |};
      {| span_start := 2; span_end := 2 |}]).
Proof. reflexivity. Qed.

Example replacement_output_bound_oracle :
  bounded_replace_all
    {| maximum_replacement_steps := 3; maximum_output_scalars := 4 |}
    EpsilonPattern x_template [scalar_a; scalar_b] =
  RegexUndetermined OutputExhausted.
Proof. reflexivity. Qed.

Definition brute_force_longest_prefix
    (pattern : RegexPattern) (text : Text) : option nat :=
  fold_left
    (fun current candidate_length =>
       if full_match pattern (firstn candidate_length text)
       then match current with
            | None => Some candidate_length
            | Some prior => Some (Nat.max prior candidate_length)
            end
       else current)
    (seq 0 (S (length text))) None.

Fixpoint brute_force_search
    (pattern : RegexPattern) (text : Text) : option (nat * nat) :=
  match brute_force_longest_prefix pattern text with
  | Some matched_length => Some (0, matched_length)
  | None =>
      match text with
      | [] => None
      | _ :: rest =>
          match brute_force_search pattern rest with
          | Some (start, matched_length) => Some (S start, matched_length)
          | None => None
          end
      end
  end.

Definition optional_pair_eqb
    (lhs rhs : option (nat * nat)) : bool :=
  match lhs, rhs with
  | None, None => true
  | Some (lhs_start, lhs_length), Some (rhs_start, rhs_length) =>
      Nat.eqb lhs_start rhs_start && Nat.eqb lhs_length rhs_length
  | _, _ => false
  end.

Definition oracle_alphabet : list Scalar := [scalar_a; scalar_b].

Fixpoint texts_of_exact_length (size : nat) : list Text :=
  match size with
  | 0 => [[]]
  | S smaller =>
      flat_map
        (fun scalar => map (fun text => scalar :: text)
          (texts_of_exact_length smaller))
        oracle_alphabet
  end.

Definition oracle_texts : list Text :=
  concat (map texts_of_exact_length (seq 0 4)).

Definition base_oracle_patterns : list RegexPattern :=
  [FailPattern; EpsilonPattern; LiteralPattern scalar_a;
   LiteralPattern scalar_b; AnyPattern].

Fixpoint oracle_patterns (depth : nat) : list RegexPattern :=
  match depth with
  | 0 => base_oracle_patterns
  | S smaller =>
      let prior := oracle_patterns smaller in
      base_oracle_patterns ++
      map smart_star prior ++
      flat_map (fun lhs => map (smart_alt lhs) prior) prior ++
      flat_map (fun lhs => map (smart_concat lhs) prior) prior
  end.

Definition search_case_oracle
    (pattern : RegexPattern) (text : Text) : bool :=
  optional_pair_eqb
    (search_raw pattern text)
    (brute_force_search pattern text).

Definition finite_search_property_oracle : bool :=
  forallb
    (fun pattern => forallb (search_case_oracle pattern) oracle_texts)
    (oracle_patterns 1).

Example finite_search_property_oracle_passes :
  finite_search_property_oracle = true.
Proof. vm_compute. reflexivity. Qed.

Fixpoint ordered_spansb
    (lower upper : nat) (spans : list MatchSpan) : bool :=
  match spans with
  | [] => true
  | span :: rest =>
      Nat.leb lower (span_start span) &&
      Nat.leb (span_start span) (span_end span) &&
      Nat.leb (span_end span) upper &&
      ordered_spansb (span_end span) upper rest
  end.

Theorem ordered_spansb_is_sound :
  forall lower upper spans,
    ordered_spansb lower upper spans = true ->
    OrderedSpans lower upper spans.
Proof.
  intros lower upper spans.
  revert lower.
  induction spans as [| span rest IH]; intros lower Hordered.
  - constructor.
  - simpl in Hordered.
    repeat rewrite andb_true_iff in Hordered.
    destruct Hordered as [[[Hlower Hvalid] Hupper] Hrest].
    constructor.
    + now apply Nat.leb_le.
    + now apply Nat.leb_le.
    + now apply Nat.leb_le.
    + now apply IH.
Qed.

Definition replacement_case_oracle
    (pattern : RegexPattern) (text : Text) : bool :=
  match replace_all_plan (S (length text)) pattern x_template text 0 with
  | RegexUndetermined _ => false
  | RegexProven (_, spans) => ordered_spansb 0 (length text) spans
  end.

Definition finite_replacement_property_oracle : bool :=
  forallb
    (fun pattern => forallb (replacement_case_oracle pattern) oracle_texts)
    (oracle_patterns 1).

Example finite_replacement_property_oracle_passes :
  finite_replacement_property_oracle = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions exact_match_positive_oracle.
Print Assumptions leftmost_longest_search_oracle.
Print Assumptions replace_all_non_overlapping_oracle.
Print Assumptions replace_all_empty_match_progress_oracle.
Print Assumptions finite_search_property_oracle_passes.
Print Assumptions ordered_spansb_is_sound.
Print Assumptions finite_replacement_property_oracle_passes.
