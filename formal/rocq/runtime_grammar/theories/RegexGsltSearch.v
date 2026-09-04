(**
  RegexGsltSearch.v

  Deterministic leftmost-longest search for the GSLT regular-expression
  theory.  Search is defined entirely from the derivative semantics in
  RegexGsltMatch: the longest prefix at a position is selected first, and
  positions are considered from left to right.  A [SearchCandidate] is the
  relational specification against which the executable search is proved.
*)

From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch.
Import ListNotations.

Definition PrefixMatch
    (pattern : RegexPattern) (text : Text) (matched_length : nat) : Prop :=
  matched_length <= length text /\
  full_match pattern (firstn matched_length text) = true.

(** The recursive result is longest because a successful match in the tail
    is necessarily one scalar longer than any nullable match at the current
    state.  Only when the tail has no match may the empty prefix win. *)
Fixpoint longest_prefix
    (pattern : RegexPattern) (text : Text) : option nat :=
  match text with
  | [] => if nullable pattern then Some 0 else None
  | scalar :: rest =>
      match longest_prefix (derivative scalar pattern) rest with
      | Some matched_length => Some (S matched_length)
      | None => if nullable pattern then Some 0 else None
      end
  end.

Theorem longest_prefix_returns_a_match :
  forall pattern text matched_length,
    longest_prefix pattern text = Some matched_length ->
    PrefixMatch pattern text matched_length.
Proof.
  intros pattern text.
  revert pattern.
  induction text as [| scalar rest IH]; intros pattern matched_length Hlongest.
  - simpl in Hlongest.
    destruct (nullable pattern) eqn:Hnullable; try discriminate.
    inversion Hlongest; subst.
    split; [simpl; lia|].
    unfold full_match. simpl. exact Hnullable.
  - simpl in Hlongest.
    remember (longest_prefix (derivative scalar pattern) rest)
      as recursive_result eqn:Hrecursive.
    destruct recursive_result as [rest_length|].
    + inversion Hlongest; subst matched_length.
      specialize (IH (derivative scalar pattern) rest_length (eq_sym Hrecursive)).
      destruct IH as [Hlength Hmatches].
      split; [simpl; lia|].
      simpl.
      rewrite derivative_step_sound.
      exact Hmatches.
    + destruct (nullable pattern) eqn:Hnullable; try discriminate.
      inversion Hlongest; subst matched_length.
      split; [simpl; lia|].
      unfold full_match. simpl. exact Hnullable.
Qed.

Theorem longest_prefix_none_means_no_prefix_matches :
  forall pattern text,
    longest_prefix pattern text = None ->
    forall candidate_length,
      candidate_length <= length text ->
      full_match pattern (firstn candidate_length text) = false.
Proof.
  intros pattern text.
  revert pattern.
  induction text as [| scalar rest IH];
    intros pattern Hnone candidate_length Hlength.
  - simpl in Hnone.
    destruct (nullable pattern) eqn:Hnullable; try discriminate.
    assert (candidate_length = 0) by (simpl in Hlength; lia).
    subst candidate_length.
    unfold full_match. simpl. exact Hnullable.
  - simpl in Hnone.
    remember (longest_prefix (derivative scalar pattern) rest)
      as recursive_result eqn:Hrecursive.
    destruct recursive_result as [rest_length|]; try discriminate.
    destruct (nullable pattern) eqn:Hnullable; try discriminate.
    destruct candidate_length as [| rest_candidate].
    + unfold full_match. simpl. exact Hnullable.
    + simpl.
      rewrite derivative_step_sound.
      apply (IH (derivative scalar pattern) (eq_sym Hrecursive)
        rest_candidate).
      simpl in Hlength. lia.
Qed.

Theorem longest_prefix_is_maximal :
  forall pattern text longest_length,
    longest_prefix pattern text = Some longest_length ->
    forall candidate_length,
      PrefixMatch pattern text candidate_length ->
      candidate_length <= longest_length.
Proof.
  intros pattern text.
  revert pattern.
  induction text as [| scalar rest IH];
    intros pattern longest_length Hlongest candidate_length Hcandidate.
  - destruct Hcandidate as [Hlength _].
    simpl in Hlength. lia.
  - simpl in Hlongest.
    remember (longest_prefix (derivative scalar pattern) rest)
      as recursive_result eqn:Hrecursive.
    destruct recursive_result as [rest_length|].
    + inversion Hlongest; subst longest_length.
      destruct candidate_length as [| rest_candidate]; [lia|].
      assert (rest_candidate <= rest_length) as Hrest_maximal.
      { apply (IH (derivative scalar pattern) rest_length
          (eq_sym Hrecursive) rest_candidate).
        destruct Hcandidate as [Hlength Hmatches].
        split.
        - simpl in Hlength. lia.
        - simpl in Hmatches.
          rewrite derivative_step_sound in Hmatches.
          exact Hmatches. }
      lia.
    + destruct (nullable pattern) eqn:Hnullable; try discriminate.
      inversion Hlongest; subst longest_length.
      destruct candidate_length as [| rest_candidate]; [lia|].
      destruct Hcandidate as [Hlength Hmatches].
      simpl in Hmatches.
      rewrite derivative_step_sound in Hmatches.
      pose proof
        (longest_prefix_none_means_no_prefix_matches
          (derivative scalar pattern) rest (eq_sym Hrecursive)
          rest_candidate) as Hno_match.
      assert (rest_candidate <= length rest) by
        (simpl in Hlength; lia).
      specialize (Hno_match H).
      rewrite Hmatches in Hno_match. discriminate.
Qed.

(** A candidate records a match length at a start position.  This inductive
    presentation avoids defining substring arithmetic in the trusted model:
    moving right consumes one actual scalar, while a match at the current
    position is exactly a prefix match. *)
Inductive SearchCandidate (pattern : RegexPattern)
    : Text -> nat -> nat -> Prop :=
| CandidateHere : forall text matched_length,
    PrefixMatch pattern text matched_length ->
    SearchCandidate pattern text 0 matched_length
| CandidateLater : forall scalar rest start matched_length,
    SearchCandidate pattern rest start matched_length ->
    SearchCandidate pattern (scalar :: rest) (S start) matched_length.

Lemma candidate_at_zero_is_a_prefix :
  forall pattern text matched_length,
    SearchCandidate pattern text 0 matched_length ->
    PrefixMatch pattern text matched_length.
Proof. intros pattern text matched_length Hcandidate; inversion Hcandidate; assumption. Qed.

Lemma candidate_after_one_scalar_is_in_the_tail :
  forall pattern scalar rest start matched_length,
    SearchCandidate pattern (scalar :: rest) (S start) matched_length ->
    SearchCandidate pattern rest start matched_length.
Proof. intros pattern scalar rest start matched_length Hcandidate; inversion Hcandidate; assumption. Qed.

Fixpoint search_raw
    (pattern : RegexPattern) (text : Text) : option (nat * nat) :=
  match longest_prefix pattern text with
  | Some matched_length => Some (0, matched_length)
  | None =>
      match text with
      | [] => None
      | _ :: rest =>
          match search_raw pattern rest with
          | Some (start, matched_length) => Some (S start, matched_length)
          | None => None
          end
      end
  end.

Theorem search_raw_returns_a_candidate :
  forall pattern text start matched_length,
    search_raw pattern text = Some (start, matched_length) ->
    SearchCandidate pattern text start matched_length.
Proof.
  intros pattern text.
  induction text as [| scalar rest IH]; intros start matched_length Hsearch.
  - change
      (match longest_prefix pattern [] with
       | Some prefix_length => Some (0, prefix_length)
       | None => None
       end = Some (start, matched_length)) in Hsearch.
    destruct (longest_prefix pattern []) eqn:Hlongest; try discriminate.
    inversion Hsearch; subst.
    constructor. now apply longest_prefix_returns_a_match.
  - change
      (match longest_prefix pattern (scalar :: rest) with
       | Some prefix_length => Some (0, prefix_length)
       | None =>
           match search_raw pattern rest with
           | Some (rest_start, rest_length) => Some (S rest_start, rest_length)
           | None => None
           end
       end = Some (start, matched_length)) in Hsearch.
    destruct (longest_prefix pattern (scalar :: rest))
      as [prefix_length|] eqn:Hlongest.
    + inversion Hsearch; subst.
      constructor. now apply longest_prefix_returns_a_match.
    + destruct (search_raw pattern rest) as [[rest_start rest_length]|]
        eqn:Hrest; try discriminate.
      inversion Hsearch; subst.
      constructor. now apply IH.
Qed.

Theorem search_raw_none_means_no_candidate :
  forall pattern text,
    search_raw pattern text = None ->
    forall start matched_length,
      ~ SearchCandidate pattern text start matched_length.
Proof.
  intros pattern text.
  induction text as [| scalar rest IH];
    intros Hsearch start matched_length Hcandidate.
  - destruct start as [| impossible_start].
    2: inversion Hcandidate.
    change
      (match longest_prefix pattern [] with
       | Some prefix_length => Some (0, prefix_length)
       | None => None
       end = None) in Hsearch.
    destruct (longest_prefix pattern []) eqn:Hlongest; try discriminate.
    pose proof
      (candidate_at_zero_is_a_prefix pattern [] matched_length Hcandidate)
      as [Hlength Hmatches].
    pose proof
      (longest_prefix_none_means_no_prefix_matches
        pattern [] Hlongest matched_length Hlength) as Hno_match.
    rewrite Hmatches in Hno_match. discriminate.
  - change
      (match longest_prefix pattern (scalar :: rest) with
       | Some prefix_length => Some (0, prefix_length)
       | None =>
           match search_raw pattern rest with
           | Some (rest_start, rest_length) => Some (S rest_start, rest_length)
           | None => None
           end
       end = None) in Hsearch.
    destruct (longest_prefix pattern (scalar :: rest))
      as [prefix_length|] eqn:Hlongest; try discriminate.
    destruct (search_raw pattern rest) as [[rest_start rest_length]|]
      eqn:Hrest; try discriminate.
    destruct start as [| tail_start].
    + pose proof
        (candidate_at_zero_is_a_prefix
          pattern (scalar :: rest) matched_length Hcandidate)
        as [Hlength Hmatches].
      pose proof
        (longest_prefix_none_means_no_prefix_matches
          pattern (scalar :: rest) Hlongest matched_length Hlength)
        as Hno_match.
      rewrite Hmatches in Hno_match. discriminate.
    + apply (IH eq_refl tail_start matched_length).
      now apply (candidate_after_one_scalar_is_in_the_tail
        pattern scalar rest tail_start matched_length).
Qed.

Theorem search_raw_is_leftmost_longest :
  forall pattern text start matched_length,
    search_raw pattern text = Some (start, matched_length) ->
    forall candidate_start candidate_length,
      SearchCandidate pattern text candidate_start candidate_length ->
      start <= candidate_start /\
      (start = candidate_start -> candidate_length <= matched_length).
Proof.
  intros pattern text.
  induction text as [| scalar rest IH];
    intros start matched_length Hsearch candidate_start candidate_length
      Hcandidate.
  - change
      (match longest_prefix pattern [] with
       | Some prefix_length => Some (0, prefix_length)
       | None => None
       end = Some (start, matched_length)) in Hsearch.
    destruct (longest_prefix pattern []) as [prefix_length|]
      eqn:Hlongest; try discriminate.
    inversion Hsearch; subst start matched_length.
    destruct candidate_start as [| impossible_start].
    2: inversion Hcandidate.
    split; [lia|].
    intros _.
    apply (longest_prefix_is_maximal
      pattern [] prefix_length Hlongest candidate_length).
    now apply candidate_at_zero_is_a_prefix.
  - change
      (match longest_prefix pattern (scalar :: rest) with
       | Some prefix_length => Some (0, prefix_length)
       | None =>
           match search_raw pattern rest with
           | Some (rest_start, rest_length) => Some (S rest_start, rest_length)
           | None => None
           end
       end = Some (start, matched_length)) in Hsearch.
    destruct (longest_prefix pattern (scalar :: rest))
      as [prefix_length|] eqn:Hlongest.
    + inversion Hsearch; subst start matched_length.
      destruct candidate_start as [| tail_start].
      * split; [lia|].
        intros _.
        apply (longest_prefix_is_maximal
          pattern (scalar :: rest) prefix_length Hlongest candidate_length).
        now apply candidate_at_zero_is_a_prefix.
      * split; [lia|]. intros Habsurd. lia.
    + destruct (search_raw pattern rest) as [[rest_start rest_length]|]
        eqn:Hrest; try discriminate.
      inversion Hsearch; subst start matched_length.
      destruct candidate_start as [| tail_start].
      * pose proof
          (candidate_at_zero_is_a_prefix
            pattern (scalar :: rest) candidate_length Hcandidate)
          as [Hlength Hmatches].
        pose proof
          (longest_prefix_none_means_no_prefix_matches
            pattern (scalar :: rest) Hlongest candidate_length Hlength)
          as Hno_match.
        rewrite Hmatches in Hno_match. discriminate.
      * pose proof
          (candidate_after_one_scalar_is_in_the_tail
            pattern scalar rest tail_start candidate_length Hcandidate)
          as Htail_candidate.
        pose proof
          (IH rest_start rest_length eq_refl
            tail_start candidate_length Htail_candidate) as Hoptimal.
        destruct Hoptimal as [Hleftmost Hlongest_same].
        split; [lia|].
        intros Hequal.
        apply Hlongest_same. lia.
Qed.

Record MatchSpan : Type := {
  span_start : nat;
  span_end : nat
}.

Definition search
    (pattern : RegexPattern) (text : Text) : option MatchSpan :=
  match search_raw pattern text with
  | Some (start, matched_length) =>
      Some {| span_start := start; span_end := start + matched_length |}
  | None => None
  end.

Lemma search_candidate_fits_in_text :
  forall pattern text start matched_length,
    SearchCandidate pattern text start matched_length ->
    start + matched_length <= length text.
Proof.
  intros pattern text start matched_length Hcandidate.
  induction Hcandidate.
  - destruct H as [Hlength _]. simpl. exact Hlength.
  - simpl. lia.
Qed.

Theorem search_span_is_valid :
  forall pattern text span,
    search pattern text = Some span ->
    span_start span <= span_end span /\
    span_end span <= length text.
Proof.
  intros pattern text span Hsearch.
  unfold search in Hsearch.
  destruct (search_raw pattern text) as [[start matched_length]|]
    eqn:Hraw; try discriminate.
  inversion Hsearch; subst span. simpl.
  split; [lia|].
  apply (search_candidate_fits_in_text pattern text start matched_length).
  now apply search_raw_returns_a_candidate.
Qed.

Theorem search_is_observably_deterministic :
  forall pattern text lhs rhs,
    search pattern text = lhs ->
    search pattern text = rhs ->
    lhs = rhs.
Proof. congruence. Qed.

Print Assumptions longest_prefix_returns_a_match.
Print Assumptions longest_prefix_none_means_no_prefix_matches.
Print Assumptions longest_prefix_is_maximal.
Print Assumptions search_raw_returns_a_candidate.
Print Assumptions search_raw_none_means_no_candidate.
Print Assumptions search_raw_is_leftmost_longest.
Print Assumptions search_span_is_valid.
Print Assumptions search_is_observably_deterministic.
