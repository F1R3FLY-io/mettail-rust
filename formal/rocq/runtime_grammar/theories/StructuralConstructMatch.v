From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

(** A finite model of the installed-language FLT construction/matching seam.

    Captures below are identifiers of alpha-equivalence classes of normalized
    Rho terms.  Equality is therefore exact equality on the quotient, matching
    the executable boundary where binders have already been normalized to
    de-Bruijn indices.  A prepared pattern owns both the occurrence equality
    plan and the projection into its public, typed capture telescope.  Callers
    may supply only the raw occurrence matches; they cannot assert the public
    captures. *)
Module StructuralConstructMatch.

Inductive LanguageRight : Type :=
| ConstructRight
| MatchRight.

Definition right_eqb (left right : LanguageRight) : bool :=
  match left, right with
  | ConstructRight, ConstructRight | MatchRight, MatchRight => true
  | _, _ => false
  end.

Definition authorized (rights : list LanguageRight) (right : LanguageRight) : bool :=
  existsb (right_eqb right) rights.

Inductive Judgment : Type :=
| ConstructJudgment
| MatchJudgment.

Definition required_right (judgment : Judgment) : LanguageRight :=
  match judgment with
  | ConstructJudgment => ConstructRight
  | MatchJudgment => MatchRight
  end.

Theorem construct_authority_does_not_grant_match :
  authorized [ConstructRight] (required_right MatchJudgment) = false.
Proof. reflexivity. Qed.

Theorem match_authority_does_not_grant_construct :
  authorized [MatchRight] (required_right ConstructJudgment) = false.
Proof. reflexivity. Qed.

(** Structural grafting is simultaneous substitution, never source
    interpolation.  [graft_at] shifts a fill once for every guest binder crossed,
    so a free de-Bruijn index in a host fill cannot be captured by guest syntax. *)
Inductive StructuralTerm : Type :=
| Bound : nat -> StructuralTerm
| Atom : nat -> StructuralTerm
| GuestBinder : StructuralTerm -> StructuralTerm
| GuestNode : nat -> list StructuralTerm -> StructuralTerm
| GraftHole : nat -> StructuralTerm.

Fixpoint shift_by (cutoff amount : nat) (term : StructuralTerm) : StructuralTerm :=
  match term with
  | Bound index => Bound (if index <? cutoff then index else index + amount)
  | Atom atom => Atom atom
  | GuestBinder body => GuestBinder (shift_by (S cutoff) amount body)
  | GuestNode tag children => GuestNode tag (map (shift_by cutoff amount) children)
  | GraftHole id => GraftHole id
  end.

Definition FillEnvironment := nat -> option StructuralTerm.

Fixpoint graft_at
    (depth : nat) (environment : FillEnvironment) (term : StructuralTerm)
    : option StructuralTerm :=
  match term with
  | Bound index => Some (Bound index)
  | Atom atom => Some (Atom atom)
  | GuestBinder body =>
      match graft_at (S depth) environment body with
      | Some grafted => Some (GuestBinder grafted)
      | None => None
      end
  | GuestNode tag children =>
      let fix graft_children (remaining : list StructuralTerm)
          : option (list StructuralTerm) :=
          match remaining with
          | [] => Some []
          | child :: rest =>
              match graft_at depth environment child, graft_children rest with
              | Some grafted_child, Some grafted_rest =>
                  Some (grafted_child :: grafted_rest)
              | _, _ => None
              end
          end in
      match graft_children children with
      | Some grafted => Some (GuestNode tag grafted)
      | None => None
      end
  | GraftHole id =>
      match environment id with
      | Some fill => Some (shift_by 0 depth fill)
      | None => None
      end
  end.

Theorem graft_at_hole_is_capture_avoiding :
  forall depth environment id fill,
    environment id = Some fill ->
    graft_at depth environment (GraftHole id) = Some (shift_by 0 depth fill).
Proof. intros depth environment id fill Hfill. simpl. now rewrite Hfill. Qed.

Theorem graft_under_guest_binder_increments_depth :
  forall depth environment body grafted,
    graft_at (S depth) environment body = Some grafted ->
    graft_at depth environment (GuestBinder body) = Some (GuestBinder grafted).
Proof.
  intros depth environment body grafted Hgraft. simpl. now rewrite Hgraft.
Qed.

Example free_fill_is_shifted_past_guest_binder :
  forall environment id,
    environment id = Some (Bound 0) ->
    graft_at 0 environment (GuestBinder (GraftHole id)) =
      Some (GuestBinder (Bound 1)).
Proof. intros environment id Hfill. simpl. now rewrite Hfill. Qed.

Definition LanguageId := nat.
Definition CategoryId := nat.
Definition AlphaClass := nat.

Record TermIndex : Type := {
  index_language : LanguageId;
  index_category : CategoryId
}.

Definition index_eqb (left right : TermIndex) : bool :=
  Nat.eqb (index_language left) (index_language right) &&
  Nat.eqb (index_category left) (index_category right).

Lemma index_eqb_sound :
  forall left right, index_eqb left right = true -> left = right.
Proof.
  intros [ll lc] [rl rc] Hequal. unfold index_eqb in Hequal; simpl in Hequal.
  apply andb_true_iff in Hequal as [Hlanguage Hcategory].
  apply Nat.eqb_eq in Hlanguage. apply Nat.eqb_eq in Hcategory.
  now subst.
Qed.

Lemma index_eqb_complete :
  forall left right, left = right -> index_eqb left right = true.
Proof.
  intros left right ->. destruct right. unfold index_eqb; simpl.
  now rewrite !Nat.eqb_refl.
Qed.

(** [projection] maps each public telescope entry to its first raw occurrence.
    [repetitions] maps each repeated occurrence to that first occurrence. *)
Record PreparedPattern : Type := {
  pattern_index : TermIndex;
  occurrence_count : nat;
  projection : list nat;
  repetitions : list (nat * nat);
  capture_categories : list CategoryId
}.

Definition position_valid (count position : nat) : Prop := position < count.

Definition pattern_well_formed (pattern : PreparedPattern) : Prop :=
  length (projection pattern) = length (capture_categories pattern) /\
  Forall (position_valid (occurrence_count pattern)) (projection pattern) /\
  Forall
    (fun pair =>
       position_valid (occurrence_count pattern) (fst pair) /\
       position_valid (occurrence_count pattern) (snd pair))
    (repetitions pattern).

Definition occurrence_equal
    (captures : list AlphaClass) (pair : nat * nat) : bool :=
  Nat.eqb (nth (fst pair) captures 0) (nth (snd pair) captures 0).

Definition project_captures
    (captures : list AlphaClass) (indices : list nat) : list AlphaClass :=
  map (fun index => nth index captures 0) indices.

Section Matching.
  Variable admits : CategoryId -> AlphaClass -> bool.

  Definition captures_typed
      (categories : list CategoryId) (captures : list AlphaClass) : bool :=
    forallb (fun pair => admits (fst pair) (snd pair)) (combine categories captures).

  (** The subject carries an immutable language/category index.  The matcher
      receives occurrence captures, checks the complete equality plan, derives
      the public telescope itself, and publishes it only after typed admission. *)
  Definition run_match
      (subject_index : TermIndex)
      (pattern : PreparedPattern)
      (occurrences : list AlphaClass) : option (list AlphaClass) :=
    if index_eqb subject_index (pattern_index pattern) then
      if Nat.eqb (length occurrences) (occurrence_count pattern) then
        if forallb (occurrence_equal occurrences) (repetitions pattern) then
          let captures := project_captures occurrences (projection pattern) in
          if captures_typed (capture_categories pattern) captures
          then Some captures
          else None
        else None
      else None
    else None.

  Theorem successful_match_preserves_language_and_category :
    forall subject_index pattern occurrences captures,
      run_match subject_index pattern occurrences = Some captures ->
      subject_index = pattern_index pattern.
  Proof.
    intros subject_index pattern occurrences captures Hmatch.
    unfold run_match in Hmatch.
    destruct (index_eqb subject_index (pattern_index pattern)) eqn:Hindex;
      [now apply index_eqb_sound | discriminate].
  Qed.

  Theorem cross_index_match_is_rejected :
    forall subject_index pattern occurrences,
      subject_index <> pattern_index pattern ->
      run_match subject_index pattern occurrences = None.
  Proof.
    intros subject_index pattern occurrences Hdifferent.
    unfold run_match.
    destruct (index_eqb subject_index (pattern_index pattern)) eqn:Hindex.
    - apply index_eqb_sound in Hindex. contradiction.
    - reflexivity.
  Qed.

  Theorem successful_match_has_exact_occurrence_arity :
    forall subject_index pattern occurrences captures,
      run_match subject_index pattern occurrences = Some captures ->
      length occurrences = occurrence_count pattern.
  Proof.
    intros subject_index pattern occurrences captures Hmatch.
    unfold run_match in Hmatch.
    destruct (index_eqb subject_index (pattern_index pattern)); [|discriminate].
    destruct (Nat.eqb (length occurrences) (occurrence_count pattern))
      eqn:Hlength; [now apply Nat.eqb_eq | discriminate].
  Qed.

  Theorem successful_match_is_matcher_projection :
    forall subject_index pattern occurrences captures,
      run_match subject_index pattern occurrences = Some captures ->
      captures = project_captures occurrences (projection pattern).
  Proof.
    intros subject_index pattern occurrences captures Hmatch.
    unfold run_match in Hmatch.
    destruct (index_eqb subject_index (pattern_index pattern)); [|discriminate].
    destruct (Nat.eqb (length occurrences) (occurrence_count pattern)); [|discriminate].
    destruct (forallb (occurrence_equal occurrences) (repetitions pattern)); [|discriminate].
    remember (project_captures occurrences (projection pattern)) as projected.
    destruct (captures_typed (capture_categories pattern) projected); [|discriminate].
    inversion Hmatch. now subst.
  Qed.

  Theorem successful_match_satisfies_every_repeated_hole :
    forall subject_index pattern occurrences captures first repeated,
      run_match subject_index pattern occurrences = Some captures ->
      In (first, repeated) (repetitions pattern) ->
      nth first occurrences 0 = nth repeated occurrences 0.
  Proof.
    intros subject_index pattern occurrences captures first repeated Hmatch Hin.
    unfold run_match in Hmatch.
    destruct (index_eqb subject_index (pattern_index pattern)); [|discriminate].
    destruct (Nat.eqb (length occurrences) (occurrence_count pattern)); [|discriminate].
    destruct (forallb (occurrence_equal occurrences) (repetitions pattern))
      eqn:Hequalities; [|discriminate].
    apply forallb_forall with (x := (first, repeated)) in Hequalities; [|exact Hin].
    unfold occurrence_equal in Hequalities; simpl in Hequalities.
    now apply Nat.eqb_eq.
  Qed.

  Theorem successful_well_formed_match_has_telescope_arity :
    forall subject_index pattern occurrences captures,
      pattern_well_formed pattern ->
      run_match subject_index pattern occurrences = Some captures ->
      length captures = length (capture_categories pattern).
  Proof.
    intros subject_index pattern occurrences captures [Hprojection _] Hmatch.
    pose proof (successful_match_is_matcher_projection
      subject_index pattern occurrences captures Hmatch) as Hcaptures.
    subst captures. unfold project_captures. rewrite length_map. exact Hprojection.
  Qed.

  Theorem successful_match_has_typed_captures :
    forall subject_index pattern occurrences captures,
      run_match subject_index pattern occurrences = Some captures ->
      captures_typed (capture_categories pattern) captures = true.
  Proof.
    intros subject_index pattern occurrences captures Hmatch.
    unfold run_match in Hmatch.
    destruct (index_eqb subject_index (pattern_index pattern)); [|discriminate].
    destruct (Nat.eqb (length occurrences) (occurrence_count pattern)); [|discriminate].
    destruct (forallb (occurrence_equal occurrences) (repetitions pattern)); [|discriminate].
    remember (project_captures occurrences (projection pattern)) as projected.
    destruct (captures_typed (capture_categories pattern) projected)
      eqn:Htyped; [|discriminate].
    inversion Hmatch. now subst.
  Qed.

  Inductive ReceiveDecision : Type :=
  | RefuseReceive
  | CommitReceive (captures : list AlphaClass).

  Definition decide_receive subject_index pattern occurrences : ReceiveDecision :=
    match run_match subject_index pattern occurrences with
    | Some captures => CommitReceive captures
    | None => RefuseReceive
    end.

  Theorem failed_match_publishes_no_partial_telescope :
    forall subject_index pattern occurrences,
      run_match subject_index pattern occurrences = None ->
      decide_receive subject_index pattern occurrences = RefuseReceive.
  Proof.
    intros subject_index pattern occurrences Hmatch.
    unfold decide_receive. now rewrite Hmatch.
  Qed.
End Matching.

(** Pattern ambiguity is checked before publication.  Equal weighted parses may
    collapse to the same meaning; two distinct meanings have no prepared result. *)
Definition PatternMeaning := nat.

Definition prepare_unique (alternatives : list PatternMeaning) : option PatternMeaning :=
  match alternatives with
  | [] => None
  | first :: rest =>
      if forallb (Nat.eqb first) rest then Some first else None
  end.

Theorem distinct_pattern_meanings_are_rejected :
  forall left right,
    left <> right -> prepare_unique [left; right] = None.
Proof.
  intros left right Hdifferent. unfold prepare_unique; simpl.
  apply Nat.eqb_neq in Hdifferent. now rewrite Hdifferent.
Qed.

Theorem duplicate_pattern_meanings_are_safe_to_collapse :
  forall meaning, prepare_unique [meaning; meaning] = Some meaning.
Proof. intros meaning. unfold prepare_unique; simpl. now rewrite Nat.eqb_refl. Qed.

End StructuralConstructMatch.

Print Assumptions StructuralConstructMatch.construct_authority_does_not_grant_match.
Print Assumptions StructuralConstructMatch.match_authority_does_not_grant_construct.
Print Assumptions StructuralConstructMatch.graft_at_hole_is_capture_avoiding.
Print Assumptions StructuralConstructMatch.graft_under_guest_binder_increments_depth.
Print Assumptions StructuralConstructMatch.free_fill_is_shifted_past_guest_binder.
Print Assumptions StructuralConstructMatch.successful_match_preserves_language_and_category.
Print Assumptions StructuralConstructMatch.cross_index_match_is_rejected.
Print Assumptions StructuralConstructMatch.successful_match_has_exact_occurrence_arity.
Print Assumptions StructuralConstructMatch.successful_match_is_matcher_projection.
Print Assumptions StructuralConstructMatch.successful_match_satisfies_every_repeated_hole.
Print Assumptions StructuralConstructMatch.successful_well_formed_match_has_telescope_arity.
Print Assumptions StructuralConstructMatch.successful_match_has_typed_captures.
Print Assumptions StructuralConstructMatch.failed_match_publishes_no_partial_telescope.
Print Assumptions StructuralConstructMatch.distinct_pattern_meanings_are_rejected.
Print Assumptions StructuralConstructMatch.duplicate_pattern_meanings_are_safe_to_collapse.
