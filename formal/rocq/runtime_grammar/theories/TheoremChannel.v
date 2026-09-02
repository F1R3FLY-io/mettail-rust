From Stdlib Require Import List Bool PeanoNat.
From RuntimeGrammar Require Import CapabilitySeparation.
Import ListNotations.

Definition LanguageId := nat.
Definition CategoryId := nat.
Definition TermHash := nat.
Definition CheckerAbi := nat.
Definition LimitProfile := nat.

Record Flt : Type := {
  flt_language : LanguageId;
  flt_category : CategoryId;
  flt_hash : TermHash
}.

Inductive AdmissionTheorem : Type :=
| Bottom : AdmissionTheorem
| Membership : CategoryId -> AdmissionTheorem
| ExactTerm : CategoryId -> TermHash -> AdmissionTheorem.

(* The executable Rust representation is a collision-resistant digest.  The
   proof model uses the collision-free semantic quotient itself as its id. *)
Definition TheoremId := AdmissionTheorem.
Definition StructuralCheckerAbi : CheckerAbi := 1.
Definition StructuralLimitProfile : LimitProfile := 1.

Definition theorem_eqb (left right : AdmissionTheorem) : bool :=
  match left, right with
  | Bottom, Bottom => true
  | Membership left_category, Membership right_category =>
      Nat.eqb left_category right_category
  | ExactTerm left_category left_hash, ExactTerm right_category right_hash =>
      Nat.eqb left_category right_category && Nat.eqb left_hash right_hash
  | _, _ => false
  end.

Definition theorem_holds (term : Flt) (theorem : AdmissionTheorem) : bool :=
  match theorem with
  | Bottom => false
  | Membership category => Nat.eqb (flt_category term) category
  | ExactTerm category hash =>
      Nat.eqb (flt_category term) category && Nat.eqb (flt_hash term) hash
  end.

Definition Holds (term : Flt) (theorem : AdmissionTheorem) : Prop :=
  match theorem with
  | Bottom => False
  | Membership category => flt_category term = category
  | ExactTerm category hash =>
      flt_category term = category /\ flt_hash term = hash
  end.

Definition meet (left right : AdmissionTheorem) : AdmissionTheorem :=
  match left, right with
  | Bottom, _ | _, Bottom => Bottom
  | Membership left_category, Membership right_category =>
      if Nat.eqb left_category right_category
      then Membership left_category
      else Bottom
  | ExactTerm exact_category hash, Membership member_category
  | Membership member_category, ExactTerm exact_category hash =>
      if Nat.eqb exact_category member_category
      then ExactTerm exact_category hash
      else Bottom
  | ExactTerm left_category left_hash, ExactTerm right_category right_hash =>
      if Nat.eqb left_category right_category && Nat.eqb left_hash right_hash
      then ExactTerm left_category left_hash
      else Bottom
  end.

Lemma theorem_eqb_sound :
  forall left right, theorem_eqb left right = true -> left = right.
Proof.
  destruct left as [| left_category | left_category left_hash];
    destruct right as [| right_category | right_category right_hash];
    simpl; intros H;
    try discriminate.
  - reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H as [Hcategory Hhash].
    apply Nat.eqb_eq in Hcategory. apply Nat.eqb_eq in Hhash.
    subst. reflexivity.
Qed.

Lemma theorem_eqb_complete :
  forall left right, left = right -> theorem_eqb left right = true.
Proof.
  intros left right ->. destruct right; simpl.
  - reflexivity.
  - apply Nat.eqb_refl.
  - rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma theorem_holds_sound :
  forall term theorem, theorem_holds term theorem = true -> Holds term theorem.
Proof.
  intros term theorem. destruct theorem as [| category | category hash];
    simpl; intros H.
  - discriminate.
  - apply Nat.eqb_eq. exact H.
  - apply andb_true_iff in H as [Hcategory Hhash]. split.
    + apply Nat.eqb_eq. exact Hcategory.
    + apply Nat.eqb_eq. exact Hhash.
Qed.

Lemma theorem_holds_complete :
  forall term theorem, Holds term theorem -> theorem_holds term theorem = true.
Proof.
  intros term theorem. destruct theorem as [| category | category hash];
    simpl; intros H.
  - contradiction.
  - apply Nat.eqb_eq. exact H.
  - destruct H as [Hcategory Hhash]. apply andb_true_iff. split.
    + apply Nat.eqb_eq. exact Hcategory.
    + apply Nat.eqb_eq. exact Hhash.
Qed.

Lemma meet_sound :
  forall term left right,
    Holds term (meet left right) -> Holds term left /\ Holds term right.
Proof.
  intros term left right.
  destruct left as [| left_category | left_category left_hash];
    destruct right as [| right_category | right_category right_hash];
    simpl; try tauto.
  - destruct (Nat.eqb left_category right_category) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. simpl. tauto.
    + simpl. tauto.
  - destruct (Nat.eqb right_category left_category) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. simpl. tauto.
    + simpl. tauto.
  - destruct (Nat.eqb left_category right_category) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. simpl. tauto.
    + simpl. tauto.
  - destruct
      (Nat.eqb left_category right_category && Nat.eqb left_hash right_hash)
      eqn:Heq.
    + apply andb_true_iff in Heq as [Hcategory Hhash].
      apply Nat.eqb_eq in Hcategory. apply Nat.eqb_eq in Hhash.
      subst. simpl. tauto.
    + simpl. tauto.
Qed.

Lemma meet_complete :
  forall term left right,
    Holds term left /\ Holds term right -> Holds term (meet left right).
Proof.
  intros term left right.
  destruct left as [| left_category | left_category left_hash];
    destruct right as [| right_category | right_category right_hash];
    simpl; intros H.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [Hleft Hright].
    assert (left_category = right_category) as Heq.
    { transitivity (flt_category term); [symmetry |]; assumption. }
    subst. rewrite Nat.eqb_refl. assumption.
  - destruct H as [Hleft [Hright_category Hright_hash]].
    pose proof (conj Hright_category Hright_hash) as Hexact.
    assert (right_category = left_category) as Heq.
    { transitivity (flt_category term); [symmetry |]; assumption. }
    subst. rewrite Nat.eqb_refl. exact Hexact.
  - tauto.
  - destruct H as [[Hleft_category Hleft_hash] Hright].
    pose proof (conj Hleft_category Hleft_hash) as Hexact.
    assert (left_category = right_category) as Heq.
    { transitivity (flt_category term); [symmetry |]; assumption. }
    subst. rewrite Nat.eqb_refl. exact Hexact.
  - destruct H as [[Hleft_category Hleft_hash]
                    [Hright_category Hright_hash]].
    pose proof (conj Hleft_category Hleft_hash) as Hexact.
    assert (left_category = right_category) as Hcategory.
    { transitivity (flt_category term); [symmetry |]; assumption. }
    assert (left_hash = right_hash) as Hhash.
    { transitivity (flt_hash term); [symmetry |]; assumption. }
    subst. rewrite !Nat.eqb_refl. exact Hexact.
Qed.

Theorem meet_is_semantic_conjunction :
  forall term left right,
    Holds term (meet left right) <-> Holds term left /\ Holds term right.
Proof. intros. split; [apply meet_sound | apply meet_complete]. Qed.

Theorem meet_semantically_commutative :
  forall term left right,
    Holds term (meet left right) <-> Holds term (meet right left).
Proof.
  intros. rewrite !meet_is_semantic_conjunction. tauto.
Qed.

Theorem meet_semantically_associative :
  forall term first second third,
    Holds term (meet (meet first second) third) <->
    Holds term (meet first (meet second third)).
Proof.
  intros. rewrite !meet_is_semantic_conjunction. tauto.
Qed.

Theorem meet_semantically_idempotent :
  forall term theorem,
    Holds term (meet theorem theorem) <-> Holds term theorem.
Proof.
  intros. rewrite meet_is_semantic_conjunction. tauto.
Qed.

Inductive Refines : AdmissionTheorem -> AdmissionTheorem -> Prop :=
| RefinesRefl : forall theorem, Refines theorem theorem
| BottomRefines : forall theorem, Refines Bottom theorem
| ExactRefinesMembership : forall category hash,
    Refines (ExactTerm category hash) (Membership category).

Theorem theorem_refinement_sound :
  forall source target,
    Refines source target -> forall term, Holds term source -> Holds term target.
Proof.
  intros source target refinement.
  induction refinement as
      [theorem
      |theorem
      |category hash
      ];
    intros term Hholds; simpl in *.
  - exact Hholds.
  - contradiction.
  - exact (proj1 Hholds).
Qed.

Record Certificate : Type := {
  certificate_language : LanguageId;
  certificate_theorem : AdmissionTheorem;
  certificate_theorem_id : TheoremId;
  certificate_category : CategoryId;
  certificate_term_hash : TermHash;
  certificate_checker_abi : CheckerAbi;
  certificate_limit_profile : LimitProfile
}.

Definition check_certificate
    (checker_abi : CheckerAbi) (limit_profile : LimitProfile)
    (language : LanguageId) (theorem : AdmissionTheorem)
    (term : Flt) (certificate : Certificate) : bool :=
  Nat.eqb (flt_language term) language &&
  (Nat.eqb (certificate_language certificate) language &&
  (theorem_eqb (certificate_theorem certificate) theorem &&
  (theorem_eqb (certificate_theorem_id certificate) theorem &&
  (Nat.eqb (certificate_category certificate) (flt_category term) &&
  (Nat.eqb (certificate_term_hash certificate) (flt_hash term) &&
  (Nat.eqb (certificate_checker_abi certificate) checker_abi &&
  (Nat.eqb (certificate_limit_profile certificate) limit_profile &&
   theorem_holds term theorem))))))).

Theorem checked_certificate_is_sound :
  forall checker_abi limit_profile language theorem term certificate,
    check_certificate checker_abi limit_profile language theorem term certificate = true ->
    flt_language term = language /\
    certificate_language certificate = language /\
    certificate_theorem certificate = theorem /\
    certificate_theorem_id certificate = theorem /\
    certificate_category certificate = flt_category term /\
    certificate_term_hash certificate = flt_hash term /\
    certificate_checker_abi certificate = checker_abi /\
    certificate_limit_profile certificate = limit_profile /\
    Holds term theorem.
Proof.
  intros checker_abi limit_profile language theorem term certificate H.
  unfold check_certificate in H.
  apply andb_true_iff in H as [Hterm_language H].
  apply andb_true_iff in H as [Hcertificate_language H].
  apply andb_true_iff in H as [Htheorem H].
  apply andb_true_iff in H as [Htheorem_id H].
  apply andb_true_iff in H as [Hcategory H].
  apply andb_true_iff in H as [Hhash Hholds].
  apply andb_true_iff in Hholds as [Hchecker Hholds].
  apply andb_true_iff in Hholds as [Hlimit Hholds].
  repeat split.
  - apply Nat.eqb_eq. exact Hterm_language.
  - apply Nat.eqb_eq. exact Hcertificate_language.
  - apply theorem_eqb_sound. exact Htheorem.
  - apply theorem_eqb_sound. exact Htheorem_id.
  - apply Nat.eqb_eq. exact Hcategory.
  - apply Nat.eqb_eq. exact Hhash.
  - apply Nat.eqb_eq. exact Hchecker.
  - apply Nat.eqb_eq. exact Hlimit.
  - apply theorem_holds_sound. exact Hholds.
Qed.

Definition mint_certificate
    (language : LanguageId) (theorem : AdmissionTheorem) (term : Flt)
    : Certificate :=
  {| certificate_language := language;
     certificate_theorem := theorem;
     certificate_theorem_id := theorem;
     certificate_category := flt_category term;
     certificate_term_hash := flt_hash term;
     certificate_checker_abi := StructuralCheckerAbi;
     certificate_limit_profile := StructuralLimitProfile |}.

Theorem minted_certificate_checks_exactly_the_target_judgment :
  forall language theorem term,
    check_certificate
      StructuralCheckerAbi StructuralLimitProfile language theorem term
      (mint_certificate language theorem term) = true <->
    flt_language term = language /\ Holds term theorem.
Proof.
  intros language theorem term. split.
  - intros H.
    pose proof
      (checked_certificate_is_sound
         StructuralCheckerAbi StructuralLimitProfile
         language theorem term (mint_certificate language theorem term) H)
      as [Hlanguage [_ [_ [_ [_ [_ [_ [_ Hholds]]]]]]]].
    split; assumption.
  - intros [Hlanguage Hholds]. unfold check_certificate, mint_certificate. simpl.
    rewrite Hlanguage, !Nat.eqb_refl.
    rewrite (theorem_eqb_complete theorem theorem eq_refl).
    rewrite (theorem_holds_complete term theorem Hholds).
    reflexivity.
Qed.

Definition CategoryAligned
    (category : CategoryId) (theorem : AdmissionTheorem) : Prop :=
  match theorem with
  | Bottom => True
  | Membership found | ExactTerm found _ => found = category
  end.

Record Channel (language : LanguageId) (space_theorem : AdmissionTheorem) : Type := {
  channel_category : CategoryId;
  channel_theorem : AdmissionTheorem;
  channel_refinement : Refines channel_theorem space_theorem;
  channel_theorem_aligned : CategoryAligned channel_category channel_theorem;
  space_theorem_aligned : CategoryAligned channel_category space_theorem
}.

Arguments channel_category {language space_theorem} _.
Arguments channel_theorem {language space_theorem} _.
Arguments channel_refinement {language space_theorem} _.
Arguments channel_theorem_aligned {language space_theorem} _.
Arguments space_theorem_aligned {language space_theorem} _.

Theorem channel_descriptor_categories_are_aligned :
  forall language space_theorem (channel : Channel language space_theorem),
    CategoryAligned (channel_category channel) (channel_theorem channel) /\
    CategoryAligned (channel_category channel) space_theorem.
Proof.
  intros. split.
  - exact (channel_theorem_aligned channel).
  - exact (space_theorem_aligned channel).
Qed.

Definition channel_accepts
    {language space_theorem} (channel : Channel language space_theorem)
    (term : Flt) (certificate : Certificate) : bool :=
  Nat.eqb (flt_category term) (channel_category channel) &&
  check_certificate
    StructuralCheckerAbi StructuralLimitProfile
    language (channel_theorem channel) term certificate.

Theorem channel_acceptance_is_sound :
  forall language space_theorem
         (channel : Channel language space_theorem) term certificate,
    channel_accepts channel term certificate = true ->
    flt_language term = language /\
    flt_category term = channel_category channel /\
    Holds term (channel_theorem channel) /\
    Holds term space_theorem.
Proof.
  intros language space_theorem channel term certificate H.
  unfold channel_accepts in H.
  apply andb_true_iff in H as [Hcategory Hcertificate].
  apply Nat.eqb_eq in Hcategory.
  pose proof
    (checked_certificate_is_sound
       StructuralCheckerAbi StructuralLimitProfile
       language (channel_theorem channel) term certificate Hcertificate)
    as [Hlanguage [_ [_ [_ [_ [_ [_ [_ Hholds]]]]]]]].
  repeat split; try assumption.
  eapply theorem_refinement_sound.
  - exact (channel_refinement channel).
  - exact Hholds.
Qed.

Record Admitted
    (language : LanguageId) (space_theorem : AdmissionTheorem)
    (channel : Channel language space_theorem) : Type := {
  admitted_term : Flt;
  admitted_certificate : Certificate;
  admitted_check :
    channel_accepts channel admitted_term admitted_certificate = true
}.

Arguments admitted_term {language space_theorem channel} _.
Arguments admitted_certificate {language space_theorem channel} _.
Arguments admitted_check {language space_theorem channel} _.

Definition State
    (language : LanguageId) (space_theorem : AdmissionTheorem)
    (channel : Channel language space_theorem) : Type :=
  list (Admitted language space_theorem channel).

Definition admit
    {language space_theorem} (channel : Channel language space_theorem)
    (term : Flt) (certificate : Certificate)
    : option (Admitted language space_theorem channel).
Proof.
  destruct (channel_accepts channel term certificate) eqn:Haccepts.
  - exact (Some {| admitted_term := term;
                   admitted_certificate := certificate;
                   admitted_check := Haccepts |}).
  - exact None.
Defined.

Definition reclassify
    {language space_theorem} (channel : Channel language space_theorem)
    (term : Flt) : option (Admitted language space_theorem channel) :=
  admit channel term
    (mint_certificate language (channel_theorem channel) term).

Theorem reclassification_checks_the_target_fibre :
  forall language space_theorem
         (channel : Channel language space_theorem) term,
    channel_accepts channel term
      (mint_certificate language (channel_theorem channel) term) = true <->
    flt_language term = language /\
    flt_category term = channel_category channel /\
    Holds term (channel_theorem channel).
Proof.
  intros language space_theorem channel term. split.
  - intros H.
    pose proof
      (channel_acceptance_is_sound
         language space_theorem channel term
         (mint_certificate language (channel_theorem channel) term) H)
      as [Hlanguage [Hcategory [Hchannel _]]].
    repeat split; assumption.
  - intros [Hlanguage [Hcategory Hholds]].
    unfold channel_accepts. apply andb_true_iff. split.
    + apply Nat.eqb_eq. exact Hcategory.
    + apply minted_certificate_checks_exactly_the_target_judgment.
      split; assumption.
Qed.

Theorem checked_reclassification_carries_fresh_channel_evidence :
  forall language space_theorem
         (channel : Channel language space_theorem) term,
    channel_accepts channel term
      (mint_certificate language (channel_theorem channel) term) = true ->
    certificate_theorem
      (mint_certificate language (channel_theorem channel) term) =
        channel_theorem channel /\
    Holds term (channel_theorem channel) /\ Holds term space_theorem.
Proof.
  intros language space_theorem channel term Haccept. split; [reflexivity |].
  pose proof
    (channel_acceptance_is_sound
       language space_theorem channel term
       (mint_certificate language (channel_theorem channel) term) Haccept)
    as [_ [_ [Hchannel Hspace]]].
  split; assumption.
Qed.

Definition run_produce
    {language space_theorem} (channel : Channel language space_theorem)
    (state : State language space_theorem channel)
    (term : Flt) (certificate : Certificate)
    : bool * State language space_theorem channel :=
  match admit channel term certificate with
  | Some admitted => (true, admitted :: state)
  | None => (false, state)
  end.

Theorem rejected_produce_is_atomic :
  forall language space_theorem
         (channel : Channel language space_theorem) state term certificate,
    fst (run_produce channel state term certificate) = false ->
    snd (run_produce channel state term certificate) = state.
Proof.
  intros language space_theorem channel state term certificate H.
  unfold run_produce in *.
  destruct (admit channel term certificate); simpl in *;
    [discriminate | reflexivity].
Qed.

Theorem successful_produce_adds_one_admitted_message :
  forall language space_theorem
         (channel : Channel language space_theorem) state term certificate,
    fst (run_produce channel state term certificate) = true ->
    exists admitted,
      snd (run_produce channel state term certificate) = admitted :: state.
Proof.
  intros language space_theorem channel state term certificate H.
  unfold run_produce in *.
  destruct (admit channel term certificate) as [admitted |] eqn:Hadmit;
    simpl in *; [| discriminate].
  exists admitted. reflexivity.
Qed.

Theorem admitted_message_satisfies_channel_and_space_theorems :
  forall language space_theorem
         (channel : Channel language space_theorem)
         (message : Admitted language space_theorem channel),
    flt_language (admitted_term message) = language /\
    flt_category (admitted_term message) = channel_category channel /\
    Holds (admitted_term message) (channel_theorem channel) /\
    Holds (admitted_term message) space_theorem.
Proof.
  intros. eapply channel_acceptance_is_sound
    with (certificate := admitted_certificate message).
  exact (admitted_check message).
Qed.

Record Pattern : Type := {
  pattern_language : LanguageId;
  pattern_category : CategoryId;
  pattern_compiled_id : nat;
  pattern_exact_hash : option TermHash;
  pattern_capture_categories : list CategoryId;
  pattern_capture_limit : nat;
  pattern_capture_bounded :
    length pattern_capture_categories <= pattern_capture_limit
}.

Definition pattern_matches (pattern : Pattern) (term : Flt) : bool :=
  Nat.eqb (pattern_language pattern) (flt_language term) &&
  (Nat.eqb (pattern_category pattern) (flt_category term) &&
   match pattern_exact_hash pattern with
   | None => true
   | Some hash => Nat.eqb hash (flt_hash term)
   end).

Theorem checked_pattern_match_is_sound :
  forall pattern term,
    pattern_matches pattern term = true ->
    pattern_language pattern = flt_language term /\
    pattern_category pattern = flt_category term /\
    match pattern_exact_hash pattern with
    | None => True
    | Some hash => hash = flt_hash term
    end.
Proof.
  intros pattern term H. unfold pattern_matches in H.
  apply andb_true_iff in H as [Hlanguage H].
  apply andb_true_iff in H as [Hcategory Hhash].
  split; [apply Nat.eqb_eq; exact Hlanguage |]. split.
  - apply Nat.eqb_eq. exact Hcategory.
  - destruct (pattern_exact_hash pattern) as [hash |]; simpl in *.
    + apply Nat.eqb_eq. exact Hhash.
    + exact I.
Qed.

Definition CaptureEnvironment := list (nat * TermHash).

Definition capture_environment
    (hash : TermHash) (categories : list CategoryId) : CaptureEnvironment :=
  map (fun category => (category, hash)) categories.

Lemma capture_environment_has_telescope :
  forall hash categories,
    map fst (capture_environment hash categories) = categories.
Proof.
  intros hash categories. induction categories as [| category rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Record MatchWitness
    {language space_theorem}
    (channel : Channel language space_theorem) (pattern : Pattern) : Type := {
  witness_message : Admitted language space_theorem channel;
  witness_captures : CaptureEnvironment;
  witness_pattern_id : nat;
  witness_check : pattern_matches pattern (admitted_term witness_message) = true;
  witness_pattern_identity : witness_pattern_id = pattern_compiled_id pattern;
  witness_capture_telescope :
    map fst witness_captures = pattern_capture_categories pattern
}.

Arguments witness_message {language space_theorem channel pattern} _.
Arguments witness_captures {language space_theorem channel pattern} _.
Arguments witness_pattern_id {language space_theorem channel pattern} _.
Arguments witness_check {language space_theorem channel pattern} _.
Arguments witness_pattern_identity {language space_theorem channel pattern} _.
Arguments witness_capture_telescope {language space_theorem channel pattern} _.

Definition prepare_match
    {language space_theorem}
    (channel : Channel language space_theorem) (pattern : Pattern)
    (message : Admitted language space_theorem channel)
    : option (MatchWitness channel pattern).
Proof.
  destruct (pattern_matches pattern (admitted_term message)) eqn:Hmatch.
  - exact (Some {| witness_message := message;
                   witness_captures :=
                     capture_environment
                       (flt_hash (admitted_term message))
                       (pattern_capture_categories pattern);
                   witness_pattern_id := pattern_compiled_id pattern;
                   witness_check := Hmatch;
                   witness_pattern_identity := eq_refl;
                   witness_capture_telescope :=
                     capture_environment_has_telescope
                       (flt_hash (admitted_term message))
                       (pattern_capture_categories pattern) |}).
  - exact None.
Defined.

Inductive ConsumeResult
    {language space_theorem}
    (channel : Channel language space_theorem) (pattern : Pattern) : Type :=
| ConsumeMiss : ConsumeResult channel pattern
| ConsumeHit :
    State language space_theorem channel ->
    MatchWitness channel pattern ->
    ConsumeResult channel pattern.

Fixpoint run_consume
    {language space_theorem}
    (channel : Channel language space_theorem) (pattern : Pattern)
    (state : State language space_theorem channel)
    : ConsumeResult channel pattern :=
  match state with
  | [] => ConsumeMiss channel pattern
  | message :: rest =>
      match prepare_match channel pattern message with
      | Some witness => ConsumeHit channel pattern rest witness
      | None =>
          match run_consume channel pattern rest with
          | ConsumeMiss _ _ => ConsumeMiss channel pattern
          | ConsumeHit _ _ remaining witness =>
              ConsumeHit channel pattern (message :: remaining) witness
          end
      end
  end.

Theorem consume_miss_means_no_message_has_a_match_witness :
  forall language space_theorem
         (channel : Channel language space_theorem) pattern state,
    run_consume channel pattern state = ConsumeMiss channel pattern ->
    Forall
      (fun message => prepare_match channel pattern message = None)
      state.
Proof.
  intros language space_theorem channel pattern state.
  induction state as [| message rest IH]; intros Hresult.
  - constructor.
  - simpl in Hresult.
    destruct (prepare_match channel pattern message) as [witness |] eqn:Hprepare.
    + discriminate.
    + constructor.
      * exact Hprepare.
      * destruct (run_consume channel pattern rest) eqn:Hrest;
          [apply IH; reflexivity | discriminate].
Qed.

Theorem consume_hit_carries_checked_match_and_admission_evidence :
  forall language space_theorem
         (channel : Channel language space_theorem) pattern state remaining witness,
    run_consume channel pattern state =
      ConsumeHit channel pattern remaining witness ->
    pattern_matches pattern
      (admitted_term (witness_message witness)) = true /\
    witness_pattern_id witness = pattern_compiled_id pattern /\
    map fst (witness_captures witness) = pattern_capture_categories pattern /\
    Holds (admitted_term (witness_message witness))
      (channel_theorem channel) /\
    Holds (admitted_term (witness_message witness)) space_theorem.
Proof.
  intros. repeat split.
  - exact (witness_check witness).
  - exact (witness_pattern_identity witness).
  - exact (witness_capture_telescope witness).
  - pose proof
      (admitted_message_satisfies_channel_and_space_theorems
         language space_theorem channel (witness_message witness))
      as [_ [_ [Hchannel Hspace]]].
    exact Hchannel.
  - pose proof
      (admitted_message_satisfies_channel_and_space_theorems
         language space_theorem channel (witness_message witness))
      as [_ [_ [Hchannel Hspace]]].
    exact Hspace.
Qed.

Theorem match_witness_respects_the_host_capture_limit :
  forall language space_theorem
         (channel : Channel language space_theorem) pattern
         (witness : MatchWitness channel pattern),
    length (witness_captures witness) <= pattern_capture_limit pattern.
Proof.
  intros.
  pose proof (pattern_capture_bounded pattern) as Hbounded.
  rewrite <- (witness_capture_telescope witness) in Hbounded.
  rewrite length_map in Hbounded. exact Hbounded.
Qed.

Record ConsumeTransaction
    {language space_theorem}
    (channel : Channel language space_theorem) : Type := {
  consume_committed : bool;
  consume_state : State language space_theorem channel;
  consume_captures : option CaptureEnvironment
}.

Arguments consume_committed {language space_theorem channel} _.
Arguments consume_state {language space_theorem channel} _.
Arguments consume_captures {language space_theorem channel} _.

Definition transact_consume
    {language space_theorem}
    (channel : Channel language space_theorem) (pattern : Pattern)
    (state : State language space_theorem channel)
    : ConsumeTransaction channel :=
  match run_consume channel pattern state with
  | ConsumeMiss _ _ =>
      {| consume_committed := false;
         consume_state := state;
         consume_captures := None |}
  | ConsumeHit _ _ remaining witness =>
      {| consume_committed := true;
         consume_state := remaining;
         consume_captures := Some (witness_captures witness) |}
  end.

Theorem nonfiring_consume_has_no_partial_state_or_capture :
  forall language space_theorem
         (channel : Channel language space_theorem) pattern state,
    consume_committed (transact_consume channel pattern state) = false ->
    consume_state (transact_consume channel pattern state) = state /\
    consume_captures (transact_consume channel pattern state) = None.
Proof.
  intros language space_theorem channel pattern state H.
  unfold transact_consume in *.
  destruct (run_consume channel pattern state); simpl in *.
  - split; reflexivity.
  - discriminate.
Qed.

Record ProofCacheKey : Type := {
  cache_language : LanguageId;
  cache_theorem : TheoremId;
  cache_term_hash : TermHash;
  cache_checker_abi : CheckerAbi;
  cache_limit_profile : LimitProfile
}.

Definition authorized_produce
    {language space_theorem}
    (prepared_epoch : nat) (live : LiveAuthority) (_cache_hit : bool)
    (channel : Channel language space_theorem)
    (state : State language space_theorem channel)
    (term : Flt) (certificate : Certificate)
    : bool * State language space_theorem channel :=
  if space_commit_allowed prepared_epoch Produce live
  then run_produce channel state term certificate
  else (false, state).

Theorem stale_epoch_cannot_commit_even_with_proof_cache_hit :
  forall language space_theorem prepared_epoch live
         (channel : Channel language space_theorem) state term certificate,
    prepared_epoch <> authority_epoch live ->
    authorized_produce prepared_epoch live true channel state term certificate =
      (false, state).
Proof.
  intros language space_theorem prepared_epoch live channel state term certificate Hstale.
  unfold authorized_produce.
  rewrite changed_epoch_rejects_space_commit by exact Hstale.
  reflexivity.
Qed.

Theorem absent_produce_right_cannot_commit_even_with_proof_cache_hit :
  forall language space_theorem prepared_epoch live
         (channel : Channel language space_theorem) state term certificate,
    has_space_right Produce (space_rights (live_authority live)) = false ->
    authorized_produce prepared_epoch live true channel state term certificate =
      (false, state).
Proof.
  intros language space_theorem prepared_epoch live channel state term certificate Hright.
  unfold authorized_produce, space_commit_allowed. rewrite Hright.
  destruct (Nat.eqb prepared_epoch (authority_epoch live)); reflexivity.
Qed.

(** Language authority is indexed as strictly as theorem evidence.  A handle
    with the right operation bit for another installed language cannot prepare
    a transaction for this channel. *)
Record LanguageHandleRef : Type := {
  handle_language : LanguageId;
  handle_operation_authorized : bool
}.

Definition handle_prepares_channel
    (channel_language : LanguageId) (handle : LanguageHandleRef) : bool :=
  handle_operation_authorized handle &&
  Nat.eqb (handle_language handle) channel_language.

Theorem prepared_channel_handle_has_exact_language_identity :
  forall channel_language handle,
    handle_prepares_channel channel_language handle = true ->
    handle_operation_authorized handle = true /\
    handle_language handle = channel_language.
Proof.
  intros channel_language handle Hprepared.
  unfold handle_prepares_channel in Hprepared.
  apply andb_true_iff in Hprepared as [Hright Hlanguage].
  split; [exact Hright |].
  apply Nat.eqb_eq. exact Hlanguage.
Qed.

Theorem foreign_language_handle_cannot_prepare_channel :
  forall channel_language handle,
    handle_language handle <> channel_language ->
    handle_prepares_channel channel_language handle = false.
Proof.
  intros channel_language handle Hforeign.
  unfold handle_prepares_channel.
  apply andb_false_iff. right.
  apply Nat.eqb_neq. exact Hforeign.
Qed.

Print Assumptions theorem_refinement_sound.
Print Assumptions meet_is_semantic_conjunction.
Print Assumptions meet_semantically_commutative.
Print Assumptions meet_semantically_associative.
Print Assumptions meet_semantically_idempotent.
Print Assumptions checked_certificate_is_sound.
Print Assumptions minted_certificate_checks_exactly_the_target_judgment.
Print Assumptions channel_descriptor_categories_are_aligned.
Print Assumptions channel_acceptance_is_sound.
Print Assumptions reclassification_checks_the_target_fibre.
Print Assumptions checked_reclassification_carries_fresh_channel_evidence.
Print Assumptions rejected_produce_is_atomic.
Print Assumptions consume_miss_means_no_message_has_a_match_witness.
Print Assumptions consume_hit_carries_checked_match_and_admission_evidence.
Print Assumptions match_witness_respects_the_host_capture_limit.
Print Assumptions nonfiring_consume_has_no_partial_state_or_capture.
Print Assumptions stale_epoch_cannot_commit_even_with_proof_cache_hit.
Print Assumptions absent_produce_right_cannot_commit_even_with_proof_cache_hit.
Print Assumptions prepared_channel_handle_has_exact_language_identity.
Print Assumptions foreign_language_handle_cannot_prepare_channel.
