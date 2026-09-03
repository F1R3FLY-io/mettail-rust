From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import TheoremChannel.
Import ListNotations.

(** A runtime theorem checker is a reject-safe, three-valued decision procedure.
    [Undetermined] is observably different from a semantic refutation: it says
    that the configured work or evidence bound did not justify either Boolean
    conclusion.  Only [Proven] carries a certificate to the transaction phase. *)
Inductive AdmissionDecision : Type :=
| Proven : Certificate -> AdmissionDecision
| Refuted : AdmissionDecision
| Undetermined : AdmissionDecision.

Record AdmissionBudget : Type := {
  budget_work_units : nat;
  budget_evidence_bytes : nat
}.

(** An optional externally supplied certificate carries opaque evidence bytes.
    The structural compatibility checker does not interpret those bytes, but it
    still bounds them before touching the certificate.  A later OSLF checker may
    validate their contents behind the same interface. *)
Record PresentedCertificate : Type := {
  presented_certificate : Certificate;
  presented_evidence : list nat
}.

Definition structural_required_work : nat := 1.

Definition presented_evidence_size
    (supplied : option PresentedCertificate) : nat :=
  match supplied with
  | Some presented => length (presented_evidence presented)
  | None => 0
  end.

Definition budget_allows
    (budget : AdmissionBudget) (supplied : option PresentedCertificate) : bool :=
  (structural_required_work <=? budget_work_units budget) &&
  (presented_evidence_size supplied <=? budget_evidence_bytes budget).

(** The executable structural checker.  Without a supplied certificate it
    decides the finite structural theorem and mints canonical evidence.  With a
    supplied certificate it verifies the complete certificate commitment. *)
Definition bounded_structural_check
    (language : LanguageId) (theorem : AdmissionTheorem) (term : Flt)
    (supplied : option PresentedCertificate) (budget : AdmissionBudget)
    : AdmissionDecision :=
  if budget_allows budget supplied then
    match supplied with
    | Some presented =>
        if check_certificate
             StructuralCheckerAbi StructuralLimitProfile language theorem term
             (presented_certificate presented)
        then Proven (presented_certificate presented)
        else Refuted
    | None =>
        if Nat.eqb (flt_language term) language && theorem_holds term theorem
        then Proven (mint_certificate language theorem term)
        else Refuted
    end
  else Undetermined.

Theorem bounded_structural_proof_is_sound :
  forall language theorem term supplied budget certificate,
    bounded_structural_check language theorem term supplied budget =
      Proven certificate ->
    flt_language term = language /\ Holds term theorem.
Proof.
  intros language theorem term supplied budget certificate Hdecision.
  unfold bounded_structural_check in Hdecision.
  destruct (budget_allows budget supplied) eqn:Hbudget; [| discriminate].
  destruct supplied as [presented |].
  - destruct
      (check_certificate
         StructuralCheckerAbi StructuralLimitProfile language theorem term
         (presented_certificate presented)) eqn:Hcheck; [| discriminate].
    inversion Hdecision; subst.
    pose proof
      (checked_certificate_is_sound
         StructuralCheckerAbi StructuralLimitProfile language theorem term
         (presented_certificate presented) Hcheck)
      as [Hlanguage [_ [_ [_ [_ [_ [_ [_ Hholds]]]]]]]].
    split; assumption.
  - destruct
      (Nat.eqb (flt_language term) language && theorem_holds term theorem)
      eqn:Hcheck; [| discriminate].
    inversion Hdecision; subst.
    apply andb_true_iff in Hcheck as [Hlanguage Hholds].
    split.
    + apply Nat.eqb_eq. exact Hlanguage.
    + apply theorem_holds_sound. exact Hholds.
Qed.

Theorem exhausted_checker_is_undetermined :
  forall language theorem term supplied budget,
    budget_allows budget supplied = false ->
    bounded_structural_check language theorem term supplied budget =
      Undetermined.
Proof.
  intros. unfold bounded_structural_check. rewrite H. reflexivity.
Qed.

Theorem invalid_presented_certificate_is_refuted :
  forall language theorem term presented budget,
    budget_allows budget (Some presented) = true ->
    check_certificate
      StructuralCheckerAbi StructuralLimitProfile language theorem term
      (presented_certificate presented) = false ->
    bounded_structural_check language theorem term (Some presented) budget =
      Refuted.
Proof.
  intros. unfold bounded_structural_check. rewrite H, H0. reflexivity.
Qed.

Definition budget_dominates
    (smaller larger : AdmissionBudget) : Prop :=
  budget_work_units smaller <= budget_work_units larger /\
  budget_evidence_bytes smaller <= budget_evidence_bytes larger.

Lemma allowed_budget_is_monotone :
  forall smaller larger supplied,
    budget_dominates smaller larger ->
    budget_allows smaller supplied = true ->
    budget_allows larger supplied = true.
Proof.
  intros smaller larger supplied [Hwork Hevidence] Hsmall.
  unfold budget_allows in *.
  apply andb_true_iff in Hsmall as [Hsmall_work Hsmall_evidence].
  apply andb_true_iff. split; apply Nat.leb_le.
  - apply Nat.leb_le in Hsmall_work. lia.
  - apply Nat.leb_le in Hsmall_evidence. lia.
Qed.

Theorem proven_decision_is_monotone_in_budget :
  forall language theorem term supplied smaller larger certificate,
    budget_dominates smaller larger ->
    bounded_structural_check language theorem term supplied smaller =
      Proven certificate ->
    bounded_structural_check language theorem term supplied larger =
      Proven certificate.
Proof.
  intros language theorem term supplied smaller larger certificate
    Hdominates Hsmall.
  unfold bounded_structural_check in *.
  destruct (budget_allows smaller supplied) eqn:Hsmall_budget;
    [| discriminate].
  assert (Hlarge_budget : budget_allows larger supplied = true).
  { apply (allowed_budget_is_monotone smaller larger supplied Hdominates).
    exact Hsmall_budget. }
  rewrite Hlarge_budget.
  destruct supplied as [presented |]; exact Hsmall.
Qed.

(** Cache lookup is deliberately absent from the semantic decision.  It may
    select an already verified implementation path, but cannot change the
    decision or its protocol-defined logical charge. *)
Definition check_with_cache
    (_cache_hit : bool)
    (language : LanguageId) (theorem : AdmissionTheorem) (term : Flt)
    (supplied : option PresentedCertificate) (budget : AdmissionBudget)
    : nat * AdmissionDecision :=
  (structural_required_work,
   bounded_structural_check language theorem term supplied budget).

Theorem proof_cache_is_semantics_and_charge_transparent :
  forall language theorem term supplied budget left_hit right_hit,
    check_with_cache left_hit language theorem term supplied budget =
    check_with_cache right_hit language theorem term supplied budget.
Proof. reflexivity. Qed.

Definition decision_admits (decision : AdmissionDecision) : bool :=
  match decision with
  | Proven _ => true
  | Refuted | Undetermined => false
  end.

Theorem undetermined_never_admits :
  decision_admits Undetermined = false.
Proof. reflexivity. Qed.

Theorem refuted_never_admits :
  decision_admits Refuted = false.
Proof. reflexivity. Qed.

(** The callback boundary is represented as a single state transition.  The
    checker has no access to [state]; rejected and exhausted decisions therefore
    cannot partially publish a message. *)
Definition commit_checked_produce
    (decision : AdmissionDecision) (term : Flt) (state : list Flt)
    : bool * list Flt :=
  match decision with
  | Proven _ => (true, term :: state)
  | Refuted | Undetermined => (false, state)
  end.

Theorem refuted_produce_changes_nothing :
  forall term state,
    commit_checked_produce Refuted term state = (false, state).
Proof. reflexivity. Qed.

Theorem undetermined_produce_changes_nothing :
  forall term state,
    commit_checked_produce Undetermined term state = (false, state).
Proof. reflexivity. Qed.

Definition CaptureEnvironment := list (CategoryId * TermHash).

Record ConsumeCommit : Type := {
  consume_did_commit : bool;
  consume_messages_after : list Flt;
  consume_captures_after : option CaptureEnvironment
}.

Definition commit_checked_consume
    (decision : AdmissionDecision)
    (messages remaining : list Flt) (captures : CaptureEnvironment)
    : ConsumeCommit :=
  match decision with
  | Proven _ =>
      {| consume_did_commit := true;
         consume_messages_after := remaining;
         consume_captures_after := Some captures |}
  | Refuted | Undetermined =>
      {| consume_did_commit := false;
         consume_messages_after := messages;
         consume_captures_after := None |}
  end.

Theorem nonproven_consume_has_no_partial_state_or_capture :
  forall decision messages remaining captures,
    decision_admits decision = false ->
    consume_did_commit
      (commit_checked_consume decision messages remaining captures) = false /\
    consume_messages_after
      (commit_checked_consume decision messages remaining captures) = messages /\
    consume_captures_after
      (commit_checked_consume decision messages remaining captures) = None.
Proof.
  destruct decision; simpl; intros; [discriminate | repeat split | repeat split].
Qed.

(** Language [Check] authority is independent of Publish/Match authority.  The
    epoch and both rights are re-read at commit; neither a prepared certificate
    nor a cache hit can replace them. *)
Definition commit_authorized
    (prepared_epoch live_epoch : nat)
    (operation_right check_right : bool) : bool :=
  Nat.eqb prepared_epoch live_epoch && operation_right && check_right.

Definition authorized_checked_produce
    (prepared_epoch live_epoch : nat)
    (publish_right check_right cache_hit : bool)
    (decision : AdmissionDecision) (term : Flt) (state : list Flt)
    : bool * list Flt :=
  if commit_authorized
       prepared_epoch live_epoch publish_right check_right
  then commit_checked_produce decision term state
  else (false, state).

Theorem missing_check_right_cannot_commit_even_with_cached_proof :
  forall prepared_epoch live_epoch publish_right decision term state,
    authorized_checked_produce
      prepared_epoch live_epoch publish_right false true decision term state =
      (false, state).
Proof.
  intros. unfold authorized_checked_produce, commit_authorized.
  destruct (Nat.eqb prepared_epoch live_epoch); destruct publish_right;
    reflexivity.
Qed.

Theorem stale_epoch_cannot_commit_any_checker_decision :
  forall prepared_epoch live_epoch publish_right check_right cache_hit
         decision term state,
    prepared_epoch <> live_epoch ->
    authorized_checked_produce
      prepared_epoch live_epoch publish_right check_right cache_hit
      decision term state = (false, state).
Proof.
  intros. unfold authorized_checked_produce, commit_authorized.
  apply Nat.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Print Assumptions bounded_structural_proof_is_sound.
Print Assumptions exhausted_checker_is_undetermined.
Print Assumptions invalid_presented_certificate_is_refuted.
Print Assumptions proven_decision_is_monotone_in_budget.
Print Assumptions proof_cache_is_semantics_and_charge_transparent.
Print Assumptions undetermined_never_admits.
Print Assumptions refuted_never_admits.
Print Assumptions refuted_produce_changes_nothing.
Print Assumptions undetermined_produce_changes_nothing.
Print Assumptions nonproven_consume_has_no_partial_state_or_capture.
Print Assumptions missing_check_right_cannot_commit_even_with_cached_proof.
Print Assumptions stale_epoch_cannot_commit_any_checker_decision.
