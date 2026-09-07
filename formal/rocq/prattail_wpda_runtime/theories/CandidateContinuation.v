(*
 * CandidateContinuation specifies the evidence boundary after a packed-forest
 * enumerator presents candidate occurrences.  Its budget counts transitions,
 * not admissible results.  An undecided occurrence stays in the pending queue;
 * a checked positive or negative judgment moves it to the corresponding ledger.
 * Stopping and resuming never discards the queue or either ledger.
 *
 * This is a consumer protocol, not a replacement ranking algorithm.  Refining
 * a lazy heap/product enumerator to the supplied candidate stream is a separate
 * obligation.  Completeness also requires complete recognition: draining the
 * represented stream cannot repair a forest that was itself truncated.
 *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Section EvidenceContinuation.
  Context {Candidate : Type}.
  Variable admissible : Candidate -> Prop.

  Inductive Verdict (candidate : Candidate) : Type :=
  | Supported : admissible candidate -> Verdict candidate
  | Excluded : (~ admissible candidate) -> Verdict candidate
  | Unresolved : Verdict candidate.

  Variable judge : forall candidate, Verdict candidate.

  Record Continuation : Type := {
    supported_rev : list Candidate;
    excluded_rev : list Candidate;
    pending : list Candidate
  }.

  Definition initial (candidates : list Candidate) : Continuation :=
    {| supported_rev := []; excluded_rev := []; pending := candidates |}.

  Definition advance (state : Continuation) : Continuation :=
    match pending state with
    | [] => state
    | candidate :: rest =>
        match judge candidate with
        | Supported _ =>
            {| supported_rev := candidate :: supported_rev state;
               excluded_rev := excluded_rev state; pending := rest |}
        | Excluded _ =>
            {| supported_rev := supported_rev state;
               excluded_rev := candidate :: excluded_rev state; pending := rest |}
        | Unresolved _ =>
            {| supported_rev := supported_rev state;
               excluded_rev := excluded_rev state; pending := rest ++ [candidate] |}
        end
    end.

  Fixpoint resume (work_budget : nat) (state : Continuation) : Continuation :=
    match work_budget with
    | 0 => state
    | S rest => resume rest (advance state)
    end.

  Theorem resume_is_uninterrupted_execution : forall first second state,
    resume second (resume first state) = resume (first + second) state.
  Proof.
    induction first as [|first IH]; intros second state; cbn.
    - reflexivity.
    - apply IH.
  Qed.

  Definition accounted (candidate : Candidate) (state : Continuation) : Prop :=
    In candidate (supported_rev state) \/
    In candidate (excluded_rev state) \/ In candidate (pending state).

  Definition checked_ledgers (state : Continuation) : Prop :=
    Forall admissible (supported_rev state) /\
    Forall (fun candidate => ~ admissible candidate) (excluded_rev state).

  Theorem advance_preserves_every_candidate : forall state candidate,
    accounted candidate (advance state) <-> accounted candidate state.
  Proof.
    intros [supported excluded [|head rest]] candidate;
      unfold advance, accounted; cbn.
    - tauto.
    - destruct (judge head); cbn.
      + tauto.
      + tauto.
      + rewrite in_app_iff. cbn. tauto.
  Qed.

  Theorem advance_preserves_checked_ledgers : forall state,
    checked_ledgers state -> checked_ledgers (advance state).
  Proof.
    intros [supported excluded [|head rest]] [Hsupported Hexcluded];
      unfold advance, checked_ledgers; cbn in *.
    - now split.
    - destruct (judge head) as [Hyes|Hno|]; cbn; split; auto.
  Qed.

  Theorem resume_preserves_every_candidate : forall budget state candidate,
    accounted candidate (resume budget state) <-> accounted candidate state.
  Proof.
    induction budget as [|budget IH]; intros state candidate; cbn.
    - tauto.
    - rewrite IH. apply advance_preserves_every_candidate.
  Qed.

  Theorem resume_preserves_checked_ledgers : forall budget state,
    checked_ledgers state -> checked_ledgers (resume budget state).
  Proof.
    induction budget as [|budget IH]; intros state Hchecked; cbn.
    - exact Hchecked.
    - apply IH. now apply advance_preserves_checked_ledgers.
  Qed.

  (* Counting occurrences strengthens membership preservation: repeated shared
     candidates cannot be collapsed merely because their identities coincide. *)
  Variable same_candidate : forall left right : Candidate, {left = right} + {left <> right}.

  Definition occurrence_count (candidate : Candidate) (state : Continuation) : nat :=
    count_occ same_candidate (supported_rev state) candidate +
    count_occ same_candidate (excluded_rev state) candidate +
    count_occ same_candidate (pending state) candidate.

  Theorem advance_preserves_occurrence_count : forall state candidate,
    occurrence_count candidate (advance state) = occurrence_count candidate state.
  Proof.
    intros [supported excluded [|head rest]] candidate;
      unfold advance, occurrence_count; cbn.
    - reflexivity.
    - destruct (judge head); cbn.
      + destruct (same_candidate head candidate); lia.
      + destruct (same_candidate head candidate); lia.
      + rewrite count_occ_app. cbn.
        destruct (same_candidate head candidate); lia.
  Qed.

  Theorem resume_preserves_occurrence_count : forall budget state candidate,
    occurrence_count candidate (resume budget state) = occurrence_count candidate state.
  Proof.
    induction budget as [|budget IH]; intros state candidate; cbn.
    - reflexivity.
    - rewrite IH. apply advance_preserves_occurrence_count.
  Qed.

  Inductive Completion : Type :=
  | RecognitionIncomplete
  | CandidatesPending
  | Complete.

  Definition completion (recognition_complete : bool) (state : Continuation) : Completion :=
    if recognition_complete then
      match pending state with [] => Complete | _ => CandidatesPending end
    else RecognitionIncomplete.

  Theorem complete_requires_recognition_and_exhaustion : forall recognized state,
    completion recognized state = Complete <-> recognized = true /\ pending state = [].
  Proof.
    intros [|] [supported excluded [|head rest]];
      unfold completion; cbn; split; intros H; try discriminate; intuition discriminate.
  Qed.

  Theorem admissible_candidate_cannot_disappear : forall candidates budget candidate,
    In candidate candidates -> admissible candidate ->
    In candidate (supported_rev (resume budget (initial candidates))) \/
    In candidate (pending (resume budget (initial candidates))).
  Proof.
    intros candidates budget candidate Hin Hvalid.
    assert (Hchecked : checked_ledgers (resume budget (initial candidates))).
    { apply resume_preserves_checked_ledgers. split; constructor. }
    assert (Haccounted : accounted candidate (resume budget (initial candidates))).
    { apply resume_preserves_every_candidate.
      unfold accounted, initial; cbn. tauto. }
    destruct Haccounted as [Hyes|[Hno|Hpending]]; auto.
    destruct Hchecked as [_ Hexcluded].
    apply Forall_forall with (x := candidate) in Hexcluded; [contradiction | exact Hno].
  Qed.

  Theorem complete_result_contains_every_admissible_candidate :
    forall candidates budget candidate,
      completion true (resume budget (initial candidates)) = Complete ->
      In candidate candidates -> admissible candidate ->
      In candidate (supported_rev (resume budget (initial candidates))).
  Proof.
    intros candidates budget candidate Hcomplete Hin Hvalid.
    apply complete_requires_recognition_and_exhaustion in Hcomplete.
    destruct Hcomplete as [_ Hempty].
    destruct (@admissible_candidate_cannot_disappear candidates budget candidate Hin Hvalid)
      as [Hyes|Hpending]; [exact Hyes | now rewrite Hempty in Hpending].
  Qed.

  Corollary complete_empty_result_proves_absence : forall candidates budget,
    completion true (resume budget (initial candidates)) = Complete ->
    supported_rev (resume budget (initial candidates)) = [] ->
    forall candidate, In candidate candidates -> ~ admissible candidate.
  Proof.
    intros candidates budget Hcomplete Hempty candidate Hin Hvalid.
    pose proof (@complete_result_contains_every_admissible_candidate
      candidates budget candidate Hcomplete Hin Hvalid) as Hfound.
    now rewrite Hempty in Hfound.
  Qed.

  Corollary complete_singleton_proves_uniqueness : forall candidates budget only,
    completion true (resume budget (initial candidates)) = Complete ->
    supported_rev (resume budget (initial candidates)) = [only] ->
    forall candidate, In candidate candidates -> admissible candidate -> candidate = only.
  Proof.
    intros candidates budget only Hcomplete Hsingle candidate Hin Hvalid.
    pose proof (@complete_result_contains_every_admissible_candidate
      candidates budget candidate Hcomplete Hin Hvalid) as Hfound.
    rewrite Hsingle in Hfound. cbn in Hfound. intuition congruence.
  Qed.
End EvidenceContinuation.

Definition positive_is_admissible (candidate : nat) : Prop := candidate <> 0.

Definition positive_judgment (candidate : nat) : Verdict positive_is_admissible candidate.
Proof.
  destruct candidate as [|candidate].
  - apply Excluded. unfold positive_is_admissible. tauto.
  - apply Supported. unfold positive_is_admissible. discriminate.
Defined.

Example nonempty_prefix_is_not_unique :
  supported_rev (resume positive_judgment 1 (initial [1; 2])) = [1] /\
  pending (resume positive_judgment 1 (initial [1; 2])) = [2] /\
  completion true (resume positive_judgment 1 (initial [1; 2])) = CandidatesPending.
Proof. repeat split; reflexivity. Qed.

Example rejected_prefix_does_not_mean_no_parse :
  supported_rev (resume positive_judgment 1 (initial [0; 1])) = [] /\
  pending (resume positive_judgment 1 (initial [0; 1])) = [1] /\
  supported_rev (resume positive_judgment 2 (initial [0; 1])) = [1].
Proof. repeat split; reflexivity. Qed.

Example exhausted_enumeration_cannot_complete_truncated_recognition :
  completion false (resume positive_judgment 2 (initial [0; 1])) = RecognitionIncomplete.
Proof. reflexivity. Qed.

Print Assumptions resume_is_uninterrupted_execution.
Print Assumptions advance_preserves_every_candidate.
Print Assumptions advance_preserves_checked_ledgers.
Print Assumptions resume_preserves_every_candidate.
Print Assumptions resume_preserves_occurrence_count.
Print Assumptions complete_requires_recognition_and_exhaustion.
Print Assumptions admissible_candidate_cannot_disappear.
Print Assumptions complete_result_contains_every_admissible_candidate.
Print Assumptions complete_empty_result_proves_absence.
Print Assumptions complete_singleton_proves_uniqueness.
