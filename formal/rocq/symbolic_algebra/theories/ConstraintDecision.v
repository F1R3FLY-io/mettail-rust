(*
 * ConstraintDecision: reject-safe bounded search and the exact-decision gate.
 *
 * A finite prefix of a fair search is evidence for satisfiability when it
 * contains a checked witness.  Absence from that prefix is not evidence for
 * unsatisfiability.  Even exhausting an implementation stream is insufficient
 * unless the constraint theory supplies a completeness proof connecting that
 * stream to its semantic domain.  This is the proof contract implemented by
 * `ConstraintTheory`, `DecidableConstraintTheory`, `BoundedCollection`, and
 * `TheoryAlgebra` in `prattail/src/logict.rs`.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Section RejectSafeSearch.
  Context {Witness : Type}.
  Variable valid : Witness -> bool.

  Fixpoint find_valid (observed : list Witness) : option Witness :=
    match observed with
    | [] => None
    | witness :: rest =>
        if valid witness then Some witness else find_valid rest
    end.

  Lemma find_valid_sound :
    forall observed witness,
      find_valid observed = Some witness ->
      In witness observed /\ valid witness = true.
  Proof.
    induction observed as [| candidate rest IH]; intros witness Hfound.
    - discriminate.
    - simpl in Hfound. destruct (valid candidate) eqn:Hcandidate.
      + inversion Hfound; subst. split; [left; reflexivity | exact Hcandidate].
      + apply IH in Hfound as [Hin Hvalid].
        split; [right; exact Hin | exact Hvalid].
  Qed.

  Lemma find_valid_none :
    forall observed,
      find_valid observed = None ->
      forall witness, In witness observed -> valid witness = false.
  Proof.
    induction observed as [| candidate rest IH]; intros Hnone witness Hin.
    - contradiction.
    - simpl in Hnone. destruct (valid candidate) eqn:Hcandidate.
      + discriminate.
      + destruct Hin as [Hequal | Hin].
        * subst. exact Hcandidate.
        * apply (IH Hnone witness Hin).
  Qed.

  Inductive SearchFrontier : Type :=
  | Exhausted
  | Truncated.

  Record SearchReport : Type := {
    report_observed : list Witness;
    report_frontier : SearchFrontier
  }.

  Inductive Decision : Type :=
  | Proven (witness : Witness)
  | Refuted
  | Undetermined.

  (** The general adapter may trust a positive checked witness, but no negative
      conclusion.  [Exhausted] describes only the implementation stream; it is
      not a semantic completeness certificate. *)
  Definition decide_general (report : SearchReport) : Decision :=
    match find_valid (report_observed report) with
    | Some witness => Proven witness
    | None => Undetermined
    end.

  Theorem general_proven_is_sound :
    forall report witness,
      decide_general report = Proven witness ->
      In witness (report_observed report) /\ valid witness = true.
  Proof.
    intros report witness Hdecision.
    unfold decide_general in Hdecision.
    destruct (find_valid (report_observed report)) as [found |] eqn:Hfound.
    - inversion Hdecision; subst. apply find_valid_sound. exact Hfound.
    - discriminate.
  Qed.

  Theorem general_no_witness_is_undetermined :
    forall report,
      find_valid (report_observed report) = None ->
      decide_general report = Undetermined.
  Proof. intros report Hnone. unfold decide_general. rewrite Hnone. reflexivity. Qed.

  Corollary truncated_no_witness_is_undetermined :
    forall observed,
      find_valid observed = None ->
      decide_general
        {| report_observed := observed; report_frontier := Truncated |} =
        Undetermined.
  Proof. intros observed Hnone. apply general_no_witness_is_undetermined. exact Hnone. Qed.

  Corollary implementation_exhaustion_alone_is_undetermined :
    forall observed,
      find_valid observed = None ->
      decide_general
        {| report_observed := observed; report_frontier := Exhausted |} =
        Undetermined.
  Proof. intros observed Hnone. apply general_no_witness_is_undetermined. exact Hnone. Qed.

  Definition Complete (report : SearchReport) : Prop :=
    forall witness, valid witness = true -> In witness (report_observed report).

  (** Only a caller carrying [Complete] may construct the classical negative
      branch.  In Rust this proof obligation is represented by the sealed
      `DecidableConstraintTheory` contract and its exact decision procedure. *)
  Definition decide_complete
      (report : SearchReport) (_ : Complete report) : Decision :=
    match find_valid (report_observed report) with
    | Some witness => Proven witness
    | None => Refuted
    end.

  Theorem complete_proven_is_sound :
    forall report (complete : Complete report) witness,
      decide_complete report complete = Proven witness ->
      valid witness = true.
  Proof.
    intros report complete witness Hdecision.
    unfold decide_complete in Hdecision.
    destruct (find_valid (report_observed report)) as [found |] eqn:Hfound.
    - inversion Hdecision; subst.
      exact (proj2 (find_valid_sound _ _ Hfound)).
    - discriminate.
  Qed.

  Theorem complete_refuted_is_sound :
    forall report (complete : Complete report),
      decide_complete report complete = Refuted ->
      forall witness, valid witness = false.
  Proof.
    intros report complete Hdecision witness.
    unfold decide_complete in Hdecision.
    destruct (find_valid (report_observed report)) as [found |] eqn:Hfound.
    - discriminate.
    - destruct (valid witness) eqn:Hvalid; [| reflexivity].
      exfalso.
      pose proof (complete witness Hvalid) as Hin.
      pose proof (find_valid_none (report_observed report) Hfound witness Hin) as Hfalse.
      rewrite Hvalid in Hfalse. discriminate.
  Qed.

  Definition admission_allowed (decision : Decision) : bool :=
    match decision with
    | Proven _ => true
    | Refuted | Undetermined => false
    end.

  Theorem undetermined_fails_closed :
    admission_allowed Undetermined = false.
  Proof. reflexivity. Qed.

  Theorem admitted_decision_has_checked_witness :
    forall report,
      admission_allowed (decide_general report) = true ->
      exists witness,
        In witness (report_observed report) /\ valid witness = true.
  Proof.
    intros report Hadmitted.
    unfold admission_allowed, decide_general in Hadmitted.
    destruct (find_valid (report_observed report)) as [witness |] eqn:Hfound.
    - exists witness. apply find_valid_sound. exact Hfound.
    - discriminate.
  Qed.
End RejectSafeSearch.

Section CheckedEvaluation.
  Inductive CheckedTruth : Type :=
  | Determined (value : bool)
  | Unknown.

  Definition checked_not (truth : CheckedTruth) : CheckedTruth :=
    match truth with
    | Determined value => Determined (negb value)
    | Unknown => Unknown
    end.

  Definition checked_admission (truth : CheckedTruth) : bool :=
    match truth with
    | Determined true => true
    | Determined false | Unknown => false
    end.

  Theorem checked_negation_preserves_unknown :
    checked_not Unknown = Unknown.
  Proof. reflexivity. Qed.

  Theorem checked_unknown_fails_closed :
    checked_admission Unknown = false.
  Proof. reflexivity. Qed.

  Theorem checked_negated_unknown_fails_closed :
    checked_admission (checked_not Unknown) = false.
  Proof. reflexivity. Qed.

  Inductive Quantifier : Type := ForallQ | ExistsQ.

  Definition finish_quantifier
      (quantifier : Quantifier)
      (implementation_exhausted : bool)
      (observed : CheckedTruth) : CheckedTruth :=
    if implementation_exhausted then observed
    else
      match quantifier, observed with
      | ForallQ, Determined false => Determined false
      | ExistsQ, Determined true => Determined true
      | _, _ => Unknown
      end.

  Theorem truncated_forall_without_counterexample_is_unknown :
    finish_quantifier ForallQ false (Determined true) = Unknown.
  Proof. reflexivity. Qed.

  Theorem truncated_exists_without_witness_is_unknown :
    finish_quantifier ExistsQ false (Determined false) = Unknown.
  Proof. reflexivity. Qed.

  Theorem truncated_forall_counterexample_is_decisive :
    finish_quantifier ForallQ false (Determined false) = Determined false.
  Proof. reflexivity. Qed.

  Theorem truncated_exists_witness_is_decisive :
    finish_quantifier ExistsQ false (Determined true) = Determined true.
  Proof. reflexivity. Qed.

  Theorem negated_truncated_quantifier_fails_closed :
    checked_admission
      (checked_not (finish_quantifier ForallQ false (Determined true))) = false.
  Proof. reflexivity. Qed.

  Definition entailment_allowed {Witness : Type}
      (counterexample_decision : @Decision Witness) : bool :=
    match counterexample_decision with
    | Refuted => true
    | Proven _ | Undetermined => false
    end.

  Theorem undetermined_counterexample_does_not_prove_entailment :
    forall Witness,
      @entailment_allowed Witness Undetermined = false.
  Proof. reflexivity. Qed.

  Theorem found_counterexample_refutes_entailment :
    forall (Witness : Type) (witness : Witness),
      entailment_allowed (Proven witness) = false.
  Proof. reflexivity. Qed.
End CheckedEvaluation.

Section BoundedCollection.
  Context {A : Type}.

  Record BoundedCollection : Type := {
    collected_values : list A;
    collection_exhausted : bool
  }.

  Definition collect_bounded_status (limit : nat) (stream : list A)
      : BoundedCollection :=
    {| collected_values := firstn limit stream;
       collection_exhausted := Nat.leb (length stream) limit |}.

  Theorem bounded_collection_never_invents_values :
    forall limit stream value,
      In value (collected_values (collect_bounded_status limit stream)) ->
      In value stream.
  Proof.
    induction limit as [| limit IH]; intros stream value Hin.
    - simpl in Hin. contradiction.
    - destruct stream as [| head tail].
      + simpl in Hin. contradiction.
      + simpl in Hin. destruct Hin as [Hequal | Hin].
        * left. exact Hequal.
        * right. apply (IH tail value Hin).
  Qed.

  Theorem bounded_collection_marks_every_truncation :
    forall limit stream,
      length stream > limit ->
      collection_exhausted (collect_bounded_status limit stream) = false.
  Proof.
    intros limit stream Hlong.
    unfold collect_bounded_status. simpl.
    apply Nat.leb_gt. lia.
  Qed.

  Theorem bounded_collection_exhaustion_is_exact_for_the_stream :
    forall limit stream,
      collection_exhausted (collect_bounded_status limit stream) = true ->
      collected_values (collect_bounded_status limit stream) = stream.
  Proof.
    intros limit stream. revert limit.
    induction stream as [| head tail IH]; intros limit Hexhausted.
    - destruct limit; reflexivity.
    - destruct limit as [| limit].
      + simpl in Hexhausted. discriminate.
      + simpl in *. f_equal. apply IH. exact Hexhausted.
  Qed.
End BoundedCollection.

Section ExactFiniteWitnessUniverse.
  Context {Witness : Type}.
  Variable valid : Witness -> Prop.
  Variable satisfies : Witness -> bool.

  (** A classical type-predicate adapter must search one complete semantic
      domain.  In particular, conjunction cannot combine unrelated witnesses
      obtained by deciding its leaves independently. *)
  Definition exact_witness (universe : list Witness) : option Witness :=
    find_valid satisfies universe.

  Definition CompleteWitnessUniverse (universe : list Witness) : Prop :=
    forall witness, valid witness <-> In witness universe.

  Theorem exact_witness_is_shared_and_sound :
    forall universe witness,
      CompleteWitnessUniverse universe ->
      exact_witness universe = Some witness ->
      valid witness /\ satisfies witness = true.
  Proof.
    intros universe witness Hcomplete Hfound.
    unfold exact_witness in Hfound.
    apply find_valid_sound in Hfound as [Hin Hsatisfies].
    split; [now apply (proj2 (Hcomplete witness)) | exact Hsatisfies].
  Qed.

  Theorem complete_witness_universe_refutation_is_sound :
    forall universe,
      CompleteWitnessUniverse universe ->
      exact_witness universe = None ->
      forall witness, valid witness -> satisfies witness = false.
  Proof.
    intros universe Hcomplete Hnone witness Hvalid.
    unfold exact_witness in Hnone.
    now apply (find_valid_none satisfies universe Hnone witness
      (proj1 (Hcomplete witness) Hvalid)).
  Qed.

  Theorem uninhabited_witness_is_excluded :
    forall universe bottom,
      CompleteWitnessUniverse universe ->
      ~ valid bottom ->
      ~ In bottom universe.
  Proof.
    intros universe bottom Hcomplete Huninhabited Hin.
    apply Huninhabited.
    now apply (proj2 (Hcomplete bottom)).
  Qed.
End ExactFiniteWitnessUniverse.

Module IndependentTypeLeafCounterexample.
  Definition universe : list bool := [false; true].
  Definition left (candidate : bool) : bool := candidate.
  Definition right (candidate : bool) : bool := negb candidate.

  (** The former TypeSystemAlgebra algorithm asked whether each leaf had some
      witness, then conjoined those answers. *)
  Definition leafwise_conjunction : bool :=
    existsb left universe && existsb right universe.

  (** Correct satisfiability requires one candidate satisfying both leaves. *)
  Definition shared_witness_conjunction : bool :=
    existsb (fun candidate => left candidate && right candidate) universe.

  Theorem independent_leaf_witnesses_do_not_prove_conjunction :
    leafwise_conjunction = true /\ shared_witness_conjunction = false.
  Proof. split; reflexivity. Qed.
End IndependentTypeLeafCounterexample.

Module OldBooleanCounterexample.
  Definition valid_one (candidate : nat) : bool := Nat.eqb candidate 1.

  Definition old_boolean_result (observed : list nat) : bool :=
    match find_valid valid_one observed with
    | Some _ => true
    | None => false
    end.

  (** The old `None => false` erasure claims unsatisfiability for an empty
      bounded prefix although the semantic domain contains a valid witness. *)
  Theorem bounded_none_to_false_is_unsound :
    old_boolean_result [] = false /\ exists witness, valid_one witness = true.
  Proof.
    split; [reflexivity |].
    exists 1. unfold valid_one. apply Nat.eqb_refl.
  Qed.
End OldBooleanCounterexample.

Print Assumptions general_proven_is_sound.
Print Assumptions truncated_no_witness_is_undetermined.
Print Assumptions implementation_exhaustion_alone_is_undetermined.
Print Assumptions complete_refuted_is_sound.
Print Assumptions undetermined_fails_closed.
Print Assumptions admitted_decision_has_checked_witness.
Print Assumptions checked_negation_preserves_unknown.
Print Assumptions checked_negated_unknown_fails_closed.
Print Assumptions truncated_forall_without_counterexample_is_unknown.
Print Assumptions truncated_exists_without_witness_is_unknown.
Print Assumptions negated_truncated_quantifier_fails_closed.
Print Assumptions undetermined_counterexample_does_not_prove_entailment.
Print Assumptions bounded_collection_marks_every_truncation.
Print Assumptions bounded_collection_exhaustion_is_exact_for_the_stream.
Print Assumptions exact_witness_is_shared_and_sound.
Print Assumptions complete_witness_universe_refutation_is_sound.
Print Assumptions uninhabited_witness_is_excluded.
Print Assumptions IndependentTypeLeafCounterexample.independent_leaf_witnesses_do_not_prove_conjunction.
Print Assumptions OldBooleanCounterexample.bounded_none_to_false_is_unsound.
