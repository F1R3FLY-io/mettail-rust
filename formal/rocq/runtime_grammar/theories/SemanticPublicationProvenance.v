(** Exact provenance through the existing bounded publication collector.

    This file does not supply semantic validity merely because a candidate
    has a bound receipt. It proves that successful publication introduces no
    transition or receipt: every published pair is an unchanged candidate
    supplied to SemanticTransitionKernel. A source-derivation proof can then
    be transported without assuming that envelope validation establishes it.

    This is a soundness result, not a successor-completeness or proof-
    multiplicity result. The existing collector and its deduplication policy
    are imported unchanged. No new evaluator or collection algorithm is
    defined here. *)

From Stdlib Require Import List Bool PeanoNat.
From RuntimeGrammar Require Import SemanticTransitionKernel.

Import ListNotations.
Import SemanticTransitionKernel.SemanticTransitionKernel.

Module SemanticPublicationProvenance.

Definition published_candidate (candidate : RuleCandidate) : ProvenTransition :=
  {| proven_transition := candidate_transition candidate;
     proven_receipt := candidate_receipt candidate |}.

Lemma insertion_retains_exact_pair :
  forall candidate private result,
    In result (insert_unique candidate private) ->
    result = candidate \/ In result private.
Proof.
  intros candidate private result Hin.
  unfold insert_unique in Hin.
  destruct (existsb (proven_eqb candidate) private).
  - now right.
  - simpl in Hin. destruct Hin as [Heq | Hin]; auto.
Qed.

Theorem collection_retains_exact_candidate_or_private_pair :
  forall pending manifest request fuel used private results final_used,
    collect_candidates manifest request fuel used pending private =
      CollectionComplete results final_used ->
    forall result, In result results ->
      In result private \/
      exists candidate, In candidate pending /\
        result = published_candidate candidate.
Proof.
  induction pending as [|candidate rest IH];
    intros manifest request fuel used private results final_used Hcollect
      result Hin.
  - simpl in Hcollect. inversion Hcollect; subst.
    left. now apply in_rev in Hin.
  - simpl in Hcollect.
    destruct (Nat.leb (candidate_work candidate) fuel); try discriminate.
    destruct (receipt_bound manifest request
      (candidate_transition candidate) (candidate_receipt candidate));
      try discriminate.
    specialize (IH manifest request _ _ _ results final_used Hcollect result Hin).
    destruct IH as [Hprivate | [origin [Horigin Heq]]].
    + apply insertion_retains_exact_pair in Hprivate.
      destruct Hprivate as [Heq | Hin_private].
      * right. exists candidate. split; [now left | exact Heq].
      * now left.
    + right. exists origin. split; [now right | exact Heq].
Qed.

Theorem complete_collection_from_empty_has_exact_origin :
  forall manifest request fuel used candidates results final_used result,
    collect_candidates manifest request fuel used candidates [] =
      CollectionComplete results final_used ->
    In result results ->
    exists candidate, In candidate candidates /\
      proven_transition result = candidate_transition candidate /\
      proven_receipt result = candidate_receipt candidate.
Proof.
  intros manifest request fuel used candidates results final_used result
    Hcollect Hin.
  destruct (collection_retains_exact_candidate_or_private_pair candidates
    manifest request fuel used [] results final_used Hcollect result Hin)
    as [Hempty | [candidate [Hcandidate Heq]]].
  - contradiction.
  - subst result. exists candidate. repeat split; auto.
Qed.

Theorem proven_successor_has_exact_input_candidate :
  forall manifest request fuel cancelled candidates results result,
    successor_decision manifest request fuel cancelled candidates =
      Proven results ->
    In result results ->
    exists candidate, In candidate candidates /\
      proven_transition result = candidate_transition candidate /\
      proven_receipt result = candidate_receipt candidate.
Proof.
  intros manifest request fuel cancelled candidates results result Hdecision Hin.
  unfold successor_decision in Hdecision.
  destruct cancelled; try discriminate.
  destruct (negb (request_admitted manifest request)); try discriminate.
  destruct (collect_candidates manifest request fuel 0 candidates [])
    as [collected used | reason used] eqn:Hcollect; try discriminate.
  destruct collected as [|first rest]; try discriminate.
  destruct (deterministic_claim manifest (request_action request) &&
    Nat.ltb 1 (length (first :: rest))); try discriminate.
  inversion Hdecision; subst results.
  eapply complete_collection_from_empty_has_exact_origin; eauto.
Qed.

Lemma found_output_was_in_the_supplied_results :
  forall target results result,
    find_output target results = Some result -> In result results.
Proof.
  intros target results. induction results as [|head tail IH];
    intros result Hfind; simpl in Hfind; try discriminate.
  destruct (same_output target head).
  - inversion Hfind; subst. now left.
  - right. now apply IH.
Qed.

Theorem verified_output_has_exact_input_candidate :
  forall manifest request fuel cancelled candidates target result,
    verify_transition manifest request fuel cancelled candidates target =
      Proven result ->
    exists candidate, In candidate candidates /\
      proven_transition result = candidate_transition candidate /\
      proven_receipt result = candidate_receipt candidate.
Proof.
  intros manifest request fuel cancelled candidates target result Hverified.
  unfold verify_transition in Hverified.
  destruct (successor_decision manifest request fuel cancelled candidates)
    as [results | refuted | undetermined] eqn:Hsuccess; try discriminate.
  destruct (find_output target results) as [found |] eqn:Hfind;
    try discriminate.
  inversion Hverified; subst found.
  eapply proven_successor_has_exact_input_candidate; eauto.
  now apply found_output_was_in_the_supplied_results in Hfind.
Qed.

(** The parameter below is a transport interface, not an assumption of source
    validity hidden inside a receipt checker. Instantiating it with authored
    derivations requires the separate source-frame completion theorem and
    an authentic projection of those completed frames into candidates. *)
Theorem publication_transports_established_candidate_properties :
  forall (property : SemanticTransition -> TransitionReceipt -> Prop)
    manifest request fuel cancelled candidates results,
    (forall candidate, In candidate candidates ->
      property (candidate_transition candidate) (candidate_receipt candidate)) ->
    successor_decision manifest request fuel cancelled candidates =
      Proven results ->
    forall result, In result results ->
      property (proven_transition result) (proven_receipt result).
Proof.
  intros property manifest request fuel cancelled candidates results
    Hproperty Hdecision result Hin.
  destruct (proven_successor_has_exact_input_candidate manifest request fuel
    cancelled candidates results result Hdecision Hin)
    as [candidate [Hcandidate [Htransition Hreceipt]]].
  rewrite Htransition, Hreceipt. now apply Hproperty.
Qed.

End SemanticPublicationProvenance.

Print Assumptions SemanticPublicationProvenance.insertion_retains_exact_pair.
Print Assumptions SemanticPublicationProvenance.collection_retains_exact_candidate_or_private_pair.
Print Assumptions SemanticPublicationProvenance.complete_collection_from_empty_has_exact_origin.
Print Assumptions SemanticPublicationProvenance.proven_successor_has_exact_input_candidate.
Print Assumptions SemanticPublicationProvenance.found_output_was_in_the_supplied_results.
Print Assumptions SemanticPublicationProvenance.verified_output_has_exact_input_candidate.
Print Assumptions SemanticPublicationProvenance.publication_transports_established_candidate_properties.
