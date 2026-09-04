(**
  SemanticTransitionKernel: proof-carrying, bounded publication for the single
  runtime semantic-transition boundary.

  The matcher, premise machine, capture-avoiding substitution engine, and
  equality engine produce [RuleCandidate] values.  Their local correctness is
  supplied by ExecutableTheoryImage, the Dovetail set-automaton proofs, and the
  de-Bruijn substitution development.  This file proves the composition rule
  which is easy to lose in an implementation: candidates are private until
  their complete fingerprint/capability/receipt envelope has been checked.
  Exhaustion and cancellation discard the private accumulator, so neither a
  prefix of the successor set nor a prefix of its effects can escape.

  Commitments are modeled as byte strings ([list nat]).  Their cryptographic
  construction is outside the transition calculus; only exact equality is
  used here, matching the Rust boundary's full 32-byte comparisons.

  Rocq 9.1 compatible.  No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List Bool PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Module SemanticTransitionKernel.

Definition Commitment := list nat.
Definition ActionId := nat.
Definition RuleId := nat.
Definition RightId := nat.
Definition EffectId := nat.
Definition SortId := nat.

(** Semantic resource accounting is optional structure on a theory.  It is
    deliberately independent of the action's effect class: a pure action may
    still consume a semantic resource.  An uncosted theory carries no semantic
    grade, while a costed theory must provide checked, non-empty grade
    evidence. *)
Inductive ResourceProfile :=
| Uncosted
| Costed.

Inductive ResourceEvidence :=
| NoSemanticGrade
| CheckedSemanticGrade (commitment : Commitment).

(** A version-1 rule-backed semantic action is a label on a transition of one
    canonical term.  Its declared domain is therefore exactly one source sort,
    and its codomain is the referenced rule's target sort.  This removes an
    otherwise under-specified mapping from an arbitrary argument vector to a
    single rule redex.  More general handlers require a distinct checked ABI;
    they cannot be inferred from a [RuleId]. *)
Record RuleSignature := {
  rule_source_sort : SortId;
  rule_target_sort : SortId
}.

Record RuleBackedActionSignature := {
  action_domain_sorts : list SortId;
  action_codomain_sort : SortId
}.

Definition rule_backed_action_compatible
    (action : RuleBackedActionSignature)
    (rule : RuleSignature) : Prop :=
  action_domain_sorts action = [rule_source_sort rule] /\
  action_codomain_sort action = rule_target_sort rule.

Theorem compatible_rule_backed_action_has_exact_source_and_target :
  forall action rule input_sort output_sort,
    rule_backed_action_compatible action rule ->
    input_sort = rule_source_sort rule ->
    output_sort = rule_target_sort rule ->
    action_domain_sorts action = [input_sort] /\
    action_codomain_sort action = output_sort.
Proof.
  intros action rule input_sort output_sort [Hdomain Hcodomain] Hinput Houtput.
  subst input_sort. subst output_sort. auto.
Qed.

Theorem same_sort_rule_backed_action_is_endomorphic :
  forall action rule,
    rule_backed_action_compatible action rule ->
    rule_source_sort rule = rule_target_sort rule ->
    action_domain_sorts action = [action_codomain_sort action].
Proof.
  intros action rule [Hdomain Hcodomain] Hsame.
  rewrite Hdomain, Hcodomain, Hsame. reflexivity.
Qed.

Fixpoint nat_list_eqb (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | left_head :: left_tail, right_head :: right_tail =>
      Nat.eqb left_head right_head && nat_list_eqb left_tail right_tail
  | _, _ => false
  end.

Lemma nat_list_eqb_spec :
  forall left right, nat_list_eqb left right = true <-> left = right.
Proof.
  induction left as [|left_head left_tail IH];
    destruct right as [|right_head right_tail]; simpl.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, Nat.eqb_eq, IH.
    split.
    + intros [Hhead Htail]. now rewrite Hhead, Htail.
    + intro Heq. inversion Heq; subst. auto.
Qed.

Definition resource_evidence_eqb
    (left right : ResourceEvidence) : bool :=
  match left, right with
  | NoSemanticGrade, NoSemanticGrade => true
  | CheckedSemanticGrade left_grade, CheckedSemanticGrade right_grade =>
      nat_list_eqb left_grade right_grade
  | _, _ => false
  end.

Lemma resource_evidence_eqb_spec :
  forall left right,
    resource_evidence_eqb left right = true <-> left = right.
Proof.
  intros [|left_grade] [|right_grade]; simpl.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite nat_list_eqb_spec. split; congruence.
Qed.

Definition resource_evidence_valid
    (profile : ResourceProfile) (evidence : ResourceEvidence) : bool :=
  match profile, evidence with
  | Uncosted, NoSemanticGrade => true
  | Costed, CheckedSemanticGrade grade => negb (Nat.eqb (length grade) 0)
  | _, _ => false
  end.

Lemma uncosted_evidence_cannot_fabricate_a_grade :
  forall evidence,
    resource_evidence_valid Uncosted evidence = true ->
    evidence = NoSemanticGrade.
Proof. intros [|grade] H; simpl in H; [reflexivity|discriminate]. Qed.

Lemma costed_evidence_contains_a_checked_grade :
  forall evidence,
    resource_evidence_valid Costed evidence = true ->
    exists grade,
      evidence = CheckedSemanticGrade grade /\ grade <> [].
Proof.
  intros [|grade] H; simpl in H; try discriminate.
  exists grade. split; [reflexivity|].
  apply Bool.negb_true_iff in H. apply Nat.eqb_neq in H.
  destruct grade; [simpl in H; contradiction|discriminate].
Qed.

(** Input admission and successor publication have different resource
    dimensions.  In particular, attenuating an output quota must not
    retroactively invalidate a canonical input term. *)
Record SemanticTermBounds := {
  bound_input_nodes : nat;
  bound_input_bytes : nat;
  bound_output_nodes : nat;
  bound_output_bytes : nat
}.

Definition input_admitted
    (bounds : SemanticTermBounds) (nodes bytes : nat) : bool :=
  Nat.leb nodes (bound_input_nodes bounds) &&
  Nat.leb bytes (bound_input_bytes bounds).

Definition output_admitted
    (bounds : SemanticTermBounds) (nodes bytes : nat) : bool :=
  Nat.leb nodes (bound_output_nodes bounds) &&
  Nat.leb bytes (bound_output_bytes bounds).

Definition output_only_attenuation
    (base narrower : SemanticTermBounds) : Prop :=
  bound_input_nodes narrower = bound_input_nodes base /\
  bound_input_bytes narrower = bound_input_bytes base /\
  bound_output_nodes narrower <= bound_output_nodes base /\
  bound_output_bytes narrower <= bound_output_bytes base.

Theorem output_attenuation_cannot_reject_an_admitted_input :
  forall base narrower nodes bytes,
    output_only_attenuation base narrower ->
    input_admitted base nodes bytes = true ->
    input_admitted narrower nodes bytes = true.
Proof.
  intros base narrower nodes bytes [Hnodes [Hbytes [_ _]]] Hadmitted.
  unfold input_admitted in *. now rewrite Hnodes, Hbytes.
Qed.

Definition member_nat (needle : nat) (haystack : list nat) : bool :=
  existsb (Nat.eqb needle) haystack.

Definition rights_subset (required granted : list RightId) : bool :=
  forallb (fun right => member_nat right granted) required.

Record ActionManifest := {
  manifest_action : ActionId;
  manifest_required_rights : list RightId;
  manifest_resource_profile : ResourceProfile
}.

Record KernelManifest := {
  manifest_language : Commitment;
  manifest_theory : Commitment;
  manifest_image : Commitment;
  manifest_actions : list ActionManifest;
  manifest_deterministic_actions : list ActionId
}.

Record TransitionRequest := {
  request_language : Commitment;
  request_theory : Commitment;
  request_image : Commitment;
  request_action : ActionId;
  request_input : Commitment;
  request_granted_rights : list RightId
}.

Fixpoint find_action
    (action : ActionId) (manifests : list ActionManifest)
    : option ActionManifest :=
  match manifests with
  | [] => None
  | manifest :: rest =>
      if Nat.eqb action (manifest_action manifest)
      then Some manifest
      else find_action action rest
  end.

Definition request_admitted
    (manifest : KernelManifest) (request : TransitionRequest) : bool :=
  nat_list_eqb (request_language request) (manifest_language manifest) &&
  nat_list_eqb (request_theory request) (manifest_theory manifest) &&
  nat_list_eqb (request_image request) (manifest_image manifest) &&
  match find_action (request_action request) (manifest_actions manifest) with
  | None => false
  | Some action =>
      rights_subset (manifest_required_rights action)
                    (request_granted_rights request)
  end.

Record SemanticTransition := {
  transition_action : ActionId;
  transition_rule : RuleId;
  transition_input : Commitment;
  transition_output : Commitment;
  transition_grade : ResourceEvidence;
  transition_observation : Commitment;
  transition_effects : list EffectId
}.

Record TransitionReceipt := {
  receipt_language : Commitment;
  receipt_theory : Commitment;
  receipt_image : Commitment;
  receipt_action : ActionId;
  receipt_rule : RuleId;
  receipt_input : Commitment;
  receipt_output : Commitment;
  receipt_grade : ResourceEvidence;
  receipt_effects : list EffectId;
  receipt_work : nat
}.

Definition receipt_bound
    (manifest : KernelManifest)
    (request : TransitionRequest)
    (transition : SemanticTransition)
    (receipt : TransitionReceipt) : bool :=
  nat_list_eqb (receipt_language receipt) (manifest_language manifest) &&
  nat_list_eqb (receipt_theory receipt) (manifest_theory manifest) &&
  nat_list_eqb (receipt_image receipt) (manifest_image manifest) &&
  Nat.eqb (receipt_action receipt) (request_action request) &&
  Nat.eqb (receipt_action receipt) (transition_action transition) &&
  Nat.eqb (receipt_rule receipt) (transition_rule transition) &&
  nat_list_eqb (receipt_input receipt) (request_input request) &&
  nat_list_eqb (receipt_input receipt) (transition_input transition) &&
  nat_list_eqb (receipt_output receipt) (transition_output transition) &&
  resource_evidence_eqb (receipt_grade receipt) (transition_grade transition) &&
  match find_action (request_action request) (manifest_actions manifest) with
  | Some action =>
      resource_evidence_valid
        (manifest_resource_profile action) (transition_grade transition)
  | None => false
  end &&
  nat_list_eqb (receipt_effects receipt) (transition_effects transition) &&
  Nat.leb 1 (receipt_work receipt).

Theorem bound_receipt_has_profile_valid_resource_evidence :
  forall manifest request transition receipt action,
    find_action (request_action request) (manifest_actions manifest) =
      Some action ->
    receipt_bound manifest request transition receipt = true ->
    resource_evidence_valid
      (manifest_resource_profile action) (transition_grade transition) = true.
Proof.
  intros manifest request transition receipt action Haction Hbound.
  unfold receipt_bound in Hbound. rewrite Haction in Hbound.
  repeat rewrite andb_true_iff in Hbound. tauto.
Qed.

Record ProvenTransition := {
  proven_transition : SemanticTransition;
  proven_receipt : TransitionReceipt
}.

Inductive UndeterminedReason :=
| WorkBudgetExhausted
| Cancelled
| InvalidInternalEvidence.

Inductive RefutedReason :=
| RequestRejected
| NoTransition
| DeterminismClaimViolated
| PresentedTransitionAbsent.

Inductive Decision (A : Type) :=
| Proven : A -> Decision A
| Refuted : RefutedReason -> Decision A
| Undetermined : UndeterminedReason -> Decision A.

Arguments Proven {A} _.
Arguments Refuted {A} _.
Arguments Undetermined {A} _.

Record RuleCandidate := {
  candidate_transition : SemanticTransition;
  candidate_receipt : TransitionReceipt
}.

Definition candidate_work (candidate : RuleCandidate) : nat :=
  receipt_work (candidate_receipt candidate).

Definition transition_eqb
    (left right : SemanticTransition) : bool :=
  Nat.eqb (transition_action left) (transition_action right) &&
  Nat.eqb (transition_rule left) (transition_rule right) &&
  nat_list_eqb (transition_input left) (transition_input right) &&
  nat_list_eqb (transition_output left) (transition_output right) &&
  resource_evidence_eqb (transition_grade left) (transition_grade right) &&
  nat_list_eqb (transition_observation left) (transition_observation right) &&
  nat_list_eqb (transition_effects left) (transition_effects right).

Lemma transition_eqb_spec :
  forall left right, transition_eqb left right = true <-> left = right.
Proof.
  intros [la lr li lo lg lob le] [ra rr ri ro rg rob re].
  unfold transition_eqb; simpl.
  repeat rewrite andb_true_iff.
  repeat rewrite Nat.eqb_eq.
  repeat rewrite nat_list_eqb_spec.
  repeat rewrite resource_evidence_eqb_spec.
  intuition congruence.
Qed.

Definition proven_eqb (left right : ProvenTransition) : bool :=
  transition_eqb (proven_transition left) (proven_transition right).

Definition insert_unique
    (candidate : ProvenTransition) (results : list ProvenTransition)
    : list ProvenTransition :=
  if existsb (proven_eqb candidate) results
  then results
  else candidate :: results.

Inductive CollectionResult :=
| CollectionComplete (results : list ProvenTransition) (used : nat)
| CollectionStopped (reason : UndeterminedReason) (used : nat).

Fixpoint collect_candidates
    (manifest : KernelManifest)
    (request : TransitionRequest)
    (fuel used : nat)
    (pending : list RuleCandidate)
    (private_results : list ProvenTransition)
    : CollectionResult :=
  match pending with
  | [] => CollectionComplete (rev private_results) used
  | candidate :: rest =>
      let work := candidate_work candidate in
      if Nat.leb work fuel then
        if receipt_bound manifest request
             (candidate_transition candidate) (candidate_receipt candidate)
        then
          collect_candidates manifest request (fuel - work) (used + work) rest
            (insert_unique
              {| proven_transition := candidate_transition candidate;
                 proven_receipt := candidate_receipt candidate |}
              private_results)
        else CollectionStopped InvalidInternalEvidence used
      else CollectionStopped WorkBudgetExhausted used
  end.

Definition deterministic_claim
    (manifest : KernelManifest) (action : ActionId) : bool :=
  member_nat action (manifest_deterministic_actions manifest).

Definition successor_decision
    (manifest : KernelManifest)
    (request : TransitionRequest)
    (fuel : nat)
    (cancelled : bool)
    (candidates : list RuleCandidate)
    : Decision (list ProvenTransition) :=
  if cancelled then Undetermined Cancelled
  else if negb (request_admitted manifest request) then Refuted RequestRejected
  else
    match collect_candidates manifest request fuel 0 candidates [] with
    | CollectionStopped reason _ => Undetermined reason
    | CollectionComplete [] _ => Refuted NoTransition
    | CollectionComplete results _ =>
        if deterministic_claim manifest (request_action request) &&
           Nat.ltb 1 (length results)
        then Refuted DeterminismClaimViolated
        else Proven results
    end.

Definition committable_effects
    (decision : Decision (list ProvenTransition)) : list EffectId :=
  match decision with
  | Proven results =>
      concat (map (fun result =>
        transition_effects (proven_transition result)) results)
  | Refuted _ | Undetermined _ => []
  end.

Definition same_output
    (target : Commitment) (result : ProvenTransition) : bool :=
  nat_list_eqb target
    (transition_output (proven_transition result)).

Fixpoint find_output
    (target : Commitment) (results : list ProvenTransition)
    : option ProvenTransition :=
  match results with
  | [] => None
  | result :: rest =>
      if same_output target result then Some result else find_output target rest
  end.

Definition verify_transition
    (manifest : KernelManifest)
    (request : TransitionRequest)
    (fuel : nat)
    (cancelled : bool)
    (candidates : list RuleCandidate)
    (target : Commitment)
    : Decision ProvenTransition :=
  match successor_decision manifest request fuel cancelled candidates with
  | Proven results =>
      match find_output target results with
      | Some result => Proven result
      | None => Refuted PresentedTransitionAbsent
      end
  | Refuted reason => Refuted reason
  | Undetermined reason => Undetermined reason
  end.

Definition verified_effects
    (decision : Decision ProvenTransition) : list EffectId :=
  match decision with
  | Proven result => transition_effects (proven_transition result)
  | Refuted _ | Undetermined _ => []
  end.

Theorem cancellation_never_publishes :
  forall manifest request fuel candidates,
    committable_effects
      (successor_decision manifest request fuel true candidates) = [].
Proof. reflexivity. Qed.

Theorem rejected_request_never_publishes :
  forall manifest request fuel candidates,
    request_admitted manifest request = false ->
    committable_effects
      (successor_decision manifest request fuel false candidates) = [].
Proof.
  intros manifest request fuel candidates Hrejected.
  unfold successor_decision. simpl. now rewrite Hrejected.
Qed.

Theorem collection_stop_discards_private_prefix :
  forall manifest request fuel used candidates private reason stopped_used,
    collect_candidates manifest request fuel used candidates private =
      CollectionStopped reason stopped_used ->
    committable_effects (Undetermined reason) = [].
Proof. reflexivity. Qed.

Theorem exhausted_successor_search_never_publishes :
  forall manifest request fuel candidates,
    successor_decision manifest request fuel false candidates =
      Undetermined WorkBudgetExhausted ->
    committable_effects
      (successor_decision manifest request fuel false candidates) = [].
Proof. intros; now rewrite H. Qed.

Theorem invalid_evidence_never_publishes :
  forall manifest request fuel candidates,
    successor_decision manifest request fuel false candidates =
      Undetermined InvalidInternalEvidence ->
    committable_effects
      (successor_decision manifest request fuel false candidates) = [].
Proof. intros; now rewrite H. Qed.

Theorem determinism_violation_never_publishes :
  forall manifest request fuel cancelled candidates,
    successor_decision manifest request fuel cancelled candidates =
      Refuted DeterminismClaimViolated ->
    committable_effects
      (successor_decision manifest request fuel cancelled candidates) = [].
Proof. intros; now rewrite H. Qed.

Lemma find_output_sound :
  forall target results result,
    find_output target results = Some result ->
    In result results /\
    transition_output (proven_transition result) = target.
Proof.
  intros target results. induction results as [|head rest IH]; intros result Hfind;
    simpl in Hfind; try discriminate.
  destruct (same_output target head) eqn:Hsame.
  - inversion Hfind; subst result. split; [now left|].
    unfold same_output in Hsame. apply nat_list_eqb_spec in Hsame. now symmetry.
  - apply IH in Hfind. destruct Hfind as [Hin Houtput].
    split; [now right|exact Houtput].
Qed.

Theorem verified_transition_is_a_complete_successor :
  forall manifest request fuel cancelled candidates target result,
    verify_transition manifest request fuel cancelled candidates target = Proven result ->
    exists results,
      successor_decision manifest request fuel cancelled candidates = Proven results /\
      In result results /\
      transition_output (proven_transition result) = target.
Proof.
  intros manifest request fuel cancelled candidates target result Hverify.
  unfold verify_transition in Hverify.
  destruct (successor_decision manifest request fuel cancelled candidates)
    as [results|reason|reason] eqn:Hsuccessors; try discriminate.
  destruct (find_output target results) as [found|] eqn:Hfind; try discriminate.
  inversion Hverify; subst found.
  apply find_output_sound in Hfind.
  destruct Hfind as [Hin Houtput].
  exists results. auto.
Qed.

Theorem unverified_transition_never_publishes :
  forall manifest request fuel cancelled candidates target reason,
    verify_transition manifest request fuel cancelled candidates target =
      Undetermined reason ->
    verified_effects
      (verify_transition manifest request fuel cancelled candidates target) = [].
Proof. intros; now rewrite H. Qed.

Theorem transition_search_is_deterministic :
  forall manifest request fuel cancelled candidates,
    successor_decision manifest request fuel cancelled candidates =
    successor_decision manifest request fuel cancelled candidates.
Proof. reflexivity. Qed.

Theorem zero_fuel_cannot_run_positive_candidate :
  forall manifest request candidate rest private used,
    Nat.leb 1 (candidate_work candidate) = true ->
    collect_candidates manifest request 0 used (candidate :: rest) private =
      CollectionStopped WorkBudgetExhausted used.
Proof.
  intros manifest request candidate rest private used Hpositive.
  simpl. unfold candidate_work in *.
  apply Nat.leb_le in Hpositive.
  assert (Nat.leb (receipt_work (candidate_receipt candidate)) 0 = false)
    by (apply Nat.leb_gt; lia).
  now rewrite H.
Qed.

(** The set-automaton evaluator uses the same publication discipline one layer
    earlier.  A scan step represents one explicitly charged unit (or batch of
    units) of root dispatch, state evaluation, slot merging, or match emission.
    The cancellation bit is sampled before its work is charged.  Emissions stay
    in a private accumulator until every step has completed. *)
Record MatcherStep := {
  matcher_step_work : nat;
  matcher_step_cancelled : bool;
  matcher_step_emissions : list nat
}.

Inductive MatcherStop :=
| MatcherWorkBudgetExhausted
| MatcherCancelled.

Inductive MatcherResult :=
| MatcherComplete (matches : list nat) (used : nat)
| MatcherStopped (reason : MatcherStop) (used : nat).

Fixpoint run_matcher_private
    (fuel used : nat)
    (steps : list MatcherStep)
    (private_matches : list nat) : MatcherResult :=
  match steps with
  | [] => MatcherComplete (rev private_matches) used
  | step :: rest =>
      if matcher_step_cancelled step
      then MatcherStopped MatcherCancelled used
      else if Nat.leb (matcher_step_work step) fuel
      then run_matcher_private
             (fuel - matcher_step_work step)
             (used + matcher_step_work step)
             rest
             (rev_append (matcher_step_emissions step) private_matches)
      else MatcherStopped MatcherWorkBudgetExhausted used
  end.

Definition published_matcher_results (result : MatcherResult) : list nat :=
  match result with
  | MatcherComplete matches _ => matches
  | MatcherStopped _ _ => []
  end.

Theorem stopped_matcher_never_publishes_private_prefix :
  forall fuel used steps private reason stopped_used,
    run_matcher_private fuel used steps private =
      MatcherStopped reason stopped_used ->
    published_matcher_results
      (run_matcher_private fuel used steps private) = [].
Proof. intros; now rewrite H. Qed.

Theorem matcher_cancellation_precedes_work_and_publication :
  forall fuel used work emissions rest private,
    run_matcher_private fuel used
      ({| matcher_step_work := work;
          matcher_step_cancelled := true;
          matcher_step_emissions := emissions |} :: rest)
      private = MatcherStopped MatcherCancelled used /\
    published_matcher_results
      (run_matcher_private fuel used
        ({| matcher_step_work := work;
            matcher_step_cancelled := true;
            matcher_step_emissions := emissions |} :: rest)
        private) = [].
Proof. intros; simpl; auto. Qed.

Theorem matcher_exhaustion_precedes_work_and_publication :
  forall fuel used work emissions rest private,
    fuel < work ->
    run_matcher_private fuel used
      ({| matcher_step_work := work;
          matcher_step_cancelled := false;
          matcher_step_emissions := emissions |} :: rest)
      private = MatcherStopped MatcherWorkBudgetExhausted used /\
    published_matcher_results
      (run_matcher_private fuel used
        ({| matcher_step_work := work;
            matcher_step_cancelled := false;
            matcher_step_emissions := emissions |} :: rest)
        private) = [].
Proof.
  intros fuel used work emissions rest private Hlt.
  simpl. assert (Nat.leb work fuel = false) by (apply Nat.leb_gt; lia).
  now rewrite H.
Qed.

Theorem matcher_success_publishes_only_after_the_complete_scan :
  forall fuel used steps private matches final_used,
    run_matcher_private fuel used steps private =
      MatcherComplete matches final_used ->
    published_matcher_results
      (run_matcher_private fuel used steps private) = matches.
Proof. intros; now rewrite H. Qed.

(** Premise proofs use a FIFO frontier rather than native recursion.  A branch
    is an opaque checked machine state: its internal environment and pending
    premise continuation are represented by identifiers here and by bounded
    arenas in the runtime image.  The scheduler is intentionally independent
    of any particular theory or judgment. *)
Record PremiseBranch := {
  premise_branch_id : nat;
  premise_branch_continuation : list nat
}.

Inductive PremiseStepResult :=
| PremiseRefuted
| PremiseAdvanced (children : list PremiseBranch)
| PremiseProven (candidate : RuleCandidate)
| PremiseUndetermined (reason : UndeterminedReason).

Inductive PremiseFrontierResult :=
| PremiseFrontierComplete (candidates : list RuleCandidate) (used : nat)
| PremiseFrontierStopped (reason : UndeterminedReason) (used : nat).

(** Existing siblings remain ahead of descendants produced by the current
    branch.  This is the breadth-first, round-robin fairness rule. *)
Definition enqueue_premise_children
    (siblings children : list PremiseBranch) : list PremiseBranch :=
  siblings ++ children.

Theorem premise_children_never_overtake_existing_siblings :
  forall siblings children,
    firstn (length siblings) (enqueue_premise_children siblings children) =
    siblings.
Proof.
  intros siblings children.
  unfold enqueue_premise_children.
  now rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
Qed.

(** [step] is the checked semantic operation for one frontier state.  The
    recursion below is solely over [fuel], never over a guest term, proof, or
    premise tree.  Exactly one unit is charged before [step] is observed. *)
Fixpoint run_premise_frontier
    (step : PremiseBranch -> PremiseStepResult)
    (fuel used : nat)
    (frontier : list PremiseBranch)
    (private_candidates : list RuleCandidate) : PremiseFrontierResult :=
  match frontier with
  | [] => PremiseFrontierComplete (rev private_candidates) used
  | branch :: siblings =>
      match fuel with
      | O => PremiseFrontierStopped WorkBudgetExhausted used
      | S remaining =>
          match step branch with
          | PremiseRefuted =>
              run_premise_frontier step remaining (S used)
                siblings private_candidates
          | PremiseAdvanced children =>
              run_premise_frontier step remaining (S used)
                (enqueue_premise_children siblings children)
                private_candidates
          | PremiseProven candidate =>
              run_premise_frontier step remaining (S used)
                siblings (candidate :: private_candidates)
          | PremiseUndetermined reason =>
              PremiseFrontierStopped reason (S used)
          end
      end
  end.

Definition published_premise_candidates
    (result : PremiseFrontierResult) : list RuleCandidate :=
  match result with
  | PremiseFrontierComplete candidates _ => candidates
  | PremiseFrontierStopped _ _ => []
  end.

Theorem stopped_premise_frontier_discards_private_candidates :
  forall step fuel used frontier private reason stopped_used,
    run_premise_frontier step fuel used frontier private =
      PremiseFrontierStopped reason stopped_used ->
    published_premise_candidates
      (run_premise_frontier step fuel used frontier private) = [].
Proof. intros; now rewrite H. Qed.

Theorem empty_premise_frontier_is_the_only_immediate_publication_point :
  forall step fuel used private,
    run_premise_frontier step fuel used [] private =
      PremiseFrontierComplete (rev private) used.
Proof. intros step [|fuel] used private; reflexivity. Qed.

Theorem zero_fuel_nonempty_premise_frontier_cannot_publish :
  forall step used branch siblings private,
    run_premise_frontier step 0 used (branch :: siblings) private =
      PremiseFrontierStopped WorkBudgetExhausted used /\
    published_premise_candidates
      (run_premise_frontier step 0 used (branch :: siblings) private) = [].
Proof. intros; simpl; auto. Qed.

Theorem premise_frontier_step_is_deterministic :
  forall step fuel used frontier private,
    run_premise_frontier step fuel used frontier private =
    run_premise_frontier step fuel used frontier private.
Proof. reflexivity. Qed.

Theorem premise_frontier_charges_before_undetermined_stop :
  forall step fuel used branch siblings private reason,
    0 < fuel ->
    step branch = PremiseUndetermined reason ->
    run_premise_frontier step fuel used (branch :: siblings) private =
      PremiseFrontierStopped reason (S used).
Proof.
  intros step [|remaining] used branch siblings private reason Hfuel Hstep;
    [inversion Hfuel|].
  simpl. now rewrite Hstep.
Qed.

(** A Horn-clause activation owns a fresh namespace.  The local variable
    number emitted by the theory image is therefore never used as a global
    proof-search identity: the runtime key is the pair
    [(activation, local_variable)].  This is the minimum structure required
    for recursive clauses and premise-only existential variables to coexist
    without capture. *)
Record ScopedVariable := {
  scoped_activation : nat;
  scoped_local : nat
}.

Definition scoped_variable_eqb
    (left right : ScopedVariable) : bool :=
  Nat.eqb (scoped_activation left) (scoped_activation right) &&
  Nat.eqb (scoped_local left) (scoped_local right).

Lemma scoped_variable_eqb_spec :
  forall left right,
    scoped_variable_eqb left right = true <-> left = right.
Proof.
  intros [left_activation left_local] [right_activation right_local].
  unfold scoped_variable_eqb; simpl.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split.
  - intros [Hactivation Hlocal]. now subst.
  - intro Heq. inversion Heq. auto.
Qed.

Theorem different_activations_cannot_capture_the_same_local_variable :
  forall left_activation right_activation local,
    left_activation <> right_activation ->
    {| scoped_activation := left_activation; scoped_local := local |} <>
    {| scoped_activation := right_activation; scoped_local := local |}.
Proof.
  intros left_activation right_activation local Hdifferent Hequal.
  inversion Hequal. contradiction.
Qed.

(** [LogicTerm] is the mathematical view of the runtime's flat term arena.
    Rust retains nodes by dense image reference and evaluates this structure
    with an explicit worklist; the inductive view is used only to state the
    Martelli--Montanari head-step contract. *)
Inductive LogicTerm :=
| LogicVariable (variable : ScopedVariable)
| LogicApplication (operator : nat) (arguments : list LogicTerm).

Fixpoint scoped_occurs (needle : ScopedVariable) (term : LogicTerm) : bool :=
  match term with
  | LogicVariable variable => scoped_variable_eqb needle variable
  | LogicApplication _ arguments => existsb (scoped_occurs needle) arguments
  end.

Inductive BindingDecision :=
| BindingIdentity
| BindingAccepted (variable : ScopedVariable) (term : LogicTerm)
| BindingRejectedOccurs.

(** Literate head-binding algorithm.

    - If both sides are the same scoped variable, emit the identity step.
    - Otherwise, reject when the variable occurs in the already-dereferenced
      target.
    - Only an occurs-free target extends the branch-local substitution.

    The runtime charges before dereference, each visited arena node, the
    occurs scan, and publication of the accepted binding. *)
Definition decide_binding
    (variable : ScopedVariable) (term : LogicTerm) : BindingDecision :=
  match term with
  | LogicVariable other =>
      if scoped_variable_eqb variable other
      then BindingIdentity
      else BindingAccepted variable term
  | LogicApplication _ _ =>
      if scoped_occurs variable term
      then BindingRejectedOccurs
      else BindingAccepted variable term
  end.

Theorem accepted_binding_is_occurs_free :
  forall variable term bound_variable bound_term,
    decide_binding variable term =
      BindingAccepted bound_variable bound_term ->
    variable = bound_variable /\ term = bound_term /\
    scoped_occurs variable term = false.
Proof.
  intros variable [other|operator arguments] bound_variable bound_term Hdecision.
  - simpl in Hdecision.
    destruct (scoped_variable_eqb variable other) eqn:Hequal; try discriminate.
    inversion Hdecision; subst.
    repeat split; auto.
  - simpl in Hdecision.
    destruct (existsb (scoped_occurs variable) arguments) eqn:Hoccurs;
      try discriminate.
    inversion Hdecision; subst.
    repeat split; auto.
Qed.

Theorem self_binding_is_identity_not_a_cycle :
  forall variable,
    decide_binding variable (LogicVariable variable) = BindingIdentity.
Proof.
  intro variable. simpl.
  rewrite (proj2 (scoped_variable_eqb_spec variable variable) eq_refl).
  reflexivity.
Qed.

Definition ScopedSubstitution := list (ScopedVariable * LogicTerm).

Fixpoint lookup_scoped
    (needle : ScopedVariable) (substitution : ScopedSubstitution)
    : option LogicTerm :=
  match substitution with
  | [] => None
  | (variable, term) :: rest =>
      if scoped_variable_eqb needle variable
      then Some term
      else lookup_scoped needle rest
  end.

Definition extend_scoped
    (variable : ScopedVariable)
    (term : LogicTerm)
    (substitution : ScopedSubstitution) : ScopedSubstitution :=
  (variable, term) :: substitution.

Theorem extending_one_scoped_variable_preserves_every_other_lookup :
  forall substitution variable term other,
    other <> variable ->
    lookup_scoped other (extend_scoped variable term substitution) =
    lookup_scoped other substitution.
Proof.
  intros substitution variable term other Hdifferent.
  unfold extend_scoped. simpl.
  destruct (scoped_variable_eqb other variable) eqn:Hequal; auto.
  apply scoped_variable_eqb_spec in Hequal. contradiction.
Qed.

Inductive UnificationHeadDecision :=
| UnificationHeadIdentity
| UnificationHeadBind (decision : BindingDecision)
| UnificationHeadDecompose (equations : list (LogicTerm * LogicTerm))
| UnificationHeadClash.

(** One checked Martelli--Montanari head step.  Constructor equality and arity
    equality are both established before child equations enter the private
    worklist, so a malformed or clashing application cannot publish a partial
    substitution. *)
Definition decide_unification_head
    (left right : LogicTerm) : UnificationHeadDecision :=
  match left, right with
  | LogicVariable variable, term =>
      UnificationHeadBind (decide_binding variable term)
  | term, LogicVariable variable =>
      UnificationHeadBind (decide_binding variable term)
  | LogicApplication left_operator left_arguments,
    LogicApplication right_operator right_arguments =>
      if Nat.eqb left_operator right_operator &&
         Nat.eqb (length left_arguments) (length right_arguments)
      then UnificationHeadDecompose (combine left_arguments right_arguments)
      else UnificationHeadClash
  end.

Theorem different_constructor_heads_are_rejected_before_decomposition :
  forall left_operator right_operator left_arguments right_arguments,
    left_operator <> right_operator ->
    decide_unification_head
      (LogicApplication left_operator left_arguments)
      (LogicApplication right_operator right_arguments) =
    UnificationHeadClash.
Proof.
  intros left_operator right_operator left_arguments right_arguments Hdifferent.
  assert (Hequal : Nat.eqb left_operator right_operator = false).
  { apply Nat.eqb_neq. exact Hdifferent. }
  simpl. now rewrite Hequal.
Qed.

Theorem different_constructor_arities_are_rejected_before_decomposition :
  forall operator left_arguments right_arguments,
    length left_arguments <> length right_arguments ->
    decide_unification_head
      (LogicApplication operator left_arguments)
      (LogicApplication operator right_arguments) =
    UnificationHeadClash.
Proof.
  intros operator left_arguments right_arguments Hdifferent.
  simpl. rewrite Nat.eqb_refl. simpl.
  assert (Hequal :
    Nat.eqb (length left_arguments) (length right_arguments) = false).
  { apply Nat.eqb_neq. exact Hdifferent. }
  now rewrite Hequal.
Qed.

Theorem compatible_constructor_heads_decompose_positionally :
  forall operator left_arguments right_arguments,
    length left_arguments = length right_arguments ->
    decide_unification_head
      (LogicApplication operator left_arguments)
      (LogicApplication operator right_arguments) =
    UnificationHeadDecompose (combine left_arguments right_arguments).
Proof.
  intros operator left_arguments right_arguments Harity.
  simpl. rewrite !Nat.eqb_refl. now rewrite Harity, Nat.eqb_refl.
Qed.

(** Runtime terms are supplied by an untrusted caller, whereas the source
    theory is no longer consulted on the execution hot path.  The semantic
    image must therefore retain a dense, independently checked description of
    every sort.  In particular, a substitution operator that retained only
    its result sort would lose the function domain whenever two function
    sorts shared that codomain. *)
Inductive RuntimeSortShape :=
| RuntimeSyntax (literal_carrier : option nat)
| RuntimeCollection (kind : nat) (key : option SortId) (element : SortId)
| RuntimeFunction (domain codomain : SortId) (multiple : bool)
| RuntimeProduct (factors : list SortId)
| RuntimeOpaque.

Definition RuntimeSortTable := list RuntimeSortShape.

Inductive RuntimeOperator :=
| RuntimeConstructor (domain : list SortId) (codomain : SortId)
| RuntimeAbstraction (function_sort : SortId)
| RuntimeSubstitution (function_sort : SortId)
| RuntimeCollectionLiteral
    (collection_sort element_sort : SortId) (kind : nat)
| RuntimeMap
    (source_sort target_sort : SortId) (parameter_sorts : list SortId)
| RuntimeZip (product_sort : SortId)
| RuntimeLiteral (sort : SortId) (carrier : nat).

Inductive RuntimeChildContract :=
| FixedChildren (sorts : list SortId)
| HomogeneousChildren (sort : SortId).

Record RuntimeOperatorSignature := {
  runtime_result_sort : SortId;
  runtime_child_contract : RuntimeChildContract
}.

(** A mapped element is destructured into the factors of a product, or into
    one parameter when it is not a product.  Carrying this exact parameter
    vector in the operator prevents a map body from being interpreted under a
    different binding telescope. *)
Definition map_parameter_sorts
    (sorts : RuntimeSortTable) (element : SortId) : list SortId :=
  match nth_error sorts element with
  | Some (RuntimeProduct factors) => factors
  | Some _ => [element]
  | None => []
  end.

Definition map_parameters_admitted
    (sorts : RuntimeSortTable) (element : SortId)
    (declared : list SortId) : bool :=
  nat_list_eqb declared (map_parameter_sorts sorts element).

Theorem admitted_map_parameters_are_the_exact_source_telescope :
  forall sorts element declared,
    map_parameters_admitted sorts element declared = true ->
    declared = map_parameter_sorts sorts element.
Proof.
  intros sorts element declared Hadmitted.
  unfold map_parameters_admitted in Hadmitted.
  now apply nat_list_eqb_spec.
Qed.

Definition runtime_operator_signature
    (sorts : RuntimeSortTable) (operator : RuntimeOperator)
    : option RuntimeOperatorSignature :=
  match operator with
  | RuntimeConstructor domain codomain =>
      Some {| runtime_result_sort := codomain;
              runtime_child_contract := FixedChildren domain |}
  | RuntimeAbstraction function_sort =>
      match nth_error sorts function_sort with
      | Some (RuntimeFunction domain codomain _) =>
          Some {| runtime_result_sort := function_sort;
                  runtime_child_contract := FixedChildren [domain; codomain] |}
      | _ => None
      end
  | RuntimeSubstitution function_sort =>
      match nth_error sorts function_sort with
      | Some (RuntimeFunction domain codomain _) =>
          Some {| runtime_result_sort := codomain;
                  runtime_child_contract :=
                    FixedChildren [function_sort; domain] |}
      | _ => None
      end
  | RuntimeCollectionLiteral collection_sort element_sort kind =>
      match nth_error sorts collection_sort with
      | Some (RuntimeCollection declared_kind _ declared_element) =>
          if Nat.eqb kind declared_kind &&
             Nat.eqb element_sort declared_element
          then Some {| runtime_result_sort := collection_sort;
                       runtime_child_contract :=
                         HomogeneousChildren element_sort |}
          else None
      | _ => None
      end
  | RuntimeMap source_sort target_sort parameter_sorts =>
      match nth_error sorts source_sort, nth_error sorts target_sort with
      | Some (RuntimeCollection source_kind _ source_element),
        Some (RuntimeCollection target_kind _ target_element) =>
          if Nat.eqb source_kind target_kind &&
             nat_list_eqb parameter_sorts
               (map_parameter_sorts sorts source_element)
          then Some {| runtime_result_sort := target_sort;
                       runtime_child_contract := FixedChildren
                         (parameter_sorts ++ [source_sort; target_element]) |}
          else None
      | _, _ => None
      end
  | RuntimeZip product_sort =>
      match nth_error sorts product_sort with
      | Some (RuntimeProduct [left_sort; right_sort]) =>
          Some {| runtime_result_sort := product_sort;
                  runtime_child_contract :=
                    FixedChildren [left_sort; right_sort] |}
      | _ => None
      end
  | RuntimeLiteral sort carrier =>
      match nth_error sorts sort with
      | Some (RuntimeSyntax (Some declared_carrier)) =>
          if Nat.eqb carrier declared_carrier
          then Some {| runtime_result_sort := sort;
                       runtime_child_contract := FixedChildren [] |}
          else None
      | _ => None
      end
  end.

Theorem substitution_signature_recovers_the_function_domain_and_codomain :
  forall sorts function_sort domain codomain multiple,
    nth_error sorts function_sort =
      Some (RuntimeFunction domain codomain multiple) ->
    runtime_operator_signature sorts (RuntimeSubstitution function_sort) =
      Some {| runtime_result_sort := codomain;
              runtime_child_contract :=
                FixedChildren [function_sort; domain] |}.
Proof. intros sorts function_sort domain codomain multiple H; simpl; now rewrite H. Qed.

Theorem abstraction_signature_places_the_binder_before_the_body :
  forall sorts function_sort domain codomain multiple,
    nth_error sorts function_sort =
      Some (RuntimeFunction domain codomain multiple) ->
    runtime_operator_signature sorts (RuntimeAbstraction function_sort) =
      Some {| runtime_result_sort := function_sort;
              runtime_child_contract := FixedChildren [domain; codomain] |}.
Proof. intros sorts function_sort domain codomain multiple H; simpl; now rewrite H. Qed.

(** Concrete counterexample to the old result-only substitution encoding: both
    function sorts return sort 2, but their argument sorts differ.  No decoder
    receiving only the result identifier 2 can choose the required child
    signature. *)
Example result_only_substitution_signature_is_ambiguous :
  let sorts := [RuntimeFunction 0 2 false; RuntimeFunction 1 2 false] in
  runtime_operator_signature sorts (RuntimeSubstitution 0) =
    Some {| runtime_result_sort := 2;
            runtime_child_contract := FixedChildren [0; 0] |} /\
  runtime_operator_signature sorts (RuntimeSubstitution 1) =
    Some {| runtime_result_sort := 2;
            runtime_child_contract := FixedChildren [1; 1] |}.
Proof. split; reflexivity. Qed.

Theorem map_signature_preserves_the_complete_binding_telescope :
  forall sorts source target source_kind source_element target_element
         parameters,
    nth_error sorts source =
      Some (RuntimeCollection source_kind None source_element) ->
    nth_error sorts target =
      Some (RuntimeCollection source_kind None target_element) ->
    map_parameter_sorts sorts source_element = parameters ->
    runtime_operator_signature sorts (RuntimeMap source target parameters) =
      Some {| runtime_result_sort := target;
              runtime_child_contract := FixedChildren
                (parameters ++ [source; target_element]) |}.
Proof.
  intros sorts source target source_kind source_element target_element
    parameters Hsource Htarget Hparameters.
  simpl. rewrite Hsource, Htarget, Nat.eqb_refl, Hparameters.
  rewrite (proj2 (nat_list_eqb_spec parameters parameters) eq_refl).
  reflexivity.
Qed.

(** A judgment conclusion has a synthetic operator and ground argument
    e-classes.  The implementation evaluates that application view directly;
    it does not insert a synthetic node into the caller's semantic e-graph.
    Both routes invoke the same root evaluator. *)
Record ApplicationView := {
  application_operator : nat;
  application_arguments : list nat
}.

Definition ApplicationEvaluator :=
  ApplicationView -> list (nat * ScopedSubstitution).

Definition evaluate_virtual_application
    (evaluate : ApplicationEvaluator) (view : ApplicationView) :=
  evaluate view.

Definition evaluate_singleton_physical_root
    (evaluate : ApplicationEvaluator) (nodes : list ApplicationView) :=
  match nodes with
  | [view] => evaluate view
  | _ => []
  end.

Theorem virtual_application_matches_singleton_physical_root :
  forall evaluate view,
    evaluate_virtual_application evaluate view =
    evaluate_singleton_physical_root evaluate [view].
Proof. reflexivity. Qed.

Print Assumptions cancellation_never_publishes.
Print Assumptions rejected_request_never_publishes.
Print Assumptions exhausted_successor_search_never_publishes.
Print Assumptions invalid_evidence_never_publishes.
Print Assumptions determinism_violation_never_publishes.
Print Assumptions verified_transition_is_a_complete_successor.
Print Assumptions unverified_transition_never_publishes.
Print Assumptions transition_search_is_deterministic.
Print Assumptions zero_fuel_cannot_run_positive_candidate.
Print Assumptions stopped_matcher_never_publishes_private_prefix.
Print Assumptions matcher_cancellation_precedes_work_and_publication.
Print Assumptions matcher_exhaustion_precedes_work_and_publication.
Print Assumptions matcher_success_publishes_only_after_the_complete_scan.
Print Assumptions premise_children_never_overtake_existing_siblings.
Print Assumptions stopped_premise_frontier_discards_private_candidates.
Print Assumptions empty_premise_frontier_is_the_only_immediate_publication_point.
Print Assumptions zero_fuel_nonempty_premise_frontier_cannot_publish.
Print Assumptions premise_frontier_step_is_deterministic.
Print Assumptions premise_frontier_charges_before_undetermined_stop.
Print Assumptions different_activations_cannot_capture_the_same_local_variable.
Print Assumptions accepted_binding_is_occurs_free.
Print Assumptions self_binding_is_identity_not_a_cycle.
Print Assumptions extending_one_scoped_variable_preserves_every_other_lookup.
Print Assumptions different_constructor_heads_are_rejected_before_decomposition.
Print Assumptions different_constructor_arities_are_rejected_before_decomposition.
Print Assumptions compatible_constructor_heads_decompose_positionally.
Print Assumptions substitution_signature_recovers_the_function_domain_and_codomain.
Print Assumptions abstraction_signature_places_the_binder_before_the_body.
Print Assumptions result_only_substitution_signature_is_ambiguous.
Print Assumptions admitted_map_parameters_are_the_exact_source_telescope.
Print Assumptions map_signature_preserves_the_complete_binding_telescope.
Print Assumptions virtual_application_matches_singleton_physical_root.
Print Assumptions compatible_rule_backed_action_has_exact_source_and_target.
Print Assumptions same_sort_rule_backed_action_is_endomorphic.
Print Assumptions uncosted_evidence_cannot_fabricate_a_grade.
Print Assumptions costed_evidence_contains_a_checked_grade.
Print Assumptions bound_receipt_has_profile_valid_resource_evidence.
Print Assumptions output_attenuation_cannot_reject_an_admitted_input.

End SemanticTransitionKernel.
