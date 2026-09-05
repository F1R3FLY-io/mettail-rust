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

From Stdlib Require Import List Bool PeanoNat Permutation.
From Stdlib Require Import Lia.
From Dovetail.Lowering Require Import CollectionAcLowering.
From RuntimeGrammar Require Import CollectionComprehension.

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

(** An action label selects only its declared rule identifiers.  A transition
    premise has different semantics: it queries the theory-wide rewrite
    relation at the premise's source sort.  Equations remain structural
    congruence and therefore cannot become nested transition steps. *)
Inductive RuleOrigin :=
| EquationOrigin
| RewriteOrigin.

Record TransitionRuleManifest := {
  transition_rule_id : RuleId;
  transition_rule_origin : RuleOrigin;
  transition_rule_source_sort : SortId;
  transition_rule_target_sort : SortId;
  transition_rule_executable : bool
}.

Definition action_rule_selected
    (rule_ids : list RuleId) (rule : TransitionRuleManifest) : bool :=
  transition_rule_executable rule &&
  existsb (Nat.eqb (transition_rule_id rule)) rule_ids.

Definition rewrite_relation_rule_selected
    (sort : SortId) (rule : TransitionRuleManifest) : bool :=
  transition_rule_executable rule &&
  match transition_rule_origin rule with
  | EquationOrigin => false
  | RewriteOrigin => Nat.eqb (transition_rule_source_sort rule) sort
  end.

Theorem rewrite_relation_selects_exactly_executable_same_sort_rewrites :
  forall sort rule,
    rewrite_relation_rule_selected sort rule = true <->
    transition_rule_executable rule = true /\
    transition_rule_origin rule = RewriteOrigin /\
    transition_rule_source_sort rule = sort.
Proof.
  intros sort [rule_id origin source_sort target_sort executable].
  unfold rewrite_relation_rule_selected.
  destruct origin; simpl.
  - split.
    + intro Hselected. destruct executable; discriminate Hselected.
    + intros [_ [Horigin _]]. discriminate Horigin.
  - destruct executable; simpl.
    + split.
      * intro Hselected. apply Nat.eqb_eq in Hselected.
        repeat split; try reflexivity; exact Hselected.
      * intros [_ [_ Hsort]]. apply Nat.eqb_eq. exact Hsort.
    + split.
      * intro Himpossible. discriminate Himpossible.
      * intros [Hfalse _]. discriminate Hfalse.
Qed.

Theorem rewrite_relation_never_selects_an_equation :
  forall sort rule,
    transition_rule_origin rule = EquationOrigin ->
    rewrite_relation_rule_selected sort rule = false.
Proof.
  intros sort [rule_id origin source_sort target_sort executable] Horigin.
  unfold rewrite_relation_rule_selected.
  destruct origin; simpl; [destruct executable; reflexivity|discriminate].
Qed.

Theorem action_selection_does_not_confine_the_rewrite_relation :
  forall action_rules nested_rule sort,
    transition_rule_executable nested_rule = true ->
    transition_rule_origin nested_rule = RewriteOrigin ->
    transition_rule_source_sort nested_rule = sort ->
    action_rule_selected action_rules nested_rule = false ->
    rewrite_relation_rule_selected sort nested_rule = true.
Proof.
  intros action_rules nested_rule sort Hexecutable Horigin Hsort _.
  apply rewrite_relation_selects_exactly_executable_same_sort_rewrites.
  repeat split; assumption.
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

(** Nested semantic transitions execute in a fresh child frame.  Returning a
    child result resumes from the saved parent substitution and binds only the
    declared target variable; the child's private substitution is deliberately
    not an argument to [resume_transition].  This is the semantic counterpart
    of the runtime's explicit continuation stack. *)
Record TransitionResumeFrame := {
  transition_parent_substitution : ScopedSubstitution;
  transition_target_variable : ScopedVariable
}.

Definition resume_transition
    (frame : TransitionResumeFrame) (successor : LogicTerm)
    : ScopedSubstitution :=
  extend_scoped
    (transition_target_variable frame)
    successor
    (transition_parent_substitution frame).

Definition resume_nested_transition
    (frame : TransitionResumeFrame) (successor : LogicTerm)
    (_child_private_substitution : ScopedSubstitution)
    : ScopedSubstitution :=
  resume_transition frame successor.

Theorem resumed_transition_binds_exact_target :
  forall frame successor,
    lookup_scoped
      (transition_target_variable frame)
      (resume_transition frame successor) = Some successor.
Proof.
  intros frame successor.
  unfold resume_transition, extend_scoped. simpl.
  rewrite (proj2
    (scoped_variable_eqb_spec
      (transition_target_variable frame)
      (transition_target_variable frame)) eq_refl).
  reflexivity.
Qed.

Theorem resumed_transition_preserves_every_parent_binding :
  forall frame successor other,
    other <> transition_target_variable frame ->
    lookup_scoped other (resume_transition frame successor) =
    lookup_scoped other (transition_parent_substitution frame).
Proof.
  intros frame successor other Hdifferent.
  unfold resume_transition.
  now apply extending_one_scoped_variable_preserves_every_other_lookup.
Qed.

Theorem child_substitutions_cannot_escape_transition_resume :
  forall frame successor
    (child_left child_right : ScopedSubstitution),
    resume_nested_transition frame successor child_left =
    resume_nested_transition frame successor child_right.
Proof. reflexivity. Qed.

(** A universal collection premise evaluates its body in an overlay and then
    restores the exact saved outer substitution.  Consequently quantified and
    body-local derived variables cannot survive one element iteration or leak
    into the next. *)
Record ForAllScope := {
  forall_outer_substitution : ScopedSubstitution;
  forall_parameter_variable : ScopedVariable;
  forall_element_value : LogicTerm
}.

Definition enter_forall_scope (scope : ForAllScope) : ScopedSubstitution :=
  extend_scoped
    (forall_parameter_variable scope)
    (forall_element_value scope)
    (forall_outer_substitution scope).

Definition leave_forall_scope
    (scope : ForAllScope) (_body_private_substitution : ScopedSubstitution)
    : ScopedSubstitution :=
  forall_outer_substitution scope.

Theorem entered_forall_scope_binds_exact_element :
  forall scope,
    lookup_scoped
      (forall_parameter_variable scope)
      (enter_forall_scope scope) = Some (forall_element_value scope).
Proof.
  intro scope.
  unfold enter_forall_scope, extend_scoped. simpl.
  rewrite (proj2
    (scoped_variable_eqb_spec
      (forall_parameter_variable scope)
      (forall_parameter_variable scope)) eq_refl).
  reflexivity.
Qed.

Theorem leaving_forall_scope_restores_exact_outer_substitution :
  forall scope (body_private_substitution : ScopedSubstitution),
    leave_forall_scope scope body_private_substitution =
    forall_outer_substitution scope.
Proof. reflexivity. Qed.

(** AC row unification may need a fresh residual row shared by the two tail
    bindings.  The residual row is allocated in a globally fresh activation,
    rather than borrowing a clause-local index.  This is the same monotone
    activation namespace used by the runtime and makes non-capture independent
    of how many locals a clause declares. *)
Definition internal_scoped_variable
    (fresh_activation : nat) : ScopedVariable :=
  {| scoped_activation := fresh_activation;
     scoped_local := 0 |}.

Theorem internal_row_variable_cannot_capture_declared_variable :
  forall fresh_activation clause_activation declared_local,
    fresh_activation <> clause_activation ->
    internal_scoped_variable fresh_activation <>
    {| scoped_activation := clause_activation; scoped_local := declared_local |}.
Proof.
  intros fresh_activation clause_activation declared_local Hfresh Hequal.
  inversion Hequal. contradiction.
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

(** Collection patterns are not positional applications.  An ordered
    collection with a remainder consumes a prefix and binds the exact suffix;
    an unordered collection enumerates positional sub-multiset splits and
    binds the exact complement.  The latter reuses Dovetail's proved lazy
    selector rather than introducing a second enumeration semantics in the
    semantic kernel. *)
Definition ordered_collection_split
    (fixed_count : nat) (subject : list nat)
    : option (list nat * list nat) :=
  if fixed_count <=? length subject
  then Some (firstn fixed_count subject, skipn fixed_count subject)
  else None.

Theorem accepted_ordered_collection_split_is_exact :
  forall fixed_count subject selected remainder,
    ordered_collection_split fixed_count subject =
      Some (selected, remainder) ->
    subject = selected ++ remainder /\
    length selected = fixed_count.
Proof.
  intros fixed_count subject selected remainder Hsplit.
  unfold ordered_collection_split in Hsplit.
  destruct (fixed_count <=? length subject) eqn:Hfits; try discriminate.
  inversion Hsplit; subst; clear Hsplit.
  split.
  - symmetry. apply firstn_skipn.
  - rewrite length_firstn. apply Nat.min_l. now apply Nat.leb_le.
Qed.

Definition admitted_unordered_collection_branch
    (subject : list nat) (fixed_count : nat)
    (selected remainder : list nat) : Prop :=
  In (selected, remainder) (ac_select subject fixed_count).

Theorem admitted_unordered_collection_branch_is_exact :
  forall subject fixed_count selected remainder,
    admitted_unordered_collection_branch
      subject fixed_count selected remainder ->
    Permutation subject (selected ++ remainder) /\
    length selected = fixed_count.
Proof.
  intros subject fixed_count selected remainder Hadmitted.
  unfold admitted_unordered_collection_branch in Hadmitted.
  now apply ac_select_partitions_bag in Hadmitted.
Qed.

(** A two-sided unordered-row branch chooses the same number of fixed
    occurrences from each side.  Semantic unification subsequently pairs the
    two selected lists; before any pair is admitted, both selections already
    carry exact, disjoint complements.  Unmatched right occurrences populate
    the left tail, unmatched left occurrences populate the right tail, and an
    internal fresh residual row is shared when both source rows are open. *)
Definition admitted_unordered_row_pairing
    (left right : list nat) (paired_count : nat)
    (left_selected left_unmatched right_selected right_unmatched : list nat)
    : Prop :=
  In (left_selected, left_unmatched) (ac_select left paired_count) /\
  In (right_selected, right_unmatched) (ac_select right paired_count).

Theorem admitted_unordered_row_pairing_partitions_both_sides :
  forall left right paired_count
    left_selected left_unmatched right_selected right_unmatched,
    admitted_unordered_row_pairing
      left right paired_count
      left_selected left_unmatched right_selected right_unmatched ->
    Permutation left (left_selected ++ left_unmatched) /\
    length left_selected = paired_count /\
    Permutation right (right_selected ++ right_unmatched) /\
    length right_selected = paired_count.
Proof.
  intros left right paired_count
    left_selected left_unmatched right_selected right_unmatched
    [Hleft Hright].
  apply ac_select_partitions_bag in Hleft.
  apply ac_select_partitions_bag in Hright.
  tauto.
Qed.

(** Range restriction is a sufficient fast-path condition, not an admission
    restriction on the Horn language.  When every variable used by a premise
    occurs in its conclusion, matching a ground conclusion grounds every
    recursive premise.  The full evaluator additionally gives each clause
    activation a fresh variable namespace (proved above), so premise-only
    variables remain sound bounded search variables rather than being captured
    or silently rejected.  Collection matching itself remains directional;
    unrestricted symmetric AC row unification is not confused with matching. *)
Definition variables_covered
    (conclusion_variables premise_variables : list nat) : Prop :=
  forall variable,
    In variable premise_variables -> In variable conclusion_variables.

Definition variables_bound
    (substitution_domain variables : list nat) : Prop :=
  forall variable,
    In variable variables -> In variable substitution_domain.

Theorem range_restricted_premise_is_ground_after_conclusion_match :
  forall conclusion_variables premise_variables substitution_domain,
    variables_covered conclusion_variables premise_variables ->
    variables_bound substitution_domain conclusion_variables ->
    variables_bound substitution_domain premise_variables.
Proof.
  intros conclusion_variables premise_variables substitution_domain
    Hcovered Hbound variable Hvariable.
  apply Hbound. now apply Hcovered.
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
| RuntimeProductNode (product_sort : SortId)
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
  | RuntimeProductNode product_sort =>
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

Theorem product_signature_preserves_binary_product_factors :
  forall sorts product_sort left_sort right_sort,
    nth_error sorts product_sort =
      Some (RuntimeProduct [left_sort; right_sort]) ->
    runtime_operator_signature sorts (RuntimeProductNode product_sort) =
      Some {| runtime_result_sort := product_sort;
              runtime_child_contract :=
                FixedChildren [left_sort; right_sort] |}.
Proof.
  intros sorts product_sort left_sort right_sort Hproduct.
  simpl. now rewrite Hproduct.
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

(** Freshness is absence of a free occurrence, not absence of a syntactic
    occurrence.  The runtime graph stores an abstraction binder and body as
    two child e-classes, but a freshness traversal never descends into the
    binder position.  A binder equal to the sought term also shields the
    complete body.  These rules are independent of the concrete arena and
    therefore apply equally to trees, shared DAGs, and cyclic e-graphs; the
    implementation's visited set is solely a bounded termination mechanism. *)
Inductive RuntimeFreshnessNode :=
| RuntimePlainNode (children : list nat)
| RuntimeAbstractionNode (binder body : nat).

Definition RuntimeFreshnessGraph := nat -> option RuntimeFreshnessNode.

Inductive FreeOccurrence
    (graph : RuntimeFreshnessGraph) (needle : nat) : nat -> Prop :=
| FreeOccurrenceHere : FreeOccurrence graph needle needle
| FreeOccurrencePlain : forall root children child,
    graph root = Some (RuntimePlainNode children) ->
    In child children ->
    FreeOccurrence graph needle child ->
    FreeOccurrence graph needle root
| FreeOccurrenceAbstraction : forall root binder body,
    graph root = Some (RuntimeAbstractionNode binder body) ->
    binder <> needle ->
    FreeOccurrence graph needle body ->
    FreeOccurrence graph needle root.

Definition freshness_holds
    (graph : RuntimeFreshnessGraph) (needle target : nat) : Prop :=
  ~ FreeOccurrence graph needle target.

Inductive FreshnessStep :=
| FreshnessFound
| FreshnessContinue (children : list nat)
| FreshnessMalformed.

(** The equality check precedes graph inspection, exactly as in the runtime
    worklist.  Consequently the root itself is observable even if it is also
    an abstraction, while the binder child is never scheduled. *)
Definition freshness_step
    (graph : RuntimeFreshnessGraph) (needle root : nat) : FreshnessStep :=
  if Nat.eqb root needle then FreshnessFound
  else
    match graph root with
    | None => FreshnessMalformed
    | Some (RuntimePlainNode children) => FreshnessContinue children
    | Some (RuntimeAbstractionNode binder body) =>
        if Nat.eqb binder needle
        then FreshnessContinue []
        else FreshnessContinue [body]
    end.

Theorem matching_abstraction_binder_schedules_no_body :
  forall graph root needle body,
    root <> needle ->
    graph root = Some (RuntimeAbstractionNode needle body) ->
    freshness_step graph needle root = FreshnessContinue [].
Proof.
  intros graph root needle body Hroot Hgraph.
  unfold freshness_step.
  destruct (Nat.eqb root needle) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. contradiction.
  - rewrite Hgraph, Nat.eqb_refl. reflexivity.
Qed.

Theorem different_abstraction_binder_schedules_exactly_the_body :
  forall graph root needle binder body,
    root <> needle ->
    binder <> needle ->
    graph root = Some (RuntimeAbstractionNode binder body) ->
    freshness_step graph needle root = FreshnessContinue [body].
Proof.
  intros graph root needle binder body Hroot Hbinder Hgraph.
  unfold freshness_step.
  destruct (Nat.eqb root needle) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. contradiction.
  - rewrite Hgraph.
    destruct (Nat.eqb binder needle) eqn:Hsame_binder.
    + apply Nat.eqb_eq in Hsame_binder. contradiction.
    + reflexivity.
Qed.

Theorem matching_abstraction_binder_shields_every_body_occurrence :
  forall graph root needle body,
    root <> needle ->
    graph root = Some (RuntimeAbstractionNode needle body) ->
    freshness_holds graph needle root.
Proof.
  intros graph root needle body Hroot Hgraph Hoccurs.
  inversion Hoccurs as
    [|root' children child Hplain Hin Hchild
     |root' binder' body' Habstraction Hbinder Hbody]; subst.
  - contradiction.
  - rewrite Hgraph in Hplain. discriminate.
  - rewrite Hgraph in Habstraction. inversion Habstraction; subst.
    apply Hbinder. reflexivity.
Qed.

Theorem different_abstraction_binder_preserves_body_freedom :
  forall graph root needle binder body,
    root <> needle ->
    binder <> needle ->
    graph root = Some (RuntimeAbstractionNode binder body) ->
    (FreeOccurrence graph needle body <->
     FreeOccurrence graph needle root).
Proof.
  intros graph root needle binder body Hroot Hbinder Hgraph.
  split.
  - intro Hbody. eapply FreeOccurrenceAbstraction; eauto.
  - intro Hroot_occurs.
    inversion Hroot_occurs as
      [|root' children child Hplain Hin Hchild
       |root' binder' body' Habstraction Hbinder' Hbody]; subst.
    + contradiction.
    + rewrite Hgraph in Hplain. discriminate.
    + rewrite Hgraph in Habstraction. inversion Habstraction; subst.
      exact Hbody.
Qed.

(** Successful execution may allocate nodes for branches that are ultimately
    refuted.  Publication therefore copies a closed reachable subgraph into a
    fresh arena.  Outputs and exported substitution values are the roots; no
    other private node is an observable root. *)
Record PublicationNode := {
  publication_label : nat;
  publication_children : list nat
}.

Definition PublicationGraph := nat -> option PublicationNode.

Inductive ReachableFrom
    (graph : PublicationGraph) (roots : list nat) : nat -> Prop :=
| ReachableRoot : forall root,
    In root roots -> ReachableFrom graph roots root
| ReachableChild : forall parent node children,
    ReachableFrom graph roots parent ->
    graph parent = Some node ->
    In children (publication_children node) ->
    ReachableFrom graph roots children.

Definition all_reachable
    (graph : PublicationGraph) (roots nodes : list nat) : Prop :=
  Forall (ReachableFrom graph roots) nodes.

Lemma reachable_children_of_a_reachable_parent :
  forall graph roots parent node,
    ReachableFrom graph roots parent ->
    graph parent = Some node ->
    all_reachable graph roots (publication_children node).
Proof.
  intros graph roots parent node Hparent Hnode.
  unfold all_reachable. apply Forall_forall.
  intros child Hchild.
  eapply ReachableChild; eauto.
Qed.

Theorem iterative_projection_pushes_only_reachable_nodes :
  forall graph roots parent node pending discovered,
    all_reachable graph roots (parent :: pending) ->
    all_reachable graph roots discovered ->
    graph parent = Some node ->
    all_reachable graph roots
      (publication_children node ++ pending) /\
    all_reachable graph roots (parent :: discovered).
Proof.
  intros graph roots parent node pending discovered
    Hpending Hdiscovered Hnode.
  inversion Hpending as [|parent' pending' Hparent Hrest]; subst.
  split.
  - unfold all_reachable in *.
    apply Forall_app. split.
    + now apply reachable_children_of_a_reachable_parent with (parent := parent).
    + exact Hrest.
  - constructor; assumption.
Qed.

Inductive ChildrenRemapped (remap : nat -> option nat)
    : list nat -> list nat -> Prop :=
| ChildrenRemappedNil : ChildrenRemapped remap [] []
| ChildrenRemappedCons : forall source target sources targets,
    remap source = Some target ->
    ChildrenRemapped remap sources targets ->
    ChildrenRemapped remap (source :: sources) (target :: targets).

Record ReachabilityProjection
    (source : PublicationGraph) (roots : list nat) := {
  projection_remap : nat -> option nat;
  projection_graph : PublicationGraph;
  projection_roots_valid : forall source_id,
    In source_id roots -> exists source_node, source source_id = Some source_node;
  projection_domain_exact : forall source_id,
    ReachableFrom source roots source_id <->
    exists target_id, projection_remap source_id = Some target_id;
  projection_nodes_exact : forall source_id target_id source_node,
    projection_remap source_id = Some target_id ->
    source source_id = Some source_node ->
    exists target_children,
      ChildrenRemapped projection_remap
        (publication_children source_node) target_children /\
      projection_graph target_id =
        Some {| publication_label := publication_label source_node;
                publication_children := target_children |}
}.

Theorem invalid_publication_root_has_no_projection :
  forall source roots root,
    In root roots ->
    source root = None ->
    ReachabilityProjection source roots -> False.
Proof.
  intros source roots root Hroot Hmissing projection.
  destruct (projection_roots_valid source roots projection root Hroot)
    as [source_node Hsource].
  rewrite Hmissing in Hsource. discriminate.
Qed.

Theorem unreachable_private_node_has_no_published_identifier :
  forall source roots (projection : ReachabilityProjection source roots) private,
    ~ ReachableFrom source roots private ->
    projection_remap source roots projection private = None.
Proof.
  intros source roots projection private Hunreachable.
  destruct (projection_remap source roots projection private) as [target|] eqn:Hmap;
    [|reflexivity].
  exfalso. apply Hunreachable.
  apply (proj2 (projection_domain_exact source roots projection private)).
  now exists target.
Qed.

Theorem every_publication_root_receives_an_identifier :
  forall source roots (projection : ReachabilityProjection source roots) root,
    In root roots ->
    exists target, projection_remap source roots projection root = Some target.
Proof.
  intros source roots projection root Hroot.
  apply (proj1 (projection_domain_exact source roots projection root)).
  now apply ReachableRoot.
Qed.

Theorem projected_children_preserve_order_and_arity :
  forall remap sources targets,
    ChildrenRemapped remap sources targets ->
    length sources = length targets.
Proof.
  intros remap sources targets Hmapped.
  induction Hmapped; simpl; congruence.
Qed.

(** Canonical collection admission is part of the transition boundary, not a
    convenience performed by callers.  [ExactKey] abstracts the complete
    framed structural key computed by the Rust implementation; naturals give
    us a decidable total order without assuming a finite digest is identity.

    A PathMap carries an explicit mode independently of its entry count.  Its
    three empty values are therefore distinct, and its physical encoding has
    one leading mode marker.  Set-mode payloads contain keys, whereas map-mode
    payloads contain key/value pairs. *)
Definition ExactKey := nat.

Inductive RuntimeCollectionKind :=
| AdmissionList
| AdmissionBag
| AdmissionSet
| AdmissionMap
| AdmissionPathMap.

Inductive RuntimePathMapMode :=
| RuntimePathMapNeutral
| RuntimePathMapSet
| RuntimePathMapMap.

Inductive RuntimeCollectionEntry :=
| RuntimeValueEntry (value : ExactKey)
| RuntimePairEntry (key value : ExactKey).

Fixpoint value_entries_only (entries : list RuntimeCollectionEntry) : Prop :=
  match entries with
  | [] => True
  | RuntimeValueEntry _ :: rest => value_entries_only rest
  | RuntimePairEntry _ _ :: _ => False
  end.

Fixpoint pair_entries_only (entries : list RuntimeCollectionEntry) : Prop :=
  match entries with
  | [] => True
  | RuntimePairEntry _ _ :: rest => pair_entries_only rest
  | RuntimeValueEntry _ :: _ => False
  end.

Fixpoint entry_keys (entries : list RuntimeCollectionEntry) : list ExactKey :=
  match entries with
  | [] => []
  | RuntimeValueEntry value :: rest => value :: entry_keys rest
  | RuntimePairEntry key _ :: rest => key :: entry_keys rest
  end.

Fixpoint keys_nondecreasing (keys : list ExactKey) : Prop :=
  match keys with
  | [] => True
  | key :: rest =>
      (forall later, In later rest -> key <= later) /\
      keys_nondecreasing rest
  end.

Fixpoint keys_strictly_increasing (keys : list ExactKey) : Prop :=
  match keys with
  | [] => True
  | key :: rest =>
      (forall later, In later rest -> key < later) /\
      keys_strictly_increasing rest
  end.

Definition canonical_runtime_collection
    (kind : RuntimeCollectionKind)
    (mode : option RuntimePathMapMode)
  (entries : list RuntimeCollectionEntry) : Prop :=
  match kind with
  | AdmissionList => mode = None /\ value_entries_only entries
  | AdmissionBag =>
      mode = None /\ value_entries_only entries /\
      keys_nondecreasing (entry_keys entries)
  | AdmissionSet =>
      mode = None /\ value_entries_only entries /\
      keys_strictly_increasing (entry_keys entries)
  | AdmissionMap =>
      mode = None /\ pair_entries_only entries /\
      keys_strictly_increasing (entry_keys entries)
  | AdmissionPathMap =>
      match mode with
      | None => False
      | Some RuntimePathMapNeutral => entries = []
      | Some RuntimePathMapSet =>
          value_entries_only entries /\
          keys_strictly_increasing (entry_keys entries)
      | Some RuntimePathMapMap =>
          pair_entries_only entries /\
          keys_strictly_increasing (entry_keys entries)
      end
  end.

Lemma strictly_increasing_keys_are_unique :
  forall keys,
    keys_strictly_increasing keys -> NoDup keys.
Proof.
  induction keys as [|key rest IH]; simpl.
  - constructor.
  - intros [Hless Hrest]. constructor.
    + intro Hin. specialize (Hless key Hin). lia.
    + now apply IH.
Qed.

Theorem canonical_set_has_no_duplicate_values :
  forall entries,
    canonical_runtime_collection AdmissionSet None entries ->
    NoDup (entry_keys entries).
Proof.
  intros entries [_ [_ Hstrict]].
  now apply strictly_increasing_keys_are_unique.
Qed.

Theorem canonical_map_has_no_duplicate_keys :
  forall entries,
    canonical_runtime_collection AdmissionMap None entries ->
    NoDup (entry_keys entries).
Proof.
  intros entries [_ [_ Hstrict]].
  now apply strictly_increasing_keys_are_unique.
Qed.

Theorem canonical_pathmap_has_explicit_mode :
  forall mode entries,
    canonical_runtime_collection AdmissionPathMap mode entries ->
    exists exact_mode, mode = Some exact_mode.
Proof.
  intros [exact_mode|] entries Hcanonical.
  - now exists exact_mode.
  - exact (False_rect _ Hcanonical).
Qed.

Theorem canonical_pathmap_set_has_no_duplicate_keys :
  forall entries,
    canonical_runtime_collection
      AdmissionPathMap (Some RuntimePathMapSet) entries ->
    NoDup (entry_keys entries).
Proof.
  intros entries [_ Hstrict].
  now apply strictly_increasing_keys_are_unique.
Qed.

Theorem canonical_pathmap_map_has_no_duplicate_keys :
  forall entries,
    canonical_runtime_collection
      AdmissionPathMap (Some RuntimePathMapMap) entries ->
    NoDup (entry_keys entries).
Proof.
  intros entries [_ Hstrict].
  now apply strictly_increasing_keys_are_unique.
Qed.

Inductive PhysicalPathMapChild :=
| RuntimeModeMarker (mode : RuntimePathMapMode)
| RuntimePayloadEntry (entry : RuntimeCollectionEntry).

Definition encode_runtime_pathmap
    (mode : RuntimePathMapMode)
    (entries : list RuntimeCollectionEntry) : list PhysicalPathMapChild :=
  RuntimeModeMarker mode :: map RuntimePayloadEntry entries.

Theorem encoded_pathmap_has_one_leading_mode_marker :
  forall mode entries,
    exists payload,
      encode_runtime_pathmap mode entries =
        RuntimeModeMarker mode :: payload /\
      Forall
        (fun child =>
          match child with
          | RuntimeModeMarker _ => False
          | RuntimePayloadEntry _ => True
          end)
        payload.
Proof.
  intros mode entries. exists (map RuntimePayloadEntry entries).
  split; [reflexivity|].
  apply Forall_forall. intros child Hchild.
  apply in_map_iff in Hchild.
  destruct Hchild as [entry [<- _]]. exact I.
Qed.

Theorem empty_pathmap_modes_remain_distinct :
  encode_runtime_pathmap RuntimePathMapNeutral [] <>
    encode_runtime_pathmap RuntimePathMapSet [] /\
  encode_runtime_pathmap RuntimePathMapNeutral [] <>
    encode_runtime_pathmap RuntimePathMapMap [] /\
  encode_runtime_pathmap RuntimePathMapSet [] <>
    encode_runtime_pathmap RuntimePathMapMap [].
Proof.
  repeat split; discriminate.
Qed.

(** Rule terms carry PathMap mode evidence separately from their payload
    entries.  Construction may copy a canonical remainder's marker or use an
    explicit annotation, but it must never infer a mode from entry shape or
    cardinality. *)
Inductive RuntimeModeResolution :=
| RuntimeModeResolved (mode : RuntimePathMapMode)
| RuntimeModeRejected.

Definition resolve_runtime_pathmap_mode
    (declared remainder : option RuntimePathMapMode)
    : RuntimeModeResolution :=
  match declared, remainder with
  | Some expected, Some actual =>
      match expected, actual with
      | RuntimePathMapNeutral, RuntimePathMapNeutral
      | RuntimePathMapSet, RuntimePathMapSet
      | RuntimePathMapMap, RuntimePathMapMap => RuntimeModeResolved expected
      | _, _ => RuntimeModeRejected
      end
  | Some mode, None | None, Some mode => RuntimeModeResolved mode
  | None, None => RuntimeModeRejected
  end.

Theorem resolved_pathmap_mode_has_explicit_evidence :
  forall declared remainder mode,
    resolve_runtime_pathmap_mode declared remainder =
      RuntimeModeResolved mode ->
    declared = Some mode \/ remainder = Some mode.
Proof.
  intros [declared|] [remainder|] mode Hresolved.
  - destruct declared, remainder; simpl in Hresolved;
      try discriminate; inversion Hresolved; subst; auto.
  - simpl in Hresolved. inversion Hresolved. auto.
  - simpl in Hresolved. inversion Hresolved. auto.
  - discriminate.
Qed.

Theorem pathmap_mode_is_not_inferred_without_evidence :
  resolve_runtime_pathmap_mode None None = RuntimeModeRejected.
Proof.
  reflexivity.
Qed.

(** The application-level PathMap mode determines the payload sort and the
    admissible remainder shape.  This contract is separate from the operator
    tag because a PathMap collection operator has one declared pair element
    sort while set-mode entries have the declared key sort. *)
Inductive RuntimePathMapChildContract :=
| RuntimePathMapFixed (sorts : list SortId)
| RuntimePathMapHomogeneous (sort : SortId)
| RuntimePathMapRemainderOnly.

Definition runtime_pathmap_child_contract
    (mode : option RuntimePathMapMode)
    (key_sort pair_sort : SortId) : RuntimePathMapChildContract :=
  match mode with
  | Some RuntimePathMapNeutral => RuntimePathMapFixed []
  | Some RuntimePathMapSet => RuntimePathMapHomogeneous key_sort
  | Some RuntimePathMapMap => RuntimePathMapHomogeneous pair_sort
  | None => RuntimePathMapRemainderOnly
  end.

Theorem neutral_pathmap_accepts_no_payload_children :
  forall key_sort pair_sort,
    runtime_pathmap_child_contract
      (Some RuntimePathMapNeutral) key_sort pair_sort =
      RuntimePathMapFixed [].
Proof. reflexivity. Qed.

Theorem set_pathmap_uses_the_declared_key_sort :
  forall key_sort pair_sort,
    runtime_pathmap_child_contract
      (Some RuntimePathMapSet) key_sort pair_sort =
      RuntimePathMapHomogeneous key_sort.
Proof. reflexivity. Qed.

Theorem map_pathmap_uses_the_declared_pair_sort :
  forall key_sort pair_sort,
    runtime_pathmap_child_contract
      (Some RuntimePathMapMap) key_sort pair_sort =
      RuntimePathMapHomogeneous pair_sort.
Proof. reflexivity. Qed.

Theorem mode_polymorphic_pathmap_is_remainder_only :
  forall key_sort pair_sort,
    runtime_pathmap_child_contract None key_sort pair_sort =
      RuntimePathMapRemainderOnly.
Proof. reflexivity. Qed.

Definition retain_runtime_pathmap_marker
    (mode : RuntimePathMapMode)
    (residual_entries : list RuntimeCollectionEntry)
    : list PhysicalPathMapChild :=
  RuntimeModeMarker mode :: map RuntimePayloadEntry residual_entries.

Theorem pathmap_remainder_retains_exact_mode_marker :
  forall mode residual_entries,
    retain_runtime_pathmap_marker mode residual_entries =
      encode_runtime_pathmap mode residual_entries.
Proof.
  reflexivity.
Qed.

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
Print Assumptions resumed_transition_binds_exact_target.
Print Assumptions resumed_transition_preserves_every_parent_binding.
Print Assumptions child_substitutions_cannot_escape_transition_resume.
Print Assumptions entered_forall_scope_binds_exact_element.
Print Assumptions leaving_forall_scope_restores_exact_outer_substitution.
Print Assumptions internal_row_variable_cannot_capture_declared_variable.
Print Assumptions different_constructor_heads_are_rejected_before_decomposition.
Print Assumptions different_constructor_arities_are_rejected_before_decomposition.
Print Assumptions compatible_constructor_heads_decompose_positionally.
Print Assumptions accepted_ordered_collection_split_is_exact.
Print Assumptions admitted_unordered_collection_branch_is_exact.
Print Assumptions admitted_unordered_row_pairing_partitions_both_sides.
Print Assumptions range_restricted_premise_is_ground_after_conclusion_match.
Print Assumptions substitution_signature_recovers_the_function_domain_and_codomain.
Print Assumptions abstraction_signature_places_the_binder_before_the_body.
Print Assumptions result_only_substitution_signature_is_ambiguous.
Print Assumptions admitted_map_parameters_are_the_exact_source_telescope.
Print Assumptions product_signature_preserves_binary_product_factors.
Print Assumptions virtual_application_matches_singleton_physical_root.
Print Assumptions matching_abstraction_binder_schedules_no_body.
Print Assumptions different_abstraction_binder_schedules_exactly_the_body.
Print Assumptions matching_abstraction_binder_shields_every_body_occurrence.
Print Assumptions different_abstraction_binder_preserves_body_freedom.
Print Assumptions iterative_projection_pushes_only_reachable_nodes.
Print Assumptions invalid_publication_root_has_no_projection.
Print Assumptions unreachable_private_node_has_no_published_identifier.
Print Assumptions every_publication_root_receives_an_identifier.
Print Assumptions projected_children_preserve_order_and_arity.
Print Assumptions strictly_increasing_keys_are_unique.
Print Assumptions canonical_set_has_no_duplicate_values.
Print Assumptions canonical_map_has_no_duplicate_keys.
Print Assumptions canonical_pathmap_has_explicit_mode.
Print Assumptions canonical_pathmap_set_has_no_duplicate_keys.
Print Assumptions canonical_pathmap_map_has_no_duplicate_keys.
Print Assumptions encoded_pathmap_has_one_leading_mode_marker.
Print Assumptions empty_pathmap_modes_remain_distinct.
Print Assumptions resolved_pathmap_mode_has_explicit_evidence.
Print Assumptions pathmap_mode_is_not_inferred_without_evidence.
Print Assumptions neutral_pathmap_accepts_no_payload_children.
Print Assumptions set_pathmap_uses_the_declared_key_sort.
Print Assumptions map_pathmap_uses_the_declared_pair_sort.
Print Assumptions mode_polymorphic_pathmap_is_remainder_only.
Print Assumptions pathmap_remainder_retains_exact_mode_marker.
Print Assumptions compatible_rule_backed_action_has_exact_source_and_target.
Print Assumptions same_sort_rule_backed_action_is_endomorphic.
Print Assumptions uncosted_evidence_cannot_fabricate_a_grade.
Print Assumptions costed_evidence_contains_a_checked_grade.
Print Assumptions bound_receipt_has_profile_valid_resource_evidence.
Print Assumptions output_attenuation_cannot_reject_an_admitted_input.

End SemanticTransitionKernel.
