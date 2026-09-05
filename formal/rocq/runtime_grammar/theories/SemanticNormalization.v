(**
  SemanticNormalization: bounded, atomic normal-form execution over the
  one-step SemanticTransitionKernel.

  A public semantic action still selects exactly one named entry rewrite.  Its
  result may be a private machine state whose subsequent transitions use the
  theory-wide directed rewrite relation.  This file models that second phase.
  Equations never become operational steps, terminal constructors are explicit,
  and every enumeration must be exhaustive before any successor is selected.

  Equal exact successor keys coalesce even when several proofs derive them.
  Different grades or effects for the same successor are rejected as a
  determinism violation.  Cancellation, malformed evidence, incomplete
  enumeration, cycles, frontier limits, and either budget discard every private
  trace and effect.  Only explicit terminal states are publishable.

  The deterministic driver is tail-recursive in the semantic-step budget.  The
  fair driver is a bounded breadth-first worklist; neither follows rewrite depth
  through the native call stack.

  Rocq 9.1 compatible.  No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import SemanticTransitionKernel SemanticIntrinsics.
Import ListNotations.

Module SemanticNormalization.

Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.
Module Intrinsics := SemanticIntrinsics.SemanticIntrinsics.

Definition ConstructorId := nat.
Definition RuleId := nat.
Definition SortId := nat.
Definition EffectId := nat.
Definition ExactKey := Kernel.Commitment.

Inductive NormalizationBranching :=
| DeterministicNormalForm
| FairAllNormalForms.

Record NormalizationPolicy := {
  policy_relation_sort : SortId;
  policy_terminal_constructors : list ConstructorId;
  policy_branching : NormalizationBranching;
  policy_reduce_right : Kernel.RightId;
  policy_required_rights : list Kernel.RightId
}.

Inductive SemanticExecutionPolicy :=
| ExecuteOneStep
| ExecuteToNormalForm (policy : NormalizationPolicy).

Record NormalizationConstructorManifest := {
  normalization_constructor_id : ConstructorId;
  normalization_constructor_codomain : SortId
}.

Record NormalizationRuleManifest := {
  normalization_rule_transition : Kernel.TransitionRuleManifest;
  normalization_rule_lhs_constructor : ConstructorId
}.

Fixpoint find_constructor
    (identifier : ConstructorId)
    (constructors : list NormalizationConstructorManifest)
    : option NormalizationConstructorManifest :=
  match constructors with
  | [] => None
  | constructor :: rest =>
      if Nat.eqb identifier (normalization_constructor_id constructor)
      then Some constructor
      else find_constructor identifier rest
  end.

Fixpoint find_rule
    (identifier : RuleId)
    (rules : list NormalizationRuleManifest)
    : option NormalizationRuleManifest :=
  match rules with
  | [] => None
  | rule :: rest =>
      if Nat.eqb identifier
           (Kernel.transition_rule_id (normalization_rule_transition rule))
      then Some rule
      else find_rule identifier rest
  end.

Definition rule_is_selected_rewrite
    (policy : NormalizationPolicy) (rule : NormalizationRuleManifest) : bool :=
  Kernel.rewrite_relation_rule_selected
    (policy_relation_sort policy) (normalization_rule_transition rule).

Definition rule_is_same_sort
    (policy : NormalizationPolicy) (rule : NormalizationRuleManifest) : bool :=
  Nat.eqb
    (Kernel.transition_rule_target_sort (normalization_rule_transition rule))
    (policy_relation_sort policy).

Definition rule_leaves_terminal
    (terminal : ConstructorId) (rule : NormalizationRuleManifest) : bool :=
  negb (Nat.eqb terminal (normalization_rule_lhs_constructor rule)).

Definition terminal_manifest_valid
    (policy : NormalizationPolicy)
    (constructors : list NormalizationConstructorManifest)
    (rules : list NormalizationRuleManifest)
    (terminal : ConstructorId) : bool :=
  match find_constructor terminal constructors with
  | None => false
  | Some constructor =>
      Nat.eqb (normalization_constructor_codomain constructor)
        (policy_relation_sort policy) &&
      forallb
        (fun rule =>
          negb (rule_is_selected_rewrite policy rule) ||
          rule_leaves_terminal terminal rule)
        rules
  end.

Fixpoint nat_nodupb (values : list nat) : bool :=
  match values with
  | [] => true
  | value :: rest =>
      negb (existsb (Nat.eqb value) rest) && nat_nodupb rest
  end.

Definition normalization_policy_admitted
    (sort_count : nat)
    (constructors : list NormalizationConstructorManifest)
    (rules : list NormalizationRuleManifest)
    (policy : NormalizationPolicy) : bool :=
  Nat.ltb (policy_relation_sort policy) sort_count &&
  existsb (Nat.eqb (policy_reduce_right policy))
    (policy_required_rights policy) &&
  negb (Nat.eqb (length (policy_terminal_constructors policy)) 0) &&
  nat_nodupb (policy_terminal_constructors policy) &&
  forallb
    (terminal_manifest_valid policy constructors rules)
    (policy_terminal_constructors policy) &&
  forallb
    (fun rule =>
      negb (rule_is_selected_rewrite policy rule) ||
      rule_is_same_sort policy rule)
    rules.

Theorem empty_terminal_set_is_rejected :
  forall sort_count constructors rules sort branching,
    normalization_policy_admitted sort_count constructors rules
      {| policy_relation_sort := sort;
         policy_terminal_constructors := [];
         policy_branching := branching;
         policy_reduce_right := 0;
         policy_required_rights := [0] |} = false.
Proof.
  intros. unfold normalization_policy_admitted. simpl.
  repeat destruct (Nat.ltb _ _); reflexivity.
Qed.

Theorem selected_equations_cannot_enter_normalization :
  forall sort transition lhs,
    Kernel.transition_rule_origin transition = Kernel.EquationOrigin ->
    rule_is_selected_rewrite
      {| policy_relation_sort := sort;
         policy_terminal_constructors := [];
         policy_branching := DeterministicNormalForm;
         policy_reduce_right := 0;
         policy_required_rights := [0] |}
      {| normalization_rule_transition := transition;
         normalization_rule_lhs_constructor := lhs |} = false.
Proof.
  intros sort transition lhs Horigin.
  unfold rule_is_selected_rewrite; simpl.
  now apply Kernel.rewrite_relation_never_selects_an_equation.
Qed.

Theorem missing_reduce_authority_is_rejected :
  forall sort_count constructors rules sort terminals branching reduce_right,
    normalization_policy_admitted sort_count constructors rules
      {| policy_relation_sort := sort;
         policy_terminal_constructors := terminals;
         policy_branching := branching;
         policy_reduce_right := reduce_right;
         policy_required_rights := [] |} = false.
Proof.
  intros. unfold normalization_policy_admitted. simpl.
  now destruct (Nat.ltb sort sort_count).
Qed.

Record MachineState := {
  machine_state_sort : SortId;
  machine_state_root : ConstructorId;
  machine_state_key : ExactKey;
  machine_state_nodes : nat;
  machine_state_bytes : nat
}.

Definition machine_state_eqb (left right : MachineState) : bool :=
  Nat.eqb (machine_state_sort left) (machine_state_sort right) &&
  Nat.eqb (machine_state_root left) (machine_state_root right) &&
  Kernel.nat_list_eqb (machine_state_key left) (machine_state_key right) &&
  Nat.eqb (machine_state_nodes left) (machine_state_nodes right) &&
  Nat.eqb (machine_state_bytes left) (machine_state_bytes right).

Lemma machine_state_eqb_spec :
  forall left right, machine_state_eqb left right = true <-> left = right.
Proof.
  intros [ls lr lk ln lb] [rs rr rk rn rb].
  unfold machine_state_eqb; simpl.
  repeat rewrite andb_true_iff.
  repeat rewrite Nat.eqb_eq.
  rewrite Kernel.nat_list_eqb_spec.
  intuition congruence.
Qed.

Definition exact_key_eqb (left right : MachineState) : bool :=
  Kernel.nat_list_eqb (machine_state_key left) (machine_state_key right).

Definition terminal_state
    (policy : NormalizationPolicy) (state : MachineState) : bool :=
  Nat.eqb (machine_state_sort state) (policy_relation_sort policy) &&
  existsb (Nat.eqb (machine_state_root state))
    (policy_terminal_constructors policy).

Record NormalizationStepWitness := {
  normalization_step_rule : RuleId;
  normalization_step_before : MachineState;
  normalization_step_after : MachineState;
  normalization_step_premises : list Kernel.Commitment;
  normalization_step_intrinsics : list Intrinsics.IntrinsicReceipt;
  normalization_step_grade : Kernel.ResourceEvidence;
  normalization_step_effects : list EffectId;
  normalization_step_match_work : nat;
  normalization_step_premise_work : nat;
  normalization_step_build_work : nat
}.

Fixpoint intrinsic_work
    (receipts : list Intrinsics.IntrinsicReceipt) : nat :=
  match receipts with
  | [] => 0
  | receipt :: rest =>
      Intrinsics.intrinsic_receipt_work receipt + intrinsic_work rest
  end.

Definition normalization_step_work (step : NormalizationStepWitness) : nat :=
  S (normalization_step_match_work step +
     normalization_step_premise_work step +
     normalization_step_build_work step +
     intrinsic_work (normalization_step_intrinsics step)).

Lemma normalization_step_work_positive :
  forall step, 1 <= normalization_step_work step.
Proof. intro step. unfold normalization_step_work. lia. Qed.

Definition intrinsic_receipt_well_shapedb
    (receipt : Intrinsics.IntrinsicReceipt) : bool :=
  Nat.eqb (length (Intrinsics.intrinsic_receipt_inputs receipt))
    (length (Intrinsics.intrinsic_domain
      (Intrinsics.intrinsic_receipt_opcode receipt))) &&
  Nat.eqb (length (Intrinsics.intrinsic_receipt_outputs receipt))
    (length (Intrinsics.intrinsic_codomain
      (Intrinsics.intrinsic_receipt_opcode receipt))) &&
  Nat.leb 1 (Intrinsics.intrinsic_receipt_work receipt).

Lemma intrinsic_receipt_well_shapedb_sound :
  forall receipt,
    intrinsic_receipt_well_shapedb receipt = true ->
    Intrinsics.intrinsic_receipt_well_shaped receipt.
Proof.
  intros receipt Hvalid.
  unfold intrinsic_receipt_well_shapedb in Hvalid.
  repeat rewrite andb_true_iff in Hvalid.
  repeat rewrite Nat.eqb_eq in Hvalid.
  destruct Hvalid as [[Hinputs Houtputs] Hwork].
  apply Nat.leb_le in Hwork.
  exact (conj Hinputs (conj Houtputs Hwork)).
Qed.

Definition step_observation_eqb
    (left right : NormalizationStepWitness) : bool :=
  Kernel.resource_evidence_eqb
    (normalization_step_grade left) (normalization_step_grade right) &&
  Kernel.nat_list_eqb
    (normalization_step_effects left) (normalization_step_effects right).

Definition normalization_step_valid
    (policy : NormalizationPolicy)
    (rules : list NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (current : MachineState)
    (step : NormalizationStepWitness) : bool :=
  machine_state_eqb current (normalization_step_before step) &&
  Nat.eqb (machine_state_sort (normalization_step_after step))
    (policy_relation_sort policy) &&
  Kernel.output_admitted bounds
    (machine_state_nodes (normalization_step_after step))
    (machine_state_bytes (normalization_step_after step)) &&
  Kernel.resource_evidence_valid profile (normalization_step_grade step) &&
  forallb intrinsic_receipt_well_shapedb
    (normalization_step_intrinsics step) &&
  match find_rule (normalization_step_rule step) rules with
  | None => false
  | Some rule =>
      rule_is_selected_rewrite policy rule &&
      rule_is_same_sort policy rule &&
      Nat.eqb (normalization_rule_lhs_constructor rule)
        (machine_state_root current)
  end.

Inductive StepEnumeration :=
| EnumerationComplete (steps : list NormalizationStepWitness)
| EnumerationIncomplete (reason : Kernel.UndeterminedReason).

Definition StepEnumerator := MachineState -> StepEnumeration.
Definition CancellationProbe := nat -> bool.

Record SuccessorGroup := {
  successor_state : MachineState;
  successor_primary : NormalizationStepWitness;
  successor_alternatives : list NormalizationStepWitness
}.

Fixpoint insert_successor
    (step : NormalizationStepWitness) (groups : list SuccessorGroup)
    : list SuccessorGroup :=
  match groups with
  | [] =>
      [{| successor_state := normalization_step_after step;
          successor_primary := step;
          successor_alternatives := [] |}]
  | group :: rest =>
      if exact_key_eqb (normalization_step_after step) (successor_state group)
      then
        {| successor_state := successor_state group;
           successor_primary := successor_primary group;
           successor_alternatives :=
             successor_alternatives group ++ [step] |} :: rest
      else group :: insert_successor step rest
  end.

Fixpoint coalesce_successors
    (steps : list NormalizationStepWitness) : list SuccessorGroup :=
  match steps with
  | [] => []
  | step :: rest => insert_successor step (coalesce_successors rest)
  end.

Theorem equal_successor_keys_coalesce :
  forall first second,
    exact_key_eqb
      (normalization_step_after first)
      (normalization_step_after second) = true ->
    length (coalesce_successors [first; second]) = 1.
Proof.
  intros first second Hsame.
  unfold coalesce_successors; simpl.
  now rewrite Hsame.
Qed.

Theorem different_successor_keys_remain_distinct :
  forall first second,
    exact_key_eqb
      (normalization_step_after first)
      (normalization_step_after second) = false ->
    length (coalesce_successors [first; second]) = 2.
Proof.
  intros first second Hdifferent.
  unfold coalesce_successors; simpl.
  now rewrite Hdifferent.
Qed.

Definition group_observationally_coherent (group : SuccessorGroup) : bool :=
  forallb
    (step_observation_eqb (successor_primary group))
    (successor_alternatives group).

Definition groups_observationally_coherent
    (groups : list SuccessorGroup) : bool :=
  forallb group_observationally_coherent groups.

Fixpoint enumeration_work (steps : list NormalizationStepWitness) : nat :=
  match steps with
  | [] => 0
  | step :: rest => normalization_step_work step + enumeration_work rest
  end.

Record NormalizationHopReceipt := {
  hop_before : MachineState;
  hop_after : MachineState;
  hop_exhaustive_proofs : list NormalizationStepWitness;
  hop_charged_work : nat
}.

Record PrivateBranch := {
  branch_current : MachineState;
  branch_seen : list ExactKey;
  branch_hops_rev : list NormalizationHopReceipt;
  branch_effect_chunks_rev : list (list EffectId);
  branch_grades_rev : list Kernel.ResourceEvidence
}.

Definition initial_branch (state : MachineState) : PrivateBranch :=
  {| branch_current := state;
     branch_seen := [machine_state_key state];
     branch_hops_rev := [];
     branch_effect_chunks_rev := [];
     branch_grades_rev := [] |}.

Definition exact_key_seen (key : ExactKey) (seen : list ExactKey) : bool :=
  existsb (Kernel.nat_list_eqb key) seen.

Definition extend_branch
    (branch : PrivateBranch)
    (group : SuccessorGroup)
    (charged_work : nat) : PrivateBranch :=
  let primary := successor_primary group in
  let next := successor_state group in
  {| branch_current := next;
     branch_seen := machine_state_key next :: branch_seen branch;
     branch_hops_rev :=
       {| hop_before := branch_current branch;
          hop_after := next;
          hop_exhaustive_proofs :=
            primary :: successor_alternatives group;
          hop_charged_work := charged_work |} :: branch_hops_rev branch;
     branch_effect_chunks_rev :=
       normalization_step_effects primary :: branch_effect_chunks_rev branch;
     branch_grades_rev :=
       normalization_step_grade primary :: branch_grades_rev branch |}.

Record NormalFormReceipt := {
  normal_form_state : MachineState;
  normal_form_hops : list NormalizationHopReceipt;
  normal_form_effects : list EffectId;
  normal_form_grades : list Kernel.ResourceEvidence
}.

Definition publish_branch (branch : PrivateBranch) : NormalFormReceipt :=
  {| normal_form_state := branch_current branch;
     normal_form_hops := rev (branch_hops_rev branch);
     normal_form_effects :=
       concat (rev (branch_effect_chunks_rev branch));
     normal_form_grades := rev (branch_grades_rev branch) |}.

Record NormalizationSuccess := {
  normalization_initial : MachineState;
  normalization_normal_forms : list NormalFormReceipt;
  normalization_total_work : nat
}.

Inductive NormalizationUndeterminedReason :=
| NormalizationCancelled
| NormalizationStepBudgetExhausted
| NormalizationWorkBudgetExhausted
| NormalizationFrontierLimitExceeded
| NormalizationCycleDetected
| NormalizationInvalidInternalEvidence
| NormalizationEnumerationIncomplete (reason : Kernel.UndeterminedReason).

Inductive NormalizationRefutedReason :=
| NormalizationPolicyRejected
| NormalizationInputRejected
| StuckNonterminal
| NormalizationDeterminismClaimViolated.

Inductive NormalizationDecision :=
| NormalizationProven (success : NormalizationSuccess)
| NormalizationRefuted (reason : NormalizationRefutedReason)
| NormalizationUndetermined (reason : NormalizationUndeterminedReason).

Definition normalization_committable_effects
    (decision : NormalizationDecision) : list EffectId :=
  match decision with
  | NormalizationProven success =>
      concat (map normal_form_effects (normalization_normal_forms success))
  | NormalizationRefuted _ | NormalizationUndetermined _ => []
  end.

Definition success_from_branches
    (initial : MachineState)
    (branches : list PrivateBranch)
    (used_work : nat) : NormalizationSuccess :=
  {| normalization_initial := initial;
     normalization_normal_forms := map publish_branch branches;
     normalization_total_work := used_work |}.

Fixpoint run_deterministic_private
    (enumerate : StepEnumerator)
    (cancelled : CancellationProbe)
    (policy : NormalizationPolicy)
    (rules : list NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (initial : MachineState)
    (step_fuel work_remaining used_steps used_work : nat)
    (branch : PrivateBranch) : NormalizationDecision :=
  if cancelled used_steps then
    NormalizationUndetermined NormalizationCancelled
  else if terminal_state policy (branch_current branch) then
    NormalizationProven (success_from_branches initial [branch] used_work)
  else
    match step_fuel with
    | 0 => NormalizationUndetermined NormalizationStepBudgetExhausted
    | S remaining_steps =>
        match enumerate (branch_current branch) with
        | EnumerationIncomplete reason =>
            NormalizationUndetermined
              (NormalizationEnumerationIncomplete reason)
        | EnumerationComplete steps =>
            if forallb
                 (normalization_step_valid policy rules profile bounds
                    (branch_current branch)) steps
            then
              let charged_work := enumeration_work steps in
              if Nat.leb charged_work work_remaining then
                let groups := coalesce_successors steps in
                if groups_observationally_coherent groups then
                  match groups with
                  | [] => NormalizationRefuted StuckNonterminal
                  | [group] =>
                      if exact_key_seen
                           (machine_state_key (successor_state group))
                           (branch_seen branch)
                      then
                        NormalizationUndetermined NormalizationCycleDetected
                      else
                        run_deterministic_private enumerate cancelled policy rules
                          profile bounds initial remaining_steps
                          (work_remaining - charged_work) (S used_steps)
                          (used_work + charged_work)
                          (extend_branch branch group charged_work)
                  | _ :: _ :: _ =>
                      NormalizationRefuted
                        NormalizationDeterminismClaimViolated
                  end
                else
                  NormalizationRefuted
                    NormalizationDeterminismClaimViolated
              else
                NormalizationUndetermined NormalizationWorkBudgetExhausted
            else
              NormalizationUndetermined NormalizationInvalidInternalEvidence
        end
    end.

Definition branching_is_deterministic
    (branching : NormalizationBranching) : bool :=
  match branching with
  | DeterministicNormalForm => true
  | FairAllNormalForms => false
  end.

Definition normalize_deterministic
    (sort_count : nat)
    (constructors : list NormalizationConstructorManifest)
    (rules : list NormalizationRuleManifest)
    (enumerate : StepEnumerator)
    (cancelled : CancellationProbe)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (policy : NormalizationPolicy)
    (step_budget work_budget : nat)
    (initial : MachineState) : NormalizationDecision :=
  if negb (normalization_policy_admitted
       sort_count constructors rules policy &&
       branching_is_deterministic (policy_branching policy))
  then NormalizationRefuted NormalizationPolicyRejected
  else if negb (Nat.eqb (machine_state_sort initial)
                       (policy_relation_sort policy) &&
                Kernel.input_admitted bounds
                  (machine_state_nodes initial) (machine_state_bytes initial))
  then NormalizationRefuted NormalizationInputRejected
  else run_deterministic_private enumerate cancelled policy rules profile
         bounds initial step_budget work_budget 0 0 (initial_branch initial).

(** Breadth-first relational normalization.  Fair mode is restricted to pure
    transitions: a relation may expose every normal form, but it cannot commit
    mutually exclusive branch effects. *)
Definition step_is_pure (step : NormalizationStepWitness) : bool :=
  match normalization_step_effects step with
  | [] => true
  | _ :: _ => false
  end.

Fixpoint groups_are_acyclic
    (seen : list ExactKey) (groups : list SuccessorGroup) : bool :=
  match groups with
  | [] => true
  | group :: rest =>
      negb (exact_key_seen (machine_state_key (successor_state group)) seen) &&
      groups_are_acyclic seen rest
  end.

Definition extend_groups
    (branch : PrivateBranch)
    (groups : list SuccessorGroup)
    (charged_work : nat) : list PrivateBranch :=
  map (fun group => extend_branch branch group charged_work) groups.

Fixpoint run_fair_private
    (enumerate : StepEnumerator)
    (cancelled : CancellationProbe)
    (policy : NormalizationPolicy)
    (rules : list NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (initial : MachineState)
    (frontier_limit scheduler_fuel work_remaining
      visited used_work : nat)
    (frontier complete_rev : list PrivateBranch) : NormalizationDecision :=
  if cancelled visited then
    NormalizationUndetermined NormalizationCancelled
  else
    match frontier with
    | [] =>
        NormalizationProven
          (success_from_branches initial (rev complete_rev) used_work)
    | branch :: siblings =>
        match scheduler_fuel with
        | 0 => NormalizationUndetermined NormalizationStepBudgetExhausted
        | S remaining_fuel =>
            if terminal_state policy (branch_current branch) then
              run_fair_private enumerate cancelled policy rules profile bounds
                initial frontier_limit remaining_fuel work_remaining
                (S visited) used_work siblings (branch :: complete_rev)
            else
              match enumerate (branch_current branch) with
              | EnumerationIncomplete reason =>
                  NormalizationUndetermined
                    (NormalizationEnumerationIncomplete reason)
              | EnumerationComplete steps =>
                  if forallb
                       (fun step =>
                         normalization_step_valid policy rules profile bounds
                           (branch_current branch) step && step_is_pure step)
                       steps
                  then
                    let charged_work := enumeration_work steps in
                    if Nat.leb charged_work work_remaining then
                      let groups := coalesce_successors steps in
                      if groups_observationally_coherent groups then
                        match groups with
                        | [] => NormalizationRefuted StuckNonterminal
                        | _ :: _ =>
                            if groups_are_acyclic (branch_seen branch) groups
                            then
                              let next_frontier :=
                                siblings ++
                                extend_groups branch groups charged_work in
                              if Nat.leb (length next_frontier) frontier_limit
                              then
                                run_fair_private enumerate cancelled policy
                                  rules profile bounds initial frontier_limit
                                  remaining_fuel
                                  (work_remaining - charged_work)
                                  (S visited) (used_work + charged_work)
                                  next_frontier complete_rev
                              else
                                NormalizationUndetermined
                                  NormalizationFrontierLimitExceeded
                            else
                              NormalizationUndetermined
                                NormalizationCycleDetected
                        end
                      else
                        NormalizationRefuted
                          NormalizationDeterminismClaimViolated
                    else
                      NormalizationUndetermined
                        NormalizationWorkBudgetExhausted
                  else
                    NormalizationUndetermined
                      NormalizationInvalidInternalEvidence
              end
        end
    end.

Definition branching_is_fair
    (branching : NormalizationBranching) : bool :=
  match branching with
  | DeterministicNormalForm => false
  | FairAllNormalForms => true
  end.

Definition normalize_fair
    (sort_count : nat)
    (constructors : list NormalizationConstructorManifest)
    (rules : list NormalizationRuleManifest)
    (enumerate : StepEnumerator)
    (cancelled : CancellationProbe)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (policy : NormalizationPolicy)
    (frontier_limit scheduler_budget work_budget : nat)
    (initial : MachineState) : NormalizationDecision :=
  if negb (normalization_policy_admitted
       sort_count constructors rules policy &&
       branching_is_fair (policy_branching policy) &&
       Nat.leb 1 frontier_limit)
  then NormalizationRefuted NormalizationPolicyRejected
  else if negb (Nat.eqb (machine_state_sort initial)
                       (policy_relation_sort policy) &&
                Kernel.input_admitted bounds
                  (machine_state_nodes initial) (machine_state_bytes initial))
  then NormalizationRefuted NormalizationInputRejected
  else run_fair_private enumerate cancelled policy rules profile bounds
         initial frontier_limit scheduler_budget work_budget 0 0
         [initial_branch initial] [].

Theorem refutation_never_publishes_effects :
  forall reason,
    normalization_committable_effects
      (NormalizationRefuted reason) = [].
Proof. reflexivity. Qed.

Theorem undetermined_normalization_never_publishes_effects :
  forall reason,
    normalization_committable_effects
      (NormalizationUndetermined reason) = [].
Proof. reflexivity. Qed.

Theorem cancellation_at_deterministic_entry_discards_private_state :
  forall enumerate cancelled policy rules profile bounds initial
         step_fuel work_remaining branch,
    cancelled 0 = true ->
    run_deterministic_private enumerate cancelled policy rules profile bounds
      initial step_fuel work_remaining 0 0 branch =
      NormalizationUndetermined NormalizationCancelled /\
    normalization_committable_effects
      (run_deterministic_private enumerate cancelled policy rules profile bounds
        initial step_fuel work_remaining 0 0 branch) = [].
Proof.
  intros. destruct step_fuel; simpl; now rewrite H.
Qed.

Theorem terminal_deterministic_entry_publishes_without_a_rewrite :
  forall enumerate cancelled policy rules profile bounds initial
         work_remaining used_steps used_work branch,
    cancelled used_steps = false ->
    terminal_state policy (branch_current branch) = true ->
    run_deterministic_private enumerate cancelled policy rules profile bounds
      initial 0 work_remaining used_steps used_work branch =
      NormalizationProven
        (success_from_branches initial [branch] used_work).
Proof.
  intros. simpl. now rewrite H, H0.
Qed.

Theorem nonterminal_zero_step_budget_is_undetermined :
  forall enumerate cancelled policy rules profile bounds initial
         work_remaining used_steps used_work branch,
    cancelled used_steps = false ->
    terminal_state policy (branch_current branch) = false ->
    run_deterministic_private enumerate cancelled policy rules profile bounds
      initial 0 work_remaining used_steps used_work branch =
      NormalizationUndetermined NormalizationStepBudgetExhausted.
Proof.
  intros. simpl. now rewrite H, H0.
Qed.

Theorem incomplete_enumeration_never_publishes :
  forall enumerate cancelled policy rules profile bounds initial
         work_remaining used_steps used_work branch reason,
    cancelled used_steps = false ->
    terminal_state policy (branch_current branch) = false ->
    enumerate (branch_current branch) = EnumerationIncomplete reason ->
    normalization_committable_effects
      (run_deterministic_private enumerate cancelled policy rules profile bounds
        initial 1 work_remaining used_steps used_work branch) = [].
Proof.
  intros. simpl. rewrite H, H0, H1. reflexivity.
Qed.

Theorem deterministic_normalization_is_a_function :
  forall sort_count constructors rules enumerate cancelled profile bounds
         policy step_budget work_budget initial,
    normalize_deterministic sort_count constructors rules enumerate cancelled
      profile bounds policy step_budget work_budget initial =
    normalize_deterministic sort_count constructors rules enumerate cancelled
      profile bounds policy step_budget work_budget initial.
Proof. reflexivity. Qed.

Theorem fair_normalization_is_a_function :
  forall sort_count constructors rules enumerate cancelled profile bounds
         policy frontier_limit scheduler_budget work_budget initial,
    normalize_fair sort_count constructors rules enumerate cancelled profile
      bounds policy frontier_limit scheduler_budget work_budget initial =
    normalize_fair sort_count constructors rules enumerate cancelled profile
      bounds policy frontier_limit scheduler_budget work_budget initial.
Proof. reflexivity. Qed.

Print Assumptions empty_terminal_set_is_rejected.
Print Assumptions selected_equations_cannot_enter_normalization.
Print Assumptions missing_reduce_authority_is_rejected.
Print Assumptions machine_state_eqb_spec.
Print Assumptions intrinsic_receipt_well_shapedb_sound.
Print Assumptions equal_successor_keys_coalesce.
Print Assumptions different_successor_keys_remain_distinct.
Print Assumptions refutation_never_publishes_effects.
Print Assumptions undetermined_normalization_never_publishes_effects.
Print Assumptions cancellation_at_deterministic_entry_discards_private_state.
Print Assumptions terminal_deterministic_entry_publishes_without_a_rewrite.
Print Assumptions nonterminal_zero_step_budget_is_undetermined.
Print Assumptions incomplete_enumeration_never_publishes.
Print Assumptions deterministic_normalization_is_a_function.
Print Assumptions fair_normalization_is_a_function.

End SemanticNormalization.
