(**
  DataFreeObservationPolicy: a rewrite relation alone cannot determine the
  successful terminal observations of a language.

  The counterexample uses the production normalization model's admitted
  terminal policy, not an alternative evaluator. The two policies share the
  same constructors, directed rules, relation sort, and source state. They
  differ only in which irreducible constructor is publishable. Thus a
  data-free service must obtain terminal evidence from an explicit checked
  query, such as an authored Boolean projection, rather than infer success
  from the absence of a rewrite successor.

  No axioms or admitted results.
*)

From Stdlib Require Import List Bool.
From RuntimeGrammar Require Import SemanticNormalization.
Import ListNotations.

Module DataFreeObservationPolicy.

Module N := SemanticNormalization.SemanticNormalization.

Definition constructors : list N.NormalizationConstructorManifest :=
  [{| N.normalization_constructor_id := 1;
      N.normalization_constructor_codomain := 0 |};
   {| N.normalization_constructor_id := 2;
      N.normalization_constructor_codomain := 0 |}].

Definition accepts_one : N.NormalizationPolicy :=
  {| N.policy_relation_sort := 0;
     N.policy_terminal_constructors := [1];
     N.policy_branching := N.FairAllNormalForms;
     N.policy_reduce_right := 0;
     N.policy_required_rights := [0] |}.

Definition accepts_two : N.NormalizationPolicy :=
  {| N.policy_relation_sort := 0;
     N.policy_terminal_constructors := [2];
     N.policy_branching := N.FairAllNormalForms;
     N.policy_reduce_right := 0;
     N.policy_required_rights := [0] |}.

Definition answer_one : N.MachineState :=
  {| N.machine_state_sort := 0;
     N.machine_state_root := 1;
     N.machine_state_key := [17];
     N.machine_state_nodes := 1;
     N.machine_state_bytes := 1 |}.

Theorem same_relation_different_admitted_terminal_answers :
  N.normalization_policy_admitted 1 constructors [] accepts_one = true /\
  N.normalization_policy_admitted 1 constructors [] accepts_two = true /\
  N.terminal_state accepts_one answer_one = true /\
  N.terminal_state accepts_two answer_one = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A complete typed terminal projection must agree on sort and the entire
    terminal roster. No-match can then reject a candidate only after complete
    projection enumeration; this equation alone does not prove completeness. *)
Definition projection_accepts
    (sort : N.SortId) (roots : list N.ConstructorId)
    (state : N.MachineState) : bool :=
  Nat.eqb (N.machine_state_sort state) sort &&
  existsb (Nat.eqb (N.machine_state_root state)) roots.

Theorem exact_projection_roster_preserves_terminal_membership :
  forall policy state roots,
    roots = N.policy_terminal_constructors policy ->
    projection_accepts (N.policy_relation_sort policy) roots state =
      N.terminal_state policy state.
Proof.
  intros policy state roots Hroots.
  subst roots.
  reflexivity.
Qed.

(** The authored query is in a distinct guest sort. Its source rewrite roster
    is [accepted_roots]; a successful rule produces the terminal-query Yes
    constructor. The host Boolean projection examines that exact query sort
    and constructor, never the carrier of the original result category. *)
Definition terminal_query_yes : N.MachineState :=
  {| N.machine_state_sort := 1;
     N.machine_state_root := 9;
     N.machine_state_key := [9];
     N.machine_state_nodes := 1;
     N.machine_state_bytes := 1 |}.

Definition authored_judgment
    (input_sort : N.SortId) (accepted_roots : list N.ConstructorId)
    (state : N.MachineState) : option N.MachineState :=
  if Nat.eqb (N.machine_state_sort state) input_sort &&
     existsb (Nat.eqb (N.machine_state_root state)) accepted_roots
  then Some terminal_query_yes
  else None.

Definition project_terminal_query (query : N.MachineState) : bool :=
  Nat.eqb (N.machine_state_sort query) 1 &&
  Nat.eqb (N.machine_state_root query) 9.

Theorem authored_two_stage_query_refines_terminal_policy :
  forall policy state accepted_roots,
    accepted_roots = N.policy_terminal_constructors policy ->
    match authored_judgment (N.policy_relation_sort policy) accepted_roots state with
    | Some query => project_terminal_query query
    | None => false
    end = N.terminal_state policy state.
Proof.
  intros policy state accepted_roots Hroots.
  subst accepted_roots.
  unfold authored_judgment, project_terminal_query, N.terminal_state.
  destruct (Nat.eqb (N.machine_state_sort state) (N.policy_relation_sort policy) &&
            existsb (Nat.eqb (N.machine_state_root state))
              (N.policy_terminal_constructors policy)); reflexivity.
Qed.

Theorem authored_query_result_is_sort_separated :
  forall sort roots state query,
    authored_judgment sort roots state = Some query ->
    N.machine_state_sort query = 1 /\ N.machine_state_root query = 9.
Proof.
  intros sort roots state query Hresult.
  unfold authored_judgment in Hresult.
  destruct (Nat.eqb (N.machine_state_sort state) sort &&
            existsb (Nat.eqb (N.machine_state_root state)) roots);
    inversion Hresult; auto.
Qed.

Print Assumptions same_relation_different_admitted_terminal_answers.
Print Assumptions exact_projection_roster_preserves_terminal_membership.
Print Assumptions authored_two_stage_query_refines_terminal_policy.
Print Assumptions authored_query_result_is_sort_separated.

End DataFreeObservationPolicy.
