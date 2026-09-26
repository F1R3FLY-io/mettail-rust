(** Separate retained source role from runtime variable authority.

    Macro CategoryRole::Data/SpannedData forbids implicit native, collection,
    variable and binder-name synthesis; Object uses the original passes.
    DDL TypeDecl has NO Data/SpannedData source role. Its admits_variables field
    controls variable authority independently of native/collection declaration.
    The DDL producer therefore explicitly retains Known false for source data
    role, not a guess based on carrier, token patterns, or variable permission.

    Rust adds one required SourceObservation<bool> to retained declarations.
    Unavailable is refusal, not false. Existing checked category bindings supply
    runtime authority separately. These are source/adapter obligations, not new
    literal synthesis or permission to invent missing source metadata.

    The only shared synthesis gate extended below is Variables. The original
    bodies, phase order and callback schedule remain unchanged. Arbitrary Result
    includes full payload, state, trace and failure. The finite schedule law is
    a gate-substitution law, not another synthesis/recognition algorithm.
    FIRST's three variable-only predicates use the new authority observation;
    its macro default calls the original role observer exactly once, at the same
    short-circuit site. Owned callers read actual Core authority instead.
    No runtime parser completeness, native evaluation or binder admission claim.
*)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module SourceRoleVariableAuthority.

Record Observation := {
  data_role : option bool;
  admits_variables : bool
}.

Definition checked_pair (observation : Observation) : option (bool * bool) :=
  match data_role observation with
  | None => None
  | Some role => Some (role, admits_variables observation)
  end.
Definition macro_observation (role : bool) : Observation :=
  {| data_role := Some role; admits_variables := negb role |}.
Definition ddl_observation (authority : bool) : Observation :=
  {| data_role := Some false; admits_variables := authority |}.

Theorem missing_role_is_never_inferred : forall authority,
  checked_pair {| data_role := None; admits_variables := authority |} = None.
Proof. reflexivity. Qed.
Theorem macro_retains_both_original_observations : forall role,
  checked_pair (macro_observation role) = Some (role, negb role).
Proof. reflexivity. Qed.
Theorem ddl_role_is_independent_of_authority : forall authority,
  checked_pair (ddl_observation authority) = Some (false, authority).
Proof. reflexivity. Qed.

(** HeaderCounts already prepays shallow category observations through the
    checked aggregate W debit before constructing the retained header. The new
    role boolean increases that roster charge from three to four per category.
    No new name root or vector element is created by this scalar field. *)
Definition header_observation_work (categories : nat) := 4 * categories.
Theorem role_observation_is_charged_for_every_category : forall categories,
  header_observation_work categories = 3 * categories + categories.
Proof. intros; unfold header_observation_work; lia. Qed.
Definition admitted_header {Header : Type} (categories : nat)
    (original_debit : nat -> bool) (construct : unit -> Header) :=
  if original_debit (header_observation_work categories)
  then Some (construct tt) else None.
Theorem failed_original_debit_precedes_header_construction :
  forall Header categories debit (construct : unit -> Header),
  debit (header_observation_work categories) = false ->
  admitted_header categories debit construct = None.
Proof. intros; unfold admitted_header; now rewrite H. Qed.
Theorem admitted_observation_charge_reuses_same_header_builder :
  forall Header categories debit (construct : unit -> Header),
  debit (header_observation_work categories) = true ->
  admitted_header categories debit construct = Some (construct tt).
Proof. intros; unfold admitted_header; now rewrite H. Qed.

Inductive Phase := Native | Collections | Variables | BinderNames.
Definition original_eligible (role : bool) := negb role.
Definition observed_eligible (role authority : bool) (phase : Phase) :=
  match phase with
  | Variables => if role then false else authority
  | _ => negb role
  end.

Theorem macro_all_phase_gates_are_original : forall role phase,
  observed_eligible role (negb role) phase = original_eligible role.
Proof. intros [] []; reflexivity. Qed.
Theorem native_gate_does_not_read_variable_authority : forall role authority,
  observed_eligible role authority Native = original_eligible role.
Proof. reflexivity. Qed.
Theorem closed_ddl_native_is_not_a_data_category :
  observed_eligible false false Native = true /\
  observed_eligible false false Variables = false.
Proof. split; reflexivity. Qed.
Theorem source_data_never_synthesizes_even_with_authority : forall phase,
  observed_eligible true true phase = false.
Proof. intros []; reflexivity. Qed.

Section GateSubstitution.
Context {State Result : Type}.
Variable original_body skip_body : Phase -> State -> Result.
Definition original_gate role phase state :=
  if original_eligible role then original_body phase state else skip_body phase state.
Definition observed_gate role authority phase state :=
  if observed_eligible role authority phase
  then original_body phase state else skip_body phase state.

Theorem macro_gate_preserves_complete_result : forall role phase state,
  observed_gate role (negb role) phase state = original_gate role phase state.
Proof. intros; unfold observed_gate, original_gate;
  now rewrite macro_all_phase_gates_are_original. Qed.
Theorem closed_ddl_reuses_original_native_body : forall state,
  observed_gate false false Native state = original_body Native state.
Proof. reflexivity. Qed.
Theorem closed_ddl_skips_original_variable_body : forall state,
  observed_gate false false Variables state = skip_body Variables state.
Proof. reflexivity. Qed.

(** A caller-supplied continuation consumes the ENTIRE prior result, including
    trace/failure/state if observable. No callback is replayed or assumed pure. *)
Fixpoint schedule (gate : Phase -> State -> Result)
    (resume : Result -> State) (phases : list Phase) state : list Result :=
  match phases with
  | [] => []
  | phase :: rest =>
      let result := gate phase state in result :: schedule gate resume rest (resume result)
  end.
Theorem macro_schedule_preserves_every_result_and_order : forall phases role resume state,
  schedule (observed_gate role (negb role)) resume phases state =
  schedule (original_gate role) resume phases state.
Proof.
  induction phases as [|phase rest IH]; intros; simpl; [reflexivity|].
  rewrite macro_gate_preserves_complete_result, IH; reflexivity.
Qed.
End GateSubstitution.

Section FirstObservation.
Context {State Error Trace : Type}.
Variable role_query : State -> ((bool + Error) * State * list Trace).
Definition default_authority state :=
  let '(answer, after, trace) := role_query state in
  (match answer with inl role => inl (negb role) | inr error => inr error end,
   after, trace).
Definition original_home_var (user_var : bool) state :=
  if user_var then (inl true, state, []) else
  let '(answer, after, trace) := role_query state in
  (match answer with inl role => inl (negb role) | inr error => inr error end,
   after, trace).
Definition observed_home_var (user_var : bool) state :=
  if user_var then (inl true, state, []) else default_authority state.
Theorem first_default_preserves_observer_state_trace_and_error : forall user_var state,
  observed_home_var user_var state = original_home_var user_var state.
Proof. intros []; reflexivity. Qed.
Theorem authored_var_short_circuit_does_not_query_role : forall state,
  observed_home_var true state = (inl true, state, []).
Proof. reflexivity. Qed.
Theorem default_observer_is_called_once : forall state answer after trace,
  role_query state = (answer, after, trace) ->
  default_authority state =
    (match answer with inl role => inl (negb role) | inr error => inr error end,
     after, trace).
Proof. intros; unfold default_authority; now rewrite H. Qed.
End FirstObservation.

Print Assumptions missing_role_is_never_inferred.
Print Assumptions macro_retains_both_original_observations.
Print Assumptions ddl_role_is_independent_of_authority.
Print Assumptions role_observation_is_charged_for_every_category.
Print Assumptions failed_original_debit_precedes_header_construction.
Print Assumptions admitted_observation_charge_reuses_same_header_builder.
Print Assumptions macro_all_phase_gates_are_original.
Print Assumptions native_gate_does_not_read_variable_authority.
Print Assumptions closed_ddl_native_is_not_a_data_category.
Print Assumptions source_data_never_synthesizes_even_with_authority.
Print Assumptions macro_gate_preserves_complete_result.
Print Assumptions closed_ddl_reuses_original_native_body.
Print Assumptions closed_ddl_skips_original_variable_body.
Print Assumptions macro_schedule_preserves_every_result_and_order.
Print Assumptions first_default_preserves_observer_state_trace_and_error.
Print Assumptions authored_var_short_circuit_does_not_query_role.
Print Assumptions default_observer_is_called_once.
End SourceRoleVariableAuthority.
