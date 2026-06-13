(*
 * HostRhoMachineReuse: the Rho backend is accepted only when it delegates the
 * Rho machine responsibilities to F1r3node/Rholang/RSpace and does not install
 * a parallel MeTTaIL-owned reducer, tuple space, matcher, or replay engine.
 *
 * This is a boundary theorem, not a proof of the host implementation.  It
 * formalizes the architectural contract used by the documentation and rollout
 * gate: mettail-rho-* may lower, drive sessions, extract observations, and
 * register explicit native handlers, but the Rho machine itself is the host
 * Rholang interpreter plus host RSpace services.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

Import ListNotations.

Section HostRhoMachineReuse.

  Inductive Component : Type :=
    | HostRholangInterpreter
    | HostRSpace
    | HostReplay
    | BackendLowerer
    | BackendSessionDriver
    | BackendObservationExtractor
    | BackendNativeHandler
    | CustomReducer
    | CustomTupleSpace
    | CustomMatcher
    | CustomReplay.

  Definition Component_eq_dec (a b : Component) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  Definition contains (c : Component) (cs : list Component) : bool :=
    if in_dec Component_eq_dec c cs then true else false.

  Definition is_custom_machine_component (c : Component) : bool :=
    match c with
    | CustomReducer | CustomTupleSpace | CustomMatcher | CustomReplay => true
    | _ => false
    end.

  Definition no_custom_machine (cs : list Component) : Prop :=
    forall c, In c cs -> is_custom_machine_component c = false.

  Record BackendPlan : Type := {
    plan_components : list Component
  }.

  Definition uses_host_rho_machine (p : BackendPlan) : Prop :=
    In HostRholangInterpreter (plan_components p)
    /\ In HostRSpace (plan_components p).

  Definition accepted_backend (p : BackendPlan) : Prop :=
    uses_host_rho_machine p /\ no_custom_machine (plan_components p).

  Lemma contains_true_iff : forall c cs,
    contains c cs = true <-> In c cs.
  Proof.
    intros c cs. unfold contains.
    destruct (in_dec Component_eq_dec c cs) as [Hin | Hnot].
    - split.
      + intro Htrue. exact Hin.
      + intro Hmem. reflexivity.
    - split.
      + intro H. discriminate H.
      + intro Hin. contradiction.
  Qed.

  Theorem accepted_backend_uses_host_interpreter : forall p,
    accepted_backend p -> In HostRholangInterpreter (plan_components p).
  Proof.
    intros p [[Hinterp _] _]. exact Hinterp.
  Qed.

  Theorem accepted_backend_uses_host_rspace : forall p,
    accepted_backend p -> In HostRSpace (plan_components p).
  Proof.
    intros p [[_ Hrspace] _]. exact Hrspace.
  Qed.

  Theorem accepted_backend_excludes_custom_reducer : forall p,
    accepted_backend p -> ~ In CustomReducer (plan_components p).
  Proof.
    intros p [_ Hno] Hin.
    specialize (Hno CustomReducer Hin). simpl in Hno. discriminate Hno.
  Qed.

  Theorem accepted_backend_excludes_custom_tuple_space : forall p,
    accepted_backend p -> ~ In CustomTupleSpace (plan_components p).
  Proof.
    intros p [_ Hno] Hin.
    specialize (Hno CustomTupleSpace Hin). simpl in Hno. discriminate Hno.
  Qed.

  Theorem accepted_backend_excludes_custom_matcher : forall p,
    accepted_backend p -> ~ In CustomMatcher (plan_components p).
  Proof.
    intros p [_ Hno] Hin.
    specialize (Hno CustomMatcher Hin). simpl in Hno. discriminate Hno.
  Qed.

  Theorem accepted_backend_excludes_custom_replay : forall p,
    accepted_backend p -> ~ In CustomReplay (plan_components p).
  Proof.
    intros p [_ Hno] Hin.
    specialize (Hno CustomReplay Hin). simpl in Hno. discriminate Hno.
  Qed.

  Theorem missing_host_interpreter_blocks_acceptance : forall p,
    ~ In HostRholangInterpreter (plan_components p) -> ~ accepted_backend p.
  Proof.
    intros p Hmissing Haccepted.
    apply Hmissing.
    apply accepted_backend_uses_host_interpreter.
    exact Haccepted.
  Qed.

  Theorem missing_host_rspace_blocks_acceptance : forall p,
    ~ In HostRSpace (plan_components p) -> ~ accepted_backend p.
  Proof.
    intros p Hmissing Haccepted.
    apply Hmissing.
    apply accepted_backend_uses_host_rspace.
    exact Haccepted.
  Qed.

  Theorem custom_machine_component_blocks_acceptance : forall p c,
    is_custom_machine_component c = true ->
    In c (plan_components p) ->
    ~ accepted_backend p.
  Proof.
    intros p c Hcustom Hin [_ Hno].
    specialize (Hno c Hin). rewrite Hcustom in Hno. discriminate Hno.
  Qed.

  Example canonical_host_plan_is_accepted :
    accepted_backend
      {| plan_components :=
          [ HostRholangInterpreter;
            HostRSpace;
            HostReplay;
            BackendLowerer;
            BackendSessionDriver;
            BackendObservationExtractor;
            BackendNativeHandler ] |}.
  Proof.
    split.
    - split; simpl; auto.
    - intros c Hin. simpl in Hin.
      destruct Hin as [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | []]]]]]]];
        subst; reflexivity.
  Qed.

  Example lowerer_with_custom_tuple_space_is_rejected :
    ~ accepted_backend
      {| plan_components :=
          [ HostRholangInterpreter;
            BackendLowerer;
            BackendSessionDriver;
            CustomTupleSpace ] |}.
  Proof.
    apply custom_machine_component_blocks_acceptance with (c := CustomTupleSpace).
    - reflexivity.
    - simpl. auto.
  Qed.

End HostRhoMachineReuse.
