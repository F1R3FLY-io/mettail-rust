From Stdlib Require Import List Bool PeanoNat.
From RhoBridge Require Import CommRuleFiring DeBruijnSubstTRS MonikerScopeInstantiation.
Import ListNotations DeBruijnSubstTRS MonikerScopeInstantiation.MonikerScopeInstantiation.

Module CommContinuationReadiness.

Inductive communication (receive send : nat) (argument body : Obj) (rest : list Obj)
    : list Obj -> Prop :=
| communicate : receive = send ->
    communication receive send argument body rest (osubst 0 argument body :: rest).

Definition dispatch (receive send : nat) (argument body : Obj) (rest : list Obj)
    : option (list Obj) :=
  if comm_guard receive send then Some (instantiate 0 argument body :: rest) else None.

Definition old_dispatch (allowed : Obj -> bool) (receive send : nat)
    (argument body : Obj) (rest : list Obj) : option (list Obj) :=
  if allowed body then dispatch receive send argument body rest else None.

Theorem matching_channels_accept_any_continuation : forall channel argument body rest,
  dispatch channel channel argument body rest = Some (osubst 0 argument body :: rest).
Proof.
  intros. unfold dispatch.
  assert (comm_guard channel channel = true) as H by
    (apply comm_guard_iff_channels_agree; reflexivity).
  rewrite H, instantiation_is_debruijn_substitution. reflexivity.
Qed.

Theorem different_channels_do_not_communicate : forall receive send argument body rest,
  receive <> send -> dispatch receive send argument body rest = None.
Proof.
  intros. unfold dispatch. destruct (comm_guard receive send) eqn:G; [|reflexivity].
  apply comm_guard_iff_channels_agree in G. contradiction.
Qed.

Theorem dispatch_corresponds_to_communication : forall receive send argument body rest result,
  dispatch receive send argument body rest = Some result <->
  communication receive send argument body rest result.
Proof.
  intros. split.
  - unfold dispatch. destruct (comm_guard receive send) eqn:G; [|discriminate].
    rewrite instantiation_is_debruijn_substitution. intros H. inversion H; subst.
    constructor. now apply comm_guard_iff_channels_agree.
  - intros H. inversion H; subst. apply matching_channels_accept_any_continuation.
Qed.

Theorem communication_preserves_remainder : forall receive send argument body rest result,
  dispatch receive send argument body rest = Some result ->
  result = osubst 0 argument body :: rest.
Proof.
  intros. apply dispatch_corresponds_to_communication in H. now inversion H.
Qed.

Theorem old_continuation_gate_rejects_a_valid_step :
  forall allowed channel argument body rest,
  allowed body = false ->
  old_dispatch allowed channel channel argument body rest = None /\
  communication channel channel argument body rest (osubst 0 argument body :: rest).
Proof.
  intros. split.
  - unfold old_dispatch. now rewrite H.
  - constructor. reflexivity.
Qed.

Theorem communication_preserves_nested_binding : forall channel rest,
  dispatch channel channel (oBound 0) (oLam (oBound 1)) rest =
    Some (oLam (oBound 1) :: rest).
Proof. intros. rewrite matching_channels_accept_any_continuation. reflexivity. Qed.

End CommContinuationReadiness.

Print Assumptions CommContinuationReadiness.matching_channels_accept_any_continuation.
Print Assumptions CommContinuationReadiness.different_channels_do_not_communicate.
Print Assumptions CommContinuationReadiness.dispatch_corresponds_to_communication.
Print Assumptions CommContinuationReadiness.communication_preserves_remainder.
Print Assumptions CommContinuationReadiness.old_continuation_gate_rejects_a_valid_step.
Print Assumptions CommContinuationReadiness.communication_preserves_nested_binding.
