(**
  HostCostV2Authority: origin separation for the RestingComm event epoch.

  This is a small admission model, not a proof of the RSpace event codec or
  Cost(G) settlement. [Adopted] represents a policy token obtained from the
  approved-genesis path, and [LocalHost] with [trusted_node = true] represents
  the node's standalone evaluator. Neither token is derived from a Rholang term
  or request payload. A local capability carries a different constructor and
  cannot authorize a consensus root or replay. Neither path meters host work
  (DR-131 extension to F1R3Lang, user decision 1 of 2026-10-16).

  The implementation must preserve this discriminant across runtime creation,
  sandbox creation, block application, and replay. In particular, a numeric
  equality between a local node ID and a consensus root is not authority.
*)

From Stdlib Require Import Bool PeanoNat.

Module HostCostV2Authority.

Inductive Epoch := Legacy | CostV1 | CostV2.

Definition epoch_is_cost_v2 (epoch : Epoch) : bool :=
  match epoch with CostV2 => true | _ => false end.

Record Adopted := {
  adopted_approved : bool;
  adopted_epoch : Epoch;
  adopted_root : nat
}.

Inductive HostContext :=
| ConsensusHost (policy : Adopted)
| LocalHost (trusted_node : bool) (node_id : nat).

Inductive ExecutionSpace :=
| ConsensusSpace (root : nat)
| LocalSpace (node_id : nat).

Inductive Operation := Live | Replay.

(** The selected epoch is tested at the host boundary, not inferred from
    source syntax, a selected grade, or an event payload. *)
Definition admit_cost_v2 (context : HostContext) (space : ExecutionSpace)
    (operation : Operation) : bool :=
  match context, space with
  | ConsensusHost policy, ConsensusSpace root =>
      adopted_approved policy &&
      epoch_is_cost_v2 (adopted_epoch policy) &&
      Nat.eqb (adopted_root policy) root
  | LocalHost trusted node, LocalSpace selected_node =>
      match operation with
      | Live => trusted && Nat.eqb node selected_node
      | Replay => false
      end
  | _, _ => false
  end.

Theorem admitted_consensus_has_approved_exact_policy :
  forall context root operation,
    admit_cost_v2 context (ConsensusSpace root) operation = true ->
    exists policy,
      context = ConsensusHost policy /\
      adopted_approved policy = true /\
      adopted_epoch policy = CostV2 /\
      adopted_root policy = root.
Proof.
  intros context root operation Hadmit.
  destruct context as [policy|trusted node]; simpl in Hadmit;
    try discriminate.
  destruct (adopted_approved policy) eqn:Happroved;
    destruct (adopted_epoch policy) eqn:Hepoch;
    destruct (Nat.eqb (adopted_root policy) root) eqn:Hroot;
    simpl in Hadmit; try discriminate.
  apply Nat.eqb_eq in Hroot.
  exists policy. repeat split; assumption || reflexivity.
Qed.

Theorem admitted_local_is_trusted_and_live :
  forall context node operation,
    admit_cost_v2 context (LocalSpace node) operation = true ->
    exists trusted owner,
      context = LocalHost trusted owner /\
      trusted = true /\ owner = node /\ operation = Live.
Proof.
  intros context node operation Hadmit.
  destruct context as [policy|trusted owner]; simpl in Hadmit;
    try discriminate.
  destruct operation; try discriminate.
  destruct trusted;
    destruct (Nat.eqb owner node) eqn:Howner;
    simpl in Hadmit; try discriminate.
  apply Nat.eqb_eq in Howner. subst owner.
  exists true, node.
  repeat split; assumption || reflexivity.
Qed.

Theorem local_context_never_authorizes_consensus :
  forall trusted node root operation,
    admit_cost_v2 (LocalHost trusted node) (ConsensusSpace root) operation = false.
Proof. reflexivity. Qed.

Theorem local_context_never_authorizes_replay :
  forall trusted node space,
    admit_cost_v2 (LocalHost trusted node) space Replay = false.
Proof. intros; destruct space; reflexivity. Qed.

Example approved_consensus_cost_v2_is_admitted :
  admit_cost_v2
    (ConsensusHost {| adopted_approved := true; adopted_epoch := CostV2;
                      adopted_root := 7 |})
    (ConsensusSpace 7) Replay = true.
Proof. reflexivity. Qed.

Example local_cost_v2_is_live_only_even_when_ids_alias :
  admit_cost_v2 (LocalHost true 7) (LocalSpace 7) Live = true /\
  admit_cost_v2 (LocalHost true 7) (ConsensusSpace 7) Replay = false.
Proof. split; reflexivity. Qed.

Example unapproved_or_old_epoch_or_wrong_root_is_refused :
  admit_cost_v2
    (ConsensusHost {| adopted_approved := false; adopted_epoch := CostV2;
                      adopted_root := 7 |})
    (ConsensusSpace 7) Live = false /\
  admit_cost_v2
    (ConsensusHost {| adopted_approved := true; adopted_epoch := CostV1;
                      adopted_root := 7 |})
    (ConsensusSpace 7) Live = false /\
  admit_cost_v2
    (ConsensusHost {| adopted_approved := true; adopted_epoch := CostV2;
                      adopted_root := 7 |})
    (ConsensusSpace 8) Replay = false.
Proof. repeat split; reflexivity. Qed.

Example untrusted_local_is_refused :
  admit_cost_v2 (LocalHost false 7) (LocalSpace 7) Live = false.
Proof. reflexivity. Qed.

End HostCostV2Authority.
