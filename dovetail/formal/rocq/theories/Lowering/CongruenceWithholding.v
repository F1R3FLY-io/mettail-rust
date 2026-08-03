(*
 * CongruenceWithholding: why an e-graph position can withhold propagation only
 * by ceasing to store a child e-class identifier at that position.
 *
 * The Rust lowering has two carriers for a scalar category field:
 *
 *   ChildClass c       -- an ordinary child edge, canonicalized through [find]
 *   WithheldPayload p  -- the original payload, retained verbatim in a leaf
 *
 * An e-node key is an operator plus the keys of its fields.  Consequently two
 * [ChildClass] fields whose e-classes have merged are the same key.  This is
 * not a rewrite policy that can be disabled after the fact: it is the identity
 * relation of the hash-consed data structure.  A [WithheldPayload] field does
 * not consult [find], so distinct payloads remain distinct even if the terms'
 * ordinary e-classes have merged.
 *
 * The second model below states the corresponding edge-set property.  Given a
 * derived set W of withheld positions, severance retains exactly the ordinary
 * propagation edges whose position is outside W.  No edge outside W is lost,
 * and no edge inside W survives.
 *
 * This file deliberately models identifiers and payloads as [nat].  The Rust
 * representation is richer, but the proof depends only on equality and on the
 * fact that [find] canonicalizes child identifiers.  There are no admissions,
 * axioms, or unproved assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Inductive FieldCarrier : Type :=
| ChildClass : nat -> FieldCarrier
| WithheldPayload : nat -> FieldCarrier.

Inductive FieldKey : Type :=
| ClassKey : nat -> FieldKey
| PayloadKey : nat -> FieldKey.

Definition field_key (find : nat -> nat) (field : FieldCarrier) : FieldKey :=
  match field with
  | ChildClass child => ClassKey (find child)
  | WithheldPayload payload => PayloadKey payload
  end.

Definition ENodeKey : Type := (nat * list FieldKey)%type.

Definition enode_key
    (find : nat -> nat) (operator : nat) (fields : list FieldCarrier) : ENodeKey :=
  (operator, map (field_key find) fields).

(** Theorem W1.  If a position stores a child e-class identifier, merging the
    two children makes the enclosing one-field e-nodes identical.  Therefore a
    representation that must keep the enclosing nodes distinct cannot continue
    to use [ChildClass] at that position. *)
Theorem withholding_requires_severance :
  forall (find : nat -> nat) (operator left right : nat),
    find left = find right ->
    enode_key find operator [ChildClass left] =
    enode_key find operator [ChildClass right].
Proof.
  intros find operator left right Hmerge.
  unfold enode_key, field_key. simpl.
  now rewrite Hmerge.
Qed.

(** A verbatim withheld carrier is insensitive to e-class merging and remains
    injective in its payload. *)
Theorem severed_payload_key_injective :
  forall (find : nat -> nat) (operator left right : nat),
    enode_key find operator [WithheldPayload left] =
    enode_key find operator [WithheldPayload right] ->
    left = right.
Proof.
  intros find operator left right Hkey.
  unfold enode_key, field_key in Hkey. simpl in Hkey.
  now inversion Hkey.
Qed.

(** A propagation edge is identified by its constructor-field position and
    its source and target payloads. *)
Record PropagationEdge : Type := edge {
  edge_position : nat;
  edge_source : nat;
  edge_target : nat
}.

Definition ordinary_edge
    (step : nat -> nat -> Prop) (candidate : PropagationEdge) : Prop :=
  step (edge_source candidate) (edge_target candidate).

Definition severed_edge
    (withheld : list nat)
    (step : nat -> nat -> Prop)
    (candidate : PropagationEdge) : Prop :=
  ordinary_edge step candidate /\ ~ In (edge_position candidate) withheld.

(** Severance removes exactly the edges at withheld positions. *)
Theorem severance_removes_exactly_the_withheld_edges :
  forall (withheld : list nat)
         (step : nat -> nat -> Prop)
         (candidate : PropagationEdge),
    severed_edge withheld step candidate <->
      ordinary_edge step candidate /\
      ~ In (edge_position candidate) withheld.
Proof.
  intros withheld step candidate.
  unfold severed_edge.
  tauto.
Qed.

Corollary severance_preserves_every_unwithheld_edge :
  forall (withheld : list nat)
         (step : nat -> nat -> Prop)
         (candidate : PropagationEdge),
    ordinary_edge step candidate ->
    ~ In (edge_position candidate) withheld ->
    severed_edge withheld step candidate.
Proof.
  intros withheld step candidate Hedge Houtside.
  split; assumption.
Qed.

Corollary severance_rejects_every_withheld_edge :
  forall (withheld : list nat)
         (step : nat -> nat -> Prop)
         (candidate : PropagationEdge),
    In (edge_position candidate) withheld ->
    ~ severed_edge withheld step candidate.
Proof.
  intros withheld step candidate Hinside [_ Houtside].
  now apply Houtside.
Qed.
