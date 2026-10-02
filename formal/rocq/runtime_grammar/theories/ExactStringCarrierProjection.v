(** * Exact String carrier projection at the guest/host boundary

    This model covers a derived relation, not an implicit output operation.
    A caller must select it and hold Bridge authority.  Guest owner and sort,
    host profile and sort, and UTF-8 admission are checked before returning a
    host string.  A private name has no String-carrier projection, even when
    its bytes happen to be valid UTF-8.  Numeric identities below abstract
    committed fingerprints; their cryptographic binding is the separate
    HostProfileLifecycle obligation.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Module ExactStringCarrierProjection.

Record Signature := signature {
  guest_owner : nat;
  guest_sort : nat;
  host_profile : nat;
  host_sort : nat
}.

Inductive GuestValue :=
| StringLeaf (owner sort : nat) (bytes : list nat)
| PrivateLeaf (owner sort : nat) (name_bytes : list nat)
| Structured (owner sort : nat).

Inductive HostValue :=
| HostString (profile sort : nat) (bytes : list nat)
| HostPrivate (profile sort : nat) (name_bytes : list nat).

Section Codec.
Variable valid_utf8 : list nat -> bool.

Definition forward (sig : Signature) (selected bridge : bool)
           (value : GuestValue) : option HostValue :=
  if selected && bridge then
    match value with
    | StringLeaf owner sort bytes =>
        if Nat.eqb owner (guest_owner sig) &&
           Nat.eqb sort (guest_sort sig) && valid_utf8 bytes
        then Some (HostString (host_profile sig) (host_sort sig) bytes)
        else None
    | PrivateLeaf _ _ _ | Structured _ _ => None
    end
  else None.

Definition reverse (sig : Signature) (selected bridge : bool)
           (value : HostValue) : option GuestValue :=
  if selected && bridge then
    match value with
    | HostString profile sort bytes =>
        if Nat.eqb profile (host_profile sig) &&
           Nat.eqb sort (host_sort sig) && valid_utf8 bytes
        then Some (StringLeaf (guest_owner sig) (guest_sort sig) bytes)
        else None
    | HostPrivate _ _ _ => None
    end
  else None.

Theorem forward_requires_selection : forall sig bridge value,
  forward sig false bridge value = None.
Proof. intros. reflexivity. Qed.

Theorem forward_requires_bridge : forall sig selected value,
  forward sig selected false value = None.
Proof. intros. now destruct selected. Qed.

Theorem private_names_never_project : forall sig selected bridge owner sort bytes,
  forward sig selected bridge (PrivateLeaf owner sort bytes) = None.
Proof. intros. now destruct selected, bridge. Qed.

Theorem only_admitted_string_payload_projects : forall sig selected bridge value output,
  forward sig selected bridge value = Some output ->
  exists bytes,
    value = StringLeaf (guest_owner sig) (guest_sort sig) bytes /\
    valid_utf8 bytes = true /\
    output = HostString (host_profile sig) (host_sort sig) bytes.
Proof.
  intros sig selected bridge value output Projected.
  unfold forward in Projected.
  destruct selected, bridge; cbn in Projected; try discriminate.
  destruct value as [owner sort bytes|owner sort bytes|owner sort];
    cbn in Projected; try discriminate.
  destruct (Nat.eqb owner (guest_owner sig) &&
            Nat.eqb sort (guest_sort sig) && valid_utf8 bytes)
    eqn:Admitted; cbn in Projected; try discriminate.
  injection Projected as Output. subst output.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end.
  subst owner sort. exists bytes. repeat split; assumption || reflexivity.
Qed.

Theorem forward_never_emits_private_name :
  forall sig selected bridge value profile sort bytes,
  forward sig selected bridge value <> Some (HostPrivate profile sort bytes).
Proof.
  intros sig selected bridge value profile sort bytes Private.
  apply only_admitted_string_payload_projects in Private as [payload [_ [_ Equal]]].
  discriminate Equal.
Qed.

Theorem forward_refuses_other_owner : forall sig sort bytes owner,
  owner <> guest_owner sig ->
  forward sig true true (StringLeaf owner sort bytes) = None.
Proof.
  intros sig sort bytes owner Distinct. unfold forward. cbn.
  destruct (Nat.eqb owner (guest_owner sig)) eqn:Equal; [|reflexivity].
  apply Nat.eqb_eq in Equal. contradiction.
Qed.

Theorem forward_refuses_other_sort : forall sig owner bytes sort,
  sort <> guest_sort sig ->
  forward sig true true (StringLeaf owner sort bytes) = None.
Proof.
  intros sig owner bytes sort Distinct. unfold forward. cbn.
  destruct (Nat.eqb owner (guest_owner sig)); [|reflexivity].
  destruct (Nat.eqb sort (guest_sort sig)) eqn:Equal; [|reflexivity].
  apply Nat.eqb_eq in Equal. contradiction.
Qed.

Theorem exact_string_round_trip : forall sig bytes,
  valid_utf8 bytes = true ->
  reverse sig true true
    (HostString (host_profile sig) (host_sort sig) bytes) =
    Some (StringLeaf (guest_owner sig) (guest_sort sig) bytes).
Proof.
  intros [guest_owner guest_sort host_profile host_sort] bytes Valid.
  unfold reverse. cbn.
  rewrite ?Nat.eqb_refl, Valid. reflexivity.
Qed.

Theorem private_host_names_never_reverse :
  forall sig selected bridge profile sort bytes,
  reverse sig selected bridge (HostPrivate profile sort bytes) = None.
Proof. intros. now destruct selected, bridge. Qed.

End Codec.
End ExactStringCarrierProjection.
