(** * Strict enrollment of reflected nominal heads

    The existing String protobuf decoder is permissive about unknown fields.
    Decoding two private-name byte strings to the same text does not make the
    original names equal. The new closed FLT adapter therefore checks equality
    with the existing writer's canonical bytes before accepting a name. These
    theorems hold for every writer and reader, without a codec-correctness axiom:
    the concrete equality check supplies the exact identity guarantee.

    A closed marked constructor must carry the exact ground marker, rather than
    the nonground marker that the more general existing admission accepts.
    Marker observations here stand for exact equality with the existing marker
    Par constants. They do not abstract away arbitrary executable components;
    ReflectedParEnvelope supplies that separate prerequisite. No statement here
    claims arbitrary Par annotations or protobuf implementation correctness.

    The resource layer models the shared caller's cumulative logical work and
    a decreasing payload-byte allowance, checked together before an allocation
    or traversal step. Payload bytes are not an assertion about allocator RSS. *)

From Stdlib Require Import Lists.List Strings.Ascii Strings.String Bool.Bool
  Arith.PeanoNat Lia.
From RuntimeGrammar Require Import InstalledFltJudgments.
Import ListNotations.

Module ReflectedHeadEnrollment.
Module Budget := InstalledFltJudgments.InstalledFltJudgments.

Definition Bytes := list ascii.
Definition bytes_eq_dec := list_eq_dec ascii_dec.

Section NominalIdentity.
  Variable encode : string -> Bytes.
  Variable decode : Bytes -> option string.

  Definition canonical_name bytes :=
    match decode bytes with
    | Some name => if bytes_eq_dec (encode name) bytes then Some name else None
    | None => None
    end.

  Theorem admitted_name_retains_exact_identity : forall bytes name,
    canonical_name bytes = Some name ->
    decode bytes = Some name /\ encode name = bytes.
  Proof.
    intros bytes name H. unfold canonical_name in H.
    destruct (decode bytes) as [decoded|] eqn:Hdecode; try discriminate.
    destruct (bytes_eq_dec (encode decoded) bytes); try discriminate.
    inversion H; subst. auto.
  Qed.

  Theorem same_admitted_name_cannot_merge_distinct_private_ids :
    forall first second name,
      canonical_name first = Some name -> canonical_name second = Some name ->
      first = second.
  Proof.
    intros first second name Hfirst Hsecond.
    apply admitted_name_retains_exact_identity in Hfirst, Hsecond.
    destruct Hfirst as [_ Hfirst], Hsecond as [_ Hsecond]. congruence.
  Qed.

  Theorem noncanonical_private_id_is_not_normalized : forall bytes name,
    decode bytes = Some name -> encode name <> bytes -> canonical_name bytes = None.
  Proof.
    intros bytes name Hdecode Hdifferent. unfold canonical_name. rewrite Hdecode.
    destruct (bytes_eq_dec (encode name) bytes); [contradiction|reflexivity].
  Qed.

  Variable parse_tag : string -> option (string * string).

  Definition owned_tag expected bytes :=
    match canonical_name bytes with
    | Some tag =>
        match parse_tag tag with
        | Some (owner, label) =>
            if String.eqb owner expected then Some (tag, label) else None
        | None => None
        end
    | None => None
    end.

  Theorem admitted_tag_keeps_owner_label_and_private_identity :
    forall expected bytes tag label,
      owned_tag expected bytes = Some (tag, label) ->
      encode tag = bytes /\ parse_tag tag = Some (expected, label).
  Proof.
    intros expected bytes tag label H. unfold owned_tag in H.
    destruct (canonical_name bytes) as [decoded|] eqn:Hname; try discriminate.
    destruct (parse_tag decoded) as [[owner actual]|] eqn:Hparse; try discriminate.
    destruct (String.eqb owner expected) eqn:Howner; try discriminate.
    inversion H; subst. apply String.eqb_eq in Howner. subst owner.
    apply admitted_name_retains_exact_identity in Hname. tauto.
  Qed.
End NominalIdentity.

Inductive Marker := Absent | Ground | Nonground | InvalidMarker.

Definition closed_marker marked marker :=
  match marked, marker with true, Ground | false, Absent => true | _, _ => false end.

Definition reconstructed_marker (marked : bool) := if marked then Ground else Absent.

Theorem accepted_closed_marker_round_trips : forall marked marker,
  closed_marker marked marker = true -> reconstructed_marker marked = marker.
Proof. intros [] []; cbn; intros H; try discriminate; reflexivity. Qed.

Theorem nonground_marker_cannot_be_silently_promoted : forall marked,
  closed_marker marked Nonground = false.
Proof. intros []; reflexivity. Qed.

(** [reserve] is atomic across both dimensions: no byte balance is changed when
    work fails, and no work is spent when the byte allowance is insufficient. *)
Definition reserve ceiling used available units bytes : option (nat * nat) :=
  match Budget.charge_work ceiling used units with
  | Some total =>
      if Nat.leb bytes available then Some (total, available - bytes) else None
  | None => None
  end.

Theorem successful_reservation_preserves_both_bounds :
  forall ceiling used available units bytes total remaining,
    reserve ceiling used available units bytes = Some (total, remaining) ->
    total = used + units /\ used <= total /\ total <= ceiling /\
    bytes <= available /\ remaining + bytes = available.
Proof.
  intros ceiling used available units bytes total remaining H.
  unfold reserve in H.
  destruct (Budget.charge_work ceiling used units) as [charged|] eqn:Hwork;
    try discriminate.
  destruct (Nat.leb bytes available) eqn:Hbytes; try discriminate.
  inversion H; subst. apply Nat.leb_le in Hbytes.
  apply Budget.successful_charge_preserves_prefix_and_ceiling in Hwork. lia.
Qed.

Inductive ReservationEvent := AllocatePayload (bytes : nat).

Definition before_allocation ceiling used available units bytes :=
  match reserve ceiling used available units bytes with
  | Some balances => (Some balances, [AllocatePayload bytes])
  | None => (None, [])
  end.

Theorem no_allocation_event_before_successful_reservation :
  forall ceiling used available units bytes,
    reserve ceiling used available units bytes = None ->
    snd (before_allocation ceiling used available units bytes) = [].
Proof. intros. unfold before_allocation. now rewrite H. Qed.

Theorem emitted_allocation_is_within_byte_allowance :
  forall ceiling used available units bytes balances,
    before_allocation ceiling used available units bytes =
      (Some balances, [AllocatePayload bytes]) -> bytes <= available.
Proof.
  intros ceiling used available units bytes [total remaining] H.
  unfold before_allocation in H.
  destruct (reserve ceiling used available units bytes) as [[charged rest]|]
    eqn:Hreserve; try discriminate.
  apply successful_reservation_preserves_both_bounds in Hreserve. lia.
Qed.

Example zero_byte_allowance_cannot_allocate : reserve 100 0 0 1 1 = None.
Proof. reflexivity. Qed.
Example overdrawn_work_cannot_reserve_even_zero_bytes : reserve 3 4 8 0 0 = None.
Proof. reflexivity. Qed.

End ReflectedHeadEnrollment.

Print Assumptions ReflectedHeadEnrollment.admitted_name_retains_exact_identity.
Print Assumptions ReflectedHeadEnrollment.same_admitted_name_cannot_merge_distinct_private_ids.
Print Assumptions ReflectedHeadEnrollment.noncanonical_private_id_is_not_normalized.
Print Assumptions ReflectedHeadEnrollment.admitted_tag_keeps_owner_label_and_private_identity.
Print Assumptions ReflectedHeadEnrollment.accepted_closed_marker_round_trips.
Print Assumptions ReflectedHeadEnrollment.nonground_marker_cannot_be_silently_promoted.
Print Assumptions ReflectedHeadEnrollment.successful_reservation_preserves_both_bounds.
Print Assumptions ReflectedHeadEnrollment.no_allocation_event_before_successful_reservation.
Print Assumptions ReflectedHeadEnrollment.emitted_allocation_is_within_byte_allowance.
