(*
 * RhoEscrowSettlement: Δ4 reserve/commit/refund settlement contract.
 *
 * Reserve moves funds from available to escrow. Commit moves escrow to charged.
 * Refund returns escrow to available. Mismatched purses or over-escrow tickets
 * fail closed and preserve the input state.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Section RhoEscrowSettlement.

  Definition PurseId : Type := nat.

  Record EscrowState : Type := {
    purse_id : PurseId;
    available : nat;
    escrowed : nat;
    charged : nat
  }.

  Record EscrowTicket : Type := {
    ticket_purse : PurseId;
    ticket_amount : nat
  }.

  Inductive SettlementBlocker : Type :=
    | InsufficientAvailable
    | PurseMismatch
    | InsufficientEscrow
    | ArithmeticOverflow.

  Inductive SettlementOutcome : Type :=
    | SettlementOk : EscrowState -> option EscrowTicket -> SettlementOutcome
    | SettlementBlocked : SettlementBlocker -> EscrowState -> SettlementOutcome.

  Definition reserve_escrow (s : EscrowState) (amount : nat) : SettlementOutcome :=
    if amount <=? available s then
      SettlementOk
        {| purse_id := purse_id s;
           available := available s - amount;
           escrowed := escrowed s + amount;
           charged := charged s |}
        (Some {| ticket_purse := purse_id s; ticket_amount := amount |})
    else
      SettlementBlocked InsufficientAvailable s.

  Definition ticket_matches_purse (s : EscrowState) (t : EscrowTicket) : bool :=
    Nat.eqb (ticket_purse t) (purse_id s).

  Definition ticket_fits_escrow (s : EscrowState) (t : EscrowTicket) : bool :=
    ticket_amount t <=? escrowed s.

  Definition commit_escrow (s : EscrowState) (t : EscrowTicket) : SettlementOutcome :=
    if ticket_matches_purse s t then
      if ticket_fits_escrow s t then
        SettlementOk
          {| purse_id := purse_id s;
             available := available s;
             escrowed := escrowed s - ticket_amount t;
             charged := charged s + ticket_amount t |}
          None
      else
        SettlementBlocked InsufficientEscrow s
    else
      SettlementBlocked PurseMismatch s.

  Definition refund_escrow (s : EscrowState) (t : EscrowTicket) : SettlementOutcome :=
    if ticket_matches_purse s t then
      if ticket_fits_escrow s t then
        SettlementOk
          {| purse_id := purse_id s;
             available := available s + ticket_amount t;
             escrowed := escrowed s - ticket_amount t;
             charged := charged s |}
          None
      else
        SettlementBlocked InsufficientEscrow s
    else
      SettlementBlocked PurseMismatch s.

  Definition total_funds (s : EscrowState) : nat :=
    available s + escrowed s + charged s.

  Theorem reserve_insufficient_available_blocks : forall s amount,
    available s < amount ->
    reserve_escrow s amount = SettlementBlocked InsufficientAvailable s.
  Proof.
    intros s amount Hlt. unfold reserve_escrow.
    assert (Hblock : (amount <=? available s) = false).
    { apply Nat.leb_gt. exact Hlt. }
    rewrite Hblock. reflexivity.
  Qed.

  Theorem reserve_success_conserves_total : forall s amount s' ticket,
    reserve_escrow s amount = SettlementOk s' (Some ticket) ->
    total_funds s' = total_funds s.
  Proof.
    intros s amount s' ticket Hreserve.
    unfold reserve_escrow in Hreserve.
    destruct (amount <=? available s) eqn:Hle; inversion Hreserve; subst.
    unfold total_funds. simpl.
    apply Nat.leb_le in Hle. lia.
  Qed.

  Theorem reserve_success_ticket_matches_state : forall s amount s' ticket,
    reserve_escrow s amount = SettlementOk s' (Some ticket) ->
    ticket_purse ticket = purse_id s
    /\ ticket_amount ticket = amount
    /\ purse_id s' = purse_id s
    /\ escrowed s' = escrowed s + amount
    /\ available s' = available s - amount.
  Proof.
    intros s amount s' ticket Hreserve.
    unfold reserve_escrow in Hreserve.
    destruct (amount <=? available s); inversion Hreserve; subst.
    repeat split; reflexivity.
  Qed.

  Theorem commit_purse_mismatch_blocks : forall s ticket,
    ticket_purse ticket <> purse_id s ->
    commit_escrow s ticket = SettlementBlocked PurseMismatch s.
  Proof.
    intros s ticket Hneq. unfold commit_escrow, ticket_matches_purse.
    assert (Hmismatch : Nat.eqb (ticket_purse ticket) (purse_id s) = false).
    { apply Nat.eqb_neq. exact Hneq. }
    rewrite Hmismatch. reflexivity.
  Qed.

  Theorem refund_purse_mismatch_blocks : forall s ticket,
    ticket_purse ticket <> purse_id s ->
    refund_escrow s ticket = SettlementBlocked PurseMismatch s.
  Proof.
    intros s ticket Hneq. unfold refund_escrow, ticket_matches_purse.
    assert (Hmismatch : Nat.eqb (ticket_purse ticket) (purse_id s) = false).
    { apply Nat.eqb_neq. exact Hneq. }
    rewrite Hmismatch. reflexivity.
  Qed.

  Theorem commit_over_escrow_blocks : forall s ticket,
    ticket_purse ticket = purse_id s ->
    escrowed s < ticket_amount ticket ->
    commit_escrow s ticket = SettlementBlocked InsufficientEscrow s.
  Proof.
    intros s ticket Hpurse Hlt.
    unfold commit_escrow, ticket_matches_purse, ticket_fits_escrow.
    assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
    { apply Nat.eqb_eq. exact Hpurse. }
    assert (Hover : (ticket_amount ticket <=? escrowed s) = false).
    { apply Nat.leb_gt. exact Hlt. }
    rewrite Hmatch. rewrite Hover. reflexivity.
  Qed.

  Theorem refund_over_escrow_blocks : forall s ticket,
    ticket_purse ticket = purse_id s ->
    escrowed s < ticket_amount ticket ->
    refund_escrow s ticket = SettlementBlocked InsufficientEscrow s.
  Proof.
    intros s ticket Hpurse Hlt.
    unfold refund_escrow, ticket_matches_purse, ticket_fits_escrow.
    assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
    { apply Nat.eqb_eq. exact Hpurse. }
    assert (Hover : (ticket_amount ticket <=? escrowed s) = false).
    { apply Nat.leb_gt. exact Hlt. }
    rewrite Hmatch. rewrite Hover. reflexivity.
  Qed.

  Theorem commit_success_conserves_total : forall s ticket s',
    commit_escrow s ticket = SettlementOk s' None ->
    total_funds s' = total_funds s.
  Proof.
    intros s ticket s' Hcommit.
    unfold commit_escrow, ticket_matches_purse, ticket_fits_escrow in Hcommit.
    destruct (Nat.eqb (ticket_purse ticket) (purse_id s)) eqn:Hpurse;
      try discriminate Hcommit.
    destruct (ticket_amount ticket <=? escrowed s) eqn:Hle;
      inversion Hcommit; subst.
    unfold total_funds. simpl.
    apply Nat.leb_le in Hle. lia.
  Qed.

  Theorem refund_success_conserves_total : forall s ticket s',
    refund_escrow s ticket = SettlementOk s' None ->
    total_funds s' = total_funds s.
  Proof.
    intros s ticket s' Hrefund.
    unfold refund_escrow, ticket_matches_purse, ticket_fits_escrow in Hrefund.
    destruct (Nat.eqb (ticket_purse ticket) (purse_id s)) eqn:Hpurse;
      try discriminate Hrefund.
    destruct (ticket_amount ticket <=? escrowed s) eqn:Hle;
      inversion Hrefund; subst.
    unfold total_funds. simpl.
    apply Nat.leb_le in Hle. lia.
  Qed.

  Theorem commit_success_charges_ticket_amount : forall s ticket s',
    commit_escrow s ticket = SettlementOk s' None ->
    charged s' = charged s + ticket_amount ticket
    /\ escrowed s' = escrowed s - ticket_amount ticket
    /\ available s' = available s
    /\ purse_id s' = purse_id s.
  Proof.
    intros s ticket s' Hcommit.
    unfold commit_escrow, ticket_matches_purse, ticket_fits_escrow in Hcommit.
    destruct (Nat.eqb (ticket_purse ticket) (purse_id s)); try discriminate Hcommit.
    destruct (ticket_amount ticket <=? escrowed s); inversion Hcommit; subst.
    repeat split; reflexivity.
  Qed.

  Theorem refund_success_returns_ticket_amount : forall s ticket s',
    refund_escrow s ticket = SettlementOk s' None ->
    available s' = available s + ticket_amount ticket
    /\ escrowed s' = escrowed s - ticket_amount ticket
    /\ charged s' = charged s
    /\ purse_id s' = purse_id s.
  Proof.
    intros s ticket s' Hrefund.
    unfold refund_escrow, ticket_matches_purse, ticket_fits_escrow in Hrefund.
    destruct (Nat.eqb (ticket_purse ticket) (purse_id s)); try discriminate Hrefund.
    destruct (ticket_amount ticket <=? escrowed s); inversion Hrefund; subst.
    repeat split; reflexivity.
  Qed.

  Theorem reserve_then_refund_restores_state : forall s amount reserved ticket refunded,
    reserve_escrow s amount = SettlementOk reserved (Some ticket) ->
    refund_escrow reserved ticket = SettlementOk refunded None ->
    refunded = s.
  Proof.
    intros s amount reserved ticket refunded Hreserve Hrefund.
    destruct s as [p a e c]. simpl in *.
    unfold reserve_escrow in Hreserve.
    simpl in Hreserve.
    destruct (amount <=? a) eqn:Hle; inversion Hreserve; subst.
    apply Nat.leb_le in Hle.
    unfold refund_escrow, ticket_matches_purse, ticket_fits_escrow in Hrefund.
    simpl in Hrefund.
    destruct (Nat.eqb p p) eqn:Hpurse.
    2: { rewrite Nat.eqb_refl in Hpurse. discriminate Hpurse. }
    destruct (amount <=? e + amount) eqn:Hfits.
    2: { apply Nat.leb_gt in Hfits. lia. }
    inversion Hrefund; subst.
    assert (Ha : a - amount + amount = a) by lia.
    assert (He : e + amount - amount = e) by lia.
    rewrite Ha. rewrite He. reflexivity.
  Qed.

  Definition u64_max : nat := Nat.pow 2 64 - 1.

  Definition checked_add_nat (x y : nat) : option nat :=
    if x + y <=? u64_max then Some (x + y) else None.

  Definition bounded_state (s : EscrowState) : Prop :=
    available s <= u64_max /\ escrowed s <= u64_max /\ charged s <= u64_max.

  Definition reserve_escrow_u64 (s : EscrowState) (amount : nat)
    : SettlementOutcome :=
    if amount <=? available s then
      match checked_add_nat (escrowed s) amount with
      | Some escrowed' =>
          SettlementOk
            {| purse_id := purse_id s;
               available := available s - amount;
               escrowed := escrowed';
               charged := charged s |}
            (Some {| ticket_purse := purse_id s; ticket_amount := amount |})
      | None => SettlementBlocked ArithmeticOverflow s
      end
    else
      SettlementBlocked InsufficientAvailable s.

  Definition commit_escrow_u64 (s : EscrowState) (t : EscrowTicket)
    : SettlementOutcome :=
    if ticket_matches_purse s t then
      if ticket_fits_escrow s t then
        match checked_add_nat (charged s) (ticket_amount t) with
        | Some charged' =>
            SettlementOk
              {| purse_id := purse_id s;
                 available := available s;
                 escrowed := escrowed s - ticket_amount t;
                 charged := charged' |}
              None
        | None => SettlementBlocked ArithmeticOverflow s
        end
      else
        SettlementBlocked InsufficientEscrow s
    else
      SettlementBlocked PurseMismatch s.

  Definition refund_escrow_u64 (s : EscrowState) (t : EscrowTicket)
    : SettlementOutcome :=
    if ticket_matches_purse s t then
      if ticket_fits_escrow s t then
        match checked_add_nat (available s) (ticket_amount t) with
        | Some available' =>
            SettlementOk
              {| purse_id := purse_id s;
                 available := available';
                 escrowed := escrowed s - ticket_amount t;
                 charged := charged s |}
              None
        | None => SettlementBlocked ArithmeticOverflow s
        end
      else
        SettlementBlocked InsufficientEscrow s
    else
      SettlementBlocked PurseMismatch s.

  Theorem checked_add_nat_overflow : forall x y,
    u64_max < x + y ->
    checked_add_nat x y = None.
  Proof.
    intros x y Hoverflow. unfold checked_add_nat.
    assert (Hblock : (x + y <=? u64_max) = false).
    { apply Nat.leb_gt. exact Hoverflow. }
    rewrite Hblock. reflexivity.
  Qed.

  Theorem reserve_u64_insufficient_available_blocks : forall s amount,
    available s < amount ->
    reserve_escrow_u64 s amount = SettlementBlocked InsufficientAvailable s.
  Proof.
    intros s amount Hlt. unfold reserve_escrow_u64.
    assert (Hblock : (amount <=? available s) = false).
    { apply Nat.leb_gt. exact Hlt. }
    rewrite Hblock. reflexivity.
  Qed.

  Theorem reserve_u64_overflow_blocks : forall s amount,
    amount <= available s ->
    u64_max < escrowed s + amount ->
    reserve_escrow_u64 s amount = SettlementBlocked ArithmeticOverflow s.
  Proof.
    intros s amount Havailable Hoverflow.
    unfold reserve_escrow_u64, checked_add_nat.
    assert (Hle : (amount <=? available s) = true).
    { apply Nat.leb_le. exact Havailable. }
    assert (Hoverflow' : (escrowed s + amount <=? u64_max) = false).
    { apply Nat.leb_gt. exact Hoverflow. }
    rewrite Hle. rewrite Hoverflow'. reflexivity.
  Qed.

  Theorem commit_u64_overflow_blocks : forall s ticket,
    ticket_purse ticket = purse_id s ->
    ticket_amount ticket <= escrowed s ->
    u64_max < charged s + ticket_amount ticket ->
    commit_escrow_u64 s ticket = SettlementBlocked ArithmeticOverflow s.
  Proof.
    intros s ticket Hpurse Hfits Hoverflow.
    unfold commit_escrow_u64, ticket_matches_purse, ticket_fits_escrow,
      checked_add_nat.
    assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
    { apply Nat.eqb_eq. exact Hpurse. }
    assert (Hle : (ticket_amount ticket <=? escrowed s) = true).
    { apply Nat.leb_le. exact Hfits. }
    assert (Hoverflow' : (charged s + ticket_amount ticket <=? u64_max) = false).
    { apply Nat.leb_gt. exact Hoverflow. }
    rewrite Hmatch. rewrite Hle. rewrite Hoverflow'. reflexivity.
  Qed.

  Theorem refund_u64_overflow_blocks : forall s ticket,
    ticket_purse ticket = purse_id s ->
    ticket_amount ticket <= escrowed s ->
    u64_max < available s + ticket_amount ticket ->
    refund_escrow_u64 s ticket = SettlementBlocked ArithmeticOverflow s.
  Proof.
    intros s ticket Hpurse Hfits Hoverflow.
    unfold refund_escrow_u64, ticket_matches_purse, ticket_fits_escrow,
      checked_add_nat.
    assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
    { apply Nat.eqb_eq. exact Hpurse. }
    assert (Hle : (ticket_amount ticket <=? escrowed s) = true).
    { apply Nat.leb_le. exact Hfits. }
    assert (Hoverflow' : (available s + ticket_amount ticket <=? u64_max) = false).
    { apply Nat.leb_gt. exact Hoverflow. }
    rewrite Hmatch. rewrite Hle. rewrite Hoverflow'. reflexivity.
  Qed.

  Theorem reserve_u64_success_refines_unbounded :
    forall s amount s' ticket,
    reserve_escrow_u64 s amount = SettlementOk s' (Some ticket) ->
    reserve_escrow s amount = SettlementOk s' (Some ticket).
  Proof.
    intros s amount s' ticket Hreserve.
    unfold reserve_escrow_u64 in Hreserve.
    unfold reserve_escrow.
    destruct (amount <=? available s) eqn:Hle; try discriminate Hreserve.
    unfold checked_add_nat in Hreserve.
    destruct (escrowed s + amount <=? u64_max); inversion Hreserve; subst.
    reflexivity.
  Qed.

  Theorem commit_u64_success_refines_unbounded :
    forall s ticket s',
    commit_escrow_u64 s ticket = SettlementOk s' None ->
    commit_escrow s ticket = SettlementOk s' None.
  Proof.
    intros s ticket s' Hcommit.
    unfold commit_escrow_u64 in Hcommit.
    unfold commit_escrow.
    destruct (ticket_matches_purse s ticket) eqn:Hpurse;
      try discriminate Hcommit.
    destruct (ticket_fits_escrow s ticket) eqn:Hfits;
      try discriminate Hcommit.
    unfold checked_add_nat in Hcommit.
    destruct (charged s + ticket_amount ticket <=? u64_max);
      inversion Hcommit; subst.
    reflexivity.
  Qed.

  Theorem refund_u64_success_refines_unbounded :
    forall s ticket s',
    refund_escrow_u64 s ticket = SettlementOk s' None ->
    refund_escrow s ticket = SettlementOk s' None.
  Proof.
    intros s ticket s' Hrefund.
    unfold refund_escrow_u64 in Hrefund.
    unfold refund_escrow.
    destruct (ticket_matches_purse s ticket) eqn:Hpurse;
      try discriminate Hrefund.
    destruct (ticket_fits_escrow s ticket) eqn:Hfits;
      try discriminate Hrefund.
    unfold checked_add_nat in Hrefund.
    destruct (available s + ticket_amount ticket <=? u64_max);
      inversion Hrefund; subst.
    reflexivity.
  Qed.

  Theorem reserve_u64_success_conserves_total : forall s amount s' ticket,
    reserve_escrow_u64 s amount = SettlementOk s' (Some ticket) ->
    total_funds s' = total_funds s.
  Proof.
    intros s amount s' ticket Hreserve.
    eapply reserve_success_conserves_total.
    apply reserve_u64_success_refines_unbounded. exact Hreserve.
  Qed.

  Theorem commit_u64_success_conserves_total : forall s ticket s',
    commit_escrow_u64 s ticket = SettlementOk s' None ->
    total_funds s' = total_funds s.
  Proof.
    intros s ticket s' Hcommit.
    eapply commit_success_conserves_total.
    apply commit_u64_success_refines_unbounded. exact Hcommit.
  Qed.

  Theorem refund_u64_success_conserves_total : forall s ticket s',
    refund_escrow_u64 s ticket = SettlementOk s' None ->
    total_funds s' = total_funds s.
  Proof.
    intros s ticket s' Hrefund.
    eapply refund_success_conserves_total.
    apply refund_u64_success_refines_unbounded. exact Hrefund.
  Qed.

  Theorem reserve_u64_then_refund_restores_state :
    forall s amount reserved ticket refunded,
    bounded_state s ->
    reserve_escrow_u64 s amount = SettlementOk reserved (Some ticket) ->
    refund_escrow_u64 reserved ticket = SettlementOk refunded None ->
    refunded = s.
  Proof.
    intros s amount reserved ticket refunded Hbounded Hreserve Hrefund.
    destruct s as [p a e c]. simpl in *.
    destruct Hbounded as [Ha_max [_ _]].
    unfold reserve_escrow_u64 in Hreserve. simpl in Hreserve.
    destruct (amount <=? a) eqn:Hle; try discriminate Hreserve.
    apply Nat.leb_le in Hle.
    unfold checked_add_nat in Hreserve.
    destruct (e + amount <=? u64_max) eqn:Hreserve_add;
      try discriminate Hreserve.
    inversion Hreserve; subst; clear Hreserve.
    unfold refund_escrow_u64, ticket_matches_purse, ticket_fits_escrow in Hrefund.
    simpl in Hrefund.
    destruct (Nat.eqb p p) eqn:Hpurse.
    2: { rewrite Nat.eqb_refl in Hpurse. discriminate Hpurse. }
    destruct (amount <=? e + amount) eqn:Hfits.
    2: { apply Nat.leb_gt in Hfits. lia. }
    unfold checked_add_nat in Hrefund.
    assert (Ha : a - amount + amount = a) by lia.
    assert (Hrefund_add : (a - amount + amount <=? u64_max) = true).
    { rewrite Ha. apply Nat.leb_le. exact Ha_max. }
    rewrite Hrefund_add in Hrefund.
    inversion Hrefund; subst.
    assert (He : e + amount - amount = e) by lia.
    rewrite Ha. rewrite He. reflexivity.
  Qed.

End RhoEscrowSettlement.
