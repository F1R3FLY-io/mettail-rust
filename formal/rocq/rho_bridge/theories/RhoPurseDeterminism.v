(*
 * RhoPurseDeterminism: Δ3 located-purse determinism for settlement.
 *
 * The settlement layer is deterministic per purse: duplicate purse states are
 * rejected, missing purse states are rejected, failed local settlement preserves
 * the ledger, and actions located at distinct purses commute on the final
 * ledger state.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.
From RhoBridge Require Import RhoEscrowSettlement.

Section RhoPurseDeterminism.

  Inductive LocatedAction : Type :=
    | ReserveAt : PurseId -> nat -> LocatedAction
    | CommitAt : EscrowTicket -> LocatedAction
    | RefundAt : EscrowTicket -> LocatedAction.

  Definition action_purse (a : LocatedAction) : PurseId :=
    match a with
    | ReserveAt p _ => p
    | CommitAt t => ticket_purse t
    | RefundAt t => ticket_purse t
    end.

  Record TwoPurseLedger : Type := {
    left_state : EscrowState;
    right_state : EscrowState
  }.

  Inductive LedgerBlocker : Type :=
    | MissingPurse
    | DuplicatePurse
    | LocalSettlementBlocked : SettlementBlocker -> LedgerBlocker.

  Inductive LedgerOutcome : Type :=
    | LedgerOk : TwoPurseLedger -> option EscrowTicket -> LedgerOutcome
    | LedgerBlocked : LedgerBlocker -> TwoPurseLedger -> LedgerOutcome.

  Definition outcome_ledger (outcome : LedgerOutcome) : TwoPurseLedger :=
    match outcome with
    | LedgerOk ledger _ => ledger
    | LedgerBlocked _ ledger => ledger
    end.

  Definition ledger_distinct (ledger : TwoPurseLedger) : bool :=
    negb (Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger))).

  Definition ledger_has_purse (p : PurseId) (ledger : TwoPurseLedger) : bool :=
    Nat.eqb p (purse_id (left_state ledger))
    || Nat.eqb p (purse_id (right_state ledger)).

  Definition with_left (ledger : TwoPurseLedger) (state : EscrowState)
    : TwoPurseLedger :=
    {| left_state := state; right_state := right_state ledger |}.

  Definition with_right (ledger : TwoPurseLedger) (state : EscrowState)
    : TwoPurseLedger :=
    {| left_state := left_state ledger; right_state := state |}.

  Definition apply_action_to_state (a : LocatedAction) (s : EscrowState)
    : SettlementOutcome :=
    match a with
    | ReserveAt p amount =>
        if Nat.eqb p (purse_id s) then
          reserve_escrow_u64 s amount
        else
          SettlementBlocked PurseMismatch s
    | CommitAt ticket => commit_escrow_u64 s ticket
    | RefundAt ticket => refund_escrow_u64 s ticket
    end.

  Definition next_state (a : LocatedAction) (s : EscrowState) : EscrowState :=
    match apply_action_to_state a s with
    | SettlementOk s' _ => s'
    | SettlementBlocked _ _ => s
    end.

  Definition finish_left (ledger : TwoPurseLedger) (outcome : SettlementOutcome)
    : LedgerOutcome :=
    match outcome with
    | SettlementOk state ticket => LedgerOk (with_left ledger state) ticket
    | SettlementBlocked blocker _ =>
        LedgerBlocked (LocalSettlementBlocked blocker) ledger
    end.

  Definition finish_right (ledger : TwoPurseLedger) (outcome : SettlementOutcome)
    : LedgerOutcome :=
    match outcome with
    | SettlementOk state ticket => LedgerOk (with_right ledger state) ticket
    | SettlementBlocked blocker _ =>
        LedgerBlocked (LocalSettlementBlocked blocker) ledger
    end.

  Definition apply_located_action (ledger : TwoPurseLedger) (a : LocatedAction)
    : LedgerOutcome :=
    if Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger)) then
      LedgerBlocked DuplicatePurse ledger
    else if Nat.eqb (action_purse a) (purse_id (left_state ledger)) then
      finish_left ledger (apply_action_to_state a (left_state ledger))
    else if Nat.eqb (action_purse a) (purse_id (right_state ledger)) then
      finish_right ledger (apply_action_to_state a (right_state ledger))
    else
      LedgerBlocked MissingPurse ledger.

  Definition apply_located_state (ledger : TwoPurseLedger) (a : LocatedAction)
    : TwoPurseLedger :=
    if Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger)) then
      ledger
    else if Nat.eqb (action_purse a) (purse_id (left_state ledger)) then
      with_left ledger (next_state a (left_state ledger))
    else if Nat.eqb (action_purse a) (purse_id (right_state ledger)) then
      with_right ledger (next_state a (right_state ledger))
    else
      ledger.

  Lemma finish_left_matches_state : forall ledger outcome a,
    outcome = apply_action_to_state a (left_state ledger) ->
    outcome_ledger (finish_left ledger outcome)
    = with_left ledger (next_state a (left_state ledger)).
  Proof.
    intros ledger outcome a Houtcome.
    destruct ledger as [left right]. simpl in *.
    subst. unfold finish_left, next_state, with_left.
    destruct (apply_action_to_state a left); reflexivity.
  Qed.

  Lemma finish_right_matches_state : forall ledger outcome a,
    outcome = apply_action_to_state a (right_state ledger) ->
    outcome_ledger (finish_right ledger outcome)
    = with_right ledger (next_state a (right_state ledger)).
  Proof.
    intros ledger outcome a Houtcome.
    destruct ledger as [left right]. simpl in *.
    subst. unfold finish_right, next_state, with_right.
    destruct (apply_action_to_state a right); reflexivity.
  Qed.

  Theorem located_outcome_matches_state : forall ledger a,
    outcome_ledger (apply_located_action ledger a) = apply_located_state ledger a.
  Proof.
    intros ledger a.
    unfold apply_located_action, apply_located_state.
    destruct (Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger)));
      try reflexivity.
    destruct (Nat.eqb (action_purse a) (purse_id (left_state ledger))) eqn:Hleft.
    - apply finish_left_matches_state. reflexivity.
    - destruct (Nat.eqb (action_purse a) (purse_id (right_state ledger))) eqn:Hright.
      + apply finish_right_matches_state. reflexivity.
      + reflexivity.
  Qed.

  Theorem duplicate_purses_block : forall ledger a,
    purse_id (left_state ledger) = purse_id (right_state ledger) ->
    apply_located_action ledger a = LedgerBlocked DuplicatePurse ledger.
  Proof.
    intros ledger a Hdup.
    unfold apply_located_action.
    assert (Hdup_bool :
      Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger)) = true).
    { apply Nat.eqb_eq. exact Hdup. }
    rewrite Hdup_bool. reflexivity.
  Qed.

  Theorem missing_purse_blocks : forall ledger a,
    ledger_distinct ledger = true ->
    ledger_has_purse (action_purse a) ledger = false ->
    apply_located_action ledger a = LedgerBlocked MissingPurse ledger.
  Proof.
    intros ledger a Hdistinct Hmissing.
    unfold apply_located_action, ledger_distinct, ledger_has_purse in *.
    apply negb_true_iff in Hdistinct.
    rewrite Hdistinct.
    apply orb_false_elim in Hmissing as [Hleft Hright].
    rewrite Hleft. rewrite Hright. reflexivity.
  Qed.

  Theorem blocked_local_settlement_preserves_ledger : forall ledger a blocker ledger',
    apply_located_action ledger a = LedgerBlocked (LocalSettlementBlocked blocker) ledger' ->
    ledger' = ledger.
  Proof.
    intros ledger a blocker ledger' Happly.
    unfold apply_located_action, finish_left, finish_right in Happly.
    destruct (Nat.eqb (purse_id (left_state ledger)) (purse_id (right_state ledger)));
      try discriminate Happly.
    destruct (Nat.eqb (action_purse a) (purse_id (left_state ledger))) eqn:Hleft.
    - destruct (apply_action_to_state a (left_state ledger));
        try discriminate Happly.
      inversion Happly; reflexivity.
    - destruct (Nat.eqb (action_purse a) (purse_id (right_state ledger))) eqn:Hright.
      + destruct (apply_action_to_state a (right_state ledger));
          try discriminate Happly.
        inversion Happly; reflexivity.
      + discriminate Happly.
  Qed.

  Theorem located_action_deterministic : forall ledger a outcome1 outcome2,
    apply_located_action ledger a = outcome1 ->
    apply_located_action ledger a = outcome2 ->
    outcome1 = outcome2.
  Proof.
    intros ledger a outcome1 outcome2 H1 H2.
    rewrite <- H1. exact H2.
  Qed.

  Lemma next_state_preserves_purse : forall a s,
    action_purse a = purse_id s ->
    purse_id (next_state a s) = purse_id s.
  Proof.
    intros a s Hpurse.
    destruct a as [p amount | ticket | ticket]; simpl in *.
    - unfold next_state, apply_action_to_state. simpl.
      assert (Hmatch : Nat.eqb p (purse_id s) = true).
      { apply Nat.eqb_eq. exact Hpurse. }
      rewrite Hmatch.
      unfold reserve_escrow_u64, checked_add_nat.
      destruct (amount <=? available s);
        try reflexivity.
      destruct (escrowed s + amount <=? u64_max);
        reflexivity.
    - unfold next_state, apply_action_to_state. simpl.
      unfold commit_escrow_u64, ticket_matches_purse, ticket_fits_escrow.
      assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
      { apply Nat.eqb_eq. exact Hpurse. }
      rewrite Hmatch.
      destruct (ticket_amount ticket <=? escrowed s);
        try reflexivity.
      unfold checked_add_nat.
      destruct (charged s + ticket_amount ticket <=? u64_max);
        reflexivity.
    - unfold next_state, apply_action_to_state. simpl.
      unfold refund_escrow_u64, ticket_matches_purse, ticket_fits_escrow.
      assert (Hmatch : Nat.eqb (ticket_purse ticket) (purse_id s) = true).
      { apply Nat.eqb_eq. exact Hpurse. }
      rewrite Hmatch.
      destruct (ticket_amount ticket <=? escrowed s);
        try reflexivity.
      unfold checked_add_nat.
      destruct (available s + ticket_amount ticket <=? u64_max);
        reflexivity.
  Qed.

  Theorem located_action_preserves_target_purse : forall ledger a ledger' ticket,
    ledger_distinct ledger = true ->
    apply_located_action ledger a = LedgerOk ledger' ticket ->
    ledger_has_purse (action_purse a) ledger' = true.
  Proof.
    intros ledger a ledger' ticket Hdistinct Happly.
    unfold apply_located_action, ledger_distinct in Happly, Hdistinct.
    apply negb_true_iff in Hdistinct.
    rewrite Hdistinct in Happly.
    destruct (Nat.eqb (action_purse a) (purse_id (left_state ledger))) eqn:Hleft.
    - unfold finish_left in Happly.
      destruct (apply_action_to_state a (left_state ledger)) eqn:Hlocal;
        try discriminate Happly.
      inversion Happly; subst. clear Happly.
      unfold ledger_has_purse. simpl.
      apply Nat.eqb_eq in Hleft.
      assert (Hnext : next_state a (left_state ledger) = e).
      { unfold next_state. rewrite Hlocal. reflexivity. }
      rewrite <- Hnext.
      rewrite (next_state_preserves_purse a (left_state ledger) Hleft).
      rewrite <- Hleft. rewrite Nat.eqb_refl. reflexivity.
    - destruct (Nat.eqb (action_purse a) (purse_id (right_state ledger))) eqn:Hright;
        try discriminate Happly.
      unfold finish_right in Happly.
      destruct (apply_action_to_state a (right_state ledger)) eqn:Hlocal;
        try discriminate Happly.
      inversion Happly; subst. clear Happly.
      unfold ledger_has_purse. simpl.
      apply Nat.eqb_eq in Hright.
      assert (Hnext : next_state a (right_state ledger) = e).
      { unfold next_state. rewrite Hlocal. reflexivity. }
      rewrite <- Hnext.
      rewrite (next_state_preserves_purse a (right_state ledger) Hright).
      rewrite <- Hright. rewrite Nat.eqb_refl.
      rewrite orb_true_r. reflexivity.
  Qed.

  Theorem distinct_purse_actions_commute_left_right : forall ledger left_action right_action,
    ledger_distinct ledger = true ->
    action_purse left_action = purse_id (left_state ledger) ->
    action_purse right_action = purse_id (right_state ledger) ->
    apply_located_state (apply_located_state ledger left_action) right_action
    = apply_located_state (apply_located_state ledger right_action) left_action.
  Proof.
    intros ledger left_action right_action Hdistinct Hleft_action Hright_action.
    destruct ledger as [left right]. simpl in *.
    unfold ledger_distinct in Hdistinct. simpl in Hdistinct.
    apply negb_true_iff in Hdistinct.
    apply Nat.eqb_neq in Hdistinct.
    unfold apply_located_state. simpl.
    assert (Hlr : Nat.eqb (purse_id left) (purse_id right) = false).
    { apply Nat.eqb_neq. exact Hdistinct. }
    assert (Hrl : Nat.eqb (purse_id right) (purse_id left) = false).
    { apply Nat.eqb_neq. lia. }
    rewrite Hlr.
    rewrite Hleft_action. rewrite Nat.eqb_refl.
    simpl.
    rewrite (next_state_preserves_purse left_action left Hleft_action).
    rewrite Hlr.
    rewrite Hright_action. rewrite Hrl. rewrite Nat.eqb_refl.
    simpl.
    rewrite (next_state_preserves_purse right_action right Hright_action).
    rewrite Hlr. rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

End RhoPurseDeterminism.
