//! Escrow/refund settlement for MeTTaIL Rho funding.
//!
//! This is the Δ4 cost hardening contract: reserve funds before a guarded
//! communication commits, charge escrow only on commit, and refund escrow on a
//! failed guard or abandoned candidate. All failures preserve the input state.

use std::collections::BTreeMap;

/// Stable identifier for the purse/account whose funds back one candidate.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PurseId(pub u64);

/// A pure funding-state snapshot for one purse.
#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EscrowState {
    pub purse: PurseId,
    pub available: u64,
    pub escrowed: u64,
    pub charged: u64,
}

impl EscrowState {
    pub const fn new(purse: PurseId, available: u64) -> Self {
        Self {
            purse,
            available,
            escrowed: 0,
            charged: 0,
        }
    }
}

/// Capability produced by a successful reserve operation.
#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EscrowTicket {
    pub purse: PurseId,
    pub amount: u64,
}

/// Reason a settlement step failed closed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SettlementBlocker {
    InsufficientAvailable,
    PurseMismatch,
    InsufficientEscrow,
    ArithmeticOverflow,
}

/// A located settlement operation whose target purse is explicit.
#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SettlementAction {
    Reserve { purse: PurseId, amount: u64 },
    Commit(EscrowTicket),
    Refund(EscrowTicket),
}

impl SettlementAction {
    pub const fn purse(self) -> PurseId {
        match self {
            Self::Reserve { purse, .. } => purse,
            Self::Commit(ticket) | Self::Refund(ticket) => ticket.purse,
        }
    }
}

/// Reason a located ledger operation failed closed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LedgerBlocker {
    MissingPurse,
    DuplicatePurse(PurseId),
    Settlement(SettlementBlocker),
}

/// Output of a settlement step.
#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SettlementStep {
    pub state: EscrowState,
    pub ticket: Option<EscrowTicket>,
    pub blocker: Option<SettlementBlocker>,
}

impl SettlementStep {
    const fn allowed(state: EscrowState, ticket: Option<EscrowTicket>) -> Self {
        Self { state, ticket, blocker: None }
    }

    const fn blocked(state: EscrowState, blocker: SettlementBlocker) -> Self {
        Self {
            state,
            ticket: None,
            blocker: Some(blocker),
        }
    }

    pub const fn is_allowed(&self) -> bool {
        self.blocker.is_none()
    }
}

/// Deterministic purse-indexed settlement ledger.
///
/// Construction rejects duplicate purse states. Every operation then targets
/// exactly one purse, or fails closed when the purse is absent.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocatedEscrowLedger {
    states: BTreeMap<PurseId, EscrowState>,
}

/// Output of a located settlement step.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LedgerSettlementStep {
    pub ledger: LocatedEscrowLedger,
    pub ticket: Option<EscrowTicket>,
    pub blocker: Option<LedgerBlocker>,
}

impl LedgerSettlementStep {
    fn allowed(ledger: LocatedEscrowLedger, ticket: Option<EscrowTicket>) -> Self {
        Self { ledger, ticket, blocker: None }
    }

    fn blocked(ledger: LocatedEscrowLedger, blocker: LedgerBlocker) -> Self {
        Self {
            ledger,
            ticket: None,
            blocker: Some(blocker),
        }
    }

    pub const fn is_allowed(&self) -> bool {
        self.blocker.is_none()
    }
}

impl LocatedEscrowLedger {
    /// Build a deterministic ledger, rejecting duplicate purse states.
    pub fn new(states: impl IntoIterator<Item = EscrowState>) -> Result<Self, LedgerBlocker> {
        let mut indexed = BTreeMap::new();
        for state in states {
            if indexed.insert(state.purse, state).is_some() {
                return Err(LedgerBlocker::DuplicatePurse(state.purse));
            }
        }
        Ok(Self { states: indexed })
    }

    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    pub fn state(&self, purse: PurseId) -> Option<EscrowState> {
        self.states.get(&purse).copied()
    }

    pub fn purses(&self) -> impl Iterator<Item = PurseId> + '_ {
        self.states.keys().copied()
    }

    /// Apply one located action to exactly one purse.
    ///
    /// Missing purses and local settlement blockers preserve the whole ledger.
    pub fn apply(&self, action: SettlementAction) -> LedgerSettlementStep {
        self.clone().apply_owned(action)
    }

    /// Apply one located action, consuming the ledger to avoid cloning it.
    ///
    /// This is the preferred path for generated runtime code that does not need
    /// to retain the pre-state after the step.
    pub fn apply_owned(mut self, action: SettlementAction) -> LedgerSettlementStep {
        let purse = action.purse();
        let Some(state) = self.states.get(&purse).copied() else {
            return LedgerSettlementStep::blocked(self, LedgerBlocker::MissingPurse);
        };

        let step = match action {
            SettlementAction::Reserve { amount, .. } => reserve_escrow(state, amount),
            SettlementAction::Commit(ticket) => commit_escrow(state, ticket),
            SettlementAction::Refund(ticket) => refund_escrow(state, ticket),
        };

        if let Some(blocker) = step.blocker {
            return LedgerSettlementStep::blocked(self, LedgerBlocker::Settlement(blocker));
        }

        self.states.insert(purse, step.state);
        LedgerSettlementStep::allowed(self, step.ticket)
    }
}

/// Reserve `amount` from available funds into escrow.
///
/// A successful reserve returns a ticket that must later be committed or
/// refunded. Failed reservation preserves `state`.
pub const fn reserve_escrow(state: EscrowState, amount: u64) -> SettlementStep {
    if amount > state.available {
        return SettlementStep::blocked(state, SettlementBlocker::InsufficientAvailable);
    }

    let Some(escrowed) = state.escrowed.checked_add(amount) else {
        return SettlementStep::blocked(state, SettlementBlocker::ArithmeticOverflow);
    };

    SettlementStep::allowed(
        EscrowState {
            purse: state.purse,
            available: state.available - amount,
            escrowed,
            charged: state.charged,
        },
        Some(EscrowTicket { purse: state.purse, amount }),
    )
}

/// Commit a reserved ticket, moving the ticket amount from escrow to charged.
pub const fn commit_escrow(state: EscrowState, ticket: EscrowTicket) -> SettlementStep {
    if ticket.purse.0 != state.purse.0 {
        return SettlementStep::blocked(state, SettlementBlocker::PurseMismatch);
    }
    if ticket.amount > state.escrowed {
        return SettlementStep::blocked(state, SettlementBlocker::InsufficientEscrow);
    }
    let Some(charged) = state.charged.checked_add(ticket.amount) else {
        return SettlementStep::blocked(state, SettlementBlocker::ArithmeticOverflow);
    };
    SettlementStep::allowed(
        EscrowState {
            purse: state.purse,
            available: state.available,
            escrowed: state.escrowed - ticket.amount,
            charged,
        },
        None,
    )
}

/// Refund a reserved ticket, moving the ticket amount back to available funds.
pub const fn refund_escrow(state: EscrowState, ticket: EscrowTicket) -> SettlementStep {
    if ticket.purse.0 != state.purse.0 {
        return SettlementStep::blocked(state, SettlementBlocker::PurseMismatch);
    }
    if ticket.amount > state.escrowed {
        return SettlementStep::blocked(state, SettlementBlocker::InsufficientEscrow);
    }
    let Some(available) = state.available.checked_add(ticket.amount) else {
        return SettlementStep::blocked(state, SettlementBlocker::ArithmeticOverflow);
    };
    SettlementStep::allowed(
        EscrowState {
            purse: state.purse,
            available,
            escrowed: state.escrowed - ticket.amount,
            charged: state.charged,
        },
        None,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn total(state: EscrowState) -> u64 {
        state.available + state.escrowed + state.charged
    }

    #[test]
    fn reserve_moves_available_to_escrow_and_returns_ticket() {
        let state = EscrowState::new(PurseId(7), 10);
        let step = reserve_escrow(state, 4);

        assert!(step.is_allowed());
        assert_eq!(
            step.state,
            EscrowState {
                purse: PurseId(7),
                available: 6,
                escrowed: 4,
                charged: 0
            }
        );
        assert_eq!(step.ticket, Some(EscrowTicket { purse: PurseId(7), amount: 4 }));
        assert_eq!(total(step.state), total(state));
    }

    #[test]
    fn reserve_without_available_funds_preserves_state() {
        let state = EscrowState::new(PurseId(7), 3);
        let step = reserve_escrow(state, 4);

        assert!(!step.is_allowed());
        assert_eq!(step.blocker, Some(SettlementBlocker::InsufficientAvailable));
        assert_eq!(step.state, state);
        assert_eq!(step.ticket, None);
    }

    #[test]
    fn commit_moves_escrow_to_charged_and_preserves_total() {
        let state = reserve_escrow(EscrowState::new(PurseId(7), 10), 4).state;
        let ticket = EscrowTicket { purse: PurseId(7), amount: 4 };
        let step = commit_escrow(state, ticket);

        assert!(step.is_allowed());
        assert_eq!(
            step.state,
            EscrowState {
                purse: PurseId(7),
                available: 6,
                escrowed: 0,
                charged: 4
            }
        );
        assert_eq!(total(step.state), total(state));
    }

    #[test]
    fn refund_reverses_a_successful_reserve() {
        let initial = EscrowState::new(PurseId(7), 10);
        let reserved = reserve_escrow(initial, 4);
        let step = refund_escrow(reserved.state, reserved.ticket.expect("ticket"));

        assert!(step.is_allowed());
        assert_eq!(step.state, initial);
    }

    #[test]
    fn purse_mismatch_preserves_state() {
        let state = reserve_escrow(EscrowState::new(PurseId(7), 10), 4).state;
        let wrong = EscrowTicket { purse: PurseId(8), amount: 4 };

        assert_eq!(commit_escrow(state, wrong).state, state);
        assert_eq!(commit_escrow(state, wrong).blocker, Some(SettlementBlocker::PurseMismatch));
        assert_eq!(refund_escrow(state, wrong).state, state);
        assert_eq!(refund_escrow(state, wrong).blocker, Some(SettlementBlocker::PurseMismatch));
    }

    #[test]
    fn over_escrow_ticket_preserves_state() {
        let state = reserve_escrow(EscrowState::new(PurseId(7), 10), 4).state;
        let too_large = EscrowTicket { purse: PurseId(7), amount: 5 };

        assert_eq!(commit_escrow(state, too_large).state, state);
        assert_eq!(
            commit_escrow(state, too_large).blocker,
            Some(SettlementBlocker::InsufficientEscrow)
        );
        assert_eq!(refund_escrow(state, too_large).state, state);
        assert_eq!(
            refund_escrow(state, too_large).blocker,
            Some(SettlementBlocker::InsufficientEscrow)
        );
    }

    #[test]
    fn reserve_overflow_preserves_state() {
        let state = EscrowState {
            purse: PurseId(7),
            available: 1,
            escrowed: u64::MAX,
            charged: 0,
        };
        let step = reserve_escrow(state, 1);

        assert!(!step.is_allowed());
        assert_eq!(step.blocker, Some(SettlementBlocker::ArithmeticOverflow));
        assert_eq!(step.state, state);
        assert_eq!(step.ticket, None);
    }

    #[test]
    fn commit_overflow_preserves_state() {
        let state = EscrowState {
            purse: PurseId(7),
            available: 0,
            escrowed: 1,
            charged: u64::MAX,
        };
        let ticket = EscrowTicket { purse: PurseId(7), amount: 1 };
        let step = commit_escrow(state, ticket);

        assert!(!step.is_allowed());
        assert_eq!(step.blocker, Some(SettlementBlocker::ArithmeticOverflow));
        assert_eq!(step.state, state);
        assert_eq!(step.ticket, None);
    }

    #[test]
    fn refund_overflow_preserves_state() {
        let state = EscrowState {
            purse: PurseId(7),
            available: u64::MAX,
            escrowed: 1,
            charged: 0,
        };
        let ticket = EscrowTicket { purse: PurseId(7), amount: 1 };
        let step = refund_escrow(state, ticket);

        assert!(!step.is_allowed());
        assert_eq!(step.blocker, Some(SettlementBlocker::ArithmeticOverflow));
        assert_eq!(step.state, state);
        assert_eq!(step.ticket, None);
    }

    #[test]
    fn located_ledger_rejects_duplicate_purse_states() {
        let duplicate = LocatedEscrowLedger::new([
            EscrowState::new(PurseId(7), 10),
            EscrowState::new(PurseId(7), 20),
        ]);

        assert_eq!(duplicate, Err(LedgerBlocker::DuplicatePurse(PurseId(7))));
    }

    #[test]
    fn located_ledger_missing_purse_preserves_ledger() {
        let ledger = LocatedEscrowLedger::new([EscrowState::new(PurseId(7), 10)]).expect("ledger");
        let step = ledger.apply(SettlementAction::Reserve { purse: PurseId(8), amount: 1 });

        assert!(!step.is_allowed());
        assert_eq!(step.blocker, Some(LedgerBlocker::MissingPurse));
        assert_eq!(step.ledger, ledger);
        assert_eq!(step.ticket, None);
    }

    #[test]
    fn located_ledger_updates_only_matching_purse() {
        let ledger = LocatedEscrowLedger::new([
            EscrowState::new(PurseId(7), 10),
            EscrowState::new(PurseId(8), 20),
        ])
        .expect("ledger");

        let step = ledger.apply(SettlementAction::Reserve { purse: PurseId(7), amount: 4 });

        assert!(step.is_allowed());
        assert_eq!(
            step.ledger.state(PurseId(7)),
            Some(EscrowState {
                purse: PurseId(7),
                available: 6,
                escrowed: 4,
                charged: 0
            })
        );
        assert_eq!(step.ledger.state(PurseId(8)), ledger.state(PurseId(8)));
    }

    #[test]
    fn located_ledger_local_blocker_preserves_whole_ledger() {
        let ledger = LocatedEscrowLedger::new([EscrowState::new(PurseId(7), 3)]).expect("ledger");
        let step = ledger.apply(SettlementAction::Reserve { purse: PurseId(7), amount: 4 });

        assert!(!step.is_allowed());
        assert_eq!(
            step.blocker,
            Some(LedgerBlocker::Settlement(SettlementBlocker::InsufficientAvailable))
        );
        assert_eq!(step.ledger, ledger);
    }

    #[test]
    fn located_ledger_distinct_purse_actions_commute() {
        let ledger = LocatedEscrowLedger::new([
            EscrowState::new(PurseId(7), 10),
            EscrowState::new(PurseId(8), 20),
        ])
        .expect("ledger");
        let left = SettlementAction::Reserve { purse: PurseId(7), amount: 4 };
        let right = SettlementAction::Reserve { purse: PurseId(8), amount: 5 };

        let left_then_right = ledger.apply(left).ledger.apply(right).ledger;
        let right_then_left = ledger.apply(right).ledger.apply(left).ledger;

        assert_eq!(left_then_right, right_then_left);
        assert_eq!(
            left_then_right.state(PurseId(7)),
            Some(EscrowState {
                purse: PurseId(7),
                available: 6,
                escrowed: 4,
                charged: 0
            })
        );
        assert_eq!(
            left_then_right.state(PurseId(8)),
            Some(EscrowState {
                purse: PurseId(8),
                available: 15,
                escrowed: 5,
                charged: 0
            })
        );
    }

    #[test]
    fn located_ledger_same_sequence_is_deterministic() {
        let ledger = LocatedEscrowLedger::new([EscrowState::new(PurseId(7), 10)]).expect("ledger");
        let reserve = SettlementAction::Reserve { purse: PurseId(7), amount: 4 };

        assert_eq!(ledger.apply(reserve), ledger.apply(reserve));
    }

    #[test]
    fn located_ledger_owned_apply_matches_borrowed_apply() {
        let ledger = LocatedEscrowLedger::new([EscrowState::new(PurseId(7), 10)]).expect("ledger");
        let reserve = SettlementAction::Reserve { purse: PurseId(7), amount: 4 };

        assert_eq!(ledger.clone().apply_owned(reserve), ledger.apply(reserve));
    }
}
