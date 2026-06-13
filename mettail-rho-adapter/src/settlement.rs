//! Escrow/refund settlement for MeTTaIL Rho funding.
//!
//! This is the Δ4 cost hardening contract: reserve funds before a guarded
//! communication commits, charge escrow only on commit, and refund escrow on a
//! failed guard or abandoned candidate. All failures preserve the input state.

/// Stable identifier for the purse/account whose funds back one candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
}
