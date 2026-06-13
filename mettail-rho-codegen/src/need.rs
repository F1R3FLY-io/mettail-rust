//! Call-by-need budget admission for generic Rho lowering.
//!
//! The generic CBN/need path represents non-native computations as thunks.
//! This module is the compile-time/runtime-planning contract for bounded force
//! admission: every force consumes one lookahead step, and a cold force that
//! must allocate a memo cell also consumes one heap cell.

/// Remaining admission budget for generic call-by-need forcing.
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallByNeedBudget {
    pub lookahead_remaining: usize,
    pub heap_remaining: usize,
}

impl CallByNeedBudget {
    pub const fn new(lookahead_remaining: usize, heap_remaining: usize) -> Self {
        Self { lookahead_remaining, heap_remaining }
    }
}

/// Whether a force observes an existing memo cell or must create one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallByNeedForce {
    MemoHit,
    MemoMiss,
}

/// Reason a call-by-need force is not admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallByNeedBudgetBlocker {
    LookaheadExceeded,
    HeapBudgetExceeded,
}

/// Result of checking whether a force may run under the current budget.
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallByNeedAdmission {
    pub budget_after: CallByNeedBudget,
    pub blocker: Option<CallByNeedBudgetBlocker>,
}

impl CallByNeedAdmission {
    pub const fn allowed(budget_after: CallByNeedBudget) -> Self {
        Self { budget_after, blocker: None }
    }

    pub const fn blocked(blocker: CallByNeedBudgetBlocker, budget_after: CallByNeedBudget) -> Self {
        Self { budget_after, blocker: Some(blocker) }
    }

    pub const fn is_allowed(&self) -> bool {
        self.blocker.is_none()
    }
}

/// Admit one generic call-by-need force under `budget`.
///
/// Failed admission preserves the incoming budget. A memo hit does not allocate
/// a heap cell; a memo miss does.
pub const fn admit_call_by_need_force(
    force: CallByNeedForce,
    budget: CallByNeedBudget,
) -> CallByNeedAdmission {
    if budget.lookahead_remaining == 0 {
        return CallByNeedAdmission::blocked(CallByNeedBudgetBlocker::LookaheadExceeded, budget);
    }

    let after_lookahead = budget.lookahead_remaining - 1;
    match force {
        CallByNeedForce::MemoHit => CallByNeedAdmission::allowed(CallByNeedBudget::new(
            after_lookahead,
            budget.heap_remaining,
        )),
        CallByNeedForce::MemoMiss => {
            if budget.heap_remaining == 0 {
                CallByNeedAdmission::blocked(CallByNeedBudgetBlocker::HeapBudgetExceeded, budget)
            } else {
                CallByNeedAdmission::allowed(CallByNeedBudget::new(
                    after_lookahead,
                    budget.heap_remaining - 1,
                ))
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memo_hit_consumes_lookahead_but_not_heap() {
        let admission =
            admit_call_by_need_force(CallByNeedForce::MemoHit, CallByNeedBudget::new(3, 2));

        assert!(admission.is_allowed());
        assert_eq!(admission.budget_after, CallByNeedBudget::new(2, 2));
    }

    #[test]
    fn memo_miss_consumes_lookahead_and_one_heap_cell() {
        let admission =
            admit_call_by_need_force(CallByNeedForce::MemoMiss, CallByNeedBudget::new(3, 2));

        assert!(admission.is_allowed());
        assert_eq!(admission.budget_after, CallByNeedBudget::new(2, 1));
    }

    #[test]
    fn zero_lookahead_blocks_before_heap_accounting() {
        let budget = CallByNeedBudget::new(0, 0);
        let admission = admit_call_by_need_force(CallByNeedForce::MemoMiss, budget);

        assert!(!admission.is_allowed());
        assert_eq!(admission.blocker, Some(CallByNeedBudgetBlocker::LookaheadExceeded));
        assert_eq!(admission.budget_after, budget);
    }

    #[test]
    fn cold_force_without_heap_budget_blocks_without_consuming_lookahead() {
        let budget = CallByNeedBudget::new(4, 0);
        let admission = admit_call_by_need_force(CallByNeedForce::MemoMiss, budget);

        assert!(!admission.is_allowed());
        assert_eq!(admission.blocker, Some(CallByNeedBudgetBlocker::HeapBudgetExceeded));
        assert_eq!(admission.budget_after, budget);
    }
}
