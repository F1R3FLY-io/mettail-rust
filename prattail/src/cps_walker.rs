//! Phase F.13 chain_10000 Exp 15 Substage 1 (2026-05-27): CPS continuation
//! queue for the planned trampolined walker rewrite.
//!
//! Per `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` §3.1
//! and §3.4: the planned CPS rewrite replaces the recursive
//! `apply_action_to_cursor` driver with an explicit `VecDeque` of
//! `Continuation<W>` records. The walker dequeues one continuation per
//! iteration, runs ONE mini-step, and may enqueue 0..N successor
//! continuations. Step boundaries are marked by `Continuation::StepBarrier`
//! records that trigger `merge_equivalent_cursors`.
//!
//! Substage 1 ships ONLY the data structure module + tests as dead code;
//! Substage 5 wires the queue into `step_fanout`.
//!
//! # Continuation format (per plan §3.1)
//!
//! Size budget: P50 ≤ 32 B, P99 ≤ 64 B per the Substage 0
//! measurement (commit `9662b81`, mean 36-47 B observed, max 63 B).
//!
//! ```text
//!   Step             { cursor_id: CursorId }                  // 8 B
//!   ApplyAction      { cursor_id: CursorId,
//!                      action: WpdaStepAction<W> }            // ≤ 64 B
//!   Resolved         { cursor_id: CursorId }                  // 8 B
//!   ShellApply       { cohort_id: CohortId,
//!                      action: WpdaStepAction<W> }            // ≤ 64 B
//!   StepBarrier                                                // 4 B
//! ```
//!
//! `cohort_id` is reserved for Substage 6's cohort generalization —
//! Substage 1 ships the enum variant + indexing helpers, no consumer.

use std::collections::VecDeque;

use crate::automata::semiring::SemiringRef;
use crate::cursor_id::CursorId;
use crate::wpda_walker::WpdaStepAction;

/// Cohort id for Substage 6 ShellApply continuations. u32 newtype
/// (`CohortId(u32)` mirrors `CursorId` to keep Vec-indexing cheap).
/// Substage 1 does not consume; the enum variant carries it for the
/// queue format soundness check (Substage 5 will instantiate cohorts).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct CohortId(pub u32);

/// `CohortId` sentinel for "no cohort". Mirrors `CURSOR_ID_NONE`.
pub const COHORT_ID_NONE: CohortId = CohortId(u32::MAX);

/// One continuation record. Mirrors the planned CPS queue format.
///
/// `Box<WpdaStepAction<W>>` for `ApplyAction` and `ShellApply` so the
/// enum tag + cursor_id + Box pointer occupy ≤ 24 B regardless of action
/// payload size. The Substage 0 size projection helper
/// (`project_continuation_record_for_action`) calculates the unboxed
/// size for the gate measurement; this on-the-wire format uses Box for
/// queue cache locality.
#[derive(Debug)]
pub enum Continuation<W: SemiringRef> {
    /// Drive cursor `cursor_id` one step: look up its state, ask the
    /// engine for the next action, enqueue an `ApplyAction`.
    Step { cursor_id: CursorId },
    /// Apply `action` to cursor `cursor_id`. Produced by:
    /// - the Step path (engine returned a single action)
    /// - the Fork-arm broadcast (one ApplyAction per branch, with the
    ///   per-branch state already installed in `CursorStore::minimal`)
    ApplyAction {
        cursor_id: CursorId,
        action: Box<WpdaStepAction<W>>,
    },
    /// Cursor reached a terminal state (`WpdaState::Resolved`); held in
    /// the queue until the next `StepBarrier` collects all Resolved
    /// records for `merge_equivalent_cursors`.
    Resolved { cursor_id: CursorId },
    /// Substage 6+ cohort-shell dispatch: apply `action` to the shell
    /// once, broadcast per-arc weight multiplication to the cohort's
    /// members.
    ShellApply {
        cohort_id: CohortId,
        action: Box<WpdaStepAction<W>>,
    },
    /// End-of-step rendezvous marker. The walker drains the queue until
    /// a barrier dequeues, then runs `merge_equivalent_cursors` over
    /// the alive cursor set, then re-enqueues `Step { cursor_id }` per
    /// survivor plus a fresh barrier.
    StepBarrier,
}

impl<W: SemiringRef> Continuation<W> {
    /// Variant index for stats / debug. Matches the enum declaration
    /// order: Step=0, ApplyAction=1, Resolved=2, ShellApply=3,
    /// StepBarrier=4.
    pub fn variant_index(&self) -> usize {
        match self {
            Continuation::Step { .. } => 0,
            Continuation::ApplyAction { .. } => 1,
            Continuation::Resolved { .. } => 2,
            Continuation::ShellApply { .. } => 3,
            Continuation::StepBarrier => 4,
        }
    }

    /// Is this continuation the step barrier?
    pub fn is_barrier(&self) -> bool {
        matches!(self, Continuation::StepBarrier)
    }
}

/// Walker-owned continuation queue. Single-threaded `VecDeque` (FIFO).
/// Per plan §3.4, lock-free crossbeam deque is reserved for future
/// multi-thread cohort dispatch — out of scope for Substage 1 / 5.
pub struct ContinuationQueue<W: SemiringRef> {
    inner: VecDeque<Continuation<W>>,
    /// Cumulative enqueue count (stats).
    enqueued_total: u64,
    /// Cumulative dequeue count (stats).
    dequeued_total: u64,
    /// Peak inner length.
    peak_len: usize,
}

impl<W: SemiringRef> Default for ContinuationQueue<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: SemiringRef> ContinuationQueue<W> {
    /// Construct an empty queue.
    pub fn new() -> Self {
        Self {
            inner: VecDeque::new(),
            enqueued_total: 0,
            dequeued_total: 0,
            peak_len: 0,
        }
    }

    /// Preallocate `capacity` slots.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: VecDeque::with_capacity(capacity),
            enqueued_total: 0,
            dequeued_total: 0,
            peak_len: 0,
        }
    }

    /// Reset to empty (parse-boundary hook).
    pub fn clear(&mut self) {
        self.inner.clear();
        self.enqueued_total = 0;
        self.dequeued_total = 0;
        self.peak_len = 0;
    }

    /// Enqueue at the back (FIFO).
    pub fn push_back(&mut self, c: Continuation<W>) {
        self.inner.push_back(c);
        self.enqueued_total = self.enqueued_total.saturating_add(1);
        let len = self.inner.len();
        if len > self.peak_len {
            self.peak_len = len;
        }
    }

    /// Dequeue from the front (FIFO).
    pub fn pop_front(&mut self) -> Option<Continuation<W>> {
        let popped = self.inner.pop_front();
        if popped.is_some() {
            self.dequeued_total = self.dequeued_total.saturating_add(1);
        }
        popped
    }

    /// True iff empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Current length.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Total enqueues (stats).
    pub fn enqueued_total(&self) -> u64 {
        self.enqueued_total
    }

    /// Total dequeues (stats).
    pub fn dequeued_total(&self) -> u64 {
        self.dequeued_total
    }

    /// Peak length observed (stats).
    pub fn peak_len(&self) -> usize {
        self.peak_len
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::semiring::Semiring;
    use crate::wpda_runtime::WpdaState;

    fn ready() -> WpdaState {
        WpdaState::Ready { min_bp: 0 }
    }

    fn one() -> LexicographicWeight {
        <LexicographicWeight as Semiring>::one()
    }

    #[test]
    fn queue_starts_empty() {
        let q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        assert_eq!(q.len(), 0);
        assert!(q.is_empty());
        assert_eq!(q.enqueued_total(), 0);
        assert_eq!(q.dequeued_total(), 0);
        assert_eq!(q.peak_len(), 0);
    }

    #[test]
    fn push_back_pop_front_is_fifo() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::Step {
            cursor_id: CursorId(1),
        });
        q.push_back(Continuation::Step {
            cursor_id: CursorId(2),
        });
        q.push_back(Continuation::Step {
            cursor_id: CursorId(3),
        });
        match q.pop_front().expect("pop") {
            Continuation::Step { cursor_id } => assert_eq!(cursor_id, CursorId(1)),
            _ => panic!("expected Step"),
        }
        match q.pop_front().expect("pop") {
            Continuation::Step { cursor_id } => assert_eq!(cursor_id, CursorId(2)),
            _ => panic!("expected Step"),
        }
    }

    #[test]
    fn stats_count_enqueue_and_dequeue() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::Step {
            cursor_id: CursorId(0),
        });
        q.push_back(Continuation::Step {
            cursor_id: CursorId(1),
        });
        assert_eq!(q.enqueued_total(), 2);
        assert_eq!(q.dequeued_total(), 0);
        let _ = q.pop_front();
        assert_eq!(q.dequeued_total(), 1);
    }

    #[test]
    fn peak_len_is_high_water_mark() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::Step {
            cursor_id: CursorId(0),
        });
        q.push_back(Continuation::Step {
            cursor_id: CursorId(1),
        });
        q.push_back(Continuation::Step {
            cursor_id: CursorId(2),
        });
        assert_eq!(q.peak_len(), 3);
        let _ = q.pop_front();
        let _ = q.pop_front();
        assert_eq!(q.peak_len(), 3, "peak should not regress on dequeue");
    }

    #[test]
    fn clear_resets_state() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::Step {
            cursor_id: CursorId(0),
        });
        q.clear();
        assert!(q.is_empty());
        assert_eq!(q.enqueued_total(), 0);
        assert_eq!(q.dequeued_total(), 0);
        assert_eq!(q.peak_len(), 0);
    }

    #[test]
    fn continuation_variant_indices_are_distinct() {
        let step: Continuation<LexicographicWeight> = Continuation::Step {
            cursor_id: CursorId(0),
        };
        let apply: Continuation<LexicographicWeight> = Continuation::ApplyAction {
            cursor_id: CursorId(0),
            action: Box::new(WpdaStepAction::Advance(ready())),
        };
        let resolved: Continuation<LexicographicWeight> = Continuation::Resolved {
            cursor_id: CursorId(0),
        };
        let shell: Continuation<LexicographicWeight> = Continuation::ShellApply {
            cohort_id: CohortId(0),
            action: Box::new(WpdaStepAction::Advance(ready())),
        };
        let barrier: Continuation<LexicographicWeight> = Continuation::StepBarrier;
        assert_eq!(step.variant_index(), 0);
        assert_eq!(apply.variant_index(), 1);
        assert_eq!(resolved.variant_index(), 2);
        assert_eq!(shell.variant_index(), 3);
        assert_eq!(barrier.variant_index(), 4);
    }

    #[test]
    fn is_barrier_distinguishes_step_barrier() {
        let barrier: Continuation<LexicographicWeight> = Continuation::StepBarrier;
        let step: Continuation<LexicographicWeight> = Continuation::Step {
            cursor_id: CursorId(0),
        };
        assert!(barrier.is_barrier());
        assert!(!step.is_barrier());
    }

    #[test]
    fn cohort_id_sentinel_distinct_from_zero() {
        assert_ne!(COHORT_ID_NONE, CohortId(0));
    }

    #[test]
    fn drain_to_barrier_pattern() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::Step {
            cursor_id: CursorId(1),
        });
        q.push_back(Continuation::Resolved {
            cursor_id: CursorId(2),
        });
        q.push_back(Continuation::StepBarrier);
        q.push_back(Continuation::Step {
            cursor_id: CursorId(3),
        });
        let mut steps_before_barrier = 0;
        let mut resolved_before_barrier = 0;
        while let Some(c) = q.pop_front() {
            if c.is_barrier() {
                break;
            }
            match c {
                Continuation::Step { .. } => steps_before_barrier += 1,
                Continuation::Resolved { .. } => resolved_before_barrier += 1,
                _ => {}
            }
        }
        assert_eq!(steps_before_barrier, 1);
        assert_eq!(resolved_before_barrier, 1);
        // Remaining: one Step after the barrier.
        assert_eq!(q.len(), 1);
    }

    #[test]
    fn apply_action_carries_boxed_payload() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::new();
        q.push_back(Continuation::ApplyAction {
            cursor_id: CursorId(7),
            action: Box::new(WpdaStepAction::Push {
                symbol: crate::wpda_runtime::StackSymbolV2::return_symbol(0, 0),
                weight: one(),
                new_state: ready(),
            }),
        });
        match q.pop_front().expect("pop") {
            Continuation::ApplyAction { cursor_id, action } => {
                assert_eq!(cursor_id, CursorId(7));
                matches!(*action, WpdaStepAction::Push { .. });
            }
            _ => panic!("expected ApplyAction"),
        }
    }

    #[test]
    fn with_capacity_avoids_reallocation_for_small_volumes() {
        let mut q: ContinuationQueue<LexicographicWeight> =
            ContinuationQueue::with_capacity(1024);
        for i in 0..1000 {
            q.push_back(Continuation::Step {
                cursor_id: CursorId(i as u32),
            });
        }
        assert_eq!(q.len(), 1000);
        assert_eq!(q.peak_len(), 1000);
        assert_eq!(q.enqueued_total(), 1000);
    }
}
