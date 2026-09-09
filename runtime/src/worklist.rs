//! Node-independent storage for the existing explicit lowering worklist.
//!
//! Jobs remain caller-owned: this module neither walks syntax nor executes a
//! constructor. A classifier returns `None` for an Enter and `Some(arity)` for
//! a continuation, including zero-arity continuations. It must be a stable,
//! side-effect-free classification of the same immutable job on push and pop.
//! Arity arithmetic belongs to the producer and must already be checked where
//! it is derived from untrusted dimensions.
//!
//! Two vectors retain LIFO work and source-ordered values. Three incremental
//! counters make the transition-boundary check constant-time:
//!
//! ```text
//! values + pending_enters + pending_continuations = 1 + pending_operand_count
//! ```
//!
//! Check only after a complete transition, not during its individual pushes
//! and pops. This global equation does not establish local operand readiness;
//! checked value pops remain necessary. The small model
//! `formal/rocq/rho_bridge/theories/RholangWorklistStorage.v` proves counter,
//! ordered-suffix, staged-debt and carrier-mapping laws. It does not prove the
//! caller's scheduling, constructor semantics or Rust allocation behavior.
//!
//! Vector allocation follows the existing lowering storage policy. This type
//! supplies shape/arithmetic errors, not a resource policy or bounded teardown
//! for arbitrary recursively owned `J` or `V`; those remain caller obligations.

/// A rejected storage operation. No error supplies a substitute result value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorklistError {
    CounterOverflow,
    CounterUnderflow,
    ValueUnderflow {
        requested: usize,
        available: usize,
    },
    Deficit {
        values: usize,
        enters: usize,
        continuations: usize,
        operands: usize,
    },
    Unfinished {
        pending_work: usize,
        values: usize,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Counts {
    enters: usize,
    continuations: usize,
    operands: usize,
}

impl Counts {
    fn pushed(self, arity: Option<usize>) -> Result<Self, WorklistError> {
        let mut next = self;
        match arity {
            None => {
                next.enters = self
                    .enters
                    .checked_add(1)
                    .ok_or(WorklistError::CounterOverflow)?;
            },
            Some(arity) => {
                next.continuations = self
                    .continuations
                    .checked_add(1)
                    .ok_or(WorklistError::CounterOverflow)?;
                next.operands = self
                    .operands
                    .checked_add(arity)
                    .ok_or(WorklistError::CounterOverflow)?;
            },
        }
        Ok(next)
    }

    fn popped(self, arity: Option<usize>) -> Result<Self, WorklistError> {
        let mut next = self;
        match arity {
            None => {
                next.enters = self
                    .enters
                    .checked_sub(1)
                    .ok_or(WorklistError::CounterUnderflow)?;
            },
            Some(arity) => {
                next.continuations = self
                    .continuations
                    .checked_sub(1)
                    .ok_or(WorklistError::CounterUnderflow)?;
                next.operands = self
                    .operands
                    .checked_sub(arity)
                    .ok_or(WorklistError::CounterUnderflow)?;
            },
        }
        Ok(next)
    }
}

/// The factored two-stack storage; job and value representations are independent.
pub struct Worklist<J, V> {
    work: Vec<J>,
    values: Vec<V>,
    counts: Counts,
}

impl<J, V> Worklist<J, V> {
    /// Preserve the source lowerer's explicit capacity choice without imposing
    /// that choice on other consumers. This creates empty storage, not a root.
    pub fn with_capacity(work: usize, values: usize) -> Self {
        Self {
            work: Vec::with_capacity(work),
            values: Vec::with_capacity(values),
            counts: Counts::default(),
        }
    }

    /// Check all counter changes before committing either the job or counters.
    pub fn push(
        &mut self,
        job: J,
        classify: impl FnOnce(&J) -> Option<usize>,
    ) -> Result<(), WorklistError> {
        let counts = self.counts.pushed(classify(&job))?;
        self.work.push(job);
        self.counts = counts;
        Ok(())
    }

    /// Pop LIFO work. An empty stack is not an error; a counter mismatch is.
    pub fn pop(
        &mut self,
        classify: impl FnOnce(&J) -> Option<usize>,
    ) -> Result<Option<J>, WorklistError> {
        let Some(job) = self.work.last() else {
            return Ok(None);
        };
        let counts = self.counts.popped(classify(job))?;
        let job = self.work.pop();
        self.counts = counts;
        Ok(job)
    }

    pub fn value(&mut self, value: V) {
        self.values.push(value);
    }

    pub fn value_count(&self) -> usize {
        self.values.len()
    }

    pub fn pop_value(&mut self) -> Result<V, WorklistError> {
        self.values
            .pop()
            .ok_or(WorklistError::ValueUnderflow { requested: 1, available: 0 })
    }

    /// Remove the exact suffix in source order, retaining repeated values.
    /// An underflow leaves both stacks and all counters unchanged.
    pub fn pop_values(&mut self, count: usize) -> Result<Vec<V>, WorklistError> {
        let start = self
            .values
            .len()
            .checked_sub(count)
            .ok_or(WorklistError::ValueUnderflow {
                requested: count,
                available: self.values.len(),
            })?;
        Ok(self.values.split_off(start))
    }

    /// Validate the global debt at a completed transition boundary.
    #[inline]
    pub fn check(&self) -> Result<(), WorklistError> {
        let paid = self
            .values
            .len()
            .checked_add(self.counts.enters)
            .and_then(|n| n.checked_add(self.counts.continuations))
            .ok_or(WorklistError::CounterOverflow)?;
        let owed = self
            .counts
            .operands
            .checked_add(1)
            .ok_or(WorklistError::CounterOverflow)?;
        if paid != owed {
            return Err(WorklistError::Deficit {
                values: self.values.len(),
                enters: self.counts.enters,
                continuations: self.counts.continuations,
                operands: self.counts.operands,
            });
        }
        Ok(())
    }

    /// Consume the storage, returning only a fully drained singleton result.
    /// This is a shape check, not source-admission or publication evidence.
    pub fn finish(mut self) -> Result<V, WorklistError> {
        if !self.work.is_empty() || self.values.len() != 1 {
            return Err(WorklistError::Unfinished {
                pending_work: self.work.len(),
                values: self.values.len(),
            });
        }
        self.check()?;
        self.pop_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, Eq)]
    enum Job {
        Enter(u32),
        Combine(usize),
    }
    fn classify(job: &Job) -> Option<usize> {
        match job {
            Job::Enter(_) => None,
            Job::Combine(n) => Some(*n),
        }
    }
    fn stacks() -> Worklist<Job, u32> {
        Worklist::with_capacity(64, 64)
    }

    #[test]
    fn worklist_zero_arity_is_a_continuation() {
        let mut s = stacks();
        s.push(Job::Combine(0), classify).expect("zero arity");
        assert_eq!(s.counts, Counts { enters: 0, continuations: 1, operands: 0 });
        s.check().expect("zero-ary node still owes one result");
        assert_eq!(s.pop(classify), Ok(Some(Job::Combine(0))));
        assert_eq!(s.pop_values(0), Ok(vec![]));
        s.value(42);
        assert_eq!(s.finish(), Ok(42));
    }

    #[test]
    fn worklist_children_and_repeated_values_keep_source_order() {
        let mut s = stacks();
        s.push(Job::Combine(4), classify).expect("parent");
        for id in [7, 9, 7, 11].into_iter().rev() {
            s.push(Job::Enter(id), classify).expect("child");
        }
        for expected in [7, 9, 7, 11] {
            s.check().expect("complete leaf transition");
            assert_eq!(s.pop(classify), Ok(Some(Job::Enter(expected))));
            s.value(expected);
        }
        s.check().expect("all children ready");
        assert_eq!(s.pop(classify), Ok(Some(Job::Combine(4))));
        assert_eq!(s.pop_values(4), Ok(vec![7, 9, 7, 11]));
        s.value(23);
        assert_eq!(s.finish(), Ok(23));
    }

    #[test]
    fn worklist_staged_replacement_preserves_debt() {
        let mut s = stacks();
        s.push(Job::Combine(1), classify).expect("first stage");
        s.value(8);
        s.check().expect("first stage ready");
        s.pop(classify).expect("pop first stage");
        assert_eq!(s.pop_value(), Ok(8));
        s.push(Job::Combine(2), classify).expect("next stage");
        s.push(Job::Enter(2), classify).expect("second child");
        s.push(Job::Enter(1), classify).expect("first child");
        s.check().expect("staged boundary");
        for value in [1, 2] {
            assert_eq!(s.pop(classify), Ok(Some(Job::Enter(value))));
            s.value(value);
            s.check().expect("leaf boundary");
        }
        s.pop(classify).expect("next stage");
        assert_eq!(s.pop_values(2), Ok(vec![1, 2]));
        s.value(3);
        assert_eq!(s.finish(), Ok(3));
    }

    #[test]
    fn worklist_underflow_leaves_storage_unchanged() {
        let mut s = stacks();
        s.value(4);
        s.value(5);
        let before = s.counts;
        assert_eq!(
            s.pop_values(3),
            Err(WorklistError::ValueUnderflow { requested: 3, available: 2 })
        );
        assert_eq!(s.counts, before);
        assert_eq!(s.pop_values(2), Ok(vec![4, 5]));
        assert_eq!(
            s.pop_value(),
            Err(WorklistError::ValueUnderflow { requested: 1, available: 0 })
        );
    }

    #[test]
    fn worklist_counter_overflow_is_atomic_without_large_allocation() {
        let mut s = stacks();
        s.push(Job::Combine(usize::MAX), classify)
            .expect("representable sum");
        let before = s.counts;
        assert_eq!(s.push(Job::Combine(1), classify), Err(WorklistError::CounterOverflow));
        assert_eq!(s.counts, before);
        assert_eq!(s.work.len(), 1);
        assert_eq!(s.check(), Err(WorklistError::CounterOverflow));
        assert_eq!(s.pop(classify), Ok(Some(Job::Combine(usize::MAX))));
        assert_eq!(s.counts, Counts::default());
    }

    #[test]
    fn worklist_inconsistent_pop_classifier_cannot_partially_mutate() {
        let mut s = stacks();
        s.push(Job::Combine(1), classify).expect("job");
        let before = s.counts;
        assert_eq!(s.pop(|_| Some(2)), Err(WorklistError::CounterUnderflow));
        assert_eq!(s.counts, before);
        assert_eq!(s.work.len(), 1);
        assert_eq!(s.pop(classify), Ok(Some(Job::Combine(1))));
    }

    #[test]
    fn worklist_global_debt_does_not_bypass_operand_check() {
        let mut s = stacks();
        s.push(Job::Enter(1), classify).expect("misordered child");
        s.push(Job::Combine(1), classify)
            .expect("premature continuation");
        s.check().expect("global debt alone passes");
        s.pop(classify).expect("continuation");
        assert_eq!(
            s.pop_value(),
            Err(WorklistError::ValueUnderflow { requested: 1, available: 0 })
        );
    }

    #[test]
    fn worklist_finish_rejects_pending_missing_and_extra_roots() {
        assert_eq!(
            stacks().finish(),
            Err(WorklistError::Unfinished { pending_work: 0, values: 0 })
        );
        let mut pending = stacks();
        pending.value(1);
        pending.push(Job::Enter(2), classify).expect("pending job");
        assert_eq!(pending.finish(), Err(WorklistError::Unfinished { pending_work: 1, values: 1 }));
        let mut extra = stacks();
        extra.value(1);
        extra.value(2);
        assert_eq!(extra.finish(), Err(WorklistError::Unfinished { pending_work: 0, values: 2 }));
    }

    #[test]
    fn worklist_suffix_preserves_unconsumed_prefix() {
        let mut s = stacks();
        for value in [1, 2, 3, 2, 4] {
            s.value(value);
        }
        assert_eq!(s.pop_values(4), Ok(vec![2, 3, 2, 4]));
        assert_eq!(s.finish(), Ok(1));
    }

    #[test]
    fn worklist_deep_iterative_storage_uses_no_recursive_jobs() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut s = stacks();
                for _ in 0..20_000 {
                    s.push(Job::Combine(1), classify).expect("unary parent");
                }
                s.value(0);
                while s.pop(classify).expect("parent").is_some() {
                    let value = s.pop_value().expect("one child");
                    s.value(value + 1);
                    s.check().expect("one completed unary transition");
                }
                assert_eq!(s.finish(), Ok(20_000));
            })
            .expect("small-stack worker")
            .join()
            .expect("iterative stack storage");
    }
}
