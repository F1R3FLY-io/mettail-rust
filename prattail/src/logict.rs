//! LogicT Fair Backtracking Search Framework
//!
//! ## Theory
//!
//! LogicT is a fair backtracking monad implementing the `msplit`-based design
//! of Kiselyov, Shan, Friedman & Sabry (ICFP 2005). Unlike depth-first
//! backtracking (which starves late branches), LogicT's `interleave` operation
//! guarantees that both branches of a disjunction are explored infinitely often,
//! preventing starvation. This is critical for constraint propagation where
//! the search tree may be unbalanced.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                 LogicT Framework                             │
//! │                                                             │
//! │  LogicStream<T>                                              │
//! │    ├── msplit()   — peek at first result + remainder         │
//! │    ├── mzero()    — empty stream (failure)                   │
//! │    ├── mplus()    — concatenation (unfair)                   │
//! │    ├── interleave() — fair disjunction (alternating)         │
//! │    ├── fair_conjoin() — fair conjunction (>>-)               │
//! │    ├── ifte()     — soft cut (if-then-else)                  │
//! │    ├── once()     — commit to first result                   │
//! │    └── gnot()     — negation as finite failure               │
//! │                                                             │
//! │  ConstraintTheory (trait)                                    │
//! │    ├── propagate() — add constraint, check consistency       │
//! │    ├── label()     — generate search choices (LogicStream)   │
//! │    ├── witness()   — extract concrete assignment             │
//! │    └── evaluate()  — check constraint against assignment     │
//! │                                                             │
//! │  TheoryAlgebra<T>                                            │
//! │    ├── RejectSafeAlgebra — bounded Sat/Unsat/DontKnow        │
//! │    └── BooleanAlgebra only when T: DecidableConstraintTheory │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## References
//!
//! - Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005).
//!   "Backtracking, Interleaving, and Terminating Monad Transformers."
//!   ICFP 2005. DOI: 10.1145/1086365.1086390
//! - Hemann, J. & Friedman, D. P. (2013). "μKanren: A Minimal Functional
//!   Core for Relational Programming." Scheme Workshop 2013.

use std::collections::VecDeque;
use std::fmt;

use std::hash::Hash;

// ══════════════════════════════════════════════════════════════════════════════
// LogicStream — Fair backtracking search stream
// ══════════════════════════════════════════════════════════════════════════════

/// Result of evaluating a branch.
///
/// The `Yield` and `Fail` variants are part of the documented LogicT
/// `msplit` protocol (Kiselyov ICFP 2005 §3.2; see
/// `prattail/docs/design/constraint-theories/logict-framework.md:158-170`)
/// but are not currently constructed by `LogicStream::suspend` — that
/// constructor hard-codes `Fork(...)` since the suspension always
/// represents a deferred set of branches. The variants are reserved for
/// future direct-`BranchResult`-producing constructors. Match arms
/// covering them remain in `msplit` and `fair_conjoin` for
/// exhaustiveness.
enum BranchResult<T> {
    /// Yield a value, with additional branches to explore.
    // dead_code: reserved LogicT `msplit` protocol variant (see the module doc above);
    // matched for exhaustiveness but not yet constructed by any `BranchResult` producer.
    #[allow(dead_code)]
    Yield(T, Vec<Branch<T>>),
    /// No result from this branch.
    // dead_code: reserved LogicT `msplit` protocol variant (see the module doc above);
    // matched for exhaustiveness but not yet constructed by any `BranchResult` producer.
    #[allow(dead_code)]
    Fail,
    /// Fork into sub-branches (no immediate result).
    Fork(Vec<Branch<T>>),
}

/// A branch in the search tree.
enum Branch<T> {
    /// A value ready to yield.
    Ready(T),
    /// A suspended computation returning zero or more results.
    Suspended(Box<dyn FnOnce() -> BranchResult<T> + Send>),
}

/// Fair backtracking search stream.
///
/// Implements `msplit`-based LogicT (Kiselyov et al., ICFP 2005).
/// Uses an explicit `VecDeque`-based branch queue for round-robin
/// fair scheduling, following the same philosophy as the trampoline
/// parser (explicit stack, no recursion).
///
/// # Fairness Guarantee
///
/// `interleave(a, b)` alternates between branches from `a` and `b`,
/// ensuring both are explored infinitely often. This prevents
/// starvation when one branch produces results faster than the other.
pub struct LogicStream<T> {
    /// Branch queue for round-robin fair scheduling.
    branches: VecDeque<Branch<T>>,
}

/// Values observed from a bounded stream prefix together with evidence about
/// whether the implementation stream was completely exhausted.
///
/// `exhausted == false` means that at least one additional result exists beyond
/// `values`; it must never be interpreted as semantic unsatisfiability.  Even
/// `exhausted == true` proves only that this implementation stream ended.  A
/// constraint theory still needs an independent completeness contract before
/// absence of a witness can become a classical negative conclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedCollection<T> {
    /// The prefix retained by the caller, in fair-search order.
    pub values: Vec<T>,
    /// Whether the consumed implementation stream had no further result.
    pub exhausted: bool,
}

impl<T: fmt::Debug> fmt::Debug for LogicStream<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LogicStream({} branches)", self.branches.len())
    }
}

impl<T: Send + 'static> LogicStream<T> {
    // ── Constructors ────────────────────────────────────────────────────

    /// Create an empty stream (failure / mzero).
    ///
    /// The identity element for `mplus` and `interleave`.
    pub fn empty() -> Self {
        LogicStream { branches: VecDeque::new() }
    }

    /// Create a stream with a single result.
    pub fn unit(value: T) -> Self {
        let mut branches = VecDeque::with_capacity(1);
        branches.push_back(Branch::Ready(value));
        LogicStream { branches }
    }

    /// Create a stream from an iterator of values.
    pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Self {
        let branches: VecDeque<Branch<T>> = iter.into_iter().map(Branch::Ready).collect();
        LogicStream { branches }
    }

    /// Create a stream from a suspended computation.
    pub fn suspend(f: impl FnOnce() -> LogicStream<T> + Send + 'static) -> Self {
        let mut branches = VecDeque::with_capacity(1);
        branches.push_back(Branch::Suspended(Box::new(move || {
            let stream = f();
            Fork(stream.branches.into_iter().collect())
        })));
        LogicStream { branches }
    }

    // ── Core operations (all derived from msplit) ───────────────────────

    /// Peek at the first result and the remaining stream.
    ///
    /// This is the fundamental primitive from which all other LogicT
    /// operations are derived. Returns `None` if the stream is exhausted,
    /// or `Some((first_result, remaining_stream))`.
    ///
    /// # Implementation
    ///
    /// Processes branches from the front of the queue:
    /// - `Ready(v)`: return immediately with `v` and remaining branches
    /// - `Suspended(f)`: evaluate `f()` and handle the result:
    ///   - `Yield(v, more)`: return `v`, enqueue `more` at back
    ///   - `Fail`: skip this branch, continue to next
    ///   - `Fork(branches)`: enqueue all at back, continue to next
    pub fn msplit(mut self) -> Option<(T, LogicStream<T>)> {
        while let Some(branch) = self.branches.pop_front() {
            match branch {
                Branch::Ready(value) => {
                    return Some((value, self));
                },
                Branch::Suspended(f) => match f() {
                    BranchResult::Yield(value, more) => {
                        for b in more {
                            self.branches.push_back(b);
                        }
                        return Some((value, self));
                    },
                    BranchResult::Fail => {
                        continue;
                    },
                    BranchResult::Fork(more) => {
                        for b in more {
                            self.branches.push_back(b);
                        }
                        continue;
                    },
                },
            }
        }
        None
    }

    /// Concatenation (unfair disjunction).
    ///
    /// Appends all branches of `other` after all branches of `self`.
    /// This is NOT fair — `other`'s branches are explored only after
    /// `self` is exhausted. Use `interleave` for fair disjunction.
    pub fn mplus(mut self, other: LogicStream<T>) -> LogicStream<T> {
        self.branches.extend(other.branches);
        self
    }

    /// Fair disjunction (alternating interleave).
    ///
    /// Alternates branches from `self` and `other` in round-robin
    /// fashion, ensuring both streams are explored infinitely often.
    ///
    /// # Fairness
    ///
    /// For streams A = [a₁, a₂, a₃, ...] and B = [b₁, b₂, b₃, ...],
    /// `interleave(A, B)` produces [a₁, b₁, a₂, b₂, a₃, b₃, ...].
    /// Both A and B are explored at each step.
    pub fn interleave(self, other: LogicStream<T>) -> LogicStream<T> {
        let mut result = VecDeque::with_capacity(self.branches.len() + other.branches.len());
        let mut iter_a = self.branches.into_iter();
        let mut iter_b = other.branches.into_iter();

        loop {
            match (iter_a.next(), iter_b.next()) {
                (Some(a), Some(b)) => {
                    result.push_back(a);
                    result.push_back(b);
                },
                (Some(a), None) => {
                    result.push_back(a);
                    result.extend(iter_a);
                    break;
                },
                (None, Some(b)) => {
                    result.push_back(b);
                    result.extend(iter_b);
                    break;
                },
                (None, None) => break,
            }
        }

        LogicStream { branches: result }
    }

    /// Fair conjunction (>>- / fair bind).
    ///
    /// Applies `f` to each result from `self`, then interleaves all
    /// resulting streams. This prevents `f` applied to the first result
    /// from starving results from later values.
    ///
    /// Equivalent to: `fold(self.map(f), empty, interleave)`
    pub fn fair_conjoin<U: Send + 'static>(
        self,
        f: impl Fn(T) -> LogicStream<U> + Send + 'static,
    ) -> LogicStream<U> {
        let mut accumulated = LogicStream::<U>::empty();

        for branch in self.branches {
            let stream = match branch {
                Branch::Ready(value) => f(value),
                Branch::Suspended(suspended) => {
                    // Evaluate the suspended computation, then apply f
                    match suspended() {
                        BranchResult::Yield(value, more) => {
                            let mut result = f(value);
                            // Process remaining branches from the suspension
                            for b in more {
                                if let Branch::Ready(v) = b {
                                    result = result.interleave(f(v));
                                }
                            }
                            result
                        },
                        BranchResult::Fail => LogicStream::empty(),
                        BranchResult::Fork(branches) => {
                            let mut result = LogicStream::<U>::empty();
                            for b in branches {
                                if let Branch::Ready(v) = b {
                                    result = result.interleave(f(v));
                                }
                            }
                            result
                        },
                    }
                },
            };
            accumulated = accumulated.interleave(stream);
        }

        accumulated
    }

    /// Soft cut (if-then-else).
    ///
    /// If `self` produces at least one result, apply `then_fn` to each
    /// result. Otherwise, return `else_stream`.
    ///
    /// This is Prolog's soft cut (`*->`): commit to the "then" branch
    /// if the test succeeds, but don't cut within the "then" branch.
    pub fn ifte<U: Send + 'static>(
        self,
        then_fn: impl Fn(T) -> LogicStream<U> + Send + 'static,
        else_stream: LogicStream<U>,
    ) -> LogicStream<U> {
        match self.msplit() {
            None => else_stream,
            Some((first, rest)) => {
                let first_results = then_fn(first);
                let rest_results = rest.fair_conjoin(then_fn);
                first_results.interleave(rest_results)
            },
        }
    }

    /// Commit to first result only.
    ///
    /// Returns a stream containing at most one element: the first
    /// result from `self`. All other results are discarded.
    ///
    /// This is Prolog's cut (`!`): take the first solution and stop.
    pub fn once(self) -> LogicStream<T> {
        match self.msplit() {
            None => LogicStream::empty(),
            Some((first, _rest)) => LogicStream::unit(first),
        }
    }

    /// Negation as finite failure.
    ///
    /// Succeeds (with `()`) if `self` produces no results.
    /// Fails if `self` produces any result.
    ///
    /// This implements the closed-world assumption: absence of evidence
    /// is treated as evidence of absence.
    pub fn gnot(self) -> LogicStream<()> {
        match self.msplit() {
            None => LogicStream::unit(()),
            Some(_) => LogicStream::empty(),
        }
    }

    /// Map a function over all results in the stream.
    ///
    /// Eagerly evaluates suspended branches during mapping. This is
    /// simpler than trying to compose closures and preserves all results.
    pub fn map<U: Send + 'static>(self, f: impl Fn(T) -> U + Send + 'static) -> LogicStream<U> {
        // Eagerly evaluate all branches to Ready values, then map.
        let all_values = self.collect_all();
        LogicStream::from_iter(all_values.into_iter().map(f))
    }

    /// Filter results by a predicate.
    ///
    /// Eagerly evaluates suspended branches during filtering. This is
    /// simpler than composing closures and preserves fairness by
    /// processing all branches before filtering.
    pub fn filter(self, pred: impl Fn(&T) -> bool + Send + 'static) -> LogicStream<T> {
        let all_values = self.collect_all();
        LogicStream::from_iter(all_values.into_iter().filter(|v| pred(v)))
    }

    /// Collect a bounded prefix and retain implementation-exhaustion evidence.
    ///
    /// The method probes at most one result beyond the retained prefix.  That
    /// probe is necessary to distinguish a stream containing exactly `limit`
    /// results from a truncated stream.  The stream is consumed, so the probed
    /// value is intentionally discarded rather than exposed without budget.
    pub fn collect_bounded_with_status(self, limit: usize) -> BoundedCollection<T> {
        let mut values = Vec::with_capacity(limit.min(64));
        let mut stream = self;

        while values.len() < limit {
            match stream.msplit() {
                Some((value, rest)) => {
                    values.push(value);
                    stream = rest;
                },
                None => {
                    return BoundedCollection { values, exhausted: true };
                },
            }
        }

        let exhausted = stream.msplit().is_none();
        BoundedCollection { values, exhausted }
    }

    /// Collect all results into a Vec (bounded by `limit`).
    ///
    /// Consumes the stream, collecting up to `limit` results. This
    /// prevents unbounded allocation from infinite streams.  Call
    /// [`LogicStream::collect_bounded_with_status`] whenever the distinction
    /// between exhaustion and truncation affects correctness.
    pub fn collect_bounded(self, limit: usize) -> Vec<T> {
        self.collect_bounded_with_status(limit).values
    }

    /// Collect all results into a Vec.
    ///
    /// Warning: this will loop forever on infinite streams.
    /// Prefer `collect_bounded` when the stream size is unknown.
    pub fn collect_all(self) -> Vec<T> {
        let mut results = Vec::new();
        let mut stream = self;

        loop {
            match stream.msplit() {
                Some((value, rest)) => {
                    results.push(value);
                    stream = rest;
                },
                None => break,
            }
        }

        results
    }

    /// Check if the stream is empty (has no results).
    ///
    /// Consumes the stream. Use `msplit` if you need to preserve results.
    pub fn is_empty(self) -> bool {
        self.msplit().is_none()
    }

    /// Count the number of results (bounded).
    pub fn count_bounded(self, limit: usize) -> usize {
        self.collect_bounded(limit).len()
    }
}

// Use a private import for the Fork variant to avoid cluttering the namespace
use BranchResult::Fork;

// ══════════════════════════════════════════════════════════════════════════════
// Iterator integration
// ══════════════════════════════════════════════════════════════════════════════

/// Iterator adapter for LogicStream.
///
/// Yields results one at a time via `msplit`. Each call to `next()`
/// processes branches until a result is found or the stream is exhausted.
pub struct LogicStreamIter<T> {
    stream: LogicStream<T>,
}

impl<T: Send + 'static> Iterator for LogicStreamIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let stream = std::mem::replace(&mut self.stream, LogicStream::empty());
        match stream.msplit() {
            Some((value, rest)) => {
                self.stream = rest;
                Some(value)
            },
            None => None,
        }
    }
}

impl<T: Send + 'static> IntoIterator for LogicStream<T> {
    type Item = T;
    type IntoIter = LogicStreamIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        LogicStreamIter { stream: self }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// ConstraintTheory trait
// ══════════════════════════════════════════════════════════════════════════════

/// A pluggable constraint domain for predicated type checking.
///
/// Theories implement propagation + labeling; LogicT handles search.
/// This enables any user-defined language to plug in domain-specific
/// constraint solvers (unification, lattice operations, custom matching)
/// through the reject-safe algebra layer. Classical SFA operations additionally
/// require [`DecidableConstraintTheory`].
///
/// # Design
///
/// The trait separates two concerns:
/// - **Propagation** (`propagate`): deterministic constraint narrowing.
///   Some theories completely decide conjunctions during propagation, but
///   arbitrary Boolean predicates require the separate exactness contract.
/// - **Labeling** (`label`): non-deterministic search choices. For
///   theories requiring search (e.g., unification with multiple matches),
///   `label()` produces a `LogicStream` of constraint alternatives.
///
/// # Type Parameters
///
/// - `Constraint`: guard predicates in this theory's domain
/// - `Assignment`: concrete witness values (domain elements)
/// - `Store`: accumulated constraint state
pub trait ConstraintTheory: Clone + fmt::Debug + Send + Sync + 'static {
    /// Constraint representation (guard predicates in this theory).
    type Constraint: Clone + fmt::Debug + Eq + std::hash::Hash + Send + Sync + 'static;
    /// Concrete domain element (witness type).
    type Assignment: Clone + fmt::Debug + Send + Sync + 'static;
    /// Constraint store accumulating added constraints.
    type Store: Clone + fmt::Debug + Send + Sync + 'static;

    /// Create an empty (unconstrained) store.
    fn empty_store(&self) -> Self::Store;

    /// Add constraint to store and propagate. Returns `None` if inconsistent.
    fn propagate(&self, store: &Self::Store, c: &Self::Constraint) -> Option<Self::Store>;

    /// Check store consistency without adding constraints.
    fn is_consistent(&self, store: &Self::Store) -> bool;

    /// Extract a witness assignment from a consistent store.
    ///
    /// Returns `None` if store is inconsistent or incomplete (needs labeling).
    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment>;

    /// Generate labeling choices for search (used by LogicT).
    ///
    /// A theory whose propagation is complete may return
    /// `LogicStream::empty()`. An empty or exhausted implementation stream is
    /// not, by itself, a semantic completeness certificate; exact classical
    /// reasoning additionally requires [`DecidableConstraintTheory`]. Other
    /// theories produce a fair stream of variable assignments to search over.
    fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint>;

    /// Evaluate whether an assignment satisfies a constraint.
    fn evaluate(&self, c: &Self::Constraint, assignment: &Self::Assignment) -> bool;

    /// Evaluate a constraint without erasing an indeterminate result.
    ///
    /// The default is exact for theories whose `evaluate` operation is total.
    /// Domains with overflow, solver uncertainty, partial observations, or any
    /// other source of indeterminacy must override this method and return `None`
    /// rather than choosing a Boolean side.  [`TheoryAlgebra`] composes this
    /// result through the full predicate before applying the fail-closed policy,
    /// so `Not(unknown)` remains unknown instead of becoming accepted.
    fn evaluate_checked(
        &self,
        c: &Self::Constraint,
        assignment: &Self::Assignment,
    ) -> Option<bool> {
        Some(self.evaluate(c, assignment))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// QuantifiedFormula — FOL formulas for guard evaluation
// ══════════════════════════════════════════════════════════════════════════════

/// A first-order logic formula for quantified guard evaluation via LogicT.
///
/// Used to express predicates like `∀y. (reachable(x,y) ⇒ safe(y))` in
/// behavioral guards. The evaluator resolves atoms against Ascent fixpoint
/// relations and uses LogicT's `gnot`/`fair_conjoin` for quantifiers.
///
/// # Evaluation Strategy
///
/// - `Atom`: resolved by querying the Ascent relation fixpoint
/// - `And`/`Or`/`Not`: standard short-circuit Boolean evaluation
/// - `Implies(a, b)`: desugared to `Or(Not(a), b)`
/// - `ForAll`: domain enumeration + check body for ALL elements
/// - `Exists`: domain enumeration + check body for ANY element
///
/// # References
///
/// - Gap 3 in `docs/design/predicated-types.md` §22
/// - Strategy 3 (LogicT evaluation) selected for composability
pub enum QuantifiedFormula {
    /// Atomic relation query: `R(args)` — checks Ascent fixpoint.
    Atom {
        relation: String,
        args: Vec<QuantifiedArg>,
    },
    /// Conjunction: `a ∧ b`
    And(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    /// Disjunction: `a ∨ b`
    Or(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    /// Negation: `¬a`
    Not(Box<QuantifiedFormula>),
    /// Implication: `a ⇒ b` (sugar for `¬a ∨ b`)
    Implies(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    /// Universal quantification: `∀var ∈ domain. body`
    ForAll {
        var: String,
        domain: QuantifiedDomain,
        body: Box<QuantifiedFormula>,
    },
    /// Existential quantification: `∃var ∈ domain. body`
    Exists {
        var: String,
        domain: QuantifiedDomain,
        body: Box<QuantifiedFormula>,
    },
}

/// Domain specification for quantified variables.
///
/// Determines the set of values a quantified variable ranges over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedDomain {
    /// All tuples in an Ascent relation (finite, decidable — T1/T2).
    Relation(String),
    /// Bounded iteration over a relation (semi-decidable — T3).
    /// Enumerates at most `limit` tuples before concluding.
    Bounded { relation: String, limit: usize },
}

/// An argument to an atomic relation query in a quantified formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedArg {
    /// A variable reference (resolved from the environment).
    Var(String),
    /// A literal constant value.
    Constant(String),
}

impl QuantifiedFormula {
    /// Convenience: create an atom with the given relation and args.
    pub fn atom(relation: impl Into<String>, args: Vec<QuantifiedArg>) -> Self {
        QuantifiedFormula::Atom { relation: relation.into(), args }
    }

    /// Convenience: `a ∧ b`
    pub fn and(a: QuantifiedFormula, b: QuantifiedFormula) -> Self {
        QuantifiedFormula::And(Box::new(a), Box::new(b))
    }

    /// Convenience: `a ∨ b`
    pub fn or(a: QuantifiedFormula, b: QuantifiedFormula) -> Self {
        QuantifiedFormula::Or(Box::new(a), Box::new(b))
    }

    /// Convenience: `¬a`
    pub fn not(a: QuantifiedFormula) -> Self {
        QuantifiedFormula::Not(Box::new(a))
    }

    /// Convenience: `a ⇒ b`
    pub fn implies(a: QuantifiedFormula, b: QuantifiedFormula) -> Self {
        QuantifiedFormula::Implies(Box::new(a), Box::new(b))
    }

    /// Convenience: `∀var ∈ relation. body`
    pub fn forall(
        var: impl Into<String>,
        domain: QuantifiedDomain,
        body: QuantifiedFormula,
    ) -> Self {
        QuantifiedFormula::ForAll {
            var: var.into(),
            domain,
            body: Box::new(body),
        }
    }

    /// Convenience: `∃var ∈ relation. body`
    pub fn exists(
        var: impl Into<String>,
        domain: QuantifiedDomain,
        body: QuantifiedFormula,
    ) -> Self {
        QuantifiedFormula::Exists {
            var: var.into(),
            domain,
            body: Box::new(body),
        }
    }

    /// Collect all free variables referenced in this formula (not bound by a quantifier).
    pub fn free_vars(&self) -> std::collections::HashSet<String> {
        enum Task<'formula> {
            Visit(&'formula QuantifiedFormula),
            LeaveBinding(&'formula str),
        }

        let mut free = std::collections::HashSet::new();
        let mut bound_counts = std::collections::HashMap::<&str, usize>::new();
        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(QuantifiedFormula::Atom { args, .. }) => {
                    for arg in args {
                        if let QuantifiedArg::Var(variable) = arg {
                            if !bound_counts.contains_key(variable.as_str()) {
                                free.insert(variable.clone());
                            }
                        }
                    }
                },
                Task::Visit(
                    QuantifiedFormula::And(left, right)
                    | QuantifiedFormula::Or(left, right)
                    | QuantifiedFormula::Implies(left, right),
                ) => {
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(QuantifiedFormula::Not(inner)) => tasks.push(Task::Visit(inner)),
                Task::Visit(
                    QuantifiedFormula::ForAll { var, body, .. }
                    | QuantifiedFormula::Exists { var, body, .. },
                ) => {
                    *bound_counts.entry(var).or_default() += 1;
                    tasks.push(Task::LeaveBinding(var));
                    tasks.push(Task::Visit(body));
                },
                Task::LeaveBinding(variable) => {
                    let count = bound_counts
                        .get_mut(variable)
                        .expect("quantified free-variable PDA lost binding");
                    *count -= 1;
                    if *count == 0 {
                        bound_counts.remove(variable);
                    }
                },
            }
        }
        free
    }
}

impl QuantifiedArg {
    /// Convenience: create a variable argument.
    pub fn var(name: impl Into<String>) -> Self {
        QuantifiedArg::Var(name.into())
    }

    /// Convenience: create a constant argument.
    pub fn constant(value: impl Into<String>) -> Self {
        QuantifiedArg::Constant(value.into())
    }
}

impl fmt::Display for QuantifiedDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuantifiedDomain::Relation(name) => write!(f, "{}", name),
            QuantifiedDomain::Bounded { relation, limit } => {
                write!(f, "{}[≤{}]", relation, limit)
            },
        }
    }
}

impl fmt::Display for QuantifiedArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuantifiedArg::Var(v) => write!(f, "{}", v),
            QuantifiedArg::Constant(c) => write!(f, "'{}'", c),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// evaluate_quantified — FOL evaluator over Ascent fixpoint relations
// ══════════════════════════════════════════════════════════════════════════════

/// Evaluate a quantified formula against Ascent fixpoint relations.
///
/// # Arguments
///
/// * `formula` — The FOL formula to evaluate.
/// * `env` — Current variable bindings (var name → resolved value).
/// * `relation_query` — Callback: `(relation_name, resolved_args) → bool`.
///   Returns true if the tuple exists in the named Ascent relation.
/// * `domain_enumerate` — Callback: `(relation_name) → Vec<Vec<String>>`.
///   Returns all tuples in the named relation (for quantifier iteration).
/// * `bound` — Maximum tuples to enumerate for `Bounded` domains (T3 safety).
///
/// # Evaluation Rules
///
/// | Formula | Evaluation |
/// |---------|------------|
/// | `Atom(R, args)` | Resolve args from env, call `relation_query(R, resolved)` |
/// | `And(a, b)` | `eval(a) && eval(b)` (short-circuit) |
/// | `Or(a, b)` | `eval(a) \|\| eval(b)` (short-circuit) |
/// | `Not(a)` | `!eval(a)` |
/// | `Implies(a, b)` | `!eval(a) \|\| eval(b)` |
/// | `ForAll(var, dom, body)` | `∀ tuple ∈ dom: eval(body[var↦tuple])` |
/// | `Exists(var, dom, body)` | `∃ tuple ∈ dom: eval(body[var↦tuple])` |
///
/// A `Bounded` domain retains whether enumeration was truncated. A witnessed
/// existential or counterexampled universal may decide early; otherwise
/// truncation becomes [`TriState::Unknown`]. This Boolean compatibility wrapper
/// collapses the complete formula only after three-valued evaluation, so an
/// enclosing negation cannot turn uncertainty into acceptance.
///
/// # Example
///
/// ```rust
/// use mettail_prattail::logict::{QuantifiedFormula, QuantifiedArg, QuantifiedDomain, evaluate_quantified};
/// use std::collections::HashMap;
///
/// let formula = QuantifiedFormula::forall(
///     "x",
///     QuantifiedDomain::Relation("items".into()),
///     QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
/// );
///
/// let env = HashMap::new();
/// let result = evaluate_quantified(
///     &formula,
///     &env,
///     &|rel, args| rel == "positive" && args[0].parse::<i32>().map_or(false, |n| n > 0),
///     &|rel| match rel { "items" => vec![vec!["1".into()], vec!["2".into()], vec!["3".into()]], _ => vec![] },
///     1000,
/// );
/// assert!(result);
/// ```
pub fn evaluate_quantified<F, G>(
    formula: &QuantifiedFormula,
    env: &std::collections::HashMap<String, String>,
    relation_query: &F,
    domain_enumerate: &G,
    bound: usize,
) -> bool
where
    F: Fn(&str, &[String]) -> bool,
    G: Fn(&str) -> Vec<Vec<String>>,
{
    evaluate_quantified_3v(formula, env, relation_query, domain_enumerate, bound).into_safe_bool()
}

/// Evaluate a quantified formula without erasing bounded-domain truncation.
///
/// A finite counterexample decides `forall` as false, and a finite witness
/// decides `exists` as true.  If the enumerated prefix is truncated before
/// either event, the result is [`TriState::Unknown`].  Callers that require a
/// Boolean admission decision must collapse only after evaluating the complete
/// formula, using [`TriState::into_safe_bool`], so outer negation cannot turn an
/// unknown subformula into acceptance.
pub fn evaluate_quantified_3v<F, G>(
    formula: &QuantifiedFormula,
    env: &std::collections::HashMap<String, String>,
    relation_query: &F,
    domain_enumerate: &G,
    bound: usize,
) -> TriState
where
    F: Fn(&str, &[String]) -> bool,
    G: Fn(&str) -> Vec<Vec<String>>,
{
    evaluate_quantified_pda(formula, env, relation_query, domain_enumerate, bound)
}

#[derive(Clone, Copy)]
enum FormulaBinary {
    And,
    Or,
    Implies,
}

#[derive(Clone, Copy)]
enum FormulaQuantifier {
    ForAll,
    Exists,
}

trait QuantifiedTruth: Copy {
    fn from_bool(value: bool) -> Self;
    fn not(self) -> Self;
    fn binary_short_circuit(self, operation: FormulaBinary) -> Option<Self>;
    fn combine(self, right: Self, operation: FormulaBinary) -> Self;
    fn quantifier_identity(quantifier: FormulaQuantifier) -> Self;
    fn accumulate(self, value: Self, quantifier: FormulaQuantifier) -> Self;
    fn quantifier_is_decided(self, quantifier: FormulaQuantifier) -> bool;
    fn finish_quantifier(self, quantifier: FormulaQuantifier, exhausted: bool) -> Self;
}

fn evaluate_quantified_pda<R, F, G>(
    formula: &QuantifiedFormula,
    env: &std::collections::HashMap<String, String>,
    relation_query: &F,
    domain_enumerate: &G,
    bound: usize,
) -> R
where
    R: QuantifiedTruth,
    F: Fn(&str, &[String]) -> bool,
    G: Fn(&str) -> Vec<Vec<String>>,
{
    enum Task<'formula, R> {
        Visit(&'formula QuantifiedFormula),
        Not,
        BinaryAfterLeft {
            operation: FormulaBinary,
            right: &'formula QuantifiedFormula,
        },
        Combine {
            operation: FormulaBinary,
            left: R,
        },
        BeginQuantifier {
            quantifier: FormulaQuantifier,
            var: &'formula String,
            domain: &'formula QuantifiedDomain,
            body: &'formula QuantifiedFormula,
        },
        QuantifierContinue {
            quantifier: FormulaQuantifier,
            var: &'formula String,
            body: &'formula QuantifiedFormula,
            tuples: Vec<Vec<String>>,
            exhausted: bool,
            next_index: usize,
            previous: Option<String>,
            accumulated: R,
        },
    }

    fn restore_binding(
        env: &mut std::collections::HashMap<String, String>,
        variable: &str,
        previous: Option<&String>,
    ) {
        match previous {
            Some(value) => {
                env.insert(variable.to_owned(), value.clone());
            },
            None => {
                env.remove(variable);
            },
        }
    }

    fn finish_binding(
        env: &mut std::collections::HashMap<String, String>,
        variable: &str,
        previous: Option<String>,
    ) {
        match previous {
            Some(value) => {
                env.insert(variable.to_owned(), value);
            },
            None => {
                env.remove(variable);
            },
        }
    }

    let mut runtime_env = env.clone();
    let mut tasks = vec![Task::Visit(formula)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(QuantifiedFormula::Atom { relation, args }) => {
                let resolved = args
                    .iter()
                    .map(|arg| match arg {
                        QuantifiedArg::Var(variable) => runtime_env.get(variable).cloned(),
                        QuantifiedArg::Constant(constant) => Some(constant.clone()),
                    })
                    .collect::<Option<Vec<_>>>();
                values.push(R::from_bool(
                    resolved.is_some_and(|resolved| relation_query(relation, &resolved)),
                ));
            },
            Task::Visit(QuantifiedFormula::And(left, right)) => {
                tasks.push(Task::BinaryAfterLeft { operation: FormulaBinary::And, right });
                tasks.push(Task::Visit(left));
            },
            Task::Visit(QuantifiedFormula::Or(left, right)) => {
                tasks.push(Task::BinaryAfterLeft { operation: FormulaBinary::Or, right });
                tasks.push(Task::Visit(left));
            },
            Task::Visit(QuantifiedFormula::Not(inner)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(inner));
            },
            Task::Visit(QuantifiedFormula::Implies(left, right)) => {
                tasks.push(Task::BinaryAfterLeft { operation: FormulaBinary::Implies, right });
                tasks.push(Task::Visit(left));
            },
            Task::Visit(QuantifiedFormula::ForAll { var, domain, body }) => {
                tasks.push(Task::BeginQuantifier {
                    quantifier: FormulaQuantifier::ForAll,
                    var,
                    domain,
                    body,
                });
            },
            Task::Visit(QuantifiedFormula::Exists { var, domain, body }) => {
                tasks.push(Task::BeginQuantifier {
                    quantifier: FormulaQuantifier::Exists,
                    var,
                    domain,
                    body,
                });
            },
            Task::BeginQuantifier { quantifier, var, domain, body } => {
                let enumeration = enumerate_domain(domain, domain_enumerate, bound);
                let accumulated = R::quantifier_identity(quantifier);
                if enumeration.tuples.is_empty() {
                    values.push(accumulated.finish_quantifier(quantifier, enumeration.exhausted));
                    continue;
                }

                let previous = runtime_env.get(var).cloned();
                if let Some(value) = enumeration.tuples[0].first() {
                    runtime_env.insert(var.clone(), value.clone());
                }
                tasks.push(Task::QuantifierContinue {
                    quantifier,
                    var,
                    body,
                    tuples: enumeration.tuples,
                    exhausted: enumeration.exhausted,
                    next_index: 1,
                    previous,
                    accumulated,
                });
                tasks.push(Task::Visit(body));
            },
            Task::Not => {
                let value = values.pop().expect("quantified evaluator lost negand");
                values.push(value.not());
            },
            Task::BinaryAfterLeft { operation, right } => {
                let left = values.pop().expect("quantified evaluator lost binary LHS");
                if let Some(result) = left.binary_short_circuit(operation) {
                    values.push(result);
                } else {
                    tasks.push(Task::Combine { operation, left });
                    tasks.push(Task::Visit(right));
                }
            },
            Task::Combine { operation, left } => {
                let right = values.pop().expect("quantified evaluator lost binary RHS");
                values.push(left.combine(right, operation));
            },
            Task::QuantifierContinue {
                quantifier,
                var,
                body,
                tuples,
                exhausted,
                next_index,
                previous,
                accumulated,
            } => {
                let value = values
                    .pop()
                    .expect("quantified evaluator lost quantified body value");
                let accumulated = accumulated.accumulate(value, quantifier);
                if accumulated.quantifier_is_decided(quantifier) {
                    finish_binding(&mut runtime_env, var, previous);
                    values.push(accumulated);
                    continue;
                }
                if next_index == tuples.len() {
                    finish_binding(&mut runtime_env, var, previous);
                    values.push(accumulated.finish_quantifier(quantifier, exhausted));
                    continue;
                }

                let next_value = tuples[next_index].first().cloned();
                restore_binding(&mut runtime_env, var, previous.as_ref());
                if let Some(value) = next_value {
                    runtime_env.insert(var.clone(), value);
                }
                tasks.push(Task::QuantifierContinue {
                    quantifier,
                    var,
                    body,
                    tuples,
                    exhausted,
                    next_index: next_index + 1,
                    previous,
                    accumulated,
                });
                tasks.push(Task::Visit(body));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("quantified formula evaluator produced no value")
}

struct DomainEnumeration {
    tuples: Vec<Vec<String>>,
    exhausted: bool,
}

/// Enumerate tuples from a domain while retaining whether the declared bound
/// truncated the finite relation snapshot.
fn enumerate_domain<G>(
    domain: &QuantifiedDomain,
    domain_enumerate: &G,
    default_bound: usize,
) -> DomainEnumeration
where
    G: Fn(&str) -> Vec<Vec<String>>,
{
    match domain {
        QuantifiedDomain::Relation(name) => DomainEnumeration {
            tuples: domain_enumerate(name),
            exhausted: true,
        },
        QuantifiedDomain::Bounded { relation, limit } => {
            let all = domain_enumerate(relation);
            let effective_limit = (*limit).min(default_bound);
            let exhausted = all.len() <= effective_limit;
            DomainEnumeration {
                tuples: all.into_iter().take(effective_limit).collect(),
                exhausted,
            }
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TriState evaluation — three-valued logic for theory-guided guards
// ══════════════════════════════════════════════════════════════════════════════

/// Three-valued result for theory-guided quantified evaluation.
///
/// Phase 6 (predicated types): the standard `evaluate_quantified` returns
/// a Boolean. When the underlying domain is undecidable (e.g., Presburger
/// over an infinite domain) or the search exhausts its bound without
/// finding a witness, "unknown" is the only honest answer. The
/// theory-guided evaluator uses `TriState::Unknown` to signal this case
/// so that callers can fall back to a conservative default (Phase 7
/// T3 codegen uses `Unknown → False`, the spec's safe choice).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TriState {
    /// The formula is definitely true under the given environment.
    True,
    /// The formula is definitely false under the given environment.
    False,
    /// The formula's truth value could not be determined within the
    /// search bound or by the theory's decision procedure.
    Unknown,
}

impl TriState {
    /// Three-valued conjunction (Kleene strong logic).
    pub fn and(self, other: TriState) -> TriState {
        use TriState::*;
        match (self, other) {
            (False, _) | (_, False) => False,
            (True, True) => True,
            _ => Unknown,
        }
    }

    /// Three-valued disjunction (Kleene strong logic).
    pub fn or(self, other: TriState) -> TriState {
        use TriState::*;
        match (self, other) {
            (True, _) | (_, True) => True,
            (False, False) => False,
            _ => Unknown,
        }
    }

    /// Three-valued negation.
    pub fn not(self) -> TriState {
        use TriState::*;
        match self {
            True => False,
            False => True,
            Unknown => Unknown,
        }
    }

    /// Three-valued implication: `a ⟹ b ≡ ¬a ∨ b`.
    pub fn implies(self, other: TriState) -> TriState {
        self.not().or(other)
    }

    /// Conservative collapse: `True → true`, anything else → false.
    /// Used by T3 codegen for the "safe-fail" default.
    pub fn into_safe_bool(self) -> bool {
        matches!(self, TriState::True)
    }
}

impl From<bool> for TriState {
    fn from(b: bool) -> Self {
        if b {
            TriState::True
        } else {
            TriState::False
        }
    }
}

impl QuantifiedTruth for TriState {
    fn from_bool(value: bool) -> Self {
        value.into()
    }

    fn not(self) -> Self {
        TriState::not(self)
    }

    fn binary_short_circuit(self, operation: FormulaBinary) -> Option<Self> {
        match (operation, self) {
            (FormulaBinary::And, TriState::False) => Some(TriState::False),
            (FormulaBinary::Or, TriState::True) => Some(TriState::True),
            // Preserve the theory evaluator's eager RHS evaluation for
            // three-valued implication; unlike Boolean implication, `False`
            // did not previously short-circuit this path.
            _ => None,
        }
    }

    fn combine(self, right: Self, operation: FormulaBinary) -> Self {
        match operation {
            FormulaBinary::And => self.and(right),
            FormulaBinary::Or => self.or(right),
            FormulaBinary::Implies => self.implies(right),
        }
    }

    fn quantifier_identity(quantifier: FormulaQuantifier) -> Self {
        match quantifier {
            FormulaQuantifier::ForAll => TriState::True,
            FormulaQuantifier::Exists => TriState::False,
        }
    }

    fn accumulate(self, value: Self, quantifier: FormulaQuantifier) -> Self {
        match quantifier {
            FormulaQuantifier::ForAll => self.and(value),
            FormulaQuantifier::Exists => self.or(value),
        }
    }

    fn quantifier_is_decided(self, quantifier: FormulaQuantifier) -> bool {
        match quantifier {
            FormulaQuantifier::ForAll => self == TriState::False,
            FormulaQuantifier::Exists => self == TriState::True,
        }
    }

    fn finish_quantifier(self, quantifier: FormulaQuantifier, exhausted: bool) -> Self {
        if exhausted || self.quantifier_is_decided(quantifier) {
            self
        } else {
            TriState::Unknown
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// evaluate_quantified_with_theory — theory-guided FOL evaluator
// ══════════════════════════════════════════════════════════════════════════════

/// Theory-guided variant of `evaluate_quantified`.
///
/// Phase 6A (predicated types) compatibility entrypoint. It evaluates the same
/// [`QuantifiedFormula`] language as [`evaluate_quantified`] and lifts the result
/// into [`TriState`]. Both entrypoints share one iterative evaluator.
///
/// A quantified atom contains a relation name and string arguments, not a
/// `T::Constraint`, so this generic API has no sound conversion it can pass to
/// [`ConstraintTheory::propagate`]. The `theory` parameter is therefore exercised
/// once through [`ConstraintTheory::empty_store`] for backend-specific
/// monomorphization, but atom truth still comes exclusively from `relation_query`.
/// Atomic relation answers are Boolean, but a truncated bounded quantifier still
/// produces `Unknown`. A caller that needs atom-level theory refinement must first
/// lower its relation atoms into the theory's concrete constraint representation.
///
/// # Returns
///
/// `TriState::True`, `TriState::False`, or `TriState::Unknown`.
pub fn evaluate_quantified_with_theory<T, F, G>(
    formula: &QuantifiedFormula,
    theory: &T,
    relation_query: &F,
    domain_enumerate: &G,
    env: &std::collections::HashMap<String, String>,
    bound: usize,
) -> TriState
where
    T: ConstraintTheory,
    F: Fn(&str, &[String]) -> bool,
    G: Fn(&str) -> Vec<Vec<String>>,
{
    // Defensive: keep the theory parameter exercised so the
    // monomorphization actually emits theory-specific code paths.
    let _ = theory.empty_store();
    evaluate_quantified_pda(formula, env, relation_query, domain_enumerate, bound)
}

// ══════════════════════════════════════════════════════════════════════════════
// TheoryPred — Boolean combination of constraints
// ══════════════════════════════════════════════════════════════════════════════

/// Boolean combination of constraints from a `ConstraintTheory`.
///
/// This is the predicate type used by [`TheoryAlgebra`]. It wraps
/// theory-specific constraints in a standard Boolean AST. Every constraint
/// theory can search it reject-safely; only exact theories expose it through the
/// classical `BooleanAlgebra` interface.
pub enum TheoryPred<T: ConstraintTheory> {
    /// Always true (unconstrained).
    True,
    /// Always false (contradictory).
    False,
    /// An atomic constraint from the theory.
    Atom(T::Constraint),
    /// Conjunction.
    And(Box<TheoryPred<T>>, Box<TheoryPred<T>>),
    /// Disjunction.
    Or(Box<TheoryPred<T>>, Box<TheoryPred<T>>),
    /// Negation.
    Not(Box<TheoryPred<T>>),
}

/// An exact satisfiability result produced by a complete decision procedure.
///
/// Unlike [`crate::algebra_tower::Sat3`], this type has no undecided case.  A
/// `Satisfiable` result carries a concrete assignment that can be checked by
/// [`ConstraintTheory::evaluate`].  Implementations of
/// [`DecidableConstraintTheory`] are responsible for the complementary proof:
/// `Unsatisfiable` is returned only when no satisfying assignment exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactSatisfiability<A> {
    /// The predicate has a concrete satisfying assignment.
    Satisfiable(A),
    /// A complete decision procedure proved the predicate empty.
    Unsatisfiable,
}

/// Explicit completeness gate for classical constraint reasoning.
///
/// Implementing [`ConstraintTheory`] alone provides bounded, reject-safe
/// search.  It deliberately does **not** grant classical complement,
/// determinization, language inclusion, or two-valued satisfiability.  A trusted
/// native theory may additionally implement this trait when it owns a total,
/// exact decision procedure for every [`TheoryPred`] over its constraint
/// language.  Runtime DDL data cannot implement Rust traits and therefore cannot
/// manufacture this authority.
///
/// # Semantic contract
///
/// For every `predicate`:
///
/// - `Satisfiable(witness)` requires that evaluating `predicate` at `witness`
///   returns `true`;
/// - `Unsatisfiable` requires that no assignment satisfies `predicate`;
/// - the procedure terminates for the theory instance's declared finite or
///   otherwise decidable domain.
///
/// The Rocq model in `formal/rocq/symbolic_algebra/theories/ConstraintDecision.v`
/// proves why this additional completeness premise is necessary.
pub trait DecidableConstraintTheory: ConstraintTheory {
    /// Decide a full Boolean predicate exactly.
    fn decide_exact(&self, predicate: &TheoryPred<Self>) -> ExactSatisfiability<Self::Assignment>
    where
        Self: Sized;
}

/// Evidence returned by bounded, certificate-checked theory search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryDecision<A> {
    /// A concrete assignment was found and rechecked against the full predicate.
    Proven(A),
    /// The predicate is structurally false, or an exact theory proved it empty.
    Refuted,
    /// No checked witness was found; the Boolean answer is not known.
    Undetermined {
        /// Whether all implementation streams explored by this bounded run ended.
        /// This is operational evidence only, never semantic completeness.
        implementation_exhausted: bool,
    },
}

impl<A> TheoryDecision<A> {
    /// Erase witness evidence while preserving all three logical outcomes.
    pub fn satisfiability(&self) -> crate::algebra_tower::Sat3 {
        match self {
            TheoryDecision::Proven(_) => crate::algebra_tower::Sat3::Sat,
            TheoryDecision::Refuted => crate::algebra_tower::Sat3::Unsat,
            TheoryDecision::Undetermined { .. } => crate::algebra_tower::Sat3::DontKnow,
        }
    }

    /// Return the checked witness, if this is a positive decision.
    pub fn into_witness(self) -> Option<A> {
        match self {
            TheoryDecision::Proven(witness) => Some(witness),
            TheoryDecision::Refuted | TheoryDecision::Undetermined { .. } => None,
        }
    }
}

#[path = "logict/lifecycle.rs"]
mod lifecycle;

// ══════════════════════════════════════════════════════════════════════════════
// TheoryAlgebra — reject-safe search plus an exact classical gate
// ══════════════════════════════════════════════════════════════════════════════

/// Wraps a [`ConstraintTheory`] in the algebra tower.
///
/// Every theory receives bounded, fair, certificate-checked search through
/// [`crate::algebra_tower::RejectSafeAlgebra`].  A missing witness is reported as
/// [`crate::algebra_tower::Sat3::DontKnow`], even when the implementation stream
/// ended.  Only [`DecidableConstraintTheory`] implementations receive the
/// classical [`crate::symbolic::BooleanAlgebra`] interface required by SFA
/// complement, determinization, inclusion, and equivalence.
#[derive(Clone, Debug)]
pub struct TheoryAlgebra<T: ConstraintTheory> {
    /// The underlying constraint theory.
    pub theory: T,
    /// Maximum search depth for non-decidable theories (bounded).
    /// Limits the number of labeling steps to prevent infinite search.
    pub search_bound: usize,
}

impl<T: ConstraintTheory> TheoryAlgebra<T> {
    /// Create a new TheoryAlgebra with the given theory and search bound.
    pub fn new(theory: T, search_bound: usize) -> Self {
        TheoryAlgebra { theory, search_bound }
    }

    fn conjunction(a: &TheoryPred<T>, b: &TheoryPred<T>) -> TheoryPred<T> {
        match (a, b) {
            (TheoryPred::True, _) => b.clone(),
            (_, TheoryPred::True) => a.clone(),
            (TheoryPred::False, _) | (_, TheoryPred::False) => TheoryPred::False,
            _ => TheoryPred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn disjunction(a: &TheoryPred<T>, b: &TheoryPred<T>) -> TheoryPred<T> {
        match (a, b) {
            (TheoryPred::True, _) | (_, TheoryPred::True) => TheoryPred::True,
            (TheoryPred::False, _) => b.clone(),
            (_, TheoryPred::False) => a.clone(),
            _ => TheoryPred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn negation(a: &TheoryPred<T>) -> TheoryPred<T> {
        match a {
            TheoryPred::True => TheoryPred::False,
            TheoryPred::False => TheoryPred::True,
            TheoryPred::Not(inner) => (**inner).clone(),
            _ => TheoryPred::Not(Box::new(a.clone())),
        }
    }

    /// Evaluate a full theory predicate without collapsing an indeterminate
    /// atom through negation or another Boolean connective.
    ///
    /// Exact theory implementations use this operation to recheck positive
    /// certificates before exposing classical decisions.
    pub fn evaluate_predicate_checked(
        &self,
        pred: &TheoryPred<T>,
        elem: &T::Assignment,
    ) -> Option<bool> {
        enum Task<'predicate, T: ConstraintTheory> {
            Visit(&'predicate TheoryPred<T>),
            Not,
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(pred)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TheoryPred::True) => values.push(Some(true)),
                Task::Visit(TheoryPred::False) => values.push(Some(false)),
                Task::Visit(TheoryPred::Atom(constraint)) => {
                    values.push(self.theory.evaluate_checked(constraint, elem));
                },
                Task::Visit(TheoryPred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Not => {
                    let value = values
                        .pop()
                        .expect("theory predicate evaluator lost negand");
                    values.push(value.map(|value| !value));
                },
                Task::And => {
                    let right = values
                        .pop()
                        .expect("theory predicate evaluator lost conjunction RHS");
                    let left = values
                        .pop()
                        .expect("theory predicate evaluator lost conjunction LHS");
                    values.push(match (left, right) {
                        (Some(false), _) | (_, Some(false)) => Some(false),
                        (Some(true), Some(true)) => Some(true),
                        _ => None,
                    });
                },
                Task::Or => {
                    let right = values
                        .pop()
                        .expect("theory predicate evaluator lost disjunction RHS");
                    let left = values
                        .pop()
                        .expect("theory predicate evaluator lost disjunction LHS");
                    values.push(match (left, right) {
                        (Some(true), _) | (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("theory predicate evaluator produced no value")
    }

    fn evaluate_predicate(&self, pred: &TheoryPred<T>, elem: &T::Assignment) -> bool {
        self.evaluate_predicate_checked(pred, elem).unwrap_or(false)
    }

    /// Decide whether a predicate is false using only its Boolean constants.
    /// Atoms remain unknown, so a `true` result is an exact structural
    /// refutation and never depends on search completeness.
    fn structurally_refuted(pred: &TheoryPred<T>) -> bool {
        #[derive(Clone, Copy)]
        enum PartialTruth {
            True,
            False,
            Unknown,
        }

        enum Task<'predicate, T: ConstraintTheory> {
            Visit(&'predicate TheoryPred<T>),
            Not,
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(pred)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TheoryPred::True) => values.push(PartialTruth::True),
                Task::Visit(TheoryPred::False) => values.push(PartialTruth::False),
                Task::Visit(TheoryPred::Atom(_)) => values.push(PartialTruth::Unknown),
                Task::Visit(TheoryPred::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(TheoryPred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Not => {
                    let value = values.pop().expect("partial truth PDA lost negand");
                    values.push(match value {
                        PartialTruth::True => PartialTruth::False,
                        PartialTruth::False => PartialTruth::True,
                        PartialTruth::Unknown => PartialTruth::Unknown,
                    });
                },
                Task::And => {
                    let right = values
                        .pop()
                        .expect("partial truth PDA lost conjunction RHS");
                    let left = values
                        .pop()
                        .expect("partial truth PDA lost conjunction LHS");
                    values.push(match (left, right) {
                        (PartialTruth::False, _) | (_, PartialTruth::False) => PartialTruth::False,
                        (PartialTruth::True, PartialTruth::True) => PartialTruth::True,
                        _ => PartialTruth::Unknown,
                    });
                },
                Task::Or => {
                    let right = values
                        .pop()
                        .expect("partial truth PDA lost disjunction RHS");
                    let left = values
                        .pop()
                        .expect("partial truth PDA lost disjunction LHS");
                    values.push(match (left, right) {
                        (PartialTruth::True, _) | (_, PartialTruth::True) => PartialTruth::True,
                        (PartialTruth::False, PartialTruth::False) => PartialTruth::False,
                        _ => PartialTruth::Unknown,
                    });
                },
            }
        }
        matches!(values.pop(), Some(PartialTruth::False))
    }

    /// Enumerate propagation-compatible stores using an explicit fair branch
    /// queue. Deterministic conjunction chains consume no search choices, while
    /// disjunctions are explored breadth-first and capped by `search_bound`.
    fn candidate_stores(&self, pred: &TheoryPred<T>) -> BoundedCollection<T::Store> {
        struct State<'predicate, T: ConstraintTheory> {
            pending: Vec<(&'predicate TheoryPred<T>, bool)>,
            store: T::Store,
        }

        let mut frontier = VecDeque::new();
        frontier.push_back(State {
            pending: vec![(pred, false)],
            store: self.theory.empty_store(),
        });
        let mut stores = Vec::new();
        let mut explored_branches = 0usize;

        'search: while let Some(mut state) = frontier.pop_front() {
            if explored_branches >= self.search_bound {
                return BoundedCollection { values: stores, exhausted: false };
            }
            explored_branches += 1;
            let mut rejected = false;

            while let Some((predicate, negated)) = state.pending.pop() {
                match (predicate, negated) {
                    (TheoryPred::True, false) | (TheoryPred::False, true) => {},
                    (TheoryPred::False, false) | (TheoryPred::True, true) => {
                        rejected = true;
                        break;
                    },
                    (TheoryPred::Atom(_), true) => {
                        // Complements are retained in the original predicate and
                        // checked against each concrete witness below.
                    },
                    (TheoryPred::Atom(constraint), false) => {
                        let Some(store) = self.theory.propagate(&state.store, constraint) else {
                            rejected = true;
                            break;
                        };
                        state.store = store;
                    },
                    (TheoryPred::Not(inner), polarity) => {
                        state.pending.push((inner, !polarity));
                    },
                    (TheoryPred::And(left, right), false) | (TheoryPred::Or(left, right), true) => {
                        state.pending.push((right, negated));
                        state.pending.push((left, negated));
                    },
                    (TheoryPred::Or(left, right), false) | (TheoryPred::And(left, right), true) => {
                        let mut right_pending = state.pending.clone();
                        right_pending.push((right, negated));
                        state.pending.push((left, negated));
                        let right_store = state.store.clone();
                        frontier.push_back(state);
                        frontier.push_back(State {
                            pending: right_pending,
                            store: right_store,
                        });
                        continue 'search;
                    },
                }
            }

            if !rejected {
                stores.push(state.store);
            }
        }

        BoundedCollection { values: stores, exhausted: true }
    }

    /// Run bounded, fair, certificate-checked search.
    pub fn decide_bounded(&self, pred: &TheoryPred<T>) -> TheoryDecision<T::Assignment> {
        if Self::structurally_refuted(pred) {
            return TheoryDecision::Refuted;
        }

        let candidates = self.candidate_stores(pred);
        let mut implementation_exhausted = candidates.exhausted;
        let mut frontier: VecDeque<T::Store> = candidates.values.into();
        let mut labeling_steps = 0usize;

        while let Some(store) = frontier.pop_front() {
            if let Some(witness) = self.theory.witness(&store) {
                if self.evaluate_predicate_checked(pred, &witness) == Some(true) {
                    return TheoryDecision::Proven(witness);
                }
            }

            if labeling_steps >= self.search_bound {
                implementation_exhausted = false;
                break;
            }

            let remaining = self.search_bound - labeling_steps;
            let labels = self
                .theory
                .label(&store)
                .collect_bounded_with_status(remaining);
            implementation_exhausted &= labels.exhausted;
            for label in labels.values {
                labeling_steps += 1;
                if let Some(next_store) = self.theory.propagate(&store, &label) {
                    frontier.push_back(next_store);
                }
            }
        }

        if !frontier.is_empty() {
            implementation_exhausted = false;
        }
        TheoryDecision::Undetermined { implementation_exhausted }
    }

    /// Run an exact theory's decision procedure and recheck every positive
    /// witness against the complete predicate.
    pub fn decide_exact_checked(&self, pred: &TheoryPred<T>) -> ExactSatisfiability<T::Assignment>
    where
        T: DecidableConstraintTheory,
    {
        match self.theory.decide_exact(pred) {
            ExactSatisfiability::Satisfiable(witness) => {
                assert!(
                    self.evaluate_predicate_checked(pred, &witness) == Some(true),
                    "DecidableConstraintTheory returned an invalid satisfiability witness"
                );
                ExactSatisfiability::Satisfiable(witness)
            },
            ExactSatisfiability::Unsatisfiable => ExactSatisfiability::Unsatisfiable,
        }
    }
}

impl<T> crate::algebra_tower::RejectSafeAlgebra for TheoryAlgebra<T>
where
    T: ConstraintTheory,
{
    type Predicate = TheoryPred<T>;
    type Domain = T::Assignment;

    fn true_pred(&self) -> Self::Predicate {
        TheoryPred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        TheoryPred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        Self::conjunction(a, b)
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        Self::disjunction(a, b)
    }

    fn pseudo_complement(&self, a: &Self::Predicate) -> Self::Predicate {
        Self::negation(a)
    }

    fn is_satisfiable_3v(&self, pred: &Self::Predicate) -> crate::algebra_tower::Sat3 {
        self.decide_bounded(pred).satisfiability()
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        self.evaluate_predicate(pred, elem)
    }

    fn witness(&self, pred: &Self::Predicate) -> Option<Self::Domain> {
        self.decide_bounded(pred).into_witness()
    }
}

impl<T> crate::symbolic::BooleanAlgebra for TheoryAlgebra<T>
where
    T: DecidableConstraintTheory,
{
    type Predicate = TheoryPred<T>;
    type Domain = T::Assignment;

    fn true_pred(&self) -> Self::Predicate {
        TheoryPred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        TheoryPred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        Self::conjunction(a, b)
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        Self::disjunction(a, b)
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        Self::negation(a)
    }

    fn is_satisfiable(&self, pred: &Self::Predicate) -> bool {
        matches!(self.decide_exact_checked(pred), ExactSatisfiability::Satisfiable(_))
    }

    fn witness(&self, pred: &Self::Predicate) -> Option<Self::Domain> {
        match self.decide_exact_checked(pred) {
            ExactSatisfiability::Satisfiable(witness) => Some(witness),
            ExactSatisfiability::Unsatisfiable => None,
        }
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        self.evaluate_predicate(pred, elem)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AC-Matching — Multiset partition enumeration via LogicStream
// ══════════════════════════════════════════════════════════════════════════════

/// A partition of a multiset into "selected" elements and "remainder".
///
/// Used for associative-commutative matching: given a bag `{A:3, B:2}` and a
/// pattern requesting 2 elements, this type represents one way to select 2
/// elements from the bag (e.g., `{A:2}` with remainder `{A:1, B:2}`).
///
/// # Invariants
///
/// - `selected_count == selected.iter().map(|(_, c)| c).sum()`
/// - For every element `e`: `selected.count(e) + remainder.count(e) == source.count(e)`
/// - `selected_count + remainder_count == source_count`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultisetPartition<T: Clone + Eq + Hash> {
    /// Selected elements with their multiplicities.
    pub selected: Vec<(T, usize)>,
    /// Remaining elements after selection.
    pub remainder: Vec<(T, usize)>,
    /// Total count of selected elements (sum of selected multiplicities).
    pub selected_count: usize,
}

/// Lazily enumerate all ways to select exactly `k` elements (with multiplicity)
/// from a multiset represented as `(element, count)` pairs.
///
/// The algorithm proceeds over distinct elements, choosing how many
/// copies of each element to include in the selection (0..=min(count, remaining_k)).
/// Duplicate-free enumeration is guaranteed because elements at index `i` are never
/// reconsidered after advancing to index `i+1`.
///
/// Results are combined via `interleave()` for fair exploration across branches.
///
/// # Arguments
///
/// * `items` — distinct elements with their multiplicities (from `HashBag::iter()`)
/// * `k` — total number of elements to select
///
/// # Examples
///
/// ```
/// # use mettail_prattail::logict::{multiset_partitions, MultisetPartition};
/// let items = vec![('A', 3), ('B', 2)];
/// let partitions: Vec<_> = multiset_partitions(&items, 2).collect_all();
/// assert_eq!(partitions.len(), 3);
/// // {A:2} rem {A:1, B:2}, {A:1, B:1} rem {A:2, B:1}, {B:2} rem {A:3}
/// ```
pub fn multiset_partitions<T>(items: &[(T, usize)], k: usize) -> LogicStream<MultisetPartition<T>>
where
    T: Clone + Eq + Hash + Send + 'static,
{
    enum Frame<T: Clone + Eq + Hash + Send + 'static> {
        Call {
            start: usize,
            remaining: usize,
        },
        Resume {
            start: usize,
            remaining: usize,
            q: usize,
            max_take: usize,
            accumulated: LogicStream<MultisetPartition<T>>,
        },
    }

    // The recursive implementation recomputed this suffix sum at every call.
    // Precomputing it makes the feasibility checks linear in the number of
    // distinct elements rather than quadratic along a deep successful branch.
    let mut suffix_available = vec![0usize; items.len() + 1];
    for index in (0..items.len()).rev() {
        suffix_available[index] = suffix_available[index + 1] + items[index].1;
    }

    let mut frames = vec![Frame::Call { start: 0, remaining: k }];
    let mut values: Vec<LogicStream<MultisetPartition<T>>> = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Call { start, remaining } => {
                if remaining == 0 {
                    let remainder = items[start..]
                        .iter()
                        .filter(|(_, count)| *count > 0)
                        .cloned()
                        .collect();
                    values.push(LogicStream::unit(MultisetPartition {
                        selected: Vec::new(),
                        remainder,
                        selected_count: 0,
                    }));
                } else if start >= items.len() || suffix_available[start] < remaining {
                    values.push(LogicStream::empty());
                } else {
                    let max_take = items[start].1.min(remaining);
                    frames.push(Frame::Resume {
                        start,
                        remaining,
                        q: 0,
                        max_take,
                        accumulated: LogicStream::empty(),
                    });
                    frames.push(Frame::Call { start: start + 1, remaining });
                }
            },
            Frame::Resume {
                start,
                remaining,
                q,
                max_take,
                accumulated,
            } => {
                let sub = values
                    .pop()
                    .expect("multiset partition PDA continuation without a child value");
                let (elem, count) = items[start].clone();
                let merged = if q == 0 {
                    sub.map(move |mut partition| {
                        if count > 0 {
                            partition.remainder.push((elem.clone(), count));
                            partition.remainder.sort_by(|a, b| a.1.cmp(&b.1));
                        }
                        partition
                    })
                } else {
                    let leftover = count - q;
                    sub.map(move |mut partition| {
                        partition.selected.push((elem.clone(), q));
                        partition.selected_count += q;
                        if leftover > 0 {
                            partition.remainder.push((elem.clone(), leftover));
                            partition.remainder.sort_by(|a, b| a.1.cmp(&b.1));
                        }
                        partition
                    })
                };
                let accumulated = accumulated.interleave(merged);

                if q < max_take {
                    frames.push(Frame::Resume {
                        start,
                        remaining,
                        q: q + 1,
                        max_take,
                        accumulated,
                    });
                    frames.push(Frame::Call {
                        start: start + 1,
                        remaining: remaining - (q + 1),
                    });
                } else {
                    values.push(accumulated);
                }
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("multiset partition PDA produced no stream")
}

/// Convenience function: eagerly collect up to `bound` multiset partitions.
///
/// Wraps `multiset_partitions()` with `collect_bounded()` for direct use
/// in AC-match guard evaluation where a `Vec` result is needed.
///
/// # Arguments
///
/// * `items` — distinct elements with their multiplicities
/// * `k` — number of elements to select
/// * `bound` — maximum number of partitions to return (T3 safety)
pub fn multiset_select<T>(items: &[(T, usize)], k: usize, bound: usize) -> Vec<MultisetPartition<T>>
where
    T: Clone + Eq + Hash + Send + 'static,
{
    multiset_partitions(items, k).collect_bounded(bound)
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── LogicStream core tests ──────────────────────────────────────────

    #[test]
    fn msplit_empty_returns_none() {
        let stream: LogicStream<i32> = LogicStream::empty();
        assert!(stream.msplit().is_none());
    }

    #[test]
    fn msplit_singleton_returns_value_and_empty() {
        let stream = LogicStream::unit(42);
        let (val, rest) = stream.msplit().expect("should have a value");
        assert_eq!(val, 42);
        assert!(rest.msplit().is_none());
    }

    #[test]
    fn from_iter_produces_all_values() {
        let stream = LogicStream::from_iter(vec![1, 2, 3]);
        let results = stream.collect_all();
        assert_eq!(results, vec![1, 2, 3]);
    }

    #[test]
    fn mplus_concatenates_streams() {
        let a = LogicStream::from_iter(vec![1, 2]);
        let b = LogicStream::from_iter(vec![3, 4]);
        let results = a.mplus(b).collect_all();
        assert_eq!(results, vec![1, 2, 3, 4]);
    }

    #[test]
    fn interleave_alternates_results() {
        let a = LogicStream::from_iter(vec![1, 3, 5]);
        let b = LogicStream::from_iter(vec![2, 4, 6]);
        let results = a.interleave(b).collect_all();
        assert_eq!(results, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn interleave_with_unequal_lengths() {
        let a = LogicStream::from_iter(vec![1, 3, 5, 7, 9]);
        let b = LogicStream::from_iter(vec![2, 4]);
        let results = a.interleave(b).collect_all();
        assert_eq!(results, vec![1, 2, 3, 4, 5, 7, 9]);
    }

    #[test]
    fn interleave_with_empty() {
        let a = LogicStream::from_iter(vec![1, 2, 3]);
        let b = LogicStream::<i32>::empty();
        let results = a.interleave(b).collect_all();
        assert_eq!(results, vec![1, 2, 3]);
    }

    #[test]
    fn fair_conjoin_does_not_starve() {
        // Key fairness test: fair_conjoin should interleave results
        // from applying f to each element, not depth-first explore
        // all results of f(first_element) before moving on.
        let stream = LogicStream::from_iter(vec![10, 20]);
        let results = stream
            .fair_conjoin(|x| LogicStream::from_iter(vec![x + 1, x + 2]))
            .collect_all();
        // Should interleave: [11, 21, 12, 22] (alternating from each source)
        // rather than [11, 12, 21, 22] (depth-first)
        assert_eq!(results, vec![11, 21, 12, 22]);
    }

    #[test]
    fn ifte_success_uses_then_branch() {
        let test = LogicStream::from_iter(vec![1, 2]);
        let result = test.ifte(|x| LogicStream::unit(x * 10), LogicStream::unit(0));
        let results = result.collect_all();
        assert!(results.contains(&10));
        assert!(results.contains(&20));
    }

    #[test]
    fn ifte_failure_uses_else_branch() {
        let test: LogicStream<i32> = LogicStream::empty();
        let result = test.ifte(|x| LogicStream::unit(x * 10), LogicStream::unit(0));
        let results = result.collect_all();
        assert_eq!(results, vec![0]);
    }

    #[test]
    fn once_commits_to_first() {
        let stream = LogicStream::from_iter(vec![1, 2, 3]);
        let results = stream.once().collect_all();
        assert_eq!(results, vec![1]);
    }

    #[test]
    fn once_on_empty_returns_empty() {
        let stream: LogicStream<i32> = LogicStream::empty();
        let results = stream.once().collect_all();
        assert!(results.is_empty());
    }

    #[test]
    fn gnot_succeeds_on_empty() {
        let stream: LogicStream<i32> = LogicStream::empty();
        let results = stream.gnot().collect_all();
        assert_eq!(results.len(), 1); // Produces one ()
    }

    #[test]
    fn gnot_fails_on_nonempty() {
        let stream = LogicStream::unit(42);
        let results = stream.gnot().collect_all();
        assert!(results.is_empty());
    }

    #[test]
    fn collect_bounded_limits_results() {
        let stream = LogicStream::from_iter(0..1000);
        let results = stream.collect_bounded(5);
        assert_eq!(results.len(), 5);
        assert_eq!(results, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn collect_bounded_reports_truncation_without_losing_prefix_order() {
        let report = LogicStream::from_iter(0..6).collect_bounded_with_status(5);
        assert_eq!(report.values, vec![0, 1, 2, 3, 4]);
        assert!(!report.exhausted);
    }

    #[test]
    fn collect_bounded_reports_exact_exhaustion_at_the_limit() {
        let report = LogicStream::from_iter(0..5).collect_bounded_with_status(5);
        assert_eq!(report.values, vec![0, 1, 2, 3, 4]);
        assert!(report.exhausted);
    }

    #[test]
    fn zero_bound_distinguishes_empty_from_nonempty_streams() {
        let empty = LogicStream::<usize>::empty().collect_bounded_with_status(0);
        assert!(empty.values.is_empty());
        assert!(empty.exhausted);

        let nonempty = LogicStream::unit(1usize).collect_bounded_with_status(0);
        assert!(nonempty.values.is_empty());
        assert!(!nonempty.exhausted);
    }

    #[test]
    fn iterator_integration() {
        let stream = LogicStream::from_iter(vec![10, 20, 30]);
        let collected: Vec<i32> = stream.into_iter().collect();
        assert_eq!(collected, vec![10, 20, 30]);
    }

    #[test]
    fn filter_removes_non_matching() {
        let stream = LogicStream::from_iter(1..=10);
        let even = stream.filter(|x| x % 2 == 0);
        let results = even.collect_all();
        assert_eq!(results, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn suspend_defers_computation() {
        let stream = LogicStream::suspend(|| LogicStream::from_iter(vec![1, 2, 3]));
        let results = stream.collect_all();
        assert_eq!(results, vec![1, 2, 3]);
    }

    // ── ConstraintTheory tests (trivial propositional theory) ───────────

    /// A trivial propositional theory for testing the ConstraintTheory trait.
    /// Constraints are propositional atoms (positive or negative).
    /// The store is a set of asserted and negated atoms.
    /// Satisfiable iff no atom is both asserted and negated.
    #[derive(Clone, Debug)]
    struct PropTheory;

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    enum PropConstraint {
        Assert(String),
        Negate(String),
    }

    #[derive(Clone, Debug)]
    struct PropAssignment(std::collections::HashMap<String, bool>);

    #[derive(Clone, Debug)]
    struct PropStore {
        asserted: std::collections::HashSet<String>,
        negated: std::collections::HashSet<String>,
    }

    impl ConstraintTheory for PropTheory {
        type Constraint = PropConstraint;
        type Assignment = PropAssignment;
        type Store = PropStore;

        fn empty_store(&self) -> PropStore {
            PropStore {
                asserted: std::collections::HashSet::new(),
                negated: std::collections::HashSet::new(),
            }
        }

        fn propagate(&self, store: &PropStore, c: &PropConstraint) -> Option<PropStore> {
            let mut new_store = store.clone();
            match c {
                PropConstraint::Assert(name) => {
                    if new_store.negated.contains(name) {
                        return None; // Contradiction
                    }
                    new_store.asserted.insert(name.clone());
                },
                PropConstraint::Negate(name) => {
                    if new_store.asserted.contains(name) {
                        return None; // Contradiction
                    }
                    new_store.negated.insert(name.clone());
                },
            }
            Some(new_store)
        }

        fn is_consistent(&self, store: &PropStore) -> bool {
            store.asserted.intersection(&store.negated).next().is_none()
        }

        fn witness(&self, store: &PropStore) -> Option<PropAssignment> {
            if !self.is_consistent(store) {
                return None;
            }
            let mut assignment = std::collections::HashMap::new();
            for name in &store.asserted {
                assignment.insert(name.clone(), true);
            }
            for name in &store.negated {
                assignment.insert(name.clone(), false);
            }
            Some(PropAssignment(assignment))
        }

        fn label(&self, _store: &PropStore) -> LogicStream<PropConstraint> {
            // Decidable theory — no labeling needed
            LogicStream::empty()
        }

        fn evaluate(&self, c: &PropConstraint, assignment: &PropAssignment) -> bool {
            match c {
                PropConstraint::Assert(name) => *assignment.0.get(name).unwrap_or(&false),
                PropConstraint::Negate(name) => !*assignment.0.get(name).unwrap_or(&false),
            }
        }
    }

    #[test]
    fn constraint_theory_consistent_store() {
        let theory = PropTheory;
        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &PropConstraint::Assert("a".into()))
            .expect("should succeed");
        let store = theory
            .propagate(&store, &PropConstraint::Negate("b".into()))
            .expect("should succeed");
        assert!(theory.is_consistent(&store));
        let witness = theory.witness(&store).expect("should have witness");
        assert_eq!(witness.0.get("a"), Some(&true));
        assert_eq!(witness.0.get("b"), Some(&false));
    }

    #[test]
    fn constraint_theory_contradiction() {
        let theory = PropTheory;
        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &PropConstraint::Assert("a".into()))
            .expect("should succeed");
        // Negating "a" should fail (contradiction)
        assert!(theory
            .propagate(&store, &PropConstraint::Negate("a".into()))
            .is_none());
    }

    #[test]
    fn constraint_theory_evaluate() {
        let theory = PropTheory;
        let mut assignment = std::collections::HashMap::new();
        assignment.insert("a".into(), true);
        assignment.insert("b".into(), false);
        let assignment = PropAssignment(assignment);

        assert!(theory.evaluate(&PropConstraint::Assert("a".into()), &assignment));
        assert!(!theory.evaluate(&PropConstraint::Assert("b".into()), &assignment));
        assert!(theory.evaluate(&PropConstraint::Negate("b".into()), &assignment));
    }

    // ── TheoryAlgebra tests (requires symbolic-automata feature) ────────

    mod theory_algebra_tests {
        use super::*;
        use crate::algebra_tower::{RejectSafeAlgebra, Sat3};

        #[test]
        fn theory_algebra_true_is_satisfiable() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            assert_eq!(algebra.is_satisfiable_3v(&algebra.true_pred()), Sat3::Sat);
        }

        #[test]
        fn theory_algebra_false_is_not_satisfiable() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            assert_eq!(algebra.is_satisfiable_3v(&algebra.false_pred()), Sat3::Unsat);
        }

        #[test]
        fn theory_algebra_atom_satisfiable() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            let pred = TheoryPred::Atom(PropConstraint::Assert("x".into()));
            assert_eq!(algebra.is_satisfiable_3v(&pred), Sat3::Sat);
        }

        #[test]
        fn generic_theory_exhaustion_does_not_claim_unsatisfiable() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            let pred = algebra.and(
                &TheoryPred::Atom(PropConstraint::Assert("x".into())),
                &TheoryPred::Atom(PropConstraint::Negate("x".into())),
            );
            assert_eq!(algebra.is_satisfiable_3v(&pred), Sat3::DontKnow);
            assert!(matches!(
                algebra.decide_bounded(&pred),
                TheoryDecision::Undetermined { implementation_exhausted: true }
            ));
        }

        #[test]
        fn theory_algebra_disjunction_satisfiable() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            // (x ∧ ¬x) ∨ y — unsatisfiable left, satisfiable right
            let pred = algebra.or(
                &algebra.and(
                    &TheoryPred::Atom(PropConstraint::Assert("x".into())),
                    &TheoryPred::Atom(PropConstraint::Negate("x".into())),
                ),
                &TheoryPred::Atom(PropConstraint::Assert("y".into())),
            );
            assert_eq!(algebra.is_satisfiable_3v(&pred), Sat3::Sat);
        }

        #[test]
        fn theory_algebra_negation() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            let true_pred = algebra.true_pred();
            let not_true = algebra.pseudo_complement(&true_pred);
            assert_eq!(algebra.is_satisfiable_3v(&not_true), Sat3::Unsat);
        }

        #[test]
        fn theory_algebra_evaluate() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            let pred = TheoryPred::Atom(PropConstraint::Assert("x".into()));
            let mut map = std::collections::HashMap::new();
            map.insert("x".into(), true);
            let assignment = PropAssignment(map);
            assert!(algebra.evaluate(&pred, &assignment));
        }

        #[test]
        fn theory_algebra_witness() {
            let algebra = TheoryAlgebra::new(PropTheory, 100);
            let pred = TheoryPred::Atom(PropConstraint::Assert("x".into()));
            let witness = algebra.witness(&pred);
            assert!(witness.is_some());
            let w = witness.expect("should have witness");
            assert_eq!(w.0.get("x"), Some(&true));
        }
    }

    // ── QuantifiedFormula & evaluate_quantified tests ────────────────────

    /// Test helper: relation query that checks membership in a simple database.
    /// Database: positive(1), positive(2), positive(3), reachable(1,2),
    /// reachable(2,3), safe(1), safe(2), safe(3)
    fn test_relation_query(rel: &str, args: &[String]) -> bool {
        match rel {
            "positive" => args.len() == 1 && matches!(args[0].as_str(), "1" | "2" | "3"),
            "reachable" => {
                args.len() == 2
                    && matches!((args[0].as_str(), args[1].as_str()), ("1", "2") | ("2", "3"))
            },
            "safe" => args.len() == 1 && matches!(args[0].as_str(), "1" | "2" | "3"),
            "items" => args.len() == 1 && matches!(args[0].as_str(), "1" | "2" | "3"),
            "greater_than_one" => {
                args.len() == 1 && args[0].parse::<i32>().map_or(false, |n| n > 1)
            },
            "greater_than_two" => {
                args.len() == 1 && args[0].parse::<i32>().map_or(false, |n| n > 2)
            },
            _ => false,
        }
    }

    /// Test helper: domain enumerator for test relations.
    fn test_domain_enumerate(rel: &str) -> Vec<Vec<String>> {
        match rel {
            "positive" | "items" | "safe" => {
                vec![vec!["1".into()], vec!["2".into()], vec!["3".into()]]
            },
            "reachable" => vec![vec!["1".into(), "2".into()], vec!["2".into(), "3".into()]],
            "nodes" => {
                vec![vec!["1".into()], vec!["2".into()], vec!["3".into()]]
            },
            _ => vec![],
        }
    }

    #[test]
    fn quantified_formula_display() {
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        assert_eq!(format!("{}", f), "∀x ∈ items. positive(x)");
    }

    #[test]
    fn quantified_formula_display_bounded() {
        let f = QuantifiedFormula::exists(
            "y",
            QuantifiedDomain::Bounded { relation: "nodes".into(), limit: 100 },
            QuantifiedFormula::atom("safe", vec![QuantifiedArg::var("y")]),
        );
        assert_eq!(format!("{}", f), "∃y ∈ nodes[≤100]. safe(y)");
    }

    #[test]
    fn quantified_formula_display_implies() {
        let f = QuantifiedFormula::implies(
            QuantifiedFormula::atom(
                "reachable",
                vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
            ),
            QuantifiedFormula::atom("safe", vec![QuantifiedArg::var("y")]),
        );
        assert_eq!(format!("{}", f), "(reachable(x, y) ⇒ safe(y))");
    }

    #[test]
    fn quantified_formula_free_vars() {
        // ∀y ∈ nodes. (reachable(x, y) ⇒ safe(y))
        // Free vars: {x} (y is bound by ∀)
        let f = QuantifiedFormula::forall(
            "y",
            QuantifiedDomain::Relation("nodes".into()),
            QuantifiedFormula::implies(
                QuantifiedFormula::atom(
                    "reachable",
                    vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
                ),
                QuantifiedFormula::atom("safe", vec![QuantifiedArg::var("y")]),
            ),
        );
        let free = f.free_vars();
        assert_eq!(free.len(), 1);
        assert!(free.contains("x"));
    }

    #[test]
    fn quantified_formula_free_vars_nested() {
        // ∀x ∈ nodes. ∃y ∈ nodes. reachable(x, y)
        // Free vars: {} (both x and y are bound)
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("nodes".into()),
            QuantifiedFormula::exists(
                "y",
                QuantifiedDomain::Relation("nodes".into()),
                QuantifiedFormula::atom(
                    "reachable",
                    vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
                ),
            ),
        );
        assert!(f.free_vars().is_empty());
    }

    #[test]
    fn evaluate_atom_true() {
        let f = QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]);
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_atom_false() {
        let f = QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("99".into())]);
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_atom_with_var() {
        let f = QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]);
        let mut env = std::collections::HashMap::new();
        env.insert("x".into(), "2".into());
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_and() {
        let f = QuantifiedFormula::and(
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("2".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_and_short_circuit() {
        let f = QuantifiedFormula::and(
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("99".into())]),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_or() {
        let f = QuantifiedFormula::or(
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("99".into())]),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_not() {
        let f = QuantifiedFormula::not(QuantifiedFormula::atom(
            "positive",
            vec![QuantifiedArg::Constant("99".into())],
        ));
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_implies_true_antecedent() {
        // positive(1) ⇒ safe(1) — both true, so true
        let f = QuantifiedFormula::implies(
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]),
            QuantifiedFormula::atom("safe", vec![QuantifiedArg::Constant("1".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_implies_false_antecedent() {
        // positive(99) ⇒ safe(99) — false ⇒ anything = true (vacuous truth)
        let f = QuantifiedFormula::implies(
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("99".into())]),
            QuantifiedFormula::atom("safe", vec![QuantifiedArg::Constant("99".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_forall_all_positive() {
        // ∀x ∈ items. positive(x) — all items {1,2,3} are positive → true
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_forall_not_all_greater_than_one() {
        // ∀x ∈ items. greater_than_one(x) — item "1" fails → false
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("greater_than_one", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_exists_some_greater_than_two() {
        // ∃x ∈ items. greater_than_two(x) — item "3" satisfies → true
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("greater_than_two", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_exists_none_match() {
        // ∃x ∈ items. positive(99) — no element can make "99" positive → false
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("99".into())]),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_forall_implies() {
        // ∀y ∈ nodes. (reachable(x, y) ⇒ safe(y))
        // With x=1: reachable(1,2) ⇒ safe(2) ✓, reachable(1,3)=false ⇒ vacuous ✓,
        //           reachable(1,1)=false ⇒ vacuous ✓
        let f = QuantifiedFormula::forall(
            "y",
            QuantifiedDomain::Relation("nodes".into()),
            QuantifiedFormula::implies(
                QuantifiedFormula::atom(
                    "reachable",
                    vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
                ),
                QuantifiedFormula::atom("safe", vec![QuantifiedArg::var("y")]),
            ),
        );
        let mut env = std::collections::HashMap::new();
        env.insert("x".into(), "1".into());
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_nested_forall_exists() {
        // ∀x ∈ nodes. ∃y ∈ nodes. reachable(x, y)
        // x=1: reachable(1,2) ✓
        // x=2: reachable(2,3) ✓
        // x=3: no reachable(3,_) → false
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("nodes".into()),
            QuantifiedFormula::exists(
                "y",
                QuantifiedDomain::Relation("nodes".into()),
                QuantifiedFormula::atom(
                    "reachable",
                    vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
                ),
            ),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_exists_forall() {
        // ∃x ∈ nodes. ∀y ∈ nodes. (reachable(x, y) ⇒ safe(y))
        // x=1: reachable(1,2)⇒safe(2) ✓, reachable(1,3)=F⇒vacuous, reachable(1,1)=F⇒vacuous → ✓
        // So exists succeeds with x=1
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("nodes".into()),
            QuantifiedFormula::forall(
                "y",
                QuantifiedDomain::Relation("nodes".into()),
                QuantifiedFormula::implies(
                    QuantifiedFormula::atom(
                        "reachable",
                        vec![QuantifiedArg::var("x"), QuantifiedArg::var("y")],
                    ),
                    QuantifiedFormula::atom("safe", vec![QuantifiedArg::var("y")]),
                ),
            ),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_bounded_domain() {
        // ∃x ∈ items[≤2]. greater_than_two(x)
        // The first two items contain no witness, but item "3" lies beyond the
        // prefix, so the logical result is Unknown and Boolean admission fails.
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Bounded { relation: "items".into(), limit: 2 },
            QuantifiedFormula::atom("greater_than_two", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
        assert_eq!(
            evaluate_quantified_3v(&f, &env, &test_relation_query, &test_domain_enumerate, 1000,),
            TriState::Unknown
        );
    }

    #[test]
    fn truncated_forall_and_its_negation_both_fail_closed() {
        let forall = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Bounded { relation: "items".into(), limit: 2 },
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        let negated = QuantifiedFormula::not(forall.clone());
        let env = std::collections::HashMap::new();

        assert_eq!(
            evaluate_quantified_3v(
                &forall,
                &env,
                &test_relation_query,
                &test_domain_enumerate,
                1000,
            ),
            TriState::Unknown
        );
        assert_eq!(
            evaluate_quantified_3v(
                &negated,
                &env,
                &test_relation_query,
                &test_domain_enumerate,
                1000,
            ),
            TriState::Unknown
        );
        assert!(!evaluate_quantified(
            &negated,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000,
        ));
    }

    #[test]
    fn evaluate_bounded_domain_succeeds() {
        // ∃x ∈ items[≤3]. greater_than_two(x) — bound allows item "3" → true
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Bounded { relation: "items".into(), limit: 3 },
            QuantifiedFormula::atom("greater_than_two", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_empty_domain_forall_vacuous() {
        // ∀x ∈ empty_rel. positive(x) — vacuously true (no elements to check)
        let f = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("nonexistent".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn evaluate_empty_domain_exists_false() {
        // ∃x ∈ empty_rel. positive(x) — false (no elements to find)
        let f = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("nonexistent".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        let env = std::collections::HashMap::new();
        assert!(!evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn gnot_equivalence_forall_not_exists_not() {
        // Property: ∀x.P(x) ≡ ¬∃x.¬P(x)
        // Test with P = positive, domain = items
        let forall_p = QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("positive", vec![QuantifiedArg::var("x")]),
        );
        let not_exists_not_p = QuantifiedFormula::not(QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::not(QuantifiedFormula::atom(
                "positive",
                vec![QuantifiedArg::var("x")],
            )),
        ));
        let env = std::collections::HashMap::new();
        let r1 = evaluate_quantified(
            &forall_p,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000,
        );
        let r2 = evaluate_quantified(
            &not_exists_not_p,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000,
        );
        assert_eq!(r1, r2, "∀x.P(x) must equal ¬∃x.¬P(x)");
    }

    #[test]
    fn gnot_equivalence_exists_not_forall_not() {
        // Property: ∃x.P(x) ≡ ¬∀x.¬P(x)
        // Test with P = greater_than_two, domain = items
        let exists_p = QuantifiedFormula::exists(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::atom("greater_than_two", vec![QuantifiedArg::var("x")]),
        );
        let not_forall_not_p = QuantifiedFormula::not(QuantifiedFormula::forall(
            "x",
            QuantifiedDomain::Relation("items".into()),
            QuantifiedFormula::not(QuantifiedFormula::atom(
                "greater_than_two",
                vec![QuantifiedArg::var("x")],
            )),
        ));
        let env = std::collections::HashMap::new();
        let r1 = evaluate_quantified(
            &exists_p,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000,
        );
        let r2 = evaluate_quantified(
            &not_forall_not_p,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000,
        );
        assert_eq!(r1, r2, "∃x.P(x) must equal ¬∀x.¬P(x)");
    }

    #[test]
    fn evaluate_complex_nested_boolean() {
        // (positive(1) && safe(1)) || !positive(99)
        let f = QuantifiedFormula::or(
            QuantifiedFormula::and(
                QuantifiedFormula::atom("positive", vec![QuantifiedArg::Constant("1".into())]),
                QuantifiedFormula::atom("safe", vec![QuantifiedArg::Constant("1".into())]),
            ),
            QuantifiedFormula::not(QuantifiedFormula::atom(
                "positive",
                vec![QuantifiedArg::Constant("99".into())],
            )),
        );
        let env = std::collections::HashMap::new();
        assert!(evaluate_quantified(
            &f,
            &env,
            &test_relation_query,
            &test_domain_enumerate,
            1000
        ));
    }

    #[test]
    fn quantified_arg_display() {
        assert_eq!(format!("{}", QuantifiedArg::var("x")), "x");
        assert_eq!(format!("{}", QuantifiedArg::constant("hello")), "'hello'");
    }

    #[test]
    fn quantified_domain_display() {
        assert_eq!(format!("{}", QuantifiedDomain::Relation("items".into())), "items");
        assert_eq!(
            format!("{}", QuantifiedDomain::Bounded { relation: "items".into(), limit: 50 }),
            "items[≤50]"
        );
    }

    // ── AC-Matching: Multiset partition tests ────────────────────────────

    /// Helper: compute total element count in a partition's selected or remainder.
    fn total_count<T: Clone + Eq + Hash>(pairs: &[(T, usize)]) -> usize {
        pairs.iter().map(|(_, c)| c).sum()
    }

    #[test]
    fn partition_empty_k0() {
        // Empty bag, K=0: one partition (empty selection, empty remainder)
        let items: Vec<(char, usize)> = vec![];
        let parts = multiset_partitions(&items, 0).collect_all();
        assert_eq!(parts.len(), 1);
        assert!(parts[0].selected.is_empty());
        assert!(parts[0].remainder.is_empty());
        assert_eq!(parts[0].selected_count, 0);
    }

    #[test]
    fn partition_empty_k1() {
        // Empty bag, K=1: no partitions possible
        let items: Vec<(char, usize)> = vec![];
        let parts = multiset_partitions(&items, 1).collect_all();
        assert!(parts.is_empty());
    }

    #[test]
    fn partition_singleton_k1() {
        // {A:1}, K=1: exactly one partition
        let items = vec![('A', 1)];
        let parts = multiset_partitions(&items, 1).collect_all();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].selected, vec![('A', 1)]);
        assert!(parts[0].remainder.is_empty());
        assert_eq!(parts[0].selected_count, 1);
    }

    #[test]
    fn partition_pair_k1() {
        // {A:1, B:1}, K=1: two partitions
        let items = vec![('A', 1), ('B', 1)];
        let parts = multiset_partitions(&items, 1).collect_all();
        assert_eq!(parts.len(), 2);

        // Each partition should select exactly one element
        for p in &parts {
            assert_eq!(p.selected_count, 1);
            assert_eq!(total_count(&p.remainder), 1);
        }
    }

    #[test]
    fn partition_multiplicity_k2() {
        // {A:3}, K=2: one partition {A:2} remainder {A:1}
        let items = vec![('A', 3)];
        let parts = multiset_partitions(&items, 2).collect_all();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].selected, vec![('A', 2)]);
        assert_eq!(parts[0].selected_count, 2);
        assert_eq!(parts[0].remainder, vec![('A', 1)]);
    }

    #[test]
    fn partition_mixed_k2() {
        // {A:2, B:1}, K=2: two partitions
        // - {A:2} remainder {B:1}
        // - {A:1, B:1} remainder {A:1}
        let items = vec![('A', 2), ('B', 1)];
        let parts = multiset_partitions(&items, 2).collect_all();
        assert_eq!(parts.len(), 2);

        for p in &parts {
            assert_eq!(p.selected_count, 2);
        }
    }

    #[test]
    fn partition_three_elements_k2() {
        // {A:1, B:1, C:1}, K=2: three partitions (C(3,2) = 3)
        let items = vec![('A', 1), ('B', 1), ('C', 1)];
        let parts = multiset_partitions(&items, 2).collect_all();
        assert_eq!(parts.len(), 3);

        for p in &parts {
            assert_eq!(p.selected_count, 2);
            assert_eq!(total_count(&p.remainder), 1);
        }
    }

    #[test]
    fn partition_sum_invariant() {
        // For all partitions: selected_count + remainder_count == source_count
        let items = vec![('A', 3), ('B', 2), ('C', 1)];
        let source_total: usize = items.iter().map(|(_, c)| c).sum(); // 6
        let parts = multiset_partitions(&items, 3).collect_all();

        for p in &parts {
            let selected_total = total_count(&p.selected);
            let remainder_total = total_count(&p.remainder);
            assert_eq!(selected_total, p.selected_count);
            assert_eq!(
                selected_total + remainder_total,
                source_total,
                "sum invariant violated: selected={selected_total} + remainder={remainder_total} != {source_total}"
            );
        }
    }

    #[test]
    fn partition_no_duplicates() {
        // All partitions should be distinct
        let items = vec![('A', 2), ('B', 2), ('C', 1)];
        let parts = multiset_partitions(&items, 3).collect_all();

        for i in 0..parts.len() {
            for j in (i + 1)..parts.len() {
                // Compare by sorted selected sets
                let mut sel_i = parts[i].selected.clone();
                let mut sel_j = parts[j].selected.clone();
                sel_i.sort_by_key(|(c, _)| *c);
                sel_j.sort_by_key(|(c, _)| *c);
                assert_ne!(sel_i, sel_j, "duplicate partitions at indices {i} and {j}");
            }
        }
    }

    #[test]
    fn partition_k_equals_n() {
        // K = total count: exactly one partition (select everything)
        let items = vec![('A', 2), ('B', 1)];
        let parts = multiset_partitions(&items, 3).collect_all();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].selected_count, 3);
        assert!(parts[0].remainder.is_empty());
    }

    #[test]
    fn partition_k_exceeds_n() {
        // K > total count: no partitions
        let items = vec![('A', 2), ('B', 1)];
        let parts = multiset_partitions(&items, 4).collect_all();
        assert!(parts.is_empty());
    }

    #[test]
    fn partition_bounded() {
        // collect_bounded(2) limits results even if more exist
        let items = vec![('A', 1), ('B', 1), ('C', 1)];
        // C(3,2) = 3 partitions exist
        let parts = multiset_partitions(&items, 2).collect_bounded(2);
        assert_eq!(parts.len(), 2);
    }

    #[test]
    fn partition_fairness() {
        // interleave ensures late elements aren't starved:
        // collect_bounded should include partitions drawing from later elements
        let items = vec![('A', 1), ('B', 1), ('C', 1), ('D', 1), ('E', 1)];
        let parts = multiset_partitions(&items, 1).collect_bounded(3);
        assert_eq!(parts.len(), 3);
        // Due to interleaving, we should see elements from different positions
        let selected_elems: Vec<char> = parts
            .iter()
            .flat_map(|p| p.selected.iter().map(|(c, _)| *c))
            .collect();
        // At least 2 distinct elements should appear in first 3 results
        let distinct: std::collections::HashSet<char> = selected_elems.into_iter().collect();
        assert!(distinct.len() >= 2, "interleave should mix elements from different positions");
    }

    #[test]
    fn partition_complement_symmetry() {
        // |partitions(M, K)| == |partitions(M, N-K)|
        let items = vec![('A', 2), ('B', 2), ('C', 1)];
        let n: usize = items.iter().map(|(_, c)| c).sum(); // 5

        for k in 0..=n {
            let count_k = multiset_partitions(&items, k).collect_all().len();
            let count_complement = multiset_partitions(&items, n - k).collect_all().len();
            assert_eq!(
                count_k,
                count_complement,
                "|partitions(M, {k})| = {count_k} != |partitions(M, {})| = {count_complement}",
                n - k
            );
        }
    }

    #[test]
    fn partition_select_convenience() {
        // multiset_select() is a convenience wrapper returning Vec directly
        let items = vec![('A', 1), ('B', 1), ('C', 1)];
        let result = multiset_select(&items, 2, 1000);
        assert_eq!(result.len(), 3); // C(3,2)

        // With bound
        let bounded = multiset_select(&items, 2, 2);
        assert_eq!(bounded.len(), 2);
    }

    #[test]
    fn partition_per_element_count_invariant() {
        // For every partition and every element:
        // selected.count(e) + remainder.count(e) == source.count(e)
        let items = vec![('X', 4), ('Y', 2), ('Z', 1)];
        let parts = multiset_partitions(&items, 3).collect_all();

        for p in &parts {
            for &(ref elem, source_count) in &items {
                let sel_count = p
                    .selected
                    .iter()
                    .filter(|(e, _)| e == elem)
                    .map(|(_, c)| c)
                    .sum::<usize>();
                let rem_count = p
                    .remainder
                    .iter()
                    .filter(|(e, _)| e == elem)
                    .map(|(_, c)| c)
                    .sum::<usize>();
                assert_eq!(
                    sel_count + rem_count,
                    source_count,
                    "element {:?}: selected={sel_count} + remainder={rem_count} != source={source_count}",
                    elem
                );
            }
        }
    }

    // ──────────────────────────────────────────────────────────────
    // Phase 6 — TriState + evaluate_quantified_with_theory
    // ──────────────────────────────────────────────────────────────

    #[test]
    fn tristate_kleene_and() {
        use TriState::*;
        assert_eq!(True.and(True), True);
        assert_eq!(True.and(False), False);
        assert_eq!(True.and(Unknown), Unknown);
        assert_eq!(False.and(True), False);
        assert_eq!(False.and(False), False);
        assert_eq!(False.and(Unknown), False);
        assert_eq!(Unknown.and(True), Unknown);
        assert_eq!(Unknown.and(False), False);
        assert_eq!(Unknown.and(Unknown), Unknown);
    }

    #[test]
    fn tristate_kleene_or() {
        use TriState::*;
        assert_eq!(True.or(True), True);
        assert_eq!(True.or(False), True);
        assert_eq!(True.or(Unknown), True);
        assert_eq!(False.or(False), False);
        assert_eq!(False.or(Unknown), Unknown);
        assert_eq!(Unknown.or(False), Unknown);
        assert_eq!(Unknown.or(Unknown), Unknown);
    }

    #[test]
    fn tristate_negation() {
        assert_eq!(TriState::True.not(), TriState::False);
        assert_eq!(TriState::False.not(), TriState::True);
        assert_eq!(TriState::Unknown.not(), TriState::Unknown);
    }

    #[test]
    fn tristate_implies() {
        use TriState::*;
        assert_eq!(True.implies(True), True);
        assert_eq!(True.implies(False), False);
        assert_eq!(False.implies(True), True);
        assert_eq!(False.implies(False), True); // ⊥ ⟹ anything
        assert_eq!(True.implies(Unknown), Unknown);
        assert_eq!(Unknown.implies(True), True); // ¬Unknown ∨ True = True
    }

    #[test]
    fn tristate_safe_bool_collapse() {
        assert!(TriState::True.into_safe_bool());
        assert!(!TriState::False.into_safe_bool());
        assert!(!TriState::Unknown.into_safe_bool()); // safe-fail
    }

    #[test]
    fn evaluate_with_theory_atom_true_when_relation_holds() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::Atom {
            relation: "halts".into(),
            args: vec![QuantifiedArg::Var("x".into())],
        };
        let mut env = std::collections::HashMap::new();
        env.insert("x".into(), "p".into());

        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|rel, args| rel == "halts" && args == ["p"],
            &|_| Vec::new(),
            &env,
            16,
        );
        assert_eq!(result, TriState::True);
    }

    #[test]
    fn evaluate_with_theory_atom_false_when_relation_misses() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::Atom {
            relation: "halts".into(),
            args: vec![QuantifiedArg::Var("x".into())],
        };
        let mut env = std::collections::HashMap::new();
        env.insert("x".into(), "q".into());

        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|_, _| false,
            &|_| Vec::new(),
            &env,
            16,
        );
        assert_eq!(result, TriState::False);
    }

    #[test]
    fn evaluate_with_theory_forall_over_singleton_domain() {
        let theory = PropTheory;
        // ∀x ∈ items. positive(x) — items has just one tuple "5"
        let formula = QuantifiedFormula::ForAll {
            var: "x".into(),
            domain: QuantifiedDomain::Relation("items".into()),
            body: Box::new(QuantifiedFormula::Atom {
                relation: "positive".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
        };
        let env = std::collections::HashMap::new();
        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|rel, args| rel == "positive" && args == ["5"],
            &|rel| {
                if rel == "items" {
                    vec![vec!["5".into()]]
                } else {
                    Vec::new()
                }
            },
            &env,
            16,
        );
        assert_eq!(result, TriState::True);
    }

    #[test]
    fn evaluate_with_theory_forall_falsified_by_counterexample() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::ForAll {
            var: "x".into(),
            domain: QuantifiedDomain::Relation("items".into()),
            body: Box::new(QuantifiedFormula::Atom {
                relation: "positive".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
        };
        let env = std::collections::HashMap::new();
        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|rel, args| rel == "positive" && args == ["5"], // 5 is positive, 7 is not
            &|rel| {
                if rel == "items" {
                    vec![vec!["5".into()], vec!["7".into()]]
                } else {
                    Vec::new()
                }
            },
            &env,
            16,
        );
        assert_eq!(result, TriState::False);
    }

    #[test]
    fn evaluate_with_theory_exists_finds_witness() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::Exists {
            var: "x".into(),
            domain: QuantifiedDomain::Relation("items".into()),
            body: Box::new(QuantifiedFormula::Atom {
                relation: "positive".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
        };
        let env = std::collections::HashMap::new();
        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|rel, args| rel == "positive" && args == ["7"],
            &|rel| {
                if rel == "items" {
                    vec![vec!["5".into()], vec!["7".into()]]
                } else {
                    Vec::new()
                }
            },
            &env,
            16,
        );
        assert_eq!(result, TriState::True);
    }

    #[test]
    fn evaluate_with_theory_exists_empty_domain_is_false() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::Exists {
            var: "x".into(),
            domain: QuantifiedDomain::Relation("items".into()),
            body: Box::new(QuantifiedFormula::Atom {
                relation: "positive".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
        };
        let env = std::collections::HashMap::new();
        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|_, _| true,
            &|_| Vec::new(),
            &env,
            16,
        );
        assert_eq!(result, TriState::False);
    }

    #[test]
    fn evaluate_with_theory_forall_empty_domain_is_true() {
        let theory = PropTheory;
        let formula = QuantifiedFormula::ForAll {
            var: "x".into(),
            domain: QuantifiedDomain::Relation("items".into()),
            body: Box::new(QuantifiedFormula::Atom {
                relation: "positive".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
        };
        let env = std::collections::HashMap::new();
        let result = evaluate_quantified_with_theory(
            &formula,
            &theory,
            &|_, _| false,
            &|_| Vec::new(),
            &env,
            16,
        );
        assert_eq!(result, TriState::True);
    }
}
