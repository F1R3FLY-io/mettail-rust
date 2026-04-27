//! CEK Evaluator for Term Rewriting.
//!
//! Extends PraTTaIL's CEK architecture from **parsing** to **rewriting**.
//! The parsing CEK traces how tokens are consumed and AST nodes constructed;
//! this evaluator CEK traces how AST terms are simplified via rewrite rules.
//!
//! ## CEK Components (Evaluation)
//!
//! | CEK Component | Evaluator Representation |
//! |---------------|--------------------------|
//! | **C** (Control) | Current term + rewrite rule selector |
//! | **E** (Environment) | Variable bindings (`HashMap<String, String>`) |
//! | **K** (Kontinuation) | Evaluation context stack (`Vec<EvalFrame>`) |
//!
//! ## Transition Rules
//!
//! | Rule | Meaning |
//! |------|---------|
//! | `Reduce` | Select a rewrite rule for the current term |
//! | `Descend` | Enter a subterm for evaluation |
//! | `Ascend` | Return from a subterm evaluation |
//! | `Bind` | Bind a variable in the environment |
//! | `Apply` | Apply a rewrite rule to the current term |
//! | `Accept` | Evaluation complete — no more rules apply |
//!
//! ## Memoization
//!
//! Ground terms (terms with no free variables) are cached in a memo table.
//! When the evaluator encounters a ground term it has already reduced, it
//! returns the cached normal form immediately, avoiding redundant work.
//!
//! ## Observer Pattern
//!
//! The evaluator emits [`EvalStepEvent`] at each transition. Consumers
//! implement [`EvalObserver`] to receive notifications:
//!
//! - **`TracingEvalObserver`**: Collects full [`EvalTrace`] statistics.
//! - **`NullEvalObserver`**: Discards all events (zero overhead).
//!
//! ## References
//!
//! - Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
//!   and the λ-calculus. *Formal Description of Programming Concepts III*, pp. 193–219.
//! - Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge Univ. Press.

use std::collections::{BTreeMap, HashMap};
use std::fmt;

use crate::cesk_store::{LocalCeskStore, StoreAddr, StoreValue};
use crate::control::CekControl;
use crate::gc::{GcStrategy, RefCountGc};

// ══════════════════════════════════════════════════════════════════════════════
// Transition Rules
// ══════════════════════════════════════════════════════════════════════════════

/// Which transition the evaluator is performing.
///
/// These rules define the small-step operational semantics of term rewriting
/// in the CEK framework. Each variant corresponds to an observable transition
/// that consumers (debuggers, profilers, tracers) can intercept.
///
/// ## Transition Diagram
///
/// ```text
///   Reduce ──→ Descend ──→ Reduce (recursive subterm)
///     │            │
///     │            └──→ Ascend ──→ Apply ──→ Reduce (re-check)
///     │                                 │
///     └──→ Bind ──→ Apply               └──→ Accept (normal form)
///     │
///     └──→ Accept (no rules match)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EvalTransitionRule {
    /// Select a rewrite rule for the current term.
    ///
    /// The evaluator inspects the current control term and determines which
    /// rewrite rule (if any) applies. If no rule matches, the term is in
    /// normal form and the evaluator transitions to `Accept` or `Ascend`.
    Reduce,

    /// Enter a subterm for evaluation.
    ///
    /// The evaluator pushes the current evaluation context onto the
    /// continuation stack and focuses on a subterm. This corresponds to
    /// the "descend into left operand" or "descend into scrutinee" steps
    /// in a structured rewrite strategy.
    Descend,

    /// Return from a subterm evaluation.
    ///
    /// The evaluator pops the top continuation frame and integrates the
    /// evaluated subterm result back into the enclosing context. This
    /// corresponds to unwinding after a recursive evaluation completes.
    Ascend,

    /// Bind a variable in the environment.
    ///
    /// When a rewrite rule matches with pattern variables, the evaluator
    /// binds each matched variable in the environment before proceeding
    /// to apply the rule's right-hand side.
    Bind,

    /// Apply a rewrite rule to the current term.
    ///
    /// After subterms have been evaluated and variables bound, the evaluator
    /// applies the matched rewrite rule, substituting bound variables into
    /// the rule's right-hand side template to produce the rewritten term.
    Apply,

    /// Mutate a store cell at an existing address.
    ///
    /// The `set!` operation overwrites the store cell at the address
    /// bound to a variable without changing the environment mapping.
    /// Two variables aliasing the same address both see the mutation.
    Mutate,

    /// Evaluation complete — the term is in normal form.
    ///
    /// No rewrite rules apply to the current term (and all subterms are
    /// in normal form). The evaluator halts with the final result.
    Accept,
}

impl fmt::Display for EvalTransitionRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reduce => write!(f, "REDUCE"),
            Self::Descend => write!(f, "DESCEND"),
            Self::Ascend => write!(f, "ASCEND"),
            Self::Bind => write!(f, "BIND"),
            Self::Apply => write!(f, "APPLY"),
            Self::Mutate => write!(f, "MUTATE"),
            Self::Accept => write!(f, "ACCEPT"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation Continuation Frames
// ══════════════════════════════════════════════════════════════════════════════

/// Evaluation continuation frames — the **K** component of the evaluator CEK.
///
/// Each variant represents a "hole" in an evaluation context: the evaluator
/// has descended into a subterm and needs to know what to do with the result
/// when it ascends back.
///
/// ## Frame Variants
///
/// | Variant | Context | Waiting For |
/// |---------|---------|-------------|
/// | `BinOp` | `lhs ⊕ □` | RHS evaluation |
/// | `UnaryOp` | `⊕ □` | Operand evaluation |
/// | `MatchScrutinee` | `match □ { arms }` | Scrutinee evaluation |
/// | `LetBody` | `let x = □ in body` | Bound expression evaluation |
/// | `Parallel` | `□ \| remaining...` | Concurrent subterm evaluation |
/// | `RewriteCont` | `rule_name(□)` | Rewrite rule application |
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalFrame {
    /// Binary operator context: the LHS has been evaluated, waiting for the RHS.
    ///
    /// After the RHS subterm evaluates to a normal form, the evaluator
    /// reconstructs the binary expression and checks whether a rewrite
    /// rule now applies to the fully-evaluated expression.
    BinOp {
        /// The operator symbol (e.g., "+", "*", "&&").
        operator: String,
        /// Display representation of the already-evaluated LHS.
        lhs_display: String,
    },

    /// Unary operator context: waiting for the operand to evaluate.
    ///
    /// After the operand evaluates to a normal form, the evaluator
    /// reconstructs the unary expression and checks for applicable rules.
    UnaryOp {
        /// The operator symbol (e.g., "-", "not", "~").
        operator: String,
    },

    /// Match scrutinee context: evaluating the scrutinee before matching arms.
    ///
    /// After the scrutinee evaluates to a normal form, the evaluator
    /// pattern-matches against the arms to select the appropriate branch.
    MatchScrutinee {
        /// Display representation of the match arms for tracing.
        arms_display: String,
    },

    /// Let-binding context: evaluating the bound expression before the body.
    ///
    /// After the bound expression evaluates, the evaluator binds the
    /// result to `var_name` in the environment and proceeds to evaluate
    /// the body.
    LetBody {
        /// Variable name being bound.
        var_name: String,
        /// Display representation of the body expression for tracing.
        body_display: String,
    },

    /// Parallel evaluation context: evaluating concurrent subterms.
    ///
    /// Tracks which subterms remain to be evaluated and which have
    /// already completed. The evaluator processes subterms left-to-right
    /// in the single-threaded fallback path.
    ///
    /// ## M:N Scheduler Integration
    ///
    /// When the `green-threads` feature is enabled and the M:N runtime is
    /// active, `PPar(P, Q)` can be evaluated concurrently by forking each
    /// sub-term as a child green thread via [`GreenThread::fork_parallel()`].
    /// The children share the parent's environment spine (O(1) via `im`
    /// persistent data structures) and execute independently on worker
    /// threads with work-stealing load balancing.
    ///
    /// The fork decision is made by the evaluator or the green thread's
    /// `run_quantum()` method when it encounters a Parallel frame with
    /// multiple remaining sub-terms. The `QuantumResult::Forked` variant
    /// signals the worker to create child threads and enqueue them.
    Parallel {
        /// Display representations of subterms not yet evaluated.
        remaining: Vec<String>,
        /// Display representations of subterms already evaluated.
        completed: Vec<String>,
    },

    /// Rewrite continuation: a named rewrite rule is being applied.
    ///
    /// The evaluator is in the process of applying a specific rewrite
    /// rule. After the rule's RHS evaluates, the result replaces the
    /// original term.
    RewriteCont {
        /// Name of the rewrite rule being applied.
        rule_name: String,
    },

    /// Set (mutation) continuation: evaluating the expression for `set! var expr`.
    ///
    /// After the expression evaluates to a value, the store cell at the
    /// address bound to `var_name` is overwritten with the new value.
    /// The environment mapping is unchanged — mutation overwrites the
    /// store cell, not the binding.
    SetCont {
        /// Variable whose store cell should be mutated.
        var_name: String,
    },
}

impl EvalFrame {
    /// Return the variant name as a string (for tracing and diagnostics).
    pub fn variant_name(&self) -> &'static str {
        match self {
            Self::BinOp { .. } => "BinOp",
            Self::UnaryOp { .. } => "UnaryOp",
            Self::MatchScrutinee { .. } => "MatchScrutinee",
            Self::LetBody { .. } => "LetBody",
            Self::Parallel { .. } => "Parallel",
            Self::RewriteCont { .. } => "RewriteCont",
            Self::SetCont { .. } => "SetCont",
        }
    }
}

impl fmt::Display for EvalFrame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BinOp { operator, lhs_display } => {
                write!(f, "BinOp({} {} □)", lhs_display, operator)
            },
            Self::UnaryOp { operator } => {
                write!(f, "UnaryOp({} □)", operator)
            },
            Self::MatchScrutinee { arms_display } => {
                write!(f, "MatchScrutinee(□ {{ {} }})", arms_display)
            },
            Self::LetBody { var_name, body_display } => {
                write!(f, "LetBody(let {} = □ in {})", var_name, body_display)
            },
            Self::Parallel { remaining, completed } => {
                write!(
                    f,
                    "Parallel(done={}, remaining={})",
                    completed.len(),
                    remaining.len()
                )
            },
            Self::RewriteCont { rule_name } => {
                write!(f, "RewriteCont({})", rule_name)
            },
            Self::SetCont { var_name } => {
                write!(f, "SetCont(set! {} □)", var_name)
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation Step Event
// ══════════════════════════════════════════════════════════════════════════════

/// A single evaluation step event emitted at each CEK transition.
///
/// The observer receives this by reference, avoiding allocation on the
/// hot path. String fields are borrowed from the evaluator's internal state.
///
/// ## Fields
///
/// | Field | Description |
/// |-------|-------------|
/// | `rule` | Which transition rule fired |
/// | `term_display` | Current control term (display form) |
/// | `stack_depth` | Continuation stack depth |
/// | `env_size` | Number of variable bindings in the environment |
#[derive(Debug, Clone)]
pub struct EvalStepEvent<'a> {
    /// Which transition rule fired.
    pub rule: EvalTransitionRule,
    /// Display representation of the current control term.
    pub term_display: &'a str,
    /// Current continuation stack depth.
    pub stack_depth: usize,
    /// Number of variable bindings in the environment.
    pub env_size: usize,
    /// Number of cells in the local CESK store.
    pub local_store_size: usize,
}

// ══════════════════════════════════════════════════════════════════════════════
// Observer Trait
// ══════════════════════════════════════════════════════════════════════════════

/// Callback observer trait for runtime evaluation tracing.
///
/// Implement this to receive notifications at each CEK evaluation transition.
/// Return [`CekControl::Continue`] for zero-cost passthrough,
/// [`CekControl::Abort`] to halt evaluation immediately.
///
/// ## Consumer Patterns
///
/// | Consumer | Pattern | What It Reads |
/// |----------|---------|---------------|
/// | Profiler | `TracingEvalObserver` | Step counts, cache stats |
/// | Debugger | Custom observer with breakpoints | Term, env, stack |
/// | Batch | `NullEvalObserver` | Nothing (zero overhead) |
pub trait EvalObserver {
    /// Called at each CEK evaluation transition point.
    ///
    /// Return `CekControl::Continue` to proceed, or `CekControl::Abort`
    /// to halt evaluation immediately with the current partial result.
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl;
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation Trace Statistics
// ══════════════════════════════════════════════════════════════════════════════

/// Accumulated trace statistics from a complete or partial evaluation.
///
/// Provides aggregate data for profiling and visualization without
/// storing every individual event. Tracks per-rule counts, maximum
/// stack depth, and memo cache hit/miss statistics.
///
/// ## Cache Statistics
///
/// The `cache_hits` and `cache_misses` fields track the memoization
/// table's effectiveness. A high hit rate indicates many repeated
/// ground subterms in the input — common in Rholang's parallel
/// composition (e.g., `P | P | P` where `P` is ground).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EvalTrace {
    /// Total number of evaluation steps (all transition types).
    pub steps: usize,
    /// Per-rule activation counts.
    pub rule_counts: BTreeMap<EvalTransitionRule, usize>,
    /// Maximum continuation stack depth reached during evaluation.
    pub max_depth: usize,
    /// Number of memo cache hits (ground term lookups that succeeded).
    pub cache_hits: usize,
    /// Number of memo cache misses (ground term lookups that failed).
    pub cache_misses: usize,
}

impl EvalTrace {
    /// Create an empty trace.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a step event into this trace.
    pub fn record_step(&mut self, event: &EvalStepEvent<'_>) {
        self.steps += 1;
        *self.rule_counts.entry(event.rule).or_insert(0) += 1;
        if event.stack_depth > self.max_depth {
            self.max_depth = event.stack_depth;
        }
    }

    /// Record a memo cache hit.
    pub fn record_cache_hit(&mut self) {
        self.cache_hits += 1;
    }

    /// Record a memo cache miss.
    pub fn record_cache_miss(&mut self) {
        self.cache_misses += 1;
    }

    /// Total number of Reduce transitions.
    pub fn reduce_count(&self) -> usize {
        self.rule_counts
            .get(&EvalTransitionRule::Reduce)
            .copied()
            .unwrap_or(0)
    }

    /// Total number of Descend transitions.
    pub fn descend_count(&self) -> usize {
        self.rule_counts
            .get(&EvalTransitionRule::Descend)
            .copied()
            .unwrap_or(0)
    }

    /// Total number of Ascend transitions.
    pub fn ascend_count(&self) -> usize {
        self.rule_counts
            .get(&EvalTransitionRule::Ascend)
            .copied()
            .unwrap_or(0)
    }

    /// Total number of Apply transitions.
    pub fn apply_count(&self) -> usize {
        self.rule_counts
            .get(&EvalTransitionRule::Apply)
            .copied()
            .unwrap_or(0)
    }

    /// Memo cache hit rate as a fraction in [0.0, 1.0].
    ///
    /// Returns 0.0 if no cache lookups have been performed.
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }
}

impl fmt::Display for EvalTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "EvalTrace(steps={}, max_depth={}, cache_hit_rate={:.1}%)",
            self.steps,
            self.max_depth,
            self.cache_hit_rate() * 100.0
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluator State
// ══════════════════════════════════════════════════════════════════════════════

/// The evaluation state: which phase the evaluator is in.
///
/// Mirrors [`crate::cek::CekState`] but for rewriting rather than parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalState {
    /// Ready to begin evaluation.
    Ready,
    /// Reducing: selecting a rewrite rule for the current control term.
    Reducing,
    /// Descending: entering a subterm for evaluation.
    Descending,
    /// Ascending: returning from a subterm evaluation.
    Ascending,
    /// Evaluation completed — term is in normal form.
    Accepted,
    /// Evaluation aborted by observer.
    Aborted {
        /// Reason for abort.
        reason: String,
    },
    /// Evaluation error.
    Error {
        /// Error message.
        message: String,
    },
}

impl fmt::Display for EvalState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ready => write!(f, "Ready"),
            Self::Reducing => write!(f, "Reducing"),
            Self::Descending => write!(f, "Descending"),
            Self::Ascending => write!(f, "Ascending"),
            Self::Accepted => write!(f, "Accepted"),
            Self::Aborted { reason } => write!(f, "Aborted({})", reason),
            Self::Error { message } => write!(f, "Error({})", message),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Evaluator
// ══════════════════════════════════════════════════════════════════════════════

/// The result of a single evaluation step.
///
/// Indicates whether the evaluator should continue, has reached a terminal
/// state, or was aborted by the observer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// The evaluator performed a transition and should continue.
    Continue,
    /// The evaluator has reached a normal form (no more rules apply).
    Accepted,
    /// The evaluator was aborted by the observer.
    Aborted,
    /// An error occurred during evaluation.
    Error {
        /// Error message.
        message: String,
    },
}

/// CEK evaluator state machine for term rewriting.
///
/// Implements the CEK abstract machine adapted for rewrite-based evaluation:
///
/// - **C (Control)**: The current term being evaluated, represented as a
///   type-erased string display. This mirrors the parsing CEK's token-driven
///   dispatch but operates on AST terms instead.
///
/// - **E (Environment)**: Variable bindings from pattern matching during
///   rewrite rule application. When a rule's LHS pattern matches the control
///   term, pattern variables are bound in the environment and used for
///   substitution in the RHS.
///
/// - **K (Kontinuation)**: Evaluation context stack tracking which subterm
///   the evaluator is inside of. Each [`EvalFrame`] represents a "hole" in
///   the surrounding term.
///
/// ## Memoization
///
/// Ground terms (terms with no free variables) are cached in an internal
/// memo table. When the evaluator encounters a previously-reduced ground
/// term, it returns the cached normal form immediately. This is particularly
/// effective for Rholang's parallel composition, where identical processes
/// are composed multiple times.
///
/// ## Step Limit
///
/// To prevent divergent rewrites, the evaluator enforces a configurable
/// step limit (default: 10,000). Override with [`CekEvaluator::with_step_limit()`].
///
/// ## Usage
///
/// ```ignore
/// use prattail::cek_eval::{CekEvaluator, NullEvalObserver};
///
/// let mut evaluator = CekEvaluator::new("1 + 2".to_string());
/// let mut observer = NullEvalObserver;
/// let result = evaluator.run_to_completion(&mut observer);
/// assert_eq!(evaluator.control(), "3");
/// ```
pub struct CekEvaluator {
    /// **C (Control)**: Current term representation (type-erased string display).
    ///
    /// This is the term currently being evaluated. After each rewrite step,
    /// it is replaced by the rewritten form.
    control: String,

    /// **E (Environment)**: Variable bindings as address indirection.
    ///
    /// Maps variable names to `StoreAddr` values. The actual values are
    /// stored in `local_store` and resolved via two-stage lookup:
    /// `env[var] → StoreAddr::Local(id) → local_store[id] → StoreValue`.
    ///
    /// This indirection enables mutation (`set!`): two variables can share
    /// an address, and mutating through one is visible through the other.
    environment: HashMap<String, StoreAddr>,

    /// **K (Kontinuation)**: Evaluation context stack.
    ///
    /// Tracks the evaluation context — which subterm we descended into.
    /// When evaluation of a subterm completes, the top frame is popped
    /// and the result is integrated back into the enclosing expression.
    continuation: Vec<EvalFrame>,

    /// **S (Store)**: Local CESK store for the standalone evaluator.
    ///
    /// Maps addresses (`u64`) to `StoreValue`. Used by `bind()` to allocate
    /// values and by `lookup()` for two-stage resolution.
    local_store: LocalCeskStore,

    /// Active garbage collection strategy.
    gc_strategy: GcStrategy,

    /// Reference counting GC state (active when `gc_strategy == RefCount`).
    refcount_gc: Option<RefCountGc>,

    /// Memoization cache for ground terms.
    ///
    /// Maps ground term display strings to their normal forms. Avoids
    /// redundant evaluation of identical ground subterms.
    memo_cache: HashMap<String, String>,

    /// Current evaluation state.
    state: EvalState,

    /// Accumulated trace statistics.
    trace: EvalTrace,

    /// Maximum number of steps before forced termination.
    /// Prevents divergent rewrite sequences from running forever.
    step_limit: usize,
}

/// Default step limit for the evaluator.
const DEFAULT_STEP_LIMIT: usize = 10_000;

impl CekEvaluator {
    /// Create a new CEK evaluator with the given initial term.
    ///
    /// The evaluator starts in the `Ready` state with an empty environment
    /// and continuation stack.
    ///
    /// # Arguments
    ///
    /// - `initial_term`: The term to evaluate, in display representation.
    pub fn new(initial_term: String) -> Self {
        Self::with_gc_strategy(initial_term, GcStrategy::default())
    }

    /// Create a new evaluator with a specific GC strategy.
    pub fn with_gc_strategy(initial_term: String, gc_strategy: GcStrategy) -> Self {
        let refcount_gc = match gc_strategy {
            GcStrategy::RefCount => Some(RefCountGc::new()),
            _ => None,
        };
        Self {
            control: initial_term,
            environment: HashMap::new(),
            continuation: Vec::new(),
            local_store: LocalCeskStore::new(),
            gc_strategy,
            refcount_gc,
            memo_cache: HashMap::new(),
            state: EvalState::Ready,
            trace: EvalTrace::new(),
            step_limit: DEFAULT_STEP_LIMIT,
        }
    }

    /// Create a new evaluator with no GC (store grows monotonically).
    ///
    /// Best for short-lived evaluations bounded by a step limit.
    pub fn with_gc_none(initial_term: String) -> Self {
        Self::with_gc_strategy(initial_term, GcStrategy::None)
    }

    /// Create a new evaluator with a custom step limit.
    ///
    /// # Arguments
    ///
    /// - `initial_term`: The term to evaluate.
    /// - `step_limit`: Maximum number of evaluation steps before forced termination.
    pub fn with_step_limit(initial_term: String, step_limit: usize) -> Self {
        Self {
            step_limit,
            ..Self::new(initial_term)
        }
    }

    /// Create a new evaluator with a pre-populated environment.
    ///
    /// Useful for REPL sessions where variable bindings persist across
    /// successive evaluations. The string values are bulk-converted to
    /// store-backed bindings.
    ///
    /// # Arguments
    ///
    /// - `initial_term`: The term to evaluate.
    /// - `env`: Pre-existing variable bindings (string values).
    pub fn with_environment(initial_term: String, env: HashMap<String, String>) -> Self {
        let mut evaluator = Self::new(initial_term);
        for (name, value) in env {
            evaluator.bind(name, value);
        }
        evaluator
    }

    // ── Accessors ─────────────────────────────────────────────────────────

    /// The current control term (display representation).
    pub fn control(&self) -> &str {
        &self.control
    }

    /// The current environment (variable → store address mappings).
    pub fn environment(&self) -> &HashMap<String, StoreAddr> {
        &self.environment
    }

    /// The local CESK store.
    pub fn local_store(&self) -> &LocalCeskStore {
        &self.local_store
    }

    /// The active GC strategy.
    pub fn gc_strategy(&self) -> GcStrategy {
        self.gc_strategy
    }

    /// The current continuation stack.
    pub fn continuation(&self) -> &[EvalFrame] {
        &self.continuation
    }

    /// The current evaluation state.
    pub fn state(&self) -> &EvalState {
        &self.state
    }

    /// Accumulated trace statistics.
    pub fn trace(&self) -> &EvalTrace {
        &self.trace
    }

    /// Current continuation stack depth.
    pub fn stack_depth(&self) -> usize {
        self.continuation.len()
    }

    /// Number of variable bindings in the environment.
    pub fn env_size(&self) -> usize {
        self.environment.len()
    }

    /// Number of entries in the memo cache.
    pub fn memo_cache_size(&self) -> usize {
        self.memo_cache.len()
    }

    /// Whether the evaluator is in a terminal state (Accepted, Aborted, or Error).
    pub fn is_terminal(&self) -> bool {
        matches!(
            self.state,
            EvalState::Accepted | EvalState::Aborted { .. } | EvalState::Error { .. }
        )
    }

    // ── Environment manipulation ──────────────────────────────────────────

    /// Bind a variable in the environment via the CESK store.
    ///
    /// Allocates a `StoreValue::Simple(value)` in the local store,
    /// maps the variable name to the resulting `StoreAddr::Local(id)`,
    /// and increments the reference count (if refcount GC is active).
    ///
    /// Returns the previous string value if the variable was already bound.
    pub fn bind(&mut self, name: String, value: String) -> Option<String> {
        // Capture previous value for return
        let prev = self.lookup_string(&name).map(|s| s.to_string());

        // Unbind previous (dec_ref) if exists
        if let Some(old_addr) = self.environment.get(&name) {
            let old_id = old_addr.id();
            if let Some(ref mut gc) = self.refcount_gc {
                gc.dec_ref(old_id);
            }
        }

        // Allocate new value in store
        let id = self.local_store.alloc_with(StoreValue::Simple(value));
        let addr = StoreAddr::Local(id);

        // Track reference
        if let Some(ref mut gc) = self.refcount_gc {
            gc.inc_ref(id);
        }

        self.environment.insert(name, addr);
        prev
    }

    /// Look up a variable's string value via two-stage CESK resolution.
    ///
    /// `env[name] → StoreAddr → local_store[addr] → StoreValue → &str`
    ///
    /// Returns `None` if the variable is not bound or the value is not `Simple`.
    pub fn lookup(&self, name: &str) -> Option<&str> {
        self.environment.get(name).and_then(|addr| {
            self.local_store
                .get(addr.id())
                .and_then(|val| val.as_simple())
        })
    }

    /// Look up a variable's string value, returning an owned `String`.
    ///
    /// Convenience for callers that need `Option<&String>` compatibility.
    pub fn lookup_string(&self, name: &str) -> Option<&str> {
        self.lookup(name)
    }

    /// Look up the store address for a variable.
    pub fn lookup_addr(&self, name: &str) -> Option<StoreAddr> {
        self.environment.get(name).copied()
    }

    /// Look up the store value for a variable (any variant, not just Simple).
    pub fn lookup_value(&self, name: &str) -> Option<&StoreValue> {
        self.environment
            .get(name)
            .and_then(|addr| self.local_store.get(addr.id()))
    }

    /// Remove a variable binding from the environment.
    ///
    /// Decrements the reference count for the store address. Returns the
    /// previous string value if present.
    pub fn unbind(&mut self, name: &str) -> Option<String> {
        if let Some(addr) = self.environment.remove(name) {
            let id = addr.id();
            // Dec ref
            if let Some(ref mut gc) = self.refcount_gc {
                gc.dec_ref(id);
            }
            // Return previous value
            self.local_store
                .get(id)
                .and_then(|v| v.as_simple())
                .map(|s| s.to_string())
        } else {
            None
        }
    }

    /// Mutate the store cell at a variable's address without changing the env.
    ///
    /// This is the `set!` operation: `store[env[name]] = Simple(new_value)`.
    /// The environment mapping is unchanged — only the store cell is overwritten.
    /// Any other variable aliasing the same address will see the new value.
    ///
    /// Returns `true` if the mutation succeeded (variable exists), `false` otherwise.
    pub fn mutate(&mut self, name: &str, new_value: String) -> bool {
        if let Some(addr) = self.environment.get(name) {
            self.local_store
                .set(addr.id(), StoreValue::Simple(new_value));
            true
        } else {
            false
        }
    }

    /// Clear all variable bindings and their store cells.
    pub fn clear_environment(&mut self) {
        // Dec ref all bindings
        if let Some(ref mut gc) = self.refcount_gc {
            for addr in self.environment.values() {
                gc.dec_ref(addr.id());
            }
        }
        self.environment.clear();
    }

    /// Export the current environment as `HashMap<String, String>`.
    ///
    /// Resolves each `StoreAddr` back to a string value. Non-Simple
    /// store values are exported as their Display form.
    pub fn export_environment(&self) -> HashMap<String, String> {
        self.environment
            .iter()
            .filter_map(|(name, addr)| {
                self.local_store.get(addr.id()).map(|val| {
                    let s = match val {
                        StoreValue::Simple(s) => s.clone(),
                        other => format!("{}", other),
                    };
                    (name.clone(), s)
                })
            })
            .collect()
    }

    // ── CESK-8: Relation store ─────────────────────────────────────────

    /// Store a relation in the local CESK store.
    ///
    /// Used after Ascent fixpoint completes to cache derived relations
    /// for evaluator consultation during the `Reducing` phase.
    pub fn store_relation(
        &mut self,
        name: String,
        tuples: Vec<(String, String)>,
    ) -> StoreAddr {
        let id = self
            .local_store
            .alloc_with(StoreValue::Relation { name: name.clone(), tuples });
        let addr = StoreAddr::Local(id);
        // Store under a well-known key: __rel_<name>
        self.environment
            .insert(format!("__rel_{}", name), addr);
        addr
    }

    /// Look up a relation by name from the store.
    pub fn lookup_relation(&self, name: &str) -> Option<&[(String, String)]> {
        let key = format!("__rel_{}", name);
        self.environment.get(&key).and_then(|addr| {
            self.local_store
                .get(addr.id())
                .and_then(|val| val.as_relation().map(|(_, tuples)| tuples))
        })
    }

    // ── CESK-10: Rewrite rule store ─────────────────────────────────────

    /// Add a rewrite rule to the store.
    ///
    /// Makes rewrite rules first-class store values for MeTTa-style
    /// meta-programming. Returns the store address.
    pub fn add_rewrite_rule(
        &mut self,
        name: String,
        lhs_pattern: String,
        rhs_template: String,
        priority: u32,
    ) -> StoreAddr {
        let id = self.local_store.alloc_with(StoreValue::RewriteRule {
            name: name.clone(),
            lhs_pattern,
            rhs_template,
            priority,
            active: true,
        });
        let addr = StoreAddr::Local(id);
        self.environment
            .insert(format!("__rule_{}", name), addr);
        addr
    }

    /// Look up active rewrite rules, sorted by priority (lowest first).
    pub fn active_rewrite_rules(&self) -> Vec<(String, String, String, u32)> {
        let mut rules: Vec<_> = self
            .environment
            .iter()
            .filter(|(k, _)| k.starts_with("__rule_"))
            .filter_map(|(_, addr)| {
                self.local_store
                    .get(addr.id())
                    .and_then(|val| val.as_rewrite_rule())
                    .filter(|(_, _, _, _, active)| *active)
                    .map(|(name, lhs, rhs, priority, _)| {
                        (
                            name.to_string(),
                            lhs.to_string(),
                            rhs.to_string(),
                            priority,
                        )
                    })
            })
            .collect();
        rules.sort_by_key(|(_, _, _, p)| *p);
        rules
    }

    // ── CESK-11: E-class store ──────────────────────────────────────────

    /// Store an e-class in the local CESK store.
    pub fn store_eclass(
        &mut self,
        class_id: u64,
        members: Vec<String>,
        cost_leader: String,
    ) -> StoreAddr {
        let id = self.local_store.alloc_with(StoreValue::EClass {
            class_id,
            members,
            cost_leader,
        });
        StoreAddr::Local(id)
    }

    /// Look up the cost leader for a term via its e-class.
    ///
    /// Returns `Some(leader)` if the term has an e-class entry and the
    /// leader is different from the term itself (optimization opportunity).
    pub fn eclass_cost_leader(&self, term: &str) -> Option<&str> {
        // Search all e-class entries for one containing this term
        for (_, val) in self.local_store.iter() {
            if let Some((_, members, leader)) = val.as_eclass() {
                if members.iter().any(|m| m == term) && leader != term {
                    return Some(leader);
                }
            }
        }
        None
    }

    // ── Memo cache ────────────────────────────────────────────────────────

    /// Look up a ground term in the memo cache.
    ///
    /// Returns the normal form if the term has been previously evaluated.
    /// Records a cache hit or miss in the trace statistics.
    pub fn memo_lookup(&mut self, term: &str) -> Option<String> {
        if let Some(result) = self.memo_cache.get(term) {
            self.trace.record_cache_hit();
            Some(result.clone())
        } else {
            self.trace.record_cache_miss();
            None
        }
    }

    /// Insert a ground term and its normal form into the memo cache.
    pub fn memo_insert(&mut self, term: String, normal_form: String) {
        self.memo_cache.insert(term, normal_form);
    }

    /// Clear the memo cache.
    pub fn clear_memo_cache(&mut self) {
        self.memo_cache.clear();
    }

    // ── Continuation stack ────────────────────────────────────────────────

    /// Push a frame onto the continuation stack.
    pub fn push_frame(&mut self, frame: EvalFrame) {
        self.continuation.push(frame);
    }

    /// Pop the top frame from the continuation stack.
    pub fn pop_frame(&mut self) -> Option<EvalFrame> {
        self.continuation.pop()
    }

    /// Peek at the top frame without removing it.
    pub fn peek_frame(&self) -> Option<&EvalFrame> {
        self.continuation.last()
    }

    // ── Step execution ────────────────────────────────────────────────────

    /// Perform a single evaluation step.
    ///
    /// Executes one CEK transition and notifies the observer. Returns
    /// a [`StepResult`] indicating whether evaluation should continue.
    ///
    /// ## Evaluation Strategy
    ///
    /// The evaluator uses an innermost-first (eager) strategy:
    ///
    /// 1. **Reduce**: Check if any rewrite rule applies to the control term.
    /// 2. **Descend**: If the term has subterms, descend into the leftmost
    ///    unevaluated subterm (pushing a continuation frame).
    /// 3. **Ascend**: When a subterm reaches normal form, pop the frame and
    ///    integrate the result.
    /// 4. **Apply**: When all subterms are in normal form and a rule matches,
    ///    apply the rule.
    /// 5. **Accept**: When no rules apply and all subterms are in normal form.
    ///
    /// This method models the generic stepping behavior. Concrete rewrite
    /// rule matching is driven by the caller or by extending this evaluator
    /// with a rule set.
    pub fn step(&mut self, observer: &mut dyn EvalObserver) -> StepResult {
        // Enforce step limit
        if self.trace.steps >= self.step_limit {
            self.state = EvalState::Error {
                message: format!(
                    "step limit exceeded ({} steps)",
                    self.step_limit
                ),
            };
            return StepResult::Error {
                message: format!("step limit exceeded ({} steps)", self.step_limit),
            };
        }

        // Terminal states are idempotent
        if self.is_terminal() {
            return match &self.state {
                EvalState::Accepted => StepResult::Accepted,
                EvalState::Aborted { .. } => StepResult::Aborted,
                EvalState::Error { message } => StepResult::Error {
                    message: message.clone(),
                },
                _ => unreachable!(),
            };
        }

        // Determine the transition rule based on current state
        let rule = match &self.state {
            EvalState::Ready => EvalTransitionRule::Reduce,
            EvalState::Reducing => {
                // Check memo cache for ground terms
                if let Some(cached) = self.memo_cache.get(&self.control).cloned() {
                    self.trace.record_cache_hit();
                    self.control = cached;
                    // If we have a continuation, ascend; otherwise accept
                    if self.continuation.is_empty() {
                        EvalTransitionRule::Accept
                    } else {
                        EvalTransitionRule::Ascend
                    }
                } else {
                    self.trace.record_cache_miss();
                    // No cached result — decide based on continuation stack
                    if self.continuation.is_empty() {
                        // No continuation frames, no cached result: accept current form
                        EvalTransitionRule::Accept
                    } else {
                        // Has continuation frames: ascend to integrate result
                        EvalTransitionRule::Ascend
                    }
                }
            },
            EvalState::Descending => EvalTransitionRule::Descend,
            EvalState::Ascending => EvalTransitionRule::Ascend,
            _ => {
                return StepResult::Error {
                    message: format!("unexpected state: {}", self.state),
                };
            },
        };

        // Emit event to observer
        let event = EvalStepEvent {
            rule,
            term_display: &self.control,
            stack_depth: self.continuation.len(),
            env_size: self.environment.len(),
            local_store_size: self.local_store.len(),
        };

        // Record in trace
        self.trace.record_step(&event);

        // Check observer control
        let control = observer.on_eval_event(&event);
        if control == CekControl::Abort {
            self.state = EvalState::Aborted {
                reason: "observer abort".to_string(),
            };
            return StepResult::Aborted;
        }

        // Execute the transition
        match rule {
            EvalTransitionRule::Reduce => {
                self.state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalTransitionRule::Descend => {
                self.state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalTransitionRule::Ascend => {
                // Pop the top continuation frame and integrate
                if let Some(frame) = self.continuation.pop() {
                    match frame {
                        EvalFrame::BinOp { operator, lhs_display } => {
                            // Reconstruct binary expression
                            self.control = format!(
                                "({} {} {})",
                                lhs_display, operator, self.control
                            );
                            self.state = EvalState::Reducing;
                        },
                        EvalFrame::UnaryOp { operator } => {
                            // Reconstruct unary expression
                            self.control =
                                format!("({} {})", operator, self.control);
                            self.state = EvalState::Reducing;
                        },
                        EvalFrame::MatchScrutinee { .. } => {
                            // Scrutinee evaluated; move to reducing the match
                            self.state = EvalState::Reducing;
                        },
                        EvalFrame::LetBody { var_name, body_display } => {
                            // Bind the evaluated expression via CESK store
                            self.bind(var_name, self.control.clone());
                            self.control = body_display;
                            self.state = EvalState::Reducing;
                        },
                        EvalFrame::SetCont { var_name } => {
                            // Mutation: overwrite the store cell at env[var_name]
                            self.mutate(&var_name, self.control.clone());
                            self.control = "void".to_string();
                            self.state = EvalState::Reducing;
                        },
                        EvalFrame::Parallel {
                            mut remaining,
                            mut completed,
                        } => {
                            completed.push(self.control.clone());
                            if let Some(next) = remaining.pop() {
                                // More subterms to evaluate
                                self.control = next;
                                self.continuation.push(EvalFrame::Parallel {
                                    remaining,
                                    completed,
                                });
                                self.state = EvalState::Reducing;
                            } else {
                                // All subterms evaluated — reconstruct parallel term
                                self.control = format!("({})", completed.join(" | "));
                                self.state = EvalState::Reducing;
                            }
                        },
                        EvalFrame::RewriteCont { .. } => {
                            // Rule application result is already in control
                            self.state = EvalState::Reducing;
                        },
                    }
                } else {
                    // Stack empty: accept
                    self.state = EvalState::Accepted;
                }
                StepResult::Continue
            },
            EvalTransitionRule::Bind => {
                self.state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalTransitionRule::Apply => {
                self.state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalTransitionRule::Mutate => {
                self.state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalTransitionRule::Accept => {
                self.state = EvalState::Accepted;
                StepResult::Accepted
            },
        }
    }

    /// Run the evaluator to completion (or step limit).
    ///
    /// Repeatedly calls [`step()`](Self::step) until the evaluator reaches
    /// a terminal state. Returns the final control term (the normal form)
    /// or an error message.
    ///
    /// # Arguments
    ///
    /// - `observer`: The evaluation observer to notify at each step.
    pub fn run_to_completion(
        &mut self,
        observer: &mut dyn EvalObserver,
    ) -> Result<String, String> {
        loop {
            match self.step(observer) {
                StepResult::Continue => continue,
                StepResult::Accepted => return Ok(self.control.clone()),
                StepResult::Aborted => {
                    return Err(format!(
                        "evaluation aborted at step {}",
                        self.trace.steps
                    ));
                },
                StepResult::Error { message } => return Err(message),
            }
        }
    }

    /// Reset the evaluator with a new term, preserving the environment.
    ///
    /// Used for REPL sessions where variable bindings persist across
    /// successive evaluations but the control term changes.
    pub fn reset_with_term(&mut self, term: String) {
        self.control = term;
        self.continuation.clear();
        self.state = EvalState::Ready;
        self.trace = EvalTrace::new();
        // Environment, local store, and memo cache are preserved
    }

    /// Fully reset the evaluator, clearing everything including the store.
    pub fn reset_full(&mut self, term: String) {
        self.control = term;
        self.clear_environment();
        self.continuation.clear();
        self.local_store.reset();
        self.memo_cache.clear();
        self.state = EvalState::Ready;
        self.trace = EvalTrace::new();
        if let Some(ref mut gc) = self.refcount_gc {
            gc.clear();
        }
    }

    // ── External driving methods ──────────────────────────────────────────
    // These allow callers to explicitly drive transitions for integration
    // with external rewrite rule engines.

    /// Set the control term (external rewrite rule engine drives this).
    pub fn set_control(&mut self, term: String) {
        self.control = term;
    }

    /// Set the evaluation state (external rewrite rule engine drives this).
    pub fn set_state(&mut self, state: EvalState) {
        self.state = state;
    }

    /// Emit a Bind event and record a variable binding via the CESK store.
    ///
    /// This is called by external rewrite rule engines when a pattern
    /// match binds a variable. Notifies the observer and records the
    /// transition in the trace.
    pub fn emit_bind(
        &mut self,
        name: String,
        value: String,
        observer: &mut dyn EvalObserver,
    ) -> CekControl {
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Bind,
            term_display: &self.control,
            stack_depth: self.continuation.len(),
            env_size: self.environment.len(),
            local_store_size: self.local_store.len(),
        };
        self.trace.record_step(&event);
        let ctrl = observer.on_eval_event(&event);
        self.bind(name, value);
        ctrl
    }

    /// Emit a Mutate event for `set!` operations.
    ///
    /// Called by external rule engines when a mutation is performed.
    pub fn emit_mutate(
        &mut self,
        var_name: &str,
        new_value: String,
        observer: &mut dyn EvalObserver,
    ) -> CekControl {
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Mutate,
            term_display: &self.control,
            stack_depth: self.continuation.len(),
            env_size: self.environment.len(),
            local_store_size: self.local_store.len(),
        };
        self.trace.record_step(&event);
        let ctrl = observer.on_eval_event(&event);
        self.mutate(var_name, new_value);
        ctrl
    }

    /// Emit an Apply event.
    ///
    /// Called by external rewrite rule engines when a rule fires.
    /// The caller is responsible for updating the control term afterward.
    pub fn emit_apply(
        &mut self,
        observer: &mut dyn EvalObserver,
    ) -> CekControl {
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Apply,
            term_display: &self.control,
            stack_depth: self.continuation.len(),
            env_size: self.environment.len(),
            local_store_size: self.local_store.len(),
        };
        self.trace.record_step(&event);
        observer.on_eval_event(&event)
    }

    /// Emit a Descend event and push a continuation frame.
    ///
    /// Called by external rewrite rule engines when entering a subterm.
    pub fn emit_descend(
        &mut self,
        subterm: String,
        frame: EvalFrame,
        observer: &mut dyn EvalObserver,
    ) -> CekControl {
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Descend,
            term_display: &self.control,
            stack_depth: self.continuation.len(),
            env_size: self.environment.len(),
            local_store_size: self.local_store.len(),
        };
        self.trace.record_step(&event);
        let ctrl = observer.on_eval_event(&event);
        self.continuation.push(frame);
        self.control = subterm;
        self.state = EvalState::Reducing;
        ctrl
    }

    /// Execute up to `max_steps` evaluation steps.
    ///
    /// Convenience method that repeatedly calls [`step()`](Self::step) up to
    /// `max_steps` times. Returns the final `StepResult`.
    ///
    /// Used by the REPL for batch stepping and by the green thread runtime
    /// for quantum-based execution.
    pub fn step_quantum(
        &mut self,
        max_steps: usize,
        observer: &mut dyn EvalObserver,
    ) -> StepResult {
        for _ in 0..max_steps {
            match self.step(observer) {
                StepResult::Continue => continue,
                terminal => return terminal,
            }
        }
        StepResult::Continue
    }

}

impl fmt::Debug for CekEvaluator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CekEvaluator")
            .field("control", &self.control)
            .field("env_size", &self.environment.len())
            .field("store_size", &self.local_store.len())
            .field("stack_depth", &self.continuation.len())
            .field("state", &self.state)
            .field("gc_strategy", &self.gc_strategy)
            .field("steps", &self.trace.steps)
            .field("memo_cache_size", &self.memo_cache.len())
            .finish()
    }
}

impl fmt::Display for CekEvaluator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CekEvaluator(C=\"{}\", |E|={}, |K|={}, state={})",
            self.control,
            self.environment.len(),
            self.continuation.len(),
            self.state
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Observer Implementations
// ══════════════════════════════════════════════════════════════════════════════

/// A tracing observer that collects full [`EvalTrace`] statistics.
///
/// Records every evaluation step and maintains aggregate counters for
/// profiling and debugging. Analogous to [`crate::cek::TracingObserver`]
/// for parsing.
///
/// ## Usage
///
/// ```ignore
/// use prattail::cek_eval::{CekEvaluator, TracingEvalObserver};
///
/// let mut evaluator = CekEvaluator::new("1 + 2".to_string());
/// let mut observer = TracingEvalObserver::new();
/// let result = evaluator.run_to_completion(&mut observer);
/// println!("{}", observer.trace());
/// ```
#[derive(Debug, Clone, Default)]
pub struct TracingEvalObserver {
    /// Accumulated trace statistics.
    trace: EvalTrace,
    /// Optional: log of all events as `(rule, term_display)` pairs.
    /// Only populated when `record_events` is true.
    events: Vec<(EvalTransitionRule, String)>,
    /// Whether to record individual events (more memory but full replay).
    record_events: bool,
}

impl TracingEvalObserver {
    /// Create a new tracing observer (aggregate statistics only).
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a tracing observer that also records individual events.
    ///
    /// This enables full replay of the evaluation trace but uses more
    /// memory. Use for debugging; prefer `new()` for profiling.
    pub fn with_event_recording() -> Self {
        Self {
            record_events: true,
            ..Self::default()
        }
    }

    /// The accumulated trace statistics.
    pub fn trace(&self) -> &EvalTrace {
        &self.trace
    }

    /// The recorded events (empty if `record_events` is false).
    pub fn events(&self) -> &[(EvalTransitionRule, String)] {
        &self.events
    }

    /// Number of events recorded.
    pub fn event_count(&self) -> usize {
        self.events.len()
    }
}

impl EvalObserver for TracingEvalObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl {
        self.trace.record_step(event);
        if self.record_events {
            self.events
                .push((event.rule, event.term_display.to_string()));
        }
        CekControl::Continue
    }
}

/// A no-op observer that discards all evaluation events.
///
/// Zero overhead: the compiler can inline and eliminate the calls.
/// Use for batch evaluation where no tracing is needed.
#[derive(Debug, Clone, Copy, Default)]
pub struct NullEvalObserver;

impl EvalObserver for NullEvalObserver {
    #[inline(always)]
    fn on_eval_event(&mut self, _event: &EvalStepEvent<'_>) -> CekControl {
        CekControl::Continue
    }
}

/// An observer that aborts evaluation after a specified number of steps.
///
/// Useful for testing and for implementing user-visible "cancel" behavior.
#[derive(Debug, Clone)]
pub struct AbortAfterObserver {
    /// Number of steps after which to abort.
    abort_after: usize,
    /// Current step count.
    step_count: usize,
}

impl AbortAfterObserver {
    /// Create an observer that aborts after `n` steps.
    pub fn new(abort_after: usize) -> Self {
        Self {
            abort_after,
            step_count: 0,
        }
    }

    /// The current step count.
    pub fn step_count(&self) -> usize {
        self.step_count
    }
}

impl EvalObserver for AbortAfterObserver {
    fn on_eval_event(&mut self, _event: &EvalStepEvent<'_>) -> CekControl {
        self.step_count += 1;
        if self.step_count >= self.abort_after {
            CekControl::Abort
        } else {
            CekControl::Continue
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── EvalTransitionRule tests ──────────────────────────────────────────

    #[test]
    fn test_eval_transition_rule_display() {
        assert_eq!(EvalTransitionRule::Reduce.to_string(), "REDUCE");
        assert_eq!(EvalTransitionRule::Descend.to_string(), "DESCEND");
        assert_eq!(EvalTransitionRule::Ascend.to_string(), "ASCEND");
        assert_eq!(EvalTransitionRule::Bind.to_string(), "BIND");
        assert_eq!(EvalTransitionRule::Apply.to_string(), "APPLY");
        assert_eq!(EvalTransitionRule::Accept.to_string(), "ACCEPT");
    }

    #[test]
    fn test_eval_transition_rule_equality_and_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(EvalTransitionRule::Reduce);
        set.insert(EvalTransitionRule::Descend);
        set.insert(EvalTransitionRule::Reduce); // duplicate
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_eval_transition_rule_ord() {
        // Verify that Ord is consistent (Reduce < Descend < ... < Accept)
        assert!(EvalTransitionRule::Reduce < EvalTransitionRule::Descend);
        assert!(EvalTransitionRule::Descend < EvalTransitionRule::Ascend);
        assert!(EvalTransitionRule::Ascend < EvalTransitionRule::Bind);
        assert!(EvalTransitionRule::Bind < EvalTransitionRule::Apply);
        assert!(EvalTransitionRule::Apply < EvalTransitionRule::Accept);
    }

    // ── EvalFrame tests ──────────────────────────────────────────────────

    #[test]
    fn test_eval_frame_variant_names() {
        assert_eq!(
            EvalFrame::BinOp {
                operator: "+".to_string(),
                lhs_display: "1".to_string(),
            }
            .variant_name(),
            "BinOp"
        );
        assert_eq!(
            EvalFrame::UnaryOp {
                operator: "-".to_string(),
            }
            .variant_name(),
            "UnaryOp"
        );
        assert_eq!(
            EvalFrame::MatchScrutinee {
                arms_display: "...".to_string(),
            }
            .variant_name(),
            "MatchScrutinee"
        );
        assert_eq!(
            EvalFrame::LetBody {
                var_name: "x".to_string(),
                body_display: "x + 1".to_string(),
            }
            .variant_name(),
            "LetBody"
        );
        assert_eq!(
            EvalFrame::Parallel {
                remaining: vec![],
                completed: vec![],
            }
            .variant_name(),
            "Parallel"
        );
        assert_eq!(
            EvalFrame::RewriteCont {
                rule_name: "beta".to_string(),
            }
            .variant_name(),
            "RewriteCont"
        );
    }

    #[test]
    fn test_eval_frame_display() {
        let frame = EvalFrame::BinOp {
            operator: "+".to_string(),
            lhs_display: "1".to_string(),
        };
        let s = frame.to_string();
        assert!(s.contains("BinOp"));
        assert!(s.contains("1"));
        assert!(s.contains("+"));

        let frame2 = EvalFrame::Parallel {
            remaining: vec!["a".to_string(), "b".to_string()],
            completed: vec!["c".to_string()],
        };
        let s2 = frame2.to_string();
        assert!(s2.contains("done=1"));
        assert!(s2.contains("remaining=2"));
    }

    // ── EvalTrace tests ──────────────────────────────────────────────────

    #[test]
    fn test_eval_trace_new() {
        let trace = EvalTrace::new();
        assert_eq!(trace.steps, 0);
        assert_eq!(trace.max_depth, 0);
        assert_eq!(trace.cache_hits, 0);
        assert_eq!(trace.cache_misses, 0);
        assert_eq!(trace.reduce_count(), 0);
        assert_eq!(trace.descend_count(), 0);
        assert_eq!(trace.ascend_count(), 0);
        assert_eq!(trace.apply_count(), 0);
    }

    #[test]
    fn test_eval_trace_record_step() {
        let mut trace = EvalTrace::new();
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Reduce,
            term_display: "1 + 2",
            stack_depth: 0,
            env_size: 0,
            local_store_size: 0,
        };
        trace.record_step(&event);
        assert_eq!(trace.steps, 1);
        assert_eq!(trace.reduce_count(), 1);
        assert_eq!(trace.max_depth, 0);

        let event2 = EvalStepEvent {
            rule: EvalTransitionRule::Descend,
            term_display: "1",
            stack_depth: 3,
            env_size: 1,
            local_store_size: 0,
        };
        trace.record_step(&event2);
        assert_eq!(trace.steps, 2);
        assert_eq!(trace.descend_count(), 1);
        assert_eq!(trace.max_depth, 3);
    }

    #[test]
    fn test_eval_trace_cache_stats() {
        let mut trace = EvalTrace::new();
        trace.record_cache_hit();
        trace.record_cache_hit();
        trace.record_cache_miss();
        assert_eq!(trace.cache_hits, 2);
        assert_eq!(trace.cache_misses, 1);
        let rate = trace.cache_hit_rate();
        assert!((rate - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_eval_trace_cache_hit_rate_zero_lookups() {
        let trace = EvalTrace::new();
        assert_eq!(trace.cache_hit_rate(), 0.0);
    }

    #[test]
    fn test_eval_trace_display() {
        let trace = EvalTrace {
            steps: 42,
            max_depth: 5,
            cache_hits: 7,
            cache_misses: 3,
            ..EvalTrace::default()
        };
        let s = trace.to_string();
        assert!(s.contains("steps=42"));
        assert!(s.contains("max_depth=5"));
        assert!(s.contains("70.0%"));
    }

    // ── EvalState tests ──────────────────────────────────────────────────

    #[test]
    fn test_eval_state_display() {
        assert_eq!(EvalState::Ready.to_string(), "Ready");
        assert_eq!(EvalState::Reducing.to_string(), "Reducing");
        assert_eq!(EvalState::Descending.to_string(), "Descending");
        assert_eq!(EvalState::Ascending.to_string(), "Ascending");
        assert_eq!(EvalState::Accepted.to_string(), "Accepted");
        assert_eq!(
            EvalState::Aborted {
                reason: "test".to_string()
            }
            .to_string(),
            "Aborted(test)"
        );
        assert_eq!(
            EvalState::Error {
                message: "oops".to_string()
            }
            .to_string(),
            "Error(oops)"
        );
    }

    // ── CekEvaluator construction tests ──────────────────────────────────

    #[test]
    fn test_evaluator_new() {
        let eval = CekEvaluator::new("1 + 2".to_string());
        assert_eq!(eval.control(), "1 + 2");
        assert_eq!(eval.env_size(), 0);
        assert_eq!(eval.stack_depth(), 0);
        assert_eq!(eval.memo_cache_size(), 0);
        assert!(!eval.is_terminal());
        assert_eq!(*eval.state(), EvalState::Ready);
    }

    #[test]
    fn test_evaluator_with_step_limit() {
        let eval = CekEvaluator::with_step_limit("x".to_string(), 5);
        assert_eq!(eval.control(), "x");
        assert_eq!(eval.step_limit, 5);
    }

    #[test]
    fn test_evaluator_with_environment() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), "42".to_string());
        let eval = CekEvaluator::with_environment("x".to_string(), env);
        assert_eq!(eval.env_size(), 1);
        assert_eq!(eval.lookup("x"), Some("42"));
    }

    // ── Environment manipulation tests ───────────────────────────────────

    #[test]
    fn test_evaluator_bind_lookup_unbind() {
        let mut eval = CekEvaluator::new("x".to_string());

        // Bind
        assert_eq!(eval.bind("x".to_string(), "42".to_string()), None);
        assert_eq!(eval.env_size(), 1);
        assert_eq!(eval.lookup("x"), Some("42"));

        // Re-bind (returns old value)
        assert_eq!(
            eval.bind("x".to_string(), "99".to_string()),
            Some("42".to_string())
        );
        assert_eq!(eval.lookup("x"), Some("99"));

        // Unbind
        assert_eq!(eval.unbind("x"), Some("99".to_string()));
        assert_eq!(eval.lookup("x"), None);
        assert_eq!(eval.env_size(), 0);

        // Unbind non-existent
        assert_eq!(eval.unbind("y"), None);
    }

    #[test]
    fn test_evaluator_clear_environment() {
        let mut eval = CekEvaluator::new("x".to_string());
        eval.bind("x".to_string(), "1".to_string());
        eval.bind("y".to_string(), "2".to_string());
        assert_eq!(eval.env_size(), 2);

        eval.clear_environment();
        assert_eq!(eval.env_size(), 0);
    }

    // ── Memo cache tests ─────────────────────────────────────────────────

    #[test]
    fn test_evaluator_memo_cache() {
        let mut eval = CekEvaluator::new("t".to_string());

        // Miss
        assert_eq!(eval.memo_lookup("1 + 2"), None);
        assert_eq!(eval.trace().cache_misses, 1);

        // Insert
        eval.memo_insert("1 + 2".to_string(), "3".to_string());
        assert_eq!(eval.memo_cache_size(), 1);

        // Hit
        assert_eq!(eval.memo_lookup("1 + 2"), Some("3".to_string()));
        assert_eq!(eval.trace().cache_hits, 1);

        // Clear
        eval.clear_memo_cache();
        assert_eq!(eval.memo_cache_size(), 0);
    }

    // ── Continuation stack tests ─────────────────────────────────────────

    #[test]
    fn test_evaluator_continuation_stack() {
        let mut eval = CekEvaluator::new("t".to_string());
        assert_eq!(eval.stack_depth(), 0);
        assert_eq!(eval.peek_frame(), None);

        let frame = EvalFrame::BinOp {
            operator: "+".to_string(),
            lhs_display: "1".to_string(),
        };
        eval.push_frame(frame.clone());
        assert_eq!(eval.stack_depth(), 1);
        assert_eq!(eval.peek_frame().expect("should have frame").variant_name(), "BinOp");

        let popped = eval.pop_frame();
        assert_eq!(popped, Some(frame));
        assert_eq!(eval.stack_depth(), 0);

        // Pop empty
        assert_eq!(eval.pop_frame(), None);
    }

    // ── Step and run_to_completion tests ──────────────────────────────────

    #[test]
    fn test_evaluator_step_ready_to_accepted_empty_stack() {
        // With no continuation frames and no memo cache entry,
        // the evaluator should: Ready -> step(Reduce) -> Reducing -> step(Accept) -> Accepted
        let mut eval = CekEvaluator::new("42".to_string());
        let mut obs = NullEvalObserver;

        // Step 1: Ready -> Reducing (Reduce transition)
        let r1 = eval.step(&mut obs);
        assert_eq!(r1, StepResult::Continue);
        assert_eq!(*eval.state(), EvalState::Reducing);

        // Step 2: Reducing with empty stack and no cache -> Accept
        let r2 = eval.step(&mut obs);
        assert_eq!(r2, StepResult::Accepted);
        assert_eq!(*eval.state(), EvalState::Accepted);
        assert_eq!(eval.control(), "42");
    }

    #[test]
    fn test_evaluator_run_to_completion_simple() {
        let mut eval = CekEvaluator::new("normal_form".to_string());
        let mut obs = NullEvalObserver;

        let result = eval.run_to_completion(&mut obs);
        assert_eq!(result, Ok("normal_form".to_string()));
        assert!(eval.is_terminal());
    }

    #[test]
    fn test_evaluator_run_to_completion_with_memo_hit() {
        let mut eval = CekEvaluator::new("cached_term".to_string());
        eval.memo_insert("cached_term".to_string(), "result".to_string());

        let mut obs = NullEvalObserver;
        let result = eval.run_to_completion(&mut obs);
        assert_eq!(result, Ok("result".to_string()));
        assert!(eval.trace().cache_hits > 0);
    }

    #[test]
    fn test_evaluator_step_limit_enforced() {
        // Use a very small step limit. The evaluator cycles through
        // Ready -> Reducing -> (cache miss, ascend from frame) ->
        // Reducing -> ... until the limit is hit.
        let mut eval = CekEvaluator::with_step_limit("divergent".to_string(), 5);

        // Push a RewriteCont frame so the evaluator ascends back to
        // Reducing instead of accepting, creating a cycle:
        //   Reducing -> Ascend (pop RewriteCont) -> Reducing -> Accept
        // With the memo cache mapping to itself, the Reducing state hits
        // the cache and stays on the same term, but the stack is now empty
        // so it accepts. We need multiple frames to keep cycling.
        // Instead, just push enough frames to exhaust the step limit.
        eval.push_frame(EvalFrame::RewriteCont { rule_name: "r1".to_string() });
        eval.push_frame(EvalFrame::RewriteCont { rule_name: "r2".to_string() });
        eval.push_frame(EvalFrame::RewriteCont { rule_name: "r3".to_string() });
        eval.push_frame(EvalFrame::RewriteCont { rule_name: "r4".to_string() });
        eval.push_frame(EvalFrame::RewriteCont { rule_name: "r5".to_string() });

        let mut obs = NullEvalObserver;

        // Run up to the step limit
        let result = eval.run_to_completion(&mut obs);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("step limit exceeded"));
    }

    #[test]
    fn test_evaluator_abort_by_observer() {
        let mut eval = CekEvaluator::new("term".to_string());
        let mut obs = AbortAfterObserver::new(1);

        let result = eval.run_to_completion(&mut obs);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("aborted"));
        assert_eq!(*eval.state(), EvalState::Aborted {
            reason: "observer abort".to_string(),
        });
    }

    // ── Ascend integration tests ─────────────────────────────────────────

    #[test]
    fn test_evaluator_ascend_binop_frame() {
        let mut eval = CekEvaluator::new("2".to_string());
        eval.set_state(EvalState::Ascending);
        eval.push_frame(EvalFrame::BinOp {
            operator: "+".to_string(),
            lhs_display: "1".to_string(),
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Continue);
        assert_eq!(eval.control(), "(1 + 2)");
        assert_eq!(*eval.state(), EvalState::Reducing);
    }

    #[test]
    fn test_evaluator_ascend_unary_frame() {
        let mut eval = CekEvaluator::new("5".to_string());
        eval.set_state(EvalState::Ascending);
        eval.push_frame(EvalFrame::UnaryOp {
            operator: "-".to_string(),
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Continue);
        assert_eq!(eval.control(), "(- 5)");
    }

    #[test]
    fn test_evaluator_ascend_let_body_frame() {
        let mut eval = CekEvaluator::new("42".to_string());
        eval.set_state(EvalState::Ascending);
        eval.push_frame(EvalFrame::LetBody {
            var_name: "x".to_string(),
            body_display: "x + 1".to_string(),
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Continue);
        assert_eq!(eval.control(), "x + 1");
        assert_eq!(eval.lookup("x"), Some("42"));
    }

    #[test]
    fn test_evaluator_ascend_parallel_frame_partial() {
        let mut eval = CekEvaluator::new("P".to_string());
        eval.set_state(EvalState::Ascending);
        eval.push_frame(EvalFrame::Parallel {
            remaining: vec!["R".to_string()],
            completed: vec!["Q".to_string()],
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Continue);
        // The evaluator should now be working on "R"
        assert_eq!(eval.control(), "R");
        // There should still be a Parallel frame on the stack
        assert_eq!(eval.stack_depth(), 1);
    }

    #[test]
    fn test_evaluator_ascend_parallel_frame_complete() {
        let mut eval = CekEvaluator::new("P".to_string());
        eval.set_state(EvalState::Ascending);
        eval.push_frame(EvalFrame::Parallel {
            remaining: vec![],
            completed: vec!["Q".to_string()],
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Continue);
        assert_eq!(eval.control(), "(Q | P)");
        assert_eq!(eval.stack_depth(), 0);
    }

    // ── External driving tests ───────────────────────────────────────────

    #[test]
    fn test_evaluator_emit_bind() {
        let mut eval = CekEvaluator::new("let x = 5 in x".to_string());
        let mut obs = TracingEvalObserver::with_event_recording();

        let ctrl = eval.emit_bind("x".to_string(), "5".to_string(), &mut obs);
        assert_eq!(ctrl, CekControl::Continue);
        assert_eq!(eval.lookup("x"), Some("5"));
        assert_eq!(obs.trace().steps, 1);
        assert_eq!(
            obs.trace()
                .rule_counts
                .get(&EvalTransitionRule::Bind)
                .copied()
                .unwrap_or(0),
            1
        );
        assert_eq!(obs.events().len(), 1);
        assert_eq!(obs.events()[0].0, EvalTransitionRule::Bind);
    }

    #[test]
    fn test_evaluator_emit_apply() {
        let mut eval = CekEvaluator::new("1 + 2".to_string());
        let mut obs = TracingEvalObserver::new();

        let ctrl = eval.emit_apply(&mut obs);
        assert_eq!(ctrl, CekControl::Continue);
        assert_eq!(obs.trace().apply_count(), 1);
    }

    #[test]
    fn test_evaluator_emit_descend() {
        let mut eval = CekEvaluator::new("1 + 2".to_string());
        let mut obs = TracingEvalObserver::new();

        let ctrl = eval.emit_descend(
            "1".to_string(),
            EvalFrame::BinOp {
                operator: "+".to_string(),
                lhs_display: "□".to_string(),
            },
            &mut obs,
        );
        assert_eq!(ctrl, CekControl::Continue);
        assert_eq!(eval.control(), "1");
        assert_eq!(eval.stack_depth(), 1);
        assert_eq!(*eval.state(), EvalState::Reducing);
        assert_eq!(obs.trace().descend_count(), 1);
    }

    // ── Reset tests ──────────────────────────────────────────────────────

    #[test]
    fn test_evaluator_reset_with_term() {
        let mut eval = CekEvaluator::new("old".to_string());
        eval.bind("x".to_string(), "1".to_string());
        eval.memo_insert("cached".to_string(), "result".to_string());
        eval.push_frame(EvalFrame::UnaryOp {
            operator: "-".to_string(),
        });

        eval.reset_with_term("new".to_string());
        assert_eq!(eval.control(), "new");
        assert_eq!(*eval.state(), EvalState::Ready);
        assert_eq!(eval.stack_depth(), 0);
        assert_eq!(eval.trace().steps, 0);
        // Environment and memo cache are preserved
        assert_eq!(eval.env_size(), 1);
        assert_eq!(eval.memo_cache_size(), 1);
    }

    #[test]
    fn test_evaluator_reset_full() {
        let mut eval = CekEvaluator::new("old".to_string());
        eval.bind("x".to_string(), "1".to_string());
        eval.memo_insert("cached".to_string(), "result".to_string());

        eval.reset_full("new".to_string());
        assert_eq!(eval.control(), "new");
        assert_eq!(eval.env_size(), 0);
        assert_eq!(eval.memo_cache_size(), 0);
        assert_eq!(eval.stack_depth(), 0);
    }

    // ── Observer tests ───────────────────────────────────────────────────

    #[test]
    fn test_null_eval_observer() {
        let mut obs = NullEvalObserver;
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Reduce,
            term_display: "1 + 2",
            stack_depth: 0,
            env_size: 0,
            local_store_size: 0,
        };
        assert_eq!(obs.on_eval_event(&event), CekControl::Continue);
    }

    #[test]
    fn test_tracing_eval_observer_aggregate() {
        let mut obs = TracingEvalObserver::new();
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Reduce,
            term_display: "1 + 2",
            stack_depth: 0,
            env_size: 0,
            local_store_size: 0,
        };
        let ctrl = obs.on_eval_event(&event);
        assert_eq!(ctrl, CekControl::Continue);
        assert_eq!(obs.trace().steps, 1);
        assert_eq!(obs.trace().reduce_count(), 1);
        // No event recording by default
        assert!(obs.events().is_empty());
    }

    #[test]
    fn test_tracing_eval_observer_with_recording() {
        let mut obs = TracingEvalObserver::with_event_recording();
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Descend,
            term_display: "subterm",
            stack_depth: 2,
            env_size: 1,
            local_store_size: 0,
        };
        obs.on_eval_event(&event);
        assert_eq!(obs.event_count(), 1);
        assert_eq!(obs.events()[0].0, EvalTransitionRule::Descend);
        assert_eq!(obs.events()[0].1, "subterm");
    }

    #[test]
    fn test_abort_after_observer() {
        let mut obs = AbortAfterObserver::new(3);
        let event = EvalStepEvent {
            rule: EvalTransitionRule::Reduce,
            term_display: "t",
            stack_depth: 0,
            env_size: 0,
            local_store_size: 0,
        };

        assert_eq!(obs.on_eval_event(&event), CekControl::Continue);
        assert_eq!(obs.on_eval_event(&event), CekControl::Continue);
        assert_eq!(obs.on_eval_event(&event), CekControl::Abort);
        assert_eq!(obs.step_count(), 3);
    }

    // ── Display/Debug tests ──────────────────────────────────────────────

    #[test]
    fn test_evaluator_display() {
        let eval = CekEvaluator::new("1 + 2".to_string());
        let s = eval.to_string();
        assert!(s.contains("1 + 2"));
        assert!(s.contains("|E|=0"));
        assert!(s.contains("|K|=0"));
        assert!(s.contains("Ready"));
    }

    #[test]
    fn test_evaluator_debug() {
        let eval = CekEvaluator::new("1 + 2".to_string());
        let s = format!("{:?}", eval);
        assert!(s.contains("CekEvaluator"));
        assert!(s.contains("1 + 2"));
    }

    // ── Terminal state idempotency ───────────────────────────────────────

    #[test]
    fn test_evaluator_step_after_accepted_is_idempotent() {
        let mut eval = CekEvaluator::new("42".to_string());
        let mut obs = NullEvalObserver;

        // Run to completion
        let _ = eval.run_to_completion(&mut obs);
        assert!(eval.is_terminal());

        // Additional steps should be idempotent
        let r = eval.step(&mut obs);
        assert_eq!(r, StepResult::Accepted);
    }

    #[test]
    fn test_evaluator_step_after_error_is_idempotent() {
        let mut eval = CekEvaluator::new("x".to_string());
        eval.set_state(EvalState::Error {
            message: "test error".to_string(),
        });

        let mut obs = NullEvalObserver;
        let r = eval.step(&mut obs);
        match r {
            StepResult::Error { message } => {
                assert_eq!(message, "test error");
            },
            other => panic!("expected Error, got {:?}", other),
        }
    }

    // ── step_quantum and export_environment tests ─────────────────────────

    #[test]
    fn test_step_quantum_runs_to_completion() {
        let mut eval = CekEvaluator::new("simple".to_string());
        let mut obs = NullEvalObserver;
        let result = eval.step_quantum(100, &mut obs);
        assert_eq!(result, StepResult::Accepted);
        assert!(eval.is_terminal());
    }

    #[test]
    fn test_export_environment() {
        let mut eval = CekEvaluator::new("t".to_string());
        eval.bind("x".to_string(), "42".to_string());
        eval.bind("y".to_string(), "99".to_string());
        let env = eval.export_environment();
        assert_eq!(env.len(), 2);
        assert_eq!(env.get("x").map(String::as_str), Some("42"));
        assert_eq!(env.get("y").map(String::as_str), Some("99"));
    }

    // ── Property-Based Tests (proptest) ──────────────────────────────────

    mod proptest_cek_eval {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Step monotonicity: the step count in the trace never decreases
            /// across consecutive calls to step().
            #[test]
            fn prop_step_monotonicity(
                n_steps in 1usize..32,
                initial_term in "[a-z]{1,8}",
            ) {
                let mut eval = CekEvaluator::new(initial_term);
                let mut obs = NullEvalObserver;
                let mut prev_steps = eval.trace().steps;
                for _ in 0..n_steps {
                    let _ = eval.step(&mut obs);
                    let current_steps = eval.trace().steps;
                    prop_assert!(
                        current_steps >= prev_steps,
                        "step count must be monotonically non-decreasing: {} < {}",
                        current_steps, prev_steps
                    );
                    prev_steps = current_steps;
                }
            }

            /// Terminal stability: once the evaluator reaches a terminal state
            /// (Accepted, Aborted, or Error), subsequent steps remain in that
            /// same terminal state.
            #[test]
            fn prop_terminal_stability(
                initial_term in "[a-z]{1,8}",
                extra_steps in 1usize..16,
            ) {
                let mut eval = CekEvaluator::new(initial_term);
                let mut obs = NullEvalObserver;

                // Run to completion (the simple term hits Accept quickly).
                let _ = eval.run_to_completion(&mut obs);
                prop_assert!(eval.is_terminal(), "evaluator should be terminal after run_to_completion");

                let terminal_state = eval.state().clone();
                // Additional steps must not change the terminal state.
                for _ in 0..extra_steps {
                    let _ = eval.step(&mut obs);
                    prop_assert_eq!(
                        eval.state().clone(), terminal_state.clone(),
                        "terminal state must be stable across additional steps"
                    );
                    prop_assert!(eval.is_terminal(), "must remain terminal");
                }
            }

            /// Memo soundness: inserting a term/result pair into the memo cache
            /// and then looking it up returns exactly the inserted result.
            #[test]
            fn prop_memo_soundness(
                term in "[a-z0-9 +*]{1,16}",
                normal_form in "[a-z0-9]{1,8}",
            ) {
                let mut eval = CekEvaluator::new("dummy".to_string());

                // Cache miss before insertion.
                let miss = eval.memo_lookup(&term);
                prop_assert!(miss.is_none(), "memo lookup should miss before insertion");
                let misses_before = eval.trace().cache_misses;
                prop_assert!(misses_before >= 1, "miss counter should have incremented");

                // Insert.
                eval.memo_insert(term.clone(), normal_form.clone());

                // Cache hit after insertion.
                let hit = eval.memo_lookup(&term);
                prop_assert_eq!(
                    hit.as_deref(), Some(normal_form.as_str()),
                    "memo lookup must return the inserted normal form"
                );
                let hits_after = eval.trace().cache_hits;
                prop_assert!(hits_after >= 1, "hit counter should have incremented");
            }

            /// Bind/unbind symmetry: binding a variable then unbinding it restores
            /// the original environment (the variable is no longer present, and the
            /// unbound value equals the bound value).
            #[test]
            fn prop_bind_unbind_symmetry(
                name in "[a-z]{1,8}",
                value in "[0-9]{1,8}",
            ) {
                let mut eval = CekEvaluator::new("t".to_string());
                let env_size_before = eval.env_size();

                // Bind.
                let prev = eval.bind(name.clone(), value.clone());
                prop_assert!(prev.is_none(), "fresh bind should return None");
                prop_assert_eq!(eval.env_size(), env_size_before + 1);
                prop_assert_eq!(eval.lookup(&name), Some(value.as_str()));

                // Unbind.
                let unbound = eval.unbind(&name);
                prop_assert_eq!(
                    unbound.as_deref(), Some(value.as_str()),
                    "unbind must return the previously bound value"
                );
                prop_assert_eq!(eval.env_size(), env_size_before);
                prop_assert!(eval.lookup(&name).is_none(), "variable must no longer be bound");
            }
        }
    }
}
