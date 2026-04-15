//! CEK Machine Architecture for PraTTaIL's Trampoline Parser.
//!
//! The trampolined parser is structurally isomorphic to a **CEK machine**
//! (Felleisen & Friedman, 1986):
//!
//! | CEK Component | Trampoline Representation |
//! |---------------|--------------------------|
//! | **C** (Control) | Token-driven prefix dispatch + binding power |
//! | **E** (Environment) | Accumulated captures in `Frame_Cat` fields |
//! | **K** (Kontinuation) | `Vec<Frame_Cat>` explicit continuation stack |
//!
//! This module provides the reactive CEK machine infrastructure:
//! - **`CekState`**: Externalized parse state (suspendable, inspectable)
//! - **`CekEvent`**: Events emitted during parsing (for DAP/LSP/REPL)
//! - **`CekTransition`**: State × Event → Transition results
//! - **`CekTraceEntry`**: Debug trace entries for visualization
//! - **`IncrementalSession`**: Checkpoint-based incremental parsing
//!
//! ## Reactive Architecture
//!
//! Follows MeTTaTron's reactive state machine pattern:
//! `State × Event → Transition` as a pure function.
//! External consumers (DAP, LSP, REPL) call `process_event()` at their own pace.
//!
//! ## Consumer Patterns
//!
//! | Consumer | Driving Pattern | What It Reads |
//! |----------|----------------|---------------|
//! | Batch | `run_to_completion()` | Final result |
//! | DAP | `step()` with breakpoint predicates | Stack frames, variables |
//! | LSP | `run_to_checkpoint()` | Checkpoints for incremental reparse |
//! | REPL | `run_to_completion()` + persistent env | Environment state |
//! | Railroad | `step()` + hit count collection | Rule activation map |
//!
//! ## References
//!
//! - Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
//!   and the λ-calculus. *Formal Description of Programming Concepts III*, pp. 193–219.
//! - Reynolds, J. C. (1972). Definitional interpreters for higher-order programming
//!   languages. *Proceedings of the ACM annual conference*, pp. 717–740.

use std::collections::HashMap;
use std::fmt;

use std::collections::BTreeMap;

// ══════════════════════════════════════════════════════════════════════════════
// CEK Machine States
// ══════════════════════════════════════════════════════════════════════════════

/// CEK machine state — the control component of the abstract machine.
///
/// Each variant corresponds to a phase in the trampolined parser's
/// `'drive`/`'unwind` loop:
///
/// ```text
///   Ready ──→ PrefixDispatch ──→ InfixLoop ──→ Unwinding ──→ Accepted
///     │              │               │             │              │
///     │              │               │             └──→ PrefixDispatch
///     │              │               └──→ Unwinding     (push frame)
///     │              └──→ InfixLoop
///     └──→ Error
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum CekState {
    /// Ready to begin parsing (initial state).
    Ready {
        /// Minimum binding power for the parse.
        min_bp: u8,
    },
    /// Prefix dispatch: selecting parse rule based on current token.
    PrefixDispatch {
        /// Current position in token stream.
        pos: usize,
        /// Current binding power.
        cur_bp: u8,
    },
    /// Infix loop: checking for operators after a prefix value is produced.
    InfixLoop {
        /// Current binding power.
        cur_bp: u8,
    },
    /// Unwinding: applying continuation from the stack.
    Unwinding,
    /// Parse completed successfully.
    Accepted,
    /// Parse error.
    Error {
        /// Error message.
        message: String,
    },
}

impl fmt::Display for CekState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ready { min_bp } => write!(f, "Ready(min_bp={})", min_bp),
            Self::PrefixDispatch { pos, cur_bp } => {
                write!(f, "PrefixDispatch(pos={}, cur_bp={})", pos, cur_bp)
            },
            Self::InfixLoop { cur_bp } => write!(f, "InfixLoop(cur_bp={})", cur_bp),
            Self::Unwinding => write!(f, "Unwinding"),
            Self::Accepted => write!(f, "Accepted"),
            Self::Error { message } => write!(f, "Error({})", message),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Machine Events
// ══════════════════════════════════════════════════════════════════════════════

/// Events emitted during CEK machine execution.
///
/// Each event corresponds to an observable transition in the parser.
/// Consumers (DAP, LSP, railroad annotator) subscribe to events
/// to drive their own logic.
#[derive(Debug, Clone, PartialEq)]
pub enum CekEvent {
    /// Advance one step (general-purpose driver).
    Step,
    /// A value was produced by prefix dispatch.
    ValueProduced {
        /// Display representation of the value.
        display: String,
    },
    /// A frame was pushed onto the continuation stack.
    FramePushed {
        /// Frame variant name (e.g., "InfixRHS", "RD_Let_0").
        variant: String,
    },
    /// A frame was popped from the continuation stack.
    FramePopped {
        /// Frame variant name.
        variant: String,
    },
    /// An operator was consumed in the infix loop.
    OperatorConsumed {
        /// Operator token position.
        op_pos: usize,
    },
    /// External: inspect current state (no state change).
    Inspect,
}

impl fmt::Display for CekEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Step => write!(f, "Step"),
            Self::ValueProduced { display } => write!(f, "ValueProduced({})", display),
            Self::FramePushed { variant } => write!(f, "FramePushed({})", variant),
            Self::FramePopped { variant } => write!(f, "FramePopped({})", variant),
            Self::OperatorConsumed { op_pos } => write!(f, "OperatorConsumed(pos={})", op_pos),
            Self::Inspect => write!(f, "Inspect"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Machine Transitions
// ══════════════════════════════════════════════════════════════════════════════

/// Result of processing a CEK event — the transition output.
#[derive(Debug, Clone)]
pub enum CekTransition {
    /// No state change (e.g., Inspect event).
    NoChange,
    /// Transition to a new state with an optional trace entry.
    Transition {
        /// The new machine state.
        new_state: CekState,
        /// Trace entry for debugger/DAP/railroad annotation.
        trace: Option<CekTraceEntry>,
    },
    /// Checkpoint at a natural boundary (for LSP incremental reparse).
    Checkpoint {
        /// Position in the token stream at the checkpoint.
        pos: usize,
        /// Stack depth at the checkpoint.
        stack_depth: usize,
        /// Current binding power at the checkpoint.
        cur_bp: u8,
    },
}

// ══════════════════════════════════════════════════════════════════════════════
// Trace Entries
// ══════════════════════════════════════════════════════════════════════════════

/// A trace entry recording a single CEK transition for debugging,
/// DAP step visualization, and railroad diagram annotation.
#[derive(Debug, Clone)]
pub struct CekTraceEntry {
    /// Grammar category being parsed.
    pub category: String,
    /// Position in token stream.
    pub pos: usize,
    /// Stack depth at time of entry.
    pub stack_depth: usize,
    /// Kind of trace entry.
    pub kind: TraceKind,
}

/// Classification of trace entries.
#[derive(Debug, Clone)]
pub enum TraceKind {
    /// Entering the drive loop (prefix dispatch).
    Drive {
        /// Token at current position (display form).
        token: Option<String>,
        /// Current binding power.
        cur_bp: u8,
    },
    /// Pushing a continuation frame.
    Push {
        /// Frame variant name.
        frame_variant: String,
        /// Captured values (name → display) stored in the frame.
        captures: Vec<(String, String)>,
    },
    /// Popping a continuation frame.
    Pop {
        /// Frame variant name.
        frame_variant: String,
        /// Action taken (e.g., "construct Add", "restore bp").
        action: String,
    },
    /// A value was produced.
    Value {
        /// Display representation.
        display: String,
    },
    /// An error occurred.
    Error {
        /// Error message.
        message: String,
    },
}

impl fmt::Display for CekTraceEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}@{} d={}] ", self.category, self.pos, self.stack_depth)?;
        match &self.kind {
            TraceKind::Drive { token, cur_bp } => {
                write!(f, "DRIVE bp={}", cur_bp)?;
                if let Some(tok) = token {
                    write!(f, " tok={}", tok)?;
                }
            },
            TraceKind::Push { frame_variant, captures } => {
                write!(f, "PUSH {}", frame_variant)?;
                if !captures.is_empty() {
                    write!(f, " [")?;
                    for (i, (name, val)) in captures.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}={}", name, val)?;
                    }
                    write!(f, "]")?;
                }
            },
            TraceKind::Pop { frame_variant, action } => {
                write!(f, "POP {} → {}", frame_variant, action)?;
            },
            TraceKind::Value { display } => {
                write!(f, "VALUE {}", display)?;
            },
            TraceKind::Error { message } => {
                write!(f, "ERROR {}", message)?;
            },
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Trace Collector
// ══════════════════════════════════════════════════════════════════════════════

/// Collects trace entries during CEK machine execution.
///
/// Used by railroad diagram annotation and DAP debugging.
/// Maintains per-rule hit counts for frequency visualization.
#[derive(Debug, Clone, Default)]
pub struct TraceCollector {
    /// All trace entries in order.
    pub entries: Vec<CekTraceEntry>,
    /// Per-rule hit counts: `rule_label → count`.
    pub rule_hits: HashMap<String, usize>,
    /// Maximum stack depth reached during the parse.
    pub max_stack_depth: usize,
    /// Total number of drive transitions.
    pub drive_count: usize,
    /// Total number of unwind transitions.
    pub unwind_count: usize,
}

impl TraceCollector {
    /// Create a new empty trace collector.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a trace entry.
    pub fn record(&mut self, entry: CekTraceEntry) {
        if entry.stack_depth > self.max_stack_depth {
            self.max_stack_depth = entry.stack_depth;
        }
        match &entry.kind {
            TraceKind::Drive { .. } => self.drive_count += 1,
            TraceKind::Pop { .. } => self.unwind_count += 1,
            TraceKind::Push { frame_variant, .. } => {
                *self.rule_hits.entry(frame_variant.clone()).or_insert(0) += 1;
            },
            _ => {},
        }
        self.entries.push(entry);
    }

    /// Get the hit count for a rule.
    pub fn hit_count(&self, rule_label: &str) -> usize {
        self.rule_hits.get(rule_label).copied().unwrap_or(0)
    }

    /// Total number of trace entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the trace is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Environment
// ══════════════════════════════════════════════════════════════════════════════

/// Unified environment component of the CEK machine.
///
/// Subsumes the distributed environment infrastructure:
/// - Per-category variable→value bindings (completing env infrastructure)
/// - Guard evaluation context
///
/// The environment persists across REPL submissions, enabling
/// `x = 5; x + 3` to evaluate to 8.
#[derive(Debug, Clone, Default)]
pub struct CekEnvironment {
    /// Per-category variable→value bindings.
    /// Key: category name (e.g., "Int", "Proc").
    /// Value: map from variable name to serialized value.
    ///
    /// At the codegen level, each category gets a typed env struct.
    /// This is the type-erased version for the framework.
    category_envs: HashMap<String, HashMap<String, String>>,
    /// Guard evaluation context: name → value bindings visible to guards.
    guard_bindings: HashMap<String, String>,
}

impl CekEnvironment {
    /// Create a new empty environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a variable binding in a category's environment.
    pub fn set(&mut self, category: &str, name: &str, value: String) {
        self.category_envs
            .entry(category.to_string())
            .or_default()
            .insert(name.to_string(), value);
    }

    /// Get a variable binding from a category's environment.
    pub fn get(&self, category: &str, name: &str) -> Option<&String> {
        self.category_envs.get(category)?.get(name)
    }

    /// Remove a variable binding from a category's environment.
    pub fn remove(&mut self, category: &str, name: &str) -> Option<String> {
        self.category_envs.get_mut(category)?.remove(name)
    }

    /// Set a guard binding.
    pub fn set_guard(&mut self, name: &str, value: String) {
        self.guard_bindings.insert(name.to_string(), value);
    }

    /// Get a guard binding.
    pub fn get_guard(&self, name: &str) -> Option<&String> {
        self.guard_bindings.get(name)
    }

    /// Clear all guard bindings (called after guard evaluation).
    pub fn clear_guards(&mut self) {
        self.guard_bindings.clear();
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.category_envs.is_empty() && self.guard_bindings.is_empty()
    }

    /// Get all variable names bound in a category.
    pub fn category_vars(&self, category: &str) -> Vec<&String> {
        self.category_envs
            .get(category)
            .map(|env| env.keys().collect())
            .unwrap_or_default()
    }

    /// Get all categories that have bindings.
    pub fn bound_categories(&self) -> Vec<&String> {
        self.category_envs.keys().collect()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Parse State (externalized CEK state)
// ══════════════════════════════════════════════════════════════════════════════

/// Externalized CEK machine state — suspendable, serializable, inspectable.
///
/// This is the complete parse state at any point during execution.
/// Used for checkpointing (LSP incremental reparse), debugging (DAP),
/// and REPL environment persistence.
///
/// ## DAP Mapping
///
/// | DAP Concept | ParseState Field |
/// |-------------|-----------------|
/// | Stack frames | `stack_tags` (frame variant names) |
/// | Variables | captures in each frame + `cur_bp` |
/// | Position | `pos` |
/// | Running weight | `running_weight` |
#[derive(Debug, Clone)]
pub struct ParseState {
    /// K: Continuation stack — frame variant tags.
    ///
    /// We store only the variant tags (strings) here since the actual
    /// frame data is category-specific and lives in the generated code.
    /// This provides enough information for stack inspection and
    /// convergence detection.
    pub stack_tags: Vec<String>,
    /// C: Current binding power.
    pub cur_bp: u8,
    /// Current position in the token stream.
    pub pos: usize,
    /// Accumulated confidence weight (tropical).
    pub running_weight: f64,
    /// E: Unified environment.
    pub environment: CekEnvironment,
    /// Machine state.
    pub state: CekState,
}

impl ParseState {
    /// Create a new parse state at the beginning of a parse.
    pub fn new(min_bp: u8) -> Self {
        Self {
            stack_tags: Vec::new(),
            cur_bp: min_bp,
            pos: 0,
            running_weight: 0.0,
            environment: CekEnvironment::new(),
            state: CekState::Ready { min_bp },
        }
    }

    /// Stack depth.
    pub fn stack_depth(&self) -> usize {
        self.stack_tags.len()
    }

    /// Whether the parse has completed.
    pub fn is_terminal(&self) -> bool {
        matches!(self.state, CekState::Accepted | CekState::Error { .. })
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Convergence Detection
// ══════════════════════════════════════════════════════════════════════════════

/// Two ParseStates are convergent if their continuation stacks and
/// binding powers match — the parse will proceed identically from here.
///
/// Used by `IncrementalSession::reparse()` to detect when re-parsing
/// after an edit has "caught up" with the surviving checkpoints.
pub fn is_convergent(a: &ParseState, b: &ParseState) -> bool {
    a.stack_tags.len() == b.stack_tags.len()
        && a.cur_bp == b.cur_bp
        && a.stack_tags
            .iter()
            .zip(b.stack_tags.iter())
            .all(|(ta, tb)| ta == tb)
}

// ══════════════════════════════════════════════════════════════════════════════
// Incremental Session
// ══════════════════════════════════════════════════════════════════════════════

/// Incremental parse session — manages checkpoint cache for a single source buffer.
///
/// Provides the infrastructure for LSP-style incremental reparsing:
///
/// 1. **Initial parse**: `parse_full()` creates checkpoints at natural boundaries
/// 2. **Edit**: User modifies the buffer
/// 3. **Reparse**: `reparse()` resumes from the nearest checkpoint before the edit
/// 4. **Converge**: When the parse state matches a surviving checkpoint, stop
///
/// ## Checkpoint Placement
///
/// Default: every token (`checkpoint_interval = 1`) for sub-microsecond edits.
/// Natural boundaries (rule completion, category entry) are marked for consumers
/// wanting coarser checkpoints.
///
/// ## Memory
///
/// ~200-400 KB per file with token-level checkpoints and CoW stacks.
#[derive(Debug, Clone)]
pub struct IncrementalSession {
    /// Checkpoints indexed by token position, sorted.
    checkpoints: std::collections::BTreeMap<usize, ParseState>,
    /// Checkpoint interval: create a checkpoint every N steps.
    /// Default: 1 (every token).
    pub checkpoint_interval: usize,
    /// Last fully-parsed token position.
    pub parsed_to: usize,
}

impl IncrementalSession {
    /// Create a new incremental session.
    ///
    /// # Arguments
    /// - `min_bp`: Minimum binding power for the top-level parse.
    /// - `checkpoint_interval`: Create a checkpoint every N steps.
    ///   Use 1 for token-level (fast edits, ~400KB/file).
    ///   Use 50 for coarse (slower edits, ~10KB/file).
    pub fn new(min_bp: u8, checkpoint_interval: usize) -> Self {
        let mut checkpoints = std::collections::BTreeMap::new();
        checkpoints.insert(0, ParseState::new(min_bp));
        Self {
            checkpoints,
            checkpoint_interval: checkpoint_interval.max(1),
            parsed_to: 0,
        }
    }

    /// Record a checkpoint at the given position.
    pub fn record_checkpoint(&mut self, pos: usize, state: ParseState) {
        self.checkpoints.insert(pos, state);
        if pos > self.parsed_to {
            self.parsed_to = pos;
        }
    }

    /// Find the latest checkpoint at or before the given position.
    pub fn checkpoint_at_or_before(&self, pos: usize) -> Option<(usize, &ParseState)> {
        self.checkpoints
            .range(..=pos)
            .next_back()
            .map(|(k, v)| (*k, v))
    }

    /// Invalidate all checkpoints after the given position.
    ///
    /// Called when an edit occurs: everything after the edit position
    /// may be stale.
    pub fn invalidate_after(&mut self, pos: usize) {
        // Collect keys to remove (can't mutate while iterating)
        let to_remove: Vec<usize> = self.checkpoints.range((pos + 1)..).map(|(k, _)| *k).collect();
        for key in to_remove {
            self.checkpoints.remove(&key);
        }
        if self.parsed_to > pos {
            self.parsed_to = pos;
        }
    }

    /// Number of stored checkpoints.
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    /// Clear all checkpoints and reset.
    pub fn clear(&mut self, min_bp: u8) {
        self.checkpoints.clear();
        self.checkpoints.insert(0, ParseState::new(min_bp));
        self.parsed_to = 0;
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Formal CEK Transition Rules
// ══════════════════════════════════════════════════════════════════════════════

/// The 10 core CEK transition rules (for documentation and proof reference).
///
/// These rules define the small-step operational semantics of the parser.
/// The generated trampoline code implements exactly these transitions.
///
/// | Rule | From | To | Stack Op |
/// |------|------|----|----------|
/// | DRIVE | `Drive(cat, bp)` | `Prefix(cat, tok, bp)` | — |
/// | PREFIX-TERMINAL (NT) | `Prefix(cat, tok, bp)` | `Drive(cat, bp')` | push Frame |
/// | PREFIX-TERMINAL (leaf) | `Prefix(cat, tok, bp)` | `Infix(cat, v, bp)` | — |
/// | PREFIX-TAIL (BP02) | `Prefix(cat, tok, bp)` | `Drive(cat, R.bp)` | set tail_wrap |
/// | INFIX | `Infix(cat, lhs, bp)` | `Drive(cat, r_bp)` | push InfixRHS |
/// | POSTFIX | `Infix(cat, lhs, bp)` | `Infix(cat, f(lhs), bp)` | — |
/// | UNWIND-INFIX | `Unwind(cat, rhs)` | `Infix(cat, f(lhs,rhs), bp)` | pop InfixRHS |
/// | UNWIND-PREFIX | `Unwind(cat, v)` | `Infix(cat, wrap(v), bp)` | pop UnaryPrefix |
/// | UNWIND-RD | `Unwind(cat, nt)` | `Drive/Infix` | pop RD |
/// | UNWIND-EMPTY | `Unwind(cat, v)` | `Accept(v)` | stack empty |
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TransitionRule {
    /// DRIVE: Enter prefix dispatch.
    Drive,
    /// PREFIX-TERMINAL with nonterminal: push frame, recurse.
    PrefixTerminalNt,
    /// PREFIX-TERMINAL leaf: produce value, enter infix loop.
    PrefixTerminalLeaf,
    /// PREFIX-TAIL: BP02 tail-call optimization.
    PrefixTail,
    /// INFIX: consume operator, push InfixRHS, recurse for RHS.
    Infix,
    /// POSTFIX: apply postfix operator without recursion.
    Postfix,
    /// UNWIND-INFIX: pop InfixRHS, construct binary node.
    UnwindInfix,
    /// UNWIND-PREFIX: pop UnaryPrefix, apply wrapper.
    UnwindPrefix,
    /// UNWIND-RD: pop RD segment, continue or construct.
    UnwindRd,
    /// UNWIND-EMPTY: stack empty, accept result.
    UnwindEmpty,
}

impl fmt::Display for TransitionRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Drive => write!(f, "DRIVE"),
            Self::PrefixTerminalNt => write!(f, "PREFIX-TERMINAL(NT)"),
            Self::PrefixTerminalLeaf => write!(f, "PREFIX-TERMINAL(leaf)"),
            Self::PrefixTail => write!(f, "PREFIX-TAIL(BP02)"),
            Self::Infix => write!(f, "INFIX"),
            Self::Postfix => write!(f, "POSTFIX"),
            Self::UnwindInfix => write!(f, "UNWIND-INFIX"),
            Self::UnwindPrefix => write!(f, "UNWIND-PREFIX"),
            Self::UnwindRd => write!(f, "UNWIND-RD"),
            Self::UnwindEmpty => write!(f, "UNWIND-EMPTY"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Runtime Tracing (CEK Observer Pattern) — feature = "cek-runtime"
// ══════════════════════════════════════════════════════════════════════════════

/// Observer control response — returned by [`CekObserver::on_event`] to direct
/// the parser's next step.
///
/// - `Continue`: proceed to the next transition (default / fast path).
/// - `Checkpoint`: record the current [`PdaConfiguration`] and continue.
/// - `Abort`: halt the parse immediately, returning partial results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CekControl {
    /// Proceed with the next transition.
    Continue,
    /// Record a checkpoint at the current configuration, then continue.
    Checkpoint,
    /// Abort the parse, returning partial results.
    Abort,
}

impl Default for CekControl {
    fn default() -> Self {
        Self::Continue
    }
}

/// A single CEK step event emitted at each of the 5 transition points
/// (DRIVE, PUSH, POP, INFIX, ACCEPT).
///
/// The observer receives this by reference, avoiding allocation on the hot path.
/// All string fields are borrowed from the generated parser's static data.
#[derive(Debug, Clone)]
pub struct CekStepEvent<'a> {
    /// Which transition rule fired.
    pub rule: TransitionRule,
    /// Current position in the token stream.
    pub pos: usize,
    /// Current binding power.
    pub cur_bp: u8,
    /// Continuation stack depth.
    pub stack_depth: usize,
    /// Name of the top-of-stack frame variant (e.g., "InfixRHS", "RD_Let_0").
    /// `None` when the stack is empty.
    pub frame_variant: Option<&'a str>,
    /// Accumulated tropical weight at this point.
    pub running_weight: f64,
    /// Grammar category being parsed (e.g., "Expr", "Proc").
    pub category: &'a str,
}

/// Callback observer trait for runtime parse tracing.
///
/// Implement this to receive notifications at each CEK transition:
///
/// | Point | `event.rule` | When |
/// |-------|-------------|------|
/// | DRIVE | `Drive` | Entering prefix dispatch |
/// | PUSH | `PrefixTerminalNt` | Pushing a continuation frame |
/// | POP | `UnwindInfix` / `UnwindPrefix` / `UnwindRd` | Popping a frame |
/// | INFIX | `Infix` / `Postfix` | Consuming an operator |
/// | ACCEPT | `UnwindEmpty` | Parse completed |
///
/// The generated `parse_Cat_traced` functions call `on_event()` at each
/// transition. Return [`CekControl::Continue`] for zero-cost passthrough.
///
/// When `on_event()` returns [`CekControl::Checkpoint`], the parser calls
/// `on_checkpoint()` with the current PDA configuration.
pub trait CekObserver {
    /// Called at each CEK transition point.
    ///
    /// Return `CekControl::Continue` for no-op, `Checkpoint` to record
    /// the current configuration, or `Abort` to halt immediately.
    fn on_event(&mut self, event: &CekStepEvent<'_>) -> CekControl;

    /// Called when `on_event` returns `CekControl::Checkpoint`.
    ///
    /// The `config` captures the full PDA configuration (stack tags, bp, pos)
    /// for later incremental reparse or time-travel debugging.
    fn on_checkpoint(&mut self, config: &PdaConfiguration);

    /// Called when the parse completes (either accept or error).
    /// Provides the final trace summary.
    fn on_complete(&mut self, _trace: &PdaTrace) {}
}

/// A snapshot of the PDA configuration at a specific point during parsing.
///
/// Captures enough state to resume parsing from this point (incremental reparse)
/// or to reconstruct the parse tree up to this point (time-travel debugging).
#[derive(Debug, Clone)]
pub struct PdaConfiguration {
    /// Current position in the token stream.
    pub pos: usize,
    /// Current binding power.
    pub cur_bp: u8,
    /// Stack frame variant tags (bottom-to-top).
    pub stack_tags: Vec<String>,
    /// The phase/state the parser is in.
    pub phase: CekState,
}

impl PdaConfiguration {
    /// Create a configuration snapshot from the current parse state.
    pub fn from_parse_state(state: &ParseState) -> Self {
        Self {
            pos: state.pos,
            cur_bp: state.cur_bp,
            stack_tags: state.stack_tags.clone(),
            phase: state.state.clone(),
        }
    }
}

/// Accumulated trace statistics from a complete traced parse.
///
/// Provides aggregate data for profiling and visualization without
/// storing the full trace (which can be done via [`TraceCollector`]).
#[derive(Debug, Clone, Default)]
pub struct PdaTrace {
    /// Total number of steps (all transition types).
    pub steps: usize,
    /// Number of PUSH transitions (frame pushes).
    pub push_counts: BTreeMap<String, usize>,
    /// Number of POP transitions (frame pops).
    pub pop_counts: BTreeMap<String, usize>,
    /// Per-rule activation counts.
    pub rule_counts: BTreeMap<TransitionRule, usize>,
    /// Maximum stack depth reached.
    pub max_depth: usize,
}

impl PdaTrace {
    /// Create an empty trace.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a step event into this trace.
    pub fn record_step(&mut self, event: &CekStepEvent<'_>) {
        self.steps += 1;
        *self.rule_counts.entry(event.rule).or_insert(0) += 1;
        if event.stack_depth > self.max_depth {
            self.max_depth = event.stack_depth;
        }
        match event.rule {
            TransitionRule::PrefixTerminalNt => {
                if let Some(variant) = event.frame_variant {
                    *self.push_counts.entry(variant.to_string()).or_insert(0) += 1;
                }
            },
            TransitionRule::UnwindInfix
            | TransitionRule::UnwindPrefix
            | TransitionRule::UnwindRd => {
                if let Some(variant) = event.frame_variant {
                    *self.pop_counts.entry(variant.to_string()).or_insert(0) += 1;
                }
            },
            _ => {},
        }
    }

    /// Total number of push transitions.
    pub fn total_pushes(&self) -> usize {
        self.push_counts.values().sum()
    }

    /// Total number of pop transitions.
    pub fn total_pops(&self) -> usize {
        self.pop_counts.values().sum()
    }
}

/// A simple observer that collects trace statistics into a [`PdaTrace`].
///
/// Usage:
/// ```ignore
/// let mut observer = TracingObserver::new();
/// let result = parse_Expr_traced(&tokens, 0, 0, &mut observer);
/// println!("Steps: {}, Max depth: {}", observer.trace.steps, observer.trace.max_depth);
/// ```
#[derive(Debug, Clone, Default)]
pub struct TracingObserver {
    /// Accumulated trace statistics.
    pub trace: PdaTrace,
    /// Optional checkpoint recording.
    pub checkpoints: Vec<PdaConfiguration>,
    /// Whether to record checkpoints on every N steps (0 = never).
    pub checkpoint_interval: usize,
}

impl TracingObserver {
    /// Create a new tracing observer (no checkpoint recording).
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a tracing observer that records checkpoints every N steps.
    pub fn with_checkpoint_interval(interval: usize) -> Self {
        Self {
            checkpoint_interval: interval,
            ..Self::default()
        }
    }
}

impl CekObserver for TracingObserver {
    fn on_event(&mut self, event: &CekStepEvent<'_>) -> CekControl {
        self.trace.record_step(event);
        if self.checkpoint_interval > 0 && self.trace.steps % self.checkpoint_interval == 0 {
            CekControl::Checkpoint
        } else {
            CekControl::Continue
        }
    }

    fn on_checkpoint(&mut self, config: &PdaConfiguration) {
        self.checkpoints.push(config.clone());
    }

    fn on_complete(&mut self, _trace: &PdaTrace) {
        // TracingObserver already has the trace from record_step calls
    }
}

/// A no-op observer that discards all events.
///
/// Zero overhead: the compiler can inline and eliminate the calls.
#[derive(Debug, Clone, Copy, Default)]
pub struct NullObserver;

impl CekObserver for NullObserver {
    #[inline(always)]
    fn on_event(&mut self, _event: &CekStepEvent<'_>) -> CekControl {
        CekControl::Continue
    }

    #[inline(always)]
    fn on_checkpoint(&mut self, _config: &PdaConfiguration) {}
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cek_state_display() {
        assert_eq!(
            CekState::Ready { min_bp: 0 }.to_string(),
            "Ready(min_bp=0)"
        );
        assert_eq!(
            CekState::PrefixDispatch { pos: 5, cur_bp: 3 }.to_string(),
            "PrefixDispatch(pos=5, cur_bp=3)"
        );
        assert_eq!(CekState::Accepted.to_string(), "Accepted");
    }

    #[test]
    fn test_cek_event_display() {
        assert_eq!(CekEvent::Step.to_string(), "Step");
        assert_eq!(
            CekEvent::FramePushed { variant: "InfixRHS".to_string() }.to_string(),
            "FramePushed(InfixRHS)"
        );
    }

    #[test]
    fn test_parse_state_new() {
        let state = ParseState::new(0);
        assert_eq!(state.cur_bp, 0);
        assert_eq!(state.pos, 0);
        assert_eq!(state.stack_depth(), 0);
        assert!(!state.is_terminal());
    }

    #[test]
    fn test_parse_state_terminal() {
        let mut state = ParseState::new(0);
        state.state = CekState::Accepted;
        assert!(state.is_terminal());

        state.state = CekState::Error { message: "test".to_string() };
        assert!(state.is_terminal());
    }

    #[test]
    fn test_convergence_identical() {
        let a = ParseState::new(0);
        let b = ParseState::new(0);
        assert!(is_convergent(&a, &b));
    }

    #[test]
    fn test_convergence_different_bp() {
        let a = ParseState::new(0);
        let mut b = ParseState::new(0);
        b.cur_bp = 5;
        assert!(!is_convergent(&a, &b));
    }

    #[test]
    fn test_convergence_different_stacks() {
        let mut a = ParseState::new(0);
        let b = ParseState::new(0);
        a.stack_tags.push("InfixRHS".to_string());
        assert!(!is_convergent(&a, &b));
    }

    #[test]
    fn test_convergence_same_stacks() {
        let mut a = ParseState::new(0);
        let mut b = ParseState::new(0);
        a.stack_tags.push("InfixRHS".to_string());
        a.stack_tags.push("RD_Let_0".to_string());
        b.stack_tags.push("InfixRHS".to_string());
        b.stack_tags.push("RD_Let_0".to_string());
        assert!(is_convergent(&a, &b));
    }

    #[test]
    fn test_environment_basic() {
        let mut env = CekEnvironment::new();
        assert!(env.is_empty());

        env.set("Int", "x", "5".to_string());
        assert_eq!(env.get("Int", "x"), Some(&"5".to_string()));
        assert_eq!(env.get("Int", "y"), None);
        assert_eq!(env.get("Proc", "x"), None);
        assert!(!env.is_empty());
    }

    #[test]
    fn test_environment_remove() {
        let mut env = CekEnvironment::new();
        env.set("Int", "x", "5".to_string());
        assert_eq!(env.remove("Int", "x"), Some("5".to_string()));
        assert_eq!(env.get("Int", "x"), None);
    }

    #[test]
    fn test_environment_guard_bindings() {
        let mut env = CekEnvironment::new();
        env.set_guard("cond", "true".to_string());
        assert_eq!(env.get_guard("cond"), Some(&"true".to_string()));

        env.clear_guards();
        assert_eq!(env.get_guard("cond"), None);
    }

    #[test]
    fn test_environment_category_vars() {
        let mut env = CekEnvironment::new();
        env.set("Int", "x", "5".to_string());
        env.set("Int", "y", "10".to_string());
        env.set("Proc", "p", "PZero".to_string());

        let int_vars = env.category_vars("Int");
        assert_eq!(int_vars.len(), 2);

        let proc_vars = env.category_vars("Proc");
        assert_eq!(proc_vars.len(), 1);

        let cats = env.bound_categories();
        assert_eq!(cats.len(), 2);
    }

    #[test]
    fn test_trace_collector() {
        let mut collector = TraceCollector::new();
        assert!(collector.is_empty());

        collector.record(CekTraceEntry {
            category: "Expr".to_string(),
            pos: 0,
            stack_depth: 0,
            kind: TraceKind::Drive { token: Some("+".to_string()), cur_bp: 0 },
        });
        collector.record(CekTraceEntry {
            category: "Expr".to_string(),
            pos: 1,
            stack_depth: 1,
            kind: TraceKind::Push {
                frame_variant: "InfixRHS".to_string(),
                captures: vec![("lhs".to_string(), "1".to_string())],
            },
        });
        collector.record(CekTraceEntry {
            category: "Expr".to_string(),
            pos: 2,
            stack_depth: 0,
            kind: TraceKind::Pop {
                frame_variant: "InfixRHS".to_string(),
                action: "construct Add".to_string(),
            },
        });

        assert_eq!(collector.len(), 3);
        assert_eq!(collector.drive_count, 1);
        assert_eq!(collector.unwind_count, 1);
        assert_eq!(collector.max_stack_depth, 1);
        assert_eq!(collector.hit_count("InfixRHS"), 1);
        assert_eq!(collector.hit_count("GroupClose"), 0);
    }

    #[test]
    fn test_trace_entry_display() {
        let entry = CekTraceEntry {
            category: "Int".to_string(),
            pos: 3,
            stack_depth: 2,
            kind: TraceKind::Push {
                frame_variant: "RD_Let_0".to_string(),
                captures: vec![("x".to_string(), "\"foo\"".to_string())],
            },
        };
        let s = entry.to_string();
        assert!(s.contains("Int@3"));
        assert!(s.contains("d=2"));
        assert!(s.contains("PUSH RD_Let_0"));
        assert!(s.contains("x=\"foo\""));
    }

    #[test]
    fn test_incremental_session_new() {
        let session = IncrementalSession::new(0, 1);
        assert_eq!(session.checkpoint_count(), 1); // Initial checkpoint at pos 0
        assert_eq!(session.parsed_to, 0);
    }

    #[test]
    fn test_incremental_session_record_and_lookup() {
        let mut session = IncrementalSession::new(0, 1);

        let state1 = ParseState::new(0);
        session.record_checkpoint(5, state1);

        let mut state2 = ParseState::new(0);
        state2.cur_bp = 3;
        session.record_checkpoint(10, state2);

        assert_eq!(session.checkpoint_count(), 3); // 0, 5, 10

        // Lookup: closest at or before pos 7
        let (pos, _state) = session.checkpoint_at_or_before(7).expect("should find checkpoint");
        assert_eq!(pos, 5);

        // Lookup: exact match
        let (pos, _state) = session.checkpoint_at_or_before(10).expect("should find checkpoint");
        assert_eq!(pos, 10);
    }

    #[test]
    fn test_incremental_session_invalidate() {
        let mut session = IncrementalSession::new(0, 1);
        session.record_checkpoint(5, ParseState::new(0));
        session.record_checkpoint(10, ParseState::new(0));
        session.record_checkpoint(15, ParseState::new(0));

        assert_eq!(session.checkpoint_count(), 4); // 0, 5, 10, 15

        session.invalidate_after(7);
        assert_eq!(session.checkpoint_count(), 2); // 0, 5
        assert_eq!(session.parsed_to, 7);
    }

    #[test]
    fn test_incremental_session_clear() {
        let mut session = IncrementalSession::new(0, 1);
        session.record_checkpoint(5, ParseState::new(0));
        session.record_checkpoint(10, ParseState::new(0));

        session.clear(0);
        assert_eq!(session.checkpoint_count(), 1);
        assert_eq!(session.parsed_to, 0);
    }

    #[test]
    fn test_transition_rule_display() {
        assert_eq!(TransitionRule::Drive.to_string(), "DRIVE");
        assert_eq!(TransitionRule::UnwindEmpty.to_string(), "UNWIND-EMPTY");
        assert_eq!(TransitionRule::PrefixTail.to_string(), "PREFIX-TAIL(BP02)");
    }

    // ── cek-runtime tests ───────────────────────────────────────────────────

    mod cek_runtime_tests {
        use super::*;

        #[test]
        fn test_cek_control_default() {
            assert_eq!(CekControl::default(), CekControl::Continue);
        }

        #[test]
        fn test_cek_step_event_construction() {
            let event = CekStepEvent {
                rule: TransitionRule::Drive,
                pos: 0,
                cur_bp: 0,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Expr",
            };
            assert_eq!(event.rule, TransitionRule::Drive);
            assert_eq!(event.category, "Expr");
            assert!(event.frame_variant.is_none());
        }

        #[test]
        fn test_pda_trace_record_step() {
            let mut trace = PdaTrace::new();
            assert_eq!(trace.steps, 0);
            assert_eq!(trace.max_depth, 0);

            // Record a DRIVE step
            trace.record_step(&CekStepEvent {
                rule: TransitionRule::Drive,
                pos: 0,
                cur_bp: 0,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Expr",
            });
            assert_eq!(trace.steps, 1);
            assert_eq!(trace.rule_counts[&TransitionRule::Drive], 1);

            // Record a PUSH step
            trace.record_step(&CekStepEvent {
                rule: TransitionRule::PrefixTerminalNt,
                pos: 1,
                cur_bp: 3,
                stack_depth: 1,
                frame_variant: Some("InfixRHS"),
                running_weight: 0.0,
                category: "Expr",
            });
            assert_eq!(trace.steps, 2);
            assert_eq!(trace.max_depth, 1);
            assert_eq!(trace.total_pushes(), 1);
            assert_eq!(trace.push_counts["InfixRHS"], 1);

            // Record a POP step
            trace.record_step(&CekStepEvent {
                rule: TransitionRule::UnwindInfix,
                pos: 2,
                cur_bp: 3,
                stack_depth: 0,
                frame_variant: Some("InfixRHS"),
                running_weight: 0.0,
                category: "Expr",
            });
            assert_eq!(trace.steps, 3);
            assert_eq!(trace.total_pops(), 1);
            assert_eq!(trace.pop_counts["InfixRHS"], 1);
        }

        #[test]
        fn test_pda_configuration_from_parse_state() {
            let mut state = ParseState::new(0);
            state.pos = 5;
            state.cur_bp = 3;
            state.stack_tags.push("InfixRHS".to_string());
            state.state = CekState::InfixLoop { cur_bp: 3 };

            let config = PdaConfiguration::from_parse_state(&state);
            assert_eq!(config.pos, 5);
            assert_eq!(config.cur_bp, 3);
            assert_eq!(config.stack_tags, vec!["InfixRHS".to_string()]);
            assert_eq!(config.phase, CekState::InfixLoop { cur_bp: 3 });
        }

        #[test]
        fn test_tracing_observer_basic() {
            let mut observer = TracingObserver::new();
            assert_eq!(observer.trace.steps, 0);
            assert!(observer.checkpoints.is_empty());

            let event = CekStepEvent {
                rule: TransitionRule::Drive,
                pos: 0,
                cur_bp: 0,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Expr",
            };
            let control = observer.on_event(&event);
            assert_eq!(control, CekControl::Continue);
            assert_eq!(observer.trace.steps, 1);
        }

        #[test]
        fn test_tracing_observer_checkpoint_interval() {
            let mut observer = TracingObserver::with_checkpoint_interval(2);
            let event = CekStepEvent {
                rule: TransitionRule::Drive,
                pos: 0,
                cur_bp: 0,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Expr",
            };

            // Step 1: no checkpoint
            let c1 = observer.on_event(&event);
            assert_eq!(c1, CekControl::Continue);

            // Step 2: checkpoint
            let c2 = observer.on_event(&event);
            assert_eq!(c2, CekControl::Checkpoint);

            // Simulate the parser calling on_checkpoint
            let config = PdaConfiguration {
                pos: 0,
                cur_bp: 0,
                stack_tags: vec![],
                phase: CekState::Ready { min_bp: 0 },
            };
            observer.on_checkpoint(&config);
            assert_eq!(observer.checkpoints.len(), 1);
        }

        #[test]
        fn test_null_observer() {
            let mut observer = NullObserver;
            let event = CekStepEvent {
                rule: TransitionRule::Drive,
                pos: 0,
                cur_bp: 0,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Expr",
            };
            assert_eq!(observer.on_event(&event), CekControl::Continue);
            observer.on_checkpoint(&PdaConfiguration {
                pos: 0,
                cur_bp: 0,
                stack_tags: vec![],
                phase: CekState::Ready { min_bp: 0 },
            });
            // NullObserver should do nothing
        }
    }
}
