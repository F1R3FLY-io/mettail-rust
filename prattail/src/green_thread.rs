//! Green Thread Core (Sprint GT-2): Suspendable CEK machines with persistent data structures.
//!
//! A green thread is a suspendable CEK machine with an **owned continuation stack**
//! (not borrowed from the thread-local pool). Uses persistent data structures from
//! the [`im`] crate for O(1) fork and O(1) checkpoint.
//!
//! ## Design
//!
//! The Rholang process calculus requires concurrent evaluation of parallel
//! compositions `P | Q`. Each sub-process becomes an independent green thread
//! that shares the parent's environment spine (via structural sharing from `im`)
//! but can diverge freely without copy overhead.
//!
//! ```text
//!   Parent Thread (P | Q)
//!         │
//!    fork(child_id)
//!        ╱ ╲
//!       P   Q          ← Both share env spine; O(1) fork via im::HashMap clone
//!       │   │
//!      ...  suspend(ch) ← Q blocks waiting for channel message
//!       │         │
//!      ...   resume()   ← Scheduler wakes Q when message arrives
//! ```
//!
//! ## Feature Gate
//!
//! All types and functions in this module require the `green-threads` feature.
//!
//! ## Key Invariants
//!
//! 1. **Non-blocking**: All registry operations use `DashMap` (lock-free sharded map).
//! 2. **O(1) fork**: `im::HashMap` and `im::Vector` use structural sharing.
//! 3. **Monotonic IDs**: `GreenThreadId` values are monotonically increasing (atomic counter).
//! 4. **State machine discipline**: Only valid state transitions are permitted
//!    (see [`CekThreadState`] documentation for the transition diagram).

use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use dashmap::mapref::one::{Ref, RefMut};
use dashmap::DashMap;

use crate::cek_eval::{EvalFrame, EvalState, StepResult};
use crate::cesk_store::{GlobalCeskStore, PersistentLocalStore, StoreAddr, StoreValue};
use crate::channel::{ChannelId, GreenThreadId};
use crate::gc::RefCountGc;

// ══════════════════════════════════════════════════════════════════════════════
// QuantumResult — Outcome of executing a green thread quantum
// ══════════════════════════════════════════════════════════════════════════════

/// Result of executing a green thread for up to N CEK steps (a "quantum").
///
/// Returned by [`GreenThread::run_quantum()`]. The worker thread uses this
/// to decide what to do next:
///
/// | Variant | Worker Action |
/// |---------|--------------|
/// | `Completed` | Report to coordinator, replenish budget |
/// | `Suspended` | Register waiters, report to coordinator |
/// | `Yielded` | Re-enqueue to local deque (cooperative yield) |
/// | `Forked` | Create children, enqueue them, report fork |
/// | `Failed` | Report error to coordinator, replenish budget |
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantumResult {
    /// Thread finished executing — all work consumed.
    Completed { result: String },
    /// Thread blocked waiting on channel(s) — needs wake-up.
    Suspended { waiting_on: Vec<ChannelId> },
    /// Quantum exhausted but thread still has work — cooperative yield.
    Yielded,
    /// Thread requests forking into child threads with the given categories.
    /// The worker creates children via `GreenThreadRegistry::spawn_child()`.
    Forked { children: Vec<String> },
    /// Thread encountered an error.
    Failed { error: String },
}

// ══════════════════════════════════════════════════════════════════════════════
// CekThreadState — Execution state of a green thread
// ══════════════════════════════════════════════════════════════════════════════

/// The execution state of a green thread.
///
/// State transition diagram:
///
/// ```text
///   Ready ──────→ Running ──────→ Completed
///     ↑               │                │
///     │               ├──→ Suspended   │
///     │               │       │        │
///     │               │       └──→ Ready (resume)
///     │               │
///     │               ├──→ Failed
///     │               │
///     │               └──→ Forked
///     │
///     └───────────── (initial state from spawn)
/// ```
///
/// **Valid transitions**:
/// - `Ready` -> `Running` (scheduler picks this thread)
/// - `Running` -> `Suspended` (thread blocks on channel)
/// - `Running` -> `Completed` (thread finishes successfully)
/// - `Running` -> `Failed` (thread encounters an error)
/// - `Running` -> `Forked` (thread splits into children via `P | Q`)
/// - `Suspended` -> `Ready` (channel message arrives)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CekThreadState {
    /// Ready to execute.
    Ready,
    /// Currently running on a native worker thread.
    Running,
    /// Suspended waiting for channel message(s).
    Suspended { waiting_on: Vec<ChannelId> },
    /// Completed successfully with a result.
    Completed { result_display: String },
    /// Failed with an error.
    Failed { error: String },
    /// Forked -- this thread has been split into children.
    Forked { children: Vec<GreenThreadId> },
}

impl fmt::Display for CekThreadState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ready => write!(f, "Ready"),
            Self::Running => write!(f, "Running"),
            Self::Suspended { waiting_on } => {
                write!(f, "Suspended(waiting_on=[")?;
                for (i, ch) in waiting_on.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ch)?;
                }
                write!(f, "])")
            },
            Self::Completed { result_display } => {
                write!(f, "Completed({})", result_display)
            },
            Self::Failed { error } => write!(f, "Failed({})", error),
            Self::Forked { children } => {
                write!(f, "Forked(children=[")?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, "])")
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GreenThread — Core green thread structure
// ══════════════════════════════════════════════════════════════════════════════

/// A suspendable CEK machine with owned continuation stack and persistent environment.
///
/// Each green thread represents an independent evaluation context for a Rholang
/// process. The environment and continuation stack use persistent data structures
/// from the [`im`] crate, enabling O(1) fork for parallel composition `P | Q`.
///
/// ## Fields
///
/// | Field | CEK Component | Description |
/// |-------|--------------|-------------|
/// | `environment` | **E** | Persistent env: category -> (name -> value) |
/// | `continuation` | **K** | Persistent continuation stack (EvalFrames) |
/// | `eval_stack` | (eval) | Rewriting evaluation stack |
/// | `control` | **C** | Current term being evaluated |
/// | `eval_state` | (phase) | CEK machine evaluation phase |
/// | `eval_bindings` | **E** (flat) | Flat variable bindings for CEK evaluation |
/// | `state` | (control) | Thread execution state machine |
pub struct GreenThread {
    /// Unique identifier.
    pub id: GreenThreadId,
    /// Current execution state.
    pub state: CekThreadState,
    /// E: Persistent environment (O(1) fork for P|Q).
    ///
    /// Outer map: category name -> inner map.
    /// Inner map: variable name -> serialized value.
    /// Uses `im::HashMap` for structural sharing across forked threads.
    pub environment: im::HashMap<String, im::HashMap<String, String>>,
    /// K: Persistent continuation stack (O(1) checkpoint).
    ///
    /// Contains [`EvalFrame`] variants representing evaluation contexts.
    /// Uses `im::Vector` for O(log n) push/pop with structural sharing.
    pub continuation: im::Vector<EvalFrame>,
    /// Eval continuation stack (for rewriting).
    ///
    /// Contains [`EvalFrame`] variants. Uses `im::Vector` for structural sharing.
    pub eval_stack: im::Vector<EvalFrame>,
    /// Channels this thread is waiting on (mirrors `Suspended { waiting_on }`).
    pub channel_waiters: Vec<ChannelId>,
    /// Parent thread (None for root threads).
    pub parent: Option<GreenThreadId>,
    /// Priority (from probabilistic weights, lower = higher priority).
    pub priority: u32,
    /// Creation timestamp (monotonic counter for age-based scheduling).
    pub created_at: u64,
    /// Category being parsed/evaluated (for scheduling heuristics).
    pub category: String,
    /// C: Current term being evaluated (CEK control component).
    pub control: String,
    /// Current evaluation state (CEK machine phase).
    pub eval_state: EvalState,
    /// S (local): Per-thread CESK store with persistent data structure for O(1) fork.
    ///
    /// Contains local bindings (let-bindings, pattern-match results, closure envs).
    /// Structural sharing via `im::HashMap` ensures forked threads share data
    /// efficiently and diverge via copy-on-write.
    pub local_store: PersistentLocalStore,
    /// S (global): Shared CESK store for cross-thread values (channels, names).
    ///
    /// Lock-free concurrent access via `DashMap`. All threads in the same
    /// evaluation share the same `Arc<GlobalCeskStore>`.
    pub global_store: Arc<GlobalCeskStore>,
    /// Flat variable bindings for CEK evaluation (CESK: var → StoreAddr).
    /// Uses `im::HashMap` for O(1) fork sharing.
    pub eval_bindings: im::HashMap<String, StoreAddr>,
    /// Reference counting GC for the local store.
    pub refcount_gc: RefCountGc,
    /// Memoization cache for ground terms (O(1) fork sharing).
    pub memo_cache: im::HashMap<String, String>,
    /// Steps taken so far in this thread's lifetime.
    pub step_count: usize,
    /// Maximum steps before forced termination.
    pub step_limit: usize,
    /// Pending fork request from EvalFrame::Parallel (GS-2).
    /// Set by cek_step() when parallel sub-terms are detected.
    pub pending_fork: Option<Vec<String>>,
    /// Channel IDs that received sends during the current quantum (GS-5).
    /// Drained by the worker after each quantum to report ChannelActivity.
    pub channel_sends: Vec<ChannelId>,
}

impl fmt::Debug for GreenThread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GreenThread")
            .field("id", &self.id)
            .field("state", &self.state)
            .field("env_size", &self.env_size())
            .field("stack_depth", &self.stack_depth())
            .field("eval_stack_depth", &self.eval_stack.len())
            .field("parent", &self.parent)
            .field("priority", &self.priority)
            .field("created_at", &self.created_at)
            .field("category", &self.category)
            .field("control", &self.control)
            .field("eval_state", &self.eval_state)
            .field("step_count", &self.step_count)
            .finish()
    }
}

impl GreenThread {
    /// Create a new green thread in the `Ready` state.
    ///
    /// The thread starts with an empty environment, empty continuation stack,
    /// default priority (0), and creation timestamp 0. The caller (typically
    /// [`GreenThreadRegistry::spawn`]) should set `created_at` to the current
    /// monotonic counter value.
    pub fn new(id: GreenThreadId, category: impl Into<String>) -> Self {
        Self::with_global_store(id, category, Arc::new(GlobalCeskStore::new()))
    }

    /// Create a new green thread with a shared global store.
    ///
    /// All threads in the same evaluation should share the same `Arc<GlobalCeskStore>`.
    pub fn with_global_store(
        id: GreenThreadId,
        category: impl Into<String>,
        global_store: Arc<GlobalCeskStore>,
    ) -> Self {
        Self {
            id,
            state: CekThreadState::Ready,
            environment: im::HashMap::new(),
            continuation: im::Vector::new(),
            eval_stack: im::Vector::new(),
            channel_waiters: Vec::new(),
            parent: None,
            priority: 0,
            created_at: 0,
            category: category.into(),
            control: String::new(),
            eval_state: EvalState::Ready,
            local_store: PersistentLocalStore::new(),
            global_store,
            eval_bindings: im::HashMap::new(),
            refcount_gc: RefCountGc::new(),
            memo_cache: im::HashMap::new(),
            step_count: 0,
            step_limit: 10_000,
            pending_fork: None,
            channel_sends: Vec::new(),
        }
    }

    /// Create a green thread with a CEK control term, ready for evaluation.
    pub fn with_control(id: GreenThreadId, category: impl Into<String>, control: String) -> Self {
        let mut thread = Self::new(id, category);
        thread.control = control;
        thread
    }

    /// Create a green thread with a CEK control term and pre-populated environment.
    /// Used for forked children that inherit parent bindings (CESK: StoreAddr-based).
    pub fn with_control_and_env(
        id: GreenThreadId,
        category: impl Into<String>,
        control: String,
        env: im::HashMap<String, StoreAddr>,
    ) -> Self {
        let mut thread = Self::with_control(id, category, control);
        thread.eval_bindings = env;
        thread
    }

    /// Create a green thread with a CEK control term and string-valued environment.
    /// Convenience for backward compatibility — bulk-converts strings to store addrs.
    pub fn with_control_and_string_env(
        id: GreenThreadId,
        category: impl Into<String>,
        control: String,
        env: im::HashMap<String, String>,
    ) -> Self {
        let mut thread = Self::with_control(id, category, control);
        for (name, value) in env.iter() {
            let addr_id = thread
                .local_store
                .alloc_with(StoreValue::Simple(value.clone()));
            thread
                .eval_bindings
                .insert(name.clone(), StoreAddr::Local(addr_id));
        }
        thread
    }

    /// O(1) fork: create a child thread sharing the parent's env spine.
    ///
    /// The child receives a structural-sharing clone of:
    /// - `environment` (im::HashMap -- O(1) clone)
    /// - `continuation` (im::Vector -- O(1) clone)
    /// - `eval_stack` (im::Vector -- O(1) clone)
    /// - `eval_bindings` (im::HashMap -- O(1) clone)
    /// - `memo_cache` (im::HashMap -- O(1) clone)
    ///
    /// The child starts in `Ready` state with `parent` set to `self.id`.
    /// The parent's state is **not** modified by this call; the caller is
    /// responsible for transitioning the parent to `Forked` if appropriate.
    pub fn fork(&self, child_id: GreenThreadId, category: impl Into<String>) -> GreenThread {
        GreenThread {
            id: child_id,
            state: CekThreadState::Ready,
            environment: self.environment.clone(),
            continuation: self.continuation.clone(),
            eval_stack: self.eval_stack.clone(),
            channel_waiters: Vec::new(),
            parent: Some(self.id),
            priority: self.priority,
            created_at: 0, // Caller sets this via registry
            category: category.into(),
            // CEK: child starts fresh but shares parent's caches
            control: String::new(), // caller sets this
            eval_state: EvalState::Ready,
            // CESK: O(1) fork of persistent local store (structural sharing)
            local_store: self.local_store.fork(),
            global_store: Arc::clone(&self.global_store), // Same shared global store
            eval_bindings: self.eval_bindings.clone(),    // O(1) im clone
            refcount_gc: RefCountGc::new(),               // Child starts with fresh refcounts
            memo_cache: self.memo_cache.clone(),          // O(1) im clone, children benefit
            step_count: 0,
            step_limit: self.step_limit,
            pending_fork: None,
            channel_sends: Vec::new(),
        }
    }

    /// Transition to `Suspended`, recording the channels being waited on.
    ///
    /// # Panics
    ///
    /// Panics if the thread is not in `Running` state (debug builds only).
    pub fn suspend(&mut self, channels: Vec<ChannelId>) {
        debug_assert!(
            matches!(self.state, CekThreadState::Running),
            "suspend() called on thread {} in state {}, expected Running",
            self.id,
            self.state,
        );
        self.channel_waiters = channels.clone();
        self.state = CekThreadState::Suspended { waiting_on: channels };
    }

    /// Transition from `Suspended` to `Ready`, clearing channel waiters.
    ///
    /// # Panics
    ///
    /// Panics if the thread is not in `Suspended` state (debug builds only).
    pub fn resume(&mut self) {
        debug_assert!(
            matches!(self.state, CekThreadState::Suspended { .. }),
            "resume() called on thread {} in state {}, expected Suspended",
            self.id,
            self.state,
        );
        self.channel_waiters.clear();
        self.state = CekThreadState::Ready;
    }

    /// Transition to `Completed` with a result string.
    ///
    /// # Panics
    ///
    /// Panics if the thread is not in `Running` state (debug builds only).
    pub fn complete(&mut self, result: String) {
        debug_assert!(
            matches!(self.state, CekThreadState::Running),
            "complete() called on thread {} in state {}, expected Running",
            self.id,
            self.state,
        );
        self.state = CekThreadState::Completed { result_display: result };
    }

    /// Transition to `Failed` with an error message.
    ///
    /// # Panics
    ///
    /// Panics if the thread is not in `Running` state (debug builds only).
    pub fn fail(&mut self, error: String) {
        debug_assert!(
            matches!(self.state, CekThreadState::Running),
            "fail() called on thread {} in state {}, expected Running",
            self.id,
            self.state,
        );
        self.state = CekThreadState::Failed { error };
    }

    /// Whether this thread is runnable (in `Ready` state).
    #[inline]
    pub fn is_runnable(&self) -> bool {
        matches!(self.state, CekThreadState::Ready)
    }

    /// Whether this thread is in a terminal state (`Completed` or `Failed`).
    #[inline]
    pub fn is_terminal(&self) -> bool {
        matches!(self.state, CekThreadState::Completed { .. } | CekThreadState::Failed { .. })
    }

    /// Continuation stack depth.
    #[inline]
    pub fn stack_depth(&self) -> usize {
        self.continuation.len()
    }

    /// Total variable count across all categories in the environment.
    pub fn env_size(&self) -> usize {
        self.environment.values().map(|inner| inner.len()).sum()
    }

    /// Push a continuation frame onto the persistent stack.
    ///
    /// This is an O(log n) operation that preserves structural sharing
    /// with any threads that forked from the same ancestor.
    pub fn push_continuation(&mut self, frame: EvalFrame) {
        self.continuation.push_back(frame);
    }

    /// Pop the top continuation frame from the persistent stack.
    ///
    /// Returns `None` if the stack is empty. This is an O(log n) operation
    /// that preserves structural sharing.
    pub fn pop_continuation(&mut self) -> Option<EvalFrame> {
        self.continuation.pop_back()
    }

    /// Set a variable binding in the environment.
    ///
    /// Creates the category's inner map if it does not exist. Uses persistent
    /// update so forked threads sharing the same spine are unaffected.
    pub fn set_env(&mut self, category: &str, name: &str, value: String) {
        let cat_key = category.to_string();
        let inner = self.environment.get(&cat_key).cloned().unwrap_or_default();
        let inner = inner.update(name.to_string(), value);
        self.environment = self.environment.update(cat_key, inner);
    }

    /// Get a variable binding from the environment.
    ///
    /// Returns `None` if the category or variable name is not bound.
    pub fn get_env(&self, category: &str, name: &str) -> Option<&String> {
        self.environment
            .get(&category.to_string())
            .and_then(|inner| inner.get(&name.to_string()))
    }

    // ── CESK Store Operations ─────────────────────────────────────────────

    /// Resolve a `StoreAddr` to its value via two-tier dispatch.
    ///
    /// - `Local(id)` → `local_store.get(id)`
    /// - `Global(id)` → `global_store.get(id)` (cloned out of DashMap)
    pub fn resolve_addr(&self, addr: StoreAddr) -> Option<StoreValue> {
        match addr {
            StoreAddr::Local(id) => self.local_store.get_cloned(id),
            StoreAddr::Global(id) => self.global_store.get(id),
        }
    }

    /// Look up a variable's string value via CESK two-stage resolution.
    ///
    /// `eval_bindings[name] → StoreAddr → resolve → StoreValue → as_simple()`
    pub fn lookup_eval_binding(&self, name: &str) -> Option<String> {
        self.eval_bindings.get(name).and_then(|addr| {
            self.resolve_addr(*addr)
                .and_then(|val| val.as_simple().map(|s| s.to_string()))
        })
    }

    /// Bind a variable in the eval environment via the CESK local store.
    pub fn bind_eval(&mut self, name: String, value: String) {
        let addr_id = self.local_store.alloc_with(StoreValue::Simple(value));
        self.refcount_gc.inc_ref(addr_id);
        self.eval_bindings = self.eval_bindings.update(name, StoreAddr::Local(addr_id));
    }

    /// Collect all global addresses reachable from this thread's environment.
    ///
    /// Used by the GC coordinator to construct the mark-sweep root set.
    pub fn collect_global_roots(&self) -> Vec<u64> {
        let mut roots = Vec::new();
        // From eval_bindings
        for addr in self.eval_bindings.values() {
            if let StoreAddr::Global(id) = addr {
                roots.push(*id);
            }
        }
        // From local store (closures may capture global refs)
        roots.extend(self.local_store.collect_global_roots());
        roots
    }

    // ── Channel Bridge (CESK-5) ─────────────────────────────────────────

    /// Create a new channel and bind it in the environment via the global store.
    ///
    /// `new ch` → allocate `ChannelRef(ch_id)` in global store, bind `ch → Global(addr)`.
    pub fn create_channel_binding(
        &mut self,
        var_name: String,
        channel_id: crate::channel::ChannelId,
    ) {
        let addr_id = self
            .global_store
            .alloc_with(StoreValue::ChannelRef(channel_id));
        self.eval_bindings = self
            .eval_bindings
            .update(var_name, StoreAddr::Global(addr_id));
    }

    /// Resolve a variable to a ChannelId (for send/receive operations).
    ///
    /// `env[ch] → StoreAddr::Global(id) → global_store[id] → ChannelRef(ch_id)`
    pub fn resolve_channel_id(&self, var_name: &str) -> Option<crate::channel::ChannelId> {
        self.eval_bindings.get(var_name).and_then(|addr| {
            self.resolve_addr(*addr)
                .and_then(|val| val.as_channel_ref())
        })
    }

    // ── Closures (CESK-5) ───────────────────────────────────────────────

    /// Create a closure value capturing the current eval environment.
    ///
    /// Allocates `StoreValue::Closure { env_snapshot, body }` in the local store.
    /// Returns the `StoreAddr` of the new closure.
    pub fn create_closure(&mut self, body: String) -> StoreAddr {
        let env_snapshot: HashMap<String, StoreAddr> = self
            .eval_bindings
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();
        let addr_id = self
            .local_store
            .alloc_with(StoreValue::Closure { env_snapshot, body });
        self.refcount_gc.inc_ref(addr_id);
        StoreAddr::Local(addr_id)
    }

    /// Apply a closure: restore its captured environment and bind the argument.
    ///
    /// Returns `Some(body)` if the addr points to a closure, `None` otherwise.
    pub fn apply_closure(
        &mut self,
        closure_addr: StoreAddr,
        arg_name: String,
        arg_value: String,
    ) -> Option<String> {
        let closure_val = self.resolve_addr(closure_addr)?;
        let (env_snapshot, body) = closure_val.as_closure()?;

        // Restore captured environment
        let mut restored = im::HashMap::new();
        for (k, v) in env_snapshot {
            restored.insert(k.clone(), *v);
        }

        // Bind the argument
        let arg_id = self.local_store.alloc_with(StoreValue::Simple(arg_value));
        self.refcount_gc.inc_ref(arg_id);
        restored.insert(arg_name, StoreAddr::Local(arg_id));

        self.eval_bindings = restored;
        Some(body.to_string())
    }

    // ── Store Promotion (CESK-5) ────────────────────────────────────────

    /// Promote a local store value to the global store.
    ///
    /// Used when a closure is about to be sent on a channel: all
    /// `StoreAddr::Local` entries in its `env_snapshot` are copied to the
    /// global store and remapped to `StoreAddr::Global`.
    ///
    /// Returns the new `StoreAddr::Global(id)` for the promoted value.
    pub fn promote_to_global(&mut self, local_addr: StoreAddr) -> StoreAddr {
        match local_addr {
            StoreAddr::Global(_) => local_addr, // Already global
            StoreAddr::Local(local_id) => {
                if let Some(value) = self.local_store.get_cloned(local_id) {
                    // For closures, recursively promote captured local addrs
                    let promoted_value = match value {
                        StoreValue::Closure { env_snapshot, body } => {
                            let promoted_env: HashMap<String, StoreAddr> = env_snapshot
                                .into_iter()
                                .map(|(k, addr)| {
                                    let promoted = self.promote_to_global(addr);
                                    (k, promoted)
                                })
                                .collect();
                            StoreValue::Closure { env_snapshot: promoted_env, body }
                        },
                        other => other,
                    };
                    let global_id = self.global_store.alloc_with(promoted_value);
                    StoreAddr::Global(global_id)
                } else {
                    local_addr // Not found in local store, return as-is
                }
            },
        }
    }

    /// Perform a single CEK evaluation transition.
    ///
    /// Drives the CEK machine one step forward, modifying the control term,
    /// environment, and continuation stack as needed. Returns a `StepResult`
    /// indicating whether evaluation should continue.
    pub fn cek_step(&mut self) -> StepResult {
        // Terminal states are idempotent
        match &self.eval_state {
            EvalState::Accepted => return StepResult::Accepted,
            EvalState::Aborted { .. } => return StepResult::Aborted,
            EvalState::Error { message } => return StepResult::Error { message: message.clone() },
            _ => {},
        }

        // Determine transition based on current eval state
        match &self.eval_state {
            EvalState::Ready => {
                self.eval_state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalState::Reducing => {
                // Check memo cache for ground terms
                if let Some(cached) = self.memo_cache.get(&self.control).cloned() {
                    self.control = cached;
                    if self.continuation.is_empty() {
                        self.eval_state = EvalState::Accepted;
                        StepResult::Accepted
                    } else {
                        self.eval_state = EvalState::Ascending;
                        StepResult::Continue
                    }
                } else {
                    // No cached result
                    if self.continuation.is_empty() {
                        self.eval_state = EvalState::Accepted;
                        StepResult::Accepted
                    } else {
                        self.eval_state = EvalState::Ascending;
                        StepResult::Continue
                    }
                }
            },
            EvalState::Descending => {
                self.eval_state = EvalState::Reducing;
                StepResult::Continue
            },
            EvalState::Ascending => {
                if let Some(frame) = self.continuation.pop_back() {
                    match frame {
                        EvalFrame::BinOp { operator, lhs_display } => {
                            self.control =
                                format!("({} {} {})", lhs_display, operator, self.control);
                            self.eval_state = EvalState::Reducing;
                        },
                        EvalFrame::UnaryOp { operator } => {
                            self.control = format!("({} {})", operator, self.control);
                            self.eval_state = EvalState::Reducing;
                        },
                        EvalFrame::MatchScrutinee { .. } => {
                            self.eval_state = EvalState::Reducing;
                        },
                        EvalFrame::LetBody { var_name, body_display } => {
                            // CESK: allocate value in local store, map var → addr
                            let addr_id = self
                                .local_store
                                .alloc_with(StoreValue::Simple(self.control.clone()));
                            let addr = StoreAddr::Local(addr_id);
                            self.refcount_gc.inc_ref(addr_id);
                            self.eval_bindings = self.eval_bindings.update(var_name, addr);
                            self.control = body_display;
                            self.eval_state = EvalState::Reducing;
                        },
                        EvalFrame::SetCont { var_name } => {
                            // CESK mutation: overwrite store cell at env[var_name]
                            if let Some(addr) = self.eval_bindings.get(&var_name) {
                                match addr {
                                    StoreAddr::Local(id) => {
                                        self.local_store
                                            .set(*id, StoreValue::Simple(self.control.clone()));
                                    },
                                    StoreAddr::Global(id) => {
                                        self.global_store
                                            .set(*id, StoreValue::Simple(self.control.clone()));
                                    },
                                }
                            }
                            self.control = "void".to_string();
                            self.eval_state = EvalState::Reducing;
                        },
                        EvalFrame::Parallel { remaining, mut completed } => {
                            completed.push(self.control.clone());
                            if remaining.is_empty() {
                                // All subterms evaluated — reconstruct parallel term
                                self.control = format!("({})", completed.join(" | "));
                                self.eval_state = EvalState::Reducing;
                            } else {
                                // GS-2: Fork remaining sub-terms as child threads
                                self.pending_fork = Some(remaining.clone());
                                // Stash completed results — parent will reconstruct when children finish
                                self.continuation.push_back(EvalFrame::Parallel {
                                    remaining: Vec::new(),
                                    completed,
                                });
                                self.eval_state = EvalState::Reducing;
                            }
                        },
                        EvalFrame::RewriteCont { .. } => {
                            self.eval_state = EvalState::Reducing;
                        },
                    }
                } else {
                    self.eval_state = EvalState::Accepted;
                }
                StepResult::Continue
            },
            _ => StepResult::Error {
                message: format!("unexpected eval state: {}", self.eval_state),
            },
        }
    }

    /// Take and clear the pending fork request.
    /// Returns `Some(children)` if a fork was requested, `None` otherwise.
    pub fn take_pending_fork(&mut self) -> Option<Vec<String>> {
        self.pending_fork.take()
    }

    /// Record a channel send that occurred during this quantum (GS-5).
    ///
    /// Called by the CEK step logic when a channel send operation executes.
    /// The worker drains these after the quantum to send a `ChannelActivity`
    /// report, enabling event-driven wake-ups.
    pub fn record_channel_send(&mut self, channel_id: ChannelId) {
        self.channel_sends.push(channel_id);
    }

    /// Drain and return all channel sends recorded during the current quantum (GS-5).
    ///
    /// The worker calls this after `run_quantum()` returns to check if any
    /// channel activity occurred that should trigger immediate wake-ups.
    pub fn take_channel_sends(&mut self) -> Vec<ChannelId> {
        std::mem::take(&mut self.channel_sends)
    }

    /// Execute up to `max_steps` of work, returning the quantum result.
    ///
    /// This is the core execution primitive for the M:N scheduler. Each
    /// "step" drives one CEK evaluation transition. The method returns when:
    ///
    /// - Evaluation accepts → `Completed`
    /// - Channel waiters are pending → `Suspended`
    /// - `max_steps` consumed → `Yielded` (cooperative yield)
    /// - Step limit exceeded → `Failed`
    /// - Parallel fork requested → `Forked`
    ///
    /// # Precondition
    ///
    /// The thread must be in `Running` state (debug-asserted).
    pub fn run_quantum(&mut self, max_steps: usize) -> QuantumResult {
        debug_assert!(
            matches!(self.state, CekThreadState::Running),
            "run_quantum() called on thread {} in state {}, expected Running",
            self.id,
            self.state,
        );

        // Check for pending channel waits (blocking receive).
        if !self.channel_waiters.is_empty() {
            let waiting_on = self.channel_waiters.clone();
            self.state = CekThreadState::Suspended { waiting_on: waiting_on.clone() };
            return QuantumResult::Suspended { waiting_on };
        }

        // If control is empty, run the legacy EvalFrame/continuation stack path.
        if self.control.is_empty() && matches!(self.eval_state, EvalState::Ready) {
            return self.run_quantum_legacy_stacks(max_steps);
        }

        // CEK evaluation loop
        for _ in 0..max_steps {
            if self.step_count >= self.step_limit {
                let error = format!("step limit exceeded ({} steps)", self.step_limit);
                self.fail(error.clone());
                return QuantumResult::Failed { error };
            }

            match self.cek_step() {
                StepResult::Continue => {
                    self.step_count += 1;
                },
                StepResult::Accepted => {
                    let result = self.control.clone();
                    self.complete(result.clone());
                    return QuantumResult::Completed { result };
                },
                StepResult::Aborted => {
                    let error = "evaluation aborted".to_string();
                    self.fail(error.clone());
                    return QuantumResult::Failed { error };
                },
                StepResult::Error { message } => {
                    self.fail(message.clone());
                    return QuantumResult::Failed { error: message };
                },
            }

            // Check for parallel fork request (GS-2)
            if let Some(children) = self.take_pending_fork() {
                self.state = CekThreadState::Forked { children: Vec::new() };
                return QuantumResult::Forked { children };
            }
        }

        QuantumResult::Yielded
    }

    /// Legacy quantum execution for threads without CEK control terms.
    /// Preserves backward compatibility with tests that use EvalFrame-based stacks.
    fn run_quantum_legacy_stacks(&mut self, max_steps: usize) -> QuantumResult {
        for _ in 0..max_steps {
            if !self.channel_waiters.is_empty() {
                let waiting_on = self.channel_waiters.clone();
                self.state = CekThreadState::Suspended { waiting_on: waiting_on.clone() };
                return QuantumResult::Suspended { waiting_on };
            }

            if self.eval_stack.pop_back().is_some() {
                continue;
            }

            if self.continuation.pop_back().is_some() {
                continue;
            }

            let result = "()".to_string();
            self.state = CekThreadState::Completed { result_display: result.clone() };
            return QuantumResult::Completed { result };
        }
        QuantumResult::Yielded
    }

    /// Request a parallel fork into child threads.
    ///
    /// Sets the thread state to `Forked` with empty children (actual child
    /// IDs are assigned by the worker after calling `spawn_child`).
    /// Returns `QuantumResult::Forked` with the category names for each child.
    ///
    /// # Precondition
    ///
    /// The thread must be in `Running` state (debug-asserted).
    pub fn fork_parallel(&mut self, categories: Vec<String>) -> QuantumResult {
        debug_assert!(
            matches!(self.state, CekThreadState::Running),
            "fork_parallel() called on thread {} in state {}, expected Running",
            self.id,
            self.state,
        );
        self.state = CekThreadState::Forked { children: Vec::new() };
        QuantumResult::Forked { children: categories }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GreenThreadRegistry — Manages all green threads
// ══════════════════════════════════════════════════════════════════════════════

/// Thread-safe registry managing all green threads.
///
/// Uses [`DashMap`] for lock-free concurrent access and [`AtomicU64`] for
/// monotonic ID generation. All operations are non-blocking.
///
/// ## Thread Safety
///
/// The registry is `Send + Sync` and can be shared across native OS threads
/// (e.g., in a work-stealing scheduler). Individual thread entries are accessed
/// via `DashMap`'s sharded locking, so concurrent reads and writes to different
/// threads do not contend.
pub struct GreenThreadRegistry {
    /// All managed green threads, keyed by their unique ID.
    threads: DashMap<GreenThreadId, GreenThread>,
    /// Monotonic ID counter for generating unique `GreenThreadId` values.
    next_id: AtomicU64,
    /// Monotonic creation counter for age-based scheduling.
    ///
    /// Each spawned thread gets `created_at = creation_counter.fetch_add(1)`.
    /// Older threads (lower `created_at`) are scheduled before newer ones
    /// at the same priority level, providing fairness.
    creation_counter: AtomicU64,
}

impl fmt::Debug for GreenThreadRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GreenThreadRegistry")
            .field("thread_count", &self.threads.len())
            .field("next_id", &self.next_id.load(Ordering::Relaxed))
            .field("creation_counter", &self.creation_counter.load(Ordering::Relaxed))
            .finish()
    }
}

impl Default for GreenThreadRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl GreenThreadRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            threads: DashMap::new(),
            next_id: AtomicU64::new(0),
            creation_counter: AtomicU64::new(0),
        }
    }

    /// Spawn a new root green thread (no parent).
    ///
    /// Returns the unique ID of the newly created thread. The thread starts
    /// in `Ready` state with the given category.
    pub fn spawn(&self, category: String) -> GreenThreadId {
        let id = GreenThreadId(self.next_id.fetch_add(1, Ordering::Relaxed));
        let created_at = self.creation_counter.fetch_add(1, Ordering::Relaxed);
        let mut thread = GreenThread::new(id, category);
        thread.created_at = created_at;
        self.threads.insert(id, thread);
        id
    }

    /// Spawn a child green thread forked from a parent.
    ///
    /// The child inherits the parent's environment and continuation stack
    /// via O(1) structural sharing. Returns `None` if the parent ID is not
    /// found in the registry.
    ///
    /// The parent thread's state is **not** modified. The caller should
    /// transition the parent to `Forked` or another appropriate state.
    pub fn spawn_child(&self, parent_id: GreenThreadId, category: String) -> Option<GreenThreadId> {
        let child_id = GreenThreadId(self.next_id.fetch_add(1, Ordering::Relaxed));
        let created_at = self.creation_counter.fetch_add(1, Ordering::Relaxed);

        // Read parent to fork from (hold the read guard briefly).
        let parent_ref = self.threads.get(&parent_id)?;
        let mut child = parent_ref.fork(child_id, category);
        child.created_at = created_at;
        drop(parent_ref); // Release parent lock before inserting child.

        self.threads.insert(child_id, child);
        Some(child_id)
    }

    /// Get a shared reference to a green thread by ID.
    ///
    /// Returns `None` if the ID is not in the registry. The returned `Ref`
    /// holds a shard lock; drop it promptly to avoid contention.
    pub fn get(&self, id: GreenThreadId) -> Option<Ref<'_, GreenThreadId, GreenThread>> {
        self.threads.get(&id)
    }

    /// Get a mutable reference to a green thread by ID.
    ///
    /// Returns `None` if the ID is not in the registry. The returned `RefMut`
    /// holds an exclusive shard lock; drop it promptly to avoid contention.
    pub fn get_mut(&self, id: GreenThreadId) -> Option<RefMut<'_, GreenThreadId, GreenThread>> {
        self.threads.get_mut(&id)
    }

    /// Remove a green thread from the registry, returning it if present.
    pub fn remove(&self, id: GreenThreadId) -> Option<GreenThread> {
        self.threads.remove(&id).map(|(_, thread)| thread)
    }

    /// Total number of threads in the registry (all states).
    pub fn thread_count(&self) -> usize {
        self.threads.len()
    }

    /// Number of active threads (Ready + Running + Suspended).
    ///
    /// Excludes Completed, Failed, and Forked threads.
    pub fn active_count(&self) -> usize {
        self.threads
            .iter()
            .filter(|entry| {
                matches!(
                    entry.value().state,
                    CekThreadState::Ready
                        | CekThreadState::Running
                        | CekThreadState::Suspended { .. }
                )
            })
            .count()
    }

    /// Collect IDs of all runnable (Ready) threads, sorted by priority then age.
    ///
    /// Lower priority value = higher scheduling priority (run first).
    /// Among threads with equal priority, older threads (lower `created_at`)
    /// are returned first for fairness.
    pub fn runnable_ids(&self) -> Vec<GreenThreadId> {
        let mut runnable: Vec<(u32, u64, GreenThreadId)> = self
            .threads
            .iter()
            .filter(|entry| entry.value().is_runnable())
            .map(|entry| {
                let t = entry.value();
                (t.priority, t.created_at, t.id)
            })
            .collect();

        // Sort by (priority ASC, created_at ASC) for deterministic scheduling.
        runnable.sort_unstable();

        runnable.into_iter().map(|(_, _, id)| id).collect()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a test EvalFrame (RewriteCont) for backward-compatible tests
    /// that previously used string-based continuation/eval stacks.
    fn test_frame(name: &str) -> EvalFrame {
        EvalFrame::RewriteCont { rule_name: name.to_string() }
    }

    // ── GreenThread::new creates Ready thread ──────────────────────────────

    #[test]
    fn test_new_creates_ready_thread() {
        let id = GreenThreadId(0);
        let thread = GreenThread::new(id, "Expr");

        assert_eq!(thread.id, id);
        assert_eq!(thread.state, CekThreadState::Ready);
        assert!(thread.is_runnable());
        assert!(!thread.is_terminal());
        assert_eq!(thread.stack_depth(), 0);
        assert_eq!(thread.env_size(), 0);
        assert!(thread.parent.is_none());
        assert_eq!(thread.priority, 0);
        assert_eq!(thread.created_at, 0);
        assert_eq!(thread.category, "Expr");
        assert!(thread.channel_waiters.is_empty());
        // New CEK fields
        assert_eq!(thread.control, "");
        assert_eq!(thread.eval_state, EvalState::Ready);
        assert!(thread.eval_bindings.is_empty());
        assert!(thread.memo_cache.is_empty());
        assert_eq!(thread.step_count, 0);
        assert_eq!(thread.step_limit, 10_000);
        assert!(thread.pending_fork.is_none());
    }

    // ── GreenThread::fork creates independent copy with shared env spine ───

    #[test]
    fn test_fork_creates_independent_copy() {
        let parent_id = GreenThreadId(0);
        let child_id = GreenThreadId(1);
        let mut parent = GreenThread::new(parent_id, "Proc");
        parent.set_env("Int", "x", "42".to_string());
        parent.push_continuation(test_frame("InfixRHS"));
        parent.priority = 5;

        let child = parent.fork(child_id, "Proc");

        assert_eq!(child.id, child_id);
        assert_eq!(child.state, CekThreadState::Ready);
        assert_eq!(child.parent, Some(parent_id));
        assert_eq!(child.priority, 5);
        // Shared spine: child sees parent's env
        assert_eq!(child.get_env("Int", "x"), Some(&"42".to_string()));
        // Shared spine: child sees parent's continuation
        assert_eq!(child.stack_depth(), 1);
    }

    // ── GreenThread environment set/get/category operations ────────────────

    #[test]
    fn test_environment_set_get() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");

        assert_eq!(thread.get_env("Int", "x"), None);

        thread.set_env("Int", "x", "5".to_string());
        assert_eq!(thread.get_env("Int", "x"), Some(&"5".to_string()));

        thread.set_env("Int", "y", "10".to_string());
        assert_eq!(thread.get_env("Int", "y"), Some(&"10".to_string()));
        assert_eq!(thread.env_size(), 2);

        // Different category
        thread.set_env("Proc", "p", "PZero".to_string());
        assert_eq!(thread.get_env("Proc", "p"), Some(&"PZero".to_string()));
        assert_eq!(thread.env_size(), 3);

        // Nonexistent lookups
        assert_eq!(thread.get_env("Int", "z"), None);
        assert_eq!(thread.get_env("Name", "n"), None);
    }

    // ── GreenThread environment overwrite ──────────────────────────────────

    #[test]
    fn test_environment_overwrite() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.set_env("Int", "x", "1".to_string());
        assert_eq!(thread.get_env("Int", "x"), Some(&"1".to_string()));

        thread.set_env("Int", "x", "2".to_string());
        assert_eq!(thread.get_env("Int", "x"), Some(&"2".to_string()));
        assert_eq!(thread.env_size(), 1);
    }

    // ── GreenThread suspend/resume state transitions ───────────────────────

    #[test]
    fn test_suspend_and_resume() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        // Must be Running to suspend.
        thread.state = CekThreadState::Running;

        let channels = vec![ChannelId(1), ChannelId(2)];
        thread.suspend(channels.clone());

        assert_eq!(thread.state, CekThreadState::Suspended { waiting_on: channels.clone() });
        assert_eq!(thread.channel_waiters, channels);
        assert!(!thread.is_runnable());
        assert!(!thread.is_terminal());

        thread.resume();
        assert_eq!(thread.state, CekThreadState::Ready);
        assert!(thread.channel_waiters.is_empty());
        assert!(thread.is_runnable());
    }

    // ── GreenThread complete/fail state transitions ────────────────────────

    #[test]
    fn test_complete_transition() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;

        thread.complete("42".to_string());
        assert_eq!(thread.state, CekThreadState::Completed { result_display: "42".to_string() });
        assert!(thread.is_terminal());
        assert!(!thread.is_runnable());
    }

    #[test]
    fn test_fail_transition() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;

        thread.fail("division by zero".to_string());
        assert_eq!(thread.state, CekThreadState::Failed { error: "division by zero".to_string() });
        assert!(thread.is_terminal());
        assert!(!thread.is_runnable());
    }

    // ── GreenThread continuation push/pop ──────────────────────────────────

    #[test]
    fn test_continuation_push_pop() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        assert_eq!(thread.stack_depth(), 0);
        assert_eq!(thread.pop_continuation(), None);

        thread.push_continuation(test_frame("InfixRHS"));
        thread.push_continuation(test_frame("RD_Let_0"));
        assert_eq!(thread.stack_depth(), 2);

        assert_eq!(thread.pop_continuation(), Some(test_frame("RD_Let_0")));
        assert_eq!(thread.stack_depth(), 1);

        assert_eq!(thread.pop_continuation(), Some(test_frame("InfixRHS")));
        assert_eq!(thread.stack_depth(), 0);
        assert_eq!(thread.pop_continuation(), None);
    }

    // ── GreenThread is_runnable/is_terminal predicates ─────────────────────

    #[test]
    fn test_is_runnable_predicate() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        assert!(thread.is_runnable());

        thread.state = CekThreadState::Running;
        assert!(!thread.is_runnable());

        thread.state = CekThreadState::Suspended { waiting_on: vec![] };
        assert!(!thread.is_runnable());

        thread.state = CekThreadState::Ready;
        assert!(thread.is_runnable());
    }

    #[test]
    fn test_is_terminal_predicate() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        assert!(!thread.is_terminal());

        thread.state = CekThreadState::Running;
        assert!(!thread.is_terminal());

        thread.state = CekThreadState::Completed { result_display: "ok".to_string() };
        assert!(thread.is_terminal());

        thread.state = CekThreadState::Failed { error: "oops".to_string() };
        assert!(thread.is_terminal());

        thread.state = CekThreadState::Forked { children: vec![GreenThreadId(1)] };
        assert!(!thread.is_terminal());
    }

    // ── GreenThreadRegistry spawn/get/remove ───────────────────────────────

    #[test]
    fn test_registry_spawn_and_get() {
        let registry = GreenThreadRegistry::new();
        assert_eq!(registry.thread_count(), 0);

        let id = registry.spawn("Expr".to_string());
        assert_eq!(registry.thread_count(), 1);

        let thread_ref = registry.get(id).expect("thread should exist");
        assert_eq!(thread_ref.id, id);
        assert_eq!(thread_ref.category, "Expr");
        assert_eq!(thread_ref.state, CekThreadState::Ready);
        drop(thread_ref);

        // Nonexistent ID
        assert!(registry.get(GreenThreadId(999)).is_none());
    }

    #[test]
    fn test_registry_remove() {
        let registry = GreenThreadRegistry::new();
        let id = registry.spawn("Proc".to_string());
        assert_eq!(registry.thread_count(), 1);

        let removed = registry.remove(id).expect("thread should be removable");
        assert_eq!(removed.id, id);
        assert_eq!(registry.thread_count(), 0);

        // Double remove returns None.
        assert!(registry.remove(id).is_none());
    }

    // ── GreenThreadRegistry spawn_child links parent ───────────────────────

    #[test]
    fn test_registry_spawn_child() {
        let registry = GreenThreadRegistry::new();
        let parent_id = registry.spawn("Proc".to_string());

        // Set some env on parent.
        {
            let mut parent = registry.get_mut(parent_id).expect("parent exists");
            parent.set_env("Int", "x", "99".to_string());
            parent.push_continuation(test_frame("Frame_A"));
        }

        let child_id = registry
            .spawn_child(parent_id, "Proc".to_string())
            .expect("parent should exist");

        assert_eq!(registry.thread_count(), 2);

        let child = registry.get(child_id).expect("child exists");
        assert_eq!(child.parent, Some(parent_id));
        assert_eq!(child.get_env("Int", "x"), Some(&"99".to_string()));
        assert_eq!(child.stack_depth(), 1);
        drop(child);

        // Spawn from nonexistent parent.
        assert!(registry
            .spawn_child(GreenThreadId(999), "Expr".to_string())
            .is_none());
    }

    // ── GreenThreadRegistry active_count tracking ──────────────────────────

    #[test]
    fn test_registry_active_count() {
        let registry = GreenThreadRegistry::new();
        assert_eq!(registry.active_count(), 0);

        let id1 = registry.spawn("Expr".to_string());
        let id2 = registry.spawn("Proc".to_string());
        let id3 = registry.spawn("Name".to_string());
        assert_eq!(registry.active_count(), 3); // All Ready

        // Transition id1 to Running (active).
        {
            let mut t = registry.get_mut(id1).expect("exists");
            t.state = CekThreadState::Running;
        }
        assert_eq!(registry.active_count(), 3); // Running is active

        // Transition id2 to Suspended (active).
        {
            let mut t = registry.get_mut(id2).expect("exists");
            t.state = CekThreadState::Suspended { waiting_on: vec![ChannelId(0)] };
        }
        assert_eq!(registry.active_count(), 3); // Suspended is active

        // Transition id3 to Completed (not active).
        {
            let mut t = registry.get_mut(id3).expect("exists");
            t.state = CekThreadState::Completed { result_display: "done".to_string() };
        }
        assert_eq!(registry.active_count(), 2);

        // Transition id1 to Failed (not active).
        {
            let mut t = registry.get_mut(id1).expect("exists");
            t.state = CekThreadState::Failed { error: "err".to_string() };
        }
        assert_eq!(registry.active_count(), 1); // Only id2 (Suspended)
    }

    // ── GreenThreadRegistry runnable_ids sorting ───────────────────────────

    #[test]
    fn test_registry_runnable_ids_sorted() {
        let registry = GreenThreadRegistry::new();

        // Spawn 4 threads with different priorities.
        let id_a = registry.spawn("A".to_string()); // priority=0, created_at=0
        let id_b = registry.spawn("B".to_string()); // priority=0, created_at=1
        let id_c = registry.spawn("C".to_string()); // priority=0, created_at=2
        let id_d = registry.spawn("D".to_string()); // priority=0, created_at=3

        // All same priority -> sorted by age (created_at ASC).
        let ids = registry.runnable_ids();
        assert_eq!(ids, vec![id_a, id_b, id_c, id_d]);

        // Give id_d lower priority (higher number = lower priority = runs later).
        {
            let mut t = registry.get_mut(id_d).expect("exists");
            t.priority = 10;
        }

        // Expected: id_a(p=0,t=0), id_b(p=0,t=1), id_c(p=0,t=2), id_d(p=10,t=3)
        let ids = registry.runnable_ids();
        assert_eq!(ids, vec![id_a, id_b, id_c, id_d]);

        // Give id_c highest priority (lowest number).
        {
            let mut t = registry.get_mut(id_c).expect("exists");
            t.priority = 0; // Same as a,b -- stays in age order among them
        }

        // Make id_a non-runnable.
        {
            let mut t = registry.get_mut(id_a).expect("exists");
            t.state = CekThreadState::Running;
        }
        let ids = registry.runnable_ids();
        assert_eq!(ids, vec![id_b, id_c, id_d]);
    }

    // ── Fork produces independent environments ─────────────────────────────

    #[test]
    fn test_fork_independent_environments() {
        let mut parent = GreenThread::new(GreenThreadId(0), "Proc");
        parent.set_env("Int", "x", "1".to_string());
        parent.set_env("Int", "y", "2".to_string());

        let mut child = parent.fork(GreenThreadId(1), "Proc");

        // Child modifies its environment.
        child.set_env("Int", "x", "100".to_string());
        child.set_env("Int", "z", "300".to_string());

        // Parent is unchanged (persistent data structures).
        assert_eq!(parent.get_env("Int", "x"), Some(&"1".to_string()));
        assert_eq!(parent.get_env("Int", "y"), Some(&"2".to_string()));
        assert_eq!(parent.get_env("Int", "z"), None);
        assert_eq!(parent.env_size(), 2);

        // Child has its own view.
        assert_eq!(child.get_env("Int", "x"), Some(&"100".to_string()));
        assert_eq!(child.get_env("Int", "y"), Some(&"2".to_string()));
        assert_eq!(child.get_env("Int", "z"), Some(&"300".to_string()));
        assert_eq!(child.env_size(), 3);
    }

    // ── Fork produces independent continuation stacks ──────────────────────

    #[test]
    fn test_fork_independent_continuation_stacks() {
        let mut parent = GreenThread::new(GreenThreadId(0), "Proc");
        parent.push_continuation(test_frame("Frame_A"));
        parent.push_continuation(test_frame("Frame_B"));

        let mut child = parent.fork(GreenThreadId(1), "Proc");

        // Child modifies its stack.
        child.push_continuation(test_frame("Frame_C"));
        assert_eq!(child.stack_depth(), 3);

        // Parent stack is unchanged.
        assert_eq!(parent.stack_depth(), 2);
        assert_eq!(parent.pop_continuation(), Some(test_frame("Frame_B")));
        assert_eq!(parent.pop_continuation(), Some(test_frame("Frame_A")));
        assert_eq!(parent.stack_depth(), 0);

        // Child still has all 3.
        assert_eq!(child.pop_continuation(), Some(test_frame("Frame_C")));
        assert_eq!(child.pop_continuation(), Some(test_frame("Frame_B")));
        assert_eq!(child.pop_continuation(), Some(test_frame("Frame_A")));
    }

    // ── CekThreadState display ─────────────────────────────────────────────

    #[test]
    fn test_cek_thread_state_display() {
        assert_eq!(CekThreadState::Ready.to_string(), "Ready");
        assert_eq!(CekThreadState::Running.to_string(), "Running");
        assert_eq!(
            CekThreadState::Suspended {
                waiting_on: vec![ChannelId(1), ChannelId(2)]
            }
            .to_string(),
            "Suspended(waiting_on=[ch#1, ch#2])"
        );
        assert_eq!(
            CekThreadState::Completed { result_display: "42".to_string() }.to_string(),
            "Completed(42)"
        );
        assert_eq!(
            CekThreadState::Failed { error: "oops".to_string() }.to_string(),
            "Failed(oops)"
        );
        assert_eq!(
            CekThreadState::Forked {
                children: vec![GreenThreadId(1), GreenThreadId(2)]
            }
            .to_string(),
            "Forked(children=[gt#1, gt#2])"
        );
    }

    // ── Registry monotonic ID generation ───────────────────────────────────

    #[test]
    fn test_registry_monotonic_ids() {
        let registry = GreenThreadRegistry::new();
        let id1 = registry.spawn("A".to_string());
        let id2 = registry.spawn("B".to_string());
        let id3 = registry.spawn("C".to_string());

        assert!(id1.0 < id2.0);
        assert!(id2.0 < id3.0);
    }

    // ── Registry get_mut allows state transitions ──────────────────────────

    #[test]
    fn test_registry_get_mut() {
        let registry = GreenThreadRegistry::new();
        let id = registry.spawn("Expr".to_string());

        {
            let mut t = registry.get_mut(id).expect("exists");
            t.state = CekThreadState::Running;
            t.push_continuation(test_frame("Frame_X"));
        }

        let t = registry.get(id).expect("exists");
        assert_eq!(t.state, CekThreadState::Running);
        assert_eq!(t.stack_depth(), 1);
    }

    // ── Eval stack independence across forks ────────────────────────────────

    #[test]
    fn test_fork_independent_eval_stacks() {
        let mut parent = GreenThread::new(GreenThreadId(0), "Expr");
        parent.eval_stack.push_back(test_frame("EvalFrame_A"));

        let mut child = parent.fork(GreenThreadId(1), "Expr");
        child.eval_stack.push_back(test_frame("EvalFrame_B"));

        // Parent's eval stack is unchanged.
        assert_eq!(parent.eval_stack.len(), 1);
        assert_eq!(child.eval_stack.len(), 2);
    }

    // ── GreenThread debug formatting ───────────────────────────────────────

    #[test]
    fn test_green_thread_debug() {
        let mut thread = GreenThread::new(GreenThreadId(42), "Expr");
        thread.set_env("Int", "x", "1".to_string());
        thread.push_continuation(test_frame("Frame_A"));

        let debug_str = format!("{:?}", thread);
        assert!(debug_str.contains("GreenThread"));
        assert!(debug_str.contains("env_size: 1"));
        assert!(debug_str.contains("stack_depth: 1"));
        assert!(debug_str.contains("Expr"));
        assert!(debug_str.contains("control"));
        assert!(debug_str.contains("eval_state"));
        assert!(debug_str.contains("step_count"));
    }

    // ── GreenThreadRegistry default ────────────────────────────────────────

    #[test]
    fn test_registry_default() {
        let registry = GreenThreadRegistry::default();
        assert_eq!(registry.thread_count(), 0);
        assert_eq!(registry.active_count(), 0);
        assert!(registry.runnable_ids().is_empty());
    }

    // ── run_quantum tests ────────────────────────────────────────────────

    #[test]
    fn test_run_quantum_completes_when_stacks_empty() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;
        // Both stacks empty, no control term -> should complete immediately.
        let result = thread.run_quantum(100);
        assert_eq!(result, QuantumResult::Completed { result: "()".to_string() });
        assert!(thread.is_terminal());
    }

    #[test]
    fn test_run_quantum_yields_on_exhaustion() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;
        // Push enough legacy stack work to exhaust the quantum.
        for i in 0..10 {
            thread
                .eval_stack
                .push_back(test_frame(&format!("frame_{}", i)));
        }
        // Quantum of 5 → should yield with 5 frames remaining.
        let result = thread.run_quantum(5);
        assert_eq!(result, QuantumResult::Yielded);
        assert_eq!(thread.eval_stack.len(), 5);
        // Thread is still Running (not terminal).
        assert_eq!(thread.state, CekThreadState::Running);
    }

    #[test]
    fn test_run_quantum_suspends_on_channel_waiters() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        thread.state = CekThreadState::Running;
        thread.channel_waiters = vec![ChannelId(10), ChannelId(20)];
        thread.eval_stack.push_back(test_frame("work"));
        let result = thread.run_quantum(100);
        assert_eq!(
            result,
            QuantumResult::Suspended {
                waiting_on: vec![ChannelId(10), ChannelId(20)]
            }
        );
        assert!(matches!(thread.state, CekThreadState::Suspended { .. }));
    }

    #[test]
    fn test_run_quantum_processes_eval_then_continuation() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;
        thread.eval_stack.push_back(test_frame("eval_a"));
        thread.eval_stack.push_back(test_frame("eval_b"));
        thread.push_continuation(test_frame("cont_x"));

        // Quantum of 10: consumes 2 eval frames + 1 continuation + completes.
        let result = thread.run_quantum(10);
        assert_eq!(result, QuantumResult::Completed { result: "()".to_string() });
        assert_eq!(thread.eval_stack.len(), 0);
        assert_eq!(thread.stack_depth(), 0);
    }

    #[test]
    fn test_run_quantum_exact_steps() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
        thread.state = CekThreadState::Running;
        for i in 0..5 {
            thread.eval_stack.push_back(test_frame(&format!("e{}", i)));
        }
        // Quantum exactly equals work: processes all 5, then loop ends → Yielded.
        let result = thread.run_quantum(5);
        assert_eq!(result, QuantumResult::Yielded);
        assert_eq!(thread.eval_stack.len(), 0);
        // Continuation is still empty, so next quantum would complete.
        let result = thread.run_quantum(1);
        assert_eq!(result, QuantumResult::Completed { result: "()".to_string() });
    }

    #[test]
    fn test_fork_parallel() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        thread.state = CekThreadState::Running;
        let result = thread.fork_parallel(vec!["Proc".to_string(), "Proc".to_string()]);
        assert_eq!(
            result,
            QuantumResult::Forked {
                children: vec!["Proc".to_string(), "Proc".to_string()]
            }
        );
        assert!(matches!(thread.state, CekThreadState::Forked { .. }));
    }

    // ── Property-Based Tests (proptest) ──────────────────────────────────

    mod proptest_green_thread {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Fork produces environment independence: mutating the child's env
            /// does not affect the parent, and vice versa.
            #[test]
            fn prop_fork_env_independence(
                parent_keys in proptest::collection::vec("[a-z]{1,8}", 1..16),
                parent_vals in proptest::collection::vec("[0-9]{1,4}", 1..16),
                child_key in "[a-z]{1,8}",
                child_val in "[0-9]{1,4}",
            ) {
                let n = parent_keys.len().min(parent_vals.len());
                let mut parent = GreenThread::new(GreenThreadId(0), "Expr");
                for i in 0..n {
                    parent.set_env("cat", &parent_keys[i], parent_vals[i].clone());
                }
                let parent_env_size_before = parent.env_size();

                let mut child = parent.fork(GreenThreadId(1), "Expr");
                // Mutate child's environment.
                child.set_env("cat", &child_key, child_val.clone());

                // Parent env size must not have changed.
                prop_assert_eq!(
                    parent.env_size(), parent_env_size_before,
                    "parent env size must be unaffected by child mutation"
                );
                // Child should see the new binding.
                prop_assert_eq!(
                    child.get_env("cat", &child_key),
                    Some(&child_val),
                    "child must see its own binding"
                );
            }

            /// Stack independence: each thread has its own continuation stack;
            /// pushing onto a forked child does not affect the parent.
            #[test]
            fn prop_stack_independence(
                parent_frame_count in 0usize..16,
                child_extra_count in 1usize..8,
            ) {
                let mut parent = GreenThread::new(GreenThreadId(0), "Proc");
                for i in 0..parent_frame_count {
                    parent.push_continuation(test_frame(&format!("F{}", i)));
                }
                let parent_depth = parent.stack_depth();

                let mut child = parent.fork(GreenThreadId(1), "Proc");
                for i in 0..child_extra_count {
                    child.push_continuation(test_frame(&format!("C{}", i)));
                }

                // Parent stack depth is unchanged.
                prop_assert_eq!(
                    parent.stack_depth(), parent_depth,
                    "parent stack depth must be unaffected by child push"
                );
                // Child stack depth grew by the extra frames.
                prop_assert_eq!(
                    child.stack_depth(), parent_depth + child_extra_count,
                    "child stack depth = parent + extra"
                );
            }

            /// Valid state transitions: only allowed transitions succeed.
            /// Running -> Suspended -> Ready is a valid chain.
            #[test]
            fn prop_valid_state_transitions(
                n_channels in 0usize..8,
            ) {
                let channels: Vec<ChannelId> = (0..n_channels).map(|i| ChannelId(i as u64)).collect();
                let mut thread = GreenThread::new(GreenThreadId(0), "Expr");

                // Ready -> Running (manual).
                thread.state = CekThreadState::Running;
                prop_assert_eq!(thread.state.clone(), CekThreadState::Running);

                // Running -> Suspended.
                thread.suspend(channels.clone());
                let is_suspended = matches!(thread.state, CekThreadState::Suspended { .. });
                prop_assert!(is_suspended, "thread should be in Suspended state");
                prop_assert_eq!(thread.channel_waiters.clone(), channels);

                // Suspended -> Ready.
                thread.resume();
                prop_assert_eq!(thread.state.clone(), CekThreadState::Ready);
                prop_assert!(thread.channel_waiters.is_empty());
                prop_assert!(thread.is_runnable());
            }

            /// Thread ID monotonicity: each new thread spawned by the registry
            /// gets a strictly higher ID than the previous one.
            #[test]
            fn prop_thread_id_monotonicity(n in 2usize..64) {
                let registry = GreenThreadRegistry::new();
                let mut prev_id = registry.spawn("A".to_string());
                for _ in 1..n {
                    let next_id = registry.spawn("A".to_string());
                    prop_assert!(
                        next_id.0 > prev_id.0,
                        "IDs must be strictly monotonic: {} must be > {}",
                        next_id.0, prev_id.0
                    );
                    prev_id = next_id;
                }
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Integration Tests (Track 7A)
    // ══════════════════════════════════════════════════════════════════════════

    /// IT-1: Fork, communicate, and verify: spawn → fork → child inherits env.
    #[test]
    fn test_integration_fork_communicate_verify() {
        let registry = GreenThreadRegistry::new();
        let parent_id = registry.spawn("Proc".to_string());

        // Set some env on parent
        registry
            .get_mut(parent_id)
            .expect("parent")
            .set_env("Proc", "x", "42".to_string());

        let child_id = registry
            .spawn_child(parent_id, "Proc".to_string())
            .expect("fork should succeed");

        // Parent and child are independent threads
        assert_ne!(parent_id, child_id);
        assert!(registry.get(parent_id).is_some());
        assert!(registry.get(child_id).is_some());

        // Child's parent field should reference the parent
        let child = registry.get(child_id).expect("child exists");
        assert_eq!(child.parent, Some(parent_id));

        // Child inherits parent's env (structural sharing)
        assert_eq!(child.get_env("Proc", "x"), Some(&"42".to_string()));

        // Both should be runnable
        assert!(registry
            .get(parent_id)
            .expect("parent exists")
            .is_runnable());
        assert!(child.is_runnable());
    }

    /// IT-2: Multi-thread with priorities: higher priority threads have higher values.
    #[test]
    fn test_integration_multi_thread_priority() {
        let registry = GreenThreadRegistry::new();
        let t1 = registry.spawn("Expr".to_string());
        let t2 = registry.spawn("Expr".to_string());
        let t3 = registry.spawn("Expr".to_string());
        let t4 = registry.spawn("Expr".to_string());

        // Set different priorities
        registry.get_mut(t1).expect("t1").priority = 0; // lowest
        registry.get_mut(t2).expect("t2").priority = 3; // highest
        registry.get_mut(t3).expect("t3").priority = 1;
        registry.get_mut(t4).expect("t4").priority = 2;

        // Verify priority ordering
        assert!(registry.get(t2).expect("t2").priority > registry.get(t1).expect("t1").priority);
        assert!(registry.get(t2).expect("t2").priority > registry.get(t4).expect("t4").priority);
        assert!(registry.get(t4).expect("t4").priority > registry.get(t3).expect("t3").priority);
    }

    /// IT-3: Full lifecycle: spawn → run → suspend → resume → complete.
    #[test]
    fn test_integration_full_lifecycle() {
        let registry = GreenThreadRegistry::new();
        let tid = registry.spawn("Proc".to_string());

        // Ready → Running (direct state assignment, as per existing test pattern)
        registry.get_mut(tid).expect("thread").state = CekThreadState::Running;
        assert_eq!(registry.get(tid).expect("t").state, CekThreadState::Running);

        // Running → Suspended
        registry
            .get_mut(tid)
            .expect("thread")
            .suspend(vec![ChannelId(99)]);
        assert!(matches!(registry.get(tid).expect("t").state, CekThreadState::Suspended { .. }));
        assert!(!registry.get(tid).expect("t").is_runnable());

        // Suspended → Ready (resume)
        registry.get_mut(tid).expect("thread").resume();
        assert_eq!(registry.get(tid).expect("t").state, CekThreadState::Ready);
        assert!(registry.get(tid).expect("t").is_runnable());

        // Ready → Running → Completed
        registry.get_mut(tid).expect("thread").state = CekThreadState::Running;
        registry
            .get_mut(tid)
            .expect("thread")
            .complete("done".to_string());
        assert!(registry.get(tid).expect("t").is_terminal());
    }

    /// IT-4: Verify continuation stack and env tracking across operations.
    #[test]
    fn test_integration_stack_and_env_tracking() {
        let registry = GreenThreadRegistry::new();
        let tid = registry.spawn("Proc".to_string());

        // Push continuation frames
        {
            let mut thread = registry.get_mut(tid).expect("thread");
            thread.push_continuation(test_frame("Frame1"));
            thread.push_continuation(test_frame("Frame2"));
            assert_eq!(thread.stack_depth(), 2);
        }

        // Pop frame (LIFO)
        {
            let mut thread = registry.get_mut(tid).expect("thread");
            let frame = thread.pop_continuation();
            assert_eq!(frame, Some(test_frame("Frame2")));
            assert_eq!(thread.stack_depth(), 1);
        }

        // Env operations
        {
            let mut thread = registry.get_mut(tid).expect("thread");
            thread.set_env("Proc", "x", "val_x".to_string());
            thread.set_env("Proc", "y", "val_y".to_string());
            assert_eq!(thread.env_size(), 2);
            assert_eq!(thread.get_env("Proc", "x"), Some(&"val_x".to_string()));
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GS-1 / GS-2 Tests: CEK Integration and Parallel Fork
    // ══════════════════════════════════════════════════════════════════════════

    /// GS-1: Create a green thread via with_control() and verify CEK fields.
    #[test]
    fn test_green_thread_with_control() {
        let id = GreenThreadId(10);
        let thread = GreenThread::with_control(id, "Expr", "1 + 2".to_string());

        assert_eq!(thread.id, id);
        assert_eq!(thread.control, "1 + 2");
        assert_eq!(thread.category, "Expr");
        assert_eq!(thread.eval_state, EvalState::Ready);
        assert!(thread.eval_bindings.is_empty());
        assert!(thread.memo_cache.is_empty());
        assert_eq!(thread.step_count, 0);
        assert_eq!(thread.step_limit, 10_000);
        assert!(thread.pending_fork.is_none());
        assert_eq!(thread.state, CekThreadState::Ready);
    }

    /// GS-1: Create a green thread with control and environment.
    #[test]
    fn test_green_thread_with_control_and_env() {
        let mut env = im::HashMap::new();
        env = env.update("x".to_string(), "42".to_string());
        env = env.update("y".to_string(), "99".to_string());

        let thread = GreenThread::with_control_and_string_env(
            GreenThreadId(5),
            "Proc",
            "x + y".to_string(),
            env.clone(),
        );

        assert_eq!(thread.control, "x + y");
        // Bindings now hold StoreAddr; resolve through local store to verify values.
        let x_addr = thread.eval_bindings.get("x").expect("x binding missing");
        let y_addr = thread.eval_bindings.get("y").expect("y binding missing");
        if let StoreAddr::Local(id) = x_addr {
            assert_eq!(thread.local_store.get(*id), Some(&StoreValue::Simple("42".to_string())));
        } else {
            panic!("expected StoreAddr::Local for x");
        }
        if let StoreAddr::Local(id) = y_addr {
            assert_eq!(thread.local_store.get(*id), Some(&StoreValue::Simple("99".to_string())));
        } else {
            panic!("expected StoreAddr::Local for y");
        }
        assert_eq!(thread.eval_bindings.len(), 2);
    }

    /// GS-1: cek_step drives a thread with no continuation to Accepted.
    #[test]
    fn test_green_thread_cek_step_accepts() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "42".to_string());

        // Step 1: Ready -> Reducing
        let r1 = thread.cek_step();
        assert_eq!(r1, StepResult::Continue);
        assert_eq!(thread.eval_state, EvalState::Reducing);

        // Step 2: Reducing with empty stack, no cache -> Accepted
        let r2 = thread.cek_step();
        assert_eq!(r2, StepResult::Accepted);
        assert_eq!(thread.eval_state, EvalState::Accepted);
        assert_eq!(thread.control, "42");
    }

    /// GS-1: run_quantum with CEK control term completes.
    #[test]
    fn test_run_quantum_cek_completes() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "42".to_string());
        thread.state = CekThreadState::Running;

        let result = thread.run_quantum(100);
        assert_eq!(result, QuantumResult::Completed { result: "42".to_string() });
        assert!(thread.is_terminal());
    }

    /// GS-1: run_quantum yields when quantum is too small for full evaluation.
    #[test]
    fn test_run_quantum_cek_yields() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "term".to_string());
        thread.state = CekThreadState::Running;
        // Push several continuation frames so evaluation doesn't terminate quickly
        for i in 0..20 {
            thread.push_continuation(test_frame(&format!("frame_{}", i)));
        }

        // Quantum of 1: should yield (can't finish in 1 step with deep stack)
        let result = thread.run_quantum(1);
        assert_eq!(result, QuantumResult::Yielded);
        assert_eq!(thread.state, CekThreadState::Running);
    }

    /// GS-1: fork shares memo_cache, child sees parent's cached results.
    #[test]
    fn test_fork_shares_memo_cache() {
        let mut parent = GreenThread::with_control(GreenThreadId(0), "Expr", "a".to_string());
        parent.memo_cache = parent
            .memo_cache
            .update("a".to_string(), "cached_a".to_string());

        let child = parent.fork(GreenThreadId(1), "Expr");

        // Child should see parent's memo cache entry
        assert_eq!(child.memo_cache.get("a"), Some(&"cached_a".to_string()));

        // Mutating child's cache doesn't affect parent
        let mut child = child;
        child.memo_cache = child
            .memo_cache
            .update("b".to_string(), "cached_b".to_string());
        assert!(parent.memo_cache.get("b").is_none());
        assert_eq!(parent.memo_cache.len(), 1);
        assert_eq!(child.memo_cache.len(), 2);
    }

    /// GS-1: fork produces independent eval_state — parent and child diverge.
    #[test]
    fn test_fork_independent_eval_state() {
        let mut parent = GreenThread::with_control(GreenThreadId(0), "Expr", "term".to_string());
        parent.eval_state = EvalState::Reducing;

        let child = parent.fork(GreenThreadId(1), "Expr");

        // Child starts with Ready eval_state (not parent's Reducing)
        assert_eq!(child.eval_state, EvalState::Ready);
        assert_eq!(parent.eval_state, EvalState::Reducing);

        // Mutating child eval_state doesn't affect parent
        let mut child = child;
        child.eval_state = EvalState::Ascending;
        assert_eq!(parent.eval_state, EvalState::Reducing);
    }

    /// GS-2: Parallel frame with remaining sub-terms triggers pending_fork.
    #[test]
    fn test_parallel_frame_triggers_fork() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Proc", "P".to_string());
        // Set to Ascending state and push a Parallel frame with remaining work
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::Parallel {
            remaining: vec!["Q".to_string(), "R".to_string()],
            completed: vec!["S".to_string()],
        });

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);

        // pending_fork should be set with the remaining sub-terms
        assert!(thread.pending_fork.is_some());
        let fork_terms = thread
            .pending_fork
            .as_ref()
            .expect("pending_fork should be set");
        assert_eq!(fork_terms, &vec!["Q".to_string(), "R".to_string()]);

        // Completed list should include our control term "P"
        // The Parallel frame pushed back should have empty remaining and updated completed
        let frame = thread
            .pop_continuation()
            .expect("should have stashed frame");
        match frame {
            EvalFrame::Parallel { remaining, completed } => {
                assert!(remaining.is_empty());
                assert_eq!(completed, vec!["S".to_string(), "P".to_string()]);
            },
            other => panic!("expected Parallel frame, got {:?}", other),
        }
    }

    /// GS-2: take_pending_fork() returns and clears the pending fork.
    #[test]
    fn test_take_pending_fork() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        assert!(thread.take_pending_fork().is_none());

        thread.pending_fork = Some(vec!["A".to_string(), "B".to_string()]);
        let taken = thread.take_pending_fork();
        assert_eq!(taken, Some(vec!["A".to_string(), "B".to_string()]));
        // Should be cleared after take
        assert!(thread.pending_fork.is_none());
        assert!(thread.take_pending_fork().is_none());
    }

    /// GS-1: BinOp frame ascend reconstructs expression correctly.
    #[test]
    fn test_cek_step_binop_ascend() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "2".to_string());
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::BinOp {
            operator: "+".to_string(),
            lhs_display: "1".to_string(),
        });

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.control, "(1 + 2)");
        assert_eq!(thread.eval_state, EvalState::Reducing);
    }

    /// GS-1: LetBody frame ascend binds variable in eval_bindings.
    #[test]
    fn test_cek_step_let_body_binds() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "42".to_string());
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::LetBody {
            var_name: "x".to_string(),
            body_display: "x + 1".to_string(),
        });

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.control, "x + 1");
        // cek_step allocates the control value in local_store and binds var → StoreAddr.
        let x_addr = thread
            .eval_bindings
            .get("x")
            .expect("x binding missing after LetBody");
        if let StoreAddr::Local(id) = x_addr {
            assert_eq!(thread.local_store.get(*id), Some(&StoreValue::Simple("42".to_string())));
        } else {
            panic!("expected StoreAddr::Local for x");
        }
        assert_eq!(thread.eval_state, EvalState::Reducing);
    }

    /// GS-1: Memo cache hit during Reducing state returns cached result.
    #[test]
    fn test_cek_step_memo_cache_hit() {
        let mut thread =
            GreenThread::with_control(GreenThreadId(0), "Expr", "cached_term".to_string());
        thread.memo_cache = thread
            .memo_cache
            .update("cached_term".to_string(), "result".to_string());
        thread.eval_state = EvalState::Reducing;

        // No continuation → should accept with cached result
        let result = thread.cek_step();
        assert_eq!(result, StepResult::Accepted);
        assert_eq!(thread.control, "result");
        assert_eq!(thread.eval_state, EvalState::Accepted);
    }

    /// GS-1: Memo cache hit with continuation → ascend.
    #[test]
    fn test_cek_step_memo_cache_hit_with_continuation() {
        let mut thread =
            GreenThread::with_control(GreenThreadId(0), "Expr", "cached_term".to_string());
        thread.memo_cache = thread
            .memo_cache
            .update("cached_term".to_string(), "result".to_string());
        thread.eval_state = EvalState::Reducing;
        thread.push_continuation(test_frame("some_frame"));

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.control, "result");
        assert_eq!(thread.eval_state, EvalState::Ascending);
    }

    /// GS-1: Step limit triggers failure via run_quantum.
    #[test]
    fn test_run_quantum_cek_step_limit() {
        let mut thread =
            GreenThread::with_control(GreenThreadId(0), "Expr", "divergent".to_string());
        thread.state = CekThreadState::Running;
        thread.step_limit = 5;
        // Push enough frames to create a cycle
        for i in 0..100 {
            thread.push_continuation(test_frame(&format!("r{}", i)));
        }

        let result = thread.run_quantum(1000);
        match result {
            QuantumResult::Failed { error } => {
                assert!(error.contains("step limit exceeded"), "error was: {}", error);
            },
            other => panic!("expected Failed, got {:?}", other),
        }
    }

    /// GS-1: UnaryOp frame ascend reconstructs expression.
    #[test]
    fn test_cek_step_unary_ascend() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "5".to_string());
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::UnaryOp { operator: "-".to_string() });

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.control, "(- 5)");
        assert_eq!(thread.eval_state, EvalState::Reducing);
    }

    /// GS-2: Parallel frame with no remaining → reconstruct parallel term.
    #[test]
    fn test_cek_step_parallel_all_complete() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Proc", "P".to_string());
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::Parallel {
            remaining: vec![],
            completed: vec!["Q".to_string()],
        });

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.control, "(Q | P)");
        assert!(thread.pending_fork.is_none());
    }

    /// GS-2: run_quantum detects pending_fork and returns Forked.
    #[test]
    fn test_run_quantum_cek_fork() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Proc", "P".to_string());
        thread.state = CekThreadState::Running;
        thread.eval_state = EvalState::Ascending;
        thread.push_continuation(EvalFrame::Parallel {
            remaining: vec!["Q".to_string(), "R".to_string()],
            completed: vec![],
        });

        let result = thread.run_quantum(100);
        match result {
            QuantumResult::Forked { children } => {
                assert_eq!(children, vec!["Q".to_string(), "R".to_string()]);
            },
            other => panic!("expected Forked, got {:?}", other),
        }
        assert!(matches!(thread.state, CekThreadState::Forked { .. }));
    }

    /// GS-1: cek_step is idempotent in terminal Accepted state.
    #[test]
    fn test_cek_step_terminal_idempotent() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "42".to_string());
        thread.eval_state = EvalState::Accepted;

        let r1 = thread.cek_step();
        assert_eq!(r1, StepResult::Accepted);
        let r2 = thread.cek_step();
        assert_eq!(r2, StepResult::Accepted);
        assert_eq!(thread.eval_state, EvalState::Accepted);
    }

    /// GS-1: cek_step is idempotent in terminal Error state.
    #[test]
    fn test_cek_step_error_idempotent() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "x".to_string());
        thread.eval_state = EvalState::Error { message: "test error".to_string() };

        let r = thread.cek_step();
        match r {
            StepResult::Error { message } => assert_eq!(message, "test error"),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    /// GS-1: Descending state transitions to Reducing.
    #[test]
    fn test_cek_step_descending() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "sub".to_string());
        thread.eval_state = EvalState::Descending;

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.eval_state, EvalState::Reducing);
    }

    /// GS-1: Ascending with empty stack → Accepted.
    #[test]
    fn test_cek_step_ascending_empty_stack() {
        let mut thread = GreenThread::with_control(GreenThreadId(0), "Expr", "done".to_string());
        thread.eval_state = EvalState::Ascending;
        // No continuation frames

        let result = thread.cek_step();
        assert_eq!(result, StepResult::Continue);
        assert_eq!(thread.eval_state, EvalState::Accepted);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GS-5: Channel send tracking tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_record_channel_send() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        assert!(thread.channel_sends.is_empty());

        thread.record_channel_send(ChannelId(1));
        thread.record_channel_send(ChannelId(5));
        assert_eq!(thread.channel_sends.len(), 2);
        assert_eq!(thread.channel_sends[0], ChannelId(1));
        assert_eq!(thread.channel_sends[1], ChannelId(5));
    }

    #[test]
    fn test_take_channel_sends_drains() {
        let mut thread = GreenThread::new(GreenThreadId(0), "Proc");
        thread.record_channel_send(ChannelId(10));
        thread.record_channel_send(ChannelId(20));

        let sends = thread.take_channel_sends();
        assert_eq!(sends, vec![ChannelId(10), ChannelId(20)]);
        // Drained — second call returns empty.
        assert!(thread.take_channel_sends().is_empty());
    }

    #[test]
    fn test_fork_does_not_inherit_channel_sends() {
        let mut parent = GreenThread::new(GreenThreadId(0), "Proc");
        parent.record_channel_send(ChannelId(99));

        let child = parent.fork(GreenThreadId(1), "Proc");
        // Child starts with empty channel_sends (not inherited).
        assert!(child.channel_sends.is_empty());
        // Parent still has its sends.
        assert_eq!(parent.channel_sends.len(), 1);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GS-6: Comprehensive Test Suite — Property-Based Tests
    // ══════════════════════════════════════════════════════════════════════════

    mod proptest_gs6 {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// GS-6: Fork N threads, mutate each evaluator's env, verify parent unchanged.
            #[test]
            fn prop_fork_evaluator_independence(
                n_children in 1usize..8,
                parent_keys in proptest::collection::vec("[a-z]{1,4}", 1..8),
                parent_vals in proptest::collection::vec("[0-9]{1,4}", 1..8),
            ) {
                let n = parent_keys.len().min(parent_vals.len());
                let mut parent = GreenThread::with_control(
                    GreenThreadId(0), "Proc", "parent_term".to_string(),
                );
                for i in 0..n {
                    let addr_id = parent.local_store.alloc_with(
                        StoreValue::Simple(parent_vals[i].clone()),
                    );
                    parent.eval_bindings = parent.eval_bindings.update(
                        parent_keys[i].clone(),
                        StoreAddr::Local(addr_id),
                    );
                }
                let parent_bindings_len = parent.eval_bindings.len();
                let parent_memo_len = parent.memo_cache.len();

                for c in 0..n_children {
                    let mut child = parent.fork(
                        GreenThreadId((c + 1) as u64),
                        "Proc",
                    );
                    // Mutate child's env.
                    let child_addr_id = child.local_store.alloc_with(
                        StoreValue::Simple(format!("val_{}", c)),
                    );
                    child.eval_bindings = child.eval_bindings.update(
                        format!("child_{}", c),
                        StoreAddr::Local(child_addr_id),
                    );
                    child.memo_cache = child.memo_cache.update(
                        format!("memo_{}", c),
                        format!("res_{}", c),
                    );
                }

                // Parent must be unchanged.
                prop_assert_eq!(
                    parent.eval_bindings.len(), parent_bindings_len,
                    "parent eval_bindings must be unaffected by children"
                );
                prop_assert_eq!(
                    parent.memo_cache.len(), parent_memo_len,
                    "parent memo_cache must be unaffected by children"
                );
            }

            /// GS-6: run_quantum(N) performs at most N evaluator steps.
            #[test]
            fn prop_quantum_step_count_bounded(
                quantum in 1usize..256,
            ) {
                let mut thread = GreenThread::with_control(
                    GreenThreadId(0), "Expr", "term".to_string(),
                );
                thread.state = CekThreadState::Running;
                let step_before = thread.step_count;
                let _ = thread.run_quantum(quantum);
                let steps_taken = thread.step_count - step_before;
                prop_assert!(
                    steps_taken <= quantum,
                    "steps_taken ({}) must be <= quantum ({})",
                    steps_taken, quantum
                );
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GS-6: Stress Tests
    // ══════════════════════════════════════════════════════════════════════════

    /// GS-6: Stress — 1000 green threads with trivial work, all complete.
    #[test]
    fn stress_1000_threads_complete() {
        let registry = GreenThreadRegistry::new();
        let mut completed = 0;

        for _ in 0..1000 {
            let tid = registry.spawn("Expr".to_string());
            let mut thread = registry.get_mut(tid).expect("thread exists");
            thread.state = CekThreadState::Running;
            // Empty stacks and no control term complete immediately.
            match thread.run_quantum(10) {
                QuantumResult::Completed { .. } => completed += 1,
                other => panic!("expected Completed, got {:?}", other),
            }
        }
        assert_eq!(completed, 1000);
        assert_eq!(registry.thread_count(), 1000);
    }

    /// GS-6: Stress — fork bomb with budget limit.
    #[test]
    fn stress_fork_bomb_budget_limit() {
        let max_forks = 100;
        let registry = GreenThreadRegistry::new();
        let root = registry.spawn("Proc".to_string());

        let mut total_forked = 0;
        let mut queue = vec![root];

        while let Some(tid) = queue.pop() {
            if total_forked >= max_forks {
                break;
            }
            // Fork 2 children from each thread.
            for _ in 0..2 {
                if total_forked >= max_forks {
                    break;
                }
                if let Some(child_id) = registry.spawn_child(tid, "Proc".to_string()) {
                    queue.push(child_id);
                    total_forked += 1;
                }
            }
        }

        assert_eq!(total_forked, max_forks);
        // All threads should exist in registry.
        assert_eq!(registry.thread_count(), max_forks + 1); // +1 for root
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GS-6: Integration Tests — E2E
    // ══════════════════════════════════════════════════════════════════════════

    /// GS-6: E2E — Parallel composition forks two threads, both complete.
    #[test]
    fn test_e2e_parallel_composition() {
        let registry = GreenThreadRegistry::new();
        let root_id = registry.spawn("Proc".to_string());

        // Set up root with a Parallel frame that has 2 remaining sub-terms.
        {
            let mut root = registry.get_mut(root_id).expect("root");
            root.control = "P".to_string();
            root.eval_state = EvalState::Ascending;
            root.continuation.push_back(EvalFrame::Parallel {
                remaining: vec!["Q".to_string()],
                completed: vec![],
            });
            root.state = CekThreadState::Running;
        }

        // Run quantum — should trigger fork.
        let result = {
            let mut root = registry.get_mut(root_id).expect("root");
            root.run_quantum(100)
        };

        match result {
            QuantumResult::Forked { children } => {
                assert_eq!(children.len(), 1, "should fork 1 remaining sub-term");
                assert_eq!(children[0], "Q");

                // Spawn and run the child.
                let child_id = registry
                    .spawn_child(root_id, "Proc".to_string())
                    .expect("fork child");
                {
                    let mut child = registry.get_mut(child_id).expect("child");
                    child.control = "Q".to_string();
                    child.eval_state = EvalState::Ready;
                    child.state = CekThreadState::Running;
                    let child_result = child.run_quantum(100);
                    assert!(
                        matches!(child_result, QuantumResult::Completed { .. }),
                        "child should complete"
                    );
                }
            },
            other => panic!("expected Forked, got {:?}", other),
        }
    }

    /// GS-6: E2E — Channel send records activity for event-driven wake.
    #[test]
    fn test_e2e_channel_send_tracking() {
        let mut thread =
            GreenThread::with_control(GreenThreadId(0), "Proc", "send_term".to_string());
        // Simulate channel sends during evaluation.
        thread.record_channel_send(ChannelId(1));
        thread.record_channel_send(ChannelId(2));

        let sends = thread.take_channel_sends();
        assert_eq!(sends.len(), 2);
        assert_eq!(sends[0], ChannelId(1));
        assert_eq!(sends[1], ChannelId(2));
    }
}
