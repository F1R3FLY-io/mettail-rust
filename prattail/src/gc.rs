//! Garbage Collection Infrastructure for the CESK Store.
//!
//! Provides configurable GC strategies for the CESK machine's store component:
//!
//! | Strategy | Mechanism | Use Case |
//! |----------|-----------|----------|
//! | `None` | No GC; store grows monotonically | Short-lived evals (step-limited) |
//! | `RefCount` | Reference counting + async dealloc | Closures, let-bindings (no cycles) |
//! | `MarkSweep` | Async snapshot-based mark-sweep | Channels, tuplespace (shared state) |
//!
//! ## Architecture
//!
//! ```text
//!   Eval Thread                    GC Background Thread(s)
//!   ┌──────────┐                  ┌──────────────────────┐
//!   │ inc_ref() │                  │                      │
//!   │ dec_ref() │──dead addrs───▶ │  Dealloc Worker      │
//!   │ (inline)  │                  │  (batch drain)       │
//!   │           │◀──removals─────│                      │
//!   └──────────┘                  └──────────────────────┘
//!        │                              ▲
//!        │ quantum yield (safe point)   │
//!        │ apply pending removals       │
//!        ▼                              │
//!   ┌──────────┐  snapshot ──────▶┌──────────────────────┐
//!   │Coordinator│                  │  Mark-Sweep Worker   │
//!   │(ParkIdle) │◀── GcResponse ─│  (iterative worklist)│
//!   └──────────┘                  └──────────────────────┘
//! ```
//!
//! ## GC Safe Points
//!
//! GC operations occur **only at quantum boundaries** (when a green thread
//! yields). No mid-quantum GC interrupts. No stop-the-world pauses.
//!
//! ## Adaptive Backpressure
//!
//! The GC cron monitor computes memory pressure from allocation rate +
//! committed bytes. Pressure drives adaptive quantum sizing: higher pressure
//! → smaller quanta → more frequent yields → more GC safe points.
//!
//! ## References
//!
//! - Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*, §4.
//! - Earl, C. et al. (2013). Introspective Pushdown Analysis. *JFP*, §4–7.
//! - MeTTaTron GC infrastructure: `gc_allocator.rs`, `gc_thread.rs`, `gc_pool.rs`,
//!   `gc_cron.rs`, `task_scheduler.rs`.

use std::collections::{HashMap, HashSet};

use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};
use std::sync::Arc;

use crate::cesk_store::{StoreAddr, StoreValue};

use crate::cesk_store::{GcResponse, GcSnapshot};
use crate::channel::ChannelId;

// ══════════════════════════════════════════════════════════════════════════════
// GC Strategy Configuration
// ══════════════════════════════════════════════════════════════════════════════

/// Configurable garbage collection strategy for the CESK store.
///
/// Selected at evaluator construction time and immutable thereafter.
/// Each strategy offers different trade-offs:
///
/// | Strategy | Overhead | Cycle Detection | Async | Best For |
/// |----------|----------|-----------------|-------|----------|
/// | `None` | Zero | N/A | N/A | Short evals, step-limited |
/// | `RefCount` | Low | No (not needed) | Yes | Lambda calculus, closures |
/// | `MarkSweep` | Medium | Yes | Yes | Rho-calculus, channels |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GcStrategy {
    /// No garbage collection. The store grows monotonically until the evaluator
    /// terminates. Appropriate when evaluation is bounded by a step limit
    /// (e.g., Calculator language with `step_limit = 10_000`).
    None,

    /// Reference counting with asynchronous background deallocation.
    ///
    /// - `inc_ref()` / `dec_ref()` called inline (fast path, single atomic op)
    /// - When refcount hits 0: addr pushed to lock-free dealloc queue
    /// - Background thread drains queue in batches, sends removal list back
    /// - Eval thread applies removals at next quantum boundary (GC safe point)
    ///
    /// Does not detect cycles. This is acceptable because cycles don't arise
    /// in the lambda calculus or rho-calculus: closures capture their
    /// environment at creation time (snapshot), and channels are acyclic
    /// by construction (names are globally unique).
    RefCount,

    /// Async snapshot-based mark-and-sweep (adapted from MeTTaTron).
    ///
    /// - Snapshot constructed at coordinator idle (`ParkIdle` state)
    /// - GC worker thread runs iterative mark from roots (no recursion)
    /// - Sweep collects unreachable addresses
    /// - Epoch-based TOCTOU prevention: addrs allocated after snapshot exempt
    ///
    /// Best for languages with shared mutable state (Rho-calculus channels,
    /// tuplespace entries) where reference counting alone is insufficient.
    MarkSweep,
}

impl Default for GcStrategy {
    fn default() -> Self {
        GcStrategy::RefCount
    }
}

impl std::fmt::Display for GcStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GcStrategy::None => write!(f, "None"),
            GcStrategy::RefCount => write!(f, "RefCount"),
            GcStrategy::MarkSweep => write!(f, "MarkSweep"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Backpressure Tiers — Adaptive quantum sizing
// ══════════════════════════════════════════════════════════════════════════════

/// Memory pressure tiers for adaptive quantum sizing.
///
/// The GC cron monitor computes pressure from allocation rate + committed
/// bytes. The scheduler reads the current tier to determine quantum size:
///
/// | Tier | Quantum | Trigger |
/// |------|---------|---------|
/// | `Normal` | 1000 steps | Default |
/// | `Light` | 750 steps | Alloc rate > 50% threshold |
/// | `Medium` | 500 steps | Alloc rate > 75% threshold |
/// | `Heavy` | 250 steps | Committed bytes > GC threshold |
///
/// Tier transitions use EMA smoothing to avoid oscillation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum BackpressureTier {
    /// No memory pressure. Full quantum (1000 steps).
    Normal = 0,
    /// Light pressure. Reduced quantum (750 steps).
    Light = 1,
    /// Medium pressure. Half quantum (500 steps).
    Medium = 2,
    /// Heavy pressure. Minimum quantum (250 steps).
    Heavy = 3,
}

impl BackpressureTier {
    /// The quantum size (in CEK steps) for this tier.
    pub fn quantum_size(&self) -> usize {
        match self {
            BackpressureTier::Normal => 1000,
            BackpressureTier::Light => 750,
            BackpressureTier::Medium => 500,
            BackpressureTier::Heavy => 250,
        }
    }

    /// Convert from a `u8` value (for atomic loads).
    pub fn from_u8(val: u8) -> Self {
        match val {
            0 => BackpressureTier::Normal,
            1 => BackpressureTier::Light,
            2 => BackpressureTier::Medium,
            _ => BackpressureTier::Heavy,
        }
    }
}

impl Default for BackpressureTier {
    fn default() -> Self {
        BackpressureTier::Normal
    }
}

impl std::fmt::Display for BackpressureTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BackpressureTier::Normal => write!(f, "Normal(1000)"),
            BackpressureTier::Light => write!(f, "Light(750)"),
            BackpressureTier::Medium => write!(f, "Medium(500)"),
            BackpressureTier::Heavy => write!(f, "Heavy(250)"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RefCountGc — Reference counting with async deallocation
// ══════════════════════════════════════════════════════════════════════════════

/// Reference counting GC for the local CESK store.
///
/// Maintains a companion `refcounts` map alongside the store. When a binding
/// is created, `inc_ref()` is called; when removed, `dec_ref()`. When the
/// count reaches zero, the address is enqueued for background deallocation.
///
/// ## Async Deallocation Protocol
///
/// 1. `dec_ref(addr)` hits zero → push addr to `dead_addrs` queue
/// 2. Background thread (when `green-threads` active) drains in batches
/// 3. For `ChannelRef` deaths: calls `ChannelMap.dec_ref(ch_id)`
/// 4. Sends removal list back via response channel
/// 5. Eval thread applies removals at next quantum boundary
///
/// In standalone mode (no `green-threads`), dead addrs accumulate in
/// `pending_removals` and are applied synchronously.
#[derive(Debug, Clone)]
pub struct RefCountGc {
    /// Per-address reference counts.
    refcounts: HashMap<u64, usize>,
    /// Addresses whose refcount has reached zero, pending removal.
    /// Applied at the next GC safe point (quantum boundary).
    pending_removals: Vec<u64>,
    /// Channel IDs from dead `ChannelRef` values, pending lifecycle cleanup.
    pending_channel_deaths: Vec<ChannelId>,
}

impl RefCountGc {
    /// Create a new reference counting GC with empty state.
    pub fn new() -> Self {
        Self {
            refcounts: HashMap::new(),
            pending_removals: Vec::new(),
            pending_channel_deaths: Vec::new(),
        }
    }

    /// Increment the reference count for an address.
    ///
    /// Called when a variable is bound to a store address.
    #[inline]
    pub fn inc_ref(&mut self, addr: u64) {
        *self.refcounts.entry(addr).or_insert(0) += 1;
    }

    /// Decrement the reference count for an address.
    ///
    /// If the count reaches zero, the address is added to `pending_removals`.
    /// If the dead value is a `ChannelRef`, the channel ID is also recorded.
    ///
    /// Returns the new reference count.
    #[inline]
    pub fn dec_ref(&mut self, addr: u64) -> usize {
        if let Some(count) = self.refcounts.get_mut(&addr) {
            *count = count.saturating_sub(1);
            if *count == 0 {
                self.refcounts.remove(&addr);
                self.pending_removals.push(addr);
                return 0;
            }
            return *count;
        }
        0
    }

    /// Decrement and record channel death if the value was a `ChannelRef`.
    ///
    /// This variant is used when the caller knows the value type and can
    /// extract the `ChannelId` for lifecycle cleanup.
    pub fn dec_ref_with_channel(&mut self, addr: u64, channel_id: Option<ChannelId>) -> usize {
        let new_count = self.dec_ref(addr);
        if new_count == 0 {
            if let Some(ch_id) = channel_id {
                self.pending_channel_deaths.push(ch_id);
            }
        }
        new_count
    }

    /// Get the current reference count for an address.
    pub fn ref_count(&self, addr: u64) -> usize {
        self.refcounts.get(&addr).copied().unwrap_or(0)
    }

    /// Take the pending removal list (drain it).
    ///
    /// Called at GC safe points to collect dead addresses for store cleanup.
    pub fn take_pending_removals(&mut self) -> Vec<u64> {
        std::mem::take(&mut self.pending_removals)
    }

    /// Whether there are pending removals waiting to be applied.
    #[inline]
    pub fn has_pending_removals(&self) -> bool {
        !self.pending_removals.is_empty()
    }

    /// Number of pending removals.
    #[inline]
    pub fn pending_removal_count(&self) -> usize {
        self.pending_removals.len()
    }

    /// Take the pending channel deaths (drain them).
    pub fn take_pending_channel_deaths(&mut self) -> Vec<ChannelId> {
        std::mem::take(&mut self.pending_channel_deaths)
    }

    /// Number of addresses currently tracked (with non-zero refcount).
    pub fn tracked_count(&self) -> usize {
        self.refcounts.len()
    }

    /// Clear all tracking state.
    pub fn clear(&mut self) {
        self.refcounts.clear();
        self.pending_removals.clear();
        self.pending_channel_deaths.clear();
    }
}

impl Default for RefCountGc {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// MarkSweepGc — Async snapshot-based mark-and-sweep
// ══════════════════════════════════════════════════════════════════════════════

/// Mark-and-sweep GC for the global CESK store.
///
/// Operates on frozen [`GcSnapshot`] objects, never touching the live store
/// directly. The mark phase traces from roots using an iterative worklist;
/// the sweep phase collects unreachable addresses.
///
/// ## Protocol (adapted from MeTTaTron `gc_thread.rs`)
///
/// 1. **Snapshot**: Coordinator constructs `GcSnapshot` at `ParkIdle`
/// 2. **Mark**: Iterative worklist from roots (follows closure env_snapshots)
/// 3. **Sweep**: Collect all addresses not in the marked set
/// 4. **Response**: `GcResponse { dead_addrs, dead_channel_refs, epoch }`
/// 5. **Apply**: Coordinator filters by epoch, removes dead addrs
///
/// ## Epoch-Based TOCTOU Prevention
///
/// The global store maintains an epoch counter incremented on each `alloc()`.
/// The snapshot captures the epoch at construction time. Any address allocated
/// after the snapshot epoch is exempt from collection — the mark phase
/// couldn't have seen it, so sweeping it would be unsound.
pub struct MarkSweepGc {
    /// Configuration: minimum allocation rate to trigger GC (allocs/check).
    pub alloc_rate_threshold: u64,
    /// Configuration: committed bytes threshold to trigger GC.
    pub committed_bytes_threshold: usize,
}

impl MarkSweepGc {
    /// Create a mark-sweep GC with default thresholds.
    pub fn new() -> Self {
        Self {
            alloc_rate_threshold: 1000,
            committed_bytes_threshold: 10 * 1024 * 1024, // 10 MB
        }
    }

    /// Create with custom thresholds.
    pub fn with_thresholds(alloc_rate_threshold: u64, committed_bytes_threshold: usize) -> Self {
        Self {
            alloc_rate_threshold,
            committed_bytes_threshold,
        }
    }

    /// Execute the mark phase on a snapshot.
    ///
    /// Starting from the root set, traces all reachable addresses by following
    /// `StoreValue::Closure.env_snapshot` chains. Uses an iterative worklist
    /// (no recursion) to avoid stack overflow on deeply-nested closures.
    ///
    /// Returns the set of live (reachable) addresses.
    pub fn mark(&self, snapshot: &GcSnapshot) -> HashSet<u64> {
        let mut live = HashSet::new();
        let mut worklist: Vec<u64> = snapshot.roots.clone();

        while let Some(addr) = worklist.pop() {
            if !live.insert(addr) {
                continue; // Already visited
            }

            // Follow references within the value at this address
            if let Some(value) = snapshot.store_cells.get(&addr) {
                Self::collect_referenced_addrs(value, &mut worklist);
            }
        }

        live
    }

    /// Execute the sweep phase: collect addresses not in the live set.
    ///
    /// Returns the dead addresses and any channel IDs from dead `ChannelRef` values.
    pub fn sweep(&self, snapshot: &GcSnapshot, live: &HashSet<u64>) -> GcResponse {
        let mut dead_addrs = Vec::new();
        let mut dead_channel_refs = Vec::new();

        for (addr, value) in &snapshot.store_cells {
            if !live.contains(addr) {
                dead_addrs.push(*addr);
                if let StoreValue::ChannelRef(ch_id) = value {
                    dead_channel_refs.push(*ch_id);
                }
            }
        }

        GcResponse {
            dead_addrs,
            dead_channel_refs,
            snapshot_epoch: snapshot.epoch,
        }
    }

    /// Run a complete mark-sweep cycle on a snapshot.
    pub fn collect(&self, snapshot: &GcSnapshot) -> GcResponse {
        let live = self.mark(snapshot);
        self.sweep(snapshot, &live)
    }

    /// Collect addresses referenced by a store value.
    ///
    /// For closures, follows the `env_snapshot` to find global addresses.
    /// For simple values and void, there are no references.
    fn collect_referenced_addrs(value: &StoreValue, worklist: &mut Vec<u64>) {
        match value {
            StoreValue::Closure { env_snapshot, .. } => {
                for addr in env_snapshot.values() {
                    if let StoreAddr::Global(id) = addr {
                        worklist.push(*id);
                    }
                }
            }
            // These variants contain no store address references
            StoreValue::Simple(_)
            | StoreValue::Void
            | StoreValue::Relation { .. }
            | StoreValue::Constraint { .. }
            | StoreValue::RewriteRule { .. }
            | StoreValue::EClass { .. } => {}
            StoreValue::ChannelRef(_) => {}
        }
    }
}

impl Default for MarkSweepGc {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for MarkSweepGc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MarkSweepGc")
            .field("alloc_rate_threshold", &self.alloc_rate_threshold)
            .field("committed_bytes_threshold", &self.committed_bytes_threshold)
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GcCron — Reactive GC scheduler (adapted from MeTTaTron task_scheduler.rs)
// ══════════════════════════════════════════════════════════════════════════════

/// Reactive state machine for GC scheduling, adapted from MeTTaTron's
/// `CronStateMachine` pattern.
///
/// ## State Diagram
///
/// ```text
///   CheckEvents ──→ DrainChannel ──→ ExecutingTask ──→ Sleeping
///        ▲                                                │
///        └────────────────────────────────────────────────┘
///        │
///        ▼ (shutdown)
///   Terminated
/// ```
///
/// The cron monitor checks memory pressure at regular intervals and
/// triggers GC when thresholds are exceeded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GcCronState {
    /// Checking for pending events (allocation counters, timer expiry).
    CheckEvents,
    /// Draining the request channel for incoming GC requests.
    DrainChannel,
    /// Executing a GC task (snapshot construction or mark-sweep dispatch).
    ExecutingTask,
    /// Sleeping until the next check interval.
    Sleeping,
    /// Terminated — no further transitions.
    Terminated,
}

impl std::fmt::Display for GcCronState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GcCronState::CheckEvents => write!(f, "CheckEvents"),
            GcCronState::DrainChannel => write!(f, "DrainChannel"),
            GcCronState::ExecutingTask => write!(f, "ExecutingTask"),
            GcCronState::Sleeping => write!(f, "Sleeping"),
            GcCronState::Terminated => write!(f, "Terminated"),
        }
    }
}

/// Memory pressure monitor state for the GC cron.
///
/// Tracks allocation rates and computes backpressure tiers using
/// Exponential Moving Average (EMA) smoothing to avoid oscillation.
#[derive(Debug)]
pub struct GcMonitor {
    /// Previous allocation count (for rate computation).
    prev_alloc_count: u64,
    /// EMA of the allocation rate (allocs per check interval).
    ema_alloc_rate: f64,
    /// EMA smoothing factor (0.0–1.0). Higher = more responsive.
    ema_alpha: f64,
    /// Current backpressure tier (stored in atomic for cross-thread access).
    backpressure: Arc<AtomicU8>,
    /// Number of allocations counted at last GC trigger (for staleness check).
    last_gc_alloc_count: u64,
    /// Whether a GC cycle is currently in flight.
    gc_in_flight: bool,
}

impl GcMonitor {
    /// Create a new GC monitor with default EMA parameters.
    ///
    /// - `backpressure`: Shared atomic for cross-thread tier reads.
    pub fn new(backpressure: Arc<AtomicU8>) -> Self {
        Self {
            prev_alloc_count: 0,
            ema_alloc_rate: 0.0,
            ema_alpha: 0.3, // ~3 samples half-life
            backpressure,
            last_gc_alloc_count: 0,
            gc_in_flight: false,
        }
    }

    /// Update the monitor with the current allocation count.
    ///
    /// Computes the allocation rate since last check, updates the EMA,
    /// and adjusts the backpressure tier. Returns `true` if a GC cycle
    /// should be triggered.
    pub fn update(
        &mut self,
        current_alloc_count: u64,
        committed_bytes: usize,
        gc: &MarkSweepGc,
    ) -> bool {
        // Compute allocation rate since last check
        let delta = current_alloc_count.saturating_sub(self.prev_alloc_count);
        self.prev_alloc_count = current_alloc_count;

        // Update EMA
        self.ema_alloc_rate =
            self.ema_alpha * delta as f64 + (1.0 - self.ema_alpha) * self.ema_alloc_rate;

        // Compute backpressure tier
        let tier = if committed_bytes >= gc.committed_bytes_threshold {
            BackpressureTier::Heavy
        } else if self.ema_alloc_rate > gc.alloc_rate_threshold as f64 * 0.75 {
            BackpressureTier::Medium
        } else if self.ema_alloc_rate > gc.alloc_rate_threshold as f64 * 0.5 {
            BackpressureTier::Light
        } else {
            BackpressureTier::Normal
        };

        self.backpressure.store(tier as u8, Ordering::Relaxed);

        // Trigger GC if:
        // 1. Not already in flight
        // 2. Allocation rate exceeds threshold OR committed bytes exceed threshold
        // 3. Allocation count has advanced since last trigger (staleness check)
        let should_trigger = !self.gc_in_flight
            && current_alloc_count > self.last_gc_alloc_count
            && (self.ema_alloc_rate > gc.alloc_rate_threshold as f64
                || committed_bytes >= gc.committed_bytes_threshold);

        if should_trigger {
            self.gc_in_flight = true;
            self.last_gc_alloc_count = current_alloc_count;
        }

        should_trigger
    }

    /// Mark the current GC cycle as completed.
    pub fn gc_completed(&mut self) {
        self.gc_in_flight = false;
    }

    /// Get the current backpressure tier.
    pub fn current_tier(&self) -> BackpressureTier {
        BackpressureTier::from_u8(self.backpressure.load(Ordering::Relaxed))
    }

    /// Get the shared backpressure atomic for cross-thread access.
    pub fn backpressure_atomic(&self) -> Arc<AtomicU8> {
        Arc::clone(&self.backpressure)
    }

    /// Current EMA allocation rate.
    pub fn ema_alloc_rate(&self) -> f64 {
        self.ema_alloc_rate
    }

    /// Whether a GC cycle is currently in progress.
    pub fn is_gc_in_flight(&self) -> bool {
        self.gc_in_flight
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GcThread — Background GC thread (adapted from MeTTaTron gc_thread.rs)
// ══════════════════════════════════════════════════════════════════════════════

/// Request sent to the GC background thread.
#[derive(Debug)]
pub enum GcRequest {
    /// Perform a mark-sweep collection on the given snapshot.
    Collect(GcSnapshot),
    /// Shut down the GC thread.
    Shutdown,
}

/// Result of a non-blocking check for a GC response.
///
/// Tri-state result following MeTTaTron's `TryRecvGcResponse` pattern:
/// distinguishes "no response yet" from "channel disconnected".
#[derive(Debug)]
pub enum TryRecvGcResult {
    /// A GC response is available.
    Response(GcResponse),
    /// No response available yet (GC still in progress or no request sent).
    Empty,
    /// The GC thread has disconnected (shutdown or panic).
    Disconnected,
}

/// Background GC thread that processes mark-sweep requests.
///
/// Wraps request/response crossbeam channels and a join handle.
/// The GC thread blocks on the request channel, processes one request
/// at a time, and sends the response back.
///
/// ## Panic Resilience
///
/// Mark-sweep operations are wrapped in `std::panic::catch_unwind`.
/// If the mark or sweep phase panics, the GC thread logs the error
/// and continues processing the next request (it does not crash).
pub struct GcThread {
    /// Send GC requests to the background thread.
    request_tx: crossbeam_channel::Sender<GcRequest>,
    /// Receive GC responses from the background thread.
    response_rx: crossbeam_channel::Receiver<GcResponse>,
    /// Join handle for the background thread.
    handle: Option<std::thread::JoinHandle<()>>,
}

impl GcThread {
    /// Spawn a new GC background thread.
    ///
    /// The thread blocks on the request channel and processes
    /// `GcRequest::Collect` requests using the provided `MarkSweepGc`.
    pub fn spawn(gc: MarkSweepGc) -> Self {
        let (request_tx, request_rx) = crossbeam_channel::unbounded::<GcRequest>();
        let (response_tx, response_rx) = crossbeam_channel::unbounded::<GcResponse>();

        let handle = std::thread::Builder::new()
            .name("cesk-gc-worker".to_string())
            .spawn(move || {
                Self::gc_loop(&gc, &request_rx, &response_tx);
            })
            .expect("failed to spawn CESK GC thread");

        Self {
            request_tx,
            response_rx,
            handle: Some(handle),
        }
    }

    /// Submit a GC collection request (non-blocking).
    pub fn request_gc(&self, snapshot: GcSnapshot) {
        // Ignore send errors (thread may have shut down)
        let _ = self.request_tx.send(GcRequest::Collect(snapshot));
    }

    /// Try to receive a GC response (non-blocking).
    pub fn try_recv_response(&self) -> TryRecvGcResult {
        match self.response_rx.try_recv() {
            Ok(response) => TryRecvGcResult::Response(response),
            Err(crossbeam_channel::TryRecvError::Empty) => TryRecvGcResult::Empty,
            Err(crossbeam_channel::TryRecvError::Disconnected) => TryRecvGcResult::Disconnected,
        }
    }

    /// Receive a GC response, blocking until available.
    pub fn recv_response_blocking(&self) -> Option<GcResponse> {
        self.response_rx.recv().ok()
    }

    /// Request shutdown and wait for the thread to finish.
    pub fn shutdown(&mut self) {
        let _ = self.request_tx.send(GcRequest::Shutdown);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }

    /// The GC thread's main loop.
    fn gc_loop(
        gc: &MarkSweepGc,
        request_rx: &crossbeam_channel::Receiver<GcRequest>,
        response_tx: &crossbeam_channel::Sender<GcResponse>,
    ) {
        loop {
            match request_rx.recv() {
                Ok(GcRequest::Collect(snapshot)) => {
                    // Panic-resilient mark-sweep
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        gc.collect(&snapshot)
                    }));

                    match result {
                        Ok(response) => {
                            let _ = response_tx.send(response);
                        }
                        Err(_) => {
                            // Mark-sweep panicked — send empty response to unblock coordinator
                            let _ = response_tx.send(GcResponse {
                                dead_addrs: Vec::new(),
                                dead_channel_refs: Vec::new(),
                                snapshot_epoch: snapshot.epoch,
                            });
                        }
                    }
                }
                Ok(GcRequest::Shutdown) | Err(_) => {
                    break;
                }
            }
        }
    }
}

impl Drop for GcThread {
    fn drop(&mut self) {
        self.shutdown();
    }
}

impl std::fmt::Debug for GcThread {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GcThread")
            .field("alive", &self.handle.is_some())
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Live Locations — LL_σ function from AAM §4, Figure 7
// ══════════════════════════════════════════════════════════════════════════════

/// Compute live (reachable) store addresses from a root set.
///
/// Implements the `LL_σ` (live locations) function from Van Horn & Might's
/// "Abstracting Abstract Machines" (ICFP 2010, §4, Figure 7):
///
/// ```text
///   LL_σ(e, ρ) = LL_σ(ρ|fv(e))
///   LL_σ(ρ)    = rng(ρ)
///   LL_σ(fn(v, ρ, a)) = {a} ∪ LL_σ(v, ρ) ∪ LL_σ(σ(a))
///   LL_σ(ar(e, ρ, a)) = {a} ∪ LL_σ(e, ρ) ∪ LL_σ(σ(a))
/// ```
///
/// The function traces from the root set (environment addrs + continuation
/// frame addrs) through the store, following closure references.
///
/// This is used by:
/// - Concrete GC: mark phase root set computation
/// - Abstract GC: abstract store maps addrs to *sets* of values
pub fn live_locations(
    env: &HashMap<String, StoreAddr>,
    store_cells: &HashMap<u64, StoreValue>,
) -> HashSet<StoreAddr> {
    let mut live = HashSet::new();
    let mut worklist: Vec<StoreAddr> = env.values().copied().collect();

    while let Some(addr) = worklist.pop() {
        if !live.insert(addr) {
            continue; // Already visited
        }

        // Follow references within the value
        let id = addr.id();
        if let Some(value) = store_cells.get(&id) {
            match value {
                StoreValue::Closure { env_snapshot, .. } => {
                    for a in env_snapshot.values() {
                        if !live.contains(a) {
                            worklist.push(*a);
                        }
                    }
                }
                StoreValue::Simple(_)
                | StoreValue::Void
                | StoreValue::Relation { .. }
                | StoreValue::Constraint { .. }
                | StoreValue::RewriteRule { .. }
                | StoreValue::EClass { .. } => {}
                StoreValue::ChannelRef(_) => {}
            }
        }
    }

    live
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── GcStrategy tests ────────────────────────────────────────────────

    #[test]
    fn gc_strategy_default_is_refcount() {
        assert_eq!(GcStrategy::default(), GcStrategy::RefCount);
    }

    #[test]
    fn gc_strategy_display() {
        assert_eq!(format!("{}", GcStrategy::None), "None");
        assert_eq!(format!("{}", GcStrategy::RefCount), "RefCount");
        assert_eq!(format!("{}", GcStrategy::MarkSweep), "MarkSweep");
    }

    // ── BackpressureTier tests ──────────────────────────────────────────

    #[test]
    fn backpressure_tier_quantum_sizes() {
        assert_eq!(BackpressureTier::Normal.quantum_size(), 1000);
        assert_eq!(BackpressureTier::Light.quantum_size(), 750);
        assert_eq!(BackpressureTier::Medium.quantum_size(), 500);
        assert_eq!(BackpressureTier::Heavy.quantum_size(), 250);
    }

    #[test]
    fn backpressure_tier_from_u8() {
        assert_eq!(BackpressureTier::from_u8(0), BackpressureTier::Normal);
        assert_eq!(BackpressureTier::from_u8(1), BackpressureTier::Light);
        assert_eq!(BackpressureTier::from_u8(2), BackpressureTier::Medium);
        assert_eq!(BackpressureTier::from_u8(3), BackpressureTier::Heavy);
        assert_eq!(BackpressureTier::from_u8(255), BackpressureTier::Heavy); // clamped
    }

    #[test]
    fn backpressure_tier_ordering() {
        assert!(BackpressureTier::Normal < BackpressureTier::Light);
        assert!(BackpressureTier::Light < BackpressureTier::Medium);
        assert!(BackpressureTier::Medium < BackpressureTier::Heavy);
    }

    // ── RefCountGc tests ────────────────────────────────────────────────

    #[test]
    fn refcount_new_is_empty() {
        let gc = RefCountGc::new();
        assert_eq!(gc.tracked_count(), 0);
        assert!(!gc.has_pending_removals());
    }

    #[test]
    fn refcount_inc_dec_basic() {
        let mut gc = RefCountGc::new();
        gc.inc_ref(0);
        gc.inc_ref(0);
        assert_eq!(gc.ref_count(0), 2);

        let count = gc.dec_ref(0);
        assert_eq!(count, 1);
        assert!(!gc.has_pending_removals());

        let count = gc.dec_ref(0);
        assert_eq!(count, 0);
        assert!(gc.has_pending_removals());
        assert_eq!(gc.pending_removal_count(), 1);
    }

    #[test]
    fn refcount_take_pending() {
        let mut gc = RefCountGc::new();
        gc.inc_ref(0);
        gc.inc_ref(1);
        gc.dec_ref(0);
        gc.dec_ref(1);

        let removals = gc.take_pending_removals();
        assert_eq!(removals.len(), 2);
        assert!(removals.contains(&0));
        assert!(removals.contains(&1));
        // After take, pending is empty
        assert!(!gc.has_pending_removals());
    }

    #[test]
    fn refcount_dec_ref_untracked_returns_zero() {
        let mut gc = RefCountGc::new();
        assert_eq!(gc.dec_ref(999), 0);
    }

    #[test]
    fn refcount_symmetry() {
        // For all n: n inc_refs then n dec_refs → count = 0
        let mut gc = RefCountGc::new();
        for n in 1..=10 {
            for _ in 0..n {
                gc.inc_ref(42);
            }
            assert_eq!(gc.ref_count(42), n);
            for _ in 0..n {
                gc.dec_ref(42);
            }
            assert_eq!(gc.ref_count(42), 0);
        }
    }

    #[test]
    fn refcount_multiple_addrs() {
        let mut gc = RefCountGc::new();
        gc.inc_ref(0);
        gc.inc_ref(0);
        gc.inc_ref(1);

        gc.dec_ref(0); // count 1
        gc.dec_ref(1); // count 0 → dead
        gc.dec_ref(0); // count 0 → dead

        let mut removals = gc.take_pending_removals();
        removals.sort();
        assert_eq!(removals, vec![0, 1]);
    }

    #[test]
    fn refcount_clear() {
        let mut gc = RefCountGc::new();
        gc.inc_ref(0);
        gc.inc_ref(1);
        gc.dec_ref(1);
        gc.clear();
        assert_eq!(gc.tracked_count(), 0);
        assert!(!gc.has_pending_removals());
    }

    // ── MarkSweepGc mark tests (green-threads — GcSnapshot is feature-gated) ──

    mod mark_sweep_tests {
        use super::*;

        #[test]
        fn mark_sweep_empty_snapshot() {
            let gc = MarkSweepGc::new();
            let snapshot = GcSnapshot {
                roots: vec![],
                store_cells: HashMap::new(),
                epoch: 0,
            };
            let live = gc.mark(&snapshot);
            assert!(live.is_empty());
        }

        #[test]
        fn mark_sweep_simple_reachable() {
            let gc = MarkSweepGc::new();
            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("a".to_string()));
            cells.insert(1, StoreValue::Simple("b".to_string()));
            cells.insert(2, StoreValue::Simple("c".to_string()));

            let snapshot = GcSnapshot {
                roots: vec![0, 1], // 0 and 1 are reachable; 2 is not
                store_cells: cells,
                epoch: 3,
            };

            let live = gc.mark(&snapshot);
            assert!(live.contains(&0));
            assert!(live.contains(&1));
            assert!(!live.contains(&2));
        }

        #[test]
        fn mark_sweep_closure_chain() {
            let gc = MarkSweepGc::new();
            let mut cells = HashMap::new();

            // Closure at addr 0 references global addr 1
            let mut env0 = HashMap::new();
            env0.insert("x".to_string(), StoreAddr::Global(1));
            cells.insert(
                0,
                StoreValue::Closure {
                    env_snapshot: env0,
                    body: "body".to_string(),
                },
            );

            // Value at addr 1 (reachable through closure at 0)
            cells.insert(1, StoreValue::Simple("reachable".to_string()));

            // Value at addr 2 (unreachable)
            cells.insert(2, StoreValue::Simple("dead".to_string()));

            let snapshot = GcSnapshot {
                roots: vec![0], // Only 0 is a root
                store_cells: cells,
                epoch: 3,
            };

            let live = gc.mark(&snapshot);
            assert!(live.contains(&0)); // Direct root
            assert!(live.contains(&1)); // Reachable through closure
            assert!(!live.contains(&2)); // Unreachable
        }

        #[test]
        fn mark_sweep_closure_chain_deep() {
        // Test a chain: root → closure A → closure B → value C
        let gc = MarkSweepGc::new();
        let mut cells = HashMap::new();

        // Closure B at addr 2 references addr 3
        let mut env_b = HashMap::new();
        env_b.insert("z".to_string(), StoreAddr::Global(3));
        cells.insert(
            2,
            StoreValue::Closure {
                env_snapshot: env_b,
                body: "b_body".to_string(),
            },
        );

        // Closure A at addr 1 references addr 2
        let mut env_a = HashMap::new();
        env_a.insert("y".to_string(), StoreAddr::Global(2));
        cells.insert(
            1,
            StoreValue::Closure {
                env_snapshot: env_a,
                body: "a_body".to_string(),
            },
        );

        // Simple value at addr 3 (reachable through B)
        cells.insert(3, StoreValue::Simple("deep".to_string()));

        // Dead value at addr 4
        cells.insert(4, StoreValue::Simple("dead".to_string()));

        let snapshot = GcSnapshot {
            roots: vec![1], // Root at addr 1
            store_cells: cells,
            epoch: 5,
        };

        let live = gc.mark(&snapshot);
        assert!(live.contains(&1)); // Root
        assert!(live.contains(&2)); // Closure A → Closure B
        assert!(live.contains(&3)); // Closure B → value
        assert!(!live.contains(&4)); // Dead
    }
    } // end mod mark_sweep_tests

    // ── MarkSweepGc sweep tests (green-threads) ────────────────────────

    mod sweep_tests {
        use super::*;

        #[test]
        fn sweep_collects_unreachable() {
            let gc = MarkSweepGc::new();
            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("live".to_string()));
            cells.insert(1, StoreValue::Simple("dead".to_string()));

            let snapshot = GcSnapshot {
                roots: vec![0],
                store_cells: cells,
                epoch: 2,
            };

            let live = gc.mark(&snapshot);
            let response = gc.sweep(&snapshot, &live);

            assert_eq!(response.dead_addrs, vec![1]);
            assert!(response.dead_channel_refs.is_empty());
            assert_eq!(response.snapshot_epoch, 2);
        }

        #[test]
        fn sweep_detects_dead_channel_refs() {
            let gc = MarkSweepGc::new();
            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("live".to_string()));
            cells.insert(1, StoreValue::ChannelRef(ChannelId(7)));

            let snapshot = GcSnapshot {
                roots: vec![0],
                store_cells: cells,
                epoch: 2,
            };

            let response = gc.collect(&snapshot);
            assert!(response.dead_addrs.contains(&1));
            assert_eq!(response.dead_channel_refs, vec![ChannelId(7)]);
        }

        #[test]
        fn collect_full_cycle() {
            let gc = MarkSweepGc::new();
            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("root".to_string()));
            cells.insert(1, StoreValue::Void);
            cells.insert(2, StoreValue::Simple("unreachable".to_string()));

            let snapshot = GcSnapshot {
                roots: vec![0, 1],
                store_cells: cells,
                epoch: 3,
            };

            let response = gc.collect(&snapshot);
            assert_eq!(response.dead_addrs, vec![2]);
            assert_eq!(response.snapshot_epoch, 3);
        }
    }

    // ── GcThread tests (green-threads) ──────────────────────────────────

    mod gc_thread_tests {
        use super::*;

        #[test]
        fn gc_thread_collect_and_respond() {
            let mut gc_thread = GcThread::spawn(MarkSweepGc::new());

            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("live".to_string()));
            cells.insert(1, StoreValue::Simple("dead".to_string()));

            let snapshot = GcSnapshot::new(vec![0], cells, 2);
            gc_thread.request_gc(snapshot);

            let response = gc_thread.recv_response_blocking().expect("should get response");
            assert_eq!(response.dead_addrs, vec![1]);
            assert_eq!(response.snapshot_epoch, 2);

            gc_thread.shutdown();
        }

        #[test]
        fn gc_thread_shutdown_clean() {
            let mut gc_thread = GcThread::spawn(MarkSweepGc::new());
            gc_thread.shutdown();
            // Verify no panic, no hang
        }

        #[test]
        fn gc_thread_try_recv_empty() {
            let gc_thread = GcThread::spawn(MarkSweepGc::new());
            match gc_thread.try_recv_response() {
                TryRecvGcResult::Empty => {} // expected
                other => panic!("expected Empty, got {:?}", other),
            }
        }
    }

    // ── GcMonitor tests (green-threads) ─────────────────────────────────

    mod monitor_tests {
        use super::*;

        #[test]
        fn monitor_initial_state() {
            let bp = Arc::new(AtomicU8::new(0));
            let monitor = GcMonitor::new(bp);
            assert_eq!(monitor.current_tier(), BackpressureTier::Normal);
            assert!(!monitor.is_gc_in_flight());
        }

        #[test]
        fn monitor_low_pressure_no_trigger() {
            let bp = Arc::new(AtomicU8::new(0));
            let mut monitor = GcMonitor::new(bp);
            let gc = MarkSweepGc::new();

            // Low allocation rate, low committed bytes
            let triggered = monitor.update(100, 1024, &gc);
            assert!(!triggered);
            assert_eq!(monitor.current_tier(), BackpressureTier::Normal);
        }

        #[test]
        fn monitor_high_alloc_rate_triggers() {
            let bp = Arc::new(AtomicU8::new(0));
            let mut monitor = GcMonitor::new(bp);
            let gc = MarkSweepGc::with_thresholds(100, 10 * 1024 * 1024);

            // First update establishes baseline
            monitor.update(0, 0, &gc);

            // Second update with large delta so EMA exceeds threshold.
            // With alpha=0.3 and delta=500: EMA = 0.3*500 = 150 > 100 → triggers.
            let triggered = monitor.update(500, 0, &gc);
            assert!(triggered);
            assert!(monitor.is_gc_in_flight());

            // Subsequent update should not re-trigger while in flight
            let triggered2 = monitor.update(400, 0, &gc);
            assert!(!triggered2);

            // Complete GC
            monitor.gc_completed();
            assert!(!monitor.is_gc_in_flight());
        }

        #[test]
        fn monitor_committed_bytes_triggers() {
            let bp = Arc::new(AtomicU8::new(0));
            let mut monitor = GcMonitor::new(bp);
            let gc = MarkSweepGc::with_thresholds(100_000, 1024); // 1KB threshold

            // First update
            monitor.update(0, 0, &gc);

            // Committed bytes exceed threshold
            let triggered = monitor.update(1, 2048, &gc);
            assert!(triggered);
            assert_eq!(monitor.current_tier(), BackpressureTier::Heavy);
        }

        #[test]
        fn monitor_backpressure_tiers() {
            let bp = Arc::new(AtomicU8::new(0));
            let mut monitor = GcMonitor::new(Arc::clone(&bp));
            let gc = MarkSweepGc::with_thresholds(1000, 10 * 1024 * 1024);

            // Below 50% → Normal
            monitor.update(0, 0, &gc);
            monitor.update(100, 0, &gc); // rate ~30 (EMA)
            assert_eq!(monitor.current_tier(), BackpressureTier::Normal);
        }
    }

    // ── live_locations tests ────────────────────────────────────────────

    #[test]
    fn live_locations_empty() {
        let env: HashMap<String, StoreAddr> = HashMap::new();
        let store: HashMap<u64, StoreValue> = HashMap::new();
        let live = live_locations(&env, &store);
        assert!(live.is_empty());
    }

    #[test]
    fn live_locations_direct_refs() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), StoreAddr::Local(0));
        env.insert("y".to_string(), StoreAddr::Local(1));

        let mut store = HashMap::new();
        store.insert(0, StoreValue::Simple("a".to_string()));
        store.insert(1, StoreValue::Simple("b".to_string()));
        store.insert(2, StoreValue::Simple("dead".to_string()));

        let live = live_locations(&env, &store);
        assert!(live.contains(&StoreAddr::Local(0)));
        assert!(live.contains(&StoreAddr::Local(1)));
        assert!(!live.contains(&StoreAddr::Local(2)));
    }

    #[test]
    fn live_locations_closure_transitivity() {
        let mut env = HashMap::new();
        env.insert("f".to_string(), StoreAddr::Local(0));

        let mut store = HashMap::new();
        // Closure at 0 captures a reference to 1
        let mut closure_env = HashMap::new();
        closure_env.insert("captured".to_string(), StoreAddr::Local(1));
        store.insert(
            0,
            StoreValue::Closure {
                env_snapshot: closure_env,
                body: "body".to_string(),
            },
        );
        store.insert(1, StoreValue::Simple("reachable".to_string()));
        store.insert(2, StoreValue::Simple("dead".to_string()));

        let live = live_locations(&env, &store);
        assert!(live.contains(&StoreAddr::Local(0)));
        assert!(live.contains(&StoreAddr::Local(1)));
        assert!(!live.contains(&StoreAddr::Local(2)));
    }
}
