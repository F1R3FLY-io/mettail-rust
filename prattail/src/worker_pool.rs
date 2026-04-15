//! Work-Stealing Worker Pool for M:N Green Thread Execution.
//!
//! Implements the execution layer of the two-pool M:N scheduler architecture.
//! N native OS threads cooperatively execute M green threads using
//! Chase-Lev work-stealing deques (via `crossbeam::deque`).
//!
//! ## Architecture
//!
//! ```text
//!   Coordinator ──push──→ Injector<GreenThreadId> (global FIFO)
//!                              │
//!                    workers steal from
//!                              │
//!     ┌────────────────────────┼────────────────────────┐
//!     │                        │                        │
//!     ▼                        ▼                        ▼
//!   Worker 0                Worker 1              Worker N-1
//!   ┌─────────┐           ┌─────────┐           ┌─────────┐
//!   │ Local   │◀── steal ─│ Local   │── steal ─▶│ Local   │
//!   │ Deque   │           │ Deque   │           │ Deque   │
//!   │ (LIFO)  │           │ (LIFO)  │           │ (LIFO)  │
//!   └─────────┘           └─────────┘           └─────────┘
//! ```
//!
//! ## Work Discovery Order
//!
//! Each worker tries work sources in this order:
//! 1. **Local deque pop** (LIFO — cache-warm, depth-first for forked threads)
//! 2. **Global injector steal** (FIFO — fairness for coordinator-dispatched work)
//! 3. **Random peer steal** (FIFO — load balancing across workers)
//! 4. **Park on condvar** (sleep until woken by new work or shutdown)
//!
//! ## References
//!
//! - Chase, D. & Lev, Y. (2005). "Dynamic circular work-stealing deque."
//!   *Proceedings of SPAA*, pp. 21-28.
//! - Blumofe, R. & Leiserson, C. (1999). "Scheduling multithreaded
//!   computations by work stealing." *JACM*, 46(5):720-748.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use crossbeam_channel::Sender;
use crossbeam_deque::{Injector, Steal, Stealer, Worker};

use crate::channel::GreenThreadId;
use crate::green_thread::{CekThreadState, GreenThreadRegistry, QuantumResult};
use crate::pool_fsm::{
    WorkerAction, WorkerEvent, WorkerReport, WorkerState, worker_process_event,
};

// ══════════════════════════════════════════════════════════════════════════════
// WorkerParker — Condvar-based parking for idle workers
// ══════════════════════════════════════════════════════════════════════════════

/// Shared parking mechanism for idle workers.
///
/// Uses a pending-work counter instead of a boolean flag to avoid
/// lost notifications when multiple `unpark_one()` calls occur between
/// worker wake-ups.
///
/// ## Protocol
///
/// - **Park**: Worker waits on condvar while `pending == 0 && !shutdown`.
///   On wake, decrements `pending` (consumes the notification).
/// - **Unpark one**: Increments `pending`, notifies one waiter.
/// - **Unpark all**: Sets `pending = u32::MAX`, notifies all waiters.
pub struct WorkerParker {
    /// Number of pending wake-up notifications.
    pending: Mutex<u32>,
    /// Condvar for sleeping workers.
    condvar: Condvar,
}

impl WorkerParker {
    /// Create a new parker with zero pending notifications.
    pub fn new() -> Self {
        Self {
            pending: Mutex::new(0),
            condvar: Condvar::new(),
        }
    }

    /// Park the calling thread until work is available or shutdown is signaled.
    ///
    /// Blocks on the condvar while `pending == 0 && !shutdown`.
    /// On return, the worker should re-check its work sources.
    pub fn park(&self, shutdown: &AtomicBool) {
        let mut pending = self.pending.lock().expect("WorkerParker mutex poisoned");
        while *pending == 0 && !shutdown.load(Ordering::Relaxed) {
            pending = self
                .condvar
                .wait(pending)
                .expect("WorkerParker condvar wait failed");
        }
        if *pending > 0 {
            *pending -= 1;
        }
    }

    /// Wake one parked worker.
    ///
    /// Increments the pending counter and notifies one condvar waiter.
    /// If no workers are parked, the notification is saved for the next
    /// worker that parks.
    pub fn unpark_one(&self) {
        let mut pending = self.pending.lock().expect("WorkerParker mutex poisoned");
        *pending = pending.saturating_add(1);
        drop(pending);
        self.condvar.notify_one();
    }

    /// Wake all parked workers (e.g., for shutdown).
    ///
    /// Sets pending to `u32::MAX` and notifies all condvar waiters.
    pub fn unpark_all(&self) {
        let mut pending = self.pending.lock().expect("WorkerParker mutex poisoned");
        *pending = u32::MAX;
        drop(pending);
        self.condvar.notify_all();
    }
}

impl Default for WorkerParker {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for WorkerParker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pending = self
            .pending
            .lock()
            .map(|p| *p)
            .unwrap_or(u32::MAX);
        f.debug_struct("WorkerParker")
            .field("pending", &pending)
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WorkerPool — N native threads with work-stealing deques
// ══════════════════════════════════════════════════════════════════════════════

/// Configuration for a worker pool.
pub struct WorkerPoolConfig {
    /// Number of worker threads to spawn.
    pub num_workers: usize,
    /// Green thread quantum size (CEK steps per quantum).
    pub quantum_size: usize,
}

impl Default for WorkerPoolConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus::get(),
            quantum_size: Self::default_quantum(),
        }
    }
}

impl WorkerPoolConfig {
    /// Default quantum size, configurable via `PRATTAIL_QUANTUM` env var.
    pub fn default_quantum() -> usize {
        std::env::var("PRATTAIL_QUANTUM")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(100)
    }
}

/// M:N work-stealing worker pool.
///
/// Owns N native OS threads, each with a local `crossbeam::deque::Worker`
/// for LIFO task scheduling. A shared `Injector` provides FIFO global
/// injection from the coordinator. Workers steal from each other via
/// `Stealer` handles for load balancing.
pub struct WorkerPool {
    /// Handles to the native worker threads.
    worker_handles: Vec<JoinHandle<()>>,
    /// Global work injector (coordinator pushes here, workers steal).
    injector: Arc<Injector<GreenThreadId>>,
    /// Cooperative shutdown flag.
    shutdown: Arc<AtomicBool>,
    /// Shared parker for idle workers.
    parker: Arc<WorkerParker>,
    /// Number of active workers (atomic to support grow-only resizing).
    num_workers: AtomicUsize,
}

impl WorkerPool {
    /// Create and start a worker pool.
    ///
    /// Spawns `config.num_workers` native threads, each running the
    /// work-stealing loop. Workers pop from their local deque (LIFO),
    /// steal from the global injector (FIFO), steal from random peers,
    /// or park on a condvar when idle.
    ///
    /// # Arguments
    ///
    /// - `config`: Pool configuration (worker count, quantum size).
    /// - `registry`: Shared green thread registry for accessing thread state.
    /// - `report_tx`: MPSC sender for worker-to-coordinator reports.
    pub fn new(
        config: WorkerPoolConfig,
        registry: Arc<GreenThreadRegistry>,
        report_tx: Sender<WorkerReport>,
    ) -> Self {
        let num_workers = config.num_workers.max(1);
        let quantum_size = config.quantum_size;
        let injector = Arc::new(Injector::new());
        let shutdown = Arc::new(AtomicBool::new(false));
        let parker = Arc::new(WorkerParker::new());

        // Create per-worker deques and collect stealers.
        let mut workers_and_stealers: Vec<(Worker<GreenThreadId>, Stealer<GreenThreadId>)> =
            (0..num_workers)
                .map(|_| {
                    let w = Worker::new_lifo();
                    let s = w.stealer();
                    (w, s)
                })
                .collect();

        // All stealers (shared among all workers for cross-stealing).
        let all_stealers: Vec<Stealer<GreenThreadId>> =
            workers_and_stealers.iter().map(|(_, s)| s.clone()).collect();

        // Spawn worker threads.
        let mut handles = Vec::with_capacity(num_workers);
        for (idx, (local_deque, _)) in workers_and_stealers.drain(..).enumerate() {
            let injector = Arc::clone(&injector);
            let shutdown = Arc::clone(&shutdown);
            let parker = Arc::clone(&parker);
            let registry = Arc::clone(&registry);
            let report_tx = report_tx.clone();
            // Clone stealers for this worker (excluding its own at index `idx`).
            let peer_stealers: Vec<Stealer<GreenThreadId>> = all_stealers
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != idx)
                .map(|(_, s)| s.clone())
                .collect();

            let handle = std::thread::Builder::new()
                .name(format!("prattail-worker-{}", idx))
                .spawn(move || {
                    worker_loop(
                        idx,
                        local_deque,
                        injector,
                        peer_stealers,
                        shutdown,
                        parker,
                        registry,
                        report_tx,
                        quantum_size,
                    );
                })
                .expect("failed to spawn worker thread");

            handles.push(handle);
        }

        Self {
            worker_handles: handles,
            injector,
            shutdown,
            parker,
            num_workers: AtomicUsize::new(num_workers),
        }
    }

    /// Push a green thread ID to the global injector for workers to pick up.
    ///
    /// The coordinator calls this to dispatch work. After pushing, call
    /// `unpark_one()` to wake a parked worker.
    pub fn inject(&self, thread_id: GreenThreadId) {
        self.injector.push(thread_id);
    }

    /// Wake one parked worker.
    pub fn unpark_one(&self) {
        self.parker.unpark_one();
    }

    /// Wake all parked workers (e.g., after injecting a batch of work).
    pub fn unpark_all(&self) {
        self.parker.unpark_all();
    }

    /// Signal all workers to shut down and join their threads.
    ///
    /// Sets the shutdown flag, wakes all parked workers, and blocks
    /// until all worker threads have exited.
    pub fn shutdown(self) {
        self.shutdown.store(true, Ordering::Release);
        self.parker.unpark_all();
        for handle in self.worker_handles {
            let _ = handle.join();
        }
    }

    /// Number of worker threads (includes any grown workers).
    pub fn num_workers(&self) -> usize {
        self.num_workers.load(Ordering::Relaxed)
    }

    /// Whether shutdown has been signaled.
    pub fn is_shutdown(&self) -> bool {
        self.shutdown.load(Ordering::Acquire)
    }

    /// Reference to the global injector.
    pub fn injector(&self) -> &Arc<Injector<GreenThreadId>> {
        &self.injector
    }

    /// Reference to the shared parker.
    pub fn parker(&self) -> &Arc<WorkerParker> {
        &self.parker
    }

    /// Reference to the shutdown flag.
    pub fn shutdown_flag(&self) -> &Arc<AtomicBool> {
        &self.shutdown
    }

    /// Spawn additional worker threads, growing the pool.
    ///
    /// New workers share the existing injector and parker, enabling them
    /// to pick up work from the global queue and be woken by unpark signals.
    /// They cannot steal from original workers' local deques (architectural
    /// simplification -- the injector handles the main dispatch path).
    ///
    /// # Note
    ///
    /// Shrinking is not supported (requires JoinHandle ownership management
    /// that conflicts with `Arc<WorkerPool>`). Only grow is implemented.
    pub fn grow(
        &self,
        additional: usize,
        registry: Arc<GreenThreadRegistry>,
        report_tx: Sender<WorkerReport>,
        quantum_size: usize,
    ) {
        let base_idx = self.num_workers.fetch_add(additional, Ordering::Relaxed);
        // Note: new workers have no peer stealers (they can only take from injector).
        // This is acceptable since the injector is the primary dispatch path.
        for i in 0..additional {
            let idx = base_idx + i;
            let injector = Arc::clone(&self.injector);
            let shutdown = Arc::clone(&self.shutdown);
            let parker = Arc::clone(&self.parker);
            let registry = Arc::clone(&registry);
            let report_tx = report_tx.clone();
            let local_deque = Worker::new_lifo();

            std::thread::Builder::new()
                .name(format!("prattail-worker-{}", idx))
                .spawn(move || {
                    worker_loop(
                        idx,
                        local_deque,
                        injector,
                        Vec::new(), // No peer stealers for grown workers
                        shutdown,
                        parker,
                        registry,
                        report_tx,
                        quantum_size,
                    );
                })
                .expect("failed to spawn additional worker thread");
        }
        // Note: We don't track the new JoinHandles. This is intentional --
        // shutdown signals via the AtomicBool flag, and unpark_all wakes them.
        // They'll exit when the shutdown flag is set.
    }
}

impl std::fmt::Debug for WorkerPool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorkerPool")
            .field("num_workers", &self.num_workers.load(Ordering::Relaxed))
            .field("shutdown", &self.shutdown.load(Ordering::Relaxed))
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Worker Loop — Core execution loop for each native thread
// ══════════════════════════════════════════════════════════════════════════════

/// Simple XorShift64 PRNG for random steal victim selection.
/// Avoids pulling in the `rand` crate.
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// The main loop for a single worker thread.
///
/// Driven by the `WorkerFSM` for state tracking:
/// 1. **Idle**: Try to find work (local → injector → peer steal).
/// 2. **Executing**: Run a green thread quantum.
/// 3. **Parking**: Sleep on condvar until woken.
/// 4. **Exiting**: Break out of the loop.
fn worker_loop(
    idx: usize,
    local: Worker<GreenThreadId>,
    injector: Arc<Injector<GreenThreadId>>,
    peer_stealers: Vec<Stealer<GreenThreadId>>,
    shutdown: Arc<AtomicBool>,
    parker: Arc<WorkerParker>,
    registry: Arc<GreenThreadRegistry>,
    report_tx: Sender<WorkerReport>,
    quantum_size: usize,
) {
    let mut fsm_state = WorkerState::Idle;
    // Seed RNG with worker index + timestamp bits for uniqueness.
    let mut rng_state = (idx as u64).wrapping_add(0xDEAD_BEEF_CAFE_BABE);
    // Ensure non-zero seed for xorshift.
    if rng_state == 0 {
        rng_state = 1;
    }

    loop {
        // Check shutdown at the top of each iteration.
        if shutdown.load(Ordering::Relaxed) {
            break;
        }

        match &fsm_state {
            WorkerState::Idle => {
                // Try to find work from any source.
                let found = try_find_work(&local, &injector, &peer_stealers, &mut rng_state);
                let event = match found {
                    Some(tid) => WorkerEvent::WorkFound(tid),
                    None => WorkerEvent::NoWorkAvailable,
                };
                let transition = worker_process_event(&fsm_state, event);
                fsm_state = transition.new_state;
                execute_worker_actions(
                    &transition.actions,
                    &local,
                    &registry,
                    &report_tx,
                    &parker,
                    &shutdown,
                    quantum_size,
                    idx,
                );
            }

            WorkerState::Executing { thread_id } => {
                let tid = *thread_id;
                let execution = execute_quantum(&registry, tid, quantum_size);

                // GS-5: Report channel activity for event-driven wake-ups.
                if !execution.channel_sends.is_empty() {
                    let _ = report_tx.send(WorkerReport::ChannelActivity {
                        channel_ids: execution.channel_sends,
                    });
                }

                let event = WorkerEvent::QuantumComplete(execution.result);
                let transition = worker_process_event(&fsm_state, event);
                fsm_state = transition.new_state;
                execute_worker_actions(
                    &transition.actions,
                    &local,
                    &registry,
                    &report_tx,
                    &parker,
                    &shutdown,
                    quantum_size,
                    idx,
                );
            }

            WorkerState::Parking => {
                parker.park(&shutdown);
                let event = if shutdown.load(Ordering::Relaxed) {
                    WorkerEvent::ShutdownSignal
                } else {
                    WorkerEvent::Unpark
                };
                let transition = worker_process_event(&fsm_state, event);
                fsm_state = transition.new_state;
            }

            WorkerState::Exiting => break,
        }
    }
}

/// Try to find a green thread to execute from any work source.
///
/// Checks in order: local deque (LIFO) → global injector (FIFO) → random peer steal.
fn try_find_work(
    local: &Worker<GreenThreadId>,
    injector: &Injector<GreenThreadId>,
    peer_stealers: &[Stealer<GreenThreadId>],
    rng_state: &mut u64,
) -> Option<GreenThreadId> {
    // 1. Local deque (LIFO — cache-warm).
    if let Some(tid) = local.pop() {
        return Some(tid);
    }

    // 2. Global injector (FIFO — fairness).
    loop {
        match injector.steal() {
            Steal::Success(tid) => return Some(tid),
            Steal::Empty => break,
            Steal::Retry => continue,
        }
    }

    // 3. Random peer steal.
    let n = peer_stealers.len();
    if n > 0 {
        let start = (xorshift64(rng_state) as usize) % n;
        for i in 0..n {
            let idx = (start + i) % n;
            loop {
                match peer_stealers[idx].steal() {
                    Steal::Success(tid) => return Some(tid),
                    Steal::Empty => break,
                    Steal::Retry => continue,
                }
            }
        }
    }

    None
}

/// Result of quantum execution: the quantum result plus any channel sends.
struct QuantumExecution {
    result: QuantumResult,
    /// Channel IDs that received sends during this quantum (for event-driven wake).
    channel_sends: Vec<crate::channel::ChannelId>,
}

/// Execute a quantum of a green thread, returning the result and channel activity.
///
/// Transitions the thread Ready → Running, calls `run_quantum()`,
/// drains channel sends for event-driven wake-up, and drops the DashMap
/// RefMut promptly to avoid holding shard locks.
fn execute_quantum(
    registry: &GreenThreadRegistry,
    thread_id: GreenThreadId,
    quantum_size: usize,
) -> QuantumExecution {
    let mut thread_ref = match registry.get_mut(thread_id) {
        Some(r) => r,
        None => {
            return QuantumExecution {
                result: QuantumResult::Failed {
                    error: format!("thread {} not found in registry", thread_id),
                },
                channel_sends: Vec::new(),
            };
        }
    };

    // Transition to Running if Ready.
    match &thread_ref.state {
        CekThreadState::Ready => {
            thread_ref.state = CekThreadState::Running;
        }
        CekThreadState::Running => {
            // Already running (e.g., re-enqueued after yield).
        }
        other => {
            return QuantumExecution {
                result: QuantumResult::Failed {
                    error: format!(
                        "thread {} in unexpected state {} for execution",
                        thread_id, other
                    ),
                },
                channel_sends: Vec::new(),
            };
        }
    }

    let result = thread_ref.run_quantum(quantum_size);
    let channel_sends = thread_ref.take_channel_sends();
    drop(thread_ref);
    // RefMut is dropped here, releasing the DashMap shard lock.

    QuantumExecution {
        result,
        channel_sends,
    }
}

/// Execute the side-effect actions produced by a worker FSM transition.
fn execute_worker_actions(
    actions: &[WorkerAction],
    local: &Worker<GreenThreadId>,
    registry: &GreenThreadRegistry,
    report_tx: &Sender<WorkerReport>,
    parker: &WorkerParker,
    shutdown: &AtomicBool,
    _quantum_size: usize,
    _worker_idx: usize,
) {
    for action in actions {
        match action {
            WorkerAction::ExecuteQuantum(_) => {
                // Handled by the FSM loop — Executing state drives this.
            }
            WorkerAction::ReenqueueLocal(tid) => {
                local.push(*tid);
            }
            WorkerAction::ReportToCoordinator(report) => {
                // Best-effort send — if coordinator is gone, we're shutting down.
                let _ = report_tx.send(report.clone());
            }
            WorkerAction::ForkAndEnqueue {
                parent_id,
                categories,
            } => {
                // Fork children from parent and push to local deque.
                // `categories` here are actually the sub-term strings from
                // QuantumResult::Forked { children }, NOT grammar categories.
                // Each string is a sub-term that a child thread must evaluate.
                for sub_term in categories {
                    if let Some(child_id) =
                        registry.spawn_child(*parent_id, sub_term.clone())
                    {
                        // Set the child's control term to the sub-term string
                        // so it runs through the real CEK path (not the stub).
                        if let Some(mut child_ref) = registry.get_mut(child_id) {
                            child_ref.control = sub_term.clone();
                            child_ref.eval_state =
                                crate::cek_eval::EvalState::Ready;
                        }
                        local.push(child_id);
                    }
                }
                // Report fork to coordinator.
                let _ = report_tx.send(WorkerReport::ForkRequested {
                    parent_id: *parent_id,
                    categories: categories.clone(),
                });
            }
            WorkerAction::Park => {
                parker.park(shutdown);
            }
            WorkerAction::Exit => {
                // No-op — the loop will break on Exiting state.
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── WorkerParker Tests ──────────────────────────────────────────────

    #[test]
    fn test_parker_unpark_before_park() {
        let parker = WorkerParker::new();
        let shutdown = AtomicBool::new(false);

        // Unpark before park: the pending counter ensures the notification
        // is not lost.
        parker.unpark_one();

        // Park should return immediately (pending = 1 → 0).
        parker.park(&shutdown);
        // If we got here, park returned without blocking. Success.
    }

    #[test]
    fn test_parker_multiple_unparks() {
        let parker = WorkerParker::new();
        let shutdown = AtomicBool::new(false);

        parker.unpark_one();
        parker.unpark_one();
        parker.unpark_one();

        // Three unparks → three parks should return immediately.
        parker.park(&shutdown);
        parker.park(&shutdown);
        parker.park(&shutdown);
    }

    #[test]
    fn test_parker_shutdown_wakes() {
        let parker = Arc::new(WorkerParker::new());
        let shutdown = Arc::new(AtomicBool::new(false));

        let p = Arc::clone(&parker);
        let s = Arc::clone(&shutdown);
        let handle = std::thread::spawn(move || {
            p.park(&s);
        });

        // Give the thread time to park.
        std::thread::sleep(std::time::Duration::from_millis(50));

        // Signal shutdown and wake.
        shutdown.store(true, Ordering::Release);
        parker.unpark_all();

        handle.join().expect("worker thread should exit");
    }

    // ── xorshift64 Tests ────────────────────────────────────────────────

    #[test]
    fn test_xorshift64_produces_different_values() {
        let mut state = 12345u64;
        let mut values = std::collections::HashSet::new();
        for _ in 0..100 {
            values.insert(xorshift64(&mut state));
        }
        // Should produce many unique values.
        assert!(
            values.len() > 90,
            "xorshift64 should produce diverse values, got {} unique out of 100",
            values.len()
        );
    }

    // ── try_find_work Tests ─────────────────────────────────────────────

    #[test]
    fn test_find_work_local_first() {
        let local = Worker::new_lifo();
        let injector = Injector::new();
        let stealers: Vec<Stealer<GreenThreadId>> = vec![];
        let mut rng = 42u64;

        local.push(GreenThreadId(1));
        injector.push(GreenThreadId(2));

        // Should find local work first.
        let found = try_find_work(&local, &injector, &stealers, &mut rng);
        assert_eq!(found, Some(GreenThreadId(1)));
    }

    #[test]
    fn test_find_work_injector_second() {
        let local = Worker::new_lifo();
        let injector = Injector::new();
        let stealers: Vec<Stealer<GreenThreadId>> = vec![];
        let mut rng = 42u64;

        injector.push(GreenThreadId(5));

        // No local work → should find injector work.
        let found = try_find_work(&local, &injector, &stealers, &mut rng);
        assert_eq!(found, Some(GreenThreadId(5)));
    }

    #[test]
    fn test_find_work_steal_third() {
        let local = Worker::new_lifo();
        let injector = Injector::new();

        // Create a peer with work.
        let peer = Worker::new_lifo();
        peer.push(GreenThreadId(10));
        let stealers = vec![peer.stealer()];
        let mut rng = 42u64;

        // No local or injector work → should steal from peer.
        let found = try_find_work(&local, &injector, &stealers, &mut rng);
        assert_eq!(found, Some(GreenThreadId(10)));
    }

    #[test]
    fn test_find_work_nothing() {
        let local = Worker::new_lifo();
        let injector = Injector::new();
        let stealers: Vec<Stealer<GreenThreadId>> = vec![];
        let mut rng = 42u64;

        let found = try_find_work(&local, &injector, &stealers, &mut rng);
        assert_eq!(found, None);
    }

    // ── execute_quantum Tests ───────────────────────────────────────────

    #[test]
    fn test_execute_quantum_completes_empty_thread() {
        let registry = GreenThreadRegistry::new();
        let tid = registry.spawn("Expr".to_string());

        // Thread is Ready, stacks are empty → should complete.
        let execution = execute_quantum(&registry, tid, 100);
        assert!(matches!(execution.result, QuantumResult::Completed { .. }));
    }

    #[test]
    fn test_execute_quantum_yields_with_work() {
        let registry = GreenThreadRegistry::new();
        let tid = registry.spawn("Expr".to_string());

        // Add eval stack work.
        {
            let mut t = registry.get_mut(tid).expect("thread exists");
            for i in 0..20 {
                t.eval_stack.push_back(crate::cek_eval::EvalFrame::RewriteCont { rule_name: format!("frame_{}", i) });
            }
        }

        // Quantum of 5 → should yield.
        let execution = execute_quantum(&registry, tid, 5);
        assert_eq!(execution.result, QuantumResult::Yielded);

        // 15 frames remaining.
        let t = registry.get(tid).expect("thread exists");
        assert_eq!(t.eval_stack.len(), 15);
    }

    #[test]
    fn test_execute_quantum_thread_not_found() {
        let registry = GreenThreadRegistry::new();
        let execution = execute_quantum(&registry, GreenThreadId(999), 100);
        assert!(matches!(execution.result, QuantumResult::Failed { .. }));
    }

    // ── WorkerPool Integration Tests ────────────────────────────────────

    #[test]
    fn test_worker_pool_spawn_and_shutdown() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, _rx) = crossbeam_channel::unbounded();

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 2,
                quantum_size: 10,
            },
            registry,
            tx,
        );

        assert_eq!(pool.num_workers(), 2);
        assert!(!pool.is_shutdown());

        pool.shutdown();
        // If we get here, shutdown completed successfully.
    }

    #[test]
    fn test_worker_pool_processes_work() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, rx) = crossbeam_channel::unbounded();

        // Spawn a thread with empty stacks (will complete immediately).
        let tid = registry.spawn("Expr".to_string());

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx,
        );

        // Inject the thread and wake the worker.
        pool.inject(tid);
        pool.unpark_one();

        // Wait for completion report.
        let report = rx
            .recv_timeout(std::time::Duration::from_secs(2))
            .expect("should receive completion report");

        assert!(
            matches!(report, WorkerReport::ThreadCompleted { thread_id, .. } if thread_id == tid),
            "expected ThreadCompleted for {:?}, got {:?}",
            tid,
            report
        );

        pool.shutdown();
    }

    #[test]
    fn test_worker_pool_cooperative_yield() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, rx) = crossbeam_channel::unbounded();

        // Spawn a thread with enough work to yield multiple times.
        let tid = registry.spawn("Expr".to_string());
        {
            let mut t = registry.get_mut(tid).expect("thread exists");
            for i in 0..50 {
                t.eval_stack.push_back(crate::cek_eval::EvalFrame::RewriteCont { rule_name: format!("frame_{}", i) });
            }
        }

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 10, // small quantum → multiple yields
            },
            Arc::clone(&registry),
            tx,
        );

        pool.inject(tid);
        pool.unpark_one();

        // Eventually the thread will complete after multiple quanta.
        // Use a generous timeout to avoid flaky failures under heavy test parallelism.
        let report = rx
            .recv_timeout(std::time::Duration::from_secs(30))
            .expect("should receive completion report");

        assert!(
            matches!(report, WorkerReport::ThreadCompleted { thread_id, .. } if thread_id == tid),
            "expected ThreadCompleted, got {:?}",
            report
        );

        pool.shutdown();
    }

    #[test]
    fn test_worker_pool_multiple_threads() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, rx) = crossbeam_channel::unbounded();

        // Spawn multiple threads.
        let tids: Vec<GreenThreadId> = (0..10)
            .map(|_| registry.spawn("Expr".to_string()))
            .collect();

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 4,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx,
        );

        for &tid in &tids {
            pool.inject(tid);
        }
        pool.unpark_all();

        // Collect all completion reports.
        let mut completed = std::collections::HashSet::new();
        for _ in 0..10 {
            let report = rx
                .recv_timeout(std::time::Duration::from_secs(5))
                .expect("should receive report");
            if let WorkerReport::ThreadCompleted { thread_id, .. } = report {
                completed.insert(thread_id);
            }
        }

        assert_eq!(
            completed.len(),
            10,
            "all 10 threads should complete"
        );

        pool.shutdown();
    }

    #[test]
    fn test_worker_pool_work_stealing() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, rx) = crossbeam_channel::unbounded();

        // Spawn many threads to force work-stealing.
        let num_threads = 100;
        let tids: Vec<GreenThreadId> = (0..num_threads)
            .map(|_| registry.spawn("Expr".to_string()))
            .collect();

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 4,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx,
        );

        // Inject all at once.
        for &tid in &tids {
            pool.inject(tid);
        }
        pool.unpark_all();

        // Collect all completions.
        let mut completed = 0;
        for _ in 0..num_threads {
            match rx.recv_timeout(std::time::Duration::from_secs(10)) {
                Ok(WorkerReport::ThreadCompleted { .. }) => completed += 1,
                Ok(_) => {} // other reports are fine
                Err(_) => break,
            }
        }

        assert_eq!(
            completed, num_threads,
            "all {} threads should complete",
            num_threads
        );

        pool.shutdown();
    }

    // ── WorkerPool::grow() Tests ──────────────────────────────────────

    #[test]
    fn test_worker_pool_grow_increases_count() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, _rx) = crossbeam_channel::unbounded();

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 2,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx.clone(),
        );

        assert_eq!(pool.num_workers(), 2);

        pool.grow(3, Arc::clone(&registry), tx, 100);
        assert_eq!(pool.num_workers(), 5);

        // Shutdown should signal all workers (original + grown) via the AtomicBool flag.
        pool.shutdown();
    }

    #[test]
    fn test_worker_pool_grow_processes_work() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, rx) = crossbeam_channel::unbounded();

        // Start with 1 worker.
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx.clone(),
        );

        // Grow by 2 more workers.
        pool.grow(2, Arc::clone(&registry), tx, 100);

        // Spawn and inject threads -- the grown workers should help process them.
        let num_threads = 20;
        let tids: Vec<GreenThreadId> = (0..num_threads)
            .map(|_| registry.spawn("Expr".to_string()))
            .collect();
        for &tid in &tids {
            pool.inject(tid);
        }
        pool.unpark_all();

        // Collect completions.
        let mut completed = 0;
        for _ in 0..num_threads {
            match rx.recv_timeout(std::time::Duration::from_secs(5)) {
                Ok(WorkerReport::ThreadCompleted { .. }) => completed += 1,
                Ok(_) => {}
                Err(_) => break,
            }
        }

        assert_eq!(
            completed, num_threads,
            "all {} threads should complete with grown pool",
            num_threads
        );

        pool.shutdown();
    }

    #[test]
    fn test_worker_pool_grow_zero_is_noop() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let (tx, _rx) = crossbeam_channel::unbounded();

        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 2,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            tx.clone(),
        );

        pool.grow(0, Arc::clone(&registry), tx, 100);
        assert_eq!(pool.num_workers(), 2, "growing by 0 should not change count");

        pool.shutdown();
    }
}
