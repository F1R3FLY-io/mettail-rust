//! Process-Global Adaptive Thread Pool for MeTTaIL green threads.
//!
//! Provides a process-wide singleton (`GlobalPool`) that manages native worker
//! threads shared across all MeTTaIL language instances. Each language registers
//! its `Scheduler` as an `AnyScheduler` for cross-language work stealing and
//! unified resource management.
//!
//! ## Architecture
//!
//! ```text
//!   ┌─────────────────────────────────────────────────────┐
//!   │                   GlobalPool (singleton)             │
//!   │                                                     │
//!   │  ┌──────────────┐  ┌──────────────┐  ┌──────────┐ │
//!   │  │ Language A    │  │ Language B    │  │ Lang C   │ │
//!   │  │ AnyScheduler  │  │ AnyScheduler  │  │ AnySched │ │
//!   │  └──────────────┘  └──────────────┘  └──────────┘ │
//!   │                                                     │
//!   │  ┌──────────────────────────────────────────────┐  │
//!   │  │          Shared Parallel Budget               │  │
//!   │  │          (AtomicU32, CAS-based)               │  │
//!   │  └──────────────────────────────────────────────┘  │
//!   │                                                     │
//!   │  ┌──────────────────────────────────────────────┐  │
//!   │  │          HillClimber (adaptive scaling)       │  │
//!   │  │          EMA throughput -> worker count        │  │
//!   │  └──────────────────────────────────────────────┘  │
//!   └─────────────────────────────────────────────────────┘
//! ```
//!
//! ## Lock-Free Guarantees
//!
//! | Component             | Synchronization         | Lock-Free? |
//! |-----------------------|-------------------------|------------|
//! | Singleton init        | `OnceLock` (one-shot)   | Yes        |
//! | Scheduler registry    | `DashMap` (sharded)     | Yes*       |
//! | Parallel budget       | `AtomicU32` CAS         | Yes        |
//! | Active flag           | `AtomicBool`            | Yes        |
//! | Hill climber state    | `AtomicU32`/`AtomicU64` | Yes        |
//! | Metrics               | `AtomicU64`             | Yes        |
//!
//! (*) DashMap uses per-shard locks but never blocks cross-shard operations;
//!     contention is minimal for the typical 2-8 language registrations.
//!
//! ## References
//!
//! - MeTTaTron's `WorkPool` + `PriorityScheduler` (adaptive scaling)
//! - Hill climbing for thread pool sizing (CLR .NET ThreadPool)

use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use crossbeam_channel;
use dashmap::DashMap;

use crate::channel::ChannelMap;
use crate::coordinator::{Coordinator, CoordinatorConfig};
use crate::green_thread::GreenThreadRegistry;
use crate::scheduler::Scheduler;
use crate::worker_pool::{WorkerPool, WorkerPoolConfig};

// ══════════════════════════════════════════════════════════════════════════════
// AnyScheduler — Type-erased scheduler interface
// ══════════════════════════════════════════════════════════════════════════════

/// Type-erased interface for language-specific schedulers.
///
/// Implemented by each language's `Scheduler` to allow the `GlobalPool`
/// to poll and drive schedulers without knowing concrete types.
///
/// All methods must be safe to call from any thread.
pub trait AnyScheduler: Send + Sync {
    /// Unique identifier for the language this scheduler serves.
    fn language_id(&self) -> u64;

    /// Whether this scheduler has at least one runnable green thread.
    ///
    /// The global pool uses this for work-stealing decisions: if one
    /// language has no work, its native workers can steal from another.
    fn has_runnable(&self) -> bool;

    /// Perform one scheduler cycle, returning the number of actions taken.
    ///
    /// The global pool calls this periodically to drive all registered
    /// schedulers. Returns 0 if no work was available.
    fn tick(&self) -> usize;
}

// ══════════════════════════════════════════════════════════════════════════════
// GlobalPoolMetrics
// ══════════════════════════════════════════════════════════════════════════════

/// Runtime metrics for the global thread pool.
#[derive(Debug)]
pub struct GlobalPoolMetrics {
    /// Total number of tasks executed across all languages.
    pub total_tasks_executed: AtomicU64,
    /// Total number of cross-language work steals (scheduler A had no work,
    /// so its worker helped scheduler B).
    pub total_cross_language_steals: AtomicU64,
    /// Peak fraction of workers that were active simultaneously
    /// (stored as percentage * 100, e.g., 7500 = 75.00%).
    pub peak_worker_utilization: AtomicU64,
}

impl Default for GlobalPoolMetrics {
    fn default() -> Self {
        Self {
            total_tasks_executed: AtomicU64::new(0),
            total_cross_language_steals: AtomicU64::new(0),
            peak_worker_utilization: AtomicU64::new(0),
        }
    }
}

impl GlobalPoolMetrics {
    /// Create zeroed metrics.
    pub fn new() -> Self {
        Self::default()
    }

    /// Snapshot all counters for reporting.
    pub fn snapshot(&self) -> GlobalPoolMetricsSnapshot {
        GlobalPoolMetricsSnapshot {
            total_tasks_executed: self.total_tasks_executed.load(Ordering::Acquire),
            total_cross_language_steals: self.total_cross_language_steals.load(Ordering::Acquire),
            peak_worker_utilization: self.peak_worker_utilization.load(Ordering::Acquire),
        }
    }
}

/// Non-atomic snapshot of global pool metrics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalPoolMetricsSnapshot {
    pub total_tasks_executed: u64,
    pub total_cross_language_steals: u64,
    pub peak_worker_utilization: u64,
}

// ══════════════════════════════════════════════════════════════════════════════
// HillClimber — Adaptive worker scaling
// ══════════════════════════════════════════════════════════════════════════════

/// Adaptive worker count tuner using hill climbing.
///
/// Observes throughput (tasks completed per interval) and adjusts the worker
/// count up or down, reversing direction when throughput drops. This is the
/// same strategy used by the .NET CLR ThreadPool and MeTTaTron's
/// `PriorityScheduler`.
///
/// ## Algorithm
///
/// 1. Observe throughput and update the exponential moving average (EMA).
/// 2. Compare current EMA with previous EMA.
/// 3. If throughput improved, continue in the same direction.
/// 4. If throughput worsened, reverse direction.
/// 5. Apply the step: `workers += direction * step_size`.
/// 6. Clamp to `[min_workers, max_workers]`.
///
/// ## Fixed-Point EMA
///
/// Throughput EMA is stored as `throughput * 1024` (10-bit fixed point)
/// to avoid floating-point atomics. The smoothing factor alpha = 0.25
/// (shift right 2) provides responsive but stable adaptation.
pub struct HillClimber {
    /// Current worker count.
    current_workers: AtomicU32,
    /// Minimum workers (floor for scaling down).
    min_workers: u32,
    /// Maximum workers (ceiling for scaling up).
    max_workers: u32,
    /// Exponential moving average of throughput (fixed-point: value * 1024).
    throughput_ema: AtomicU64,
    /// Previous EMA value for comparison (fixed-point: value * 1024).
    previous_ema: AtomicU64,
    /// Current direction: -1 (shrink), 0 (hold), or 1 (grow).
    direction: AtomicI32,
    /// Step size for worker count adjustments.
    step_size: AtomicU32,
}

impl std::fmt::Debug for HillClimber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HillClimber")
            .field("current_workers", &self.current_workers.load(Ordering::Relaxed))
            .field("min_workers", &self.min_workers)
            .field("max_workers", &self.max_workers)
            .field("throughput_ema", &self.throughput_ema.load(Ordering::Relaxed))
            .field("direction", &self.direction.load(Ordering::Relaxed))
            .field("step_size", &self.step_size.load(Ordering::Relaxed))
            .finish()
    }
}

/// Fixed-point scale factor for throughput EMA (10-bit: multiply by 1024).
const EMA_SCALE: u64 = 1024;

/// EMA smoothing weight numerator (alpha = ALPHA_NUM / ALPHA_DEN = 1/4).
const ALPHA_NUM: u64 = 1;
/// EMA smoothing weight denominator.
const ALPHA_DEN: u64 = 4;

impl HillClimber {
    /// Create a new hill climber with the given worker count bounds.
    ///
    /// Initial worker count is set to `min_workers`.
    /// Initial direction is `+1` (grow) — start optimistic.
    pub fn new(min_workers: u32, max_workers: u32) -> Result<Self, String> {
        if min_workers < 1 {
            return Err(format!("min_workers must be >= 1, got {}", min_workers));
        }
        if min_workers > max_workers {
            return Err(format!(
                "min_workers ({}) must be <= max_workers ({})",
                min_workers, max_workers
            ));
        }
        Ok(Self {
            current_workers: AtomicU32::new(min_workers),
            min_workers,
            max_workers,
            throughput_ema: AtomicU64::new(0),
            previous_ema: AtomicU64::new(0),
            direction: AtomicI32::new(1), // start growing
            step_size: AtomicU32::new(1),
        })
    }

    /// Observe a throughput measurement and update the EMA.
    ///
    /// Call this periodically (e.g., every 500ms) with the number of tasks
    /// completed in the last interval.
    pub fn observe_throughput(&self, tasks_completed: u64) {
        let scaled = tasks_completed.saturating_mul(EMA_SCALE);
        // EMA update: new_ema = alpha * sample + (1 - alpha) * old_ema
        // With alpha = 1/4: new_ema = sample/4 + old_ema*3/4
        let old_ema = self.throughput_ema.load(Ordering::Acquire);
        let new_ema = (ALPHA_NUM * scaled + (ALPHA_DEN - ALPHA_NUM) * old_ema) / ALPHA_DEN;

        // Save previous for comparison before updating.
        self.previous_ema.store(old_ema, Ordering::Release);
        self.throughput_ema.store(new_ema, Ordering::Release);
    }

    /// Suggest a new worker count based on the hill climbing algorithm.
    ///
    /// Compares current EMA with previous EMA:
    /// - If improved (current >= previous), continue in the same direction.
    /// - If worsened (current < previous), reverse direction.
    ///
    /// Returns the suggested worker count (clamped to bounds).
    pub fn suggest_worker_count(&self) -> u32 {
        let current_ema = self.throughput_ema.load(Ordering::Acquire);
        let prev_ema = self.previous_ema.load(Ordering::Acquire);
        let current = self.current_workers.load(Ordering::Acquire);
        let step = self.step_size.load(Ordering::Acquire);

        // Determine direction based on throughput trend.
        let dir = if current_ema >= prev_ema {
            // Throughput improved or held — continue in same direction.
            self.direction.load(Ordering::Acquire)
        } else {
            // Throughput worsened — reverse direction.
            let old_dir = self.direction.load(Ordering::Acquire);
            let new_dir = -old_dir;
            self.direction.store(new_dir, Ordering::Release);
            new_dir
        };

        // Apply step in the chosen direction.
        let suggested = if dir > 0 {
            current.saturating_add(step)
        } else if dir < 0 {
            current.saturating_sub(step)
        } else {
            current
        };

        // Clamp to bounds.
        let clamped = suggested.clamp(self.min_workers, self.max_workers);
        self.current_workers.store(clamped, Ordering::Release);
        clamped
    }

    /// Current worker count.
    pub fn current_workers(&self) -> u32 {
        self.current_workers.load(Ordering::Acquire)
    }

    /// Current throughput EMA (fixed-point, divide by 1024 for real value).
    pub fn throughput_ema_raw(&self) -> u64 {
        self.throughput_ema.load(Ordering::Acquire)
    }

    /// Current direction: -1 (shrink), 0 (hold), +1 (grow).
    pub fn direction(&self) -> i32 {
        self.direction.load(Ordering::Acquire)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GlobalPool — Process-wide singleton
// ══════════════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════════════
// PoolRuntime — Live thread handles for the M:N scheduler
// ══════════════════════════════════════════════════════════════════════════════

/// Live runtime state for the M:N thread pool.
///
/// Created by [`GlobalPool::start()`] and stored in the pool's `runtime`
/// field. Contains the coordinator thread and worker pool handles.
/// Cleaned up by [`GlobalPool::stop()`].
struct PoolRuntime {
    /// The coordinator thread (owns the Scheduler FSM).
    coordinator: Coordinator,
    /// The worker pool (N native threads with work-stealing deques).
    worker_pool: Arc<WorkerPool>,
    // 2026-05-12: `registry` and `channels` fields DELETED — they were
    // stored here but never read. The Coordinator and WorkerPool already
    // hold their own internal Arc<GreenThreadRegistry> / Arc<ChannelMap>
    // clones passed at construction time, so dropping the redundant
    // PoolRuntime-side clone has no Drop / liveness impact.
}

// PoolRuntime contains JoinHandle<()> (via Coordinator and WorkerPool).
// JoinHandle<()> is Send but not Sync. We guard PoolRuntime behind
// Mutex<Option<PoolRuntime>> in GlobalPool, so Send is sufficient.
// SAFETY: PoolRuntime is only accessed under the Mutex lock.
unsafe impl Send for PoolRuntime {}

/// Process-wide singleton for the green thread pool.
///
/// Manages native worker threads shared across all MeTTaIL language instances.
/// Each language registers its scheduler via `register_scheduler()` for
/// cross-language coordination and adaptive scaling.
///
/// ## Initialization
///
/// Uses `OnceLock` for thread-safe one-shot initialization. The first call
/// to `get_or_init()` creates the pool; subsequent calls return the same
/// instance.
///
/// ## Lifecycle
///
/// 1. `get_or_init()` → creates the singleton (no threads spawned yet).
/// 2. `start()` → spawns coordinator + N worker threads.
/// 3. `inject()` / `submit()` → push green threads for execution.
/// 4. `stop()` → signal shutdown, drain work, join all threads.
///
/// ## Budget
///
/// The `parallel_budget` is a shared `AtomicU32` that all language schedulers
/// compete for via CAS. When a scheduler wants to spawn a green thread on a
/// native worker, it calls `try_consume_budget()`. When the thread completes,
/// the budget is replenished via `replenish_budget()`.
pub struct GlobalPool {
    /// Number of native worker threads.
    worker_count: usize,
    /// Shared fork budget across all languages.
    parallel_budget: AtomicU32,
    /// Whether the pool is active (false after shutdown).
    active: AtomicBool,
    /// Per-language scheduler handles, keyed by language ID.
    language_schedulers: DashMap<u64, Arc<dyn AnyScheduler>>,
    /// Runtime metrics.
    metrics: GlobalPoolMetrics,
    /// Adaptive worker count tuner.
    hill_climber: HillClimber,
    /// Live runtime state (populated after `start()`, None before).
    runtime: Mutex<Option<PoolRuntime>>,
}

impl std::fmt::Debug for GlobalPool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let runtime_started = self
            .runtime
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false);
        f.debug_struct("GlobalPool")
            .field("worker_count", &self.worker_count)
            .field("parallel_budget", &self.parallel_budget.load(Ordering::Relaxed))
            .field("active", &self.active.load(Ordering::Relaxed))
            .field("registered_languages", &self.language_schedulers.len())
            .field("runtime_started", &runtime_started)
            .finish()
    }
}

/// The process-global singleton.
static GLOBAL_POOL: OnceLock<GlobalPool> = OnceLock::new();

impl GlobalPool {
    /// Get or initialize the global pool singleton.
    ///
    /// The first call creates the pool with `num_cpus::get()` workers and
    /// a parallel budget equal to `2 * num_cpus`. Subsequent calls return
    /// the same instance.
    pub fn get_or_init() -> &'static GlobalPool {
        GLOBAL_POOL.get_or_init(|| {
            let cpus = num_cpus::get();
            let budget = (cpus * 2) as u32;
            GlobalPool {
                worker_count: cpus,
                parallel_budget: AtomicU32::new(budget),
                active: AtomicBool::new(true),
                language_schedulers: DashMap::new(),
                metrics: GlobalPoolMetrics::new(),
                hill_climber: HillClimber::new(1, cpus as u32).expect("valid hill climber bounds"),
                runtime: Mutex::new(None),
            }
        })
    }

    /// Create a GlobalPool with explicit configuration (for testing).
    ///
    /// This does NOT register in the global singleton — use `get_or_init()`
    /// for production code. This constructor is `pub(crate)` to allow tests
    /// to create isolated pool instances without polluting the global state.
    #[cfg(test)]
    pub(crate) fn new_isolated(worker_count: usize, budget: u32) -> Self {
        GlobalPool {
            worker_count,
            parallel_budget: AtomicU32::new(budget),
            active: AtomicBool::new(true),
            language_schedulers: DashMap::new(),
            metrics: GlobalPoolMetrics::new(),
            hill_climber: HillClimber::new(1, worker_count.max(1) as u32)
                .expect("valid hill climber bounds"),
            runtime: Mutex::new(None),
        }
    }

    /// Register a language-specific scheduler with the global pool.
    ///
    /// The scheduler is stored as `Arc<dyn AnyScheduler>` for shared access.
    /// If a scheduler with the same language ID is already registered, it is
    /// replaced (old one dropped).
    pub fn register_scheduler(&self, id: u64, scheduler: Arc<dyn AnyScheduler>) {
        self.language_schedulers.insert(id, scheduler);
    }

    /// Unregister a language scheduler by its ID.
    ///
    /// Returns the removed scheduler if it existed, `None` otherwise.
    pub fn unregister_scheduler(&self, id: u64) -> Option<Arc<dyn AnyScheduler>> {
        self.language_schedulers.remove(&id).map(|(_, v)| v)
    }

    /// Reference to the shared parallel budget.
    pub fn parallel_budget(&self) -> &AtomicU32 {
        &self.parallel_budget
    }

    /// Atomically try to consume one unit of the parallel budget.
    ///
    /// Uses a CAS loop to decrement the budget if it is > 0.
    /// Returns `true` if a unit was consumed, `false` if budget is exhausted.
    pub fn try_consume_budget(&self) -> bool {
        self.parallel_budget
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |v| {
                if v > 0 {
                    Some(v - 1)
                } else {
                    None
                }
            })
            .is_ok()
    }

    /// Replenish the parallel budget by `amount` units.
    ///
    /// Called when green threads complete execution, freeing up worker slots.
    pub fn replenish_budget(&self, amount: u32) {
        self.parallel_budget.fetch_add(amount, Ordering::Release);
    }

    /// Number of native worker threads.
    pub fn worker_count(&self) -> usize {
        self.worker_count
    }

    /// Whether the pool is active (not shut down).
    pub fn is_active(&self) -> bool {
        self.active.load(Ordering::Acquire)
    }

    /// Shut down the global pool.
    ///
    /// Sets the active flag to `false` and clears all registered schedulers.
    /// This is a soft shutdown — native worker threads are not joined here
    /// (they check the active flag and exit on their own).
    pub fn shutdown(&self) {
        self.active.store(false, Ordering::Release);
        self.language_schedulers.clear();
    }

    /// Start the M:N thread pool runtime.
    ///
    /// Spawns the coordinator thread and N worker threads. The coordinator
    /// owns the `Scheduler` FSM and dispatches work to workers. Workers
    /// use crossbeam-deque work-stealing for load balancing.
    ///
    /// The `registry` and `channels` are shared with the caller for
    /// spawning green threads and creating channels.
    ///
    /// # Panics
    ///
    /// Panics if the runtime is already started. Call `stop()` first.
    pub fn start(&self, registry: Arc<GreenThreadRegistry>, channels: Arc<ChannelMap>) {
        let mut runtime_guard = self
            .runtime
            .lock()
            .expect("GlobalPool runtime mutex poisoned");
        assert!(runtime_guard.is_none(), "GlobalPool runtime already started; call stop() first");

        let shutdown = Arc::new(AtomicBool::new(false));

        let scheduler = Scheduler::with_budget(
            Arc::clone(&registry),
            Arc::clone(&channels),
            self.parallel_budget.load(Ordering::Relaxed),
        );

        let hill_climber = Arc::new(
            HillClimber::new(1, self.worker_count.max(1) as u32)
                .expect("valid hill climber bounds"),
        );

        // Create the MPSC channel first. Workers get report_tx to send
        // events; coordinator gets report_rx to receive them.
        let (report_tx, report_rx) = crossbeam_channel::unbounded();

        // Create worker pool (workers use report_tx to send to coordinator).
        let worker_pool = Arc::new(WorkerPool::new(
            WorkerPoolConfig {
                num_workers: self.worker_count,
                quantum_size: WorkerPoolConfig::default_quantum(),
            },
            Arc::clone(&registry),
            report_tx.clone(),
        ));

        // Spawn coordinator (receives worker reports via report_rx,
        // dispatches work to worker_pool).
        let coordinator = Coordinator::spawn(
            scheduler,
            Arc::clone(&registry),
            Arc::clone(&channels),
            Arc::clone(&worker_pool),
            Arc::clone(&hill_climber),
            Arc::clone(&shutdown),
            report_rx,
            report_tx,
            CoordinatorConfig::default(),
        );

        *runtime_guard = Some(PoolRuntime { coordinator, worker_pool });
        // registry + channels Arc handles are held internally by
        // Coordinator and WorkerPool; the PoolRuntime-side clones were
        // never read and have been removed.
        let _ = (registry, channels);
    }

    /// Stop the M:N thread pool runtime.
    ///
    /// Signals shutdown to all threads, waits for the coordinator and
    /// workers to exit, and cleans up the runtime state.
    ///
    /// No-op if the runtime is not started.
    pub fn stop(&self) {
        let mut runtime_guard = self
            .runtime
            .lock()
            .expect("GlobalPool runtime mutex poisoned");
        if let Some(mut runtime) = runtime_guard.take() {
            runtime.coordinator.shutdown();
            // Worker pool threads will exit on the shutdown flag.
            // We use Arc, so we can't call shutdown() which takes ownership.
            // Instead, the workers check their shutdown flag and exit.
        }
        self.active.store(false, Ordering::Release);
    }

    /// Submit a green thread for execution by the M:N scheduler.
    ///
    /// Pushes the thread ID to the worker pool's global injector and
    /// wakes a parked worker. The thread must already be in the registry
    /// and in `Ready` state.
    ///
    /// Returns `true` if the runtime is active, `false` otherwise.
    pub fn submit(&self, thread_id: crate::channel::GreenThreadId) -> bool {
        let runtime_guard = self
            .runtime
            .lock()
            .expect("GlobalPool runtime mutex poisoned");
        if let Some(runtime) = runtime_guard.as_ref() {
            runtime.worker_pool.inject(thread_id);
            runtime.worker_pool.unpark_one();
            true
        } else {
            false
        }
    }

    /// Whether the M:N runtime is currently started.
    pub fn is_runtime_started(&self) -> bool {
        self.runtime
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false)
    }

    /// Reference to the global pool metrics.
    pub fn metrics(&self) -> &GlobalPoolMetrics {
        &self.metrics
    }

    /// Reference to the hill climber for adaptive scaling.
    pub fn hill_climber(&self) -> &HillClimber {
        &self.hill_climber
    }

    /// Number of currently registered language schedulers.
    pub fn registered_scheduler_count(&self) -> usize {
        self.language_schedulers.len()
    }

    /// Tick all registered schedulers, returning total actions taken.
    ///
    /// Used by the global pool driver to poll all languages in round-robin.
    pub fn tick_all(&self) -> usize {
        let mut total = 0;
        for entry in self.language_schedulers.iter() {
            total += entry.value().tick();
        }
        if total > 0 {
            self.metrics
                .total_tasks_executed
                .fetch_add(total as u64, Ordering::Relaxed);
        }
        total
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    /// A test scheduler that reports a fixed number of runnable threads.
    struct TestScheduler {
        id: u64,
        runnable: AtomicBool,
        tick_count: AtomicU64,
    }

    impl TestScheduler {
        fn new(id: u64) -> Self {
            Self {
                id,
                runnable: AtomicBool::new(false),
                tick_count: AtomicU64::new(0),
            }
        }

        fn set_runnable(&self, v: bool) {
            self.runnable.store(v, Ordering::Release);
        }
    }

    impl AnyScheduler for TestScheduler {
        fn language_id(&self) -> u64 {
            self.id
        }

        fn has_runnable(&self) -> bool {
            self.runnable.load(Ordering::Acquire)
        }

        fn tick(&self) -> usize {
            self.tick_count.fetch_add(1, Ordering::Relaxed);
            if self.has_runnable() {
                1
            } else {
                0
            }
        }
    }

    // ── GlobalPool Singleton ─────────────────────────────────────────────

    #[test]
    fn test_get_or_init_returns_same_instance() {
        let pool1 = GlobalPool::get_or_init();
        let pool2 = GlobalPool::get_or_init();
        // Same pointer.
        assert!(std::ptr::eq(pool1, pool2));
    }

    #[test]
    fn test_get_or_init_is_active() {
        let pool = GlobalPool::get_or_init();
        // The singleton may have been shut down by another test, but it
        // should exist and be accessible. We just check it doesn't panic.
        let _ = pool.is_active();
    }

    // ── Register / Unregister ────────────────────────────────────────────

    #[test]
    fn test_register_and_unregister_scheduler() {
        let pool = GlobalPool::new_isolated(4, 8);
        let sched = Arc::new(TestScheduler::new(42));

        pool.register_scheduler(42, sched);
        assert_eq!(pool.registered_scheduler_count(), 1);

        let removed = pool.unregister_scheduler(42);
        assert!(removed.is_some());
        assert_eq!(pool.registered_scheduler_count(), 0);
    }

    #[test]
    fn test_unregister_nonexistent() {
        let pool = GlobalPool::new_isolated(4, 8);
        let removed = pool.unregister_scheduler(999);
        assert!(removed.is_none());
    }

    #[test]
    fn test_register_replaces_existing() {
        let pool = GlobalPool::new_isolated(4, 8);
        let sched1 = Arc::new(TestScheduler::new(1));
        let sched2 = Arc::new(TestScheduler::new(1));

        pool.register_scheduler(1, sched1);
        pool.register_scheduler(1, sched2);
        // Should still be 1 entry.
        assert_eq!(pool.registered_scheduler_count(), 1);
    }

    // ── Budget ───────────────────────────────────────────────────────────

    #[test]
    fn test_budget_consume_success() {
        let pool = GlobalPool::new_isolated(4, 3);
        assert!(pool.try_consume_budget());
        assert!(pool.try_consume_budget());
        assert!(pool.try_consume_budget());
        // Budget exhausted.
        assert!(!pool.try_consume_budget());
    }

    #[test]
    fn test_budget_replenish() {
        let pool = GlobalPool::new_isolated(4, 1);
        assert!(pool.try_consume_budget());
        assert!(!pool.try_consume_budget()); // exhausted

        pool.replenish_budget(2);
        assert!(pool.try_consume_budget());
        assert!(pool.try_consume_budget());
        assert!(!pool.try_consume_budget());
    }

    #[test]
    fn test_budget_atomic_pointer() {
        let pool = GlobalPool::new_isolated(4, 10);
        let budget = pool.parallel_budget();
        assert_eq!(budget.load(Ordering::Relaxed), 10);
    }

    // ── Shutdown ─────────────────────────────────────────────────────────

    #[test]
    fn test_shutdown_flag() {
        let pool = GlobalPool::new_isolated(4, 8);
        assert!(pool.is_active());

        pool.shutdown();
        assert!(!pool.is_active());
    }

    #[test]
    fn test_shutdown_clears_schedulers() {
        let pool = GlobalPool::new_isolated(4, 8);
        let sched = Arc::new(TestScheduler::new(1));
        pool.register_scheduler(1, sched);
        assert_eq!(pool.registered_scheduler_count(), 1);

        pool.shutdown();
        assert_eq!(pool.registered_scheduler_count(), 0);
    }

    // ── HillClimber ──────────────────────────────────────────────────────

    #[test]
    fn test_hill_climber_initial_state() {
        let hc = HillClimber::new(2, 16).expect("valid bounds");
        assert_eq!(hc.current_workers(), 2);
        assert_eq!(hc.direction(), 1); // starts growing
    }

    #[test]
    fn test_hill_climber_observe_throughput_updates_ema() {
        let hc = HillClimber::new(2, 16).expect("valid bounds");

        // Initially EMA is 0.
        assert_eq!(hc.throughput_ema_raw(), 0);

        // Observe 100 tasks.
        hc.observe_throughput(100);
        // EMA = (1/4 * 100*1024 + 3/4 * 0) = 25600
        assert_eq!(hc.throughput_ema_raw(), 100 * EMA_SCALE / 4);
    }

    #[test]
    fn test_hill_climber_suggest_grows_when_throughput_improves() {
        let hc = HillClimber::new(2, 16).expect("valid bounds");

        // First observation: throughput 100.
        hc.observe_throughput(100);
        let w1 = hc.suggest_worker_count();
        // Direction is +1, step is 1: 2 + 1 = 3.
        assert_eq!(w1, 3);

        // Second observation: throughput 200 (higher).
        hc.observe_throughput(200);
        let w2 = hc.suggest_worker_count();
        // EMA improved, direction stays +1: 3 + 1 = 4.
        assert_eq!(w2, 4);
    }

    #[test]
    fn test_hill_climber_reverses_on_throughput_drop() {
        let hc = HillClimber::new(2, 16).expect("valid bounds");

        // Build up EMA with high throughput.
        hc.observe_throughput(1000);
        let _ = hc.suggest_worker_count(); // grows to 3
        hc.observe_throughput(1000);
        let _ = hc.suggest_worker_count(); // grows to 4

        // Now throughput drops sharply.
        hc.observe_throughput(0);
        let w = hc.suggest_worker_count();
        // EMA dropped, direction reversed to -1: 4 - 1 = 3.
        assert!(w < 5, "Expected shrink but got {}", w);
    }

    #[test]
    fn test_hill_climber_clamps_to_bounds() {
        let hc = HillClimber::new(2, 4).expect("valid bounds");

        // Grow past max.
        hc.observe_throughput(1000);
        let _ = hc.suggest_worker_count(); // 3
        hc.observe_throughput(2000);
        let _ = hc.suggest_worker_count(); // 4
        hc.observe_throughput(3000);
        let w = hc.suggest_worker_count();
        assert_eq!(w, 4, "Should clamp to max_workers=4");

        // Force direction to -1 to test min clamp.
        hc.direction.store(-1, Ordering::Release);
        hc.current_workers.store(2, Ordering::Release);
        // Need current_ema >= prev_ema so direction stays -1 (not reversed).
        hc.previous_ema.store(1, Ordering::Release);
        hc.throughput_ema.store(1, Ordering::Release);
        let w = hc.suggest_worker_count();
        assert_eq!(w, 2, "Should clamp to min_workers=2");
    }

    #[test]
    fn test_hill_climber_panics_on_zero_min() {
        let err = HillClimber::new(0, 4).unwrap_err();
        assert!(err.contains("min_workers must be >= 1"), "{err}");
    }

    #[test]
    fn test_hill_climber_panics_on_inverted_bounds() {
        let err = HillClimber::new(8, 4).unwrap_err();
        assert!(err.contains("min_workers (8) must be <= max_workers (4)"), "{err}");
    }

    // ── Tick All ─────────────────────────────────────────────────────────

    #[test]
    fn test_tick_all_drives_schedulers() {
        let pool = GlobalPool::new_isolated(4, 8);
        let sched1 = Arc::new(TestScheduler::new(1));
        let sched2 = Arc::new(TestScheduler::new(2));
        sched1.set_runnable(true);
        sched2.set_runnable(false);

        pool.register_scheduler(1, sched1);
        pool.register_scheduler(2, sched2);

        let total = pool.tick_all();
        // sched1 has runnable, returns 1; sched2 has none, returns 0.
        assert_eq!(total, 1);

        let snap = pool.metrics().snapshot();
        assert_eq!(snap.total_tasks_executed, 1);
    }

    #[test]
    fn test_tick_all_empty() {
        let pool = GlobalPool::new_isolated(4, 8);
        let total = pool.tick_all();
        assert_eq!(total, 0);
    }

    // ── Metrics ──────────────────────────────────────────────────────────

    #[test]
    fn test_metrics_snapshot_initial() {
        let pool = GlobalPool::new_isolated(4, 8);
        let snap = pool.metrics().snapshot();
        assert_eq!(snap.total_tasks_executed, 0);
        assert_eq!(snap.total_cross_language_steals, 0);
        assert_eq!(snap.peak_worker_utilization, 0);
    }

    // ── Worker Count ─────────────────────────────────────────────────────

    #[test]
    fn test_worker_count() {
        let pool = GlobalPool::new_isolated(8, 16);
        assert_eq!(pool.worker_count(), 8);
    }

    // ── Debug Format ─────────────────────────────────────────────────────

    #[test]
    fn test_debug_format() {
        let pool = GlobalPool::new_isolated(4, 8);
        let debug = format!("{:?}", pool);
        assert!(debug.contains("GlobalPool"));
        assert!(debug.contains("worker_count: 4"));
    }
}
