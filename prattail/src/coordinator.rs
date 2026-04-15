//! Coordinator Thread — Scheduling layer for the M:N green thread runtime.
//!
//! The coordinator runs on its own native thread, exclusively owns the
//! `Scheduler` FSM, and acts as the single control point for:
//!
//! 1. Processing worker reports (completions, suspensions, forks, failures).
//! 2. Translating `SchedulerAction`s into concrete operations (inject work,
//!    wake workers, replenish budget).
//! 3. Periodically checking channel waiters via the `WakeRegistry`.
//! 4. Adaptively scaling the worker count via `HillClimber`.
//!
//! ## Event Loop
//!
//! ```text
//!   Workers ──MPSC──→ Coordinator ──→ Scheduler FSM ──→ Actions
//!                         │                                │
//!                         │◀── inject/unpark/budget ───────┘
//!                         │
//!                         ├── periodic: check WakeRegistry
//!                         └── periodic: HillClimber scale check
//! ```
//!
//! ## Design: Coordinator Owns Scheduler
//!
//! The `Scheduler` uses `&mut self` for `process_event()` and `enqueue()`.
//! Instead of wrapping it in a `Mutex`, the coordinator thread moves the
//! `Scheduler` into its closure and is the sole caller. Workers communicate
//! via the lock-free MPSC channel, never touching the Scheduler directly.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use crossbeam_channel::{Receiver, RecvTimeoutError, Sender};

use crate::channel::{ChannelId, ChannelMap, GreenThreadId, WakeRegistry};
use crate::global_pool::HillClimber;
use crate::green_thread::{CekThreadState, GreenThreadRegistry};
use crate::pool_fsm::WorkerReport;
use crate::scheduler::{Scheduler, SchedulerAction, SchedulerEvent};
use crate::worker_pool::{WorkerPool, WorkerPoolConfig};

// ══════════════════════════════════════════════════════════════════════════════
// Coordinator Configuration
// ══════════════════════════════════════════════════════════════════════════════

/// Configuration for the coordinator thread.
pub struct CoordinatorConfig {
    /// Timeout for `recv_timeout` on the event channel (milliseconds).
    /// Shorter values increase responsiveness but also CPU usage.
    pub poll_interval_ms: u64,
    /// Interval between HillClimber scale checks (milliseconds).
    pub scale_check_interval_ms: u64,
    /// Interval between WakeRegistry checks (milliseconds).
    pub wake_check_interval_ms: u64,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        Self {
            poll_interval_ms: 10,
            scale_check_interval_ms: 500,
            // Polling is now a fallback: event-driven wake-ups via
            // WorkerReport::ChannelActivity handle the fast path.
            wake_check_interval_ms: 500,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Coordinator — Scheduling thread
// ══════════════════════════════════════════════════════════════════════════════

/// The coordinator thread that drives the M:N scheduler.
///
/// Owns the `Scheduler` FSM exclusively (no sharing, no Mutex). Receives
/// worker reports via MPSC channel, processes them through the Scheduler,
/// and dispatches the resulting actions (inject work, wake workers, etc.).
pub struct Coordinator {
    /// Handle to the coordinator's native thread.
    handle: Option<JoinHandle<()>>,
    /// MPSC sender for workers to report events to the coordinator.
    /// Clone this for each worker thread.
    report_tx: Sender<WorkerReport>,
    /// Cooperative shutdown flag (shared with workers).
    shutdown: Arc<AtomicBool>,
}

impl Coordinator {
    /// Spawn the coordinator thread.
    ///
    /// The coordinator takes exclusive ownership of the `Scheduler` and runs
    /// an event loop that:
    /// 1. Receives worker reports via MPSC channel.
    /// 2. Processes them through the Scheduler FSM.
    /// 3. Dispatches resulting actions (inject work, wake workers, etc.).
    /// 4. Periodically checks the WakeRegistry for channel wake-ups.
    /// 5. Periodically consults the HillClimber for scaling decisions.
    ///
    /// # Channel Setup
    ///
    /// The caller creates the MPSC channel and passes `report_rx` here.
    /// The corresponding `report_tx` is given to workers via `WorkerPool::new()`.
    /// This avoids the circular dependency: coordinator needs WorkerPool,
    /// WorkerPool needs coordinator's report_tx.
    pub fn spawn(
        mut scheduler: Scheduler,
        registry: Arc<GreenThreadRegistry>,
        channels: Arc<ChannelMap>,
        worker_pool: Arc<WorkerPool>,
        hill_climber: Arc<HillClimber>,
        shutdown: Arc<AtomicBool>,
        report_rx: Receiver<WorkerReport>,
        report_tx: Sender<WorkerReport>,
        config: CoordinatorConfig,
    ) -> Self {
        let shutdown_clone = Arc::clone(&shutdown);
        let report_tx_clone = report_tx.clone();

        let handle = std::thread::Builder::new()
            .name("prattail-coordinator".to_string())
            .spawn(move || {
                coordinator_loop(
                    &mut scheduler,
                    &registry,
                    &channels,
                    &worker_pool,
                    &hill_climber,
                    &shutdown_clone,
                    &report_rx,
                    &report_tx_clone,
                    &config,
                );
            })
            .expect("failed to spawn coordinator thread");

        Self {
            handle: Some(handle),
            report_tx,
            shutdown,
        }
    }

    /// Get a clone of the report sender for additional workers.
    pub fn report_sender(&self) -> Sender<WorkerReport> {
        self.report_tx.clone()
    }

    /// Signal shutdown and join the coordinator thread.
    pub fn shutdown(&mut self) {
        self.shutdown.store(true, Ordering::Release);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }

    /// Whether the coordinator has been shut down.
    pub fn is_shutdown(&self) -> bool {
        self.handle.is_none()
    }
}

impl std::fmt::Debug for Coordinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Coordinator")
            .field("running", &self.handle.is_some())
            .field("shutdown", &self.shutdown.load(Ordering::Relaxed))
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Coordinator Event Loop
// ══════════════════════════════════════════════════════════════════════════════

/// Main event loop for the coordinator thread.
fn coordinator_loop(
    scheduler: &mut Scheduler,
    registry: &Arc<GreenThreadRegistry>,
    channels: &ChannelMap,
    worker_pool: &WorkerPool,
    hill_climber: &HillClimber,
    shutdown: &AtomicBool,
    report_rx: &Receiver<WorkerReport>,
    report_tx: &Sender<WorkerReport>,
    config: &CoordinatorConfig,
) {
    let wake_registry = WakeRegistry::new();
    // Join-pattern tracking: maps thread_id → full set of channels in its join pattern.
    // Populated when a ThreadSuspended report arrives with >1 channels.
    let mut join_sets: HashMap<GreenThreadId, Vec<ChannelId>> = HashMap::new();
    let mut tasks_completed_since_last: u64 = 0;
    let mut last_scale_check = Instant::now();
    let mut last_wake_check = Instant::now();

    let poll_timeout = Duration::from_millis(config.poll_interval_ms);
    let scale_interval = Duration::from_millis(config.scale_check_interval_ms);
    let wake_interval = Duration::from_millis(config.wake_check_interval_ms);

    loop {
        if shutdown.load(Ordering::Relaxed) {
            // Drain remaining events before exiting.
            while let Ok(report) = report_rx.try_recv() {
                handle_worker_report(
                    scheduler,
                    &report,
                    registry,
                    channels,
                    worker_pool,
                    &wake_registry,
                    &mut join_sets,
                    &mut tasks_completed_since_last,
                );
            }
            break;
        }

        // Process a worker report (with timeout for periodic tasks).
        match report_rx.recv_timeout(poll_timeout) {
            Ok(report) => {
                handle_worker_report(
                    scheduler,
                    &report,
                    registry,
                    channels,
                    worker_pool,
                    &wake_registry,
                    &mut join_sets,
                    &mut tasks_completed_since_last,
                );
            }
            Err(RecvTimeoutError::Timeout) => {
                // No reports — run periodic tasks below.
            }
            Err(RecvTimeoutError::Disconnected) => {
                // All senders dropped — workers are gone.
                break;
            }
        }

        // Periodic: check WakeRegistry for channel wake-ups (fallback polling).
        if last_wake_check.elapsed() >= wake_interval {
            // Single-channel waiters.
            let to_wake = wake_registry.check_and_wake(channels);
            for (thread_id, _channel_id) in to_wake {
                resume_and_dispatch(thread_id, registry, scheduler, worker_pool);
            }

            // Join-pattern waiters: wake only when ALL channels have pending messages.
            if !join_sets.is_empty() {
                let join_wakes =
                    wake_registry.check_and_wake_join(channels, &join_sets);
                for (thread_id, _channel_id) in &join_wakes {
                    join_sets.remove(thread_id);
                    resume_and_dispatch(*thread_id, registry, scheduler, worker_pool);
                }
            }

            last_wake_check = Instant::now();
        }

        // Periodic: HillClimber scale check.
        if last_scale_check.elapsed() >= scale_interval {
            hill_climber.observe_throughput(tasks_completed_since_last);
            let suggested = hill_climber.suggest_worker_count() as usize;
            let current = worker_pool.num_workers();
            if suggested > current {
                // Grow-only: spawn additional workers to match HillClimber suggestion.
                // Shrinking is not supported (see worker_pool::grow() docs).
                worker_pool.grow(
                    suggested - current,
                    Arc::clone(registry),
                    report_tx.clone(),
                    WorkerPoolConfig::default_quantum(),
                );
            }
            tasks_completed_since_last = 0;
            last_scale_check = Instant::now();
        }

        // Run scheduler tick to process any pending dispatch.
        let actions = scheduler.tick();
        execute_scheduler_actions(&actions, worker_pool, registry, scheduler);
    }
}

/// Resume a suspended thread and dispatch it via the scheduler.
///
/// Transitions the thread from Suspended to Ready, enqueues it in the
/// scheduler, and dispatches ready threads to the worker pool.
fn resume_and_dispatch(
    thread_id: GreenThreadId,
    registry: &GreenThreadRegistry,
    scheduler: &mut Scheduler,
    worker_pool: &WorkerPool,
) {
    if let Some(mut thread) = registry.get_mut(thread_id) {
        if matches!(thread.state, CekThreadState::Suspended { .. }) {
            thread.resume();
            let priority = thread.priority;
            drop(thread);

            scheduler.enqueue(thread_id, priority);
            dispatch_ready_threads(scheduler, worker_pool);
        }
    }
}

/// Handle a single worker report by forwarding to the Scheduler FSM
/// and executing the resulting actions.
fn handle_worker_report(
    scheduler: &mut Scheduler,
    report: &WorkerReport,
    registry: &GreenThreadRegistry,
    channels: &ChannelMap,
    worker_pool: &WorkerPool,
    wake_registry: &WakeRegistry,
    join_sets: &mut HashMap<GreenThreadId, Vec<ChannelId>>,
    tasks_completed: &mut u64,
) {
    match report {
        WorkerReport::ThreadCompleted { thread_id, .. } => {
            let transition = scheduler.process_event(SchedulerEvent::ThreadCompleted {
                thread_id: *thread_id,
            });
            execute_scheduler_actions(&transition.actions, worker_pool, registry, scheduler);
            *tasks_completed += 1;
        }

        WorkerReport::ThreadSuspended {
            thread_id,
            waiting_on,
        } => {
            if waiting_on.len() > 1 {
                // Join pattern: register the thread's join set and register
                // the thread on each channel individually.
                join_sets.insert(*thread_id, waiting_on.clone());
                for channel_id in waiting_on {
                    wake_registry.register(*channel_id, *thread_id);
                }
            } else {
                // Single-channel waiter.
                for channel_id in waiting_on {
                    wake_registry.register(*channel_id, *thread_id);
                }
            }
        }

        WorkerReport::ForkRequested {
            parent_id,
            categories,
        } => {
            for category in categories {
                let transition = scheduler.process_event(SchedulerEvent::ForkRequest {
                    parent_id: *parent_id,
                    category: category.clone(),
                });
                execute_scheduler_actions(&transition.actions, worker_pool, registry, scheduler);
            }
        }

        WorkerReport::ThreadFailed { thread_id, .. } => {
            // Treat failure like completion for budget purposes.
            let transition = scheduler.process_event(SchedulerEvent::ThreadCompleted {
                thread_id: *thread_id,
            });
            execute_scheduler_actions(&transition.actions, worker_pool, registry, scheduler);
            *tasks_completed += 1;
        }

        WorkerReport::ThreadReady {
            thread_id,
            priority,
        } => {
            scheduler.enqueue(*thread_id, *priority);
            dispatch_ready_threads(scheduler, worker_pool);
        }

        WorkerReport::ChannelActivity { channel_ids } => {
            // Event-driven wake: immediately check affected channels for waiters.
            for ch_id in channel_ids {
                let waiters = wake_registry.take_waiters(*ch_id);
                for tid in waiters {
                    // If this thread has a join pattern, check if ALL its channels
                    // now have pending messages before waking it.
                    if let Some(join_channels) = join_sets.get(&tid) {
                        let all_ready = join_channels.iter().all(|jch| {
                            channels
                                .get_channel(*jch)
                                .map(|h| h.has_pending())
                                .unwrap_or(false)
                        });
                        if !all_ready {
                            // Re-register the waiter; not all join channels are ready.
                            wake_registry.register(*ch_id, tid);
                            continue;
                        }
                        // All join channels ready -- clean up join_sets and waiter registry.
                        let join_channels_clone = join_channels.clone();
                        join_sets.remove(&tid);
                        // Unregister from remaining join channels (we already took from ch_id).
                        for jch in &join_channels_clone {
                            if *jch != *ch_id {
                                wake_registry.unregister(*jch, tid);
                            }
                        }
                    }
                    resume_and_dispatch(tid, registry, scheduler, worker_pool);
                }
            }
        }
    }
}

/// Execute `SchedulerAction`s by translating them into concrete operations.
fn execute_scheduler_actions(
    actions: &[SchedulerAction],
    worker_pool: &WorkerPool,
    registry: &GreenThreadRegistry,
    scheduler: &mut Scheduler,
) {
    for action in actions {
        match action {
            SchedulerAction::WakeThread(thread_id) => {
                // Ensure thread is Ready before injecting.
                if let Some(thread) = registry.get(*thread_id) {
                    if thread.is_runnable() {
                        drop(thread);
                        worker_pool.inject(*thread_id);
                        worker_pool.unpark_one();
                    }
                }
            }

            SchedulerAction::SpawnThread { parent, category } => {
                if let Some(parent_id) = parent {
                    if let Some(child_id) =
                        registry.spawn_child(*parent_id, category.clone())
                    {
                        let priority = registry
                            .get(child_id)
                            .map(|t| t.priority)
                            .unwrap_or(0);
                        scheduler.enqueue(child_id, priority);
                        worker_pool.inject(child_id);
                        worker_pool.unpark_one();
                    }
                } else {
                    let child_id = registry.spawn(category.clone());
                    let priority = registry
                        .get(child_id)
                        .map(|t| t.priority)
                        .unwrap_or(0);
                    scheduler.enqueue(child_id, priority);
                    worker_pool.inject(child_id);
                    worker_pool.unpark_one();
                }
            }

            SchedulerAction::ParkWorkers => {
                // Workers self-park; no action needed from coordinator.
            }

            SchedulerAction::NotifyComplete { .. } => {
                // Completion notification — budget replenishment handled by scheduler.
            }

            SchedulerAction::EmitMetrics => {
                // Metrics emission — handled by the coordinator's periodic loop.
            }

            SchedulerAction::Dispatch {
                thread_id,
                quantum_size,
            } => {
                // Dispatch a thread to a worker with an adaptive quantum size.
                // The quantum_size is determined by the current BackpressureTier.
                worker_pool.inject(*thread_id);
                let _ = quantum_size; // Used by worker when executing the thread
            }
        }
    }
}

/// Dispatch all ready threads from the scheduler to the worker pool.
fn dispatch_ready_threads(scheduler: &mut Scheduler, worker_pool: &WorkerPool) {
    while scheduler.check_budget() {
        if let Some(thread_id) = scheduler.dequeue() {
            worker_pool.inject(thread_id);
            worker_pool.unpark_one();
        } else {
            scheduler.replenish_budget(1);
            break;
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::channel::ChannelCapacity;

    fn make_test_infra() -> (
        Arc<GreenThreadRegistry>,
        Arc<ChannelMap>,
        Arc<AtomicBool>,
        Arc<HillClimber>,
    ) {
        let registry = Arc::new(GreenThreadRegistry::new());
        let channels = Arc::new(ChannelMap::new());
        let shutdown = Arc::new(AtomicBool::new(false));
        let hill_climber = Arc::new(HillClimber::new(1, 4).expect("valid hill climber bounds"));
        (registry, channels, shutdown, hill_climber)
    }

    // ── Coordinator Spawn/Shutdown ──────────────────────────────────────

    #[test]
    fn test_coordinator_spawn_and_shutdown() {
        let (registry, channels, shutdown, hill_climber) = make_test_infra();

        let scheduler = Scheduler::with_budget(
            Arc::clone(&registry),
            Arc::clone(&channels),
            8,
        );

        let (report_tx, report_rx) = crossbeam_channel::unbounded();
        let pool = Arc::new(WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            report_tx.clone(),
        ));

        let mut coordinator = Coordinator::spawn(
            scheduler,
            registry,
            channels,
            pool,
            hill_climber,
            shutdown,
            report_rx,
            report_tx,
            CoordinatorConfig::default(),
        );

        assert!(!coordinator.is_shutdown());

        coordinator.shutdown();
        assert!(coordinator.is_shutdown());
    }

    // ── handle_worker_report Tests ──────────────────────────────────────

    #[test]
    fn test_handle_thread_completed() {
        let registry = GreenThreadRegistry::new();
        let channels = Arc::new(ChannelMap::new());
        let (report_tx, _rx) = crossbeam_channel::unbounded();
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::new(GreenThreadRegistry::new()),
            report_tx,
        );
        let wake_registry = WakeRegistry::new();
        let mut join_sets = HashMap::new();
        let mut scheduler = Scheduler::with_budget(
            Arc::new(GreenThreadRegistry::new()),
            Arc::clone(&channels),
            8,
        );

        let tid = registry.spawn("Expr".to_string());
        let mut completed = 0u64;

        handle_worker_report(
            &mut scheduler,
            &WorkerReport::ThreadCompleted {
                thread_id: tid,
                result: "done".to_string(),
            },
            &registry,
            &channels,
            &pool,
            &wake_registry,
            &mut join_sets,
            &mut completed,
        );

        assert_eq!(completed, 1, "completion should increment counter");
        pool.shutdown();
    }

    #[test]
    fn test_handle_thread_suspended_registers_waiter() {
        let registry = GreenThreadRegistry::new();
        let channels = Arc::new(ChannelMap::new());
        let (report_tx, _rx) = crossbeam_channel::unbounded();
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::new(GreenThreadRegistry::new()),
            report_tx,
        );
        let wake_registry = WakeRegistry::new();
        let mut join_sets = HashMap::new();
        let mut scheduler = Scheduler::with_budget(
            Arc::new(GreenThreadRegistry::new()),
            Arc::clone(&channels),
            8,
        );

        let tid = registry.spawn("Proc".to_string());
        let ch_id = ChannelId(42);
        let mut completed = 0u64;

        handle_worker_report(
            &mut scheduler,
            &WorkerReport::ThreadSuspended {
                thread_id: tid,
                waiting_on: vec![ch_id],
            },
            &registry,
            &channels,
            &pool,
            &wake_registry,
            &mut join_sets,
            &mut completed,
        );

        // Waiter should be registered.
        assert_eq!(wake_registry.total_waiters(), 1);
        assert_eq!(
            wake_registry.channels_with_waiters(),
            vec![ch_id]
        );
        // Single-channel waiter should NOT create a join_set entry.
        assert!(join_sets.is_empty(), "single-channel waiter should not create join set");

        pool.shutdown();
    }

    #[test]
    fn test_handle_thread_suspended_join_pattern() {
        let registry = GreenThreadRegistry::new();
        let channels = Arc::new(ChannelMap::new());
        let (report_tx, _rx) = crossbeam_channel::unbounded();
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::new(GreenThreadRegistry::new()),
            report_tx,
        );
        let wake_registry = WakeRegistry::new();
        let mut join_sets = HashMap::new();
        let mut scheduler = Scheduler::with_budget(
            Arc::new(GreenThreadRegistry::new()),
            Arc::clone(&channels),
            8,
        );

        let tid = registry.spawn("Proc".to_string());
        let ch_a = ChannelId(10);
        let ch_b = ChannelId(20);
        let mut completed = 0u64;

        handle_worker_report(
            &mut scheduler,
            &WorkerReport::ThreadSuspended {
                thread_id: tid,
                waiting_on: vec![ch_a, ch_b],
            },
            &registry,
            &channels,
            &pool,
            &wake_registry,
            &mut join_sets,
            &mut completed,
        );

        // Both channels should have the thread registered.
        assert_eq!(wake_registry.total_waiters(), 2);
        // join_sets should track the join pattern.
        assert_eq!(join_sets.len(), 1);
        assert_eq!(join_sets[&tid], vec![ch_a, ch_b]);

        pool.shutdown();
    }

    #[test]
    fn test_handle_channel_activity_wakes_single_waiter() {
        let registry = GreenThreadRegistry::new();
        let channels = Arc::new(ChannelMap::new());
        let (report_tx, _rx) = crossbeam_channel::unbounded();
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::new(GreenThreadRegistry::new()),
            report_tx,
        );
        let wake_registry = WakeRegistry::new();
        let mut join_sets = HashMap::new();
        let mut scheduler = Scheduler::with_budget(
            Arc::new(GreenThreadRegistry::new()),
            Arc::clone(&channels),
            8,
        );

        let tid = registry.spawn("Proc".to_string());
        let ch_id = ChannelId(42);

        // Transition thread to Suspended first.
        {
            let mut t = registry.get_mut(tid).expect("thread exists");
            t.state = CekThreadState::Running;
            t.suspend(vec![ch_id]);
        }

        // Register single-channel waiter.
        wake_registry.register(ch_id, tid);
        let mut completed = 0u64;

        // Process ChannelActivity — should wake the thread.
        handle_worker_report(
            &mut scheduler,
            &WorkerReport::ChannelActivity {
                channel_ids: vec![ch_id],
            },
            &registry,
            &channels,
            &pool,
            &wake_registry,
            &mut join_sets,
            &mut completed,
        );

        // The waiter should have been taken and thread resumed.
        assert_eq!(wake_registry.total_waiters(), 0);

        pool.shutdown();
    }

    // ── dispatch_ready_threads Tests ────────────────────────────────────

    #[test]
    fn test_dispatch_ready_threads() {
        let registry = Arc::new(GreenThreadRegistry::new());
        let channels = Arc::new(ChannelMap::new());
        let (report_tx, _rx) = crossbeam_channel::unbounded();
        let pool = WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 1,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            report_tx,
        );

        let mut scheduler = Scheduler::with_budget(
            Arc::clone(&registry),
            channels,
            4,
        );

        // Enqueue 3 threads.
        let t1 = registry.spawn("A".to_string());
        let t2 = registry.spawn("B".to_string());
        let t3 = registry.spawn("C".to_string());
        scheduler.enqueue(t1, 0);
        scheduler.enqueue(t2, 0);
        scheduler.enqueue(t3, 0);

        dispatch_ready_threads(&mut scheduler, &pool);

        // All 3 should have been dispatched (budget was 4).
        assert_eq!(scheduler.ready_count(), 0);

        pool.shutdown();
    }

    // ── End-to-End Integration Test ─────────────────────────────────────

    #[test]
    fn test_end_to_end_spawn_execute_complete() {
        let (registry, channels, shutdown, hill_climber) = make_test_infra();

        // Create a thread to execute (empty stacks → completes immediately).
        let tid = registry.spawn("Expr".to_string());

        let scheduler = Scheduler::with_budget(
            Arc::clone(&registry),
            Arc::clone(&channels),
            8,
        );

        // Create MPSC channel: workers send reports, coordinator reads them.
        let (report_tx, report_rx) = crossbeam_channel::unbounded();

        let pool = Arc::new(WorkerPool::new(
            WorkerPoolConfig {
                num_workers: 2,
                quantum_size: 100,
            },
            Arc::clone(&registry),
            report_tx.clone(),
        ));

        let mut coordinator = Coordinator::spawn(
            scheduler,
            Arc::clone(&registry),
            channels,
            Arc::clone(&pool),
            hill_climber,
            Arc::clone(&shutdown),
            report_rx,
            report_tx,
            CoordinatorConfig::default(),
        );

        // Inject the thread directly into the pool.
        pool.inject(tid);
        pool.unpark_one();

        // Wait for the thread to complete. The worker executes the quantum
        // (empty stacks → Completed), sends ThreadCompleted to coordinator.
        // The coordinator processes it via the scheduler FSM.
        // We verify by polling the thread's state in the registry.
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(thread) = registry.get(tid) {
                if thread.is_terminal() {
                    break;
                }
            }
            if Instant::now() > deadline {
                panic!("thread {} did not complete within 5 seconds", tid);
            }
            std::thread::sleep(Duration::from_millis(10));
        }

        // Verify the thread completed (not failed).
        let thread = registry.get(tid).expect("thread should exist");
        assert!(
            matches!(thread.state, CekThreadState::Completed { .. }),
            "expected Completed state, got {}",
            thread.state
        );

        // Clean shutdown.
        coordinator.shutdown();
        shutdown.store(true, Ordering::Release);
        pool.unpark_all();
    }

    // ── Channel Wake-Up Integration Test ────────────────────────────────

    #[test]
    fn test_wake_registry_integration() {
        let registry = GreenThreadRegistry::new();
        let channels = ChannelMap::new();
        let wake_registry = WakeRegistry::new();

        // Create a channel and a suspended thread.
        let ch_id =
            channels.create_channel::<String>("test_wake", &ChannelCapacity::Unbounded);
        let tid = registry.spawn("Proc".to_string());

        // Transition thread to Suspended.
        {
            let mut t = registry.get_mut(tid).expect("thread");
            t.state = CekThreadState::Running;
            t.suspend(vec![ch_id]);
        }

        // Register waiter.
        wake_registry.register(ch_id, tid);

        // No messages yet — check_and_wake should return empty.
        let to_wake = wake_registry.check_and_wake(&channels);
        assert!(to_wake.is_empty());

        // Send a message on the channel.
        let handle = channels.get_channel(ch_id).expect("channel exists");
        let ch = handle.downcast::<String>().expect("downcast");
        ch.send("hello".to_string()).expect("send");

        // Re-register (waiter was not consumed because channel was empty before).
        // Actually the waiter IS still registered because check_and_wake only
        // takes if has_pending returned true. Since it was empty, waiter stays.
        let to_wake = wake_registry.check_and_wake(&channels);
        assert_eq!(to_wake.len(), 1);
        assert_eq!(to_wake[0].0, tid);

        // Resume the thread.
        {
            let mut t = registry.get_mut(tid).expect("thread");
            t.resume();
        }
        assert!(registry.get(tid).expect("thread").is_runnable());
    }
}
