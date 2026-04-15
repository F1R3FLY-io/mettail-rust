//! Reactive State Machine types for the M:N green thread scheduler.
//!
//! Defines the FSM types for three new layers of the scheduling hierarchy,
//! composing with the existing `Scheduler` FSM in `scheduler.rs`:
//!
//! ```text
//! PoolFSM (lifecycle: start → run → shutdown)
//!   └─ CoordinatorFSM (scheduling decisions, owns Scheduler)
//!        └─ WorkerFSM (execution management per native thread)
//!             └─ GreenThread::run_quantum() (per-thread stepping)
//! ```
//!
//! Each layer follows the `State × Event → (State', Vec<Action>)` reactive
//! pattern established by the existing `Scheduler` FSM. Actions from one
//! layer become events for adjacent layers, forming a composable stack.
//!
//! ## Design Principles
//!
//! 1. **Pure FSMs**: `process_event()` is a pure function with no side effects.
//!    All side effects are expressed as `Action` values for the caller to execute.
//! 2. **Composable**: Worker actions produce Coordinator events; Coordinator
//!    actions produce Pool events. Each layer is testable in isolation.
//! 3. **Deterministic**: Same `(State, Event)` always produces the same
//!    `(State', Actions)`. Enables deterministic replay for debugging.
//!
//! ## Feature Gate
//!
//! All types require `feature = "green-threads"`.

use std::fmt;

use crate::channel::{ChannelId, GreenThreadId};
use crate::green_thread::QuantumResult;
use crate::scheduler::SchedulerEvent;

// ══════════════════════════════════════════════════════════════════════════════
// Worker FSM — Per-native-thread execution state machine
// ══════════════════════════════════════════════════════════════════════════════

/// Execution state of a single native worker thread.
///
/// ```text
///   Idle ──→ Executing ──→ Idle
///    │                       │
///    └──→ Parking ──→ Idle ──┘
///    │
///    └──→ Exiting
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerState {
    /// Not executing anything; attempting to find work
    /// (local deque → global injector → peer steal).
    Idle,
    /// Running a green thread quantum.
    Executing { thread_id: GreenThreadId },
    /// Parked on condvar — no work available from any source.
    Parking,
    /// Shutting down — will exit the worker loop.
    Exiting,
}

impl fmt::Display for WorkerState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Idle => write!(f, "Idle"),
            Self::Executing { thread_id } => write!(f, "Executing({})", thread_id),
            Self::Parking => write!(f, "Parking"),
            Self::Exiting => write!(f, "Exiting"),
        }
    }
}

/// Events that drive worker state transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerEvent {
    /// Found a green thread to execute (from local deque, injector, or steal).
    WorkFound(GreenThreadId),
    /// All work sources exhausted (local, injector, peers).
    NoWorkAvailable,
    /// A green thread quantum completed with the given result.
    QuantumComplete(QuantumResult),
    /// Woken from parking (new work injected or shutdown signal).
    Unpark,
    /// Cooperative shutdown signal.
    ShutdownSignal,
}

impl fmt::Display for WorkerEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WorkFound(tid) => write!(f, "WorkFound({})", tid),
            Self::NoWorkAvailable => write!(f, "NoWorkAvailable"),
            Self::QuantumComplete(r) => write!(f, "QuantumComplete({:?})", r),
            Self::Unpark => write!(f, "Unpark"),
            Self::ShutdownSignal => write!(f, "ShutdownSignal"),
        }
    }
}

/// Result of a worker FSM transition: new state + side-effect actions.
#[derive(Debug, Clone)]
pub struct WorkerTransition {
    /// The state to transition to.
    pub new_state: WorkerState,
    /// Side-effect actions for the worker loop to execute.
    pub actions: Vec<WorkerAction>,
}

/// Side-effect actions emitted by worker FSM transitions.
///
/// The worker loop executes these actions after each transition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerAction {
    /// Execute a quantum of the given green thread.
    ExecuteQuantum(GreenThreadId),
    /// Re-enqueue a green thread to the local deque (cooperative yield).
    ReenqueueLocal(GreenThreadId),
    /// Report an event to the coordinator via MPSC channel.
    ReportToCoordinator(WorkerReport),
    /// Fork children from a parent thread and enqueue them locally.
    ForkAndEnqueue {
        parent_id: GreenThreadId,
        categories: Vec<String>,
    },
    /// Park on condvar (no work available).
    Park,
    /// Exit the worker loop.
    Exit,
}

/// Messages sent from workers to the coordinator via MPSC channel.
///
/// These are the observable outcomes of green thread execution that
/// the coordinator needs to know about for scheduling decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerReport {
    /// A green thread completed successfully.
    ThreadCompleted {
        thread_id: GreenThreadId,
        result: String,
    },
    /// A green thread suspended waiting on channel(s).
    ThreadSuspended {
        thread_id: GreenThreadId,
        waiting_on: Vec<ChannelId>,
    },
    /// A green thread requested forking into children.
    ForkRequested {
        parent_id: GreenThreadId,
        categories: Vec<String>,
    },
    /// A green thread failed with an error.
    ThreadFailed {
        thread_id: GreenThreadId,
        error: String,
    },
    /// A green thread is ready to be scheduled (e.g., after channel wake-up).
    ThreadReady {
        thread_id: GreenThreadId,
        priority: u32,
    },
    /// Channel activity detected during quantum execution.
    /// Sent when a green thread performs channel sends, enabling
    /// event-driven wake-ups instead of polling.
    ChannelActivity {
        channel_ids: Vec<ChannelId>,
    },
}

impl fmt::Display for WorkerReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ThreadCompleted { thread_id, .. } => {
                write!(f, "ThreadCompleted({})", thread_id)
            }
            Self::ThreadSuspended {
                thread_id,
                waiting_on,
            } => write!(
                f,
                "ThreadSuspended({}, channels={})",
                thread_id,
                waiting_on.len()
            ),
            Self::ForkRequested {
                parent_id,
                categories,
            } => write!(
                f,
                "ForkRequested(parent={}, children={})",
                parent_id,
                categories.len()
            ),
            Self::ThreadFailed { thread_id, error } => {
                write!(f, "ThreadFailed({}, {})", thread_id, error)
            }
            Self::ThreadReady {
                thread_id,
                priority,
            } => write!(f, "ThreadReady({}, prio={})", thread_id, priority),
            Self::ChannelActivity { channel_ids } => {
                write!(f, "ChannelActivity(channels={})", channel_ids.len())
            }
        }
    }
}

/// Process a worker FSM event, returning the state transition.
///
/// Pure function: `(WorkerState, WorkerEvent) → (WorkerState', Vec<WorkerAction>)`
pub fn worker_process_event(state: &WorkerState, event: WorkerEvent) -> WorkerTransition {
    match (state, event) {
        // ── Idle transitions ────────────────────────────────────────────
        (WorkerState::Idle, WorkerEvent::WorkFound(tid)) => WorkerTransition {
            new_state: WorkerState::Executing {
                thread_id: tid,
            },
            actions: vec![WorkerAction::ExecuteQuantum(tid)],
        },
        (WorkerState::Idle, WorkerEvent::NoWorkAvailable) => WorkerTransition {
            new_state: WorkerState::Parking,
            actions: vec![WorkerAction::Park],
        },
        (WorkerState::Idle, WorkerEvent::ShutdownSignal) => WorkerTransition {
            new_state: WorkerState::Exiting,
            actions: vec![WorkerAction::Exit],
        },
        (WorkerState::Idle, WorkerEvent::Unpark) => {
            // Spurious wake-up while idle — stay idle, try to find work.
            WorkerTransition {
                new_state: WorkerState::Idle,
                actions: vec![],
            }
        }

        // ── Executing transitions ───────────────────────────────────────
        (
            WorkerState::Executing { thread_id },
            WorkerEvent::QuantumComplete(result),
        ) => {
            let tid = *thread_id;
            let actions = match result {
                QuantumResult::Completed { result } => {
                    vec![WorkerAction::ReportToCoordinator(
                        WorkerReport::ThreadCompleted {
                            thread_id: tid,
                            result,
                        },
                    )]
                }
                QuantumResult::Suspended { waiting_on } => {
                    vec![WorkerAction::ReportToCoordinator(
                        WorkerReport::ThreadSuspended {
                            thread_id: tid,
                            waiting_on,
                        },
                    )]
                }
                QuantumResult::Yielded => {
                    vec![WorkerAction::ReenqueueLocal(tid)]
                }
                QuantumResult::Forked { children } => {
                    // The children are category names for fork requests.
                    // The worker will create the actual child threads.
                    vec![WorkerAction::ForkAndEnqueue {
                        parent_id: tid,
                        categories: children,
                    }]
                }
                QuantumResult::Failed { error } => {
                    vec![WorkerAction::ReportToCoordinator(
                        WorkerReport::ThreadFailed {
                            thread_id: tid,
                            error,
                        },
                    )]
                }
            };
            WorkerTransition {
                new_state: WorkerState::Idle,
                actions,
            }
        }

        // ── Parking transitions ─────────────────────────────────────────
        (WorkerState::Parking, WorkerEvent::Unpark) => WorkerTransition {
            new_state: WorkerState::Idle,
            actions: vec![],
        },
        (WorkerState::Parking, WorkerEvent::ShutdownSignal) => WorkerTransition {
            new_state: WorkerState::Exiting,
            actions: vec![WorkerAction::Exit],
        },

        // ── Exiting: absorb all events ──────────────────────────────────
        (WorkerState::Exiting, _) => WorkerTransition {
            new_state: WorkerState::Exiting,
            actions: vec![],
        },

        // ── Catch-all: unexpected (state, event) pairs ──────────────────
        (_, _) => WorkerTransition {
            new_state: WorkerState::Idle,
            actions: vec![],
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Coordinator FSM — Scheduling layer state machine
// ══════════════════════════════════════════════════════════════════════════════

/// State of the coordinator thread that owns the `Scheduler` FSM.
///
/// ```text
///   Bootstrapping ──→ Running ──→ Draining ──→ Terminated
///                       ↑  │
///                       │  └──→ Scaling ──→ Running
///                       │
///                       └──── (main loop)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CoordinatorState {
    /// Initial setup: creating scheduler, waiting for workers to start.
    Bootstrapping,
    /// Normal operation: processing worker reports, dispatching work.
    Running,
    /// Adjusting worker pool size based on HillClimber suggestion.
    Scaling,
    /// Shutdown initiated: draining pending work, waiting for workers.
    Draining,
    /// Fully shut down.
    Terminated,
}

impl fmt::Display for CoordinatorState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bootstrapping => write!(f, "Bootstrapping"),
            Self::Running => write!(f, "Running"),
            Self::Scaling => write!(f, "Scaling"),
            Self::Draining => write!(f, "Draining"),
            Self::Terminated => write!(f, "Terminated"),
        }
    }
}

/// Events that drive coordinator state transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoordinatorEvent {
    /// A worker sent a report (completion, suspension, fork, failure).
    WorkerReport(WorkerReport),
    /// Periodic timer tick (for scaling checks and scheduler polling).
    TimerTick,
    /// HillClimber suggests changing the worker count.
    ScaleCheck { suggested_workers: u32 },
    /// External shutdown request.
    ShutdownRequest,
    /// All workers have exited.
    AllWorkersExited,
    /// A channel wake-up detected (waiter can be resumed).
    ChannelWakeUp {
        thread_id: GreenThreadId,
        channel_id: ChannelId,
    },
}

impl fmt::Display for CoordinatorEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WorkerReport(r) => write!(f, "WorkerReport({})", r),
            Self::TimerTick => write!(f, "TimerTick"),
            Self::ScaleCheck { suggested_workers } => {
                write!(f, "ScaleCheck(suggested={})", suggested_workers)
            }
            Self::ShutdownRequest => write!(f, "ShutdownRequest"),
            Self::AllWorkersExited => write!(f, "AllWorkersExited"),
            Self::ChannelWakeUp {
                thread_id,
                channel_id,
            } => write!(f, "ChannelWakeUp({}, {})", thread_id, channel_id),
        }
    }
}

/// Result of a coordinator FSM transition.
#[derive(Debug, Clone)]
pub struct CoordinatorTransition {
    pub new_state: CoordinatorState,
    pub actions: Vec<CoordinatorAction>,
}

/// Side-effect actions emitted by coordinator FSM transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoordinatorAction {
    /// Push a green thread ID to the global injector for workers to pick up.
    InjectWork(GreenThreadId),
    /// Wake parked workers (notify condvar).
    UnparkWorkers,
    /// Forward an event to the owned Scheduler FSM.
    ForwardToScheduler(SchedulerEvent),
    /// Resize the worker pool to the given count.
    ResizePool(u32),
    /// Signal all workers to shut down.
    DrainWorkers,
    /// Emit metrics for observability.
    EmitMetrics,
    /// Replenish the parallel budget by the given amount.
    ReplenishBudget(u32),
}

/// Process a coordinator FSM event, returning the state transition.
///
/// Pure function: `(CoordinatorState, CoordinatorEvent) → (CoordinatorState', Vec<CoordinatorAction>)`
pub fn coordinator_process_event(
    state: &CoordinatorState,
    event: CoordinatorEvent,
) -> CoordinatorTransition {
    match (state, event) {
        // ── Shutdown overrides everything ────────────────────────────────
        (_, CoordinatorEvent::ShutdownRequest) => CoordinatorTransition {
            new_state: CoordinatorState::Draining,
            actions: vec![
                CoordinatorAction::DrainWorkers,
                CoordinatorAction::EmitMetrics,
            ],
        },

        // ── Bootstrapping ───────────────────────────────────────────────
        (CoordinatorState::Bootstrapping, CoordinatorEvent::TimerTick) => {
            // Workers are ready, transition to Running.
            CoordinatorTransition {
                new_state: CoordinatorState::Running,
                actions: vec![],
            }
        }

        // ── Running: process worker reports ─────────────────────────────
        (CoordinatorState::Running, CoordinatorEvent::WorkerReport(report)) => {
            let mut actions = Vec::new();
            match report {
                WorkerReport::ThreadCompleted { thread_id, .. } => {
                    actions.push(CoordinatorAction::ForwardToScheduler(
                        SchedulerEvent::ThreadCompleted { thread_id },
                    ));
                    actions.push(CoordinatorAction::ReplenishBudget(1));
                }
                WorkerReport::ThreadSuspended { .. } => {
                    // Thread already in Suspended state; coordinator tracks
                    // the waiter in the WakeRegistry (handled by caller).
                }
                WorkerReport::ForkRequested {
                    parent_id,
                    categories,
                } => {
                    for category in categories {
                        actions.push(CoordinatorAction::ForwardToScheduler(
                            SchedulerEvent::ForkRequest {
                                parent_id,
                                category,
                            },
                        ));
                    }
                }
                WorkerReport::ThreadFailed { thread_id, .. } => {
                    actions.push(CoordinatorAction::ForwardToScheduler(
                        SchedulerEvent::ThreadCompleted { thread_id },
                    ));
                    actions.push(CoordinatorAction::ReplenishBudget(1));
                }
                WorkerReport::ThreadReady {
                    thread_id,
                    ..
                } => {
                    // Enqueue in scheduler, then inject for workers.
                    actions.push(CoordinatorAction::InjectWork(thread_id));
                    actions.push(CoordinatorAction::UnparkWorkers);
                }
                WorkerReport::ChannelActivity { .. } => {
                    // Channel activity is handled by the coordinator loop
                    // (event-driven wake path), not by the pure FSM.
                    // The coordinator checks affected channels for waiters.
                }
            }
            CoordinatorTransition {
                new_state: CoordinatorState::Running,
                actions,
            }
        }
        (CoordinatorState::Running, CoordinatorEvent::TimerTick) => {
            // Periodic tick: forward to scheduler for polling.
            CoordinatorTransition {
                new_state: CoordinatorState::Running,
                actions: vec![CoordinatorAction::ForwardToScheduler(
                    SchedulerEvent::TimerExpired,
                )],
            }
        }
        (CoordinatorState::Running, CoordinatorEvent::ScaleCheck { suggested_workers }) => {
            CoordinatorTransition {
                new_state: CoordinatorState::Scaling,
                actions: vec![CoordinatorAction::ResizePool(suggested_workers)],
            }
        }
        (CoordinatorState::Running, CoordinatorEvent::ChannelWakeUp { thread_id, channel_id }) => {
            CoordinatorTransition {
                new_state: CoordinatorState::Running,
                actions: vec![
                    CoordinatorAction::ForwardToScheduler(SchedulerEvent::ChannelMessage {
                        channel_id,
                    }),
                    CoordinatorAction::InjectWork(thread_id),
                    CoordinatorAction::UnparkWorkers,
                ],
            }
        }

        // ── Scaling: return to Running after resize ─────────────────────
        (CoordinatorState::Scaling, _) => CoordinatorTransition {
            new_state: CoordinatorState::Running,
            actions: vec![],
        },

        // ── Draining: waiting for all workers to exit ───────────────────
        (CoordinatorState::Draining, CoordinatorEvent::AllWorkersExited) => {
            CoordinatorTransition {
                new_state: CoordinatorState::Terminated,
                actions: vec![CoordinatorAction::EmitMetrics],
            }
        }
        (CoordinatorState::Draining, _) => {
            // Absorb events while draining.
            CoordinatorTransition {
                new_state: CoordinatorState::Draining,
                actions: vec![],
            }
        }

        // ── Terminated: absorb everything ───────────────────────────────
        (CoordinatorState::Terminated, _) => CoordinatorTransition {
            new_state: CoordinatorState::Terminated,
            actions: vec![],
        },

        // ── Catch-all ───────────────────────────────────────────────────
        (_, _) => CoordinatorTransition {
            new_state: CoordinatorState::Running,
            actions: vec![],
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pool FSM — Top-level lifecycle state machine
// ══════════════════════════════════════════════════════════════════════════════

/// Lifecycle state of the entire M:N thread pool.
///
/// ```text
///   Uninitialized ──→ Starting ──→ Running ──→ ShuttingDown ──→ Terminated
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PoolState {
    /// Pool has not been started.
    Uninitialized,
    /// Spawning coordinator and worker threads.
    Starting,
    /// Normal operation.
    Running,
    /// Shutdown in progress: draining work, joining threads.
    ShuttingDown,
    /// Fully shut down: all threads joined.
    Terminated,
}

impl fmt::Display for PoolState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uninitialized => write!(f, "Uninitialized"),
            Self::Starting => write!(f, "Starting"),
            Self::Running => write!(f, "Running"),
            Self::ShuttingDown => write!(f, "ShuttingDown"),
            Self::Terminated => write!(f, "Terminated"),
        }
    }
}

/// Events that drive pool lifecycle transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoolEvent {
    /// Start the pool with the given number of workers.
    Start { num_workers: usize },
    /// Coordinator thread is ready.
    CoordinatorReady,
    /// External shutdown request.
    ShutdownRequest,
    /// All threads have been joined.
    AllJoined,
}

impl fmt::Display for PoolEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Start { num_workers } => write!(f, "Start(workers={})", num_workers),
            Self::CoordinatorReady => write!(f, "CoordinatorReady"),
            Self::ShutdownRequest => write!(f, "ShutdownRequest"),
            Self::AllJoined => write!(f, "AllJoined"),
        }
    }
}

/// Result of a pool FSM transition.
#[derive(Debug, Clone)]
pub struct PoolTransition {
    pub new_state: PoolState,
    pub actions: Vec<PoolAction>,
}

/// Side-effect actions for pool lifecycle management.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoolAction {
    /// Spawn the coordinator thread.
    SpawnCoordinator,
    /// Spawn N worker threads.
    SpawnWorkers(usize),
    /// Signal shutdown to coordinator and workers.
    SignalShutdown,
    /// Join all spawned threads.
    JoinAllThreads,
}

/// Process a pool FSM event, returning the state transition.
///
/// Pure function: `(PoolState, PoolEvent) → (PoolState', Vec<PoolAction>)`
pub fn pool_process_event(state: &PoolState, event: PoolEvent) -> PoolTransition {
    match (state, event) {
        // ── Uninitialized → Starting ────────────────────────────────────
        (PoolState::Uninitialized, PoolEvent::Start { num_workers }) => PoolTransition {
            new_state: PoolState::Starting,
            actions: vec![
                PoolAction::SpawnCoordinator,
                PoolAction::SpawnWorkers(num_workers),
            ],
        },

        // ── Starting → Running ──────────────────────────────────────────
        (PoolState::Starting, PoolEvent::CoordinatorReady) => PoolTransition {
            new_state: PoolState::Running,
            actions: vec![],
        },

        // ── Running → ShuttingDown ──────────────────────────────────────
        (PoolState::Running, PoolEvent::ShutdownRequest) => PoolTransition {
            new_state: PoolState::ShuttingDown,
            actions: vec![PoolAction::SignalShutdown, PoolAction::JoinAllThreads],
        },

        // ── ShuttingDown → Terminated ───────────────────────────────────
        (PoolState::ShuttingDown, PoolEvent::AllJoined) => PoolTransition {
            new_state: PoolState::Terminated,
            actions: vec![],
        },

        // ── Terminated: absorb ──────────────────────────────────────────
        (PoolState::Terminated, _) => PoolTransition {
            new_state: PoolState::Terminated,
            actions: vec![],
        },

        // ── Shutdown from any state ─────────────────────────────────────
        (_, PoolEvent::ShutdownRequest) => PoolTransition {
            new_state: PoolState::ShuttingDown,
            actions: vec![PoolAction::SignalShutdown, PoolAction::JoinAllThreads],
        },

        // ── Catch-all ───────────────────────────────────────────────────
        (_, _) => PoolTransition {
            new_state: *state,
            actions: vec![],
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── Worker FSM Tests ────────────────────────────────────────────────

    #[test]
    fn test_worker_idle_work_found() {
        let tid = GreenThreadId(42);
        let t = worker_process_event(&WorkerState::Idle, WorkerEvent::WorkFound(tid));
        assert_eq!(t.new_state, WorkerState::Executing { thread_id: tid });
        assert_eq!(t.actions, vec![WorkerAction::ExecuteQuantum(tid)]);
    }

    #[test]
    fn test_worker_idle_no_work() {
        let t = worker_process_event(&WorkerState::Idle, WorkerEvent::NoWorkAvailable);
        assert_eq!(t.new_state, WorkerState::Parking);
        assert_eq!(t.actions, vec![WorkerAction::Park]);
    }

    #[test]
    fn test_worker_idle_shutdown() {
        let t = worker_process_event(&WorkerState::Idle, WorkerEvent::ShutdownSignal);
        assert_eq!(t.new_state, WorkerState::Exiting);
        assert_eq!(t.actions, vec![WorkerAction::Exit]);
    }

    #[test]
    fn test_worker_idle_spurious_unpark() {
        let t = worker_process_event(&WorkerState::Idle, WorkerEvent::Unpark);
        assert_eq!(t.new_state, WorkerState::Idle);
        assert!(t.actions.is_empty());
    }

    #[test]
    fn test_worker_executing_completed() {
        let tid = GreenThreadId(7);
        let state = WorkerState::Executing { thread_id: tid };
        let result = QuantumResult::Completed {
            result: "42".to_string(),
        };
        let t = worker_process_event(&state, WorkerEvent::QuantumComplete(result));
        assert_eq!(t.new_state, WorkerState::Idle);
        assert_eq!(
            t.actions,
            vec![WorkerAction::ReportToCoordinator(
                WorkerReport::ThreadCompleted {
                    thread_id: tid,
                    result: "42".to_string()
                }
            )]
        );
    }

    #[test]
    fn test_worker_executing_yielded() {
        let tid = GreenThreadId(3);
        let state = WorkerState::Executing { thread_id: tid };
        let t =
            worker_process_event(&state, WorkerEvent::QuantumComplete(QuantumResult::Yielded));
        assert_eq!(t.new_state, WorkerState::Idle);
        assert_eq!(t.actions, vec![WorkerAction::ReenqueueLocal(tid)]);
    }

    #[test]
    fn test_worker_executing_suspended() {
        let tid = GreenThreadId(5);
        let state = WorkerState::Executing { thread_id: tid };
        let channels = vec![ChannelId(1), ChannelId(2)];
        let result = QuantumResult::Suspended {
            waiting_on: channels.clone(),
        };
        let t = worker_process_event(&state, WorkerEvent::QuantumComplete(result));
        assert_eq!(t.new_state, WorkerState::Idle);
        assert_eq!(
            t.actions,
            vec![WorkerAction::ReportToCoordinator(
                WorkerReport::ThreadSuspended {
                    thread_id: tid,
                    waiting_on: channels,
                }
            )]
        );
    }

    #[test]
    fn test_worker_executing_failed() {
        let tid = GreenThreadId(9);
        let state = WorkerState::Executing { thread_id: tid };
        let result = QuantumResult::Failed {
            error: "division by zero".to_string(),
        };
        let t = worker_process_event(&state, WorkerEvent::QuantumComplete(result));
        assert_eq!(t.new_state, WorkerState::Idle);
        assert_eq!(
            t.actions,
            vec![WorkerAction::ReportToCoordinator(
                WorkerReport::ThreadFailed {
                    thread_id: tid,
                    error: "division by zero".to_string(),
                }
            )]
        );
    }

    #[test]
    fn test_worker_executing_forked() {
        let tid = GreenThreadId(10);
        let state = WorkerState::Executing { thread_id: tid };
        let cats = vec!["Proc".to_string(), "Proc".to_string()];
        let result = QuantumResult::Forked {
            children: cats.clone(),
        };
        let t = worker_process_event(&state, WorkerEvent::QuantumComplete(result));
        assert_eq!(t.new_state, WorkerState::Idle);
        assert_eq!(
            t.actions,
            vec![WorkerAction::ForkAndEnqueue {
                parent_id: tid,
                categories: cats,
            }]
        );
    }

    #[test]
    fn test_worker_parking_unpark() {
        let t = worker_process_event(&WorkerState::Parking, WorkerEvent::Unpark);
        assert_eq!(t.new_state, WorkerState::Idle);
        assert!(t.actions.is_empty());
    }

    #[test]
    fn test_worker_parking_shutdown() {
        let t = worker_process_event(&WorkerState::Parking, WorkerEvent::ShutdownSignal);
        assert_eq!(t.new_state, WorkerState::Exiting);
        assert_eq!(t.actions, vec![WorkerAction::Exit]);
    }

    #[test]
    fn test_worker_exiting_absorbs() {
        for event in [
            WorkerEvent::WorkFound(GreenThreadId(0)),
            WorkerEvent::NoWorkAvailable,
            WorkerEvent::Unpark,
            WorkerEvent::ShutdownSignal,
        ] {
            let t = worker_process_event(&WorkerState::Exiting, event);
            assert_eq!(t.new_state, WorkerState::Exiting);
            assert!(t.actions.is_empty());
        }
    }

    #[test]
    fn test_worker_full_lifecycle() {
        // Idle → WorkFound → Executing → QuantumComplete(Yielded) → Idle
        // → NoWork → Parking → Unpark → Idle → ShutdownSignal → Exiting
        let mut state = WorkerState::Idle;

        let t = worker_process_event(&state, WorkerEvent::WorkFound(GreenThreadId(1)));
        state = t.new_state;
        assert!(matches!(state, WorkerState::Executing { .. }));

        let t = worker_process_event(&state, WorkerEvent::QuantumComplete(QuantumResult::Yielded));
        state = t.new_state;
        assert_eq!(state, WorkerState::Idle);

        let t = worker_process_event(&state, WorkerEvent::NoWorkAvailable);
        state = t.new_state;
        assert_eq!(state, WorkerState::Parking);

        let t = worker_process_event(&state, WorkerEvent::Unpark);
        state = t.new_state;
        assert_eq!(state, WorkerState::Idle);

        let t = worker_process_event(&state, WorkerEvent::ShutdownSignal);
        state = t.new_state;
        assert_eq!(state, WorkerState::Exiting);
    }

    // ── Coordinator FSM Tests ───────────────────────────────────────────

    #[test]
    fn test_coordinator_bootstrapping_to_running() {
        let t = coordinator_process_event(
            &CoordinatorState::Bootstrapping,
            CoordinatorEvent::TimerTick,
        );
        assert_eq!(t.new_state, CoordinatorState::Running);
    }

    #[test]
    fn test_coordinator_running_thread_completed() {
        let report = WorkerReport::ThreadCompleted {
            thread_id: GreenThreadId(1),
            result: "ok".to_string(),
        };
        let t = coordinator_process_event(
            &CoordinatorState::Running,
            CoordinatorEvent::WorkerReport(report),
        );
        assert_eq!(t.new_state, CoordinatorState::Running);
        assert!(t.actions.iter().any(|a| matches!(
            a,
            CoordinatorAction::ForwardToScheduler(SchedulerEvent::ThreadCompleted { .. })
        )));
        assert!(t
            .actions
            .iter()
            .any(|a| matches!(a, CoordinatorAction::ReplenishBudget(1))));
    }

    #[test]
    fn test_coordinator_running_fork_request() {
        let report = WorkerReport::ForkRequested {
            parent_id: GreenThreadId(1),
            categories: vec!["A".to_string(), "B".to_string()],
        };
        let t = coordinator_process_event(
            &CoordinatorState::Running,
            CoordinatorEvent::WorkerReport(report),
        );
        assert_eq!(t.new_state, CoordinatorState::Running);
        // Should forward 2 ForkRequest events to scheduler.
        let fork_count = t
            .actions
            .iter()
            .filter(|a| {
                matches!(
                    a,
                    CoordinatorAction::ForwardToScheduler(SchedulerEvent::ForkRequest { .. })
                )
            })
            .count();
        assert_eq!(fork_count, 2);
    }

    #[test]
    fn test_coordinator_running_scale_check() {
        let t = coordinator_process_event(
            &CoordinatorState::Running,
            CoordinatorEvent::ScaleCheck {
                suggested_workers: 8,
            },
        );
        assert_eq!(t.new_state, CoordinatorState::Scaling);
        assert_eq!(t.actions, vec![CoordinatorAction::ResizePool(8)]);
    }

    #[test]
    fn test_coordinator_running_channel_wakeup() {
        let t = coordinator_process_event(
            &CoordinatorState::Running,
            CoordinatorEvent::ChannelWakeUp {
                thread_id: GreenThreadId(5),
                channel_id: ChannelId(3),
            },
        );
        assert_eq!(t.new_state, CoordinatorState::Running);
        assert!(t
            .actions
            .iter()
            .any(|a| matches!(a, CoordinatorAction::InjectWork(tid) if *tid == GreenThreadId(5))));
        assert!(t
            .actions
            .iter()
            .any(|a| matches!(a, CoordinatorAction::UnparkWorkers)));
    }

    #[test]
    fn test_coordinator_shutdown_from_any_state() {
        for state in [
            CoordinatorState::Bootstrapping,
            CoordinatorState::Running,
            CoordinatorState::Scaling,
        ] {
            let t = coordinator_process_event(&state, CoordinatorEvent::ShutdownRequest);
            assert_eq!(t.new_state, CoordinatorState::Draining);
            assert!(t
                .actions
                .iter()
                .any(|a| matches!(a, CoordinatorAction::DrainWorkers)));
        }
    }

    #[test]
    fn test_coordinator_draining_to_terminated() {
        let t = coordinator_process_event(
            &CoordinatorState::Draining,
            CoordinatorEvent::AllWorkersExited,
        );
        assert_eq!(t.new_state, CoordinatorState::Terminated);
    }

    #[test]
    fn test_coordinator_draining_absorbs() {
        let t =
            coordinator_process_event(&CoordinatorState::Draining, CoordinatorEvent::TimerTick);
        assert_eq!(t.new_state, CoordinatorState::Draining);
        assert!(t.actions.is_empty());
    }

    #[test]
    fn test_coordinator_terminated_absorbs() {
        for event in [
            CoordinatorEvent::TimerTick,
            CoordinatorEvent::AllWorkersExited,
            CoordinatorEvent::WorkerReport(WorkerReport::ThreadCompleted {
                thread_id: GreenThreadId(0),
                result: String::new(),
            }),
        ] {
            let t = coordinator_process_event(&CoordinatorState::Terminated, event);
            assert_eq!(t.new_state, CoordinatorState::Terminated);
            assert!(t.actions.is_empty());
        }
    }

    // ── Pool FSM Tests ──────────────────────────────────────────────────

    #[test]
    fn test_pool_start() {
        let t = pool_process_event(
            &PoolState::Uninitialized,
            PoolEvent::Start { num_workers: 4 },
        );
        assert_eq!(t.new_state, PoolState::Starting);
        assert!(t
            .actions
            .contains(&PoolAction::SpawnCoordinator));
        assert!(t
            .actions
            .contains(&PoolAction::SpawnWorkers(4)));
    }

    #[test]
    fn test_pool_starting_to_running() {
        let t = pool_process_event(&PoolState::Starting, PoolEvent::CoordinatorReady);
        assert_eq!(t.new_state, PoolState::Running);
    }

    #[test]
    fn test_pool_running_to_shutting_down() {
        let t = pool_process_event(&PoolState::Running, PoolEvent::ShutdownRequest);
        assert_eq!(t.new_state, PoolState::ShuttingDown);
        assert!(t
            .actions
            .contains(&PoolAction::SignalShutdown));
        assert!(t
            .actions
            .contains(&PoolAction::JoinAllThreads));
    }

    #[test]
    fn test_pool_shutting_down_to_terminated() {
        let t = pool_process_event(&PoolState::ShuttingDown, PoolEvent::AllJoined);
        assert_eq!(t.new_state, PoolState::Terminated);
    }

    #[test]
    fn test_pool_terminated_absorbs() {
        let t = pool_process_event(
            &PoolState::Terminated,
            PoolEvent::Start { num_workers: 2 },
        );
        assert_eq!(t.new_state, PoolState::Terminated);
    }

    // ── Display Tests ───────────────────────────────────────────────────

    #[test]
    fn test_worker_state_display() {
        assert_eq!(WorkerState::Idle.to_string(), "Idle");
        assert_eq!(
            WorkerState::Executing {
                thread_id: GreenThreadId(5)
            }
            .to_string(),
            "Executing(gt#5)"
        );
        assert_eq!(WorkerState::Parking.to_string(), "Parking");
        assert_eq!(WorkerState::Exiting.to_string(), "Exiting");
    }

    #[test]
    fn test_coordinator_state_display() {
        assert_eq!(CoordinatorState::Bootstrapping.to_string(), "Bootstrapping");
        assert_eq!(CoordinatorState::Running.to_string(), "Running");
        assert_eq!(CoordinatorState::Terminated.to_string(), "Terminated");
    }

    #[test]
    fn test_pool_state_display() {
        assert_eq!(PoolState::Uninitialized.to_string(), "Uninitialized");
        assert_eq!(PoolState::Running.to_string(), "Running");
        assert_eq!(PoolState::Terminated.to_string(), "Terminated");
    }

    #[test]
    fn test_worker_report_display() {
        let r = WorkerReport::ThreadCompleted {
            thread_id: GreenThreadId(3),
            result: "ok".to_string(),
        };
        assert_eq!(r.to_string(), "ThreadCompleted(gt#3)");

        let r = WorkerReport::ForkRequested {
            parent_id: GreenThreadId(1),
            categories: vec!["A".to_string(), "B".to_string()],
        };
        assert_eq!(r.to_string(), "ForkRequested(parent=gt#1, children=2)");

        let r = WorkerReport::ChannelActivity {
            channel_ids: vec![ChannelId(1), ChannelId(2), ChannelId(3)],
        };
        assert_eq!(r.to_string(), "ChannelActivity(channels=3)");
    }

    #[test]
    fn test_coordinator_running_channel_activity() {
        let report = WorkerReport::ChannelActivity {
            channel_ids: vec![ChannelId(10), ChannelId(20)],
        };
        let t = coordinator_process_event(
            &CoordinatorState::Running,
            CoordinatorEvent::WorkerReport(report),
        );
        assert_eq!(t.new_state, CoordinatorState::Running);
        // ChannelActivity is handled by the coordinator loop, not the pure FSM,
        // so the FSM emits no actions for it.
        assert!(
            t.actions.is_empty(),
            "ChannelActivity should produce no FSM actions"
        );
    }
}
