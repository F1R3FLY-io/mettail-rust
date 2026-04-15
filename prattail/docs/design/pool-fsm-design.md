# Reactive State Machine Hierarchy

The M:N green thread runtime is organized as four layers of reactive state machines, each following the pure transition function pattern: `process_event : (State, Event) -> (State', Vec<Action>)`. Actions from one layer become events for adjacent layers, forming a composable, independently testable scheduling stack.

All FSM types and transition functions are defined in `prattail/src/pool_fsm.rs` (Pool, Coordinator, Worker layers) and `prattail/src/scheduler.rs` (Scheduler layer).

## 1. Pool FSM (Layer 4 -- Lifecycle Management)

The Pool FSM manages the top-level lifecycle of the entire M:N runtime. It has 5 states and 4 event types.

### State Diagram

```text
                             Start(N)                CoordinatorReady
  ┌───────────────┐  ────────────────────▶  ┌──────────┐  ──────────▶  ┌─────────┐
  │ Uninitialized │                         │ Starting │               │ Running │
  └───────────────┘                         └──────────┘               └────┬────┘
                                                                            │
                                                                ShutdownRequest
                                                                            │
                                                                            ▼
                                                                    ┌──────────────┐
                                                                    │ ShuttingDown │
                                                                    └──────┬───────┘
                                                                           │
                                                                       AllJoined
                                                                           │
                                                                           ▼
                                                                    ┌────────────┐
                                                                    │ Terminated │
                                                                    └────────────┘
```

Note: `ShutdownRequest` is accepted from any non-terminal state (universal override).

### Transition Table

| Current State | Event | New State | Actions |
|--------------|-------|-----------|---------|
| Uninitialized | Start { num_workers } | Starting | SpawnCoordinator, SpawnWorkers(N) |
| Starting | CoordinatorReady | Running | -- |
| Running | ShutdownRequest | ShuttingDown | SignalShutdown, JoinAllThreads |
| ShuttingDown | AllJoined | Terminated | -- |
| Terminated | * | Terminated | -- (absorb) |
| * | ShutdownRequest | ShuttingDown | SignalShutdown, JoinAllThreads |

### Actions

| Action | Effect |
|--------|--------|
| `SpawnCoordinator` | Spawn the coordinator native thread (`prattail-coordinator`) |
| `SpawnWorkers(N)` | Spawn N worker native threads (`prattail-worker-0` .. `prattail-worker-(N-1)`) |
| `SignalShutdown` | Set the `AtomicBool` shutdown flag to `true` |
| `JoinAllThreads` | Call `join()` on all spawned `JoinHandle<()>` values |

### Code Reference

`pool_process_event()` in `prattail/src/pool_fsm.rs` (line ~621).

## 2. Coordinator FSM (Layer 3 -- Scheduling Decisions)

The Coordinator FSM runs on a dedicated native thread and makes all scheduling decisions. It owns the `Scheduler` FSM (Layer 2) exclusively -- no Mutex required because only the coordinator thread calls `Scheduler::process_event()`.

### State Diagram

```text
                     TimerTick              ScaleCheck
  ┌───────────────┐  ──────▶  ┌─────────┐  ──────────▶  ┌─────────┐
  │ Bootstrapping │           │ Running │◀──────────────│ Scaling │
  └───────────────┘           └────┬────┘  (any event)   └─────────┘
                                   │
                           ShutdownRequest
                                   │
                                   ▼
                            ┌──────────┐    AllWorkersExited   ┌────────────┐
                            │ Draining │  ──────────────────▶  │ Terminated │
                            └──────────┘                       └────────────┘
```

### Transition Table

| Current State | Event | New State | Actions |
|--------------|-------|-----------|---------|
| Bootstrapping | TimerTick | Running | -- |
| Running | WorkerReport(ThreadCompleted) | Running | ForwardToScheduler(ThreadCompleted), ReplenishBudget(1) |
| Running | WorkerReport(ThreadSuspended) | Running | -- (caller handles WakeRegistry) |
| Running | WorkerReport(ForkRequested) | Running | ForwardToScheduler(ForkRequest) x N |
| Running | WorkerReport(ThreadFailed) | Running | ForwardToScheduler(ThreadCompleted), ReplenishBudget(1) |
| Running | WorkerReport(ThreadReady) | Running | InjectWork(tid), UnparkWorkers |
| Running | TimerTick | Running | ForwardToScheduler(TimerExpired) |
| Running | ScaleCheck { suggested } | Scaling | ResizePool(suggested) |
| Running | ChannelWakeUp { tid, ch } | Running | ForwardToScheduler(ChannelMessage), InjectWork(tid), UnparkWorkers |
| Scaling | * | Running | -- |
| Draining | AllWorkersExited | Terminated | EmitMetrics |
| Draining | * | Draining | -- (absorb) |
| Terminated | * | Terminated | -- (absorb) |
| * | ShutdownRequest | Draining | DrainWorkers, EmitMetrics |

### Actions

| Action | Effect |
|--------|--------|
| `InjectWork(tid)` | Push `GreenThreadId` to `WorkerPool`'s global `Injector` |
| `UnparkWorkers` | Call `WorkerParker::unpark_one()` to wake an idle worker |
| `ForwardToScheduler(event)` | Call `Scheduler::process_event(event)` on the owned Scheduler FSM |
| `ResizePool(n)` | Adjust the number of active worker threads (deferred to future sprint) |
| `DrainWorkers` | Signal shutdown to all workers, drain remaining work |
| `EmitMetrics` | Snapshot `SchedulerMetrics` and `GlobalPoolMetrics` for observability |
| `ReplenishBudget(k)` | Call `Scheduler::replenish_budget(k)` to free k worker slots |

### Code Reference

`coordinator_process_event()` in `prattail/src/pool_fsm.rs` (line ~406). The live coordinator event loop is in `coordinator_loop()` in `prattail/src/coordinator.rs` (line ~166).

## 3. Scheduler FSM (Layer 2 -- Priority Dispatch)

The Scheduler FSM is the core scheduling engine. It manages a priority-ordered ready queue (`im::OrdMap<(u32, u64), GreenThreadId>`) and a fork budget (`AtomicU32`).

### State Diagram

```text
  ┌──────────────┐  ChannelMessage   ┌───────────────┐  threads ready  ┌──────────┐
  │ CheckChannels │  ───────────────▶ │ DispatchReady │  ─────────────▶ │ Execute  │
  └──────────────┘                   └───────────────┘                 └──────────┘
        ↑                                  ↑                                │
        │            NoWork                │                                │ thread done
        │       ┌──────────┐               │                                │ or fork
        │       │          │               │                                │
        └───────│ ParkIdle │◀──────────────┴────────────────────────────────┘
                │          │
                └─────┬────┘
                      │ ShutdownRequested
                      ▼
                ┌──────────┐
                │ Shutdown │
                └──────────┘
```

### Transition Table

| Current State | Event | Guard | New State | Actions |
|--------------|-------|-------|-----------|---------|
| CheckChannels | ChannelMessage | -- | DispatchReady | -- |
| CheckChannels | NoWork | -- | ParkIdle | ParkWorkers |
| CheckChannels | TimerExpired | ready_queue non-empty | DispatchReady | -- |
| CheckChannels | TimerExpired | ready_queue empty | ParkIdle | ParkWorkers |
| DispatchReady | * | threads + budget available | Execute | WakeThread(id)... |
| DispatchReady | * | no threads or no budget | CheckChannels | -- |
| Execute | ThreadCompleted | ready_queue non-empty | DispatchReady | NotifyComplete, [WakeThread] |
| Execute | ThreadCompleted | ready_queue empty | CheckChannels | NotifyComplete |
| Execute | ForkRequest | -- | Execute | SpawnThread |
| Execute | ChannelMessage | -- | Execute | -- |
| ParkIdle | ChannelMessage | -- | CheckChannels | -- |
| ParkIdle | ForkRequest | -- | DispatchReady | SpawnThread |
| ParkIdle | TimerExpired | -- | CheckChannels | -- |
| ParkIdle | NoWork | -- | ParkIdle | -- |
| * | ShutdownRequested | -- | Shutdown | EmitMetrics |
| Shutdown | * | -- | Shutdown | -- (absorb) |

### Code Reference

`Scheduler::process_event()` in `prattail/src/scheduler.rs` (line ~351).

## 4. Worker FSM (Layer 1 -- Per-Thread Execution)

Each native worker thread runs its own instance of the Worker FSM. The FSM governs the work-discovery and quantum-execution cycle.

### State Diagram

```text
              WorkFound(tid)
  ┌──────┐  ────────────────▶  ┌───────────┐
  │ Idle │                     │ Executing │
  │      │◀────────────────────│ {tid}     │
  └──┬───┘  QuantumComplete    └───────────┘
     │
     │ NoWorkAvailable
     ▼
  ┌─────────┐   Unpark    ┌──────┐
  │ Parking │  ─────────▶ │ Idle │
  └────┬────┘              └──────┘
       │
       │ ShutdownSignal
       ▼
  ┌─────────┐
  │ Exiting │  (absorbs all events)
  └─────────┘
```

### Transition Table

| Current State | Event | New State | Actions |
|--------------|-------|-----------|---------|
| Idle | WorkFound(tid) | Executing { tid } | ExecuteQuantum(tid) |
| Idle | NoWorkAvailable | Parking | Park |
| Idle | ShutdownSignal | Exiting | Exit |
| Idle | Unpark | Idle | -- (spurious wake) |
| Executing { tid } | QuantumComplete(Completed) | Idle | ReportToCoordinator(ThreadCompleted) |
| Executing { tid } | QuantumComplete(Yielded) | Idle | ReenqueueLocal(tid) |
| Executing { tid } | QuantumComplete(Suspended) | Idle | ReportToCoordinator(ThreadSuspended) |
| Executing { tid } | QuantumComplete(Forked) | Idle | ForkAndEnqueue { parent, categories } |
| Executing { tid } | QuantumComplete(Failed) | Idle | ReportToCoordinator(ThreadFailed) |
| Parking | Unpark | Idle | -- |
| Parking | ShutdownSignal | Exiting | Exit |
| Exiting | * | Exiting | -- (absorb) |

### Actions

| Action | Effect |
|--------|--------|
| `ExecuteQuantum(tid)` | Call `GreenThread::run_quantum(quantum_size)` on the thread — internally calls `cek_step()` up to N times |
| `ReenqueueLocal(tid)` | Push `tid` back to the worker's local deque (LIFO) |
| `ReportToCoordinator(report)` | Send `WorkerReport` via MPSC channel to coordinator |
| `ForkAndEnqueue { parent, categories }` | Spawn children via registry, push to local deque, report fork |
| `Park` | Call `WorkerParker::park(shutdown_flag)` |
| `Exit` | Break out of the worker loop |

### Code Reference

`worker_process_event()` in `prattail/src/pool_fsm.rs` (line ~202).

## 5. Layer Composition: How Actions Become Events

The following diagram traces a single `ThreadCompleted` event through all four layers.

```text
Layer 1 (GreenThread — unified CEK machine, calls cek_step()):
  gt#5.run_quantum(100) returns QuantumResult::Completed { result: "()" }
                    │
                    ▼ becomes WorkerEvent::QuantumComplete(Completed)
Layer 1 (Worker FSM):
  worker_process_event(Executing{gt#5}, QuantumComplete(Completed))
  → (Idle, [ReportToCoordinator(ThreadCompleted{gt#5})])
                    │
                    │ MPSC channel send
                    ▼ becomes CoordinatorEvent::WorkerReport(ThreadCompleted)
Layer 3 (Coordinator FSM):
  coordinator_process_event(Running, WorkerReport(ThreadCompleted{gt#5}))
  → (Running, [ForwardToScheduler(ThreadCompleted{gt#5}), ReplenishBudget(1)])
                    │
                    ▼ ForwardToScheduler becomes SchedulerEvent::ThreadCompleted
Layer 2 (Scheduler FSM):
  scheduler.process_event(ThreadCompleted{gt#5})
  → (CheckChannels, [NotifyComplete{gt#5}])
                    │
                    ▼ Coordinator executes NotifyComplete (no further propagation)
```

Each `process_event` call is a pure function. Side effects (MPSC sends, injector pushes, condvar notifications) happen only in the `execute_*_actions()` functions that the caller invokes on the returned action list.

## 6. Testability

Because every FSM is a pure function, each layer can be tested in isolation by constructing synthetic event sequences:

```rust
// Test: Worker FSM processes a completed quantum correctly.
let state = WorkerState::Executing { thread_id: GreenThreadId(7) };
let result = QuantumResult::Completed { result: "42".to_string() };
let t = worker_process_event(&state, WorkerEvent::QuantumComplete(result));

assert_eq!(t.new_state, WorkerState::Idle);
assert_eq!(t.actions, vec![
    WorkerAction::ReportToCoordinator(WorkerReport::ThreadCompleted {
        thread_id: GreenThreadId(7),
        result: "42".to_string(),
    })
]);
```

No threads are spawned, no channels are created, no condvars are waited on. The FSM transition is tested as a pure input-output mapping.

### Deterministic Replay

Because the same `(State, Event)` always produces the same `(State', Actions)`, an event stream can be recorded and replayed to reproduce any scheduling behavior. This is invaluable for debugging non-deterministic concurrency bugs:

1. Run the program with event logging enabled.
2. Record the sequence of `(State, Event)` pairs at each layer.
3. Replay the recorded sequence through the FSM to reproduce the exact scheduling decisions.

The `SchedulerMetrics` and `GlobalPoolMetrics` provide additional observability: total dispatched, total completed, total forks, total suspensions, total resumptions, current ready count, current suspended count, and max concurrent threads.

## 7. Formal Properties

### Progress

**Property.** Every non-terminal state has at least one enabled transition.

*Argument.* Each non-terminal state (Idle, Executing, Parking for Worker; CheckChannels, DispatchReady, Execute, ParkIdle for Scheduler; Bootstrapping, Running, Scaling, Draining for Coordinator; Uninitialized, Starting, Running, ShuttingDown for Pool) accepts at least `TimerExpired`/`TimerTick`/`NoWork`/`Unpark` events which are periodically generated by the coordinator's polling loop or the worker's work-discovery loop. The catch-all arms in each `process_event` function guarantee that even unexpected `(State, Event)` pairs produce a valid transition (typically back to the initial/safe state). Terminal states (Shutdown, Exiting, Terminated) absorb all events.

### Deadlock Freedom

**Property.** There is no circular event dependency between FSM layers.

*Argument.* Events flow in one direction through the hierarchy:

```
GreenThread → Worker FSM → (MPSC) → Coordinator FSM → Scheduler FSM
                                       │
                                       └─→ (Injector/Unpark) → Worker FSM
```

The coordinator consumes from the MPSC channel (blocking with timeout) and produces to the injector/parker (non-blocking). Workers consume from their deques/injector (non-blocking pop/steal) and produce to the MPSC channel (non-blocking send). There is no cycle: workers never block waiting for the coordinator, and the coordinator never blocks waiting for workers (it uses `recv_timeout`).

The only blocking operation is `WorkerParker::park()`, which is a condvar wait that is always breakable by either `unpark_one()` (new work) or `unpark_all()` (shutdown). The pending counter ensures no notifications are lost.

### Shutdown Termination

**Property.** After `ShutdownRequested`/`ShutdownRequest` is delivered, all FSM layers converge to their terminal state in bounded time.

*Argument.* `ShutdownRequest` is a universal override in the Coordinator and Pool FSMs -- it transitions to `Draining`/`ShuttingDown` from any state. The coordinator then sets the `AtomicBool` shutdown flag, calls `unpark_all()` to wake all parked workers, and drains the MPSC channel. Workers check the shutdown flag at the top of each loop iteration and exit. The coordinator joins all worker threads, producing the `AllJoined`/`AllWorkersExited` event that transitions to `Terminated`. The bound is O(quantum_size) per worker (each worker completes at most one quantum before checking shutdown).

## 8. References

- MeTTaTron `CronStateMachine` pattern: `State x Event -> Transition` reactive FSM.
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine, and the lambda-calculus. *Formal Description of Programming Concepts III*.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University Press.
