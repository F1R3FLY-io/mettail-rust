# The Two-Pool M:N Architecture

PraTTaIL's green thread runtime implements an M:N scheduler: M cooperative green threads multiplexed onto N native OS threads. This document describes the full architecture, its rationale, and how the components compose.

## 1. GMP Model Mapping

The architecture draws from the Go runtime's GMP (Goroutine-Machine-Processor) model, adapted for a CEK-machine-based parser evaluator rather than a general-purpose language runtime.

| Go Runtime | PraTTaIL | Notes |
|------------|----------|-------|
| G (goroutine) | `GreenThread` (unified CEK machine with im-persistent state) | Persistent data structures enable O(1) fork |
| M (OS thread) | Worker thread in `WorkerPool` | `std::thread::spawn`, named `prattail-worker-N` |
| P (processor) | Worker's local `crossbeam::deque::Worker` | LIFO deque for cache-local scheduling |
| Global run queue | Coordinator's `Injector` + `Scheduler` FSM | FIFO global injection + priority dispatch |
| Local run queue | Per-worker LIFO deque | `Worker<GreenThreadId>` from `crossbeam_deque` |
| Work stealing | `Stealer` handles across workers | Random-victim selection via XorShift64 PRNG |
| GOMAXPROCS | `HillClimber::suggest_worker_count()` | EMA-based hill climbing (same as .NET CLR) |
| Channel ops | `Channel<T>` + `ChannelMap` + `WakeRegistry` | Lock-free MPMC via `crossbeam_channel` |
| `go func()` | `PPar(P, Q)` fork | O(1) via `im::HashMap`/`im::Vector` clone |
| Preemptive yield | Quantum-based cooperative yield | `run_quantum(N)` returns `Yielded` after N CEK steps |

### Key Differences from Go

1. **Cooperative, not preemptive.** Green threads yield at quantum boundaries rather than being interrupted by a signal. This simplifies the scheduler and eliminates safe-point overhead, but requires that each quantum is short enough to maintain responsiveness.

2. **Persistent data structures, not stack copying.** Go copies goroutine stacks on growth. PraTTaIL's green threads use `im::HashMap` (HAMT) and `im::Vector` (RRB tree), so forking is O(1) pointer copy, not O(n) deep copy.

3. **Channel-driven wake-ups, not runqueue polling.** Suspended threads register in a `WakeRegistry`; the coordinator periodically checks channels for pending messages and resumes waiters. This maps directly to Rholang's pi-calculus channel semantics.

## 2. Two-Pool Separation

The architecture separates **scheduling** from **execution** into two pools connected by a lock-free channel.

```text
                    Native Thread Pool
   ┌────────────────────────────────────────────────────────┐
   │                                                        │
   │  ┌─────────────────────────────────────────────────┐  │
   │  │           Coordinator Thread                     │  │
   │  │  ┌──────────────┐   ┌──────────────────────┐    │  │
   │  │  │ Scheduler FSM│   │ WakeRegistry          │    │  │
   │  │  │ (im::OrdMap  │   │ (DashMap<ChannelId,   │    │  │
   │  │  │  ready queue) │   │   Vec<GreenThreadId>>)│    │  │
   │  │  └──────┬───────┘   └──────────┬───────────┘    │  │
   │  │         │                      │                 │  │
   │  │         │    ┌─────────────────┘                 │  │
   │  │         ▼    ▼                                   │  │
   │  │  ┌────────────────────┐                          │  │
   │  │  │ Global Injector     │ crossbeam_deque::Injector│  │
   │  │  │ (FIFO work queue)   │                          │  │
   │  │  └────────┬───────────┘                          │  │
   │  └───────────│─────────────────────────────────────┘  │
   │              │                                        │
   │              │ steal                                   │
   │              ▼                                        │
   │  ┌───────────────────────────────────────────────┐   │
   │  │              Worker Threads (N)                │   │
   │  │                                               │   │
   │  │  ┌─────────┐  ┌─────────┐     ┌─────────┐   │   │
   │  │  │Worker  0 │  │Worker  1│ ··· │Worker N-1│   │   │
   │  │  │┌───────┐│  │┌───────┐│     │┌───────┐│   │   │
   │  │  ││Local  ││◀─▶│Local  ││◀───▶││Local  ││   │   │
   │  │  ││Deque  ││   ││Deque  ││     ││Deque  ││   │   │
   │  │  ││(LIFO) ││   ││(LIFO) ││     ││(LIFO) ││   │   │
   │  │  │└───────┘│  │└───────┘│     │└───────┘│   │   │
   │  │  └─────────┘  └─────────┘     └─────────┘   │   │
   │  │              ← peer steal →                   │   │
   │  └───────────────────────────────────────────────┘   │
   └────────────────────────────────────────────────────────┘

                    Green Thread Pool
   ┌────────────────────────────────────────────────────────┐
   │  ┌──────────┐ ┌──────────┐ ┌──────────┐              │
   │  │ gt#0     │ │ gt#1     │ │ gt#2     │  ···         │
   │  │ E: HAMT  │ │ E: HAMT  │ │ E: HAMT  │              │
   │  │ K: RRB   │ │ K: RRB   │ │ K: RRB   │              │
   │  │ state:   │ │ state:   │ │ state:   │              │
   │  │  Running │ │  Ready   │ │ Suspended│              │
   │  └──────────┘ └──────────┘ └──────────┘              │
   │                                                       │
   │  GreenThreadRegistry (DashMap<GreenThreadId, Thread>) │
   │  ChannelMap (DashMap<ChannelId, ChannelHandle>)        │
   └───────────────────────────────────────────────────────┘
```

**Why two pools?** The coordinator needs exclusive `&mut` access to the `Scheduler` FSM (it uses `im::OrdMap` which requires mutable operations for `insert`/`remove`). Rather than wrapping the Scheduler in a Mutex -- which would serialize all scheduling decisions -- the coordinator runs on a dedicated thread that owns the Scheduler outright. Workers communicate via a lock-free MPSC channel (`crossbeam_channel`), never touching the Scheduler directly.

## 3. Reactive FSM Hierarchy

The runtime is organized as a 5-layer stack of reactive state machines. Each layer follows the pure `(State, Event) -> (State', Vec<Action>)` pattern established in `scheduler.rs`. Actions from one layer become events for adjacent layers.

```text
  ┌─────────────────────────────────────────────────────────────┐
  │  Layer 5: PoolFSM (lifecycle)                                │
  │    Uninitialized ──→ Starting ──→ Running ──→ ShuttingDown   │
  │    Actions: SpawnCoordinator, SpawnWorkers, SignalShutdown   │
  ├─────────────────────────────────────────────────────────────┤
  │  Layer 4: CoordinatorFSM (scheduling decisions)              │
  │    Bootstrapping ──→ Running ──⇄ Scaling ──→ Draining        │
  │    Actions: InjectWork, UnparkWorkers, ForwardToScheduler   │
  ├─────────────────────────────────────────────────────────────┤
  │  Layer 3: SchedulerFSM (priority dispatch)                   │
  │    CheckChannels ──→ DispatchReady ──→ Execute ──→ ParkIdle  │
  │    Actions: WakeThread, SpawnThread, ParkWorkers             │
  ├─────────────────────────────────────────────────────────────┤
  │  Layer 2: WorkerFSM (per-thread execution)                   │
  │    Idle ──→ Executing ──→ Idle, Idle ──→ Parking ──→ Idle    │
  │    Actions: ExecuteQuantum, ReenqueueLocal, ReportToCoord.  │
  ├─────────────────────────────────────────────────────────────┤
  │  Layer 1: GreenThread (unified CEK machine via cek_step())    │
  │    Ready ──→ Running ──→ Completed/Suspended/Yielded/Forked │
  │    Output: QuantumResult enum                                │
  │    State: im::Vector<EvalFrame>, im::HashMap bindings/cache │
  └─────────────────────────────────────────────────────────────┘
```

**Composability.** A `WorkerReport::ThreadCompleted` from Layer 2 becomes a `CoordinatorEvent::WorkerReport(ThreadCompleted)` at Layer 4, which produces `CoordinatorAction::ForwardToScheduler(ThreadCompleted)` sent to Layer 3, which returns `SchedulerAction::NotifyComplete` back to Layer 4 for execution. Each layer is testable in isolation with synthetic event sequences.

## 4. Component Interaction Sequences

### 4.1 Fork Sequence (PPar(P, Q))

```text
  GreenThread gt#0           Worker 0          Coordinator        Scheduler
      │                         │                   │                 │
      │  run_quantum()          │                   │                 │
      │  encounters P|Q         │                   │                 │
      │  returns Forked         │                   │                 │
      │─────────────────────▶  │                   │                 │
      │                         │  ForkAndEnqueue   │                 │
      │                         │  spawn gt#1,gt#2  │                 │
      │                         │  push to local    │                 │
      │                         │ ─ ─ ─ ─ ─ ─ ─ ─▶│                 │
      │                         │   ForkRequested   │                 │
      │                         │                   │──ForkRequest──▶│
      │                         │                   │                 │
      │                         │                   │◀─SpawnThread───│
      │                         │                   │  inject+unpark │
```

### 4.2 Send/Recv Sequence

```text
  gt#1 (sender)    Worker 0     gt#2 (receiver)    Worker 1     Coordinator
      │               │              │                │              │
      │ ch.send(v)     │              │                │              │
      │ Completed      │              │                │              │
      │──────────────▶│              │                │              │
      │               │──report────────────────────────────────────▶│
      │               │              │                │              │
      │               │              │ ch.try_recv()   │              │
      │               │              │ Empty!          │              │
      │               │              │ Suspended       │              │
      │               │              │───────────────▶│              │
      │               │              │                │──report────▶│
      │               │              │                │ ThreadSusp.  │
      │               │              │                │              │
      │               │              │                │  WakeRegistry│
      │               │              │                │  .register() │
      │               │              │                │              │
      │               │              │                │  periodic    │
      │               │              │                │  check_and_  │
      │               │              │                │  wake()      │
      │               │              │                │  ch pending! │
      │               │              │                │  resume gt#2 │
      │               │              │◀────inject─────│──────────────│
      │               │              │   + unpark      │              │
```

### 4.3 Work-Stealing Sequence

```text
  Worker 0 (busy)    Worker 1 (idle)    Injector (global)
      │                    │                    │
      │ local deque:       │ local deque:       │
      │ [gt#3, gt#4]       │ []                 │ []
      │                    │                    │
      │                    │ 1. local.pop()     │
      │                    │    → None          │
      │                    │                    │
      │                    │ 2. injector.steal() │
      │                    │────────────────────▶│
      │                    │    → Empty          │
      │                    │                    │
      │                    │ 3. peer_steal(W0)   │
      │◀───────────────────│ steal()             │
      │  steal gt#3 (FIFO) │                    │
      │  deque: [gt#4]     │ got gt#3!          │
      │                    │ execute quantum    │
```

### 4.4 Shutdown Sequence

```text
  GlobalPool          Coordinator         Worker 0 ··· Worker N-1
      │                    │                 │               │
      │ stop()             │                 │               │
      │ shutdown.store(T)  │                 │               │
      │───────────────────▶│                 │               │
      │                    │ drain reports   │               │
      │                    │ set shutdown    │               │
      │                    │ break loop      │               │
      │                    │                 │               │
      │                    │              unpark_all()       │
      │                    │─────────────────▶──────────────▶│
      │                    │                 │               │
      │                    │           check shutdown → exit │
      │                    │                 │               │
      │ join coordinator   │                 │               │
      │◀───────────────────│                 │               │
```

## 5. Mathematical Model

### Expected Completion Time

Let T₁ be the total work (sum of all CEK steps across all green threads) and T_inf be the critical path length (longest dependency chain). With P workers and optimal work stealing:

```
E[completion time] = O(T₁/P + T_inf)
```

The T₁/P term captures perfect parallelism (splitting work evenly). The T_inf term is the sequential bottleneck: the longest chain of dependent operations (e.g., a sequence of sends that must complete before a join pattern fires). This bound follows from the work-stealing theorem of Blumofe & Leiserson (1999).

### Fork Budget as Admission Control

The fork budget B limits concurrency. Let M(t) be the number of active green threads at time t. The CAS-based budget enforces:

```
M(t) <= B    for all t
```

When `check_budget()` returns false, the fork is deferred (queued in the Scheduler). Budget is replenished atomically when threads complete:

```
check_budget:    B_old > 0  =>  CAS(B, B_old, B_old - 1)  =>  true
                 B_old = 0  =>  false

replenish(k):    fetch_add(B, k)
```

### Throughput Adaptation

The HillClimber measures throughput as tasks completed per interval, smoothed via exponential moving average (EMA):

```
EMA_new = alpha * sample + (1 - alpha) * EMA_old       alpha = 1/4
```

Stored as fixed-point (value * 1024) to avoid floating-point atomics. The direction reversal algorithm:

```
if EMA_new >= EMA_old:
    direction = direction           // continue (grow or shrink)
else:
    direction = -direction          // reverse

workers_new = clamp(workers + direction * step, min_workers, max_workers)
```

## 6. Comparison with Alternatives

| Runtime | Model | Why Not? |
|---------|-------|----------|
| **Rayon** | Fork-join parallelism | No cooperative yielding on channel wait; no channel-based communication model; task granularity tied to data parallelism, not process-algebraic fork |
| **Tokio** | Async I/O (epoll/kqueue) | Designed for I/O-bound workloads; async/await infects all callers; no natural mapping for pi-calculus channels and join patterns |
| **Raw threads** | 1:1 OS threads | No work stealing; thread creation cost prohibitive for thousands of Rholang processes; no cooperative scheduling |
| **async-std** | Similar to Tokio | Same I/O focus; runtime overhead for CPU-bound parsing |
| **Crossbeam scoped threads** | Scoped fork-join | Cannot suspend/resume; no channel wait semantics; lifetime constraints incompatible with persistent green thread state |

### Why a Custom Hybrid

PraTTaIL's runtime must model Rholang's `PPar(P, Q)` semantics:

1. **O(1) fork** via persistent data structures -- neither Rayon nor Tokio support structural sharing of environments.
2. **Channel-based suspension** -- when `for(@x <- ch)` encounters an empty channel, the green thread must suspend (not busy-wait) and resume when a message arrives. This is a pi-calculus primitive, not an I/O event.
3. **Join patterns** -- `for(@x <- a; @y <- b)` requires atomic multi-channel synchronization, which no existing Rust runtime provides.
4. **Compile-time verification** -- the 6-phase GT01-GT06 lint pipeline depends on the scheduler's FSM structure being introspectable at compile time.

The 22 sprints of infrastructure (channels, green threads, scheduler, coordinator, worker pool, pool FSM) enable all four properties simultaneously.

## 7. Source File Map

| File | Role | Layer |
|------|------|-------|
| `pool_fsm.rs` | Pool, Coordinator, Worker FSM types + pure transitions | 5, 4, 2 |
| `global_pool.rs` | `GlobalPool` singleton, `HillClimber`, `AnyScheduler` trait | 5 |
| `coordinator.rs` | `Coordinator` thread, event loop, action dispatch | 4 |
| `scheduler.rs` | `Scheduler` FSM, priority queue, budget, `SchedulerAutomaton` | 3 |
| `worker_pool.rs` | `WorkerPool`, `WorkerParker`, work-stealing loop | 2 |
| `green_thread.rs` | `GreenThread`, `CekThreadState`, `GreenThreadRegistry`, `QuantumResult` | 1 |
| `channel.rs` | `Channel<T>`, `ChannelMap`, `ChannelHandle`, `WakeRegistry`, `ChannelWaiter` | 1 |

## Two-Pool Architecture Drives Unified GreenThreads

After GS-1 unification, the `GreenThread` IS the CEK machine. The existing two-pool
architecture drives these unified GreenThreads without modification — `execute_quantum()`
already calls `thread.run_quantum(quantum_size)`, which now drives real CEK transitions
instead of the previous stub.

### Data Flow: Native Thread Pool → Unified GreenThread

```text
┌─────────────────────────────────────────────────────────────┐
│  Coordinator Thread (owns Scheduler FSM exclusively)        │
│  Receives: WorkerReports via MPSC (lock-free)               │
│  Dispatches: SchedulerActions → Injector push + unpark      │
│  Periodic: WakeRegistry check, HillClimber scale            │
└────────────────┬────────────────────────────────────────────┘
                 │ Injector<GreenThreadId> (global FIFO)
                 ▼
┌────────────┐  ┌────────────┐  ┌────────────┐
│  Worker 0  │  │  Worker 1  │  │  Worker N  │  ← Native OS threads
│ 1. pop tid │  │ 1. pop tid │  │ 1. pop tid │
│ 2. get_mut │  │ 2. get_mut │  │ 2. get_mut │  ← DashMap shard lock
│ 3. run_    │  │ 3. run_    │  │ 3. run_    │  ← Real CEK transitions
│    quantum │  │    quantum │  │    quantum │     on im persistent state
│ 4. match   │  │ 4. match   │  │ 4. match   │  ← QuantumResult dispatch
│    result  │  │    result  │  │    result  │
└────────────┘  └────────────┘  └────────────┘
```

### Quantum Execution Detail

When a worker calls `execute_quantum()`:
1. **Lookup**: `registry.get_mut(tid)` — DashMap shard lock
2. **Transition**: Ready → Running
3. **Step**: `thread.run_quantum(quantum_size)` — internally calls `cek_step()` up to N times
4. **Drop RefMut**: Release shard lock before further action
5. **Dispatch**: Match `QuantumResult` and re-enqueue, report, or fork

### Fork Path (PPar Integration)

When `cek_step()` encounters `EvalFrame::Parallel`:
1. `cek_step()` sets `self.pending_fork = Some(remaining_subterms)`
2. `run_quantum()` detects fork, returns `QuantumResult::Forked { children }`
3. Worker creates children via `registry.spawn_child()` — O(1) `im` structural sharing
4. Children share parent's `continuation`, `eval_bindings`, and `memo_cache` spines
5. Worker pushes children to local deque (LIFO for cache locality)
6. Idle workers steal children (FIFO for load balancing)

### Channel Suspend/Wake Path

1. Thread sets `channel_waiters` → `run_quantum()` returns `Suspended`
2. Worker reports `ThreadSuspended` to coordinator
3. Coordinator registers waiter in `WakeRegistry`
4. Event-driven: `ChannelActivity` report triggers immediate wake check
5. Fallback: periodic polling at 500ms interval
6. Coordinator resumes thread: Suspended → Ready, inject + unpark

## 8. References

- Blumofe, R. & Leiserson, C. (1999). Scheduling multithreaded computations by work stealing. *JACM*, 46(5):720-748.
- Chase, D. & Lev, Y. (2005). Dynamic circular work-stealing deque. *Proceedings of SPAA*, pp. 21-28.
- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*. Cambridge University Press.
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine, and the lambda-calculus. *Formal Description of Programming Concepts III*.
- Stucki, N., Rompf, T. & Ureche, V. (2015). RRB vector: a practical general purpose immutable sequence. *Proceedings of ICFP*.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus. *Proceedings of POPL*, pp. 372-385.
