# M:N Scheduler User Guide

## 1. Feature Flags and Dependencies

The M:N scheduler is gated behind the `green-threads` feature flag, which
transitively enables `cek-runtime`:

```toml
[dependencies]
prattail = { version = "...", features = ["green-threads"] }
```

This pulls in the following dependencies:

| Dependency | Version | Purpose |
|------------|---------|---------|
| `im` | 15.x | Persistent data structures (O(1) fork) |
| `crossbeam-channel` | 0.5 | Lock-free MPMC channels |
| `crossbeam-deque` | 0.8 | Work-stealing deques |
| `dashmap` | 6.x | Lock-free concurrent hash map |
| `num_cpus` | 1.x | Default worker count detection |

The `green-threads` feature enables six modules:

| Module | File | Purpose |
|--------|------|---------|
| `channel` | `channel.rs` | Channel infrastructure, WakeRegistry |
| `green_thread` | `green_thread.rs` | GreenThread, GreenThreadRegistry |
| `scheduler` | `scheduler.rs` | Scheduler FSM, SchedulerAutomaton |
| `global_pool` | `global_pool.rs` | GlobalPool singleton, HillClimber |
| `worker_pool` | `worker_pool.rs` | Native worker threads, work-stealing |
| `coordinator` | `coordinator.rs` | Coordinator thread, wake protocol |

## 2. Environment Variable Configuration

| Variable | Default | Description |
|----------|---------|-------------|
| `PRATTAIL_QUANTUM` | 100 | Maximum CEK steps per green thread quantum. Each green thread runs for at most this many steps before cooperatively yielding. |
| `PRATTAIL_WORKERS` | `num_cpus` | Number of native worker threads. Overrides the HillClimber's adaptive scaling. Set to a fixed value for reproducible benchmarks. |

## 3. API Walkthrough

### 3.1 Lifecycle Overview

```
    GlobalPool::get_or_init()
         │
         ▼
    pool.start(registry, channels)     ── spawns coordinator + N workers
         │
         ▼
    registry.spawn("Proc")             ── create a green thread
         │
         ▼
    pool.submit(thread_id)             ── push to worker injector
         │
         ▼
    (workers execute quanta)           ── automatic: work-stealing loop
         │
         ▼
    pool.stop()                        ── signal shutdown, join threads
```

### 3.2 Core Types

**GlobalPool** (`global_pool.rs`): Process-wide singleton managing native
worker threads shared across all MeTTaIL language instances. Created once
via `get_or_init()`, started/stopped explicitly.

```rust
use mettail_prattail::global_pool::GlobalPool;

let pool = GlobalPool::get_or_init();
// pool is &'static GlobalPool -- lives for the process lifetime
```

**GreenThreadRegistry** (`green_thread.rs`): Thread-safe registry of all
green threads. Uses `DashMap` for concurrent access with sharded locking.

```rust
use mettail_prattail::green_thread::GreenThreadRegistry;
use std::sync::Arc;

let registry = Arc::new(GreenThreadRegistry::new());
```

**ChannelMap** (`channel.rs`): Lock-free concurrent registry of typed
channels. Channels are created with `create_channel()` and looked up by
name or ID.

```rust
use mettail_prattail::channel::{ChannelMap, ChannelCapacity};
use std::sync::Arc;

let channels = Arc::new(ChannelMap::new());
let ch_id = channels.create_channel::<String>("tokens", &ChannelCapacity::Unbounded);
```

**GreenThread** (`green_thread.rs`): A suspendable CEK machine with
persistent environment and continuation stack.

```rust
use mettail_prattail::green_thread::GreenThread;
use mettail_prattail::channel::GreenThreadId;

let mut thread = GreenThread::new(GreenThreadId(0), "Expr");
thread.set_env("Int", "x", "42".to_string());
thread.push_continuation("InfixRHS".to_string());
thread.eval_stack.push_back("work_item".to_string());
```

**Channel\<T\>** (`channel.rs`): Lock-free MPMC channel wrapping
`crossbeam-channel`. Supports typed sends and receives.

```rust
use mettail_prattail::channel::{Channel, ChannelId};

let ch = Channel::<i32>::unbounded(ChannelId(0), "results");
ch.send(42).expect("channel send failed");
let value = ch.try_recv().expect("channel recv failed");
```

### 3.3 Starting and Stopping the Pool

```rust
use mettail_prattail::global_pool::GlobalPool;
use mettail_prattail::green_thread::GreenThreadRegistry;
use mettail_prattail::channel::ChannelMap;
use std::sync::Arc;

let pool = GlobalPool::get_or_init();
let registry = Arc::new(GreenThreadRegistry::new());
let channels = Arc::new(ChannelMap::new());

// Start the runtime: spawns coordinator + N worker threads
pool.start(Arc::clone(&registry), Arc::clone(&channels));

// ... submit work ...

// Stop the runtime: signals shutdown, joins all threads
pool.stop();
```

### 3.4 Spawning and Submitting Green Threads

```rust
// Spawn a root green thread
let tid = registry.spawn("Proc".to_string());

// Add work to the thread's eval stack
{
    let mut thread = registry.get_mut(tid).expect("thread should exist");
    thread.eval_stack.push_back("eval_parallel".to_string());
    thread.eval_stack.push_back("eval_send".to_string());
}

// Submit the thread for execution
pool.submit(tid);
```

### 3.5 Forking (Parallel Composition)

When a Rholang process `P | Q` is encountered, the parent thread forks
into children that share the parent's environment spine:

```rust
// Spawn children sharing the parent's environment
let child_p = registry.spawn_child(parent_id, "Proc".to_string())
    .expect("parent should exist");
let child_q = registry.spawn_child(parent_id, "Proc".to_string())
    .expect("parent should exist");

// Add work to each child
{
    let mut cp = registry.get_mut(child_p).expect("child P");
    cp.eval_stack.push_back("eval_P_body".to_string());
}
{
    let mut cq = registry.get_mut(child_q).expect("child Q");
    cq.eval_stack.push_back("eval_Q_body".to_string());
}

// Submit children for execution
pool.submit(child_p);
pool.submit(child_q);
```

### 3.6 Channel Communication

```rust
use mettail_prattail::channel::{Channel, ChannelCapacity, WakeRegistry};

// Create a channel
let ch_id = channels.create_channel::<String>("results", &ChannelCapacity::Unbounded);

// Send a message (within a green thread's quantum)
let handle = channels.get_channel(ch_id).expect("channel exists");
let ch = handle.downcast::<String>().expect("type mismatch");
ch.send("hello".to_string()).expect("send failed");

// Receive a message (non-blocking)
match ch.try_recv() {
    Ok(msg) => println!("received: {}", msg),
    Err(_) => println!("no message available"),
}

// WakeRegistry: track which threads are waiting on which channels
let wake_reg = WakeRegistry::new();
wake_reg.register(ch_id, tid);  // thread tid is waiting on ch_id

// Check for wake-ups (coordinator calls this periodically)
let to_wake = wake_reg.check_and_wake(&channels);
for (thread_id, channel_id) in to_wake {
    // Resume the thread and re-submit it
    if let Some(mut t) = registry.get_mut(thread_id) {
        t.resume();
    }
    pool.submit(thread_id);
}
```

## 4. Example: Rholang-Style P | Q Evaluation

This end-to-end example creates a simple parallel evaluation of `P | Q`
where P sends a value on a channel and Q receives it.

```rust
use mettail_prattail::global_pool::GlobalPool;
use mettail_prattail::green_thread::GreenThreadRegistry;
use mettail_prattail::channel::{ChannelMap, ChannelCapacity};
use std::sync::Arc;

// 1. Create registry, channels, pool
let pool = GlobalPool::get_or_init();
let registry = Arc::new(GreenThreadRegistry::new());
let channels = Arc::new(ChannelMap::new());

// 2. Start the pool
pool.start(Arc::clone(&registry), Arc::clone(&channels));

// 3. Create a channel for P -> Q communication
let ch_id = channels.create_channel::<String>(
    "result_ch", &ChannelCapacity::Unbounded,
);

// 4. Spawn the parent thread
let parent = registry.spawn("Proc".to_string());

// 5. Fork into P and Q
let child_p = registry.spawn_child(parent, "Proc".to_string())
    .expect("fork P");
let child_q = registry.spawn_child(parent, "Proc".to_string())
    .expect("fork Q");

// 6. Add work: P sends, Q has eval work
{
    let mut p = registry.get_mut(child_p).expect("P exists");
    p.eval_stack.push_back("send_on_result_ch".to_string());
}
{
    let mut q = registry.get_mut(child_q).expect("Q exists");
    q.eval_stack.push_back("recv_from_result_ch".to_string());
}

// 7. Submit both children
pool.submit(child_p);
pool.submit(child_q);

// 8. (In production: wait for completion via metrics or completion channel)

// 9. Stop the pool
pool.stop();
```

## `decompose_into_cek` API Reference

This is a retired production API. Historically, `decompose_into_cek` bridged
language-specific AST nodes to the generic `CekEvaluator`, and the
`language!` macro generated it on `Language` implementations. The current
production `Language` trait no longer exposes this method, generated
languages no longer emit it, and Dovetail/Rho runtime execution enters through
checked `RuntimeBackendReport` values instead.

### Historical Signature

```rust
fn decompose_into_cek(
    &self,
    term: &dyn Term,
    evaluator: &mut CekEvaluator,
) -> bool
```

### Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `term` | `&dyn Term` | Parsed AST node to decompose |
| `evaluator` | `&mut CekEvaluator` | Evaluator whose continuation stack and control term will be set |

### Return Value

- `true`: Frames were pushed onto the evaluator's continuation stack. The
  evaluator is ready to be driven via `step()` or `run_to_completion()`.
- `false`: The term could not be decomposed. The caller should fall through
  to Ascent evaluation.

### Frame Mapping

The generated code inspects each AST variant's `GrammarItem` structure and
pushes the corresponding `EvalFrame`:

| AST Pattern | EvalFrame | Control Set To |
|-------------|-----------|---------------|
| `op(lhs, rhs)` (infix) | `BinOp { operator, lhs_display }` | `display(rhs)` |
| `op(operand)` (prefix) | `UnaryOp { operator }` | `display(operand)` |
| `let x = e in body` | `LetBody { var_name, body_display }` | `display(e)` |
| `t₁ \| t₂ \| ... \| tₙ` | `Parallel { remaining, completed }` | `display(t₁)` |
| `match e { arms }` | `MatchScrutinee { arms_display }` | `display(e)` |
| Literal / Variable | (no frame) | `display(term)` |

### Usage with Green Threads

When a green thread encounters a `Parallel` frame with multiple remaining
sub-terms, `GreenThread::run_quantum()` returns `QuantumResult::Forked`
instead of evaluating sequentially. The worker creates child green threads
(one per sub-term) that share the parent's environment spine via O(1)
`im::HashMap` clone. See
[evaluation-pipeline.md](../architecture/evaluation-pipeline.md) for the
full three-tier evaluation architecture.

### Example

Archived CEK bridge example:

```rust
use mettail_prattail::cek_eval::{CekEvaluator, NullEvalObserver};

// Assuming `language` implements the Language trait:
let term = language.parse_term("(1 + 2) * (3 + 4)").expect("parse");

let mut evaluator = CekEvaluator::new(format!("{}", term));

if language.decompose_into_cek(term.as_ref(), &mut evaluator) {
    let mut obs = NullEvalObserver;
    match evaluator.run_to_completion(&mut obs) {
        Ok(result) => println!("Result: {}", result),
        Err(msg) => eprintln!("Error: {}", msg),
    }
} else {
    // Fall through to Ascent
    let results = language.run_ascent(term.as_ref()).expect("ascent");
    // ... handle results ...
}
```

## Unified GreenThread Constructors

```rust
// Create a thread ready for CEK evaluation
let thread = GreenThread::with_control(id, "Proc", "P | Q".to_string());

// Create with pre-populated bindings (for forked children)
let child = GreenThread::with_control_and_env(
    child_id,
    "Proc",
    "Q".to_string(),
    parent_bindings.clone(), // im::HashMap — O(1) clone
);
```

## 5. Debugging

Enable debug logging to trace worker and coordinator interactions:

```bash
RUST_LOG=debug cargo run --features green-threads
```

The scheduler emits log entries for:
- State transitions (`CheckChannels -> DispatchReady -> Execute -> ...`)
- Thread dispatch and completion events
- Fork budget consumption and replenishment
- Channel wake-ups
- HillClimber throughput observations and worker count suggestions

Metrics are also available programmatically:

```rust
let snap = pool.metrics().snapshot();
println!("tasks executed: {}", snap.total_tasks_executed);
println!("cross-language steals: {}", snap.total_cross_language_steals);
```

## 6. Performance Tuning

### 6.1 Quantum Size

The quantum size (`PRATTAIL_QUANTUM`) controls the granularity of
cooperative scheduling:

| Quantum | Context Switches | Fairness | Overhead |
|---------|-----------------|----------|----------|
| Small (10--50) | Many | High (low latency for all threads) | Higher (more yield/re-enqueue cycles) |
| Medium (100) | Moderate | Good balance | Low |
| Large (500--1000) | Few | Lower (some threads may wait longer) | Minimal |

**Recommendation**: Start with the default (100). Decrease to 10--50 if
latency-sensitive threads are being starved. Increase to 500+ if profiling
shows excessive context-switch overhead.

### 6.2 Worker Count

For CPU-bound workloads (pure parsing/evaluation with no I/O), set
`PRATTAIL_WORKERS` equal to the number of physical cores. For I/O-mixed
workloads (channel communication with external systems), allow the
HillClimber to adapt by not setting the environment variable.

### 6.3 Fork Budget

The default parallel budget is `2 * num_cpus`. This allows twice as many
green threads as workers, providing enough work for work-stealing while
avoiding excessive memory usage. Increase for highly parallel grammars
(many `P | Q` compositions); decrease for memory-constrained environments.

## 7. Key Invariants

These invariants must be maintained by user code interacting with the M:N
scheduler. Violating them may cause deadlocks, panics, or incorrect behavior.

### 7.1 Drop DashMap Guards Before Cross-Operations

DashMap's `RefMut` holds an exclusive shard lock. Holding it across registry
or channel operations can cause deadlocks if another operation needs the
same shard:

```rust
// WRONG: holding RefMut across a registry operation
let mut thread = registry.get_mut(tid).expect("exists");
let child = registry.spawn_child(tid, "Expr".to_string()); // DEADLOCK RISK
thread.state = CekThreadState::Forked { children: vec![child.unwrap()] };

// CORRECT: drop the guard first
{
    let thread = registry.get(tid).expect("exists");
    // read-only access is fine
    drop(thread);
}
let child = registry.spawn_child(tid, "Expr".to_string());
{
    let mut thread = registry.get_mut(tid).expect("exists");
    thread.state = CekThreadState::Forked { children: vec![child.unwrap()] };
}
```

### 7.2 Budget Conservation

Every `check_budget()` call that returns `true` has consumed one budget unit.
It must be matched by a `replenish_budget(1)` call when the corresponding
green thread completes or is cancelled. Failing to replenish leaks budget
units and eventually starves the system.

### 7.3 Channel Operations Within Quanta

Channel sends must happen within a green thread's quantum (inside
`run_quantum()`). Never call `recv_blocking()` from a worker thread -- it
blocks the OS thread and violates the cooperative scheduling contract. Always
use `try_recv()` and yield (return `QuantumResult::Suspended`) if no message
is available.

### 7.4 Workers Never Block

Worker threads must never call blocking operations (`Mutex::lock`,
`Condvar::wait`, `recv_blocking`, `thread::sleep`, etc.) during green thread
execution. The only blocking point is the worker's park/unpark mechanism,
which is controlled by the coordinator and occurs only when the worker has
no work.

```
    Worker run loop:
        loop:
            if let Some(tid) = local_deque.pop() or steal():
                // Execute the green thread's quantum (NON-BLOCKING)
                execute_quantum(tid)
            else:
                // No work: park until coordinator unparks us
                park()
```

## 8. Architecture Diagram

```
    ┌───────────────────────────────────────────────────────────────┐
    │                     GlobalPool (singleton)                    │
    │                                                               │
    │  ┌─────────────┐  ┌──────────────────┐  ┌────────────────┐  │
    │  │ HillClimber │  │ parallel_budget  │  │ GlobalMetrics  │  │
    │  │  (adaptive) │  │  (AtomicU32 CAS) │  │  (AtomicU64s)  │  │
    │  └─────────────┘  └──────────────────┘  └────────────────┘  │
    │                                                               │
    │  ┌────────────────────────────────────────────────────────┐  │
    │  │                  Coordinator Thread                     │  │
    │  │  ┌────────────┐  ┌──────────────┐  ┌──────────────┐   │  │
    │  │  │ Scheduler  │  │ WakeRegistry │  │ report_rx    │   │  │
    │  │  │   (FSM)    │  │  (DashMap)   │  │ (crossbeam)  │   │  │
    │  │  └────────────┘  └──────────────┘  └──────────────┘   │  │
    │  └────────────────────────────────────────────────────────┘  │
    │                                                               │
    │  ┌────────────────────────────────────────────────────────┐  │
    │  │                   Worker Pool (N threads)               │  │
    │  │                                                         │  │
    │  │  Worker 0          Worker 1          Worker N-1         │  │
    │  │  ┌──────────┐     ┌──────────┐     ┌──────────┐       │  │
    │  │  │ local    │     │ local    │     │ local    │       │  │
    │  │  │ deque    │────▶│ stealer  │────▶│ stealer  │       │  │
    │  │  └──────────┘     └──────────┘     └──────────┘       │  │
    │  │       ▲                                                 │  │
    │  │       │  steal                                          │  │
    │  │  ┌────┴──────────────────────────────────────────┐     │  │
    │  │  │           Global Injector (crossbeam)          │     │  │
    │  │  └───────────────────────────────────────────────┘     │  │
    │  └────────────────────────────────────────────────────────┘  │
    │                                                               │
    │  ┌─────────────────────┐  ┌────────────────────────────┐    │
    │  │ GreenThreadRegistry │  │        ChannelMap           │    │
    │  │  (DashMap, shared)  │  │  (DashMap, typed channels)  │    │
    │  └─────────────────────┘  └────────────────────────────┘    │
    └───────────────────────────────────────────────────────────────┘
```
