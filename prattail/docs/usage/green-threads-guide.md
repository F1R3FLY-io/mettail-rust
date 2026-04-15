# Green Threads Usage Guide

## 1. Overview

PraTTaIL green threads enable concurrent evaluation of parallel process
compositions (`P | Q`) within a grammar's generated parser and evaluator. Each
green thread is a **suspendable CEK machine** with a persistent continuation
stack (`im::Vector`) and environment (`im::HashMap`), communicating through
lock-free MPMC channels (crossbeam-channel). The scheduler is a pure
finite-state machine adapted from MeTTaTron's `CronStateMachine` pattern.

Green threads are designed for grammars that model concurrent languages such as
Rholang, CCS, CSP, or the pi-calculus. For purely sequential grammars, the
standard single-threaded CEK machine suffices.

**Key source files**:

| File | Purpose |
|------|---------|
| `prattail/src/green_thread.rs` | `GreenThread`, `GreenThreadRegistry`, `CekThreadState` |
| `prattail/src/channel.rs` | `Channel<T>`, `ChannelMap`, `ChannelHandle`, `ChannelWaiter`, `JoinPatternSpec` |
| `prattail/src/scheduler.rs` | `Scheduler`, `SchedulerState`, `SchedulerEvent`, `SchedulerAction`, `SchedulerMetrics` |
| `prattail/src/cek.rs` | `CekObserver`, `CekStepEvent`, `PdaTrace` (runtime tracing) |

## 2. Enabling Green Threads

Add the `green-threads` feature to your `Cargo.toml`:

```toml
[dependencies]
mettail-prattail = { version = "0.1", features = ["green-threads"] }
```

This transitively enables:

| Feature | Dependency | Purpose |
|---------|-----------|---------|
| `cek-runtime` | (built-in) | Runtime tracing, `CekObserver` trait |
| `im` | `im` crate | Persistent data structures (O(1) fork) |
| `crossbeam-channel` | `crossbeam-channel` crate | Lock-free MPMC channels |
| `dashmap` | `dashmap` crate | Lock-free concurrent hash maps |
| `num_cpus` | `num_cpus` crate | Adaptive parallel budget |

## 3. Grammar Requirements

To use green threads, your grammar must define process-algebraic constructs.
The following AST categories are expected:

| Category | Grammar Syntax | Semantic Rule |
|----------|---------------|---------------|
| `PPar` | `P \| Q` (parallel composition) | FORK: spawns two child green threads |
| `PNew` | `new x in { P }` (channel creation) | NEW: creates a fresh channel |
| `POutput` | `x!(v)` (channel send) | SEND: enqueues message on channel |
| `PInput` | `for(@v <- x) { P }` (channel receive) | RECEIVE: dequeues or suspends |

Example grammar fragment:

```
language! {
    category Proc {
        rule PPar: Proc "|" Proc;
        rule PNew: "new" @name "in" "{" Proc "}";
        rule POutput: @chan "!" "(" Expr ")";
        rule PInput: "for" "(" "@" @var "<-" @chan ")" "{" Proc "}";
        rule PNil: "Nil";
    }

    channels {
        stdout: Channel<String>;
        signals: Channel;
    }
}
```

## 4. Channel API

### Creating Channels

Channels are created either statically via the `channels {}` block or
dynamically via the `NEW` rule at runtime:

```rust
use mettail_prattail::channel::*;

// Static: create a channel map from grammar specs.
let map = ChannelMap::new();
let id = map.create_channel::<String>("stdout", &ChannelCapacity::Unbounded);

// Bounded channel (backpressure at 1024 messages):
let id_bounded = map.create_channel::<i64>("events", &ChannelCapacity::Bounded(1024));
```

### Sending Messages

```rust
let handle = map.get_channel(id).expect("channel must exist");
let ch = handle.downcast::<String>().expect("type mismatch");
ch.send("hello".to_string()).expect("channel disconnected");
```

### Receiving Messages

```rust
// Non-blocking (preferred in green-thread contexts):
match ch.try_recv() {
    Ok(msg) => { /* process msg */ }
    Err(crossbeam_channel::TryRecvError::Empty) => { /* yield to scheduler */ }
    Err(crossbeam_channel::TryRecvError::Disconnected) => { /* channel closed */ }
}

// Blocking (for tests or non-green-thread contexts):
let msg = ch.recv_blocking().expect("channel disconnected");
```

### Closing Channels

Channels are closed implicitly when all `Sender` halves are dropped. The
`ChannelMap::remove_channel()` method removes the channel from the registry
and drops the handle, which closes it if no other references exist.

### Join Patterns

For simultaneous multi-channel receive (`for (@x <- a; @y <- b) { ... }`):

```rust
use mettail_prattail::channel::*;

let waiter = ChannelWaiter::join(
    GreenThreadId(1),        // waiting thread
    ChannelId(10),           // primary channel
    vec![ChannelId(20)],     // additional channels
);
// The scheduler wakes the thread only when ALL channels have messages.
assert!(waiter.is_join());
assert_eq!(waiter.all_channels(), vec![ChannelId(10), ChannelId(20)]);
```

## 5. Scheduler Configuration

### Pool Size (Parallel Budget)

The default parallel budget equals the number of CPU cores. Override it:

```rust
use mettail_prattail::scheduler::*;
use mettail_prattail::channel::ChannelMap;
use mettail_prattail::green_thread::GreenThreadRegistry;
use std::sync::Arc;

let registry = Arc::new(GreenThreadRegistry::new());
let channels = Arc::new(ChannelMap::new());

// Explicit budget of 8 concurrent green threads:
let mut scheduler = Scheduler::with_budget(registry, channels, 8);
```

### Priority

Lower priority value = higher scheduling priority (0 is highest). Threads with
equal priority are dispatched FIFO by creation age:

```rust
// Enqueue a high-priority thread (priority=0):
scheduler.enqueue(thread_id, 0);

// Enqueue a background thread (priority=10):
scheduler.enqueue(background_id, 10);
```

### Fairness

The scheduler guarantees **bounded starvation**: within each priority level,
threads are dispatched in FIFO order by their `created_at` timestamp (a
monotonic counter). The `im::OrdMap<(u32, u64), GreenThreadId>` ready queue
sorts by `(priority ASC, age ASC)`, ensuring that older threads at the same
priority level are served first.

### Event-Driven Loop

The scheduler is a pure FSM. Drive it with events:

```rust
// Polling mode:
let actions = scheduler.tick();
for action in actions {
    match action {
        SchedulerAction::WakeThread(tid) => { /* dispatch tid to worker */ }
        SchedulerAction::ParkWorkers => { /* yield time slice */ }
        SchedulerAction::SpawnThread { parent, category } => { /* fork */ }
        SchedulerAction::NotifyComplete { thread_id, result } => { /* cleanup */ }
        SchedulerAction::EmitMetrics => { /* log metrics */ }
    }
}

// Event-driven mode:
let transition = scheduler.process_event(SchedulerEvent::ThreadCompleted {
    thread_id: GreenThreadId(1),
});
// transition.new_state, transition.actions
```

## 6. Debugging Green Threads

### CekObserver Events

Enable the `cek-runtime` feature (transitively enabled by `green-threads`) to
receive per-thread trace events:

```rust
use mettail_prattail::cek::*;

let mut observer = TracingObserver::with_checkpoint_interval(10);

// After parsing, inspect per-thread traces:
let snapshot = observer.trace.clone();
println!("Steps: {}, Max depth: {}", snapshot.steps, snapshot.max_depth);
for (rule, count) in &snapshot.rule_counts {
    println!("  {}: {}", rule, count);
}
```

### Per-Thread Traces

Each green thread can be individually inspected via the registry:

```rust
use mettail_prattail::green_thread::*;

let registry = GreenThreadRegistry::new();
let tid = registry.spawn("Proc".to_string());

// Inspect thread state:
if let Some(thread) = registry.get(tid) {
    println!("State: {}", thread.state);
    println!("Stack depth: {}", thread.stack_depth());
    println!("Env size: {}", thread.env_size());
    println!("Category: {}", thread.category);
}
```

### Scheduler Metrics

```rust
let snapshot = scheduler.metrics().snapshot();
println!("Dispatched: {}", snapshot.total_dispatched);
println!("Completed: {}", snapshot.total_completed);
println!("Forks: {}", snapshot.total_forks);
println!("Suspensions: {}", snapshot.total_suspensions);
println!("Resumptions: {}", snapshot.total_resumptions);
println!("Max concurrent: {}", snapshot.max_concurrent_threads);
```

## 7. Diagnostics

The following diagnostic codes are emitted by the thread-safety verification
pipeline (see `prattail/docs/theory/thread-safety-pipeline.md`):

| Code | Severity | Phase | Description |
|------|----------|-------|-------------|
| GT01 | Error | 1 (Nominal) | Undefined channel: `send` or `recv` references a channel not declared in the `channels {}` block and not created by a `new` operation in scope. |
| GT02 | Error | 1 (Nominal) | Send after close: a `send` operation targets a channel that has already been closed or removed from the channel map. |
| GT03 | Warning | 2 (Register) | Channel aliasing: two distinct channel names are bound to the same `ChannelId`, which may cause unexpected message interleaving. |
| GT04 | Warning | 2 (Register) | Register overflow: the number of simultaneously live channels exceeds the declared capacity, suggesting missing `close` operations. |
| GT05 | Warning | 3 (Petri Net) | Unbounded channel growth: Karp-Miller analysis shows a channel place has `omega` marking, indicating potential memory exhaustion. |
| GT06 | Info | 5 (Buchi) | Message starvation: a sent message may never be received under some fair schedules, suggesting a missing receiver or unbalanced send/recv pattern. |

## 8. Example

A complete Rholang-style example demonstrating parallel composition, channel
creation, send, and receive:

```
language! {
    category Proc {
        rule PPar:    Proc "|" Proc;
        rule PNew:    "new" @name "in" "{" Proc "}";
        rule POutput: @chan "!" "(" Value ")";
        rule PInput:  "for" "(" "@" @var "<-" @chan ")" "{" Proc "}";
        rule PNil:    "Nil";
    }

    category Value {
        rule VInt:    r"[0-9]+";
        rule VString: r#""[^"]*""#;
        rule VVar:    r"[a-z][a-zA-Z0-9]*";
    }

    channels {
        result: Channel<Value> bounded(16);
    }
}
```

Sample input:

```
new x in {
    x!(42) | for (@v <- x) { result!(v) }
}
```

Execution trace:

```
1. Root thread t0 evaluates PNew: creates fresh channel x (ch#0).
2. t0 evaluates PPar: forks into t1 (x!(42)) and t2 (for(@v <- x) { ... }).
3. Scheduler dispatches t1 (priority=0, age=1):
   t1 evaluates POutput: sends 42 on ch#0. t1 completes.
4. Scheduler dispatches t2 (priority=0, age=2):
   t2 evaluates PInput: try_recv on ch#0 succeeds (42).
   Binds v=42, evaluates body: result!(42). t2 completes.
5. All threads completed. Channel result contains [42].
```
