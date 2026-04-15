# Green Thread Runtime Design

## 1. Motivation

### Why Green Threads?

PraTTaIL generates parsers for languages that include concurrent constructs. Rholang's core semantics are built on the pi-calculus, where parallel composition `P | Q` is a first-class operator. When the generated parser encounters `P | Q`, it must evaluate both `P` and `Q` concurrently, with communication via channels.

Native OS threads are too heavyweight for this: a typical Rholang program may contain thousands of nested parallel compositions. Green threads (cooperatively scheduled, user-space fibers) provide:

1. **Low overhead**: No kernel context switch; a "suspend" writes a few pointers.
2. **Massive concurrency**: Millions of green threads on a single OS thread pool.
3. **Deterministic scheduling**: The scheduler controls interleaving, enabling reproducible verification.

### Why Channels?

Rholang communicates via named channels (`x!(data)` / `for(@v <- x) { ... }`). The channel abstraction maps directly to the pi-calculus semantics. Using `crossbeam_channel` (lock-free MPMC queues) preserves the formal semantics while providing practical performance.

### Why Persistent Data Structures?

When `P | Q` forks, both children need the parent's environment and continuation stack. With mutable `Vec<T>` and `HashMap<K, V>`, forking requires O(n) deep copies. With `im::Vector` and `im::HashMap`, forking is O(1): both children share the parent's tree spine, and subsequent mutations copy-on-write only the affected path.

This is the same approach used by Clojure's persistent data structures and Haskell's `Data.Map`, applied here to the CEK machine's E and K components.

## 2. Channel Infrastructure

### Types

```text
┌───────────────────────────────────────────────────────┐
│                    ChannelMap                          │
│  DashMap<ChannelId, ChannelHandle>  (lock-free)       │
│  DashMap<String, ChannelId>         (name→id)         │
│  AtomicU64                          (next_id)         │
│                                                       │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐   │
│  │ Channel<A>  │  │ Channel<B>  │  │ Channel<C>  │   │
│  │ crossbeam   │  │ crossbeam   │  │ crossbeam   │   │
│  │ sender/recv │  │ sender/recv │  │ sender/recv │   │
│  └─────────────┘  └─────────────┘  └─────────────┘   │
└───────────────────────────────────────────────────────┘
```

| Type | Description | Location |
|------|-------------|----------|
| `ChannelId(u64)` | Unique monotonic channel identifier | `channel.rs:66` |
| `GreenThreadId(u64)` | Unique monotonic thread identifier | `channel.rs:79` |
| `ChannelCapacity` | `Unbounded` or `Bounded(usize)` | `channel.rs:98` |
| `ChannelSpec` | AST from `channels {}` block: name, type, capacity | `channel.rs:131` |
| `JoinChannelRef` | Single channel reference in a join pattern | `channel.rs:173` |
| `JoinPatternSpec` | Multi-channel atomic receive pattern | `channel.rs:193` |
| `ChannelsBlockSpec` | Full `channels {}` block: channels + join patterns | `channel.rs:212` |
| `Channel<T>` | Runtime lock-free MPMC channel (crossbeam) | `channel.rs:249` |
| `ChannelHandle` | Type-erased `Arc<dyn Any + Send + Sync>` | `channel.rs:421` |
| `ChannelMap` | Lock-free concurrent registry (DashMap) | `channel.rs:498` |
| `WaitPattern` | `Single` or `Join(Vec<ChannelId>)` | `channel.rs:635` |
| `ChannelWaiter` | Thread-channel wait registration | `channel.rs:669` |

### Channel Registry

The `ChannelMap` provides:

- `fresh_id()`: Monotonically increasing ID via `AtomicU64::fetch_add`.
- `create_channel<T>(name, capacity)`: Creates channel, registers by ID and name.
- `get_channel(id)` / `get_channel_by_name(name)`: O(1) lookup via DashMap.
- `remove_channel(id)`: Removes both ID and name mappings atomically.

All operations are lock-free (DashMap uses fine-grained shard locks that do not block cross-shard operations).

### Formal Semantics

**Definition 1 (Channel Configuration)**. A channel configuration is a triple `(id, name, buf)` where `id ∈ ℕ`, `name ∈ String`, and `buf ∈ T*` is a finite sequence of buffered messages.

**Definition 2 (Send)**. `ch!(v)` appends `v` to `ch.buf`:
```
⟨ch, buf⟩  →  ⟨ch, buf ++ [v]⟩
```
For bounded channels with capacity κ: the send blocks (green thread yields) if `|buf| ≥ κ`.

**Definition 3 (Receive)**. `for(@x <- ch) { P }` removes the head of `ch.buf` and substitutes:
```
⟨ch, [m₁, m₂, …, mₙ]⟩, P  →  ⟨ch, [m₂, …, mₙ]⟩, P[m₁/x]       if n > 0
⟨ch, []⟩, P                  →  suspend(P, ch)                       if n = 0
```

**Definition 4 (Join)**. `for(@x <- a; @y <- b) { P }` fires only when both channels have messages:
```
⟨a, [m_a, …]⟩, ⟨b, [m_b, …]⟩, P  →  ⟨a, [...]⟩, ⟨b, [...]⟩, P[m_a/x, m_b/y]
```
The join is atomic: either all channels yield a message simultaneously or none do.

## 3. Green Thread Model

### Structure

Each `GreenThread` (defined in `green_thread.rs:142`) contains:

| Field | Type | CEK Role | Description |
|-------|------|----------|-------------|
| `id` | `GreenThreadId` | — | Unique identifier |
| `state` | `CekThreadState` | — | Execution state machine |
| `environment` | `im::HashMap<String, im::HashMap<String, String>>` | **E** | Category → (name → value) |
| `continuation` | `im::Vector<String>` | **K** | Frame tag stack |
| `eval_stack` | `im::Vector<String>` | — | Rewriting eval frames |
| `channel_waiters` | `Vec<ChannelId>` | — | Channels being waited on |
| `parent` | `Option<GreenThreadId>` | — | Parent for tree structure |
| `priority` | `u32` | — | Scheduler priority (lower = higher) |
| `created_at` | `u64` | — | Monotonic age for fairness |
| `category` | `String` | **C** | Grammar category being parsed |

### Fork

`GreenThread::fork(child_id, category)` (defined at `green_thread.rs:222`) creates a child with:

```rust
GreenThread {
    id: child_id,
    state: CekThreadState::Ready,
    environment: self.environment.clone(),   // O(1) — im::HashMap
    continuation: self.continuation.clone(), // O(1) — im::Vector
    eval_stack: self.eval_stack.clone(),     // O(1) — im::Vector
    channel_waiters: Vec::new(),
    parent: Some(self.id),
    priority: self.priority,
    created_at: 0,  // set by registry
    category: category.into(),
}
```

**Theorem (Fork Independence)**. After `child = parent.fork(...)`, any mutation to `child.environment` or `child.continuation` does not modify `parent.environment` or `parent.continuation`, and vice versa.

*Proof sketch.* The `im` crate's `clone()` returns a new root handle pointing to the same shared tree. The `update()` method copies only the path from root to the modified node, creating a new root. The original root (held by the other thread) is unchanged because `im` uses atomic reference counting for shared nodes. ∎

### Join

Join is implicit: when all children of a forked thread reach terminal state (Completed or Failed), the parent's join continuation can fire. The scheduler detects this by checking `children.iter().all(|c| c.is_terminal())`.

### Lifecycle State Diagram

```text
  Ready ──────→ Running ──────→ Completed
    ↑               │                │
    │               ├──→ Suspended   │
    │               │       │        │
    │               │       └──→ Ready (resume)
    │               │
    │               ├──→ Failed
    │               │
    │               └──→ Forked { children: [gt#1, gt#2] }
    │
    └───────────── (initial state from spawn)
```

**Valid transitions** (enforced by `debug_assert!`):

| From | To | Trigger |
|------|----|---------|
| Ready | Running | Scheduler picks thread |
| Running | Suspended { waiting_on } | `thread.suspend(channels)` |
| Running | Completed { result_display } | `thread.complete(result)` |
| Running | Failed { error } | `thread.fail(error)` |
| Running | Forked { children } | Fork creates children |
| Suspended | Ready | `thread.resume()` (channel message arrives) |

## 4. Scheduling

### FSM Design

The `Scheduler` (`scheduler.rs:274`) follows MeTTaTron's `CronStateMachine` reactive pattern:

| State | Description |
|-------|-------------|
| `CheckChannels` | Poll channels for pending messages; wake suspended threads |
| `DispatchReady` | Dequeue highest-priority thread(s) from ready queue |
| `Execute` | Threads running on native workers; await completions/forks |
| `ParkIdle` | No work; yield native worker time slices |
| `Shutdown` | Draining; absorbs all events |

### Transition Table

| Current State | Event | New State | Actions |
|--------------|-------|-----------|---------|
| CheckChannels | ChannelMessage | DispatchReady | — |
| CheckChannels | NoWork | ParkIdle | ParkWorkers |
| CheckChannels | TimerExpired (ready queue non-empty) | DispatchReady | — |
| CheckChannels | TimerExpired (ready queue empty) | ParkIdle | ParkWorkers |
| DispatchReady | * (threads available) | Execute | WakeThread(id)... |
| DispatchReady | * (no threads) | CheckChannels | — |
| Execute | ThreadCompleted | DispatchReady or CheckChannels | NotifyComplete, optionally WakeThread |
| Execute | ForkRequest | Execute | SpawnThread |
| Execute | ChannelMessage | Execute | — (note resumption) |
| ParkIdle | ChannelMessage | CheckChannels | — |
| ParkIdle | ForkRequest | DispatchReady | SpawnThread |
| ParkIdle | TimerExpired | CheckChannels | — |
| ParkIdle | NoWork | ParkIdle | — |
| * | ShutdownRequested | Shutdown | EmitMetrics |
| Shutdown | * | Shutdown | — |

### Adaptive Pool

The `GlobalPool` (`global_pool.rs:322`) is a process-wide singleton managing native workers:

- **Initialization**: `OnceLock::get_or_init()` creates pool with `num_cpus::get()` workers.
- **Budget**: `AtomicU32` shared across all language schedulers. CAS-based acquire/release.
- **Adaptive scaling**: `HillClimber` tunes worker count based on throughput EMA.
- **Cross-language**: Each language registers its `Scheduler` as `Arc<dyn AnyScheduler>`.

### Priority and Fairness

The ready queue uses `im::OrdMap<(u32, u64), GreenThreadId>`:

- `(priority, age)` key ensures lower-priority-value threads run first.
- Within equal priority, older threads (lower `created_at`) run first (FIFO fairness).
- `im::OrdMap` is a persistent balanced tree: O(log n) operations, O(1) snapshot.

## 5. Persistent Data Structure Integration

### im::Vector for Continuation Stacks

The continuation stack uses `im::Vector<String>` (RRB tree) instead of `Vec<String>`:

| Operation | `Vec<String>` | `im::Vector<String>` |
|-----------|--------------|---------------------|
| Clone (fork) | O(n) | O(1) |
| Push back | O(1) amortized | O(log₃₂ n) |
| Pop back | O(1) | O(log₃₂ n) |
| Random access | O(1) | O(log₃₂ n) |
| Memory overhead | 1x | ~1.5x |

The O(1) fork is the critical advantage. For a grammar with 100 frames on the stack, `Vec::clone()` copies 100 strings; `im::Vector::clone()` copies one pointer.

### im::HashMap for Environments

The environment uses `im::HashMap<String, im::HashMap<String, String>>` (HAMT):

| Operation | `HashMap<K,V>` | `im::HashMap<K,V>` |
|-----------|----------------|---------------------|
| Clone (fork) | O(n) | O(1) |
| Lookup | O(1) expected | O(log₃₂ n) |
| Insert/Update | O(1) expected | O(log₃₂ n) |
| Memory overhead | 1x | ~2x |

The two-level structure (category → name → value) mirrors the CEK machine's environment: the outer map is per-category, the inner map is per-variable within that category.

### Why Not Arc<RwLock<HashMap>>?

Shared mutable state via locks introduces:
1. **Contention**: Multiple green threads writing to the same environment would serialize.
2. **Deadlock risk**: Nested locks across channel operations and environment updates.
3. **Non-determinism**: Lock acquisition order may vary, making verification harder.

Persistent data structures eliminate all three: each thread has its own root, mutations are thread-local, and there is no shared mutable state.

## 6. Pipeline Integration

### Codegen Changes

The `language!` macro codegen emits channel infrastructure when the grammar includes a `channels {}` block:

1. **Channel creation**: `ChannelMap::create_channel()` calls for each `ChannelSpec`.
2. **Thread spawning**: `GreenThreadRegistry::spawn()` for the root thread.
3. **Fork points**: At each `P | Q` parallel composition rule, emit `registry.spawn_child()`.
4. **Send/Receive**: At channel send/receive syntax items, emit `channel.send()` / `channel.try_recv()` with scheduler yield on empty.

### Cost-Benefit Gate

| Property | Value |
|----------|-------|
| **Code** | `GT01` |
| **Name** | `GreenThreadForkJoin` |
| **Speedup** | 0.35 (parallelism exploitation) |
| **Cost** | 0.25 (6-phase verification pipeline) |
| **Applicability** | `category_count >= 2` |
| **Status** | `Diagnostic` |

The gate is defined in `cost_benefit.rs` (`Optimization::GreenThreadForkJoin`). It fires when the grammar has at least 2 categories (indicating potential for inter-category parallelism).

### Lint Integration

All GT lints are gated on `feature = "green-threads"` and defined in `lint.rs`:

| Code | Name | Severity | Condition |
|------|------|----------|-----------|
| GT01 | deadlock-detected | Error | Petri net reachable marking with no enabled transitions |
| GT02 | potential-starvation | Warning | Buchi product finds unfair infinite execution |
| GT03 | data-ownership-violation | Error | Register automaton detects unsynchronized access |
| GT04 | channel-freshness-violation | Warning | Nominal analysis detects `new` channel alias escape |
| GT05 | parallelism-report | Note | Petri net independent region count |
| GT06 | stack-depth-estimate | Note | WPDS upper bound on continuation stack depth |

## 7. CekObserver Extension

The `CekObserver` trait (`cek.rs:730`) provides hooks for runtime tracing:

```rust
pub trait CekObserver {
    fn on_event(&mut self, event: &CekStepEvent<'_>) -> CekControl;
    fn on_checkpoint(&mut self, config: &PdaConfiguration) { }
}
```

The green thread runtime extends this pattern via `EvalObserver` (`cek_eval.rs:308`):

```rust
pub trait EvalObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl;
}
```

**Observer implementations**:

| Observer | Module | Purpose |
|----------|--------|---------|
| `TracingObserver` | `cek.rs` | Records parse CEK trace statistics |
| `NullObserver` | `cek.rs` | Zero-cost no-op (inlined away) |
| `TracingEvalObserver` | `cek_eval.rs` | Records eval CEK trace + optional event log |
| `NullEvalObserver` | `cek_eval.rs` | Zero-cost no-op for batch evaluation |
| `AbortAfterObserver` | `cek_eval.rs` | Aborts after N steps (testing/cancel) |

The evaluator (`CekEvaluator` in `cek_eval.rs:536`) provides external driving methods for integration with green threads:

- `emit_bind(name, value, observer)`: Record a variable binding.
- `emit_apply(observer)`: Record a rewrite rule application.
- `emit_descend(subterm, frame, observer)`: Push frame and enter subterm.

When a green thread encounters a `Parallel { remaining, completed }` frame (`cek_eval.rs:887`), the single-threaded evaluator processes subterms left-to-right. A concurrent evaluator distributes them across green threads via `fork()`.

## 8. Worked Example

### Rholang Source

```rholang
new x in {
  x!(5) | for(@v <- x) { v + 1 }
}
```

### Step-by-Step Trace

**Step 1: Parse and spawn root thread.**

```text
Root thread gt#0:
  C = parse(new x in { x!(5) | for(@v <- x) { v + 1 } })
  E = {}
  K = []
  state = Ready
```

**Step 2: Channel creation (`new x`).**

The `new x in { ... }` construct creates a fresh channel:

```text
ChannelMap:
  ch#0 → Channel<i64>("x", unbounded)

gt#0.environment:
  { "Chan" → { "x" → "ch#0" } }
```

**Step 3: Fork at parallel composition (`|`).**

The parser encounters `x!(5) | for(@v <- x) { v + 1 }`:

```text
gt#0.state = Forked { children: [gt#1, gt#2] }

gt#1 (send process):
  C = parse(x!(5))
  E = { "Chan" → { "x" → "ch#0" } }     ← O(1) clone from gt#0
  K = []
  state = Ready

gt#2 (receive process):
  C = parse(for(@v <- x) { v + 1 })
  E = { "Chan" → { "x" → "ch#0" } }     ← O(1) clone from gt#0
  K = []
  state = Ready
```

**Step 4: Scheduler dispatches gt#1 and gt#2.**

```text
Scheduler ready_queue: [(0, 0, gt#1), (0, 1, gt#2)]
Scheduler.state: DispatchReady → Execute
Actions: [WakeThread(gt#1), WakeThread(gt#2)]
```

**Step 5: gt#1 executes send.**

```text
gt#1 Running:
  channel "x" (ch#0).send(5)
  gt#1.state = Completed { result_display: "()" }

ChannelMap ch#0.buf = [5]
```

**Step 6: gt#2 executes receive.**

```text
gt#2 Running:
  channel "x" (ch#0).try_recv() → Ok(5)
  gt#2.environment:
    { "Chan" → { "x" → "ch#0" }, "Int" → { "v" → "5" } }
  Evaluate: v + 1 = 5 + 1 = 6
  gt#2.state = Completed { result_display: "6" }
```

**Step 7: All children complete.**

```text
Scheduler: ThreadCompleted(gt#1), ThreadCompleted(gt#2)
All children of gt#0 complete → join fires
Final result: 6
```

### Timing Scenario (if gt#2 runs before gt#1)

If the scheduler dispatches gt#2 first:

```text
gt#2 Running:
  channel "x" (ch#0).try_recv() → Err(Empty)
  gt#2.state = Suspended { waiting_on: [ch#0] }
  ch#0.register_waiter() → waiter_count = 1

gt#1 Running:
  channel "x" (ch#0).send(5)
  ch#0.buf = [5]

Scheduler: ChannelMessage { channel_id: ch#0 }
  ch#0.unregister_waiter() → waiter_count = 0
  gt#2.resume() → Ready

gt#2 Running:
  channel "x" (ch#0).try_recv() → Ok(5)
  gt#2.state = Completed { result_display: "6" }
```

The result is the same regardless of scheduling order, as guaranteed by the pi-calculus semantics.

## 9. Files Modified/Created

### Files Created

| File | Description |
|------|-------------|
| `prattail/src/channel.rs` | Channel infrastructure: Channel<T>, ChannelMap, ChannelHandle, ChannelWaiter, JoinPatternSpec |
| `prattail/src/green_thread.rs` | GreenThread, CekThreadState, GreenThreadRegistry |
| `prattail/src/scheduler.rs` | Scheduler FSM, SchedulerMetrics, SchedulerAction |
| `prattail/src/global_pool.rs` | GlobalPool singleton, HillClimber, AnyScheduler trait |

### Files Modified

| File | Change |
|------|--------|
| `prattail/src/lib.rs` | `#[cfg(feature = "green-threads")] pub mod channel;` + `green_thread`, `scheduler`, `global_pool` |
| `prattail/src/cost_benefit.rs` | `Optimization::GreenThreadForkJoin` variant, GT01 gate |
| `prattail/src/lint.rs` | GT01-GT06 lint functions (`lint_gt01_deadlock`, etc.) |
| `prattail/Cargo.toml` | `green-threads = ["cek-runtime", "dep:im", "dep:crossbeam-channel", "dep:dashmap", "dep:num_cpus"]` feature |

## 10. Optimization Gates

### GT01: GreenThreadForkJoin

| Property | Value |
|----------|-------|
| **Code** | `GT01` |
| **Name** | `GreenThreadForkJoin` |
| **Speedup** | 0.35 |
| **Cost** | 0.25 |
| **Applicability** | `category_count >= 2` |
| **Status** | `Diagnostic` |
| **Feature gate** | `green-threads` |

**Description**: Determines whether parallel fork/join execution is beneficial for the grammar's channel operations. Uses the 6-phase verification pipeline to ensure safety before enabling parallelism.

### CEK02: CekTracedParser

| Property | Value |
|----------|-------|
| **Code** | `CEK02` |
| **Name** | `CekTracedParser` |
| **Speedup** | 0.0 (diagnostic only) |
| **Cost** | 0.1 |
| **Applicability** | Always |
| **Status** | `Diagnostic` |
| **Feature gate** | `cek-runtime` |

**Description**: Enables the `CekObserver` tracing infrastructure for runtime CEK transition recording. Used by green threads for per-thread execution traces.

## 11. Lints

### GT01: deadlock-detected

| Property | Value |
|----------|-------|
| **Code** | `GT01` |
| **Name** | `deadlock-detected` |
| **Severity** | Error |
| **Feature gate** | `green-threads` |
| **Message** | "Deadlock detected in `{grammar_name}`: threads [{blocked}] are blocked on empty channels [{empty}]" |
| **Hint** | "Ensure at least one active thread can send to {empty}" |

Fires when the Petri net constructed from the `channels {}` block has a reachable marking where no transition is enabled but not all threads are complete. This indicates a circular-wait deadlock.

### GT02: potential-starvation

| Property | Value |
|----------|-------|
| **Code** | `GT02` |
| **Name** | `potential-starvation` |
| **Severity** | Warning |
| **Feature gate** | `green-threads` |
| **Message** | "Thread `{thread_name}` may starve in `{grammar_name}`: Buchi analysis found infinite execution without progress" |
| **Hint** | "Add fairness constraint or reduce priority inversion" |

Fires when the Buchi automaton product finds an infinite execution where some thread never makes progress (violates `GF(thread_i progresses)`).

### GT03: data-ownership-violation

| Property | Value |
|----------|-------|
| **Code** | `GT03` |
| **Name** | `data-ownership-violation` |
| **Severity** | Error |
| **Feature gate** | `green-threads` |
| **Message** | "Channel `{channel}` accessed concurrently by threads [{threads}] without synchronization in `{grammar_name}`" |
| **Hint** | "Use `new` to create a private channel or introduce a mutex pattern" |

Fires when the register automaton analysis detects concurrent access to a channel's buffer register by multiple threads without synchronization.

### GT04: channel-freshness-violation

| Property | Value |
|----------|-------|
| **Code** | `GT04` |
| **Name** | `channel-freshness-violation` |
| **Severity** | Warning |
| **Feature gate** | `green-threads` |
| **Message** | "Channel `{channel}` created with `new` escapes via rule `{rule}` in `{grammar_name}`" |
| **Hint** | "Restrict channel scope or use explicit export" |

Fires when the nominal automaton analysis detects that a channel created with `new` has been aliased, breaking name-hiding guarantees.

### GT05: parallelism-report

| Property | Value |
|----------|-------|
| **Code** | `GT05` |
| **Name** | `parallelism-report` |
| **Severity** | Note |
| **Feature gate** | `green-threads` |
| **Message** | "{N} independent parallel region(s) detected; max {M} concurrent green threads" |
| **Hint** | None |

Informational lint reporting the maximum number of independent parallel regions detected by the Petri net analysis.

### GT06: stack-depth-estimate

| Property | Value |
|----------|-------|
| **Code** | `GT06` |
| **Name** | `stack-depth-estimate` |
| **Severity** | Note |
| **Feature gate** | `green-threads` |
| **Message** | "Category `{category}` in `{grammar_name}`: WPDS estimates max stack depth {depth}" |
| **Hint** | "Preallocate continuation stack to {depth}" |

Reports the WPDS-computed upper bound on green thread continuation stack depth for each category.

## 12. References

- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*. Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus. *Proceedings of POPL*, pp. 372-385.
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine, and the lambda-calculus. *Formal Description of Programming Concepts III*.
- Stucki, N., Rompf, T. & Ureche, V. (2015). RRB vector: a practical general purpose immutable sequence. *Proceedings of ICFP*.
- Bagwell, P. (2001). Ideal hash trees. *EPFL Technical Report*.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University Press.
- Petri, C. A. (1962). *Kommunikation mit Automaten*. Ph.D. thesis, University of Bonn.
- Reps, T., Lal, A. & Kidd, N. (2007). Program analysis using weighted pushdown systems. *FSTTCS*.
- Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge University Press.
