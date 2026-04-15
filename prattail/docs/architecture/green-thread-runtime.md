# Green Thread Runtime Architecture

PraTTaIL's green thread runtime extends the CEK machine architecture to support concurrent evaluation of parallel compositions (`P | Q`), modeled after the Rholang pi-calculus. The runtime is a 4-layer stack: lock-free channels, persistent-data-structure green threads, an FSM-driven scheduler, and a 6-phase verification pipeline.

## 1. Overview

```text
┌─────────────────────────────────────────────────────────────────────┐
│                 Layer 4: Verification Pipeline                       │
│  ┌──────────┐ ┌────────────┐ ┌──────────┐ ┌───────┐ ┌─────┐ ┌───┐│
│  │ Nominal  │ │ Register   │ │ Petri Net│ │ WPDS  │ │Buchi│ │KAT││
│  │ Scope    │ │ Allocation │ │ Safety   │ │ Stack │ │Live.│ │Eq.││
│  │ Analysis │ │ Analysis   │ │ Analysis │ │ Refine│ │Check│ │Chk││
│  └──────────┘ └────────────┘ └──────────┘ └───────┘ └─────┘ └───┘│
├─────────────────────────────────────────────────────────────────────┤
│                 Layer 3: Scheduling                                  │
│  ┌──────────────────┐  ┌─────────────────────────────────────────┐ │
│  │   Scheduler FSM   │  │           GlobalPool Singleton          │ │
│  │ (CronStateMachine)│  │  HillClimber + AnyScheduler registry   │ │
│  │ im::OrdMap queue  │  │  AtomicU32 shared budget + OnceLock    │ │
│  └──────────────────┘  └─────────────────────────────────────────┘ │
├─────────────────────────────────────────────────────────────────────┤
│                 Layer 2: Green Threads                               │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  GreenThread { id, state, environment, continuation, ... }  │   │
│  │  im::HashMap<String, im::HashMap<String, String>> (E)       │   │
│  │  im::Vector<String> (K)                                     │   │
│  │  GreenThreadRegistry (DashMap<GreenThreadId, GreenThread>)  │   │
│  └─────────────────────────────────────────────────────────────┘   │
├─────────────────────────────────────────────────────────────────────┤
│                 Layer 1: Channels                                    │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │  Channel<T> (crossbeam_channel MPMC, lock-free)              │  │
│  │  ChannelMap (DashMap<ChannelId, ChannelHandle>, lock-free)   │  │
│  │  JoinPatternSpec (multi-channel atomic receive)              │  │
│  │  ChannelWaiter (Single | Join)                               │  │
│  └──────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Component Map

| Concept | Implementation | Location |
|---------|---------------|----------|
| Channel (pi-calculus name) | `Channel<T>` wrapping `crossbeam_channel` | `channel.rs` |
| Channel registry | `ChannelMap` (DashMap + AtomicU64 ID counter) | `channel.rs` |
| Type-erased channel handle | `ChannelHandle` (`Arc<dyn Any + Send + Sync>`) | `channel.rs` |
| Channel capacity | `ChannelCapacity::Unbounded \| Bounded(n)` | `channel.rs` |
| Join pattern | `JoinPatternSpec` + `WaitPattern::Join` | `channel.rs` |
| Green thread (suspendable CEK) | `GreenThread` with `im` persistent data structures | `green_thread.rs` |
| Thread state machine | `CekThreadState` (Ready/Running/Suspended/Completed/Failed/Forked) | `green_thread.rs` |
| Thread registry | `GreenThreadRegistry` (DashMap + AtomicU64) | `green_thread.rs` |
| Scheduler FSM | `Scheduler` (State x Event -> Transition) | `scheduler.rs` |
| Priority queue | `im::OrdMap<(u32, u64), GreenThreadId>` | `scheduler.rs` |
| Scheduler metrics | `SchedulerMetrics` (8 AtomicU64 counters) | `scheduler.rs` |
| Process-global pool | `GlobalPool` (OnceLock singleton) | `global_pool.rs` |
| Adaptive scaling | `HillClimber` (EMA throughput, direction reversal) | `global_pool.rs` |
| Language-agnostic scheduler | `AnyScheduler` trait (Send + Sync) | `global_pool.rs` |
| Fork budget | `AtomicU32` CAS-based semaphore | `scheduler.rs`, `global_pool.rs` |
| CEK observer | `CekObserver` trait, `TracingObserver`, `NullObserver` | `cek.rs` |
| Eval CEK | `CekEvaluator` (control/environment/continuation) | `cek_eval.rs` |
| Petri net model | `PetriNet` (places = channels, transitions = actions) | `petri.rs` |
| Deadlock detection | `check_deadlock()` on constructed Petri net | `petri.rs` |
| Liveness checking | `WeightedBuchiAutomaton` product emptiness | `buchi.rs` |
| Program equivalence | `KatExpr` + `check_equivalence()` | `kat.rs` |
| Safety verification | `check_safety()` via WPDS prestar | `verify.rs` |

## 3. Layer 1: Channels

Channels are the communication primitive, modeled after the pi-calculus (Milner, 1999). Each channel is a lock-free MPMC queue backed by `crossbeam_channel`.

### Formal Semantics

A channel `ch ∈ Chan` with capacity `κ ∈ ℕ ∪ {∞}` has operational rules:

```
         ch.buf = [m₁, …, mₙ],  n < κ
SEND  ─────────────────────────────────────
         ch!(v)  →  ch.buf = [m₁, …, mₙ, v]

         ch.buf = [m₁, m₂, …, mₙ],  n > 0
RECV  ─────────────────────────────────────────
         for(@x <- ch) { P }  →  P[m₁/x],  ch.buf = [m₂, …, mₙ]
```

### Petri Net Correspondence

Each channel maps to a Petri net place; each send/receive maps to a transition:

| Channel Concept | Petri Net Element |
|----------------|-------------------|
| Channel | Place (tokens = buffered messages) |
| Send operation | Transition consuming from source, producing into channel place |
| Receive operation | Transition consuming from channel place, producing into destination |
| Join pattern | Transition with multiple input arcs (atomic multi-channel receive) |
| Channel capacity | Place bound (for bounded Petri net analysis) |

### Waiter Protocol

When a green thread blocks on `recv`, the scheduler:

1. Calls `channel.register_waiter()` (atomic increment).
2. Creates a `ChannelWaiter` record (thread_id, channel_id, pattern).
3. Transitions the thread to `Suspended { waiting_on: [channel_id] }`.
4. When a message arrives, calls `channel.unregister_waiter()` and transitions to `Ready`.

For join patterns (`WaitPattern::Join`), the scheduler waits until ALL referenced channels have messages before waking the thread.

## 4. Layer 2: Green Threads

A green thread is a suspendable CEK machine with **owned** persistent data structures.

### CEK Mapping

| CEK Component | Green Thread Field | Data Structure |
|---------------|-------------------|----------------|
| **C** (Control) | `category` + scheduler dispatch | Token-driven prefix dispatch |
| **E** (Environment) | `environment: im::HashMap<String, im::HashMap<String, String>>` | Persistent hash map |
| **K** (Kontinuation) | `continuation: im::Vector<String>` | Persistent RRB tree |
| (Eval stack) | `eval_stack: im::Vector<String>` | Persistent RRB tree |

### Fork Semantics

Fork implements Rholang's parallel composition `P | Q`:

```
          parent = ⟨C, E, K⟩
FORK  ──────────────────────────────────────────
          child₁ = ⟨C₁, E.clone(), K.clone()⟩     O(1) via im crate
          child₂ = ⟨C₂, E.clone(), K.clone()⟩     structural sharing
```

The `im::HashMap::clone()` and `im::Vector::clone()` operations are O(1) because they copy a root pointer to a shared balanced tree. Subsequent mutations copy-on-write only the path from root to the modified node.

### State Machine

```text
  Ready ──────→ Running ──────→ Completed
    ↑               │                │
    │               ├──→ Suspended   │
    │               │       │        │
    │               │       └──→ Ready (resume)
    │               │
    │               ├──→ Failed
    │               │
    │               └──→ Forked { children }
    │
    └───────────── (initial state from spawn)
```

**Invariant**: Only `Running → Suspended`, `Running → Completed`, `Running → Failed`, `Running → Forked`, and `Suspended → Ready` transitions are valid. Debug-mode assertions enforce this.

## 5. Layer 3: Scheduling

The scheduler is a pure FSM adapted from MeTTaTron's `CronStateMachine`:

```text
    ┌──────────────┐  channel msg   ┌───────────────┐  threads ready  ┌──────────┐
    │ CheckChannels │──────────────→│ DispatchReady  │──────────────→│ Execute  │
    └──────────────┘               └───────────────┘               └──────────┘
          ↑                               ↑                              │
          │                               │                              │ thread done
          │         no work               │                              │ or fork
          │    ┌──────────┐               │                              │
          └────│ ParkIdle │←──────────────┴──────────────────────────────┘
               └──────────┘
                     │
                     │ shutdown
                     ▼
               ┌──────────┐
               │ Shutdown │
               └──────────┘
```

### Transition Function

`process_event : (State, Event) → (State', Vec<Action>)`

The scheduler does NOT execute actions itself; the caller (pool driver) executes `SchedulerAction` variants and feeds resulting events back:

| Action | Effect |
|--------|--------|
| `WakeThread(id)` | Move thread from Suspended/Ready to Running |
| `SpawnThread { parent, category }` | Fork a child via the registry |
| `ParkWorkers` | Yield native worker time slices |
| `NotifyComplete { thread_id, result }` | Signal completion to parent |
| `EmitMetrics` | Snapshot scheduler counters |

### Priority Queue

The ready queue is `im::OrdMap<(u32, u64), GreenThreadId>`:

- **Key**: `(priority, age)` where lower priority value = higher scheduling priority.
- **age**: Monotonic counter ensuring FIFO within equal priorities.
- `im::OrdMap` is a persistent balanced tree: O(log n) insert/remove, O(1) clone (structural sharing).

### Fork Budget

An `AtomicU32` limits concurrent green threads. Fork requests that exceed the budget are queued. Budget is replenished when threads complete. The CAS-based `check_budget()` is lock-free.

## 6. Layer 4: Verification

The 6-phase verification pipeline statically analyzes the `channels {}` block and grammar rules to detect concurrency errors at compile time. See `prattail/docs/design/thread-safety-verification.md` for the full design.

| Phase | Analysis | Module | Detects |
|-------|----------|--------|---------|
| 1 | Nominal scope | `ara.rs` + `verify.rs` | Channel freshness violations (GT04) |
| 2 | Register allocation | `ara.rs` | Data ownership violations (GT03) |
| 3 | Petri net safety | `petri.rs` | Deadlocks (GT01), unbounded buffers |
| 4 | WPDS stack-aware refinement | `wpds.rs` + `verify.rs` | Context-sensitive reachability, stack depth (GT06) |
| 5 | Buchi liveness | `buchi.rs` + `ltl.rs` | Starvation (GT02) |
| 6 | KAT program equivalence | `kat.rs` | Optimization soundness |

## 7. Data Flow

```text
language! {
    channels { tokens: Channel<Token>; }        ← Layer 1 spec
    Expr { ... }                                ← Grammar rules
}
            │
            ▼ (macro expansion + codegen)
     ┌──────────────┐
     │ Verification  │ ← Layer 4: GT01-GT06 lints
     │ Pipeline      │
     └──────────────┘
            │
            ▼
     ┌──────────────┐     fork      ┌──────────────┐
     │ Root Thread   │────────────→│ Child Thread   │
     │ (parse Expr)  │  im clone   │ (channel recv) │
     └──────────────┘              └──────────────┘
            │                              │
            ▼                              ▼
     ┌──────────────┐              ┌──────────────┐
     │  Scheduler    │←────────────│  Channel msg  │
     │  (dispatch)   │  wake event │  (crossbeam)  │
     └──────────────┘              └──────────────┘
            │
            ▼
     ┌──────────────┐
     │  GlobalPool   │ ← Layer 3: adaptive scaling
     │  (singleton)  │
     └──────────────┘
```

## 8. Persistent Data Structures

The green thread runtime uses the `im` crate (persistent immutable collections based on Hash Array Mapped Tries and Relaxed Radix Balanced trees) for three critical fields:

| Field | `im` Type | Backing Structure | Complexity |
|-------|-----------|-------------------|------------|
| `environment` | `im::HashMap<K, V>` | HAMT (Hash Array Mapped Trie) | O(log₃₂ n) lookup/update |
| `continuation` | `im::Vector<T>` | RRB tree (Relaxed Radix Balanced) | O(log₃₂ n) push/pop |
| `eval_stack` | `im::Vector<T>` | RRB tree | O(log₃₂ n) push/pop |

### Why Persistent Data Structures?

1. **O(1) fork**: `im::HashMap::clone()` and `im::Vector::clone()` copy a single root pointer. The tree nodes are reference-counted and shared.

2. **Independent mutation after fork**: When a child thread modifies its environment, only the path from root to the changed node is copied (copy-on-write). The parent's tree is unaffected.

3. **Safe checkpointing**: Saving a snapshot of the CEK state is O(1) — just clone the persistent structures. This enables speculative execution and backtracking.

4. **No locking required**: Persistent data structures are inherently thread-safe because they are never mutated in place. Each thread has its own root pointer.

### RRB Tree Properties

The `im::Vector` uses Relaxed Radix Balanced trees (Stucki, Rompf & Ureche, 2015):

- Branching factor 32 (cache-line aligned).
- `push_back` / `pop_back`: amortized O(1), worst-case O(log₃₂ n).
- Concatenation: O(log₃₂ n) (exploiting relaxed radix for efficient rebalancing).
- Memory overhead: ~1.5x compared to `Vec<T>` due to tree nodes.

## 9. Global Pool Architecture

The `GlobalPool` is a process-wide singleton (`OnceLock<GlobalPool>`) that coordinates native worker threads across all `language!`-defined parsers:

```text
  ┌─────────────────────────────────────────────────────┐
  │                   GlobalPool (singleton)             │
  │                                                     │
  │  ┌──────────────┐  ┌──────────────┐  ┌──────────┐ │
  │  │ Language A    │  │ Language B    │  │ Lang C   │ │
  │  │ AnyScheduler  │  │ AnyScheduler  │  │ AnySched │ │
  │  └──────────────┘  └──────────────┘  └──────────┘ │
  │                                                     │
  │  ┌──────────────────────────────────────────────┐  │
  │  │          Shared Parallel Budget               │  │
  │  │          (AtomicU32, CAS-based)               │  │
  │  └──────────────────────────────────────────────┘  │
  │                                                     │
  │  ┌──────────────────────────────────────────────┐  │
  │  │          HillClimber (adaptive scaling)       │  │
  │  │          EMA throughput → worker count         │  │
  │  └──────────────────────────────────────────────┘  │
  └─────────────────────────────────────────────────────┘
```

### HillClimber Algorithm

The adaptive scaling uses hill climbing (same strategy as the .NET CLR ThreadPool):

1. Observe throughput (tasks/interval) → update exponential moving average (EMA).
2. Compare EMA with previous EMA.
3. If improved → continue in the same direction (grow or shrink).
4. If worsened → reverse direction.
5. Apply: `workers += direction * step_size`, clamped to `[min_workers, max_workers]`.

EMA is stored as fixed-point (`throughput * 1024`) to avoid floating-point atomics. Smoothing factor alpha = 1/4.

### Lock-Free Guarantees

| Component | Synchronization | Lock-Free? |
|-----------|----------------|------------|
| Singleton init | `OnceLock` (one-shot) | Yes |
| Scheduler registry | `DashMap` (sharded) | Yes* |
| Parallel budget | `AtomicU32` CAS | Yes |
| Active flag | `AtomicBool` | Yes |
| Hill climber state | `AtomicU32`/`AtomicU64` | Yes |
| Metrics | `AtomicU64` | Yes |

(*) DashMap uses per-shard locks but never blocks cross-shard operations.

## 10. MeTTaTron Comparison

| Feature | MeTTaTron | PraTTaIL |
|---------|-----------|----------|
| Scheduler pattern | `CronStateMachine` (reactive FSM) | `Scheduler` (same pattern, adapted) |
| Thread pool | `WorkPool` + `PriorityScheduler` | `GlobalPool` + `HillClimber` |
| Adaptive scaling | Hill climbing EMA | Hill climbing EMA (same algorithm) |
| Channel model | Rholang channels (Java) | `crossbeam_channel` (lock-free Rust) |
| Data structures | JVM heap (GC-managed) | `im` crate (persistent, ref-counted) |
| Fork cost | O(n) deep copy | O(1) structural sharing |
| Verification | Runtime checks | Compile-time 6-phase pipeline |
| Join patterns | `for(@x <- a; @y <- b)` | `JoinPatternSpec` + `WaitPattern::Join` |
| Budget control | JVM thread pool limits | `AtomicU32` CAS semaphore |
| Process model | Pi-calculus | Pi-calculus (same formalism) |

## 11. References

- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*. Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus. *Proceedings of POPL*, pp. 372-385.
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine, and the lambda-calculus. *Formal Description of Programming Concepts III*.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University Press.
- Stucki, N., Rompf, T. & Ureche, V. (2015). RRB vector: a practical general purpose immutable sequence. *Proceedings of ICFP*.
- Petri, C. A. (1962). *Kommunikation mit Automaten*. Ph.D. thesis, University of Bonn.
- Kozen, D. (1997). Kleene algebra with tests. *ACM TOPLAS*, 19(3):427-443.
- Reps, T., Lal, A. & Kidd, N. (2007). Program analysis using weighted pushdown systems. *FSTTCS*.
- Vardi, M. Y. & Wolper, P. (1994). Reasoning about infinite computations. *Information and Computation*, 115(1):1-37.
