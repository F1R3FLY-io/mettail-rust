# Theoretical Foundations of M:N Scheduling

## 1. The M:N Threading Model

An **M:N threading model** multiplexes M green threads onto N native OS
threads. Each green thread is a lightweight, cooperatively scheduled unit of
work that executes on whichever native worker is available:

```
    M green threads (user-space)              N native workers (OS)
  ┌──────────────────────────────┐          ┌────────────────────┐
  │  gt#0   gt#1   gt#2  ...    │          │  Worker 0          │
  │  gt#3   gt#4   gt#5         │  ═══▶    │  Worker 1          │
  │  gt#6   gt#7   ...   gt#M-1 │          │  ...               │
  └──────────────────────────────┘          │  Worker N-1        │
                                           └────────────────────┘
```

**Formal definition.** Let G = {g_0, g_1, ..., g_{M-1}} be the set of green
threads and W = {w_0, w_1, ..., w_{N-1}} be the set of native workers. A
scheduling function sigma : G x T -> W assigns each active green thread to a
worker at each discrete time step t in T. The M:N constraint is M >> N: the
scheduler must time-share workers across a potentially much larger population
of green threads.

In PraTTaIL, green threads arise from Rholang's parallel composition
`P | Q`, where each sub-process becomes an independent green thread sharing
the parent's environment spine via `im` persistent data structures.

## 2. Work-Stealing: Expected Completion Time

PraTTaIL's M:N scheduler uses a **work-stealing** strategy. Each native
worker owns a local deque of ready green threads. When a worker's deque is
empty, it steals from another worker's deque.

### 2.1 Blumofe--Leiserson Theorem (1999)

For a computation with:

- T_1 = total work (serial execution time, summing all steps across all green threads)
- T_inf = critical path length (span -- the longest chain of dependent steps)
- P = number of native workers

the expected completion time under randomized work-stealing is:

```
    E[T_P] = O(T_1/P + T_inf)
```

**Intuition.** The first term T_1/P is the best possible parallel time --
perfectly dividing work across P workers. The second term T_inf is an
irreducible lower bound dictated by the serial dependencies in the
computation DAG. Work-stealing achieves both bounds simultaneously, up to
constant factors.

### 2.2 Derivation Sketch

Model the computation as a DAG where each node is one CEK step (one call to
`GreenThread::run_quantum()` processing a single frame). Edges represent
data dependencies (e.g., a channel receive depends on a channel send).

At each time step, a worker either:
1. **Executes** a ready node from its local deque (productive step), or
2. **Steals** from a random victim's deque (steal attempt).

Blumofe and Leiserson show that the total number of steal attempts across
all P workers over the entire computation is O(P * T_inf) in expectation.
Since each steal attempt costs O(1) (it is a deque pop from the opposite
end), the overhead is O(P * T_inf). Adding the O(T_1) productive steps and
dividing by P workers gives the bound.

### 2.3 Application to PraTTaIL

In PraTTaIL's Rholang evaluator:

- T_1 = sum of all CEK steps across all green threads (each `run_quantum()`
  call processes up to Q steps, where Q is the quantum size).
- T_inf = the longest dependency chain through channel communications (the
  critical path of send/receive synchronizations).
- P = number of native workers (configurable, default = `num_cpus`).

For purely parallel compositions `P_1 | P_2 | ... | P_k` with no channel
communication, T_inf = max_i(T_i) and the speedup approaches P.

## 3. Space Bounds: Cilk-Style Stack Scaling

### 3.1 The Cilk Space Bound

The classical Cilk space bound (Blumofe & Leiserson, 1999) states:

```
    S_P <= S_1 * P
```

where S_1 is the stack space used by a serial execution and S_P is the total
stack space used by a P-worker parallel execution. Each worker needs at most
S_1 space because work-stealing preserves the serial depth-first execution
order within each worker.

### 3.2 PraTTaIL's Improvement via Structural Sharing

PraTTaIL uses `im::Vector` for continuation stacks and `im::HashMap` for
environments. These persistent data structures provide structural sharing:
forking a green thread via `GreenThread::fork()` performs an O(1) clone that
shares the underlying tree spine.

```
    Parent:  [ Frame_A, Frame_B, Frame_C ]
                  │          │         │
    Child:   [ Frame_A, Frame_B, Frame_C, Frame_D ]
                  └─ shared ─┘         │
                                    new node
```

Because forked threads share ancestor frames, the actual space is:

```
    S_P <= S_1 + delta_1 + delta_2 + ... + delta_{M-1}
```

where delta_i is the **additional** stack space that green thread i allocates
beyond its parent's snapshot. For many Rholang patterns (e.g., `P | P | P`
where P is the same process), delta_i is near zero because the child's
stack is structurally identical to the parent's until divergence.

This gives a tighter bound than the classical Cilk result whenever threads
share significant common prefixes in their continuation stacks.

## 4. Progress Guarantee: Cooperative Scheduling + Quantum Budget

### 4.1 Quantum-Bounded Execution

Each green thread runs for at most Q steps before yielding, where Q is the
quantum size (default: 100, configurable via `PRATTAIL_QUANTUM`). The
`GreenThread::run_quantum(max_steps)` method enforces this:

```
    for step in 0..Q:
        if channel_waiters.is_empty() == false:
            return Suspended { waiting_on }
        if eval_stack.pop_back().is_some():
            continue
        if continuation.pop_back().is_some():
            continue
        return Completed { result }
    return Yielded      // quantum exhausted
```

**Bounded latency.** If there are M active green threads and P workers,
each thread is guaranteed to run within ceil(M / P) * Q steps of its
last execution. No thread can monopolize a worker for more than Q steps.

### 4.2 Fork Budget

The `parallel_budget` (an `AtomicU32` with CAS-based decrement) limits the
maximum number of concurrently runnable green threads. Each fork consumes
one budget unit; each thread completion replenishes one. This prevents
unbounded thread proliferation:

```
    Invariant: active_running <= parallel_budget_initial
```

Together, the quantum bound and fork budget guarantee:
- **Bounded latency**: Every ready thread executes within O(M/P * Q) time.
- **Bounded concurrency**: At most B threads are active simultaneously
  (where B is the initial budget, typically 2 * num_cpus).
- **No starvation**: The FIFO-within-priority scheduling ensures every
  ready thread eventually runs (see Section 5).

## 5. Starvation Freedom

### 5.1 Priority Queue with Age Tie-Breaking

The scheduler's ready queue is an `im::OrdMap<(u32, u64), GreenThreadId>`
where the key is `(priority, age)`:

- **priority**: Lower value = higher priority (0 is highest). Derived from
  probabilistic weights in the grammar analysis.
- **age**: Monotonic counter incremented on each enqueue. Within equal
  priorities, older threads (lower age) are dequeued first.

This provides **FIFO ordering within each priority level**, which is
necessary for starvation freedom.

### 5.2 Starvation Freedom Argument

**Claim.** Under the assumption that every running thread either completes,
suspends, or yields within Q steps, no ready thread waits indefinitely.

**Proof sketch.** Consider a thread g at priority level p. All threads at
priority levels < p are dequeued before g. But each such thread runs for
at most Q steps before yielding, at which point it is re-enqueued with a
new (higher) age. Since the age counter is monotonically increasing, g's
age is eventually the lowest among all priority-p threads, guaranteeing
that g is the next thread dequeued at priority level p.

For the finite case (bounded budget B, finite number of priority levels),
this gives an upper bound of O(B * Q) steps between successive executions
of any given thread at the highest-numbered (lowest-priority) level.

### 5.3 FIFO Stealing

When a worker steals from another worker's deque, it steals from the
**bottom** (oldest end) of the deque (`crossbeam-deque`'s `Stealer::steal()`
returns the oldest task). This preserves FIFO ordering across workers: the
oldest tasks in the system are the most likely to be executed next, even
if they were pushed to a different worker's deque.

## 6. Connection to PraTTaIL's Formal Analysis Framework

### 6.1 Petri Net Model (GT01)

The green thread lifecycle is modeled as a Petri net for deadlock analysis.
Places correspond to thread states (`Ready`, `Running`, `Suspended`,
`Completed`, `Failed`, `Forked`) and transitions correspond to scheduler
events:

```
    Ready ──[dispatch]──▶ Running
    Running ──[suspend]──▶ Suspended
    Running ──[complete]──▶ Completed
    Running ──[fork]──▶ Forked ──[spawn]──▶ Ready (children)
    Suspended ──[wake]──▶ Ready
```

Lint GT01 uses this Petri net to detect potential deadlocks: if a channel
send can only occur in a thread that is blocked waiting on a channel
receive, the system may deadlock. The analysis is conservative (over-
approximates possible interleavings).

### 6.2 Buchi Automata (GT02)

Lint GT02 constructs a Buchi automaton over the infinite sequence of
scheduler states. The acceptance condition checks liveness properties:

- **Every spawned thread eventually reaches a terminal state.** The
  Buchi automaton accepts runs where some thread is perpetually
  `Ready` or `Suspended` without ever completing, and the lint
  reports if such accepting runs exist.

- **No priority inversion.** A high-priority thread should not be
  indefinitely delayed by low-priority threads. The automaton
  encodes the priority ordering and checks for violations.

## 7. Multi-Tape Dispatch Automaton

The `SchedulerAutomaton` compiles join patterns into a bitmask-based
multi-tape automaton. Instead of polling K channels sequentially (O(K)
per dispatch cycle), all channel readiness is evaluated in a single
pass over a K-bit configuration word:

```
    channel_states:  0 b 1 1 0 1  (channels 0,2,3 are non-empty)
    pattern mask:    0 b 1 0 0 1  (pattern requires channels 0,3)
    bitwise AND:     0 b 1 0 0 1  (== mask => pattern fires)
```

This reduces dispatch complexity from O(K * J) to O(J), where J is
the number of join patterns, and enables single-instruction readiness
checks for up to 64 channels.

## Space Efficiency via Memo Cache Sharing

Forked children share the parent's `memo_cache` via `im::HashMap` structural sharing.
When a parent evaluates a ground term to normal form and caches it, ALL children
(and their descendants) can look up that result in O(log n) time without any copying.

This reduces total memory proportional to the cache hit rate. For Rholang's common
pattern of parallel composition of identical processes (`P | P | P`), the first
evaluation caches the result and all subsequent forks hit the cache.

## 8. References

- Blumofe, R. D. & Leiserson, C. E. (1999). Scheduling multithreaded
  computations by work stealing. *JACM*, 46(5), pp. 720--748.
- Chase, D. & Lev, Y. (2005). Dynamic circular work-stealing deque.
  *SPAA '05*, pp. 21--28.
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the
  SECD-machine, and the lambda-calculus. *Formal Description of
  Programming Concepts III*, pp. 193--219.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge
  University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the
  join-calculus. *POPL '96*, pp. 372--385.
- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*.
  Cambridge University Press.
