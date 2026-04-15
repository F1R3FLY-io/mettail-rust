# Green Thread Operational Semantics

This document formalizes the operational semantics of PraTTaIL's green thread
system. Green threads extend the single-threaded CEK machine (Felleisen &
Friedman, 1986) with concurrent process composition, channel communication, and
cooperative scheduling, following the pi-calculus (Milner, 1999) and
join-calculus (Fournet & Gonthier, 1996) models.

**Source files**: `prattail/src/green_thread.rs`, `prattail/src/channel.rs`,
`prattail/src/scheduler.rs`, `prattail/src/cek.rs`.

**Feature gate**: `green-threads` (transitively enables `cek-runtime`).

---

## 1. Process Configuration

### Definition 1 (Green Thread)

A **green thread** is a quadruple `⟨id, C, E, K⟩` where:

- `id ∈ GreenThreadId` is a unique identifier (monotonic `u64`).
- `C ∈ Control` is the control component (current term under evaluation).
- `E ∈ Env = String ⇀ (String ⇀ String)` is a persistent environment mapping
  category names to variable bindings, implemented as `im::HashMap<String, im::HashMap<String, String>>`.
- `K ∈ K = String*` is a persistent continuation stack, implemented as
  `im::Vector<String>`.

### Definition 2 (Channel)

A **channel** is a triple `(id, name, queue)` where:

- `id ∈ ChannelId` is a unique identifier (monotonic `u64`).
- `name ∈ String` is a human-readable name.
- `queue ∈ T*` is a lock-free MPMC FIFO queue (crossbeam-channel) holding
  messages of type `T`.

Each channel additionally maintains an atomic waiter count `w ∈ ℕ` tracking the
number of green threads currently blocked waiting for a message.

### Definition 3 (Process Configuration)

A **process configuration** is a triple `Σ = (Π, Γ, S)` where:

- `Π : GreenThreadId ⇀ GreenThread` is the **thread pool** (a lock-free
  `DashMap` mapping thread IDs to green thread structures).
- `Γ : ChannelId ⇀ Channel` is the **channel map** (a lock-free `DashMap`
  mapping channel IDs to type-erased channel handles), with an auxiliary reverse
  map `Γ_name : String ⇀ ChannelId`.
- `S = (state, rq, budget, metrics)` is the **scheduler** where:
  - `state ∈ SchedulerState = { CheckChannels, DispatchReady, Execute, ParkIdle, Shutdown }`
  - `rq ∈ im::OrdMap<(u32, u64), GreenThreadId>` is the priority-ordered ready queue (persistent balanced tree).
  - `budget ∈ AtomicU32` is the parallel fork budget.
  - `metrics ∈ SchedulerMetrics` is the atomic runtime statistics.

### Component Mapping Table

| Abstract Component | Implementation Type | Location | Lock-Free? |
|--------------------|--------------------|----------|------------|
| Thread pool `Π` | `DashMap<GreenThreadId, GreenThread>` | `green_thread.rs` (`GreenThreadRegistry`) | Yes (sharded) |
| Channel map `Γ` | `DashMap<ChannelId, ChannelHandle>` | `channel.rs` (`ChannelMap`) | Yes (sharded) |
| Name map `Γ_name` | `DashMap<String, ChannelId>` | `channel.rs` (`ChannelMap`) | Yes (sharded) |
| Thread environment `E` | `im::HashMap<String, im::HashMap<String, String>>` | `green_thread.rs` (`GreenThread`) | N/A (persistent) |
| Continuation stack `K` | `im::Vector<String>` | `green_thread.rs` (`GreenThread`) | N/A (persistent) |
| Ready queue `rq` | `im::OrdMap<(u32, u64), GreenThreadId>` | `scheduler.rs` (`Scheduler`) | N/A (persistent) |
| Fork budget | `AtomicU32` | `scheduler.rs` (`Scheduler`) | Yes (CAS) |
| ID generation | `AtomicU64` | `green_thread.rs`, `channel.rs` | Yes (fetch_add) |

---

## 2. Operational Semantics

### 2.1 Thread States

Each green thread `t ∈ Π` has a state drawn from the set:

```
CekThreadState = Ready
               | Running
               | Suspended(W)     where W ⊆ ChannelId
               | Completed(v)     where v ∈ String
               | Failed(e)        where e ∈ String
               | Forked(C)        where C ⊆ GreenThreadId
```

The valid state transition diagram is:

```
  Ready ──────→ Running ──────→ Completed
    ↑               │
    │               ├──→ Suspended ──→ Ready (resume on channel message)
    │               │
    │               ├──→ Failed
    │               │
    │               └──→ Forked
    │
    └───────────── (initial from spawn)
```

### 2.2 Thread-Local Transitions

Within a single green thread, the standard 10 CEK transition rules apply
unchanged from the single-threaded parser. These rules operate on the triple
`⟨C, E, K⟩` of the executing thread:

| # | Rule | From | To | Stack Op |
|---|------|------|----|----------|
| 1 | DRIVE | `Drive(cat, bp)` | `Prefix(cat, tok, bp)` | -- |
| 2 | PREFIX-TERMINAL (NT) | `Prefix(cat, tok, bp)` | `Drive(cat, bp')` | push Frame |
| 3 | PREFIX-TERMINAL (leaf) | `Prefix(cat, tok, bp)` | `Infix(cat, v, bp)` | -- |
| 4 | PREFIX-TAIL (BP02) | `Prefix(cat, tok, bp)` | `Drive(cat, R.bp)` | set tail_wrap |
| 5 | INFIX | `Infix(cat, lhs, bp)` | `Drive(cat, r_bp)` | push InfixRHS |
| 6 | POSTFIX | `Infix(cat, lhs, bp)` | `Infix(cat, f(lhs), bp)` | -- |
| 7 | UNWIND-INFIX | `Unwind(cat, rhs)` | `Infix(cat, f(lhs,rhs), bp)` | pop InfixRHS |
| 8 | UNWIND-PREFIX | `Unwind(cat, v)` | `Infix(cat, wrap(v), bp)` | pop UnaryPrefix |
| 9 | UNWIND-RD | `Unwind(cat, nt)` | `Drive/Infix` | pop RD |
| 10 | UNWIND-EMPTY | `Unwind(cat, v)` | `Accept(v)` | stack empty |

See `prattail/docs/theory/cek-transition-semantics.md` and
`prattail/docs/architecture/cek-machine.md` for full definitions.

### 2.3 Concurrency Transition Rules

The following 4 rules extend the CEK machine with process-algebraic primitives.
Each rule operates on the global configuration `Σ = (Π, Γ, S)`.

#### Rule 11: FORK

```
                   ⟨PPar(P, Q), E, K⟩ ∈ Π[tid]
────────────────────────────────────────────────────────────────────────────
  Π' = Π[tid ↦ Forked({id_P, id_Q})]
        ∪ {id_P ↦ ⟨id_P, P, E, []⟩}
        ∪ {id_Q ↦ ⟨id_Q, Q, E, []⟩}
  S'.rq = S.rq ∪ {(pri, age_P) ↦ id_P, (pri, age_Q) ↦ id_Q}
  Σ' = (Π', Γ, S')
```

**Precondition**: `tid` is in `Running` state; `S.budget > 0`.

**Effect**: The parent thread `tid` transitions to `Forked({id_P, id_Q})`. Two
fresh child threads `id_P` and `id_Q` are spawned with O(1) structural-sharing
clones of the parent's environment `E` (via `im::HashMap::clone`) and fresh
empty continuation stacks. Both children are enqueued in `S.rq` with the
parent's priority. The fork budget is decremented by 1.

**Implementation**: `GreenThread::fork()` in `green_thread.rs` performs the O(1)
clone. `GreenThreadRegistry::spawn_child()` allocates the ID via `AtomicU64::fetch_add`
and sets `parent = Some(tid)`. `Scheduler::try_fork()` checks and decrements the
budget via CAS.

#### Rule 12: SEND

```
                ⟨Send(x, v), E, K⟩ ∈ Π[tid]        Γ[E(x)] = ch
────────────────────────────────────────────────────────────────────────────
  ch.queue' = ch.queue · [v]
  Π' = Π[tid ↦ ⟨tid, (), E, K⟩]
  Σ' = (Π', Γ', S)
```

**Precondition**: `tid` is in `Running` state; `E(x)` resolves to a valid
`ChannelId`; channel `ch` exists in `Γ`.

**Effect**: Message `v` is enqueued at the tail of `ch.queue` (lock-free via
crossbeam-channel `Sender::send`). The thread continues with the unit value
`()` as the result. If `ch.waiter_count > 0`, the scheduler is notified via
`SchedulerEvent::ChannelMessage { channel_id }` to wake suspended threads.

**Implementation**: `Channel::send()` in `channel.rs`. For bounded channels,
if the buffer is full, the green thread yields (transitions to `Suspended`)
rather than blocking the OS thread.

#### Rule 13: RECEIVE

```
          ⟨Recv(x, body), E, K⟩ ∈ Π[tid]        Γ[E(x)] = ch
────────────────────────────────────────────────────────────────────────────
  Case ch.queue ≠ []:
    v = head(ch.queue)
    ch.queue' = tail(ch.queue)
    E' = E[x ↦ v]
    Π' = Π[tid ↦ ⟨tid, body, E', K⟩]
    Σ' = (Π', Γ', S)

  Case ch.queue = []:
    ch.waiter_count' = ch.waiter_count + 1
    Π' = Π[tid ↦ Suspended({E(x)})]
    Σ' = (Π', Γ', S)
```

**Precondition**: `tid` is in `Running` state; `E(x)` resolves to a valid
`ChannelId`; channel `ch` exists in `Γ`.

**Effect**: If the channel has a pending message, it is dequeued and bound
to `x` in the environment. The thread continues evaluating `body`. If the
channel is empty, the thread suspends, registering as a waiter. When a
message subsequently arrives (via SEND), the scheduler wakes the thread
by transitioning it from `Suspended` to `Ready`.

**Implementation**: `Channel::try_recv()` for non-blocking attempt.
`GreenThread::suspend()` transitions state and records `channel_waiters`.
`Channel::register_waiter()` / `unregister_waiter()` use `AtomicU64` with
saturating arithmetic. `GreenThread::resume()` clears waiters and resets
state to `Ready`.

**Join pattern variant**: For `for (@x <- a; @y <- b) { body }`, the thread
suspends on the set `{a, b}` and is only woken when ALL channels have messages.
The `WaitPattern::Join(additional_channels)` variant in `channel.rs` records the
multi-channel dependency. The `ChannelWaiter::all_channels()` method returns the
complete set.

#### Rule 14: NEW

```
              ⟨New(x, body), E, K⟩ ∈ Π[tid]
────────────────────────────────────────────────────────────────────────────
  id_ch = Γ.fresh_id()
  ch = Channel::new(id_ch, x, capacity)
  Γ' = Γ ∪ {id_ch ↦ ch}
  E' = E[x ↦ id_ch]
  Π' = Π[tid ↦ ⟨tid, body, E', K⟩]
  Σ' = (Π', Γ', S)
```

**Precondition**: `tid` is in `Running` state.

**Effect**: A fresh channel is created with a unique ID (via
`AtomicU64::fetch_add`), registered in both `Γ.channels` and `Γ.name_to_id`,
and bound to `x` in the thread's environment. The thread continues evaluating
`body` with the extended environment.

**Implementation**: `ChannelMap::create_channel()` in `channel.rs`. The
channel's capacity comes from the grammar's `channels {}` block specification
(`ChannelSpec`). Default is `ChannelCapacity::Unbounded`.

### 2.4 Scheduler Transitions

The scheduler `S` is a finite-state machine with transition function
`δ : SchedulerState × SchedulerEvent → SchedulerState × Vec<SchedulerAction>`.

#### Rule S1: SELECT

```
          S.state = DispatchReady        S.rq ≠ ∅        S.budget > 0
────────────────────────────────────────────────────────────────────────────
  (pri, age, tid) = min(S.rq)
  S.rq' = S.rq \ {(pri, age) ↦ tid}
  S.budget' = S.budget - 1
  Π' = Π[tid.state ← Running]
  S.state' = Execute
  actions = [WakeThread(tid)]
```

**Effect**: The highest-priority, oldest ready thread is dequeued and
transitioned to `Running`. The budget is decremented. Multiple threads may be
dispatched in a single SELECT if budget permits (the implementation loops until
budget or queue is exhausted).

**Implementation**: `Scheduler::dequeue()` removes the minimum key from
`im::OrdMap`, which orders by `(priority ASC, age ASC)`.
`Scheduler::check_budget()` uses `AtomicU32::fetch_update` with CAS for
lock-free budget consumption.

#### Rule S2: PARK

```
       S.state = CheckChannels       S.rq = ∅       no pending messages
────────────────────────────────────────────────────────────────────────────
  S.state' = ParkIdle
  actions = [ParkWorkers]
```

**Effect**: All native worker threads yield their time slice. The scheduler
remains in `ParkIdle` until an external event arrives.

#### Rule S3: WAKE

```
  S.state ∈ {ParkIdle, CheckChannels}        event = ChannelMessage(ch)
────────────────────────────────────────────────────────────────────────────
  For each tid ∈ Π where tid.state = Suspended(W) ∧ ch ∈ W:
    If W = {ch} (single):
      Π' = Π[tid.state ← Ready]
      S.rq' = S.rq ∪ {(tid.priority, age) ↦ tid}
    If W = W' ∪ {ch} (join) ∧ ∀ch' ∈ W'. Γ[ch'].queue ≠ []:
      Π' = Π[tid.state ← Ready]
      S.rq' = S.rq ∪ {(tid.priority, age) ↦ tid}
  S.state' = DispatchReady
```

**Effect**: All threads waiting on the channel with a newly arrived message are
considered for waking. Single-receive threads wake immediately. Join-pattern
threads wake only when all channels in their wait set have messages. Woken
threads are enqueued into the ready queue.

---

## 3. Correspondence Theorems

### Theorem 1 (Thread-Local CEK Bisimulation)

Let `⟨C, E, K⟩` be a single-threaded CEK configuration and let `⟨id, C, E', K'⟩`
be a green thread where `E' = lift(E)` maps the flat `CekEnvironment` to a
persistent `im::HashMap`, and `K' = lift(K)` maps `Vec<Frame_Cat>` to
`im::Vector<String>` (frame tags only).

For every thread-local transition `⟨C, E, K⟩ →_CEK ⟨C', E'', K''⟩` in the
single-threaded machine (Rules 1--10), there exists a corresponding transition
`⟨id, C, E', K'⟩ →_GT ⟨id, C', lift(E''), lift(K'')⟩` in the green thread
machine, and vice versa.

**Proof.** The thread-local rules (1--10) operate exclusively on the `⟨C, E, K⟩`
components of a green thread, which are structurally identical to the
single-threaded CEK components modulo the change from `Vec<Frame_Cat>` to
`im::Vector<String>`. The `im::Vector` supports the same `push_back` and
`pop_back` operations with identical sequential semantics. The `im::HashMap`
supports the same `get` and `update` operations. Since Rules 1--10 do not
interact with `Π`, `Γ`, or `S`, and since `im` operations preserve the same
sequential behavior as `Vec`/`HashMap` operations (the `im` crate documentation
guarantees observational equivalence for single-writer usage), the bisimulation
holds by structural induction on the transition rules. ∎

### Theorem 2 (Channel Correctness)

For every sequence of SEND and RECEIVE operations on a channel `ch` in a
well-formed configuration:

1. **FIFO ordering**: If `send(v₁)` happens-before `send(v₂)`, then
   `recv() = v₁` happens-before `recv() = v₂` (assuming a single receiver).
2. **No message loss**: Every sent message is either received exactly once or
   remains in the queue at termination.
3. **No duplication**: Each message is received at most once.

**Proof.** Properties (1)--(3) follow directly from the crossbeam-channel
guarantees. The `crossbeam_channel::unbounded()` and `crossbeam_channel::bounded(n)`
constructors produce MPMC queues with linearizable FIFO semantics (Kogan &
Petrank, 2011). The `Sender::send()` and `Receiver::recv()` / `try_recv()`
operations are linearizable. Since each channel's queue is the sole mediator
between SEND and RECEIVE operations (no aliases, no shared mutable state
outside the crossbeam internals), the properties are inherited. ∎

### Theorem 3 (Deadlock Freedom under Fairness)

If the scheduler is **fair** (every thread that becomes `Ready` is eventually
selected for execution) and the grammar's process structure is **acyclic**
(no circular channel dependency where thread `A` waits on a channel that only
thread `B` can write to, while `B` waits on a channel that only `A` can write
to), then no reachable configuration has all non-terminal threads in `Suspended`
state.

**Proof sketch.** Assume for contradiction that all active threads are
suspended. Each suspended thread waits on some channel set `W_i`. Since the
dependency graph is acyclic, there exists a thread `t` waiting on a channel `ch`
whose writer `t'` is not suspended on any channel reachable from `t` in the
dependency graph. But `t'` must be in some state: if `Ready`, the fairness
assumption ensures it will eventually run and SEND on `ch`, contradicting the
assumption. If `Running`, it will eventually either SEND (waking `t`), complete,
or fail. If `Completed` or `Failed` without sending, then `t`'s channel has no
remaining writers, which is detected as a disconnection (crossbeam returns
`RecvError`), transitioning `t` to `Failed` rather than remaining `Suspended`.
This contradicts the assumption that all non-terminal threads are suspended. ∎

---

## 4. Petri Net Abstraction

### Definition 4 (Process Petri Net)

The **process Petri net** `N = (P, T, F, M₀)` over a process configuration is:

- **Places** `P = P_thread ∪ P_channel` where:
  - `P_thread = {p_tid | tid ∈ dom(Π)}` -- one place per green thread.
  - `P_channel = {p_ch | ch ∈ dom(Γ)}` -- one place per channel.
- **Transitions** `T = {fork, send, recv, new, complete}` -- one per semantic rule.
- **Flow** `F` defined by the arcs:
  - `fork`: consumes 1 token from `p_parent`, produces 1 token each in `p_child₁` and `p_child₂`.
  - `send`: consumes 1 token from `p_sender`, produces 1 token in `p_ch` and 1 in `p_sender`.
  - `recv`: consumes 1 token from `p_receiver` and 1 from `p_ch`, produces 1 token in `p_receiver`.
  - `new`: consumes 1 token from `p_tid`, produces 1 token in `p_tid` and 1 in `p_ch_new`.
  - `complete`: consumes 1 token from `p_tid`.
- **Initial marking** `M₀(p_root) = 1`, `M₀(p) = 0` for all other places.

### Definition 5 (Abstraction Function α)

```
α : Σ → Marking
α(Π, Γ, S) = M  where
  M(p_tid) = 1   if Π[tid].state ∈ {Ready, Running}
  M(p_tid) = 0   if Π[tid].state ∈ {Suspended, Completed, Failed, Forked}
  M(p_ch)  = |Γ[ch].queue|
```

### Theorem 4 (Petri Net Simulation)

For every concrete transition `Σ →_GT Σ'` in the green thread operational
semantics, there exists a Petri net transition `t ∈ T` such that
`α(Σ) [t⟩ α(Σ')`.

**Proof.** Case analysis on the 4 concurrency rules:

- **FORK** (Rule 11): `p_parent` loses 1 token (parent → Forked), `p_child₁`
  and `p_child₂` gain 1 token each. Matches the `fork` Petri net transition.
- **SEND** (Rule 12): `p_ch` gains 1 token (message enqueued), `p_sender`
  is preserved (thread continues). Matches `send`.
- **RECEIVE** (Rule 13, non-empty case): `p_ch` loses 1 token (message dequeued),
  `p_receiver` is preserved. Matches `recv`.
- **RECEIVE** (Rule 13, empty case): `p_receiver` loses 1 token (thread → Suspended).
  The subsequent WAKE (Rule S3) restores it when `p_ch` gains a token from a future SEND.
- **NEW** (Rule 14): `p_ch_new` gains 1 (marking initialized to 0, representing
  an empty new channel). `p_tid` is preserved. Matches `new`. ∎

---

## 5. WPDS Extension

The existing WPDS infrastructure (`prattail/src/wpds.rs`) models the
single-threaded parser as a pushdown system with one control location. Green
threads extend this to an **interleaved stack model** where multiple stacks
execute concurrently.

### Definition 6 (Interleaved WPDS)

An **interleaved WPDS** `W_I = (P, Γ_w, Δ, R_fork, R_sync)` where:

- `P = {p₀}` is the single control location (inherited from the parser WPDS).
- `Γ_w` is the set of stack symbols (rule positions, as in the single-threaded WPDS).
- `Δ` is the set of push/pop/internal WPDS rules (inherited).
- `R_fork = { ⟨p₀, γ⟩ →_fork ⟨p₀, γ₁⟩ ⊗ ⟨p₀, γ₂⟩ }` are fork rules that
  split one stack configuration into two independent stacks.
- `R_sync = { ⟨p₀, γ_send⟩ ⊗ ⟨p₀, γ_recv⟩ →_sync ⟨p₀, γ'_send⟩ ⊗ ⟨p₀, γ'_recv⟩ }`
  are synchronization rules modeling channel send/receive.

### Theorem 5 (Interleaved Reachability Reduction)

The reachability problem for the interleaved WPDS with k stacks is decidable
for bounded context switching (Qadeer & Rehof, 2005). For a context bound `c`,
the poststar computation on the product automaton has complexity
`O(|Γ_w|^(c+1) × |Δ|)`.

**Proof.** By reduction to the bounded context-switching reachability result of
Qadeer & Rehof (2005, Theorem 3.1). Each green thread corresponds to one stack
in the interleaved model. The scheduler's cooperative switching ensures that
context switches occur only at yield points (SEND, RECEIVE, FORK), giving a
natural bound on the context-switching depth per scheduling round. ∎

---

## 6. References

- Felleisen, M. & Friedman, D. P. (1986). *Control operators, the SECD-machine,
  and the lambda-calculus.* Formal Description of Programming Concepts III, pp. 193--219.
- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus.*
  Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus.
  *Proceedings of POPL*, pp. 372--385.
- Reppy, J. H. (1999). *Concurrent Programming in ML.* Cambridge University Press.
- Reynolds, J. C. (1972). Definitional interpreters for higher-order programming
  languages. *ACM Annual Conference*, pp. 717--740.
- Kogan, A. & Petrank, E. (2011). Wait-free queues with multiple enqueuers and
  dequeuers. *PPoPP*, pp. 223--234.
- Qadeer, S. & Rehof, J. (2005). Context-bounded model checking of concurrent
  software. *TACAS*, pp. 93--107.
- Reps, T., Lal, A. & Kidd, N. (2007). Program analysis using weighted pushdown
  systems. *FSTTCS*, pp. 23--51.
- Karp, R. M. & Miller, R. E. (1969). Parallel program schemata. *JCSS*,
  3(2), pp. 147--195.
- Esparza, J., Hansel, D., Rossmanith, P. & Schwoon, S. (2000). Efficient
  algorithms for model checking pushdown systems. *CAV*, pp. 232--247.
