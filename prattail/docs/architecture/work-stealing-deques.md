# Work-Stealing Deque Theory & Implementation

This document describes the work-stealing deque algorithm used by PraTTaIL's M:N green thread runtime, covering both the theoretical foundations and the concrete implementation in `worker_pool.rs`.

## 1. The Chase-Lev Algorithm

PraTTaIL's worker pool uses Chase-Lev work-stealing deques (Chase & Lev, SPAA 2005) via the `crossbeam::deque` crate. Each of the N native worker threads owns a local deque; a shared global `Injector` provides external work injection from the coordinator.

### Core Idea

A work-stealing deque is a double-ended queue with asymmetric access:

- **The owner** pushes and pops from the **bottom** (LIFO end).
- **Thieves** steal from the **top** (FIFO end).

This asymmetry is not arbitrary -- it serves two distinct scheduling goals simultaneously.

### Data Structure

```text
  top ──────────────▶ ┌──────┐
  (thieves steal       │ gt#0 │  oldest task (first in, first stolen)
   from here, FIFO)    ├──────┤
                       │ gt#1 │
                       ├──────┤
                       │ gt#2 │
                       ├──────┤
                       │ gt#3 │  newest task (last pushed, first popped)
  bottom ────────────▶ └──────┘
  (owner pushes/pops
   from here, LIFO)
```

The deque is backed by a growable circular buffer. `top` and `bottom` are atomic indices. The buffer grows (doubles capacity) when `bottom - top == capacity`.

## 2. LIFO Local / FIFO Steal Duality

### Why LIFO for the Owner?

When a green thread forks via `PPar(P, Q)`, both children are pushed to the owner's local deque. LIFO ordering means the **most recently created** child is executed first. This produces depth-first exploration of the fork tree.

Depth-first traversal has two advantages:

1. **Cache locality.** The most recently forked child shares the most state with the parent (the `im::HashMap` and `im::Vector` root pointers are identical until divergence). Executing it immediately maximizes the probability that shared HAMT nodes remain in L1/L2 cache.

2. **Space efficiency.** Depth-first exploration bounds the number of simultaneously live green threads. If the fork tree has depth D and branching factor B, depth-first uses O(D) live threads versus O(B^D) for breadth-first.

```text
  Fork tree for: (A | B) | (C | D)

  DFS (LIFO):  executes A, then B, then C, then D
               max 2 live threads at any point

  BFS (FIFO):  executes (A|B) and (C|D) concurrently,
               then all 4 leaves concurrently
               max 4 live threads
```

### Why FIFO for Thieves?

When a worker steals from a peer, it takes the **oldest** task (the one at the top of the deque). This produces breadth-first load distribution across workers.

The oldest task is typically the **largest** unit of work. In a divide-and-conquer fork tree, tasks near the root represent larger sub-problems than tasks near the leaves. Stealing the oldest task gives the thief the most work, amortizing the cost of the steal operation (which involves atomic synchronization).

```text
  Worker 0 deque (owner):            Worker 1 (thief):
  ┌──────┐ ← top                     steals gt#0 (root-level task,
  │ gt#0 │   (root fork)              carries the most sub-work)
  ├──────┤
  │ gt#3 │   (leaf of gt#0's fork)    Worker 0 keeps gt#3, gt#4
  ├──────┤                            (leaf tasks, cache-warm)
  │ gt#4 │   (another leaf)
  └──────┘ ← bottom
```

This duality -- **depth-first locally, breadth-first globally** -- is the key insight of Cilk-style work stealing and is why it achieves provably optimal expected completion time O(T₁/P + T_inf).

## 3. Pseudocode for Core Operations

### push (owner only)

```
procedure push(deque, item):
    b := load(deque.bottom)                      // relaxed
    t := load(deque.top)                         // acquire
    buf := deque.buffer
    if b - t >= buf.capacity:
        buf := grow(buf, b, t)                   // double capacity
        deque.buffer := buf
    buf[b % buf.capacity] := item
    fence(release)                               // ensure item is visible
    store(deque.bottom, b + 1)                   // relaxed
```

`push` is wait-free: the owner never contends with thieves because it writes to `bottom` (which only the owner modifies) and stores the item before advancing the index.

### pop (owner only)

```
procedure pop(deque) -> Option<item>:
    b := load(deque.bottom) - 1
    store(deque.bottom, b)                       // relaxed
    fence(seq_cst)                               // full barrier
    t := load(deque.top)                         // relaxed
    if t <= b:
        item := deque.buffer[b % capacity]
        if t == b:                               // last item -- race with steal
            if !CAS(deque.top, t, t + 1):        // try to claim it
                store(deque.bottom, b + 1)       // lost race, restore bottom
                return None
            store(deque.bottom, b + 1)           // won race
        return Some(item)
    else:
        store(deque.bottom, b + 1)               // deque was empty, restore
        return None
```

The `seq_cst` fence is the key synchronization point. It ensures that the owner's write to `bottom` is visible to thieves before the owner reads `top`. Without it, the owner and a thief could both claim the last item.

### steal (thief, any thread)

```
procedure steal(deque) -> Steal<item>:
    t := load(deque.top)                         // acquire
    fence(seq_cst)                               // ensure we see bottom updates
    b := load(deque.bottom)                      // acquire
    if t < b:
        item := deque.buffer[t % capacity]
        if CAS(deque.top, t, t + 1):             // try to claim
            return Success(item)
        else:
            return Retry                          // another thief got it
    else:
        return Empty
```

Steal returns a three-valued result: `Success(item)`, `Empty` (deque is empty), or `Retry` (CAS failed -- another thief claimed the item, try again). PraTTaIL's worker loop retries on `Retry` and moves on to the next source on `Empty`.

## 4. ABA Problem and Epoch-Based Reclamation

### The ABA Problem

The classical ABA problem occurs when a CAS succeeds because the target location has been modified from A to B and back to A, even though the state has changed. In work-stealing deques, this could occur if:

1. Thief reads `top = 5` and the item at index 5.
2. Owner pops items until `top` wraps around back to 5 (circular buffer).
3. Thief's CAS on `top` from 5 to 6 succeeds, but the item at index 5 is now a completely different task.

### How crossbeam::deque Handles It

The `crossbeam` crate uses **epoch-based reclamation** to solve this:

1. **Buffer growth is never in-place.** When the deque grows, a new buffer is allocated and old entries are copied. The old buffer is retired into an epoch-based garbage collector.
2. **Atomic pointers to buffers.** The `buffer` field is an `AtomicPtr`, so thieves always see a consistent buffer.
3. **Monotonic indices.** `top` and `bottom` are `u64` (or `usize`), never wrapping within the deque's lifetime. This eliminates the ABA problem on the indices themselves.
4. **Epoch guards.** Before reading the buffer, thieves enter an epoch. The old buffer is not freed until all thieves that might reference it have exited their epochs.

This means PraTTaIL does not need to implement its own memory reclamation for deque buffers -- `crossbeam` handles it.

## 5. Steal Policy: Random Victim Selection

When a worker's local deque is empty and the global injector has no work, the worker attempts to steal from a random peer.

### Why Random?

Round-robin steal visits peers in a fixed order, creating hotspots. If Workers 0, 1, and 2 are all idle, they would all try to steal from Worker 3 first, creating contention on Worker 3's deque. Random selection distributes steal attempts uniformly.

### Implementation

PraTTaIL uses a per-worker XorShift64 PRNG (seeded with the worker index + a constant) to select a random starting point, then scans all peers:

```
procedure find_work(local, injector, peer_stealers, rng):
    // 1. Local deque (LIFO, cache-warm)
    if item := local.pop():
        return item

    // 2. Global injector (FIFO, fairness)
    loop:
        match injector.steal():
            Success(item) -> return item
            Empty         -> break
            Retry         -> continue

    // 3. Random peer steal
    n := len(peer_stealers)
    start := xorshift64(rng) % n
    for i in 0..n:
        idx := (start + i) % n
        loop:
            match peer_stealers[idx].steal():
                Success(item) -> return item
                Empty         -> break
                Retry         -> continue

    return None
```

The full scan (all N-1 peers from a random start) ensures that if any peer has work, the idle worker will find it. The expected number of steal attempts before finding work is O(1) when work is uniformly distributed.

## 6. WorkerParker: Condvar-Based Parking

When all work sources are exhausted (local, injector, peers), a worker parks on a condvar to avoid busy-waiting.

### Lost-Notification Problem

A naive boolean flag suffers from lost notifications:

1. Coordinator sets `has_work = true` and calls `condvar.notify_one()`.
2. Worker checks `has_work`, sees `true`, consumes the notification.
3. Coordinator sets `has_work = true` again (another task injected).
4. Worker has already consumed the flag -- second notification is lost.

### Pending Counter Solution

PraTTaIL's `WorkerParker` uses a **pending count** instead of a boolean:

```
struct WorkerParker:
    pending: Mutex<u32>
    condvar: Condvar

procedure park(shutdown):
    lock pending
    while pending == 0 and not shutdown:
        condvar.wait(pending)
    if pending > 0:
        pending -= 1
    unlock pending

procedure unpark_one():
    lock pending
    pending = saturating_add(pending, 1)
    unlock pending
    condvar.notify_one()

procedure unpark_all():
    lock pending
    pending = u32::MAX
    unlock pending
    condvar.notify_all()
```

Each `unpark_one()` increments the pending counter. Each `park()` decrements it. Multiple notifications accumulate, so none are lost. `unpark_all()` is used for shutdown: setting pending to `u32::MAX` ensures all parked workers wake up.

## 7. Work Discovery Order

Each worker thread follows a strict priority order when searching for work:

```text
  ┌──────────────────────┐
  │ 1. Local deque pop   │  LIFO — cache-warm, depth-first
  │    (no contention)   │  O(1) amortized, wait-free
  └──────────┬───────────┘
             │ empty
             ▼
  ┌──────────────────────┐
  │ 2. Global injector   │  FIFO — fairness for coordinator
  │    steal()           │  O(1) per item, may retry on CAS
  └──────────┬───────────┘
             │ empty
             ▼
  ┌──────────────────────┐
  │ 3. Random peer steal │  FIFO from peer — load balancing
  │    (scan all N-1)    │  O(N) worst case, O(1) expected
  └──────────┬───────────┘
             │ all empty
             ▼
  ┌──────────────────────┐
  │ 4. Park on condvar   │  Sleep until woken by:
  │    (WorkerParker)    │  - unpark_one() (new work injected)
  └──────────────────────┘  - unpark_all() (shutdown signal)
```

This order minimizes synchronization overhead: the common case (local work available) is completely uncontended. Stealing only occurs when a worker has no local work, and parking only occurs when the entire system is temporarily idle.

## 8. Quantum-Based Cooperative Yielding

Green threads do not run to completion in a single stretch. Instead, each execution on a worker is bounded by a **quantum**: a configurable number of CEK steps (default: 100, overridable via `PRATTAIL_QUANTUM` environment variable).

```text
  Worker picks up gt#5:
    gt#5.state = Ready → Running
    result = gt#5.run_quantum(100)

  Possible outcomes:
  ┌──────────────────┐
  │ Completed        │ → report to coordinator, replenish budget
  ├──────────────────┤
  │ Yielded          │ → push gt#5 back to local deque (LIFO)
  ├──────────────────┤
  │ Suspended        │ → report to coordinator, register in WakeRegistry
  ├──────────────────┤
  │ Forked           │ → create children, push to local deque
  ├──────────────────┤
  │ Failed           │ → report to coordinator, replenish budget
  └──────────────────┘
```

The `Yielded` path re-enqueues the thread to the **local** deque (not the global injector). This preserves cache locality: the same worker continues the same thread unless a thief steals it.

## Fork and Structural Sharing

When a green thread forks (parallel composition `P | Q`), children share the parent's
state via O(1) `im` structural sharing:

- **Continuation stack** (`im::Vector<EvalFrame>`): O(1) clone, shared spine
- **Eval bindings** (`im::HashMap<String, String>`): O(1) clone
- **Memo cache** (`im::HashMap<String, String>`): O(1) clone — children benefit from
  parent's cached normal forms without copying

This means forked children automatically have access to all ground terms the parent
has already evaluated. The total memory savings are proportional to the cache hit rate.

## 9. References

- Chase, D. & Lev, Y. (2005). Dynamic circular work-stealing deque. *Proceedings of SPAA*, pp. 21-28.
- Blumofe, R. & Leiserson, C. (1999). Scheduling multithreaded computations by work stealing. *JACM*, 46(5):720-748.
- Michael, M. M. & Scott, M. L. (1996). Simple, fast, and practical non-blocking and blocking concurrent queue algorithms. *Proceedings of PODC*.
- Crossbeam documentation: <https://docs.rs/crossbeam-deque/>
