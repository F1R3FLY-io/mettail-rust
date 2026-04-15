# Channel - Worker - Coordinator Wake-Up Protocol

When a green thread attempts to receive from an empty channel, it must suspend and later resume when a message arrives. This document describes the full wake-up protocol that coordinates the three actors: the channel infrastructure, the worker threads, and the coordinator.

## 1. WakeRegistry

The `WakeRegistry` (defined in `prattail/src/channel.rs`) is a concurrent map from channel IDs to lists of waiting green thread IDs:

```text
  WakeRegistry
  ┌──────────────────────────────────────────────────────────┐
  │  DashMap<ChannelId, Vec<GreenThreadId>>                   │
  │                                                          │
  │  ch#0 ──→ [gt#3, gt#7]          ← two threads waiting   │
  │  ch#2 ──→ [gt#5]                ← one thread waiting    │
  │  ch#4 ──→ [gt#1, gt#2, gt#8]   ← three threads waiting │
  └──────────────────────────────────────────────────────────┘
```

### Operations

| Method | Description | Complexity |
|--------|-------------|------------|
| `register(ch_id, tid)` | Add `tid` to `ch_id`'s waiter list | O(1) amortized |
| `unregister(ch_id, tid)` | Remove first occurrence of `tid` from `ch_id`'s waiter list | O(n) waiter scan |
| `take_waiters(ch_id)` | Remove and return all waiters for `ch_id` | O(1) DashMap remove |
| `channels_with_waiters()` | List all channel IDs that have at least one waiter | O(k) where k = channels with waiters |
| `check_and_wake(channel_map)` | Poll all channels, return threads to wake | O(k) channels checked |

The `WakeRegistry` is owned by the coordinator thread and is not shared with workers. Workers report suspensions via the MPSC channel; the coordinator registers and resolves waiters.

## 2. Wake-Up Path: Simple Send/Recv

The following sequence describes the full path from a green thread suspending on `recv` to being resumed after a `send`.

```text
  Phase 1: Suspension
  ────────────────────────────────────────────────────────────

  Worker 1 executing gt#5:
    gt#5.run_quantum(100)
      → gt#5 calls ch#2.try_recv()
      → TryRecvError::Empty
      → gt#5.channel_waiters = [ch#2]
      → gt#5.run_quantum returns Suspended { waiting_on: [ch#2] }
      → gt#5.state = Suspended { waiting_on: [ch#2] }

  Worker FSM:
    (Executing{gt#5}, QuantumComplete(Suspended{[ch#2]}))
    → (Idle, [ReportToCoordinator(ThreadSuspended{gt#5, [ch#2]})])

  Worker 1 sends WorkerReport::ThreadSuspended to MPSC channel.


  Phase 2: Registration
  ────────────────────────────────────────────────────────────

  Coordinator receives ThreadSuspended{gt#5, [ch#2]}:
    handle_worker_report():
      for each channel_id in waiting_on:
        wake_registry.register(ch#2, gt#5)

  WakeRegistry state:
    ch#2 → [gt#5]


  Phase 3: Message Arrival (on another worker)
  ────────────────────────────────────────────────────────────

  Worker 0 executing gt#3:
    gt#3 calls ch#2.send("hello")
    → crossbeam_channel enqueues "hello" in ch#2's buffer
    → gt#3 continues executing (send is non-blocking for unbounded)


  Phase 4: Periodic Wake Check
  ────────────────────────────────────────────────────────────

  Coordinator (every wake_check_interval_ms = 50ms):
    let to_wake = wake_registry.check_and_wake(&channels)

    check_and_wake():
      for each ch_id in channels_with_waiters():  → [ch#2]
        if channel_map.get_channel(ch#2).has_pending():  → true!
          waiters = take_waiters(ch#2)  → [gt#5]
          to_wake.push((gt#5, ch#2))

  Coordinator processes to_wake:
    for (thread_id, _channel_id) in to_wake:
      registry.get_mut(gt#5).resume()
        → gt#5.channel_waiters.clear()
        → gt#5.state = Ready
      scheduler.enqueue(gt#5, priority)
      dispatch_ready_threads(scheduler, worker_pool)
        → worker_pool.inject(gt#5)
        → worker_pool.unpark_one()


  Phase 5: Resumption
  ────────────────────────────────────────────────────────────

  Worker 1 (or any worker) wakes from park:
    try_find_work():
      injector.steal() → Success(gt#5)

  Worker executes gt#5:
    gt#5.state = Ready → Running
    gt#5.run_quantum(100)
      → gt#5 calls ch#2.try_recv()
      → Ok("hello")  ← message received!
      → gt#5 continues evaluating with received value
```

## 3. ChannelHandle::has_pending() -- Type-Erased Check

The `ChannelMap` stores channels as type-erased `ChannelHandle` values (`Arc<dyn Any + Send + Sync>`). The coordinator cannot downcast to `Channel<T>` without knowing `T`. To check for pending messages without the concrete type, each `ChannelHandle` captures a closure at construction time:

```text
  ChannelHandle::new<T: Send + 'static>(channel: Channel<T>):
    let recv_clone = channel.receiver()     ← clone the crossbeam Receiver
    let pending_check = move || !recv_clone.is_empty()
                                              ↑
                                      captured at construction time;
                                      shares the same internal buffer
                                      as the original channel

  has_pending() → (self.pending_check)()    ← calls the closure
                                              returns true if buffer non-empty
```

This design avoids the need for a trait object with a `has_pending` method on `Channel<T>`, which would require `T: Send + 'static` bounds on the trait and complicate the DashMap value type. Instead, the closure captures the `Receiver<T>` (which is `Clone` and shares the underlying buffer) and performs the check via `Receiver::is_empty()`.

### Correctness

The cloned `Receiver` shares the same internal ring buffer as the `Channel<T>`'s receiver. When a `send()` enqueues a message via the `Sender`, the `is_empty()` check on any `Receiver` clone immediately reflects the new state (crossbeam's internal atomic counters are updated by the sender). There is no stale-read window beyond a single atomic load.

## 4. Join Pattern Wake-Up

For join patterns (`for(@x <- a; @y <- b) { P }`), a green thread suspends on **multiple** channels simultaneously. The thread must be woken only when **all** required channels have messages.

### SchedulerAutomaton Dispatch

The `SchedulerAutomaton` (defined in `prattail/src/scheduler.rs`) compiles join patterns into bitmasks at construction time:

```text
  channels:  [ch_a, ch_b, ch_c]
  pattern:   join_ab = { ch_a, ch_b }
  bitmask:   0b011  (bits 0 and 1 set)

  dispatch(channel_states):
    for each pattern:
      if (channel_states & pattern.required_channels) == pattern.required_channels:
        → pattern fires!
```

### Join Pattern Wake Sequence

```text
  gt#7 suspended on join { ch_a, ch_b }:

  WakeRegistry:
    ch_a → [gt#7]
    ch_b → [gt#7]     ← registered on both channels

  Coordinator check_and_wake():
    ch_a.has_pending() → true
    ch_b.has_pending() → false
    → gt#7 NOT woken (join requires all channels)

    [next interval]
    ch_a.has_pending() → true
    ch_b.has_pending() → true
    → Construct bitmask: 0b11
    → automaton.dispatch(0b11) → join_ab fires
    → take_waiters(ch_a) → [gt#7]
    → take_waiters(ch_b) → [gt#7]
    → deduplicate → [gt#7]
    → resume gt#7
```

The current implementation uses polling-based join checking: the coordinator iterates over channels with waiters, checks each for pending messages, and only wakes threads whose full join set is satisfied. The `SchedulerAutomaton::dispatch(bitmask)` function evaluates all join patterns in a single O(P) pass where P is the number of compiled patterns.

### Bitmask Encoding

Each channel is assigned an index (0-63) based on declaration order. A join pattern's `required_channels` field is a `u64` bitmask with bit `i` set if channel `i` must be non-empty. The dispatch function checks `(channel_states & required) == required` -- a single bitwise AND and comparison per pattern.

This limits the system to 64 channels per grammar. For grammars exceeding 64 channels, the bitmask would need to be widened to `u128` or a `BitVec`. In practice, 64 channels is sufficient for all current use cases.

## 5. Data Flow Summary

```text
  ┌─────────────────────────────────────────────────────────────────────┐
  │                     COORDINATOR THREAD                               │
  │                                                                     │
  │  ┌─────────────┐    ┌──────────────┐    ┌─────────────────────┐   │
  │  │ MPSC recv   │───▶│ Scheduler    │───▶│ execute_scheduler_  │   │
  │  │ (worker     │    │ FSM          │    │ actions()           │   │
  │  │  reports)   │    │ process_     │    │                     │   │
  │  │             │    │ event()      │    │ → inject(tid)       │   │
  │  └─────────────┘    └──────────────┘    │ → unpark_one()      │   │
  │        ↑                                 └─────────────────────┘   │
  │        │                                                           │
  │        │            ┌──────────────┐    ┌─────────────────────┐   │
  │        │            │ WakeRegistry │───▶│ check_and_wake()    │   │
  │        │            │ (DashMap)    │    │ periodic, 50ms      │   │
  │        │            └──────────────┘    │                     │   │
  │        │                                │ → resume(tid)       │   │
  │        │                                │ → enqueue(tid)      │   │
  │        │                                │ → inject(tid)       │   │
  │        │                                │ → unpark_one()      │   │
  │        │                                └─────────────────────┘   │
  └────────│────────────────────────────────────────────────────────────┘
           │
     MPSC channel
     (crossbeam)
           │
  ┌────────│────────────────────────────────────────────────────────────┐
  │        │                WORKER THREADS                               │
  │        │                                                            │
  │  ┌─────┴───────┐    ┌──────────────┐    ┌──────────────────────┐  │
  │  │ report_tx   │◀───│ Worker FSM   │◀───│ GreenThread::        │  │
  │  │ .send()     │    │ process_     │    │ run_quantum()        │  │
  │  │             │    │ event()      │    │                      │  │
  │  │ThreadCompl. │    │              │    │ try_recv() → Empty   │  │
  │  │ThreadSusp.  │    │              │    │ → Suspended          │  │
  │  │ForkReq.     │    │              │    │                      │  │
  │  │ThreadFailed │    │              │    │ try_recv() → Ok(v)   │  │
  │  │             │    │              │    │ → continues          │  │
  │  └─────────────┘    └──────────────┘    └──────────────────────┘  │
  └─────────────────────────────────────────────────────────────────────┘
```

## 6. Event-Driven Wake (Implemented in GS-5)

The wake path is now **event-driven** (with polling as fallback). When a green thread
performs a channel send during quantum execution:

1. When `Channel<T>::send()` succeeds, the worker checks `waiter_count > 0`.
2. If there are waiters, the worker sends `WorkerReport::ChannelActivity { channel_ids }` to the coordinator's MPSC channel.
3. The coordinator processes it immediately (no polling delay), checking `WakeRegistry` for affected channels.

This reduces wake-up latency from O(poll_interval) to O(MPSC_delivery_time), approximately microseconds. The tradeoff is additional overhead on every `send()` call (an atomic load + conditional MPSC send), which is acceptable because the event-driven path avoids unnecessary polling cycles.

The poll interval has been increased from 50ms to 500ms since the event-driven path handles the common case. Polling remains as a fallback for edge cases (e.g., external channel messages not originating from a green thread quantum).

## Event-Driven Wake Path (GS-5)

In addition to the polling-based approach, channel sends can trigger immediate wake-ups:

1. Green thread performs channel send during quantum execution
2. Worker sends `WorkerReport::ChannelActivity { channel_ids }` to coordinator
3. Coordinator immediately checks `WakeRegistry` for affected channels
4. Blocked threads are woken without waiting for the next poll interval

The poll interval has been increased from 50ms to 500ms since event-driven wake
handles the common case. Polling remains as a fallback for edge cases.

## 7. References

- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*. Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus. *Proceedings of POPL*, pp. 372-385.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University Press.
