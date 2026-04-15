# HillClimber Integration -- Adaptive Worker Scaling

## 1. Problem Statement

The optimal number of native worker threads depends on the workload: a
grammar with deep parallel composition (`P | Q | R | ...`) benefits from
many workers, while a sequential grammar wastes resources spinning idle
workers. Rather than requiring the user to manually tune the worker count,
PraTTaIL uses a **hill climbing** algorithm to adaptively scale the worker
pool at runtime.

## 2. Throughput Observation via EMA

### 2.1 Exponential Moving Average

The hill climber tracks throughput (tasks completed per observation interval)
using a fixed-point exponential moving average (EMA):

```
    EMA_t = alpha * x_t + (1 - alpha) * EMA_{t-1}
```

where:
- x_t = observed throughput at time t (tasks completed in the last interval)
- alpha = smoothing factor = 1/4 (ALPHA_NUM / ALPHA_DEN)
- EMA_0 = 0

**Why alpha = 1/4?** This gives a time constant of ~4 intervals (at
500ms per interval, ~2 seconds). The EMA responds to sustained throughput
changes within 2--3 intervals while filtering out single-interval noise.

### 2.2 Fixed-Point Representation

Floating-point atomics do not exist in the Rust standard library. To enable
lock-free updates, the EMA is stored as a scaled integer:

```
    stored_ema = EMA * 1024    (10-bit fixed point, EMA_SCALE = 1024)
```

The update formula in fixed-point arithmetic:

```
    scaled_sample = x_t * 1024
    new_ema = (1 * scaled_sample + 3 * old_ema) / 4
```

This uses only integer multiplication and division, which map to
`AtomicU64` load/store operations. No CAS loop is needed because the
coordinator thread is the sole writer; workers only read the EMA for
diagnostics.

### 2.3 Data Flow

```
    ┌──────────────────────────────────────────────────────┐
    │                   Coordinator Thread                  │
    │                                                      │
    │  Every 500ms:                                        │
    │    tasks_completed = metrics.total_completed - prev  │
    │    hill_climber.observe_throughput(tasks_completed)   │
    │    suggested = hill_climber.suggest_worker_count()    │
    │    (future: pool.resize(suggested))                  │
    └──────────────────────────────────────────────────────┘
                           │
                           ▼
    ┌──────────────────────────────────────────────────────┐
    │                  HillClimber State                    │
    │                                                      │
    │  throughput_ema:  AtomicU64  (fixed-point * 1024)    │
    │  previous_ema:    AtomicU64  (for trend detection)   │
    │  current_workers: AtomicU32  (current count)         │
    │  direction:       AtomicI32  (+1 grow, -1 shrink)    │
    │  step_size:       AtomicU32  (always 1)              │
    │  min_workers:     u32        (floor, >= 1)           │
    │  max_workers:     u32        (ceiling, <= num_cpus)  │
    └──────────────────────────────────────────────────────┘
```

## 3. Hill Climbing Algorithm

### 3.1 Core Logic

The algorithm observes throughput, compares the current EMA with the previous
EMA, and adjusts the worker count:

```
    function suggest_worker_count():
        current_ema  <- throughput_ema.load()
        prev_ema     <- previous_ema.load()
        current      <- current_workers.load()
        step         <- step_size.load()

        if current_ema >= prev_ema:
            // Throughput improved or held steady:
            // continue in the same direction
            dir <- direction.load()
        else:
            // Throughput worsened:
            // reverse direction
            dir <- -direction.load()
            direction.store(dir)

        suggested <- current + dir * step
        clamped   <- clamp(suggested, min_workers, max_workers)
        current_workers.store(clamped)
        return clamped
```

### 3.2 Direction and Step Size

- **Direction** starts at +1 (grow). The hill climber is optimistic: it
  assumes more workers will help until proven otherwise.
- **Step size** is fixed at 1. Larger steps would converge faster but
  overshoot more. For the typical range of 1--32 workers, step size 1
  provides sufficient responsiveness.

### 3.3 Hysteresis and Clamping

The `clamp(suggested, min_workers, max_workers)` operation prevents:
- **Under-provisioning**: At least `min_workers` (default 1) are always active.
- **Over-provisioning**: At most `max_workers` (default `num_cpus`) are active,
  avoiding excessive context switching at the OS level.

When the suggested count hits a bound, the direction reverses on the next
observation if throughput drops, creating a natural oscillation around the
optimal point.

## 4. Convergence Behavior

### 4.1 Stable Workload

Under a constant workload, the hill climber converges to the optimal worker
count in O(max_workers) ticks (observation intervals). The convergence path
looks like:

```
    Throughput                    Optimal
       ^                            |
       |        ___________________/|\_____________
       |       /                    |
       |      /                     |
       |     /                      |
       |    /                       |
       |___/                        |
       +----+----+----+----+----+----+----+----> Workers
       1    2    3    4    5    6    7    8

    Direction:  +1   +1   +1   +1   +1   -1   +1  (oscillates)
```

Once the optimal count is reached, throughput plateaus. Adding one more
worker causes throughput to drop (contention), the direction reverses, and
the climber oscillates between optimal and optimal+1 (or optimal-1).

### 4.2 Variable Workload

When the workload changes (e.g., a grammar with alternating parallel and
sequential phases), the EMA responds within 2--3 intervals. The climber
re-converges to the new optimal point. The oscillation band is at most
+/- 1 worker from optimal under smooth workload transitions.

### 4.3 Worst-Case Convergence Time

Starting from `min_workers`, the climber needs at most
`max_workers - min_workers` ticks to reach `max_workers`. At 500ms per
tick, this is at most `(max_workers - 1) * 0.5` seconds. For a typical
8-core system: 3.5 seconds to traverse the full range.

## 5. Coordinator Integration

The coordinator thread drives the adaptive scaling loop:

```
    loop:
        // 1. Process scheduler events (dispatch, complete, fork, ...)
        actions = scheduler.tick()
        execute(actions)

        // 2. Check for channel wake-ups
        to_wake = wake_registry.check_and_wake(channel_map)
        for (tid, _ch) in to_wake:
            resume(tid)

        // 3. Adaptive scaling (every scale_check_interval)
        if elapsed >= scale_check_interval:
            tasks_now = metrics.total_completed.load()
            tasks_completed = tasks_now - prev_tasks
            prev_tasks = tasks_now

            hill_climber.observe_throughput(tasks_completed)
            suggested = hill_climber.suggest_worker_count()
            // (Actual pool resizing deferred to future sprint)

        // 4. Park if idle
        if scheduler.is_idle():
            park(scale_check_interval)
```

### 5.1 Configuration

| Parameter | Default | Environment Variable |
|-----------|---------|---------------------|
| scale_check_interval | 500ms | -- |
| min_workers | 1 | -- |
| max_workers | num_cpus | PRATTAIL_WORKERS (overrides) |
| alpha | 1/4 | -- |
| initial direction | +1 (grow) | -- |
| step_size | 1 | -- |

### 5.2 Future Work: Actual Pool Resizing

The current implementation computes the suggested worker count but does not
yet spawn or park workers dynamically. The `WorkerPool` has a fixed size set
at `GlobalPool::start()`. When pool resizing is implemented:

- **Grow**: The coordinator spawns a new worker thread and pushes its
  `Stealer` handle into the shared stealer list.
- **Shrink**: The coordinator sets a per-worker shutdown flag. The targeted
  worker finishes its current quantum and exits its run loop. Its local
  deque contents are drained to the global injector for redistribution.

## 6. Throughput vs. Worker Count: ASCII Visualization

```
    Tasks/sec
    (throughput)
       ^
    120|                  * * *
       |                *       *
    100|              *           *
       |            *               *
     80|          *                   *
       |        *
     60|      *
       |    *
     40|  *
       |*
     20|
       +--+--+--+--+--+--+--+--+--+--+--> Workers
       0  1  2  3  4  5  6  7  8  9  10

    The hill climber starts at 1 worker, observes increasing
    throughput as it grows, reaches the peak at ~6 workers,
    observes declining throughput (contention) at 7+, reverses
    direction, and oscillates around 6 +/- 1.
```

## Worker Pool Growth (GS-3)

The worker pool supports **growing only** (not shrinking). When the HillClimber suggests
more workers than currently exist, the coordinator calls `WorkerPool::grow(additional)`:

- New workers share the existing injector and parker
- They can pick up work from the global queue and be woken by unpark signals
- They cannot steal from original workers' local deques (the injector is the primary path)
- JoinHandles are not tracked; workers exit via the shared shutdown flag

### Why Grow-Only

Shrinking requires:
1. Signaling specific workers to stop (not just any worker)
2. Draining their local deques before they exit
3. Managing JoinHandle ownership (conflicts with `Arc<WorkerPool>`)
4. Handling in-flight work when a worker is removed

These complexities are deferred. Growing provides the critical scaling benefit
(handling load spikes) while shrinking can be approximated by parking idle workers.

## 7. Lock-Free Guarantees

All HillClimber fields are atomic:

| Field | Type | Ordering |
|-------|------|----------|
| `current_workers` | `AtomicU32` | Acquire/Release |
| `throughput_ema` | `AtomicU64` | Acquire/Release |
| `previous_ema` | `AtomicU64` | Acquire/Release |
| `direction` | `AtomicI32` | Acquire/Release |
| `step_size` | `AtomicU32` | Acquire/Release |

No locks, no CAS loops, no contention. The coordinator is the sole writer;
diagnostic readers use Acquire ordering to see the latest values.

## 8. References

- .NET CLR ThreadPool hill climbing algorithm (Helander & Doll, 2008).
  Microsoft .NET Runtime source: `src/libraries/System.Threading.ThreadPool`.
- MeTTaTron `PriorityScheduler` adaptive scaling (internal).
