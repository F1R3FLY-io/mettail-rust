# Streaming Automata: Real-Time Monitors

## What Is It?

Streaming automata are online monitors that process trace events one at a time, maintaining a finite internal state that summarizes the trace seen so far. They emit **alerts** when anomalous conditions are detected. Their memory usage is O(1) or O(window_size), not O(trace_length), enabling monitoring of arbitrarily long simulation traces.

Located in `simulation/src/streaming_automaton.rs`.

## What Does It Do?

The streaming automaton module provides:

1. **StreamingMonitor trait**: the interface for all streaming monitors.
2. **WindowedMonitor**: tracks metrics over a sliding window of the last N events.
3. **AggregateMonitor**: tracks running statistics (mean, variance, min, max) via Welford's algorithm.
4. **CompositeMonitor**: runs multiple monitors in parallel over the same trace.

## Why Was It Chosen?

### The Buffering Problem

Post-hoc trace analysis requires storing the entire trace in memory or on disk. For a simulation producing millions of events, this is impractical. Streaming monitors solve this by maintaining only the information needed for their specific checks.

### Composability

Different monitors check different properties. A `WindowedMonitor` detects local trends (e.g., "term size increased for 50 consecutive steps"). An `AggregateMonitor` tracks global statistics (e.g., "the overall mean term size is 42.3 with standard deviation 7.1"). A `CompositeMonitor` runs both in parallel, delivering a unified stream of alerts.

### Real-Time Invariant Checking

Unlike the `Invariant` trait (which checks a single state), streaming monitors can detect **temporal patterns** that span multiple states. A sliding window can detect monotonic increase, stagnation, and variance spikes -- all of which require context across multiple steps.

## The StreamingMonitor Trait

```rust
pub trait StreamingMonitor: Send + Sync {
    /// The monitor's name (for alert attribution).
    fn name(&self) -> &str;

    /// Process a single trace event. Returns alerts (if any).
    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert>;

    /// Finalize at the end of the trace. Returns remaining alerts.
    fn finalize(&mut self) -> Vec<MonitorAlert>;

    /// Reset to initial state (for reuse across runs).
    fn reset(&mut self);
}
```

### TraceEvent

```rust
pub struct TraceEvent {
    pub step: usize,          // 0-based step index
    pub term_display: String, // display string of current term
    pub operation: String,    // "parse", "rewrite:Comm", etc.
    pub term_size: usize,     // approximate AST node count
    pub term_depth: usize,    // maximum nesting depth
}
```

### MonitorAlert

```rust
pub struct MonitorAlert {
    pub step: usize,           // step at which alert was triggered
    pub monitor_name: String,  // name of the monitor that produced it
    pub severity: AlertSeverity,
    pub message: String,
}

pub enum AlertSeverity {
    Info,     // informational
    Warning,  // potential issue
    Error,    // invariant violated
}
```

## WindowedMonitor

### What It Is

A monitor that maintains a sliding window of the last N metric values and checks a condition over the window at each step.

### How It Works

```
┌──────────────────────────────────────────────────┐
│  Sliding Window (size = 5)                       │
│                                                  │
│  step 0:  [3]                        (no check)  │
│  step 1:  [3, 5]                     (no check)  │
│  step 2:  [3, 5, 7]                  (no check)  │
│  step 3:  [3, 5, 7, 4]               (no check)  │
│  step 4:  [3, 5, 7, 4, 8]            CHECK       │
│  step 5:  [5, 7, 4, 8, 12]           CHECK       │
│  step 6:  [7, 4, 8, 12, 6]           CHECK       │
│           ▲              ▲                       │
│           oldest         newest                  │
└──────────────────────────────────────────────────┘
```

The window is implemented as a `VecDeque<f64>` that acts as a circular buffer. When the window is full, the oldest value is evicted before the newest is added.

### Window Check Types

```rust
pub enum WindowCheck {
    MeanAbove,               // alert if mean > threshold
    MeanBelow,               // alert if mean < threshold
    VarianceAbove,           // alert if variance > threshold
    MonotonicallyIncreasing, // alert if all values are non-decreasing
    Stagnant,                // alert if all values are identical
}
```

**MeanAbove:** Detects sustained high term sizes. Useful for catching complexity explosions:

```
PROCEDURE check_mean_above():
    IF |window| < window_size THEN RETURN None
    mean ← Σ window / |window|
    IF mean > threshold THEN
        RETURN Alert(Warning, "Window mean {mean} exceeds threshold {threshold}")
    RETURN None
```

**MonotonicallyIncreasing:** Detects monotonic growth, a signal of potential non-termination:

```
PROCEDURE check_monotonically_increasing():
    IF |window| < window_size THEN RETURN None
    increasing ← ∀ i: window[i+1] ≥ window[i]
    IF increasing THEN
        RETURN Alert(Warning, "Term size monotonically increasing
                                over {window_size} steps")
    RETURN None
```

**Stagnant:** Detects structural stagnation (the term is not changing):

```
PROCEDURE check_stagnant():
    IF |window| < window_size THEN RETURN None
    first ← window[0]
    all_same ← ∀ x ∈ window: |x - first| < ε
    IF all_same THEN
        RETURN Alert(Info, "Term stagnant (size = {first})
                            for {window_size} steps")
    RETURN None
```

### Convenience Constructors

```rust
// Alert when mean term size exceeds 1000 over a window of 50 steps
WindowedMonitor::term_size_bound(1000.0, 50)

// Alert when term size is monotonically increasing over 20 steps
WindowedMonitor::growing_term(20)

// Alert when term is unchanged for 30 steps
WindowedMonitor::stagnation_detector(30)
```

## AggregateMonitor

### What It Is

A monitor that tracks running statistics over the entire trace using Welford's online algorithm. Memory usage is O(1) regardless of trace length.

### How It Works

```
PROCEDURE AggregateMonitor.process(event):
    x ← event.term_size as f64

    // Welford's online algorithm
    count ← count + 1
    δ ← x - mean
    mean ← mean + δ / count
    δ₂ ← x - mean
    M₂ ← M₂ + δ · δ₂

    min ← min(min, x)
    max ← max(max, x)

    // Threshold check (only after 10 observations for stability)
    IF alert_threshold is Some(t) AND mean > t AND count ≥ 10 THEN
        RETURN [Alert(Warning, "Running mean {mean} exceeds threshold {t}
                                (n={count}, σ={stddev})")]

    RETURN []
```

### Finalization

At the end of the trace, the aggregate monitor emits an informational summary:

```
PROCEDURE AggregateMonitor.finalize():
    RETURN [Alert(Info, "Final stats: mean={mean}, σ={stddev},
                         min={min}, max={max}, n={count}")]
```

### Summary Access

```rust
pub fn summary(&self) -> AggregateSummary {
    AggregateSummary {
        count: self.count,
        mean: self.mean,
        variance: self.variance(),
        min: self.min,
        max: self.max,
    }
}
```

## CompositeMonitor

### What It Is

A monitor that runs multiple sub-monitors in parallel over the same event stream. Each sub-monitor receives the same `TraceEvent` and produces its own alerts independently.

### How It Works

```
┌───────────────────────────────────────────────────────┐
│  CompositeMonitor                                     │
│                                                       │
│  event ──┬──▶ WindowedMonitor (growth)  ──▶ alerts    │
│          ├──▶ WindowedMonitor (stagnation) ──▶ alerts │
│          ├──▶ AggregateMonitor (stats) ──▶ alerts     │
│          └──▶ CustomMonitor ──▶ alerts                │
│                                                       │
│  all alerts merged into single output stream          │
└───────────────────────────────────────────────────────┘
```

```rust
pub struct CompositeMonitor {
    name: String,
    monitors: Vec<Box<dyn StreamingMonitor>>,
}
```

```
PROCEDURE CompositeMonitor.process(event):
    alerts ← []
    FOR monitor in monitors:
        alerts.extend(monitor.process(event))
    RETURN alerts

PROCEDURE CompositeMonitor.finalize():
    alerts ← []
    FOR monitor in monitors:
        alerts.extend(monitor.finalize())
    RETURN alerts

PROCEDURE CompositeMonitor.reset():
    FOR monitor in monitors:
        monitor.reset()
```

### Builder Pattern

```rust
let monitor = CompositeMonitor::new("simulation_monitor")
    .add(WindowedMonitor::term_size_bound(1000.0, 50))
    .add(WindowedMonitor::growing_term(20))
    .add(WindowedMonitor::stagnation_detector(30))
    .add(AggregateMonitor::new("term_size_stats").with_threshold(500.0));
```

## Integration with the Simulation Pipeline

Streaming monitors process events extracted from `TraceEntry` records:

```rust
let event = TraceEvent {
    step: entry.step_index,
    term_display: entry.term_display.clone(),
    operation: entry.operation.clone(),
    term_size: entry.metrics.as_ref().map(|m| m.node_count).unwrap_or(0),
    term_depth: entry.metrics.as_ref().map(|m| m.depth).unwrap_or(0),
};

let alerts = monitor.process(&event);
for alert in alerts {
    match alert.severity {
        AlertSeverity::Error => { /* fail the simulation */ }
        AlertSeverity::Warning => { /* log and continue */ }
        AlertSeverity::Info => { /* record for summary */ }
    }
}
```

## Writing Custom Monitors

Implement the `StreamingMonitor` trait:

```rust
struct MaxDepthMonitor {
    max_allowed: usize,
}

impl StreamingMonitor for MaxDepthMonitor {
    fn name(&self) -> &str { "max_depth" }

    fn process(&mut self, event: &TraceEvent) -> Vec<MonitorAlert> {
        if event.term_depth > self.max_allowed {
            vec![MonitorAlert {
                step: event.step,
                monitor_name: self.name().to_string(),
                severity: AlertSeverity::Error,
                message: format!("Depth {} exceeds max {}", event.term_depth, self.max_allowed),
            }]
        } else {
            vec![]
        }
    }

    fn finalize(&mut self) -> Vec<MonitorAlert> { vec![] }
    fn reset(&mut self) {}
}
```

Then add it to a composite monitor:

```rust
let monitor = CompositeMonitor::new("all")
    .add(MaxDepthMonitor { max_allowed: 100 })
    .add(AggregateMonitor::new("stats"));
```

## Memory Analysis

| Monitor          | Memory                 | Per-Event Cost                                     |
|------------------|------------------------|----------------------------------------------------|
| WindowedMonitor  | O(window_size)         | O(window_size) for variance check, O(1) for others |
| AggregateMonitor | O(1)                   | O(1)                                               |
| CompositeMonitor | O(Σ sub-monitor sizes) | O(Σ sub-monitor costs)                             |

For a typical configuration (window size 50, 3 sub-monitors), total memory is approximately 500 bytes regardless of trace length.
