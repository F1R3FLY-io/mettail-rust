# Term Morphology Tracking

## What Is It?

Morphology tracking records structural metrics of terms across simulation steps, detecting anomalies such as unbounded growth (potential non-termination), structural stagnation (stuck rewriting), and complexity explosion. The system is designed to work uniformly across all MeTTaIL languages without requiring language-specific AST access.

Located in `simulation/src/morphology.rs`.

## What Does It Do?

The morphology system provides two components:

1. **TermMetrics**: A lightweight snapshot of a term's structural properties (node count, depth, fingerprint), computed from the term's display string.
2. **MorphologyTracker**: An accumulator that records `TermMetrics` at each simulation step, computes summary statistics, and detects anomalous patterns via sliding-window trend analysis.

## Why Was It Chosen?

### Language-Agnostic Design

MeTTaIL supports many language definitions (Calculator, Lambda, Rholang, Ambient, etc.), each with a different AST structure. A morphology tracker that operates on the AST would need to be parameterized by the language type, breaking the uniform `SimulationRunner` interface.

Instead, `TermMetrics` is computed from the **display string**, using two universal structural proxies:

- **Node count**: the number of whitespace-separated tokens (approximating AST nodes)
- **Depth**: the maximum nesting depth of parentheses, brackets, and braces

These heuristics work across all languages because MeTTaIL's display format follows a consistent S-expression-like structure: `(Constructor arg1 arg2 ...)`.

### Mathematical Basis: Welford's Online Algorithm

The `MorphologyTracker` computes summary statistics (mean, min, max) over an unbounded stream of `TermMetrics` values. The underlying algorithm is Welford's online method (Welford (1962)), which maintains a running mean and sum of squared deviations in a single pass with O(1) space per update.

Welford's algorithm avoids the numerical instability of the naive two-pass formula `var = E[X^2] - E[X]^2`, which suffers from catastrophic cancellation when the mean is large relative to the variance. This matters for simulation traces where thousands of terms may have similar sizes.

## How Does It Work?

### TermMetrics

```rust
pub struct TermMetrics {
    pub node_count: usize,             // whitespace-separated token count
    pub depth: usize,                  // max parenthesis nesting depth
    pub structural_fingerprint: u64,   // hash of display string
}
```

The metrics are computed from the display string:

```
PROCEDURE TermMetrics::from_display(display: str) → TermMetrics:
    node_count ← max(1, count of whitespace-separated tokens in display)

    max_depth ← 0
    current_depth ← 0
    FOR ch in display:
        IF ch ∈ {'(', '[', '{'} THEN
            current_depth ← current_depth + 1
            max_depth ← max(max_depth, current_depth)
        ELSE IF ch ∈ {')', ']', '}'} THEN
            current_depth ← saturating_sub(current_depth, 1)

    fingerprint ← DefaultHasher.hash(display)

    RETURN TermMetrics {
        node_count,
        depth: max_depth,
        structural_fingerprint: fingerprint
    }
```

**Examples:**

| Display String                        | node_count | depth | fingerprint        |
|---------------------------------------|------------|-------|--------------------|
| `42`                                  | 1          | 0     | h("42")            |
| `(AddInt 3 5)`                        | 3          | 1     | h("(AddInt 3 5)")  |
| `(1 + (2 * 3))`                       | 5          | 2     | h("(1 + (2 * 3))") |
| `(PPar {(PNew ^x.(PZero)), (PZero)})` | 4          | 3     | h(...)             |

The structural fingerprint is a `u64` hash of the display string. It serves as a quick equality check: if two terms have the same fingerprint, they are very likely structurally identical (modulo hash collisions). The tracker uses fingerprints to detect **structural stagnation** (the term is not changing despite rewrites still firing).

### MorphologyTracker

The tracker maintains a history of `TermMetrics` and a list of alerts:

```rust
pub struct MorphologyTracker {
    metrics: Vec<TermMetrics>,
    alerts: Vec<MorphologyAlert>,
    trend_window: usize,             // default: 10
}
```

Each call to `record(metrics)` appends to the history and triggers trend detection:

```
PROCEDURE MorphologyTracker.record(metrics):
    self.metrics.push(metrics)
    self.check_trends()

PROCEDURE MorphologyTracker.check_trends():
    IF |self.metrics| < self.trend_window THEN RETURN

    window ← self.metrics[|metrics| - trend_window ..]

    // Check 1: Monotonically increasing node count
    monotone ← ∀ i ∈ [0, |window|-2]:
        window[i+1].node_count ≥ window[i].node_count
      AND window[last].node_count > window[first].node_count

    IF monotone THEN
        self.alerts.push(MorphologyAlert {
            step: |self.metrics| - 1,
            message: "Node count monotonically increasing over last
                      {trend_window} steps ({first} → {last})"
        })

    // Check 2: Structural stagnation
    first_fp ← window[0].structural_fingerprint
    all_same ← ∀ m ∈ window: m.structural_fingerprint == first_fp

    IF all_same AND |self.metrics| > self.trend_window THEN
        self.alerts.push(MorphologyAlert {
            step: |self.metrics| - 1,
            message: "Term structurally stagnant for {trend_window} steps
                      (fingerprint={first_fp:#x})"
        })
```

### Drift Detection

**Monotonically increasing node count** is a signal of potential non-termination. If every step in the window produces a term at least as large as the previous step, and the last term is strictly larger than the first, the tracker raises an alert.

This detects rewrite rules that consistently increase term size, such as:

```
x → f(x, x)     // doubles term size each step
x → cons(x, x)  // similarly
```

### Complexity Explosion

A sudden spike in node count or depth (even if not monotonic) is captured by the summary statistics. The `MorphologySummary.max_nodes` and `MorphologySummary.max_depth` fields record the peak values, and the `mean_nodes` / `mean_depth` provide baselines for comparison.

### Non-Convergence (Stagnation)

If all fingerprints in the window are identical, the term is not changing. This can indicate:

- **Stuck rewriting**: the term is not in normal form but no rules apply (a bug in the rewrite system).
- **Oscillation**: the term is cycling between two or more states, but the window happens to capture a static phase.
- **Completed rewriting**: the term has reached normal form and the runner is still recording the same term. (This is benign and typically only occurs when `track_morphology` is enabled for post-normal-form observation.)

The stagnation alert is suppressed during the first `trend_window` steps to avoid false positives during the initial parse phase.

### MorphologySummary

The `summary()` method computes aggregate statistics over all recorded metrics:

```
PROCEDURE MorphologyTracker.summary() → MorphologySummary:
    IF metrics is empty THEN RETURN default summary

    total_steps ← |metrics|
    min_nodes, max_nodes, sum_nodes ← aggregate over metrics[].node_count
    min_depth, max_depth, sum_depth ← aggregate over metrics[].depth
    distinct_shapes ← |{m.structural_fingerprint : m ∈ metrics}|

    RETURN MorphologySummary {
        total_steps,
        min_nodes, max_nodes,
        mean_nodes: sum_nodes / total_steps,
        min_depth, max_depth,
        mean_depth: sum_depth / total_steps,
        distinct_shapes,
        alerts: self.alerts.clone()
    }
```

The `distinct_shapes` count is particularly useful: if a 100-step simulation produces only 3 distinct shapes, the rewrite system is highly constrained. If it produces 100 distinct shapes, the terms are evolving rapidly.

### Trend Detection via Linear Regression

While the current implementation uses monotonicity detection (a simple but effective heuristic), the framework is designed to support more sophisticated trend detection. Linear regression over the window can detect:

- **Linear growth**: slope > 0 with high R^2, indicating steady unbounded growth
- **Exponential growth**: log-transform followed by linear regression, indicating doubling behavior
- **Oscillation**: low R^2 with high variance, indicating cyclic behavior

The sliding window approach ensures that trend detection is responsive to recent behavior rather than being dominated by early-trace transients.

### Welford's Algorithm for Summary Statistics

The `MorphologySummary` uses a simple single-pass aggregation. The `StreamingWeight` semiring (see [semirings/streaming.md](semirings/streaming.md)) provides the full Welford algorithm with parallel merge capability. The morphology tracker uses the simpler version because it operates sequentially and does not need the parallel merge.

The relationship between the two is:

| Feature        | MorphologyTracker         | StreamingWeight       |
|----------------|---------------------------|-----------------------|
| Mean           | Σ/n (exact)               | Welford's online mean |
| Variance       | Not computed              | Welford's M2/(n-1)    |
| Parallel merge | Not needed                | Chan et al. (1979)    |
| Memory         | O(n) (stores all metrics) | O(1)                  |

## Integration with the SimulationRunner

The `SimulationRunner` creates a `MorphologyTracker` if `config.track_morphology` is true:

```
morphology_tracker ← if track_morphology then Some(MorphologyTracker::new()) else None

// After each step:
if let Some(tracker) = &mut morphology_tracker {
    tracker.record(metrics);
}

// At the end:
morphology_summary ← morphology_tracker.map(|t| t.summary())
```

The summary is included in the `ExecutionTrace` and, at the campaign level, in the `CampaignResults.aggregate_morphology`.

## References

- Welford, B.P. (1962). "Note on a Method for Calculating Corrected Sums of Squares and Products." Technometrics, 4(3), pp. 419-420.
- Chan, T.F., Golub, G.H., and LeVeque, R.J. (1979). "Updating Formulae and a Pairwise Algorithm for Computing Sample Variances." Technical Report STAN-CS-79-773, Stanford University.
