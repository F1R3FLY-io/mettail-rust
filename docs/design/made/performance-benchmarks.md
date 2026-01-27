# Performance Benchmarks Design for MeTTaIL Rho-Calculus

**Status**: Design Document  
**Date**: January 2026

## Overview

This document describes the design for performance benchmarks targeting the Ascent-based term rewriting engine for rho-calculus. The benchmarks measure:

1. **Execution time** across scaling dimensions
2. **Term/rewrite explosion** characteristics  
3. **Memory usage** patterns
4. **Bottleneck identification** for optimization

## Architecture Understanding

### Execution Model

```
Input Term → Parse → Normalize → Ascent Datalog Fixpoint → Results
                                       ↓
                     Relations: proc, name, rw_proc, eq_proc, path
```

The Ascent engine computes:
- **Category exploration**: Discover all subterms
- **Rewrite relations**: Apply reduction rules
- **Equational closure**: Compute equivalences
- **Path computation**: Transitive closure of rewrites

### Known Performance Characteristics

| Component | Complexity | Impact |
|-----------|------------|--------|
| Collection deconstruction | O(N×M) | HIGH - fact explosion |
| Equational closure | O(N²) | HIGH - union-find blowup |
| Rewrite transitivity | O(R×E) | MEDIUM - path explosion |
| Pattern matching | O(N×M) | MEDIUM - iteration cost |
| Path computation | O(K²) | LOW - final stage |

Where: N=term count, M=avg collection size, R=rewrites, E=equivalences, K=rewrite count

## Benchmark Dimensions

### 1. Term Size Scaling

Measure how execution time scales with initial term complexity.

| Test | Pattern | Expected Scaling |
|------|---------|------------------|
| `size_linear` | n independent zero processes | O(n) |
| `size_quadratic` | n×n communication pairs | O(n²) |
| `size_nested` | n-deep nesting | O(n) to O(n²) |

### 2. Rewrite Depth

Measure performance as reduction chains grow longer.

| Test | Pattern | Expected Scaling |
|------|---------|------------------|
| `depth_pipeline` | a→b→c→...→z chain | O(depth) |
| `depth_recursive` | Self-spawning process | O(depth²) - path explosion |

### 3. Parallelism Degree

Measure impact of concurrent process count.

| Test | Pattern | Expected Scaling |
|------|---------|------------------|
| `parallel_independent` | n non-interacting pairs | O(n) ideal |
| `parallel_contention` | n processes, 1 channel | O(n!) paths |
| `parallel_fanout` | 1→n broadcast | O(n) |

### 4. Non-determinism

Measure branching factor impact on state space.

| Test | Pattern | Expected Behavior |
|------|---------|-------------------|
| `ndet_race` | 2 senders, 1 receiver | 2 paths |
| `ndet_choice` | 1 sender, n receivers | n paths |
| `ndet_full` | n senders, n receivers | n! paths |

### 5. Reflection Patterns

Measure cost of quote/drop cycles.

| Test | Pattern | Stress Target |
|------|---------|---------------|
| `reflect_simple` | `*(@(P))` | PDrop rewrite |
| `reflect_nested` | `*(@(*(@(...))))` | Equation application |
| `reflect_comm` | Send quoted process, drop | Combined |

### 6. Collection Operations

Measure HashBag matching complexity.

| Test | Pattern | Stress Target |
|------|---------|---------------|
| `coll_small` | 3-element parallel | Baseline |
| `coll_medium` | 10-element parallel | Iteration cost |
| `coll_large` | 50-element parallel | Deconstruction |
| `coll_nested` | Nested parallel | Recursive matching |

### 7. Replication Pattern (Primary Target)

The `rep` combinator from `rhocalc.txt`:
```
dup = ^l.{l?x.{{*(x) | l!(*(x))}}}
rep = ^n.{^a.{^cont.{{$name(dup,n)|n!(a?y.{{$name(cont,y)|$name(dup,n)}})}}}}
```

This creates **persistent replicated input** - a fundamental rho-calculus idiom.

| Test | Pattern | Measures |
|------|---------|----------|
| `rep_basic` | `rep(loc, server, id)` | Basic replication |
| `rep_multiple` | Multiple replicated services | Interaction |
| `rep_stress` | Replicated + many clients | Real-world load |

## Metrics to Capture

### Primary Metrics (per benchmark)
- **Execution time** (mean, std dev, min, max)
- **Term count** (unique terms discovered)
- **Rewrite count** (reduction steps)
- **Normal form count** (final states)

### Secondary Metrics (profiling mode)
- **Memory peak** (RSS)
- **Relation sizes** (proc, rw_proc, eq_proc)
- **Iteration count** (fixpoint rounds)

## Test Case Generators

### Linear Scaling Generator
```rust
fn gen_parallel_procs(n: usize) -> String {
    // {0 | 0 | ... | 0}  (n zeros)
    let procs: Vec<_> = (0..n).map(|_| "0").collect();
    format!("{{{}}}", procs.join(" | "))
}
```

### Communication Pair Generator
```rust
fn gen_comm_pairs(n: usize) -> String {
    // {a1!(0) | a1?x.{*(x)} | a2!(0) | a2?x.{*(x)} | ...}
    let pairs: Vec<_> = (0..n)
        .map(|i| format!("a{}!(0) | a{}?x.{{*(x)}}", i, i))
        .collect();
    format!("{{{}}}", pairs.join(" | "))
}
```

### Pipeline Generator
```rust
fn gen_pipeline(depth: usize) -> String {
    // {a!(0) | a?x.{b!(*(x))} | b?x.{c!(*(x))} | ... | z?x.{*(x)}}
    let stages: Vec<_> = ('a'..'z')
        .take(depth)
        .collect();
    // ... build pipeline
}
```

### Replication Client Generator
```rust
fn gen_rep_clients(n_clients: usize) -> String {
    // rep(loc, server, id) with n client requests
    format!(
        "$proc($name($name(rep, loc), server), id) | {}",
        (0..n_clients)
            .map(|i| format!("server!(client{})", i))
            .collect::<Vec<_>>()
            .join(" | ")
    )
}
```

## Baseline Results (January 2026)

**Environment**: Release build, Criterion benchmarks, ~50 samples per measurement

### Communication Pairs Scaling (Primary Bottleneck)

| Pairs | Time | Per-Pair Factor | Throughput |
|-------|------|-----------------|------------|
| 1 | 206µs | baseline | 4.9K elem/s |
| 2 | 1.38ms | 6.7× | 1.5K elem/s |
| 3 | 9.1ms | 6.6× | 330 elem/s |
| 4 | 46.5ms | 5.1× | 86 elem/s |
| 5 | 193ms | 4.1× | 26 elem/s |
| 6 | 662ms | 3.4× | 9 elem/s |

**Analysis**: Super-linear scaling (~O(n!) or O(n² × 2^n)) due to combinatorial state space explosion. Each additional communication pair multiplies the rewrite graph dramatically.

### Pipeline Depth Scaling

| Depth | Time | Growth Factor |
|-------|------|---------------|
| 2 | ~200µs | baseline |
| 3 | ~700µs | 3.5× |
| 4 | 1.9ms | 2.7× |
| 5 | 6.5ms | 3.4× |
| 6 | 10.8ms | 1.7× |
| 8 | 24ms | 2.2× |
| 10 | 50ms | 2.1× |

**Analysis**: Roughly O(n²) scaling - expected for sequential path computation.

### Reflection Depth (Quote-Drop Chains)

| Depth | Time | Growth Factor |
|-------|------|---------------|
| 1 | ~60µs | baseline |
| 3 | ~200µs | 3.3× |
| 5 | 731µs | 3.7× |
| 8 | 2.8ms | 3.8× |
| 10 | 5.7ms | 2× |

**Analysis**: Approximately O(n × log n) or O(n^1.5) - each nesting level adds bounded work.

### Replication Pattern (Primary Target)

| Pattern | Time |
|---------|------|
| `rep(loc, server, id)` | **39ms** |

**Analysis**: Matches ~4 comm pairs equivalent complexity. The replication combinator creates a persistent replicated input that unfolds into nested communications.

### Parallel Zero Processes (Baseline)

| Count | Time |
|-------|------|
| 1 | 41µs |
| 10 | 42µs |
| 50 | ~45µs |

**Analysis**: Near-O(1) as expected - zeros don't interact.

### Target Performance (after optimizations)

| Test | Current | Target | Speedup Goal |
|------|---------|--------|--------------|
| 1 comm pair | 206µs | 50µs | 4× |
| 4 comm pairs | 46ms | 10ms | 4.6× |
| Pipeline-6 | 11ms | 3ms | 3.7× |
| Replication | 39ms | 10ms | 3.9× |
| Reflect-10 | 5.7ms | 1.5ms | 3.8× |

Primary optimization targets:
1. Lazy collection deconstruction
2. Limited congruence rules
3. Demand-driven evaluation

## Benchmark Infrastructure

### Directory Structure
```
languages/
  benches/
    rhocalc_bench.rs      # Main benchmark file
    generators.rs         # Test case generators
    metrics.rs            # Custom metric collection
  Cargo.toml              # Add criterion dependency
```

### Criterion Configuration
```rust
criterion_group! {
    name = scaling;
    config = Criterion::default()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = 
        bench_size_linear,
        bench_size_quadratic,
        bench_depth_pipeline,
        bench_parallel_independent,
}
```

### Custom Metrics Wrapper
```rust
struct BenchResult {
    duration: Duration,
    term_count: usize,
    rewrite_count: usize,
    normal_form_count: usize,
}

fn run_and_measure(input: &str) -> BenchResult {
    let term = RhoCalcLanguage::parse(input).unwrap();
    let start = Instant::now();
    let results = RhoCalcLanguage::run_ascent_typed(&term);
    BenchResult {
        duration: start.elapsed(),
        term_count: results.all_terms.len(),
        rewrite_count: results.rewrites.len(),
        normal_form_count: results.normal_forms().len(),
    }
}
```

## Implementation Phases

### Phase 1: Infrastructure (This Session)
1. Add Criterion dependency
2. Create benchmark scaffolding
3. Implement 3-4 key benchmarks
4. Establish baselines

### Phase 2: Comprehensive Suite
1. Implement all scaling tests
2. Add generators for parametric tests
3. Create regression tracking

### Phase 3: Profiling Integration
1. Add memory profiling
2. Track relation sizes
3. Identify specific bottlenecks

## Success Criteria

1. **Benchmarks run reliably** - Consistent results across runs
2. **Cover key dimensions** - All identified scaling patterns tested
3. **Actionable output** - Results identify optimization targets
4. **Regression detection** - Can detect performance changes

## Key Findings

### Communication Pairs: The Primary Bottleneck

The most significant finding is the **super-exponential scaling** of communication pairs:

```
1 pair  →  206µs
6 pairs →  662ms  (3200× slowdown for 6× more pairs)
```

This matches the theoretical expectation: n independent communication pairs can interleave in n! ways, creating a state space explosion. The Ascent datalog computes the full reachability relation, which grows combinatorially.

### Optimization Priority

Based on benchmarks, the optimization priority should be:

1. **Communication pair scaling** - Currently O(n!) or worse
   - Target: O(n² × log n) or better
   - Approach: Lazy deconstruction, demand-driven evaluation

2. **Pipeline depth** - Currently O(n²)
   - Target: O(n log n)
   - Approach: Efficient transitive closure (trrel)

3. **Replication** - Currently ~39ms
   - Target: <10ms
   - Approach: Memoization of repeated patterns

### Running Benchmarks

```bash
# Full benchmark suite (takes ~10 minutes)
cargo bench -p mettail-languages

# Specific benchmark group
cargo bench -p mettail-languages "size/comm_pairs"
cargo bench -p mettail-languages "replication"

# View HTML reports
open target/criterion/report/index.html
```

### Regression Detection

Use Criterion's built-in comparison:

```bash
# After changes, run benchmarks again
cargo bench -p mettail-languages

# Criterion automatically compares to previous baseline
# Results show: "Performance has regressed/improved by X%"
```

## Related Documents

- `docs/archive/phase-3/PERFORMANCE-ANALYSIS.md` - Previous analysis
- `docs/design/exploring/performance.md` - Bottleneck identification
- `repl/src/examples/rhocalc.rs` - Example patterns
