# The SimulationRunner API

## What Is It?

The `SimulationRunner` is the central orchestrator of the MeTTaIL simulation framework. It wraps proptest's `TestRunner` to execute **simulation campaigns**: generating random terms via strategies, running them through a language's parse → rewrite pipeline, checking invariants at each step, tracking morphology metrics, and collecting results.

Located in `simulation/src/runner.rs`.

## What Does It Do?

The runner provides two levels of API:

1. **Single-term simulation**: `run_to_normal_form(input: &str)` parses a term, runs the language's selected default runtime backend through `RuntimeBackendReport`, checks invariants at every observable step, and returns a complete `ExecutionTrace`. Ascent-shaped reports are walked as rewrite graphs to a normal form. Dovetail report-shaped outputs become terminal runtime-report outcomes, and observation-shaped Rho outputs become terminal runtime-observation outcomes instead of fabricated Ascent graphs.

2. **Campaign mode**: `run_campaign(strategy)` generates many terms, runs each through the single-term pipeline, collects ALL failures (does not stop at the first), attempts shrinking for each failure, and returns aggregate `CampaignResults`.

## Why Was It Designed This Way?

### Fail-Slow Philosophy

Traditional test runners stop at the first failure. This is efficient for unit tests but counterproductive for simulation. When exploring the space of all possible terms, a single failure reveals little about the failure landscape. Is it a rare corner case or a systematic problem? Does it affect one constructor or many?

The `SimulationRunner` deliberately collects **all** failures. After a campaign of 1000 test cases, the developer might find 47 failures, all involving the `PNew` constructor with depth > 15. This pattern is invisible with fail-fast semantics.

```
PROCEDURE run_campaign(strategy) → CampaignResults:
    results ← CampaignResults::new()
    tracker ← MorphologyTracker::new()
    runner  ← TestRunner(config)

    FOR case_index in 0..proptest_cases:
        value_tree ← strategy.new_tree(&mut runner)
        input ← value_tree.current()

        MATCH run_to_normal_form(input):
            Ok(trace):
                results.record_pass()
                tracker.record(trace.morphology)
                // record rule coverage from trace steps
            Err(failure):
                shrunk ← try_shrink(value_tree, failure, seed)
                results.record_failure(shrunk)

    results.coverage.finalize(total_rules)
    results.aggregate_morphology ← tracker.summary()
    RETURN results
```

### Deterministic Replay

Every test case records its seed. The `SimulationConfig` accepts an optional `seed: Option<[u8; 32]>` that initializes proptest's ChaCha RNG. Given the same seed and language definition, the campaign produces identical results.

Seeds are recorded per-failure in the `SimulationFailure` struct. To replay a specific failure:

```rust
let config = SimulationConfig {
    seed: Some(failure.seed_bytes),
    proptest_cases: 1,
    ..Default::default()
};
let mut runner = SimulationRunner::new(&language, config);
let result = runner.run_to_normal_form(&failure.input);
```

## How Does It Work?

### SimulationConfig

```rust
pub struct SimulationConfig {
    pub max_steps: usize,        // default: 1000
    pub max_term_depth: u32,     // default: 50
    pub proptest_cases: u32,     // default: 100
    pub seed: Option<[u8; 32]>,  // default: None (random)
    pub invariants: Vec<Box<dyn Invariant>>,
    pub ltl_properties: Vec<String>,
    pub track_morphology: bool,  // default: true
    pub trace_output: TraceOutputFormat,
}
```

| Field              | Purpose                                                                                |
|--------------------|----------------------------------------------------------------------------------------|
| `max_steps`        | Maximum rewrite steps before declaring non-termination                                 |
| `max_term_depth`   | Used by morphology tracking and invariant checks                                       |
| `proptest_cases`   | Number of random test cases per campaign                                               |
| `seed`             | Fixed 32-byte seed for deterministic replay                                            |
| `invariants`       | Invariants checked at each step (see [invariants.md](invariants.md))                   |
| `ltl_properties`   | LTL formulas to check (reserved; see [temporal-properties.md](temporal-properties.md)) |
| `track_morphology` | Whether to record TermMetrics at each step                                             |
| `trace_output`     | Where to write traces: None, JSONL file, or in-memory                                  |

### The Single-Term Pipeline

`run_to_normal_form(input: &str)` executes a report-aware pipeline:

```
Phase 1: Parse
├── clear_var_cache()                   // reset variable counter
├── term ← language.parse_term(input)   // parse string into AST
├── metrics ← TermMetrics::from_display(term)
├── tracker.record(metrics)
├── check_invariants()                  // check all invariants
└── steps.push(TraceEntry { op: "parse" })

Phase 2: Selected Runtime Backend
├── clear_var_cache()
├── report ← language.run_default_backend_report(term)
├── IF report.output is Ascent:
│     results contains: all_terms, rewrites, equivalences
└── IF report.output is Observations:
      observations contain backend-visible channels and values

Phase 3A: BFS Walk of Ascent Rewrite Graph
├── queue ← [(initial_id, [])]          // BFS frontier
├── visited ← {initial_id}
│
├── WHILE queue not empty:
│     (current_id, path) ← queue.pop_front()
│     IF all_terms[current_id].is_normal_form:
│         path_to_normal_form ← path ++ [current_id]
│         BREAK
│     IF path.len() ≥ max_steps:
│         CONTINUE                       // bound search depth
│     FOR rw in results.rewrites_from(current_id):
│         IF rw.to_id not in visited:
│             visited.insert(rw.to_id)
│             queue.push((rw.to_id, path ++ [current_id]))
│             coverage.record_rule(rw.rule_name)
│
├── FOR each step in path_to_normal_form:
│     metrics ← TermMetrics::from_display(term)
│     tracker.record(metrics)
│     check_invariants()
│     steps.push(TraceEntry { op: "rewrite:RuleName" })
│
└── determine outcome: NormalForm | StepLimitReached | InvariantViolation

Phase 3B: Runtime Observation Outcome
├── summarize observations by channel
├── append one terminal runtime step
└── determine outcome: RuntimeObservations | InvariantViolation
```

For Ascent-shaped reports, the BFS finds the **shortest** path from the initial
term to any normal form in the rewrite graph. This is important: the Ascent
engine computes all possible rewrites to saturation, producing a graph that may
contain multiple paths to the same normal form. BFS ensures the trace records
the most direct path.

For Dovetail report-shaped and observation-shaped reports, there is no Ascent
rewrite graph to walk. The simulation records the backend, artifact, report or
observation summary, and terminal runtime outcome. A normal-form invariant
requested against either shape fails explicitly because checked reports and
runtime observations are not normal-form graph evidence.

### Trampoline-Style Rewriting

The rewrite graph walk uses iterative BFS with a `VecDeque` work queue, not recursion. The path to each frontier node is carried explicitly in the queue entry as a `Vec<u64>` of term IDs. This avoids stack overflow on deep rewrite chains (which can occur with languages like Rholang where a single `PPar` composition may produce dozens of intermediate rewrites).

### Normal Form as First-Class Concept

Normal form is the central graph outcome for Ascent-shaped reports. A term is
in normal form when no further rewrite rules apply to it; Ascent-shaped reports
mark such terms via `is_normal_form` in `TermInfo`. The simulation framework
treats normal-form reachability as a core property when a rewrite graph is
available:

- The `NormalFormReachable` invariant explicitly checks it (see [invariants.md](invariants.md))
- The `TraceOutcome` enum has a dedicated `NormalForm` variant
- The `check_trace_ltl()` temporal checker provides an `IsNormalForm` atomic proposition for LTL formulas like `F(normal_form)` ("eventually, normal form is reached")

Rho/default-backend observation reports instead use
`TraceOutcome::RuntimeObservations`. That outcome is terminal runtime evidence,
not a normal-form graph claim.

## Seed Persistence and Regression Files

Each `SimulationFailure` records:

```rust
pub struct SimulationFailure {
    pub seed: String,    // e.g., "case_42"
    pub input: String,   // the (possibly shrunk) input that triggers the failure
    pub trace: ExecutionTrace,
    pub error: String,
}
```

The `seed` field identifies the test case within the campaign. Combined with the campaign-level seed in `SimulationConfig`, this provides complete reproducibility.

For regression testing, the minimal failing inputs can be saved to a file and replayed:

```rust
for failure in &results.failures {
    // Save to regression file
    write!(file, "{}\n", failure.input)?;
}

// Later, replay:
for line in regression_file.lines() {
    let result = runner.run_to_normal_form(&line);
    assert!(result.is_ok(), "Regression failure: {}", line);
}
```

## JSONL Trace Format Specification

When `trace_output` is set to `TraceOutputFormat::Jsonl { path }`, each simulation run produces a JSONL file (one JSON object per line). The format is:

### Line 1: Header

```json
{"type":"header","seed":"case_0","language":"Calculator","total_steps":5}
```

### Lines 2..N+1: Steps

```json
{"type":"step","step_index":0,"term_display":"(AddInt 3 5)","operation":"parse","metrics":{"node_count":3,"depth":1,"structural_fingerprint":12345}}
{"type":"step","step_index":1,"term_display":"8","operation":"rewrite:fold_AddInt","metrics":{"node_count":1,"depth":0,"structural_fingerprint":67890}}
```

### Line N+2: Outcome

```json
{"type":"outcome","outcome":{"NormalForm":{"term":"8","steps":2}}}
```

Possible outcome variants:

| Variant              | Fields                         | Meaning                                |
|----------------------|--------------------------------|----------------------------------------|
| `NormalForm`         | `term`, `steps`                | Rewriting terminated successfully      |
| `StepLimitReached`   | `final_term`                   | Max steps exceeded without normal form |
| `InvariantViolation` | `step`, `invariant`, `message` | An invariant was violated              |
| `RuntimeObservations` | `backend`, `artifact`, `channels`, `values`, `summary` | Selected runtime backend produced observations |
| `Error`              | `message`                      | Parse or selected-backend error        |

### Line N+3 (optional): Morphology

```json
{"type":"morphology","summary":{"total_steps":2,"min_nodes":1,"max_nodes":3,"mean_nodes":2.0,"min_depth":0,"max_depth":1,"mean_depth":0.5,"distinct_shapes":2,"alerts":[]}}
```

### Reading Traces Back

The `read_trace_jsonl(path)` function parses the JSONL format back into an `ExecutionTrace` struct, enabling post-hoc analysis:

```rust
let trace = mettail_simulation::trace::read_trace_jsonl(&path)?;
println!("Language: {}, Steps: {}", trace.language, trace.steps.len());
match &trace.outcome {
    TraceOutcome::NormalForm { term, steps } => { /* ... */ }
    TraceOutcome::InvariantViolation { invariant, message, .. } => { /* ... */ }
    // ...
}
```

## CampaignResults

The `CampaignResults` struct aggregates outcomes across all test cases:

```rust
pub struct CampaignResults {
    pub total_cases: usize,
    pub passed: usize,
    pub failed: usize,
    pub failures: Vec<SimulationFailure>,
    pub coverage: RuleCoverage,
    pub aggregate_morphology: Option<MorphologySummary>,
}
```

The `Display` implementation provides a human-readable summary:

```
Campaign: 100 total, 97 passed, 3 failed
Failures:
  [0] seed=case_17, input="(PPar {(PNew ^x.(PZero))})", error=Invariant 'BoundedDepth' violated: ...
  [1] seed=case_43, input="(PDrop (NQuote (PZero)))", error=Normal form not reached after 1000 steps
  [2] seed=case_89, input="...", error=Parse error: ...
Coverage: 8/12 rules covered (66.7%), 142 total firings
```
