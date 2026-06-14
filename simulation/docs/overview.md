# MeTTaIL Simulation Framework: Architecture Overview

## What Is It?

The MeTTaIL simulation framework (`mettail-simulation`) is a property-based testing and analysis infrastructure for languages defined in the MeTTaIL system. It provides automated term generation, rewrite-pipeline simulation, invariant checking, morphology tracking, temporal property verification, model-based testing, coverage-guided generation, and a suite of algebraic abstractions (semirings, automata) for formal analysis of language behavior.

The framework answers a fundamental question: **does my language definition behave correctly across the space of all possible input terms?** Rather than checking a handful of hand-written test cases, the simulation framework generates thousands of random terms, runs each through the full parse → rewrite → normal-form pipeline, and checks a battery of invariants at every step.

## Why Was It Built?

MeTTaIL languages are defined declaratively: type categories, term constructors, equations (structural congruences), and rewrite rules. A single language definition can produce hundreds of rewrite rules (including automatically generated congruence rules). Testing such a language by hand is infeasible. The simulation framework automates this, drawing on three intellectual traditions:

1. **Property-based testing** (Claessen and Hughes (2000)): generate random inputs, check properties, shrink failures to minimal reproducers.
2. **Model checking** (Vardi and Wolper (1986), Pnueli (1977)): verify temporal properties (liveness, safety) over execution traces using automata-theoretic methods.
3. **Weighted automata theory** (Mohri (2002)): use semiring-weighted automata to track quantitative properties (costs, probabilities, resource consumption) alongside qualitative correctness.

## How Everything Connects

```
┌───────────────────────────────────────────────────────────────────────────────┐
│                          mettail-prattail (upstream)                          │
│  ┌────────────────┐  ┌──────────────┐  ┌──────────────┐  ┌─────────────────┐  │
│  │  Semiring      │  │  SemiringRef │  │  PetriNet    │  │ BuchiAutomaton  │  │
│  │  TropicalWeight│  │  (no Copy)   │  │  Marking     │  │ LTL parser      │  │
│  └────────┬───────┘  └──────┬───────┘  └──────┬───────┘  └────────┬────────┘  │
└───────────┼─────────────────┼─────────────────┼───────────────────┼───────────┘
            │                 │                 │                   │
            ▼                 ▼                 ▼                   ▼
┌───────────────────────────────────────────────────────────────────────────────┐
│                        mettail-simulation (this crate)                        │
│                                                                               │
│  ┌─ semiring/ ────────────────────────────────┐                               │
│  │  ExpectationWeight  (f64, f64)  Semiring   │                               │
│  │  ParikhWeight<D>    [u64; D]    Semiring   │                               │
│  │  StreamingWeight    Welford     Semiring   │                               │
│  │  FreeWeight         AST         SemiringRef│                               │
│  └────────────────────────────────────────────┘                               │
│                                                                               │
│  ┌─ automata ─────────────────────────────────┐                               │
│  │  StochasticPetriNet  ─── Gillespie SSA     │                               │
│  │  MDP                 ─── Value iteration   │                               │
│  │  ParikhAutomaton<D>  ─── Semilinear sets   │                               │
│  │  StreamingMonitor    ─── Real-time alerts  │                               │
│  └────────────────────────────────────────────┘                               │
│                                                                               │
│  ┌─ simulation core ───────────────────────────────────────────────────────┐  │
│  │                                                                         │  │
│  │  ┌──────────────────┐     ┌──────────────────┐                          │  │
│  │  │ SimulationRunner │────▶│  run_to_normal_  │                          │  │
│  │  │  .run_campaign() │     │  form(input)     │                          │  │
│  │  └────────┬─────────┘     └──────┬───────────┘                          │  │
│  │           │                      │                                      │  │
│  │           ▼                      ▼                                      │  │
│  │  ┌────────────────┐  ┌──────────────────────┐  ┌──────────────────────┐ │  │
│  │  │ CampaignResults│  │   ExecutionTrace     │  │  Invariant           │ │  │
│  │  │  .failures[]   │  │   .steps[]           │  │  .check()            │ │  │
│  │  │  .coverage     │  │   .outcome           │  │  BoundedSize         │ │  │
│  │  │  .morphology   │  │   .morphology        │  │  BoundedDepth        │ │  │
│  │  └────────────────┘  └──────────────────────┘  │  AlwaysParseable     │ │  │
│  │                                                │  NormalFormReachable │ │  │
│  │  ┌──────────────────┐  ┌──────────────────┐    └──────────────────────┘ │  │
│  │  │ MorphologyTracker│  │ TermMetrics      │                             │  │
│  │  │  .record()       │  │  .node_count     │                             │  │
│  │  │  .summary()      │  │  .depth          │                             │  │
│  │  │  .check_trends() │  │  .fingerprint    │                             │  │
│  │  └──────────────────┘  └──────────────────┘                             │  │
│  │                                                                         │  │
│  │  ┌──────────────────────┐  ┌──────────────────────────────────┐         │  │
│  │  │ SimulationCoverage   │  │ LanguageStateMachine             │         │  │
│  │  │  .rule_firings       │  │  .categories                     │         │  │
│  │  │  .constructor_hits   │  │  .rewrite_rules                  │         │  │
│  │  │  .coverage_pct()     │  │  .arb_model_ops() → proptest     │         │  │
│  │  └──────────────────────┘  └──────────────────────────────────┘         │  │
│  │                                                                         │  │
│  │  ┌──────────────────────────────────────────────────────────┐           │  │
│  │  │ check_trace_ltl(trace, formula, propositions)            │           │  │
│  │  │  → LtlCheckResult::Satisfied | Violated | ParseError     │           │  │
│  │  └──────────────────────────────────────────────────────────┘           │  │
│  └─────────────────────────────────────────────────────────────────────────┘  │
└───────────────────────────────────────────────────────────────────────────────┘
```

## Module Map

| Module                  | File                      | Purpose                                               |
|-------------------------|---------------------------|-------------------------------------------------------|
| `semiring::expectation` | `semiring/expectation.rs` | (weight, expected_cost) via logsumexp                 |
| `semiring::parikh`      | `semiring/parikh.rs`      | `[u64; D]` component-wise max / add                   |
| `semiring::streaming`   | `semiring/streaming.rs`   | Welford's online statistics                           |
| `semiring::free`        | `semiring/free.rs`        | Symbolic AST (SemiringRef)                            |
| `stochastic_petri`      | `stochastic_petri.rs`     | Rate-parameterized Petri nets + Gillespie SSA         |
| `mdp`                   | `mdp.rs`                  | MDP with value iteration + policy extraction          |
| `parikh_automaton`      | `parikh_automaton.rs`     | Parikh automaton + semilinear sets                    |
| `streaming_automaton`   | `streaming_automaton.rs`  | StreamingMonitor + windowed/aggregate monitors        |
| `runner`                | `runner.rs`               | SimulationRunner for property-based testing campaigns |
| `step`                  | `step.rs`                 | SimStep, SimOperation step types                      |
| `trace`                 | `trace.rs`                | ExecutionTrace with JSONL serialization               |
| `invariant`             | `invariant.rs`            | Invariant trait + built-in invariants                 |
| `morphology`            | `morphology.rs`           | TermMetrics + MorphologyTracker                       |
| `results`               | `results.rs`              | CampaignResults + SimulationFailure                   |
| `model`                 | `model.rs`                | LanguageStateMachine + ModelOp + proptest strategies  |
| `coverage`              | `coverage.rs`             | SimulationCoverage + coverage_from_ascent             |
| `temporal`              | `temporal.rs`             | LTL checking over traces                              |

## Three Execution Modes

### 1. `cargo test` (Unit and Integration Tests)

Every module contains `#[cfg(test)]` unit tests. These verify individual components in isolation using mock languages (e.g., `MockLanguage` in the invariant tests, `CalculatorStubMetadata` and `RhoCalcStubMetadata` in the model tests). Running `cargo test -p mettail-simulation` exercises the full test suite.

The generated test files under `languages/tests/gen_*.rs` use the tape-based proptest strategies (see [strategies.md](strategies.md)) to generate random terms for each defined language and run them through the simulation pipeline.

### 2. CLI (Command-Line Interface)

The `SimulationRunner` can be instantiated from a command-line tool that:
- Selects a language by name
- Configures campaign parameters (number of cases, seed, max steps)
- Writes JSONL traces to disk for post-hoc analysis
- Prints a campaign summary including pass/fail counts and coverage

### 3. Library API (Programmatic Use)

```rust
use mettail_simulation::runner::{SimulationConfig, SimulationRunner};
use mettail_simulation::invariant::{BoundedSize, BoundedDepth, AlwaysParseable};

let config = SimulationConfig {
    max_steps: 500,
    proptest_cases: 200,
    invariants: vec![
        Box::new(BoundedSize { max_nodes: 1000 }),
        Box::new(BoundedDepth { max_depth: 30 }),
        Box::new(AlwaysParseable),
    ],
    ..Default::default()
};

let mut runner = SimulationRunner::new(&my_language, config);
let results = runner.run_campaign(my_input_strategy);

if results.is_success() {
    println!("All {} cases passed. Coverage: {}", results.total_cases, results.coverage);
} else {
    for failure in &results.failures {
        println!("FAIL: seed={}, input={:?}", failure.seed, failure.input);
        println!("  Error: {}", failure.error);
    }
}
```

## Data Flow

The simulation pipeline processes each test case through the following stages:

```
   proptest strategy
         │
         ▼
   ┌─────────────┐
   │  Generate   │  proptest generates a Vec<u8> "instruction tape"
   │  input      │  TapeReader interprets it into a term string
   └──────┬──────┘
          │ input: String
          ▼
   ┌─────────────┐
   │  Parse      │  language.parse_term(input) → Term
   │             │  TermMetrics computed from display string
   └──────┬──────┘  Invariants checked
          │ term: Box<dyn Term>
          ▼
   ┌─────────────┐
   │  Backend    │  language.run_default_backend_report(term)
   │  Report     │  RuntimeBackendReport from selected backend
   └──────┬──────┘
          │ Ascent graph or runtime observations
          ▼
   ┌─────────────┐
   │ Interpret   │  Ascent: BFS from initial term to normal form
   │ Report      │  Observations: terminal runtime-observation outcome
   │             │  Records observable steps and morphology metrics
   └──────┬──────┘
          │
          ▼
   ┌─────────────┐
   │  Outcome    │  NormalForm | StepLimitReached | InvariantViolation | Error
   │  + Trace    │  ExecutionTrace with full step history
   └──────┬──────┘
          │
          ▼
   ┌─────────────┐
   │  Campaign   │  CampaignResults aggregates all cases
   │  Aggregation│  Coverage, morphology summary, failures
   └─────────────┘
```

## Design Principles

**Fail-slow.** The campaign runner collects all failures rather than stopping at the first. This produces a complete picture of the failure landscape, enabling developers to identify patterns (e.g., all failures involve the same constructor, or all failures occur beyond depth 20).

**Deterministic replay.** Every test case records its seed. Given the same seed and the same language definition, the simulation reproduces exactly the same behavior. Seeds are 32-byte ChaCha RNG states.

**Trampoline-style iteration.** All potentially deep traversals (rewrite graph BFS, expression simplification, Parikh automaton simulation) use explicit work stacks rather than recursion, preventing stack overflow on pathological inputs.

**Language-agnostic metrics.** Term metrics (node count, depth, structural fingerprint) are computed from the display string representation, requiring no language-specific AST access. This makes the morphology tracker and invariant system work uniformly across all MeTTaIL languages.

## References

- Claessen, K. and Hughes, J. (2000). "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs." ACM SIGPLAN Notices.
- Eisner, J. (2002). "Parameter Estimation for Probabilistic Finite-State Transducers." ACL.
- Gillespie, D.T. (1977). "Exact Stochastic Simulation of Coupled Chemical Reactions." Journal of Physical Chemistry.
- Mohri, M. (2002). "Semiring Frameworks and Algorithms for Shortest-Distance Problems." Journal of Automata, Languages and Combinatorics.
- Parikh, R.J. (1966). "On Context-Free Languages." Journal of the ACM.
- Pnueli, A. (1977). "The Temporal Logic of Programs." FOCS.
- Puterman, M.L. (1994). Markov Decision Processes: Discrete Stochastic Dynamic Programming. Wiley.
- Vardi, M.Y. and Wolper, P. (1986). "An Automata-Theoretic Approach to Automatic Program Verification." LICS.
- Welford, B.P. (1962). "Note on a Method for Calculating Corrected Sums of Squares and Products." Technometrics.
