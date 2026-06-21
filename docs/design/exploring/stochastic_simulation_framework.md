# Public Strategies Library + Stochastic Simulation Framework

## Context

The tape-based proptest strategies (`arb_int`, `arb_proc`, etc.) are powerful but trapped inside test files as private functions. Exposing them as a public library enables:
1. External crates to generate random well-formed terms for any MeTTaIL language
2. Stochastic simulation for long-term morphological testing — reproducible, shrinkable
3. Coverage-guided fuzzing, temporal property checking, and model-based testing

## Phase 1: Public Strategy Exposure

### Approach
Generate strategies into the `language!` macro expansion itself as a `pub mod strategies { }` sub-module. `proptest` becomes an optional dependency of `languages` behind a `strategies` feature.

### Changes

**`languages/Cargo.toml`**: Add optional proptest dependency
```toml
[features]
strategies = ["proptest"]

[dependencies]
proptest = { version = "1", optional = true }
```

**`macros/src/gen/test_gen/strategies.rs`**: Add `generate_public_strategies(language) -> TokenStream` that emits `pub fn arb_{cat}()`, `pub struct TapeReader`, `pub enum AnyTerm`, `pub enum BuildTask`, `pub fn build_{cat}_from_tape()` — all public, wrapped in `#[cfg(feature = "strategies")]`.

**`macros/src/lib.rs`**: Emit the public strategies module as part of the `language!` expansion:
```rust
#[cfg(feature = "strategies")]
pub mod strategies {
    use super::*;
    // ... generated public strategy code
}
```

**`macros/src/gen/test_gen/mod.rs`**: When generating test files, detect if `strategies` feature exists and import from the public module instead of re-generating inline.

**External usage**:
```rust
use mettail_languages::calculator::strategies::arb_int;
use proptest::prelude::*;

proptest! {
    fn my_test(term in arb_int(5)) { /* ... */ }
}
```

## Phase 2: Simulation Crate

### New crate: `simulation`

```
simulation/
  Cargo.toml
  src/
    lib.rs
    runner.rs          — SimulationRunner wrapping proptest TestRunner
    step.rs            — SimStep, SimOperation enum
    trace.rs           — ExecutionTrace, TraceEntry (serde-serializable)
    invariant.rs       — Invariant trait + built-ins (BoundedSize, AlwaysParseable, etc.)
    morphology.rs      — TermMetrics, MorphologyTracker, drift/explosion detection
    model.rs           — LanguageStateMachine for model-based testing
    coverage.rs        — CoverageGuidedCampaign
    temporal.rs        — LTL property checking over simulation traces
    semiring/
      mod.rs
      expectation.rs   — ExpectationWeight(probability, expected_cost)
      parikh.rs        — ParikhWeight<D> counting rule firings per trace
      streaming.rs     — StreamingWeight for online mean/variance/min/max
      free.rs          — FreeWeight symbolic trace recording
    stochastic_petri.rs — StochasticPetriNet with Gillespie SSA
    mdp.rs             — Markov Decision Processes for adversarial simulation
    parikh_automaton.rs — Parikh image automaton for coverage completeness
    streaming_automaton.rs — Streaming monitors for real-time invariant checking
```

### Core API

```rust
pub struct SimulationRunner<'a> {
    language: &'a dyn Language,
    config: SimulationConfig,
    runner: TestRunner,
}

impl SimulationRunner {
    /// Run many simulations. proptest generates initial terms + operation sequences.
    /// Invariants checked after each step. Failures shrunk automatically.
    pub fn run_campaign<S, O>(
        &mut self,
        initial_strategy: S,
        step_strategy: impl Fn(&SimState) -> O,
    ) -> Result<CampaignResults, SimulationFailure>;
}
```

**Execution flow**: Generate initial term → apply operations (rewrite, parse, normalize, fork) → check invariants → record morphology → check LTL → repeat. On failure, proptest shrinks the operation sequence to minimal reproducer.

### Invariants (checked after each step)
- `BoundedSize { max_nodes }` — term doesn't explode
- `BoundedDepth { max_depth }` — nesting doesn't explode
- `AlwaysParseable` — display(term) always parses back
- `MonotonicProgress` — rewrites always reduce some metric
- `WellTyped` — term remains in its declared category

### Morphology Tracking
- **TermMetrics**: node_count, depth, free_var_count, constructor_histogram, structural_fingerprint
- **Alerts**: StructuralDrift (term shape changed), ComplexityExplosion (super-linear growth), NonConvergence (no normal form within bound), FingerprintShift (constructor distribution changed)
- **Trends**: Stable, Increasing, Decreasing, Oscillating (via linear regression + FFT on windowed metrics)

### Trace Output
JSONL (JSON Lines) format — one JSON object per line for streaming efficiency:
```jsonl
{"type":"header","seed":"abc123...","language":"Calculator","config":{"max_steps":1000,"max_depth":5}}
{"type":"step","index":0,"term":"1 + 2","operation":"Rewrite","metrics":{"size":3,"depth":2}}
{"type":"step","index":1,"term":"3","operation":"Rewrite","metrics":{"size":1,"depth":1}}
{"type":"outcome","kind":"NormalForm","term":"3","steps":1}
{"type":"morphology","mean_size":2.0,"max_size":3,"trend":"Decreasing","alerts":[]}
```

Benefits of JSONL over JSON:
- **Streaming writes**: append per step, no memory buffering of full trace
- **Crash resilience**: partial traces are valid (each line self-contained)
- **Partial reads**: `head -n 100 trace.jsonl` for first 100 steps
- **Tool-friendly**: `grep`, `jq`, `wc -l` work directly
- **Parallel processing**: split by line for concurrent analysis

## Phase 3: Stateful Model-Based Testing

`LanguageStateMachine::from_metadata()` derives a state machine from the language spec:
- States = equivalence classes of terms
- Transitions = rewrite rules
- proptest generates `Vec<ModelOp>` sequences (ApplyRewrite, RunAscent, CheckEquivalence, Normalize)
- Shrinking removes operations → minimal failing sequence

## Phase 4: Coverage-Guided Generation

`CoverageGuidedCampaign` iterates:
1. Generate terms with current strategy
2. Run simulation, collect rule firing coverage
3. Adjust strategy weights — boost uncovered rules
4. Regenerate with biased strategies
5. Repeat until coverage plateau

Uses constructor weights from `PipelineAnalysis` as initial bias, then refines based on observed coverage.

## Phase 5: Temporal Property Simulation

`TemporalSimulation` integrates existing LTL/Büchi infrastructure:
- User specifies LTL formulas: `"F(normal_form)"`, `"G(well_typed)"`, `"G(!deadlock)"`
- Simulation generates execution traces
- Each trace compiled to a Büchi system automaton
- Negation-intersection-emptiness pipeline checks property
- Violations shrunk by proptest

Uses existing `prattail::ltl::check_ltl_property()` and `prattail::buchi` intersection/emptiness.

## Phase 6: New Semirings

### ExpectationWeight
`(probability: f64, expected_cost: f64)` — track expected resource consumption during simulation. Semiring: (logsumexp × weighted_mix, + × +).

### ParikhWeight<D>
`[u64; D]` counting rule firings per trace. Semiring: (component-wise max, component-wise add). Detects unbalanced rule usage.

### StreamingWeight
Online mean/variance/min/max via Welford's algorithm. No full trace materialization needed for long simulations. Parallel merge for concurrent traces.

### FreeWeight
Symbolic trace: `FreeExpr` AST recording the algebraic structure of the computation. Most general provenance — subsumes `N[X]` polynomial provenance.

Requires a `SemiringRef` trait (Clone-based, not Copy) since FreeExpr is heap-allocated. All existing `Semiring: Copy` types auto-implement `SemiringRef`.

### Stochastic Petri Nets
Extend existing `petri.rs` with exponential firing rates. Gillespie's SSA for probabilistic simulation of concurrent systems. Each rewrite rule becomes a transition with a rate parameter derived from constructor weights (WFST tropical weights → firing rates).

### Markov Decision Processes (MDP)
Extend `probabilistic.rs` with non-deterministic choice points. In an MDP, some transitions are probabilistic (environment/scheduler) and some are adversarial (non-deterministic). For simulation:
- **Probabilistic transitions**: rewrite rule selection weighted by constructor frequency
- **Adversarial transitions**: scheduler decisions for concurrent terms (which process runs next)
- **Policy**: proptest generates the adversarial policy (sequence of non-deterministic choices), enabling adversarial testing — the simulator actively tries to find the worst-case scheduling
- **Value iteration**: compute expected reward (e.g., expected steps to normal form) under optimal/worst-case policy
- **Strategy synthesis**: derive a proptest strategy that maximizes the probability of hitting a bug (adversary tries to break invariants)

Implementation: `simulation/src/mdp.rs` with `MdpState`, `MdpTransition { action, probabilistic_outcomes }`, `MdpPolicy` (generated by proptest).

### Parikh Image Automaton
Beyond the ParikhWeight semiring (which counts rule firings along individual paths), a full **Parikh image automaton** tracks the set of ALL achievable Parikh vectors across all execution paths. This is a finite automaton whose language is the set of valid rule-firing histograms.

Uses:
- **Coverage completeness**: is there an execution path that fires every rule at least once? (Parikh vector with all components > 0)
- **Balance checking**: are send/receive operations balanced across all paths? (Parikh components for send and receive equal)
- **Semilinear set analysis**: the Parikh image of a CFL is semilinear (Parikh's theorem) — compute the linear set representation to characterize all possible rule-firing patterns

Implementation: `simulation/src/parikh_automaton.rs` wrapping the existing NFA infrastructure with ParikhWeight transitions. Compute the Parikh image via the standard projection construction (NFA → Parikh NFA → semilinear set).

### Streaming/Online Automata
Beyond the StreamingWeight semiring, a full **streaming automaton** processes trace events one at a time without buffering, maintaining a finite state that summarizes the trace seen so far. Uses:
- **Real-time monitoring**: check invariants during simulation without waiting for the trace to complete
- **Memory-bounded**: fixed memory regardless of trace length (critical for long-running simulations)
- **Composable**: multiple streaming automata run in parallel over the same trace, each monitoring a different property

Implementation: `simulation/src/streaming_automaton.rs` with `StreamingMonitor` trait, `WindowedMonitor` (sliding window), `AggregateMonitor` (running statistics). Integrates with the simulation runner's step-by-step execution loop.

## Implementation Order

| Phase | What | Depends On |
|---|---|---|
| 1 | Public strategies | — |
| 6 | New semirings | — (independent) |
| 2 | Simulation crate + morphology | Phase 1 |
| 3 | Model-based testing | Phase 2 |
| 4 | Coverage-guided | Phase 2 |
| 5 | Temporal properties | Phase 2 |

## Execution Modes

The simulation runs in three complementary modes sharing the same core `SimulationRunner`:

### 1. `cargo test` integration (CI regression)
Short simulations generated as `#[test]` functions in the `gen_*.rs` test files. For each language with rewrite rules, generate:
- `fn sim_{lang}_normal_form_reachability()` — 100-step, 200-case simulation verifying all generated terms reach normal form
- `fn sim_{lang}_roundtrip_under_rewrite()` — rewrite → display → parse roundtrip holds after each step
- `fn sim_{lang}_morphology_bounded()` — term size doesn't explode during rewriting
- `fn sim_{lang}_eval_determinism()` — same term always rewrites to same normal form

These run with `cargo test` and `cargo nextest run`. Fast (seconds), catches regressions.

### 2. Per-language CLI binary (`simulate_{lang}`)
The `language!` macro generates a per-language simulation binary alongside the test file. Each binary only compiles and links its language — fast compilation, small binary, independently distributable. External crates defining custom languages via `language!` automatically get their own binary.

Generated at: `languages/src/bin/simulate_{lang}.rs` (or as `[[bin]]` targets in Cargo.toml).

```
simulate_calculator [OPTIONS]

  -s, --steps <N>            Max steps per trace (default: 10000)
  -c, --cases <N>            Number of simulation runs (default: 10000)
      --seed <SEED>          Deterministic seed for reproducibility (if omitted, a random seed
                             is generated, reported in output, and written to the JSONL trace
                             header so any failure can be reproduced exactly)
      --ltl <FORMULA>        Linear Temporal Logic property to check (repeatable).
                             Operators: F (eventually), G (always), U (until), X (next), ! (not).
                             Atoms: normal_form, well_typed, bounded_size(N), contains(CTOR).
                             Examples: "F(normal_form)"         — rewriting eventually terminates
                                       "G(well_typed)"          — type preserved at every step
                                       "G(!contains(Err))"      — Err constructor never appears
                                       "F(bounded_size(10))"    — term eventually becomes small
      --invariant <NAME>     Built-in invariant (repeatable): bounded_size, bounded_depth, always_parseable, monotonic_progress, well_typed
  -o, --output <PATH>        JSONL trace output path
      --coverage             Enable coverage-guided generation
      --morphology           Enable morphology tracking
      --adversarial          Enable MDP adversarial scheduling
  -v, --verbose              Per-step output
```

For overnight/weekend simulation campaigns. Outputs JSONL traces. Failures include shrunk minimal reproducers. Each binary is self-contained — no language registry needed.

**Seed persistence and regression**: On failure, the failing seed is saved to `simulate_{lang}.regressions` (same pattern as proptest's `.proptest-regressions` files). On subsequent runs, the runner loads persisted seeds and re-runs them FIRST before generating new random cases. This provides:
- **Reproduction during debugging**: same seed → same failure, deterministically
- **Regression prevention post-fix**: after fixing the bug, the seed runs as a regression test. Check the regressions file into version control so CI continuously verifies the fix holds.

### 3. Programmatic library API
External crates construct and run simulations:
```rust
use mettail_simulation::{SimulationRunner, SimulationConfig};
use mettail_simulation::invariant::{BoundedSize, AlwaysParseable};
use mettail_languages::calculator::CalculatorLanguage;
use mettail_languages::calculator::strategies::arb_int;

let mut runner = SimulationRunner::new(
    &CalculatorLanguage,
    SimulationConfig {
        max_steps: 1000,
        proptest_config: Config::with_cases(5000),
        invariants: vec![Box::new(BoundedSize { max_nodes: 1000 })],
        ltl_properties: vec!["F(normal_form)".into()],
        track_morphology: true,
        trace_output: TraceOutputFormat::Jsonl { path: "traces.jsonl".into() },
        ..Default::default()
    },
);

let results = runner.run_campaign(
    arb_int(5),
    |state| arb_rewrite_choice(state),
)?;
```

For CI pipelines, custom harnesses, research tools.

### Normal Form as First-Class Concept

The simulation runner natively supports normal form detection — no LTL formula needed:
- After each rewrite step, check if the result term has no applicable rewrites (`AscentResults::normal_forms()` is non-empty and contains the current term)
- Track steps-to-normal-form as a metric
- Alert on non-convergence (step limit exceeded without reaching normal form)
- `SimulationRunner::run_to_normal_form()` convenience method that keeps rewriting until normal form or step limit

LTL `F(normal_form)` is available for more complex temporal assertions (e.g., "eventually normal form AND the normal form satisfies predicate P"), but simple normal form testing is built-in.

## Verification

- `cargo test -p languages --features strategies` — public strategies compile and work
- `cargo test -p simulation` — simulation framework tests pass
- External crate can `use mettail_languages::calculator::strategies::arb_int`
- Simulation applies to ALL `language!` specs (operates via the `Language` trait, not language-specific code)
- Simulation detects injected bugs for every language (mutate HOL code → simulation finds violation → proptest shrinks)
- Normal form reachability verified for all languages with rewrite rules
- LTL temporal properties verified across all languages
- Morphology tracker detects complexity explosion on intentionally-divergent rewrites
- Stochastic Petri net simulation runs for concurrent languages (RhoCalc, Ambient)

## Documentation

Thorough, pedagogical documentation with examples, diagrams, mathematical formulae, citations, pseudocode, and literate-style algorithm presentation. Unicode characters throughout. Each component documented with intuition, rationale, and theoretical basis.

### Documentation Files

**Test framework documentation** (in `testkit/docs/`):
- `testkit/docs/auto-generated-tests.md` — How tests are derived from `language!` specs. Covers: unit tests, equation tests, rewrite tests, proptest strategies (tape-based generation), operational semantics tests (symbolic evaluation), precedence/associativity tests, cross-category coercion tests, edge case generation. Includes the algebraic property detection algorithm (commutativity, associativity, identity detection from equation patterns).

- `testkit/docs/trampolines.md` — Why and how all recursive AST operations use iterative work-stacks. Covers: Display, Debug, Clone, Drop, PartialEq, Ord, Hash. Includes the `DisplayTask`/`DropTask`/`CloneTask`/`CmpTask`/`HashTask` enum designs, TLS pool pattern, raw pointer safety argument, re-entrancy handling.

**Simulation framework documentation** (in `simulation/docs/`):
- `simulation/docs/overview.md` — Architecture overview with diagrams showing how the simulation runner, strategies, invariants, morphology tracker, and trace output interact.

- `simulation/docs/strategies.md` — Tape-based term generation. Explains the `TapeReader → BuildTask work-stack → AnyTerm slots` pipeline. Pseudocode for the iterative builder. How proptest shrinking works (shorter tape = simpler term). How to write custom strategies.

- `simulation/docs/simulation-runner.md` — The `SimulationRunner` API. Three execution modes (cargo test, CLI, library). Configuration options. Seed persistence and regression file pattern. JSONL trace format specification.

- `simulation/docs/invariants.md` — Built-in invariants (BoundedSize, BoundedDepth, AlwaysParseable, MonotonicProgress, WellTyped) and how to write custom invariants. The `Invariant` trait with examples.

- `simulation/docs/morphology.md` — Term evolution tracking. TermMetrics computation. Drift detection (baseline comparison), complexity explosion detection (growth rate analysis), non-convergence detection, structural fingerprint tracking. Mathematical basis: linear regression for trend detection, Welford's online variance algorithm for streaming statistics.

- `simulation/docs/temporal-properties.md` — LTL model checking over simulation traces. The negation-intersection-emptiness pipeline. How Büchi automata encode ω-regular properties. Atomic propositions. Examples: `F(normal_form)`, `G(well_typed)`, `G(!deadlock)`. Citations: Vardi & Wolper (1986), Gerth et al. (1995) GPVW tableau construction.

- `simulation/docs/model-based-testing.md` — Stateful model-based testing. The `LanguageStateMachine` derived from the spec. States = terms, transitions = rewrites. proptest generates operation sequences. Shrinking finds minimal failing sequences. Citations: Claessen & Hughes (2000) QuickCheck, Arts et al. (2006) Erlang QuickCheck.

- `simulation/docs/coverage-guided.md` — Coverage-guided strategy generation. The feedback loop: generate → simulate → collect coverage → adjust weights → regenerate. Integration with parser-coverage tracking. Coverage metrics: rule firing coverage, constructor coverage, parse dispatch coverage.

**Semiring documentation** (in `prattail/docs/` or `simulation/docs/semirings/`):
- `simulation/docs/semirings/overview.md` — What semirings are and why they matter for analysis. The semiring framework: `(S, ⊕, ⊗, 0̄, 1̄)`. How weighted automata use them. Connection to dynamic programming and shortest-path algorithms. Citations: Mohri (2002) "Semiring Frameworks and Algorithms for Shortest-Distance Problems".

- `simulation/docs/semirings/expectation.md` — ExpectationWeight `(p, E[c])`. The expectation semiring for computing expected costs over probabilistic computations. Mathematical definition. Use in simulation: tracking expected resource consumption.

- `simulation/docs/semirings/parikh.md` — ParikhWeight and Parikh image automata. Parikh's theorem (1966): the Parikh image of any CFL is semilinear. How counting rule firings per trace reveals coverage imbalances. The semilinear set representation.

- `simulation/docs/semirings/streaming.md` — StreamingWeight for online aggregation. Welford's algorithm (1962) for numerically stable online variance. Parallel merge formula for concurrent traces. Memory-bounded long-running simulation.

- `simulation/docs/semirings/free.md` — FreeWeight for symbolic provenance. The free semiring as the most general semiring (universal property). How it records the algebraic structure of computations. Relationship to provenance semirings N[X]. Citations: Green et al. (2007) "Provenance Semirings".

**Automata documentation** (in `simulation/docs/automata/`):
- `simulation/docs/automata/stochastic-petri.md` — Stochastic Petri nets. Exponential firing rates. Gillespie's stochastic simulation algorithm (SSA, 1977). Chemical master equation analogy. Use for probabilistic simulation of concurrent MeTTaIL programs.

- `simulation/docs/automata/mdp.md` — Markov Decision Processes. States, actions, transition probabilities. Adversarial vs cooperative scheduling. Value iteration for optimal/worst-case analysis. How proptest generates adversarial policies. Citations: Puterman (1994) "Markov Decision Processes".

- `simulation/docs/automata/parikh-automaton.md` — Parikh image automaton construction. Projection from NFA to Parikh NFA. Semilinear set computation. Coverage completeness checking.

- `simulation/docs/automata/streaming-automaton.md` — Streaming monitors for real-time invariant checking. Sliding window monitors. Aggregate monitors. Composability of parallel monitors over shared traces.

### Documentation Style

- **Pseudocode in literate programming style**: algorithms presented as numbered steps with inline commentary explaining each step's purpose and invariants
- **Unicode**: ⊕, ⊗, 0̄, 1̄, ∀, ∃, →, ⟶, ≤, ≥, ∈, ∉, ∅, ∞, Σ, Π, λ, μ, ν, etc.
- **Mathematical formulae**: inline for definitions, display for theorems
- **Diagrams**: ASCII art for architecture, data flow, automaton structure
- **Citations**: author (year) format with full references
- **No exercises**: documentation is reference material, not a textbook
- **Each section answers**: What is it? What does it do? Why was it chosen? How does it work?

## Key Files

### New
- `simulation/Cargo.toml` + `simulation/src/*.rs` (entire new crate)
- `simulation/docs/*.md` (12+ documentation files)
- `testkit/docs/*.md` (2 documentation files)
- `prattail/src/automata/semiring.rs` — add `SemiringRef` trait
- `simulation/src/semiring/*.rs` — 4 new semirings (Expectation, Parikh, Streaming, Free)
- `simulation/src/stochastic_petri.rs` — Stochastic Petri nets with Gillespie SSA
- `simulation/src/mdp.rs` — Markov Decision Processes for adversarial testing
- `simulation/src/parikh_automaton.rs` — Parikh image automaton for coverage analysis
- `simulation/src/streaming_automaton.rs` — Streaming monitors for real-time checking

### Modified
- `macros/src/gen/test_gen/strategies.rs` — add `generate_public_strategies()`
- `macros/src/lib.rs` — emit public strategies module
- `languages/Cargo.toml` — add `strategies` feature + optional proptest
- `Cargo.toml` (workspace) — add `simulation` member
