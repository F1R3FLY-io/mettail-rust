//! MeTTaIL Simulation Infrastructure
//!
//! This crate provides simulation and analysis tools for MeTTaIL:
//!
//! - **New semirings**: `ExpectationWeight`, `ParikhWeight`, `StreamingWeight`, `FreeWeight`
//! - **Stochastic Petri nets**: rate-parameterized transitions with Gillespie SSA
//! - **Markov Decision Processes**: states, actions, probabilistic outcomes, value iteration
//! - **Parikh automata**: NFA with Parikh-image transitions, semilinear set projection
//! - **Streaming automata**: online monitoring with windowed and aggregate monitors
//! - **Simulation runner**: property-based simulation with invariant checking and morphology tracking
//! - **Model-based testing**: state machine derivation from language metadata + proptest strategies
//! - **Coverage-guided generation**: rule/constructor coverage tracking and gap analysis
//! - **Temporal property checking**: standalone LTL/Büchi checking over simulation traces
//! - **Guard-aware simulation (Sim-C, Sim-D)**: the simulator ingests the
//!   `guards { }` block metadata declared in each language. The
//!   `LanguageStateMachine::from_metadata` entry point reads theories,
//!   channels, join patterns, built-in predicates, and connectives directly
//!   from the `LanguageMetadata` trait, exposing them as `ModelTheory`,
//!   `ModelChannel`, `ModelJoinPattern`, `ModelBuiltinPredicate`, and
//!   `ModelConnective` vectors on the state machine. The
//!   `GuardSatisfaction` invariant in [`invariant`] and the
//!   `StochasticPetriNet::from_channel_metadata` helper in
//!   [`stochastic_petri`] consume this data to build guard-aware
//!   simulation runs. Languages without a `guards { }` block produce
//!   empty guard vectors — the ingestion is fully backward compatible.
//!   See [`docs/design/dispatch/predicate-dispatch-integration.md`](../../../docs/design/dispatch/predicate-dispatch-integration.md)
//!   for the full integration story.
//!
//! ## Architecture
//!
//! ```text
//! mettail-prattail (Semiring, SemiringRef, PetriNet)
//!       │
//!       ▼
//! mettail-simulation
//!   ├── semiring/         — 4 new semiring types
//!   │   ├── expectation   — (weight, expected_cost) via logsumexp
//!   │   ├── parikh        — [u64; D] component-wise max / add
//!   │   ├── streaming     — Welford's online statistics
//!   │   └── free          — symbolic AST (SemiringRef, not Copy)
//!   ├── stochastic_petri  — rate-parameterized Petri nets + Gillespie SSA
//!   ├── mdp               — MDP with value iteration + policy extraction
//!   ├── parikh_automaton   — Parikh automaton + semilinear sets
//!   ├── streaming_automaton — StreamingMonitor + windowed/aggregate monitors
//!   ├── runner             — SimulationRunner for property-based testing campaigns
//!   ├── step               — SimStep, SimOperation step types
//!   ├── trace              — ExecutionTrace with JSONL serialization
//!   ├── invariant          — Invariant trait + built-in invariants
//!   ├── morphology         — TermMetrics + MorphologyTracker
//!   ├── results            — CampaignResults + SimulationFailure
//!   ├── model              — LanguageStateMachine + ModelOp + proptest strategies
//!   ├── coverage           — SimulationCoverage + coverage_from_ascent
//!   └── temporal           — LTL checking over traces (AtomicProposition, check_trace_ltl)
//! ```

pub mod semiring;
pub mod stochastic_petri;
pub mod mdp;
pub mod parikh_automaton;
pub mod streaming_automaton;

pub mod step;
pub mod trace;
pub mod invariant;
pub mod morphology;
pub mod results;
pub mod runner;

pub mod model;
pub mod coverage;
pub mod temporal;
