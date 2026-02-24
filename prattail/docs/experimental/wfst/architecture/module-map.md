# WFST Module Map

**Date:** 2026-02-22

This document is a reference map of every source module that participates
in the WFST subsystem. It answers three questions for each module: which
feature tier gates it, what its public API surface is, and how it depends
on the other modules. Use it as a starting point when navigating the
source or when deciding where a new piece of WFST functionality belongs.

---

## Table of Contents

1. [Feature Tiers at a Glance](#1-feature-tiers-at-a-glance)
2. [Module Inventory](#2-module-inventory)
   - 2.1 [Always-Available Modules](#21-always-available-modules)
   - 2.2 [wfst-Gated Modules](#22-wfst-gated-modules)
   - 2.3 [wfst-log-Gated Modules](#23-wfst-log-gated-modules)
3. [Dependency Graph](#3-dependency-graph)
4. [Feature-Gate Matrix](#4-feature-gate-matrix)
5. [Public API Surface](#5-public-api-surface)

---

## 1. Feature Tiers at a Glance

PraTTaIL uses two additive feature flags to control WFST compilation.
Neither flag is enabled by default, so a plain `cargo build` compiles
only the core automata and Pratt/RD parser.

```
   ┌──────────────────────────────────────────────────────────────┐
   │  Tier 0 — no features (default)                              │
   │  Core automata · Pratt parser · RD parser · prediction sets  │
   │                                                              │
   │  ┌────────────────────────────────────────────────────────┐  │
   │  │  --features wfst                                       │  │
   │  │  + PredictionWfst · TokenLattice · RecoveryWfst        │  │
   │  │  + compose · token_id                                  │  │
   │  │                                                        │  │
   │  │  ┌──────────────────────────────────────────────────┐  │  │
   │  │  │  --features wfst-log  (implies wfst)             │  │  │
   │  │  │  + LogWeight · ForwardBackward · LogPush         │  │  │
   │  │  │  + TrainedModel · SGD training                   │  │  │
   │  │  └──────────────────────────────────────────────────┘  │  │
   │  └────────────────────────────────────────────────────────┘  │
   └──────────────────────────────────────────────────────────────┘
```

The `wfst-log` flag implies `wfst`. Any grammar feature that relies on
`LogWeight` must therefore also have access to all `wfst`-tier types.

---

## 2. Module Inventory

### 2.1 Always-Available Modules

These four modules are compiled in every build. Only specific functions
within them are feature-gated, indicated inline.

#### `automata/semiring.rs`

Algebraic foundations for weighted parsing. Defines the `Semiring` trait
and two concrete instances:

- `TropicalWeight` — `(ℝ ∪ {+∞}, min, +, +∞, 0)` — always available.
  Used for dispatch priority ordering and beam-pruning thresholds.
- `LogWeight` — `(ℝ ∪ {-∞}, log-sum-exp, +, -∞, 0)` — gated under
  `#[cfg(feature = "wfst-log")]`. Uses numerically stable log-sum-exp to
  avoid floating-point underflow when multiplying small probabilities.

631 lines, 20 tests.

#### `prediction.rs`

Computes FIRST sets, FOLLOW sets, cross-category overlap analysis, and
grammar diagnostics. The single WFST-gated function is:

- `build_dispatch_action_tables()` — `#[cfg(feature = "wfst")]` —
  extracts structured `DispatchAction` records from FIRST sets and
  overlap data. These records carry the token-to-rule mappings that
  `build_prediction_wfsts()` uses to assign initial weights.

#### `dispatch.rs`

Generates cross-category dispatch functions. The single WFST-gated
function is:

- `write_category_dispatch_weighted()` — `#[cfg(feature = "wfst")]` —
  emits a dispatch `match` arm block where handler ordering is determined
  by WFST transition weights rather than FIRST-set insertion order.

#### `pipeline.rs`

Orchestrates the full compile-time pipeline. Two private functions are
gated:

- `generate_wfst_recovery_fn()` — `#[cfg(feature = "wfst")]` — emits
  a per-category `wfst_recover_Cat()` function that evaluates all four
  repair strategies (skip, delete, insert, substitute) with full 3-tier
  context (frame kind, bracket balance, parse simulation).
- `write_trampolined_parser_recovering_wfst()` — `#[cfg(feature = "wfst")]`
  — emits the outer recovering entry point that wraps the fail-fast
  trampoline parser with a WFST-guided error catch, propagating bracket
  balance counters and nesting depth into recovery.
- `emit_prediction_wfst_static()` — `#[cfg(feature = "wfst")]` —
  serializes each `PredictionWfst` as CSR static arrays and a
  `LazyLock<PredictionWfst>` constructor in the generated code.
- `emit_recovery_wfst_static()` — `#[cfg(feature = "wfst")]` —
  serializes each `RecoveryWfst` as static sync token arrays in the
  generated code.

---

### 2.2 `wfst`-Gated Modules

These five modules are compiled only when `--features wfst` is active.

#### `wfst.rs`

The prediction engine. Builds one `PredictionWfst` per grammar category
from the dispatch action tables, drives weighted prefix dispatch in the
trampoline, and emits weighted dispatch comments into generated code.

1148 lines, 16 tests.

Key types: `WfstStateId`, `WeightedTransition`, `WfstState`,
`WeightedAction`, `PredictionWfst`, `PredictionWfstBuilder`.

Key functions: `build_prediction_wfsts()`, `generate_weighted_dispatch()`,
`PredictionWfst::from_flat()`, `PredictionWfst::with_trained_weights()`.

#### `token_id.rs`

Compact token label encoding. Maps token variant name strings (e.g.,
`"Plus"`, `"Ident"`) to `u16` identifiers for use as WFST transition
labels. Avoids string comparisons in hot paths and enables dense state
arrays.

155 lines, 4 tests.

Key types: `TokenId` (type alias for `u16`), `TokenIdMap`.

Key constants: `EPSILON_TOKEN = TokenId::MAX`.

Key functions: `TokenIdMap::from_names()`, `TokenIdMap::get()`,
`TokenIdMap::get_or_insert()`, `TokenIdMap::name()`.

#### `lattice.rs`

Weighted parse chart. Represents a token sequence as a `TokenLattice`
where each edge carries a semiring weight. Provides Viterbi shortest-path
decoding and optional beam pruning.

933 lines, 20 tests.

Key types: `TokenSource<T,S>`, `TokenLattice<T,S>`, `LatticeEdge<T,S>`,
`ViterbiPath<T,S>`.

Key functions: `viterbi_best_path()`, `viterbi_best_path_beam()`,
`linear_to_lattice()`.

`n_best_paths()` is further gated under `#[cfg(feature = "wfst-log")]`
because it uses log-probability weights for N-best ranking.

#### `recovery.rs`

Error repair engine. Constructs a `RecoveryWfst` for each grammar
category encoding the costs of skip, delete, and substitute operations.
Provides a 3-tier context model (`FrameKind`, `RecoveryContext`,
`AnnotatedSyncToken`) that captures structural position during recovery
to weight repair actions more accurately.

1840 lines, 34 tests.

Key types: `RepairAction`, `RepairResult`, `RecoveryWfst`, `FrameKind`,
`SyncSource`, `AnnotatedSyncToken`, `RecoveryContext`, `SimulationResult`,
`ParseSimulator`.

Key functions: `viterbi_recovery()`, `viterbi_recovery_beam()`,
`build_recovery_wfsts()`, `RecoveryWfst::from_flat()`,
`ParseSimulator::from_flat()`.

#### `compose.rs`

WFST composition and grammar union. Implements on-the-fly product
construction for composing prediction and recovery transducers. Also
provides `compose_languages()` for merging two `LanguageSpec` grammars
into a unified one, and `compose_many()` for composing a sequence.

1082 lines, 13 tests.

Key types: `CompositionError`, `CompositionSummary`.

Key functions: `compose_languages()`, `composition_summary()`,
`compose_many()`.

---

### 2.3 `wfst-log`-Gated Modules

These three modules require both `wfst` and `wfst-log` features.
They depend on `LogWeight` from `semiring.rs`.

#### `forward_backward.rs`

Forward-backward (Baum-Welch) algorithm for computing arc posterior
probabilities over a token lattice. Used by `training.rs` to accumulate
expected rule counts for weight re-estimation.

244 lines, 7 tests.

Key functions: `forward_scores()`, `backward_scores()`, `total_weight()`.

#### `log_push.rs`

Mohri weight pushing for WFST normalization. Pushes arc weights towards
the initial state so that the resulting WFST is in a canonical form
suitable for comparison and efficient decoding.

161 lines, 2 tests.

Key functions: `log_push_weights()`, `check_normalization()`.

#### `training.rs`

SGD and count-based weight training. Reads a corpus of parse traces,
runs forward-backward to accumulate expected counts, updates rule weights,
and serializes the result to a JSON `TrainedModel` that `pipeline.rs` can
load at compile time.

587 lines, 12 tests.

Key types: `TrainingExample`, `RuleWeights`, `TrainingStats`,
`TrainedModel`, `TrainedModelMetadata`.

Key functions: `TrainedModel::from_embedded()`, `TrainedModel::save()`,
`TrainedModel::load()`, `RuleWeights::train()`.

---

## 3. Dependency Graph

Arrows indicate "depends on" (imports types or calls functions).
Node labels in brackets indicate the feature tier: `[core]` for
always-available, `[wfst]` for `#[cfg(feature = "wfst")]`, and
`[log]` for `#[cfg(feature = "wfst-log")]`.

```
  lib.rs [core]
  ├── pipeline.rs [core] ─────────────┬──────────────────────────────────────┐
  │     │                             │                                       │
  │     ▼                             ▼                                       │
  │   prediction.rs [core] ─────────► dispatch.rs [core]                     │
  │     │  ┊                            ┊                                     │
  │     │  ┊ #[cfg(wfst)]               ┊ #[cfg(wfst)]                        │
  │     │  ▼                            ▼                                     │
  │     │  build_dispatch_         write_category_                            │
  │     │  action_tables()         dispatch_weighted()                        │
  │     │  ┊                            ┊                                     │
  │     └──╂────────────────────────────╂──► wfst.rs [wfst] ──► token_id.rs [wfst]
  │        ┊                            ┊         │                   ┊
  │        ┊                            ┊         ▼                   ┊
  │        ┊                            ┊    PredictionWfst ──────────┘
  │        ┊                            ┊         │
  │        ┊                            ┊         ▼
  │        ┊                            ┊    generate_weighted_dispatch()
  │        ┊                            ┊
  │        └────────────────────────────╂──► recovery.rs [wfst] ──► token_id.rs [wfst]
  │                                     ┊         │
  │                                     ┊         ├──► lattice.rs [wfst]
  │                                     ┊         │         │
  │                                     ┊         │         ▼
  │                                     ┊         │    semiring.rs [core/log]
  │                                     ┊         │         ┊
  │                                     ┊         │         ┊ #[cfg(wfst-log)]
  │                                     ┊         │         ▼
  │                                     ┊         │    LogWeight
  │                                     ┊         │
  │                                     ┊         └──► compose.rs [wfst] ──► lib.rs [core]
  │                                     ┊
  └─────────────────────────────────────╂──► forward_backward.rs [log]
                                        ┊         │
                                        ┊         ├──► semiring.rs (LogWeight)
                                        ┊         │
                                        ┊         ▼
                                        ┊    log_push.rs [log] ──► forward_backward.rs [log]
                                        ┊         │                      ┊
                                        ┊         └──► semiring.rs       ┊
                                        ┊                                ┊
                                        ┊    training.rs [log] ──────────┘
                                        ┊         ├──► semiring.rs (LogWeight, TropicalWeight)
                                        ┊         └──► serde_json (model I/O)
                                        ┊
                            (┊ = crossing point where a vertical dependency
                              passes through a module boundary layer)
```

Reading the graph: a module on the left of `──►` imports from the module
on the right. Dotted vertical lines `┊` mark places where one flow passes
through the horizontal space of another module without a direct import.

---

## 4. Feature-Gate Matrix

The table below shows which modules are compiled at each feature tier.
A checkmark (✓) means the module is fully available; a dash means it is
absent from the build (no code, no symbols, no overhead).

| Module                  | none | wfst | wfst-log | Lines | Tests |
|-------------------------|:----:|:----:|:--------:|------:|------:|
| `automata/semiring.rs`  |  ✓   |  ✓   |    ✓     |   631 |    20 |
| `prediction.rs`         |  ✓   |  ✓   |    ✓     |  1441+|     — |
| `dispatch.rs`           |  ✓   |  ✓   |    ✓     |   411+|     — |
| `pipeline.rs`           |  ✓   |  ✓   |    ✓     |  1482+|     — |
| `token_id.rs`           |  —   |  ✓   |    ✓     |   155 |     4 |
| `wfst.rs`               |  —   |  ✓   |    ✓     |  1358 |    20 |
| `lattice.rs`            |  —   |  ✓   |    ✓     |   933 |    20 |
| `recovery.rs`           |  —   |  ✓   |    ✓     |  1840 |    34 |
| `compose.rs`            |  —   |  ✓   |    ✓     |  1655 |    19 |
| `forward_backward.rs`   |  —   |  —   |    ✓     |   244 |     7 |
| `log_push.rs`           |  —   |  —   |    ✓     |   161 |     2 |
| `training.rs`           |  —   |  —   |    ✓     |   587 |    12 |

`wfst-log` implies `wfst`. The line counts for `prediction.rs`,
`dispatch.rs`, and `pipeline.rs` reflect the total file length; the
WFST-specific functions are small sections within those larger files.

---

## 5. Public API Surface

This section lists the key public types and functions exported by each
module. Items tagged `[wfst]` or `[log]` are conditionally compiled
under the corresponding feature.

### `automata/semiring.rs`

```
pub trait Semiring                         // core algebraic interface
pub struct TropicalWeight(pub f64)         // tropical (min, +) weight
pub struct LogWeight(pub f64)              // log-probability weight [log]
```

`TropicalWeight` provides `new()`, `value()`, `infinity()`,
`is_infinite()`, `from_priority()`. `LogWeight` [log] provides `new()`,
`value()`, `from_probability()`, `to_probability()`, `infinity()`,
`is_infinite()`.

### `token_id.rs` [wfst]

```
pub type TokenId = u16
pub const EPSILON_TOKEN: TokenId           // ε-transition sentinel (u16::MAX)
pub struct TokenIdMap                      // bidirectional name ↔ id map
  ::from_names(impl IntoIterator<Item=String>) -> Self
  ::get_or_insert(&mut self, name: &str) -> TokenId
  ::get(&self, name: &str) -> Option<TokenId>
  ::name(&self, id: TokenId) -> Option<&str>
  ::len(&self) -> usize
  ::iter(&self) -> impl Iterator<Item=(&str, TokenId)>
```

### `wfst.rs` [wfst]

```
pub type WfstStateId = u32
pub const NO_STATE: WfstStateId            // sentinel for absent state
pub struct WeightedTransition              // (token_id, target_state, weight)
pub struct WfstState                       // (transitions, final_weight)
pub struct WeightedAction                  // (rule_label, token, weight)
pub struct PredictionWfst                  // compiled prediction automaton
  ::predict(&self, token: &str) -> &[WeightedAction]
  ::predict_pruned(&self, token: &str) -> Vec<&WeightedAction>
  ::set_beam_width(&mut self, beam: Option<TropicalWeight>)
  ::from_flat(category, state_offsets, transitions, token_names, beam)
  ::with_trained_weights(&mut self, model: &TrainedModel)  // [log]
  ::union(&mut self, other: &PredictionWfst)               // weighted union for composition
  ::num_actions(&self) -> usize
pub struct PredictionWfstBuilder           // builder pattern for PredictionWfst
pub fn build_prediction_wfsts(...)
    -> BTreeMap<String, PredictionWfst>    // one per grammar category
pub fn generate_weighted_dispatch(...)
    -> Option<String>                      // weighted dispatch comment/code
```

### `lattice.rs` [wfst]

```
pub enum TokenSource<T, S>                 // Terminal | Nonterminal | Epsilon
pub struct TokenLattice<T, S>              // weighted parse chart
pub struct LatticeEdge<T, S>               // (source, weight, label)
pub struct ViterbiPath<T, S>               // decoded best path
pub fn viterbi_best_path<T,S>(...) -> Option<ViterbiPath<T,S>>
pub fn viterbi_best_path_beam<T,S>(...) -> Option<ViterbiPath<T,S>>
pub fn linear_to_lattice<T,S>(...) -> TokenLattice<T,S>
pub fn n_best_paths<T,S>(...) -> Vec<ViterbiPath<T,S>>   // [log]
```

### `recovery.rs` [wfst]

```
pub mod costs                              // default cost constants
pub enum RepairAction                      // Skip | Delete | Substitute | Insert
pub struct RepairResult                    // (actions, total_cost)
pub struct RecoveryWfst                    // edit-cost recovery automaton
  ::from_flat(category, sync_token_ids, sync_sources, token_names)
pub enum FrameKind                         // structural position tag
pub enum SyncSource                        // origin of a sync token
pub struct AnnotatedSyncToken              // (token, kind, source)
pub struct RecoveryContext                 // 3-tier context for recovery
pub enum SimulationResult                  // Success | Failure | Partial
pub struct ParseSimulator                  // simulates parse to guide recovery
  ::from_flat(first_set_tokens, follow_set_tokens, infix_tokens, depth)
pub fn viterbi_recovery(...) -> RepairResult
pub fn viterbi_recovery_beam(...) -> RepairResult
pub fn build_recovery_wfsts(...) -> Vec<RecoveryWfst>
```

### `compose.rs` [wfst]

```
pub enum CompositionError                 // +BindingPowerConflict variant
pub struct CompositionSummary              // statistics for composed grammar
pub struct WfstCompositionResult           // merged spec + prediction WFSTs
pub struct WfstCompositionSummary          // base summary + WFST stats
pub fn compose_languages(...) -> Result<LanguageSpec, CompositionError>
pub fn composition_summary(...) -> CompositionSummary
pub fn compose_many(...) -> Result<LanguageSpec, CompositionError>
pub fn compose_with_wfst(...)              // WFST-aware composition via weighted union
    -> Result<WfstCompositionResult, CompositionError>
```

### `forward_backward.rs` [log]

```
pub fn forward_scores<W: Semiring>(lattice: &TokenLattice<..>) -> Vec<W>
pub fn backward_scores<W: Semiring>(lattice: &TokenLattice<..>) -> Vec<W>
pub fn total_weight<W: Semiring>(forward: &[W], final_node: usize) -> W
```

### `log_push.rs` [log]

```
pub fn log_push_weights(wfst: &mut PredictionWfst)
pub fn check_normalization(wfst: &PredictionWfst) -> bool
```

### `training.rs` [log]

```
pub struct TrainingExample                 // (token sequence, rule labels)
pub struct RuleWeights                     // mutable weight table per rule
pub struct TrainingStats                   // iteration counts, loss history
pub struct TrainedModel                    // serializable weight snapshot
  ::save(path: &str) -> io::Result<()>    // serialize to JSON file
  ::load(path: &str) -> io::Result<Self>  // deserialize from JSON file
  ::from_embedded(json: &str) -> Result<Self, serde_json::Error>
pub struct TrainedModelMetadata            // grammar name, date, corpus size
```

---

## Cross-References

- Feature-flag DSL options: see
  [../usage/dsl-configuration.md](../usage/dsl-configuration.md).
- How modules hook into the pipeline: see
  [pipeline-integration.md](pipeline-integration.md) (this directory).
- Semiring axioms and instances: see
  [../theory/semirings.md](../theory/semirings.md).
- Viterbi algorithm and forward-backward algorithm: see
  [../theory/viterbi-and-forward-backward.md](../theory/viterbi-and-forward-backward.md).
