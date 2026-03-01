# WFST Module Map

**Date:** 2026-02-28

This document is a reference map of every source module that participates
in the WFST subsystem. It answers two questions for each module: what its
public API surface is, and how it depends on the other modules. Use it as
a starting point when navigating the source or when deciding where a new
piece of WFST functionality belongs.

All WFST modules are always compiled — there is no `wfst` feature gate.
Only `wfst-log` remains as a feature flag, gating the LogWeight semiring
and modules that depend on it (forward-backward, log-push, training).

---

## Table of Contents

1. [Feature Tiers at a Glance](#1-feature-tiers-at-a-glance)
2. [Module Inventory](#2-module-inventory)
   - 2.1 [Always-Available Modules](#21-always-available-modules)
   - 2.2 [wfst-log-Gated Modules](#22-wfst-log-gated-modules)
3. [Dependency Graph](#3-dependency-graph)
4. [Feature-Gate Matrix](#4-feature-gate-matrix)
5. [Public API Surface](#5-public-api-surface)

---

## 1. Feature Tiers at a Glance

PraTTaIL uses a single additive feature flag (`wfst-log`) to control
compilation of probabilistic/training-related WFST modules. All core
WFST functionality — prediction, recovery, lattice, composition, and
semirings — is always compiled.

```
   ┌──────────────────────────────────────────────────────────────┐
   │  Tier 0 — default (no features)                              │
   │  Core automata · Pratt parser · RD parser · prediction sets  │
   │  PredictionWfst · TokenLattice · RecoveryWfst                │
   │  compose · token_id · semirings (5 types)                    │
   │                                                              │
   │  ┌────────────────────────────────────────────────────────┐  │
   │  │  --features wfst-log                                   │  │
   │  │  + LogWeight · ForwardBackward · LogPush               │  │
   │  │  + TrainedModel · SGD training                         │  │
   │  └────────────────────────────────────────────────────────┘  │
   └──────────────────────────────────────────────────────────────┘
```

---

## 2. Module Inventory

### 2.1 Always-Available Modules

These modules are compiled in every build. All WFST core functionality
is always present — every grammar receives WFST-weighted dispatch.

#### `automata/semiring.rs`

Algebraic foundations for weighted parsing. Defines the `Semiring` trait
and six concrete types:

- `TropicalWeight` — `(ℝ⁺ ∪ {+∞}, min, +, +∞, 0)` — used for
  dispatch priority ordering and beam-pruning thresholds.
- `CountingWeight` — `(ℕ, +, x, 0, 1)` — used for parse-tree counting
  and ambiguity detection in `compute_composed_dispatch()`.
- `BooleanWeight` — `({0,1}, ∨, ∧, 0, 1)` — used for dead-rule
  detection after WFST construction.
- `EditWeight` — `(ℕ ∪ {+∞}, min, +, +∞, 0)` — used for minimum-repair
  cost computation via `RepairAction::edit_cost()`.
- `ProductWeight<S1, S2>` — componentwise product with lexicographic
  `Ord` (left first, then right) — used for multi-objective optimization.
- `LogWeight` — `(ℝ⁺ ∪ {+∞}, log-sum-exp, +, +∞, 0)` — gated under
  `#[cfg(feature = "wfst-log")]`. Uses numerically stable log-sum-exp to
  avoid floating-point underflow when multiplying small probabilities.

#### `prediction.rs`

Computes FIRST sets, FOLLOW sets, cross-category overlap analysis, and
grammar diagnostics. Includes:

- `build_dispatch_action_tables()` — extracts structured `DispatchAction`
  records from FIRST sets and overlap data. These records carry the
  token-to-rule mappings that `build_prediction_wfsts()` uses to assign
  initial weights.
- `resolve_dispatch_winners()` — converts composed dispatch table into
  `BTreeMap<(category, token), (winning_rule, weight)>`.

#### `dispatch.rs`

Generates cross-category dispatch functions. Includes:

- `write_category_dispatch_weighted()` — emits a dispatch `match` arm
  block where handler ordering is determined by WFST transition weights.
- `write_category_dispatch()` — fallback for non-weighted contexts.

Both functions accept `composed_resolutions` and `weight_map` parameters
for weight-ordered arm emission.

#### `pipeline.rs`

Orchestrates the full compile-time pipeline. WFST-related functions include:

- `generate_wfst_recovery_fn()` — emits a per-category `wfst_recover_Cat()`
  function that evaluates all four repair strategies (skip, delete, insert,
  substitute) with full 3-tier context.
- `write_trampolined_parser_recovering_wfst()` — emits the outer recovering
  entry point wrapping the fail-fast trampoline parser.
- `emit_prediction_wfst_static()` — serializes each `PredictionWfst` as
  CSR static arrays and a `LazyLock<PredictionWfst>` constructor.
- `emit_recovery_wfst_static()` — serializes each `RecoveryWfst` as static
  sync token arrays.

#### `wfst.rs`

The prediction engine. Builds one `PredictionWfst` per grammar category
from the dispatch action tables, drives weighted prefix dispatch in the
trampoline, and emits weighted dispatch comments into generated code.

Key types: `WfstStateId`, `WeightedTransition`, `WfstState`,
`WeightedAction`, `PredictionWfst`, `PredictionWfstBuilder`.

Key functions: `build_prediction_wfsts()`, `generate_weighted_dispatch()`,
`PredictionWfst::from_flat()`, `PredictionWfst::predict()`,
`PredictionWfst::predict_pruned()`, `PredictionWfst::nfa_alternative_order()`,
`PredictionWfst::with_trained_weights()` (wfst-log only).

`nfa_alternative_order()` returns indices into a rule label slice sorted by
tropical weight (lowest first). Used by the trampoline's NFA merged prefix arm
codegen to order try-all alternatives so the weight-best alternative is tried
first and returned as the primary result. Unknown rules get a default weight of
0.5 (cast-level priority).

#### `token_id.rs`

Compact token label encoding. Maps token variant name strings (e.g.,
`"Plus"`, `"Ident"`) to `u16` identifiers for use as WFST transition
labels. Avoids string comparisons in hot paths and enables dense state
arrays.

Key types: `TokenId` (type alias for `u16`), `TokenIdMap`.

Key constants: `EPSILON_TOKEN = TokenId::MAX`.

Key functions: `TokenIdMap::from_names()`, `TokenIdMap::get()`,
`TokenIdMap::get_or_insert()`, `TokenIdMap::name()`.

#### `lattice.rs`

Weighted parse chart. Represents a token sequence as a `TokenLattice`
where each edge carries a semiring weight. Provides Viterbi shortest-path
decoding and optional beam pruning. The lattice types are generic over
the weight type `W`, defaulting to `TropicalWeight`.

Key types: `TokenSource<T,S>`, `TokenLattice<T,S,W>`, `LatticeEdge<T,S,W>`,
`ViterbiPath<T,S,W>`.

Key functions: `viterbi_best_path()`, `viterbi_best_path_beam()`,
`viterbi_generic()`, `linear_to_lattice()`, `linear_to_lattice_generic()`.

`n_best_paths()` is further gated under `#[cfg(feature = "wfst-log")]`
because it uses log-probability weights for N-best ranking.

#### `recovery.rs`

Error repair engine. Constructs a `RecoveryWfst` for each grammar
category encoding the costs of skip, delete, and substitute operations.
Provides a 3-tier context model (`FrameKind`, `RecoveryContext`,
`AnnotatedSyncToken`) that captures structural position during recovery
to weight repair actions more accurately. Includes `RepairAction::edit_cost()`
for EditWeight-based cost computation.

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

Key types: `CompositionError`, `CompositionSummary`.

Key functions: `compose_languages()`, `composition_summary()`,
`compose_many()`.

---

### 2.2 `wfst-log`-Gated Modules

These three modules require the `wfst-log` feature.
They depend on `LogWeight` from `semiring.rs`.

#### `forward_backward.rs`

Forward-backward (Baum-Welch) algorithm for computing arc posterior
probabilities over a token lattice. Used by `training.rs` to accumulate
expected rule counts for weight re-estimation.

Key functions: `forward_scores()`, `backward_scores()`, `total_weight()`.

#### `log_push.rs`

Mohri weight pushing for WFST normalization. Pushes arc weights towards
the initial state so that the resulting WFST is in a canonical form
suitable for comparison and efficient decoding.

Key functions: `log_push_weights()`, `check_normalization()`.

#### `training.rs`

SGD and count-based weight training. Reads a corpus of parse traces,
runs forward-backward to accumulate expected counts, updates rule weights,
and serializes the result to a JSON `TrainedModel` that `pipeline.rs` can
load at compile time.

Key types: `TrainingExample`, `RuleWeights`, `TrainingStats`,
`TrainedModel`, `TrainedModelMetadata`.

Key functions: `TrainedModel::from_embedded()`, `TrainedModel::save()`,
`TrainedModel::load()`, `RuleWeights::train()`.

---

## 3. Dependency Graph

Arrows indicate "depends on" (imports types or calls functions).
Node labels in brackets indicate the feature tier: `[core]` for
always-available, `[log]` for `#[cfg(feature = "wfst-log")]`.

```
  lib.rs [core]
  ├── pipeline.rs [core] ─────────────┬──────────────────────────────────────┐
  │     │                             │                                       │
  │     ▼                             ▼                                       │
  │   prediction.rs [core] ─────────► dispatch.rs [core]                     │
  │     │                               │                                     │
  │     │                               ▼                                     │
  │     │                          write_category_                            │
  │     │                          dispatch_weighted()                        │
  │     │                               │                                     │
  │     └────────────────────────────────┼──► wfst.rs [core] ──► token_id.rs [core]
  │                                      │         │                   │
  │                                      │         ▼                   │
  │                                      │    PredictionWfst ──────────┘
  │                                      │         │
  │                                      │         ▼
  │                                      │    generate_weighted_dispatch()
  │                                      │
  │                                      ├──► recovery.rs [core] ──► token_id.rs [core]
  │                                      │         │
  │                                      │         ├──► lattice.rs [core]
  │                                      │         │         │
  │                                      │         │         ▼
  │                                      │         │    semiring.rs [core/log]
  │                                      │         │         ┊
  │                                      │         │         ┊ #[cfg(wfst-log)]
  │                                      │         │         ▼
  │                                      │         │    LogWeight
  │                                      │         │
  │                                      │         └──► compose.rs [core] ──► lib.rs [core]
  │                                      │
  └──────────────────────────────────────┼──► forward_backward.rs [log]
                                         │         │
                                         │         ├──► semiring.rs (LogWeight)
                                         │         │
                                         │         ▼
                                         │    log_push.rs [log] ──► forward_backward.rs [log]
                                         │         │
                                         │         └──► semiring.rs
                                         │
                                         │    training.rs [log] ──► forward_backward.rs [log]
                                         │         ├──► semiring.rs (LogWeight, TropicalWeight)
                                         │         └──► serde_json (model I/O)
                                         │
                                         └─────────────────────────────────────────────────────
```

**Additional dependency (not shown above):** `trampoline.rs` calls
`wfst.rs::PredictionWfst::nfa_alternative_order()` to order NFA merged prefix
arm alternatives by tropical weight. This dependency flows from the trampoline
codegen (Layer 2.5) to the WFST prediction engine.

Reading the graph: a module on the left of `──►` imports from the module
on the right.

---

## 4. Feature-Gate Matrix

The table below shows which modules are compiled at each feature tier.
A checkmark means the module is fully available; a dash means it is
absent from the build.

| Module                  | default | wfst-log |
|-------------------------|:-------:|:--------:|
| `automata/semiring.rs`  |    ✓    |    ✓     |
| `prediction.rs`         |    ✓    |    ✓     |
| `dispatch.rs`           |    ✓    |    ✓     |
| `pipeline.rs`           |    ✓    |    ✓     |
| `token_id.rs`           |    ✓    |    ✓     |
| `wfst.rs`               |    ✓    |    ✓     |
| `lattice.rs`            |    ✓    |    ✓     |
| `recovery.rs`           |    ✓    |    ✓     |
| `compose.rs`            |    ✓    |    ✓     |
| `forward_backward.rs`   |    —    |    ✓     |
| `log_push.rs`           |    —    |    ✓     |
| `training.rs`           |    —    |    ✓     |

**Test counts:** default (no features): 644, `wfst-log`: 678.

---

## 5. Public API Surface

This section lists the key public types and functions exported by each
module. Items tagged `[log]` are conditionally compiled under `wfst-log`.

### `automata/semiring.rs`

```
pub trait Semiring                         // core algebraic interface
pub struct TropicalWeight(pub f64)         // tropical (min, +) weight
pub struct CountingWeight(pub u64)         // counting (+, x) weight
pub struct BooleanWeight(pub bool)         // boolean (∨, ∧) weight
pub struct EditWeight(pub u64)             // edit distance (min, +) weight
pub struct ProductWeight<S1, S2>(pub S1, pub S2)  // componentwise product
pub struct LogWeight(pub f64)              // log-probability weight [log]
```

`TropicalWeight` provides `new()`, `value()`, `infinity()`,
`is_infinite()`, `from_priority()`. `CountingWeight` provides `new()`,
`value()`. `BooleanWeight` provides `new()`, `value()`. `EditWeight`
provides `new()`, `value()`, `infinity()`. `ProductWeight` provides
lexicographic `Ord`. `LogWeight` [log] provides `new()`, `value()`,
`from_probability()`, `to_probability()`, `infinity()`, `is_infinite()`.

### `token_id.rs`

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

### `wfst.rs`

```
pub type WfstStateId = u32
pub const NO_STATE: WfstStateId            // sentinel for absent state
pub struct WeightedTransition              // (token_id, target_state, weight)
pub struct WfstState                       // (transitions, final_weight)
pub struct WeightedAction                  // (rule_label, token, weight)
pub struct PredictionWfst                  // compiled prediction automaton
  ::predict(&self, token: &str) -> &[WeightedAction]
  ::predict_pruned(&self, token: &str) -> Vec<&WeightedAction>
  ::predict_with_confidence(&self, token: &str) -> ...
  ::nfa_alternative_order(&self, token: &str, labels: &[&str]) -> Vec<(usize, TropicalWeight)>
  ::beam_width(&self) -> Option<TropicalWeight>
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

### `lattice.rs`

```
pub enum TokenSource<T, S>                 // Terminal | Nonterminal | Epsilon
pub struct TokenLattice<T, S, W = TropicalWeight>  // weighted parse chart
pub struct LatticeEdge<T, S, W = TropicalWeight>   // (source, weight, label)
pub struct ViterbiPath<T, S, W = TropicalWeight>   // decoded best path
pub fn viterbi_best_path<T,S>(...) -> Option<ViterbiPath<T,S>>
pub fn viterbi_best_path_beam<T,S>(...) -> Option<ViterbiPath<T,S>>
pub fn viterbi_generic<W: Semiring + Ord>(...) -> Option<ViterbiPath<T,S,W>>
pub fn linear_to_lattice<T,S>(...) -> TokenLattice<T,S>
pub fn linear_to_lattice_generic<W>(...) -> TokenLattice<T,S,W>
pub fn n_best_paths<T,S>(...) -> Vec<ViterbiPath<T,S>>   // [log]
```

### `recovery.rs`

```
pub mod costs                              // default cost constants
pub enum RepairAction                      // Skip | Delete | Substitute | Insert
  ::edit_cost(&self) -> EditWeight         // edit-distance cost of each action
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

### `compose.rs`

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
  [../../usage/wfst/dsl-configuration.md](../../usage/wfst/dsl-configuration.md).
- How modules hook into the pipeline: see
  [pipeline-integration.md](pipeline-integration.md) (this directory).
- Semiring axioms and instances: see
  [../../theory/wfst/semirings.md](../../theory/wfst/semirings.md).
- Viterbi algorithm and forward-backward algorithm: see
  [../../theory/wfst/viterbi-and-forward-backward.md](../../theory/wfst/viterbi-and-forward-backward.md).
