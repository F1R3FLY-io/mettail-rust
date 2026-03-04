# RecoveryConfig and Trained Weights

**Date:** 2026-03-01

Covers the 19-parameter `RecoveryConfig` struct, the
`apply_trained_weights()` method, and the SGD training loop in
`train_recovery_weights()`. All recovery costs that were previously
hardcoded constants are now configurable via `RecoveryConfig`, enabling
grammar-specific tuning and machine-learned weight optimization.

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [RecoveryConfig Fields](#2-recoveryconfig-fields)
3. [Complete Default Values Table](#3-complete-default-values-table)
4. [Pipeline Data Flow](#4-pipeline-data-flow)
5. [Trained Recovery Weights](#5-trained-recovery-weights)
6. [Tuning Guidelines](#6-tuning-guidelines)
7. [Worked Examples](#7-worked-examples)
8. [Source Reference](#8-source-reference)

---

## 1. Motivation

The original recovery system used hardcoded constants in the `costs`
module:

```rust
pub const SKIP_PER_TOKEN: TropicalWeight = TropicalWeight::new(0.5);
pub const DELETE: TropicalWeight = TropicalWeight::new(1.0);
pub const SUBSTITUTE: TropicalWeight = TropicalWeight::new(1.5);
pub const INSERT: TropicalWeight = TropicalWeight::new(2.0);
pub const MAX_SKIP_LOOKAHEAD: usize = 32;
```

These defaults work well for general-purpose grammars, but specific
grammar styles benefit from tuning:

- **Bracket-heavy grammars** (Lisp, Rholang): unmatched brackets are the
  most common error → lower insert cost for closing delimiters.
- **Expression-dense grammars** (APL, J): operators appear at high
  density → wider beam width to evaluate more repair options.
- **Deeply nested grammars** (XML, S-expressions): deep nesting is
  normal → adjust depth thresholds to avoid over-discounting skip.

`RecoveryConfig` replaces all hardcoded constants with named, documented
fields that can be set by grammar authors at compile time or learned from
a training corpus.

---

## 2. RecoveryConfig Fields

### 2.1 Base Strategy Costs (5 fields)

| Field             | Type  | Default | Semantics                        |
|-------------------|-------|---------|----------------------------------|
| `skip_per_token`  | `f64` | 0.5     | Tropical cost per skipped token  |
| `delete_cost`     | `f64` | 1.0     | Cost to delete one token         |
| `substitute_cost` | `f64` | 1.5     | Cost to substitute one token     |
| `insert_cost`     | `f64` | 2.0     | Cost to insert a phantom token   |
| `swap_cost`       | `f64` | 1.25    | Cost to swap two adjacent tokens |

### 2.2 Lookahead (1 field)

| Field                | Type    | Default | Semantics                       |
|----------------------|---------|---------|---------------------------------|
| `max_skip_lookahead` | `usize` | 32      | Maximum tokens to scan for sync |

### 2.3 Tier 1: Depth Scaling (4 fields)

| Field                     | Type    | Default | Semantics                             |
|---------------------------|---------|---------|---------------------------------------|
| `deep_nesting_threshold`  | `usize` | 1000    | Depth above which skip is discounted  |
| `deep_nesting_skip_mult`  | `f64`   | 0.5     | Skip multiplier when deeply nested    |
| `shallow_depth_threshold` | `usize` | 10      | Depth below which skip is penalized   |
| `shallow_depth_skip_mult` | `f64`   | 2.0     | Skip multiplier when shallowly nested |

**Semantics:** When the parse depth exceeds `deep_nesting_threshold`,
skip actions become cheaper (multiplied by 0.5) because errors in deeply
nested code are likely noise. When depth is below
`shallow_depth_threshold`, skip actions become more expensive (multiplied
by 2.0) because the parser is near the top level and precise repair is
preferred.

### 2.4 Tier 1: BP Scaling (2 fields)

| Field              | Type  | Default | Semantics                             |
|--------------------|-------|---------|---------------------------------------|
| `low_bp_threshold` | `u8`  | 4       | BP below which skip is discounted     |
| `low_bp_skip_mult` | `f64` | 0.75    | Skip multiplier for low binding power |

**Semantics:** Low binding power means the parser is in a loosely bound
context (top-level expression, statement boundary). Skipping is safer
in these contexts because there's less accumulated state to invalidate.

### 2.5 Tier 1: Frame-Kind Multipliers (4 fields)

| Field                    | Type  | Default | Semantics                              |
|--------------------------|-------|---------|----------------------------------------|
| `collection_insert_mult` | `f64` | 0.5     | Insert discount in Collection frames   |
| `group_insert_mult`      | `f64` | 0.5     | Insert discount in Group frames        |
| `bracket_insert_mult`    | `f64` | 0.3     | Insert discount for unmatched brackets |
| `mixfix_substitute_mult` | `f64` | 0.75    | Substitute discount in Mixfix frames   |

**Semantics:**

- **Collection (0.5×):** In list/set/map bodies, missing separators and
  elements are the most common error. Cheaper insert encourages
  fabricating the missing comma or element.
- **Group (0.5×):** In parenthesized/braced groups, missing closing
  delimiters are common. Cheaper insert for the closing delimiter.
- **Bracket (0.3×):** When bracket balance shows unmatched openers,
  inserting the matching closer is strongly preferred (3.3× discount).
- **Mixfix (0.75×):** In multi-part operators (e.g. `a ? b : c`),
  substituting the wrong separator with the expected one is preferred.

### 2.6 Tier 3: Simulation Multipliers (2 fields)

| Field                     | Type  | Default | Semantics                              |
|---------------------------|-------|---------|----------------------------------------|
| `simulation_valid_mult`   | `f64` | 0.5     | Discount when simulation shows valid   |
| `simulation_fail_penalty` | `f64` | 0.2     | Penalty per unmatched token on failure |

**Semantics:** After proposing a repair, the ParseSimulator checks
whether the subsequent tokens form a valid parse continuation. If yes,
the repair's cost is halved (0.5×). If no, a penalty of
`1.0 + (lookahead − position) × 0.2` is applied — earlier failures
(more unmatched tokens) get a larger penalty.

### 2.7 Beam Pruning (1 field)

| Field        | Type          | Default     | Semantics                      |
|--------------|---------------|-------------|--------------------------------|
| `beam_width` | `Option<f64>` | `Some(3.0)` | Viterbi beam width; None = off |

**Semantics:** In `viterbi_multi_step()`, nodes whose accumulated cost
exceeds `dist[SINK] + beam_width` are pruned. `None` disables beam
pruning (evaluates all nodes).

### 2.8 Cascade Prevention (1 field)

| Field            | Type    | Default | Semantics                       |
|------------------|---------|---------|---------------------------------|
| `cascade_window` | `usize` | 3       | Tokens within which to suppress |

**Semantics:** After reporting an error at position *p*, errors at
positions [*p* + 1, *p* + *k*] are suppressed. See
[cascade-suppression.md](../../theory/wfst/cascade-suppression.md).

---

## 3. Complete Default Values Table

| #  | Field                     | Default   | Valid Range    | Effect of Increasing                |
|----|---------------------------|-----------|----------------|-------------------------------------|
| 1  | `skip_per_token`          | 0.5       | (0, ∞)         | Skip becomes more expensive         |
| 2  | `delete_cost`             | 1.0       | (0, ∞)         | Delete becomes more expensive       |
| 3  | `substitute_cost`         | 1.5       | (0, ∞)         | Substitute becomes more expensive   |
| 4  | `insert_cost`             | 2.0       | (0, ∞)         | Insert becomes more expensive       |
| 5  | `swap_cost`               | 1.25      | (0, ∞)         | Swap becomes more expensive         |
| 6  | `max_skip_lookahead`      | 32        | [1, ∞)         | Wider skip search window            |
| 7  | `deep_nesting_threshold`  | 1000      | [0, ∞)         | Fewer positions qualify as "deep"   |
| 8  | `deep_nesting_skip_mult`  | 0.5       | (0, ∞)         | Less discount when deep             |
| 9  | `shallow_depth_threshold` | 10        | [0, ∞)         | More positions qualify as "shallow" |
| 10 | `shallow_depth_skip_mult` | 2.0       | (0, ∞)         | More penalty when shallow           |
| 11 | `low_bp_threshold`        | 4         | [0, 255]       | Wider range qualifies as "low BP"   |
| 12 | `low_bp_skip_mult`        | 0.75      | (0, ∞)         | Less discount at low BP             |
| 13 | `collection_insert_mult`  | 0.5       | (0, ∞)         | Less discount in collections        |
| 14 | `group_insert_mult`       | 0.5       | (0, ∞)         | Less discount in groups             |
| 15 | `bracket_insert_mult`     | 0.3       | (0, ∞)         | Less discount for bracket repair    |
| 16 | `mixfix_substitute_mult`  | 0.75      | (0, ∞)         | Less discount in mixfix             |
| 17 | `simulation_valid_mult`   | 0.5       | (0, ∞)         | Less simulation discount            |
| 18 | `simulation_fail_penalty` | 0.2       | [0, ∞)         | Larger penalty on sim failure       |
| 19 | `beam_width`              | Some(3.0) | None or (0, ∞) | Wider beam, more paths explored     |
| 20 | `cascade_window`          | 3         | [0, ∞)         | More phantom errors suppressed      |

(20 fields total — the plan listed 19 but `cascade_window` is the 20th
when counting all individually.)

---

## 4. Pipeline Data Flow

```
LanguageSpec
    │
    │  recovery_config: RecoveryConfig
    │
    ▼
run_pipeline()
    │
    ├── extract_data()
    │       ├── build_recovery_wfsts()     (uses sync_tokens, token_map)
    │       └── build_parse_simulator()    (uses FIRST/FOLLOW/infix sets)
    │
    ├── generate_code()
    │       ├── emit_recovery_wfst_static()
    │       │       ├── RECOVERY_SYNC_TOKENS_Cat  (u16 array)
    │       │       ├── RECOVERY_TOKEN_NAMES_Cat  (&str array)
    │       │       └── from_flat() reconstruction
    │       │
    │       ├── emit_parse_simulator_static()
    │       │       ├── SIM_FIRST_SETS     (&[(&str, &[u16])])
    │       │       ├── SIM_FOLLOW_SETS    (&[(&str, &[u16])])
    │       │       ├── SIM_INFIX_SETS     (&[(&str, &[u16])])
    │       │       └── PARSE_SIMULATOR    (LazyLock<ParseSimulator>)
    │       │
    │       ├── generate_wfst_recovery_fn()
    │       │       └── wfst_recover_Cat() (7 strategies)
    │       │
    │       ├── emit beam_width constant
    │       │       └── const RECOVERY_BEAM_WIDTH: Option<f64> = ...;
    │       │
    │       └── write_trampolined_parser_recovering_wfst()
    │               ├── BRACKET_STATE_Cat    (thread-local Cell)
    │               ├── LAST_ERROR_POS_Cat   (thread-local Cell)
    │               └── parse_Cat_recovering (cascade check + recovery)
    │
    ▼
Generated Code
    │
    │  RecoveryConfig values inlined as constants:
    │    - skip costs, depth thresholds, frame multipliers
    │    - beam_width, cascade_window
    │
    ▼
Runtime
    │
    ├── parse_Cat()           ← happy path (no recovery overhead)
    └── parse_Cat_recovering  ← error path (uses config values)
            │
            ├── cascade check (LAST_ERROR_POS + cascade_window)
            ├── incremental bracket scan (BRACKET_STATE)
            ├── wfst_recover_Cat (7 strategies, config constants)
            └── ParseError::RecoveryApplied
```

**Key point:** RecoveryConfig values are inlined as constants in the
generated code. Changing the config requires recompilation. Runtime
tuning is not currently supported (the config is a compile-time
parameter).

---

## 5. Trained Recovery Weights (wfst-log feature)

The `wfst-log` feature enables machine learning of recovery strategy
costs from a corpus of erroneous inputs paired with expected repairs.

### 5.1 RecoveryTrainingExample

```rust
pub struct RecoveryTrainingExample {
    pub input_with_error: String,        // e.g. "3 + + 5"
    pub correct_input: String,           // e.g. "3 + 5"
    pub error_positions: Vec<usize>,     // e.g. [2]
    pub expected_repairs: Vec<RepairAction>, // e.g. [DeleteToken]
}
```

Each example pairs an erroneous input with the known-correct version,
the positions of errors, and the expected repair actions. The trainer
adjusts strategy costs so that the expected repair is cheaper than
alternatives.

### 5.2 train_recovery_weights() SGD

```rust
pub fn train_recovery_weights(
    examples: &[RecoveryTrainingExample],
    epochs: usize,
    learning_rate: f64,
) -> HashMap<String, f64>
```

**Algorithm:**

1. **Initialize** weights from `RecoveryConfig::default()`:
   `{skip_per_token: 0.5, delete_cost: 1.0, substitute_cost: 1.5,
   insert_cost: 2.0, swap_cost: 1.25}`

2. **For each epoch:**
   a. Initialize gradient accumulator to zero for all weights.
   b. For each example and each expected repair:
      - Identify the target strategy (e.g. `DeleteToken` → `delete_cost`).
      - Decrease the target strategy's gradient by `1.0 / |examples|`.
      - Increase all other strategies' gradients by `0.5 / |examples|`.
   c. Apply gradients: `weight += learning_rate × gradient`.
   d. Clamp all weights to [0.01, 10.0].

**Strategy name mapping:**

| RepairAction    | Config Key        |
|-----------------|-------------------|
| SkipToSync      | `skip_per_token`  |
| DeleteToken     | `delete_cost`     |
| SubstituteToken | `substitute_cost` |
| InsertToken     | `insert_cost`     |
| SwapTokens      | `swap_cost`       |
| Composite       | `delete_cost`     |
| CategorySwitch  | `substitute_cost` |

Composite uses `delete_cost` as its dominant cost key. CategorySwitch
uses `substitute_cost` since it's semantically a substitution.

### 5.3 apply_trained_weights()

```rust
impl RecoveryConfig {
    pub fn apply_trained_weights(
        &mut self,
        weights: &HashMap<String, f64>,
    ) {
        if let Some(&v) = weights.get("skip_per_token")  { self.skip_per_token = v; }
        if let Some(&v) = weights.get("delete_cost")     { self.delete_cost = v; }
        if let Some(&v) = weights.get("substitute_cost") { self.substitute_cost = v; }
        if let Some(&v) = weights.get("insert_cost")     { self.insert_cost = v; }
        if let Some(&v) = weights.get("swap_cost")       { self.swap_cost = v; }
    }
}
```

Unknown keys are silently ignored. Only the 5 base strategy costs are
overridden; threshold and multiplier fields remain at their configured
values.

### 5.4 TrainedModel Serialization

Trained weights are serialized alongside rule weights in `TrainedModel`:

```rust
pub struct TrainedModel {
    pub rule_weights: HashMap<String, f64>,
    pub recovery_weights: HashMap<String, f64>,  // #[serde(default)]
}
```

Serialization uses `postcard` (compact binary format). The
`#[serde(default)]` attribute on `recovery_weights` ensures backward
compatibility with models trained before the recovery expansion.

`TrainedModel::from_embedded(data)` deserializes from a byte slice,
enabling compile-time embedding via `include_bytes!()`.

---

## 6. Tuning Guidelines

### 6.1 When to Adjust Base Costs

- **Too many deletions:** Increase `delete_cost` to prefer skip or
  substitute over delete.
- **Too many insertions:** Increase `insert_cost` or decrease
  `bracket_insert_mult` to make phantom tokens more expensive.
- **Swaps never chosen:** Decrease `swap_cost` below `delete_cost` to
  make transposition more attractive.

### 6.2 When to Adjust Depth Thresholds

- **Grammar with deep nesting as normal:** Increase
  `deep_nesting_threshold` so that normal depth is not treated as "deep."
- **Grammar with very flat structure:** Decrease
  `shallow_depth_threshold` to avoid penalizing skip at typical depths.

### 6.3 When to Adjust Beam Width

- **Complex errors with many repair options:** Increase `beam_width` to
  explore more paths in the Viterbi lattice.
- **Performance-sensitive parsers:** Decrease `beam_width` or set to
  `None` to limit Viterbi search.

### 6.4 When to Adjust Cascade Window

- **Too many suppressed errors:** Decrease `cascade_window` (even
  `cascade_window: 1` suppresses only immediately adjacent errors).
- **Too many phantom errors:** Increase `cascade_window` to suppress
  more aggressively.

---

## 7. Worked Examples

### 7.1 Bracket-Heavy Grammar

Grammar with many parenthesized groups (e.g. Lisp-like S-expressions):

```rust
RecoveryConfig {
    insert_cost: 1.5,             // lower base insert (was 2.0)
    bracket_insert_mult: 0.2,     // stronger bracket repair (was 0.3)
    group_insert_mult: 0.3,       // stronger group insert (was 0.5)
    cascade_window: 4,            // wider cascade for bracket chains
    ..Default::default()
}
```

**Effect:** Missing `)` is strongly preferred for insertion (cost =
1.5 × 0.3 × 0.2 = 0.09 when bracket is unmatched in a Group frame).

### 7.2 Deeply Nested Grammar

Grammar with normal nesting depths of 50-100 (e.g. XML-like):

```rust
RecoveryConfig {
    deep_nesting_threshold: 200,    // was 1000 — start discounting at 200
    shallow_depth_threshold: 3,     // was 10 — only penalize very shallow
    deep_nesting_skip_mult: 0.3,    // stronger skip discount when deep
    beam_width: Some(5.0),          // wider beam for complex structures
    ..Default::default()
}
```

**Effect:** At depth 200+, skip cost is multiplied by 0.3 (was 0.5),
strongly preferring skip-to-sync over insert or substitute in deeply
nested contexts.

---

## 8. Source Reference

| Symbol                             | Location                             |
|------------------------------------|--------------------------------------|
| `RecoveryConfig`                   | `prattail/src/recovery.rs:109–166`   |
| `RecoveryConfig::default()`        | `prattail/src/recovery.rs:168–193`   |
| `apply_trained_weights()`          | `prattail/src/recovery.rs:200–217`   |
| `RecoveryContext`                  | `prattail/src/recovery.rs:1198–1227` |
| `skip_multiplier_with()`           | `prattail/src/recovery.rs:1241–1262` |
| `insert_multiplier_with()`         | `prattail/src/recovery.rs:1274–1288` |
| `bracket_insert_multiplier_with()` | `prattail/src/recovery.rs:1318–1329` |
| `RecoveryTrainingExample`          | `prattail/src/training.rs:361–370`   |
| `train_recovery_weights()`         | `prattail/src/training.rs:387–456`   |
| `TrainedModel`                     | `prattail/src/training.rs` (struct)  |
| `RECOVERY_BEAM_WIDTH`              | `prattail/src/pipeline.rs:791`       |

**Cross-references:**

- [error-recovery.md](error-recovery.md) — original cost constants
- [extended-recovery-strategies.md](extended-recovery-strategies.md) —
  strategy evaluation with config values
- [cascade-suppression.md](../../theory/wfst/cascade-suppression.md) —
  cascade_window theory
- [recovery-tuning.md](../../usage/wfst/recovery-tuning.md) —
  practical tuning guide
- [weight-training.md](weight-training.md) — LogWeight SGD training
  (separate from recovery weight training)
