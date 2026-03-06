# Feature Gates

**Updated:** 2026-02-28

PraTTaIL's WFST subsystem is mostly always-on. The default build compiles
all core WFST modules -- prediction, dispatch, recovery, composition, lattice,
and all semirings except LogWeight. Only the log-probability semiring and
its dependent modules (training, forward-backward, log-push) remain behind
a feature gate. This two-tier structure means every grammar automatically
benefits from WFST-weighted dispatch and recovery with zero configuration.

---

## 1. Feature Tiers

### 1.1 Default (No Features)

The default build activates the full PraTTaIL stack including all WFST
functionality:

**Core automata and parser:**
- NFA -> DFA -> Hopcroft minimization -> equivalence-class compression
- Pratt parser with binding-power tables
- Recursive-descent handler generation
- Trampoline stack-safe dispatch
- FIRST/FOLLOW set computation and sync-predicate synthesis
- Lexer codegen and pipeline orchestration

**WFST modules (always compiled):**
- `wfst.rs` -- `PredictionWfst`, `WeightedTransition`, `VectorWfst`,
  `PredictionWfstBuilder`, `WeightedAction`
- `token_id.rs` -- `TokenId`, `TokenIdMap` (stable integer labels for tokens)
- `lattice.rs` -- `TokenLattice`, beam-pruning mechanics, Viterbi best-path,
  N-best path enumeration, generic lattice `TokenLattice<T, S, W>`
- `recovery.rs` -- context-aware 3-tier error recovery via edit-cost
  transducers, `RecoveryWfst`, `RepairAction::edit_cost()`
- `compose.rs` -- grammar composition, `compose_languages()`,
  `compose_with_wfst()`, incremental FIRST/FOLLOW
- `prediction.rs` -- dispatch action-table construction,
  `resolve_dispatch_winners()`, composed dispatch resolution

**Semiring types (always available):**
- `TropicalWeight` -- `(R+ u {+inf}, min, +, +inf, 0)` for path cost
- `CountingWeight` -- `(N, +, x, 0, 1)` for ambiguity counting
- `BooleanWeight` -- `({T,F}, or, and, F, T)` for reachability/dead-rule detection
- `EditWeight` -- `(R+ u {+inf}, min, +, +inf, 0)` for edit distance
- `ProductWeight<L, R>` -- lexicographic product of two semirings

**Pipeline stages (always active):**
- Dispatch action-table construction (`build_dispatch_action_tables`)
- WFST codegen (`generate_wfst_recovery_fn`, `write_category_dispatch_weighted`)
- Static WFST embedding (`emit_prediction_wfst_static`, `emit_recovery_wfst_static`)
  as CSR static arrays with `LazyLock` constructors
- Full 4-strategy context-aware recovery with bracket balance tracking
- CountingWeight ambiguity warnings in `compute_composed_dispatch()`
- BooleanWeight dead-rule detection after WFST construction
- Weight-ordered dispatch arm emission

**Test count (workspace):** 644
**Extra dependencies:** none

### 1.2 `wfst-log`

Activates the log-probability semiring and all modules that depend on it.

Additional modules:

- `forward_backward.rs` -- numerically stable forward-backward algorithm
  (log-sum-exp accumulation, posterior rule counts)
- `log_push.rs` -- weight pushing to normalize WFSTs for optimal beam pruning
- `training.rs` -- `RuleWeights`, `TrainedModel`, `TrainingStats`,
  `TrainingExample`, `TrainedModelMetadata`

Additional semiring type:

- `LogWeight` -- `(R u {-inf}, log-sum-exp, +, +inf, 0)` for log-probability

Adds serde/serde_json as optional dependencies (only materialized under
`wfst-log`) for model serialization.

**Test count (workspace):** 678 (+34 over default)
**Extra dependencies:** `serde`, `serde_json` (optional, activated by this tier)

---

## 2. Cargo.toml Snippets

The `wfst-log` feature flag must be declared in every crate in the chain.
The chain runs from the workspace root through `repl`, `languages`, and
`macros` down to the `prattail` leaf.

### 2.1 `prattail/Cargo.toml` (leaf)

```toml
[features]
wfst-log = ["dep:serde", "dep:serde_json"]

[dependencies]
serde     = { version = "1", features = ["derive"], optional = true }
serde_json = { version = "1",                       optional = true }
```

### 2.2 `macros/Cargo.toml`

```toml
[features]
wfst-log = ["mettail-prattail/wfst-log"]
```

### 2.3 `languages/Cargo.toml`

```toml
[features]
wfst-log = ["mettail-macros/wfst-log"]
```

### 2.4 `repl/Cargo.toml`

```toml
[features]
wfst-log = ["mettail-languages/wfst-log", "mettail-macros/wfst-log"]
```

### 2.5 `Cargo.toml` (workspace root)

```toml
[features]
wfst-log = ["mettail-repl/wfst-log"]
```

---

## 3. Feature Propagation Diagram

The feature flag travels from the workspace root inward. At each node the
crate re-exports the flag to its downstream dependency. The `macros` crate
is listed twice because `repl` directly depends on both `languages` and
`macros`; the final activation at `prattail` is reached via both paths.

```
  Cargo.toml (root)
       |
       v
     repl --------------+--------------------------------------+
       |                |                                      |
       v                v                                      |
  languages          macros <----------------------------------+
       |                |
       v                |
    macros              |        (languages -> macros, same node)
       |                v
       +----------> prattail
```

In practice, Cargo's feature unification means prattail sees the flag
enabled if any path through the graph activates it.

---

## 4. Running Tests by Tier

The `wfst-log` tier's tests are gated with `#[cfg(feature = "wfst-log")]`
and are automatically included or excluded based on the active feature set.
All other WFST tests run unconditionally as part of the default test suite.

```sh
# Default -- all WFST functionality (644 workspace tests)
cargo test --workspace

# Default + log semiring (678 workspace tests)
cargo test --workspace --features wfst-log
```

To run tests for a single crate:

```sh
# prattail tests only, default tier
cargo test -p mettail-prattail

# prattail tests only, log semiring tier
cargo test -p mettail-prattail --features wfst-log
```

---

## 5. Running WFST Benchmarks

The WFST benchmark suite lives in `prattail/benches/` and runs without
any feature flags since all WFST functionality is always compiled.

```sh
# Run all benchmarks
cargo bench -p mettail-prattail

# Save output for later analysis
cargo bench -p mettail-prattail \
    | tee prattail/docs/benchmarks/bench-results.txt
```

Benchmark results are stored in `prattail/docs/benchmarks/wfst-pipeline-integration.md`.

---

## 6. Pitfalls

**`beam_width: auto` requires `wfst-log` and `log_semiring_model_path`.** The
DSL parser emits a compile error if `auto` is specified without a model path,
and the pipeline emits a fallback-to-`Disabled` warning if the model file is
absent at compile time. See
[dsl-configuration.md](dsl-configuration.md) for full option semantics.

**Release builds need `RUSTFLAGS=""`** to override the workspace's Cranelift
codegen backend. Benchmarks use the `bench` profile which inherits from
`release` (LLVM, `opt-level = 3`), so this is only relevant for manual
`--release` builds.

---

## 7. Semiring Summary

| Semiring         | Feature Gate | Semiring Operations                                   | Primary Use                        |
|------------------|--------------|-------------------------------------------------------|------------------------------------|
| `TropicalWeight` | (none)       | `(R+ u {+inf}, min, +, +inf, 0)`                      | Parse path cost, Viterbi best-path |
| `CountingWeight` | (none)       | `(N, +, x, 0, 1)`                                     | Ambiguity counting                 |
| `BooleanWeight`  | (none)       | `({T,F}, or, and, F, T)`                              | Reachability, dead-rule detection  |
| `EditWeight`     | (none)       | `(R+ u {+inf}, min, +, +inf, 0)`                      | Edit distance for repair actions   |
| `ProductWeight`  | (none)       | Lexicographic product of `<L: Semiring, R: Semiring>` | Multi-criteria optimization        |
| `LogWeight`      | `wfst-log`   | `(R u {-inf}, log-sum-exp, +, +inf, 0)`               | Log-probability, training, pushing |

---

## 8. Environment Variables

| Variable | Default | Effect |
|----------|---------|--------|
| `PRATTAIL_LINT_VERBOSE` | unset | When set, disables diagnostic grouping — emits individual lint diagnostics instead of collapsed summaries. Useful for CI pipelines that grep for specific rule names or categories. |
| `PRATTAIL_AUTO_OPTIMIZE` | unset | Comma-separated list of optimization gates to force-enable/disable (see `cost_benefit.rs`). |
| `PRATTAIL_EBNF_DUMP` | unset | When set to a directory path, dumps EBNF grammar to that location. |

---

## 9. Cross-References

- [dsl-configuration.md](dsl-configuration.md) -- `beam_width` and
  `log_semiring_model_path` options in the `language!` macro
- [training-guide.md](training-guide.md) -- end-to-end workflow for training
  rule weights and producing `TrainedModel` JSON
- `BeamWidthConfig` enum internals and `Auto` resolution are documented in
  [dsl-configuration.md](dsl-configuration.md) and in the source at `prattail/src/lib.rs`
