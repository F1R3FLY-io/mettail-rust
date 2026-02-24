# Feature Gates

PraTTaIL's WFST subsystem is strictly opt-in. The default build compiles
only the core automata and parser; no WFST code is emitted, no extra
dependencies are pulled in, and generated parsers carry zero weighted-parsing
overhead. Each feature tier is purely additive — enabling a tier activates
only the modules it introduces.

---

## 1. Feature Tiers

### 1.1 No Features (Default)

Activates the full core PraTTaIL stack:

- NFA → DFA → Hopcroft minimization → equivalence-class compression
- Pratt parser with binding-power tables
- Recursive-descent handler generation
- Trampoline stack-safe dispatch
- FIRST/FOLLOW set computation and sync-predicate synthesis
- Lexer codegen and pipeline orchestration

**Test count (prattail):** 150
**Test count (workspace):** 358
**Extra dependencies:** none

### 1.2 `wfst`

Activates weighted parsing on top of the core stack:

- `wfst` — `PredictionWfst`, `WeightedTransition`, `VectorWfst`
- `token_id` — `TokenId`, `TokenIdMap` (stable integer labels for tokens)
- `lattice` — `TokenLattice`, beam-pruning mechanics, Viterbi best-path,
  N-best path enumeration
- `recovery` — context-aware 3-tier error recovery via edit-cost transducers
- `compose` — on-the-fly WFST composition algorithm

The pipeline gains several additional stages: dispatch action-table
construction (`build_dispatch_action_tables` in `prediction.rs`), WFST
codegen (`generate_wfst_recovery_fn`, `write_category_dispatch_weighted`
in `dispatch.rs`), and static WFST embedding
(`emit_prediction_wfst_static`, `emit_recovery_wfst_static` in
`pipeline.rs`) that serializes WFSTs as CSR static arrays with
`LazyLock` constructors for runtime access. Recovery codegen now emits
full 4-strategy context-aware repair with bracket balance tracking.

**Test count (prattail):** 254 (+104 over default)
**Test count (workspace):** 462 (+104 over default)
**Extra dependencies:** none beyond the core crate graph

### 1.3 `wfst-log`

Activates the log-probability semiring and all modules that depend on it.
This tier **implies** `wfst` — enabling `wfst-log` alone is sufficient; you
do not need to specify both.

Additional modules:

- `forward_backward` — numerically stable forward-backward algorithm
  (log-sum-exp accumulation, posterior rule counts)
- `log_push` — weight pushing to normalize WFSTs for optimal beam pruning
- `training` — `RuleWeights`, `TrainedModel`, `TrainingStats`,
  `TrainingExample`, `TrainedModelMetadata`

Adds serde/serde_json as optional dependencies (only materialized under
`wfst-log`) for model serialization.

**Test count (prattail):** 288 (+34 over `wfst`, +138 over default)
**Test count (workspace):** 496 (+34 over `wfst`, +138 over default)
**Extra dependencies:** `serde`, `serde_json` (optional, activated by this tier)

---

## 2. Cargo.toml Snippets

Feature flags must be declared in every crate in the chain. The chain runs
from the workspace root through `repl`, `languages`, and `macros` down to
the `prattail` leaf.

### 2.1 `prattail/Cargo.toml` (leaf)

```toml
[features]
wfst = []
wfst-log = ["wfst", "dep:serde", "dep:serde_json"]

[dependencies]
serde     = { version = "1", features = ["derive"], optional = true }
serde_json = { version = "1",                       optional = true }
```

`wfst-log` declares `"wfst"` as a dependency so activating `wfst-log`
automatically enables `wfst`.

### 2.2 `macros/Cargo.toml`

```toml
[features]
wfst     = ["mettail-prattail/wfst"]
wfst-log = ["mettail-prattail/wfst-log"]
```

### 2.3 `languages/Cargo.toml`

```toml
[features]
wfst     = ["mettail-macros/wfst"]
wfst-log = ["mettail-macros/wfst-log"]
```

### 2.4 `repl/Cargo.toml`

```toml
[features]
wfst     = ["mettail-languages/wfst", "mettail-macros/wfst"]
wfst-log = ["mettail-languages/wfst-log", "mettail-macros/wfst-log"]
```

### 2.5 `Cargo.toml` (workspace root)

```toml
[features]
wfst     = ["mettail-repl/wfst"]
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
       │
       ▼
     repl ──────────┬──────────────────────────────────────────┐
       │            │                                          │
       ▼            ▼                                          │
  languages      macros ◄─────────────────────────────────────┘
       │            │
       ▼            │
    macros          │        (languages → macros, same node)
       │            ▼
       └──────► prattail
```

Dotted crossings (┊) below mark where the vertical propagation path crosses
the horizontal crate-dependency boundary:

```
  root ──→ repl ──┬──→ languages ──→ macros ──→ prattail
                  ┊                       ┊
                  └──→ macros ────────────┘
```

In practice, Cargo's feature unification means prattail sees the flag
enabled if any path through the graph activates it.

---

## 4. Running Tests by Tier

Each tier's tests are gated with `#[cfg(feature = "wfst")]` or
`#[cfg(feature = "wfst-log")]` and are automatically included or excluded
based on the active feature set.

```sh
# Tier 0 — core only (358 workspace / 150 prattail tests)
cargo test --workspace

# Tier 1 — core + WFST (462 workspace / 254 prattail tests)
cargo test --workspace --features wfst

# Tier 2 — core + WFST + log semiring (496 workspace / 288 prattail tests)
cargo test --workspace --features wfst-log
```

To run tests for a single crate at a specific tier:

```sh
# prattail tests only, WFST tier
cargo test -p mettail-prattail --features wfst

# prattail tests only, log semiring tier
cargo test -p mettail-prattail --features wfst-log
```

---

## 5. Running WFST Benchmarks

The WFST benchmark suite lives in `prattail/benches/bench_wfst.rs` and
requires the `wfst` feature. The bench target declares `required-features =
["wfst"]` in `prattail/Cargo.toml` so Cargo will refuse to build it without
the flag.

```sh
# Run all WFST benchmarks
cargo bench --features wfst -p mettail-prattail --bench bench_wfst

# Save output for later analysis
cargo bench --features wfst -p mettail-prattail --bench bench_wfst \
    | tee prattail/docs/benchmarks/wfst-results.txt
```

Benchmark results are stored in `prattail/docs/benchmarks/wfst-pipeline-integration.md`.

---

## 6. Pitfalls

**Specifying both flags is redundant.** `wfst-log` already lists `"wfst"` as
a dependency in `prattail/Cargo.toml`. Writing `--features wfst,wfst-log`
works but is unnecessary.

**`dispatch: "weighted"` without `wfst` falls back silently.** The
`DispatchStrategy::resolve()` method checks `#[cfg(feature = "wfst")]` at
compile time. If the feature is absent, `Weighted` is demoted to `Static`
with a `warning:` on stderr. See
[usage/dsl-configuration.md](dsl-configuration.md) for the `dispatch` option.

**`beam_width: auto` requires `wfst-log` and `log_semiring_model_path`.** The
DSL parser emits a compile error if `auto` is specified without a model path,
and the pipeline emits a fallback-to-`Disabled` warning if the model file is
absent at compile time. See
[usage/dsl-configuration.md](dsl-configuration.md) for full option semantics.

**Release builds need `RUSTFLAGS=""`** to override the workspace's Cranelift
codegen backend. Benchmarks use the `bench` profile which inherits from
`release` (LLVM, `opt-level = 3`), so this is only relevant for manual
`--release` builds.

---

## 7. Cross-References

- [usage/dsl-configuration.md](dsl-configuration.md) — `beam_width`, `dispatch`, and
  `log_semiring_model_path` options in the `language!` macro
- [usage/training-guide.md](training-guide.md) — end-to-end workflow for training
  rule weights and producing `TrainedModel` JSON
- [architecture/pipeline-integration.md](../architecture/pipeline-integration.md) — how
  WFST module activation hooks into `generate_parser_code()`
- `BeamWidthConfig` enum internals and `Auto` resolution are documented in
  [usage/dsl-configuration.md](dsl-configuration.md) and in the source at `prattail/src/lib.rs`
