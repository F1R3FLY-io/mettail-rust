# WFST Features Guide

Weighted Finite-State Transducers (WFSTs) extend PraTTaIL's parser with probabilistic
disambiguation, adaptive error recovery, and learnable rule weights. They are entirely
opt-in: the default build carries zero WFST overhead.

---

## What WFSTs Add

| Capability | Description |
|---|---|
| **Weighted dispatch** | Reorder parse alternatives by predicted cost instead of declaration order |
| **Beam pruning** | Discard low-probability parse paths early to limit backtracking |
| **Error recovery** | Minimum-cost token repair via the Viterbi algorithm |
| **Grammar composition** | Merge multiple grammar WFSTs into a single transducer |
| **Weight training** | Learn rule weights from annotated training data |

---

## Enabling WFST Features

Two feature tiers are available:

```bash
# Basic WFST: weighted dispatch, beam pruning, recovery, composition
cargo build --features wfst

# Full WFST: all of the above plus log semiring, training, forward-backward algorithm
cargo build --features wfst-log
```

`wfst-log` implies `wfst`; you never need to list both.

To run the test suite with WFST features:

```bash
cargo test --features wfst
cargo test --features wfst-log
```

---

## Choosing the Right Feature Tier

| Use Case | Recommended Feature |
|---|---|
| Simple grammars with no cross-category ambiguity | *(none — default)* |
| Cross-category disambiguation and error recovery | `wfst` |
| Learned weights, probabilistic parsing, N-best outputs | `wfst-log` |

The default (no features) is the right choice for most grammars. Add `wfst` when parse
alternatives overlap across categories and declaration order is insufficient for correct
disambiguation. Add `wfst-log` when you have training data and want weights to improve
over time.

---

## Test Counts by Feature Tier

| Features | PraTTaIL Tests | Workspace Tests | Notes |
|---|---|---|---|
| *(none)* | 150 | 358 | Core automata and parser |
| `wfst` | 254 | 462 | +beam, context recovery, base WFST modules, static embedding, composition |
| `wfst-log` | 288 | 496 | +LogWeight, forward-backward, N-best, log-push, training |

---

## DSL Configuration

WFST behaviour is configured in the `options` block of a `language!` macro invocation:

```rust
language! {
    options {
        beam_width: 1.5,
        dispatch: "weighted",
    }

    // ... grammar rules ...
}
```

### `beam_width`

Controls beam pruning during prediction. Accepted values:

| Value | Meaning |
|---|---|
| `none` / `disabled` | No beam pruning (default) |
| A positive float (e.g. `1.5`) | Explicit beam width |
| `auto` | Automatic width from a trained log-semiring model (requires `wfst-log` and `log_semiring_model_path`) |

Example:

```rust
options {
    beam_width: 2.0,   // prune paths whose cost exceeds best * 2.0
}
```

### `dispatch`

| Value | Meaning |
|---|---|
| `"static"` | Declaration-order dispatch (default) |
| `"weighted"` | WFST-weighted dispatch (requires `wfst`) |
| `"auto"` | Weighted when grammar is complex enough; static otherwise |

The `auto` strategy selects weighted dispatch when:
- `total_rules >= 30` AND `cross_category_count > 0`, OR
- `ambiguous_overlap_count >= 3`

---

## How Weighted Dispatch Works

When `dispatch: "weighted"` is active, the pipeline builds a prediction WFST after
computing FIRST and FOLLOW sets. Each parse alternative is assigned a weight derived from
the grammar topology. At compile time, match arm ordering is reordered by weight. At
runtime, the WFST is embedded as CSR static arrays with a `LazyLock<PredictionWfst>`
constructor, enabling `predict()` calls per token during parsing.

Alternatives are tried in ascending cost order rather than declaration order, which reduces
backtracking for ambiguous cross-category rules. Trained model weights can override
heuristic weights at runtime via `PredictionWfst::with_trained_weights()`.

Beam pruning integrates with this: any continuation whose accumulated cost exceeds
`best_cost + beam_width` is dropped before recursion.

---

## Error Recovery

With the `wfst` feature, error recovery uses a three-tier context model with four
repair strategies:

**Repair strategies** (evaluated at each error position):
1. **Skip-to-sync** — advance past unexpected tokens to the nearest sync point
2. **Delete** — remove exactly one unexpected token
3. **Insert** — fabricate a missing sync token (e.g., closing bracket)
4. **Substitute** — replace the current token with an expected one

**Context tiers** (adjust repair costs multiplicatively):
1. **Frame context** (Tier 1): the current trampoline frame kind, nesting depth, and
   binding power adjust skip/insert/substitute cost multipliers.
2. **Bracket balance** (Tier 2): unmatched open brackets get a 0.3× multiplier for
   inserting the matching closer, strongly preferring bracket repair.
3. **Parse simulation** (Tier 3): a lightweight `ParseSimulator` checks whether a
   proposed repair leads to a valid continuation over a 5-token lookahead window.

Recovery functions are generated as separate `_recovering` variants with full context
propagation (bracket balance estimated by scanning consumed tokens). The non-recovering
path has zero overhead from recovery logic.

---

## Further Reading

Detailed documentation lives under `prattail/docs/experimental/wfst/`:

- **Theory**: `../../prattail/docs/experimental/wfst/theory/` - Semirings, tropical algebra, Viterbi
- **Architecture**: `../../prattail/docs/experimental/wfst/architecture/` - Module structure and data flow
- **Design**: `../../prattail/docs/experimental/wfst/design/` - Decision records and trade-offs
- **Usage**: `../../prattail/docs/experimental/wfst/usage/` - Worked examples and recipes

Benchmark results: `../../prattail/docs/benchmarks/wfst-pipeline-integration.md`

---

**Last Updated**: February 2026
