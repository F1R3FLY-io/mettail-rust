# WFST Integration Design

This document records the design decisions made when integrating Weighted Finite-State
Transducers (WFSTs) into PraTTaIL. It covers motivation, architecture choices, feature
propagation, dispatch strategy resolution, and benchmark findings.

---

## Context: Why WFSTs Were Added

PraTTaIL generates Pratt + recursive-descent parsers from declarative grammar
specifications. The generated parsers handle unambiguous grammars efficiently, but two
patterns create friction:

1. **Cross-category dispatch**: when a token can introduce rules in multiple grammar
   categories, the parser tries alternatives in declaration order. For grammars with many
   overlapping FIRST sets, this produces quadratic backtracking in the worst case.

2. **Cast rules**: a cast from one category to another is expressed as a Pratt prefix
   handler. The infix loop continues after the cast, which is correct, but the dispatch
   path to reach the cast is still sequential.

WFSTs provide a principled framework for both problems:

- **Weighted disambiguation**: assign a cost to each alternative; try cheapest first.
- **Minimum-cost error recovery**: model token repair as a shortest-path problem over
  the transducer and solve it with the Viterbi algorithm.

Neither capability is universally needed — small, unambiguous grammars gain nothing from
WFST overhead — so the integration is entirely opt-in via Cargo features.

---

## Architecture Decision: Opt-In Features, Zero Overhead When Disabled

### Decision

Gate all WFST code behind two Cargo features: `wfst` and `wfst-log`.

- **No features**: compile-time pipeline skips WFST construction entirely; generated
  parsers contain no WFST references.
- **`wfst`**: adds prediction WFSTs, recovery WFSTs, weighted dispatch, beam pruning,
  and grammar composition. No additional heavyweight dependencies.
- **`wfst-log`**: implies `wfst`; additionally enables the log semiring, numerically
  stable log-sum-exp operations, forward-backward algorithm, N-best path extraction,
  weight training, and `serde`/`serde_json` serialisation of trained models.

### Rationale

- Users who never need WFST features pay nothing: no extra compile time, no binary
  bloat, no runtime overhead.
- The feature split at `wfst-log` avoids forcing `serde` into builds that only need
  basic weighted dispatch.
- `wfst-log` implies `wfst` via Cargo feature dependency, so callers never need to
  list both.

### Key Implementation Locations

| Component | File |
|---|---|
| Semiring definitions (including LogWeight) | `prattail/src/automata/semiring.rs` |
| Core WFST types, prediction, `from_flat()`, `with_trained_weights()` | `prattail/src/wfst.rs` |
| Lattice, N-best, Viterbi | `prattail/src/lattice.rs` |
| Grammar composition | `prattail/src/compose.rs` |
| Context-aware recovery, `from_flat()` constructors | `prattail/src/recovery.rs` |
| Forward-backward (wfst-log) | `prattail/src/forward_backward.rs` |
| Log-push weight normalisation (wfst-log) | `prattail/src/log_push.rs` |
| Weight training, `from_embedded()` (wfst-log) | `prattail/src/training.rs` |
| Token identity mapping | `prattail/src/token_id.rs` |
| Static WFST embedding codegen | `prattail/src/pipeline.rs` |

---

## Feature Propagation Chain

Features must propagate from the root workspace down to `prattail`, which defines the
actual gates. The chain is:

```
workspace root (Cargo.toml)
  └── repl/Cargo.toml
  └── languages/Cargo.toml   ──── [features: wfst, wfst-log] ────┐
  └── macros/Cargo.toml      ──── [features: wfst, wfst-log] ────┤
                                                                    ▼
                                                         prattail/Cargo.toml
                                                         [defines: wfst, wfst-log]
```

Each intermediate crate declares:

```toml
[features]
wfst     = ["prattail/wfst"]
wfst-log = ["prattail/wfst-log"]
```

This ensures that `cargo build --features wfst` at the workspace root correctly enables
the feature in the leaf crate without requiring callers to address `prattail` directly.

---

## Dispatch Strategy Auto-Resolution

The `dispatch` option in the DSL `options` block accepts three values:

| Value | Resolved Strategy |
|---|---|
| `"static"` | `DispatchStrategy::Static` — declaration-order, always |
| `"weighted"` | `DispatchStrategy::Weighted` — WFST dispatch, always (requires `wfst`) |
| `"auto"` | Resolved at pipeline time based on grammar metrics (see below) |

### Auto-Resolution Rules

`Auto` resolves to `Weighted` when either condition holds:

```
(total_rules >= 30 AND cross_category_count > 0)
OR
ambiguous_overlap_count >= 3
```

Otherwise it resolves to `Static`.

### Rationale

Small grammars (fewer than 30 rules, no cross-category overlap) gain no measurable
benefit from weighted dispatch in benchmarks. The WFST construction cost (~3-5 µs) and
the additional instruction-cache pressure outweigh any backtracking savings for grammars
that are essentially unambiguous. The threshold was set conservatively: at 50+ rules the
pipeline overhead drops below 5%, at which point weighted dispatch is consistently
beneficial.

---

## Pipeline Integration Points

WFST construction happens inside `generate_parser_code()` in `prattail/src/pipeline.rs`,
after FIRST and FOLLOW sets are computed:

1. **Prediction WFSTs** are built per category from the FIRST-set analysis.
2. **Recovery WFSTs** are built per category from the FOLLOW-set analysis.
3. **Dispatch action tables** (`build_dispatch_action_tables()` in `prediction.rs`) map
   lookahead tokens to weighted alternative lists.
4. **Static WFST embedding** (`emit_prediction_wfst_static()`,
   `emit_recovery_wfst_static()` in `pipeline.rs`) serializes WFSTs as CSR static arrays
   with `LazyLock` constructors for runtime access.
5. **Codegen** emits weighted prefix match arms (`write_prefix_match_arms()`) and
   weighted cross-category dispatch (`write_category_dispatch_weighted()` in
   `dispatch.rs`).
6. **Recovery codegen** emits full 4-strategy context-aware `wfst_recover_Cat()` functions
   via `generate_wfst_recovery_fn()`, with bracket balance and nesting depth parameters.
7. **Recovering trampoline** emits recovering parser variants via
   `write_trampolined_parser_recovering_wfst()` that estimate bracket balance by scanning
   consumed tokens before calling the recovery function.

All seven steps are inside `#[cfg(feature = "wfst")]` guards. The non-WFST code path is
unchanged.

### Runtime Data Flow

Generated parsers can access WFST data at runtime via `LazyLock` statics:

```
PREDICTION_Cat: LazyLock<PredictionWfst>    — reconstructed from CSR arrays
    → predict(token) → Vec<WeightedAction>  — try-in-order dispatch

TRAINED_MODEL: LazyLock<TrainedModel>       — from include_str!() JSON
    → with_trained_weights(&mut wfst)       — override heuristic weights
```

Recovery WFSTs are similarly embedded as static sync token arrays, reconstructed via
`RecoveryWfst::from_flat()` at runtime.

---

## Context-Aware Recovery (Four Strategies, Three Tiers)

Error recovery with the `wfst` feature evaluates four repair strategies at each error
position, with costs adjusted by a three-tier context model:

**Four repair strategies:**
1. **Skip-to-sync** — advance past unexpected tokens to the nearest sync point (cost:
   0.5 per token skipped)
2. **Delete** — remove exactly one unexpected token (cost: 1.0)
3. **Insert** — fabricate a missing sync token at the current position (cost: 2.0)
4. **Substitute** — replace the current token with an expected sync token (cost: 1.5)

**Three context tiers** (multiply base costs):

1. **Frame context** (Tier 1): `FrameKind` (InfixRHS, Group, Collection, etc.),
   nesting depth, and binding power adjust skip/insert/substitute multipliers. Deep
   nesting (depth > 1000) discounts skip to 0.5×; shallow nesting inflates it to 2.0×.

2. **Bracket balance** (Tier 2): `open_parens`, `open_braces`, `open_brackets` counters
   are estimated by scanning consumed tokens. Inserting a matching closer when brackets
   are unmatched gets a 0.3× multiplier — strongly preferred.

3. **Parse simulation** (Tier 3): `ParseSimulator` checks whether a proposed repair
   leads to a valid continuation over a 5-token lookahead window using FIRST/FOLLOW/infix
   sets. Valid continuation: 0.5× multiplier; immediate failure: up to 2.0× penalty.

The generated `wfst_recover_Cat()` function accepts all context parameters (depth,
binding_power, open_parens, open_braces, open_brackets) and evaluates all four strategies
with all three tiers. The minimum-cost repair is applied.

On non-recovering parses, none of this code is exercised — zero overhead on the happy
path.

---

## Benchmark Summary

Full results are in `../../prattail/docs/benchmarks/wfst-pipeline-integration.md`.
Key findings:

| Metric | Result |
|---|---|
| Pipeline overhead, small grammars | +117% (WFST construction dominates) |
| Pipeline overhead, 50+ rules | < 5% (amortised over rule count) |
| Parse-time impact | −12% to +10% (noise from instruction-cache effects) |
| WFST predict latency | ~200 ns |
| WFST recovery latency | ~100 ns |
| WFST construction latency | ~3–5 µs |

The parse-time variance is not statistically significant; weighted dispatch does not
measurably slow or speed up individual parses at current grammar sizes. The benefit is
correctness (correct alternative ordering) rather than throughput.

**Recommendation**: keep WFST features opt-in, not default. Enable `wfst` when grammar
cross-category overlap causes incorrect parse results or excessive backtracking.

---

## Related Documents

- User guide: `../../docs/guides/wfst_features.md`
- Benchmark report: `../../prattail/docs/benchmarks/wfst-pipeline-integration.md`
- Detailed WFST documentation: `../../prattail/docs/experimental/wfst/`

---

**Last Updated**: February 2026
