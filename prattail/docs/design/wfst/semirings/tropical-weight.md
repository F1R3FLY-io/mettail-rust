# TropicalWeight -- Design & Pipeline Integration

The tropical semiring `(R+ U {+inf}, min, +, +inf, 0.0)` is PraTTaIL's primary
weight type. Every weighted decision in the pipeline -- prediction, dispatch,
beam pruning, Viterbi shortest-path, and error-recovery costing -- flows through
`TropicalWeight`. Lower weight means higher priority.

---

## 1. Role in Pipeline

TropicalWeight participates in every major pipeline stage:

| Stage                      | Role                                                    |
|----------------------------|---------------------------------------------------------|
| **Prediction WFST**        | Transition weights rank dispatch alternatives           |
| **Dispatch arm ordering**  | Arms sorted by weight; lowest emitted first             |
| **Beam pruning**           | Threshold = `best + beam_width` prunes unlikely actions |
| **Viterbi best-path**      | Shortest path through token lattice                     |
| **Error recovery**         | Repair action costs (skip, delete, insert, substitute)  |
| **Static CSR embedding**   | Weights serialized as `f64` in codegen arrays           |
| **Trained model override** | Log-probabilities from training replace heuristics      |

---

## 2. Design Decision: f64 Representation

TropicalWeight wraps a bare `f64` (`semiring.rs:69`):

```rust
pub struct TropicalWeight(pub f64);
```

**Rationale**:

- **Flexibility**: Weight arithmetic (addition for path accumulation, comparison
  for min-selection) maps directly to IEEE 754 addition and comparison.
- **Log-probability domain**: Trained weights from LogWeight naturally convert to
  TropicalWeight without precision loss or rescaling.
- **Infinity**: `f64::INFINITY` represents the additive identity (unreachable)
  natively -- no sentinel values or Option wrappers needed.
- **Fixed-point rejected**: Fixed-point would require choosing a denominator and
  handling saturation at every arithmetic site. The precision benefits do not
  justify the complexity for compile-time codegen weights.

---

## 3. Design Decision: total_cmp Ordering

`PartialEq`, `Ord`, and `Hash` all use `f64::total_cmp` (`semiring.rs:170-192`):

```rust
impl PartialEq for TropicalWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Ord for TropicalWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}
```

**Rationale**:

- `f64::total_cmp` provides a total ordering over all f64 bit patterns,
  including NaN. Standard `partial_cmp` returns `None` for NaN, which would
  panic in `sort_by_key` or corrupt BTreeMap invariants.
- Branchless: `total_cmp` compiles to a single integer comparison on the
  reinterpreted bits (with sign fixup), avoiding conditional branches.
- Hash consistency: `to_bits()` hashing matches `total_cmp` equality -- the
  contract `a == b => hash(a) == hash(b)` is satisfied.

---

## 4. Design Decision: Priority Inversion

`from_priority()` inverts the priority scale (`semiring.rs:101-103`):

```rust
pub fn from_priority(priority: u8) -> Self {
    TropicalWeight((10.0_f64) - priority as f64)
}
```

**Rationale**:

- PraTTaIL's `TokenKind::priority()` uses higher numbers for higher priority
  (e.g., keywords = 10, identifiers = 1).
- The tropical semiring selects the minimum (via `plus = min`). Inversion maps
  high priority to low weight, making min-selection natural.
- The constant 10.0 is `MAX_PRIORITY`. All priority values are in `[0, 10]`, so
  all weights land in `[0.0, 10.0]` -- well within f64 precision.

---

## 5. Pipeline Integration Points

Exhaustive file and line references for TropicalWeight usage:

| File            | Lines                                  | Usage                                                                                                                       |
|-----------------|----------------------------------------|-----------------------------------------------------------------------------------------------------------------------------|
| `semiring.rs`   | 57-198                                 | Type definition, Semiring impl, Ord, Hash, Default                                                                          |
| `wfst.rs`       | 55, 66, 95-100, 131, 272, 378-379      | WeightedTransition.weight, WfstState.final_weight, WeightedAction.weight, beam_width field, with_trained_weights            |
| `recovery.rs`   | 176, 394, 402                          | RepairResult.cost, viterbi_recovery, viterbi_recovery_beam                                                                  |
| `lattice.rs`    | 37, 240, 343, 359, 371, 449            | Default generic param on TokenLattice/LatticeEdge/ViterbiPath, viterbi_best_path, viterbi_best_path_beam                    |
| `prediction.rs` | 1540-1543, 1718-1738, 1749-1777        | Composed entry weight sorting, resolve_dispatch_winners weight propagation, build_complete_weight_map                       |
| `pipeline.rs`   | 545-548, 638-643, 1137-1147, 1187-1278 | Beam width application, static CSR emission, format_f64 helper, LazyLock constructors                                       |
| `dispatch.rs`   | 55, 79, 162-169, 226-238, 309-310      | WeightedAction references, dispatch_arms Vec<(String, f64)>, WFST predict() for ambiguous arm sorting, final sort by weight |

---

## 6. Weight Assignment Strategy

Weights assigned during `build_prediction_wfsts()` (`wfst.rs:483-498`):

| DispatchAction                     | Weight      | Rationale                                                 |
|------------------------------------|-------------|-----------------------------------------------------------|
| `Direct` (unique token)            | 0.0         | Deterministic -- no alternatives to consider              |
| `Grouping`                         | 0.0         | Structural grouping `(`, `{`, `[` is always deterministic |
| `CrossCategory` (unique to source) | 0.0         | Token uniquely identifies cross-category path             |
| `CrossCategory` (shared)           | 0.5         | Ambiguous -- try cross-category first (explicit rule)     |
| `Cast` (unique to source)          | 0.5         | Cast less specific than direct; try after direct          |
| `Lookahead` (ident)                | 1.0 + order | Multi-rule ident-lookahead; order breaks ties             |
| `Variable` (fallback)              | 2.0         | Last resort when no structural token matches              |

The hierarchy ensures that during codegen, `dispatch_arms.sort_by(weight)`
places the most-likely arms first, improving CPU branch prediction hit rate
without any runtime cost.

Specificity-based weights for deterministic tokens are computed in
`build_complete_weight_map()` (`prediction.rs:1749`):

```
weight = 1.0 / (1.0 + terminals + 0.5 * nonterminals)
```

More structurally specific rules (more terminals) get lower weight.

---

## 7. Beam Pruning Design

The `PredictionWfst` carries an optional beam width (`wfst.rs:131`):

```rust
pub beam_width: Option<TropicalWeight>,
```

Pruning semantics in `predict_pruned()` (`wfst.rs:179-191`):

```rust
let threshold = best.weight.value() + beam.value();
actions.into_iter()
    .filter(|a| a.weight.value() <= threshold)
    .collect()
```

An action passes if `weight <= best + beam_width`. This eliminates
low-probability alternatives from codegen without requiring a global ranking.

Configuration flows through the DSL:

1. `language! { options { beam_width: 1.5 } }` -- parsed in macros crate
2. `BeamWidthConfig::Explicit(1.5)` stored in `ParserBundle` (`pipeline.rs:79`)
3. Applied to all WFSTs in `generate_parser_code()` (`pipeline.rs:545-548`)
4. Serialized to `WFST_BEAM_WIDTH_Cat` static (`pipeline.rs:1252-1263`)

---

## 8. Source Reference & See Also

- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- sections 1-4
  (tropical semiring formal definition, axioms, proofs)
- **Pipeline integration**: `prattail/docs/benchmarks/wfst-pipeline-integration.md`
- **Counting semiring**: `counting-weight.md` -- ambiguity detection companion
- **Edit semiring**: `edit-weight.md` -- discrete repair costs
- **Product semiring**: `product-weight.md` -- joint Tropical x Edit optimization
- **Log semiring**: `log-weight.md` -- training and forward-backward
