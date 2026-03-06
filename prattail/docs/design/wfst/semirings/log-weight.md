# LogWeight -- Design & Pipeline Integration

The log semiring `(R+ U {+inf}, log-sum-exp, +, +inf, 0.0)` represents negative
log probabilities: `w = -ln(p)`. Unlike the tropical semiring, LogWeight is
**not idempotent** -- `plus(a, a) = a - ln(2)`, not `a` -- because it sums
probabilities rather than selecting the minimum. This makes it suitable for
forward-backward scoring, N-best extraction, and weight training.

---

## 1. Role in Pipeline

LogWeight is used exclusively in the `wfst-log` feature-gated modules:

| Module               | File                  | Role                                                                    |
|----------------------|-----------------------|-------------------------------------------------------------------------|
| **Forward-backward** | `forward_backward.rs` | Compute total path probabilities to/from each node                      |
| **Log-pushing**      | `log_push.rs`         | Normalize outgoing edges to sum to probability 1                        |
| **Training**         | `training.rs`         | SGD weight learning from parse corpora                                  |
| **WFST override**    | `wfst.rs:367-391`     | `with_trained_weights()` converts trained LogWeights to TropicalWeights |

The flow is: train with LogWeight -> export as `TrainedModel` -> load at
compile time -> override PredictionWfst transitions with TropicalWeight values.

---

## 2. Design Decision: Feature Gating

LogWeight and its dependent modules remain behind `#[cfg(feature = "wfst-log")]`
(`semiring.rs:646-814`, `lib.rs` module declarations):

```rust
#[cfg(feature = "wfst-log")]
pub struct LogWeight(pub f64);
```

**Rationale**:

- **serde + postcard dependencies**: `TrainedModel` requires `serde::Serialize`
  and `serde::Deserialize` plus `postcard` for binary serialization
  (`training.rs:26-27, 279, 307-314`). These are non-trivial compile-time
  dependencies that the standard parsing pipeline does not need.
- **Training is optional**: Most grammars use heuristic weights (specificity,
  priority). Training is an advanced workflow for grammars with high ambiguity
  where heuristics are insufficient.
- **Compilation time**: Adding serde + postcard + training infrastructure
  increases clean build time. Feature gating keeps the default path lean
  (55-second clean build target).

The feature gate applies to:
- `semiring.rs:646-814` -- LogWeight type and Semiring impl
- `forward_backward.rs` -- entire module
- `log_push.rs` -- entire module
- `training.rs` -- entire module
- `wfst.rs:367-391` -- `with_trained_weights()` method

---

## 3. Design Decision: Numerical Stability Threshold

The `log_sum_exp` helper uses a fast-path cutoff at `diff > 20.0`
(`semiring.rs:693-694`):

```rust
let diff = (a - b).abs();
if diff > 20.0 {
    min_val // fast path: correction < 2e-9
} else {
    min_val - (1.0 + (-diff).exp()).ln()
}
```

**Rationale**:

The identity `logsumexp(a, b) = min(a, b) - ln(1 + exp(-|a - b|))` has a
correction term `ln(1 + exp(-diff))` that vanishes exponentially:

| diff | exp(-diff) | correction | relative to min_val                  |
|------|------------|------------|--------------------------------------|
| 10   | 4.5e-5     | 4.5e-5     | negligible                           |
| 15   | 3.1e-7     | 3.1e-7     | negligible                           |
| 20   | 2.1e-9     | 2.1e-9     | below f64 precision for most weights |

At `diff > 20`, the correction contributes less than 2 x 10^-9 nats. Since
weights in PraTTaIL typically range from 0.0 to ~10.0, the relative error is
well below `1e-10` -- far smaller than the `approx_eq` epsilon used in
convergence checks.

The fast path avoids an `exp()` call (typically 20-50 cycles on x86) per
log-sum-exp operation. In forward-backward scoring over large lattices, this
saves significant computation.

**No NaN or Infinity hazards**: The function handles infinity explicitly
(`semiring.rs:685-690`): if either operand is `+inf` (zero element), the other
is returned directly. This prevents `inf - inf = NaN` from the subtraction in
the correction term.

---

## 4. Design Decision: Clamped Weights

Training clamps updated weights to non-negative values (`training.rs:124`):

```rust
let new_val = weight.value() - self.learning_rate * gradient;
*weight = LogWeight::new(new_val.max(0.0)); // clamp to non-negative
```

**Rationale**:

LogWeight represents `-ln(p)` where `p` is in `(0, 1]`. A negative LogWeight
corresponds to `p > 1.0`, which is not a valid probability. This can occur
during SGD when the gradient overshoots:

```
gradient = count_correct - count_all
```

If a rule appears much more in correct parses than in all parses, the gradient
is large and positive, pushing the weight negative. Clamping at 0.0 corresponds
to `p = 1.0` (probability 1), which is the maximum allowable probability.

An alternative approach would be to reduce the learning rate or use gradient
clipping. Clamping is simpler and ensures the weight space remains valid
regardless of learning rate choice.

---

## 5. Pipeline Integration Points

- `training.rs:51-56` -- `RuleWeights`: maps rule labels to LogWeights.
  Key methods: `uniform()` (init to `one()`), `compute_loss()` (negative log
  likelihood), `update()` (SGD with clamping), `train()` (N-epoch loop).
- `forward_backward.rs:33-48, 64-80` -- `forward_scores()` / `backward_scores()`:
  generic over semiring. With LogWeight, forward[i] = total probability mass to
  node i. The partition function is `forward[final_node]`.
- `log_push.rs:32-57` -- `log_push_weights()`: normalizes edge weights in-place
  so outgoing edges at each node sum to probability ~1.0. Uses backward
  potentials: `w' = w + V[q] - V[p]`.
- `wfst.rs:367-391` -- `with_trained_weights()`: converts trained model weights
  to TropicalWeights and injects into the prediction WFST. Both LogWeight and
  TropicalWeight use f64 internally with the same `times` (addition), so raw
  values transfer directly.

---

## 6. TrainedModel Serialization

`TrainedModel` (`training.rs:279-339`) is serialized with postcard (compact
binary format):

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainedModel {
    pub rule_weights: BTreeMap<String, f64>,
    pub recommended_beam_width: Option<f64>,
    pub metadata: TrainedModelMetadata,
}
```

- `save()` / `load()` (`training.rs:306-315`): File I/O with postcard
- `to_embedded()` / `from_embedded()` (`training.rs:321-338`): For `include_bytes!`
  embedding in generated code

**Why postcard, not JSON**: The original implementation used `serde_json`, but
JSON serialization triggered Cranelift NEON intrinsic panics on macOS nightly
aarch64 (Cranelift does not implement all SIMD float intrinsics that serde_json's
float formatting uses). Postcard uses no SIMD float paths and produces smaller
binaries.

Usage in generated code (`training.rs:329-334`):

```rust
static TRAINED_MODEL: LazyLock<TrainedModel> = LazyLock::new(|| {
    TrainedModel::from_embedded(include_bytes!("path/to/model.bin"))
        .expect("embedded model should be valid")
});
```

---

## 7. Weight Strategy Hierarchy

PraTTaIL uses a three-tier weight strategy, where later sources override earlier
ones:

| Tier                     | Source                                                     | Domain                      | Applied When                      |
|--------------------------|------------------------------------------------------------|-----------------------------|-----------------------------------|
| 1. Specificity           | `compute_rule_specificity()` in `prediction.rs:1588-1599`  | TropicalWeight              | Always (default)                  |
| 2. Token priority        | `TropicalWeight::from_priority()` in `semiring.rs:101-103` | TropicalWeight              | Tokens with explicit `priority`   |
| 3. Trained probabilities | `with_trained_weights()` in `wfst.rs:367-391`              | LogWeight -> TropicalWeight | `wfst-log` feature + model loaded |

Tier 1 is the baseline: every rule gets a weight based on structural specificity
(more terminals = lower weight = higher priority).

Tier 2 overrides for tokens with explicitly declared priorities (e.g., keywords
have priority 10, identifiers have priority 1).

Tier 3 overrides with learned weights from a training corpus. The trained
weights are in the LogWeight domain but transfer directly to TropicalWeight
since both represent `-ln(p)`.

---

## 8. Source Reference & See Also

- **Type definition**: `semiring.rs:622-814`
- **Forward-backward**: `forward_backward.rs:17-88`
- **Log-pushing**: `log_push.rs:19-89`
- **Training**: `training.rs:1-339`
- **Trained weight override**: `wfst.rs:367-391`
- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- section 5
- **Tropical weight**: `tropical-weight.md` -- the runtime counterpart
