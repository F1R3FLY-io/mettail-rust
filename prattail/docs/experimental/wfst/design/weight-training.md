# Weight Training

**Feature gate:** `wfst-log`

**Date:** 2026-02-22

Weight training adapts grammar rule weights to a corpus of example inputs.
An untrained grammar assigns every action the same base cost based purely on
action kind (Direct = 0.0, Variable = 2.0, etc.). A trained grammar adjusts
those costs so that rules appearing frequently in correct parses receive lower
weights — making them tried first — while rules that appear rarely receive
higher weights.

The training infrastructure lives in two modules: `training.rs` drives the
SGD loop and serializes the result; `log_push.rs` normalizes the resulting
weights so that beam pruning has consistent semantics across all states. Both
modules require the `wfst-log` feature because they operate in the
log-probability semiring rather than the tropical semiring.

---

## Table of Contents

1. [The Log-Weight Semiring](#1-the-log-weight-semiring)
2. [Training Data Format](#2-training-data-format)
3. [Uniform Initialization](#3-uniform-initialization)
4. [Loss Function](#4-loss-function)
5. [Weight Update Rule (SGD)](#5-weight-update-rule-sgd)
6. [Training Loop](#6-training-loop)
7. [Convergence](#7-convergence)
8. [Recommended Beam Width](#8-recommended-beam-width)
9. [Log-Pushing (Mohri Weight Pushing)](#9-log-pushing-mohri-weight-pushing)
10. [TrainedModel Serialization](#10-trainedmodel-serialization)
11. [Training Data-Flow Pipeline](#11-training-data-flow-pipeline)
12. [Example: 3-Epoch Trace](#12-example-3-epoch-trace)
13. [Source Reference](#13-source-reference)

---

## 1. The Log-Weight Semiring

Training operates over `LogWeight`, the semiring `(ℝ ∪ {−∞}, log-sum-exp, +,
−∞, 0)`:

- **Addition** `a ⊕ b = −ln(e^{−a} + e^{−b})` — numerically stable log-sum-exp
- **Multiplication** `a ⊗ b = a + b` — log-probabilities add
- **Zero** `0̄ = +∞` (log of probability 0 — unreachable)
- **One** `1̄ = 0.0` (log of probability 1.0 — certain)

`LogWeight::is_zero()` checks `value == f64::INFINITY`.
`LogWeight::one()` is `LogWeight::new(0.0)`.

The relationship to probability is `p = exp(−w)`, so `w = 0.0` means
probability 1.0 and `w = 2.0` means probability `e^{−2} ≈ 0.135`.

Training decreases the log-weight of frequently correct rules (increases their
probability). Weights are clamped to `≥ 0.0` to prevent negative log-weights,
which would correspond to probabilities greater than 1.0 and break the semiring
interpretation.

---

## 2. Training Data Format

Each `TrainingExample` records an input string and the sequence of rule labels
that define the correct parse:

```rust
pub struct TrainingExample {
    pub input: String,
    pub expected_rule_labels: Vec<String>,
}
```

For example, parsing `1 + 2 * 3` with standard arithmetic precedence might
produce:

```rust
TrainingExample {
    input: "1 + 2 * 3".to_string(),
    expected_rule_labels: vec![
        "NumLit".to_string(),   // parse 1
        "NumLit".to_string(),   // parse 2
        "Mul".to_string(),      // 2 * 3
        "NumLit".to_string(),   // parse 3
        "Add".to_string(),      // 1 + (2*3)
    ],
}
```

The `input` field is currently informational; the simplified training loop uses
`expected_rule_labels` directly without re-parsing `input`. Full parse-lattice
construction (running the parser over `input` and collecting all parses) is a
planned extension — see the module-level doc comment in `training.rs`.

---

## 3. Uniform Initialization

`RuleWeights::uniform(rule_labels)` creates a weight map where every rule
starts with `LogWeight::one()` (= 0.0 in log space = probability 1.0). This
is a flat prior: no rule is preferred over any other before training.

```rust
let labels = vec!["Add", "Mul", "Lit", "Var"]
    .into_iter().map(String::from).collect::<Vec<_>>();
let mut rw = RuleWeights::uniform(&labels);
```

The default learning rate is 0.1; use `set_learning_rate(lr)` to override.

---

## 4. Loss Function

The loss for one training example is the difference between the negative
log-probability of the correct parse path and the negative log-probability of
the partition function (sum over all paths):

```
correct_weight = ⊗_{r ∈ expected_rule_labels} w[r]
              = sum of log-weights for each rule in the correct parse

total_weight   = ⊕_{r ∈ all_rules} w[r]
              = log-sum-exp of all rule weights

loss = correct_weight.value() − total_weight.value()
```

In probability terms, this is `−ln(P(correct) / P(all))`. When the correct
parse is the most probable one, `correct_weight ≈ total_weight` and `loss ≈ 0`.

The simplified training loop uses a uniform "all" distribution: the total
weight is `⊕` over all rule weights (log-sum-exp). In a full implementation,
the "all" weight would come from the forward probability computed by
`forward_backward.rs` over the complete parse lattice.

---

## 5. Weight Update Rule (SGD)

For each rule label `r`, the gradient is:

```
gradient[r] = expected_count(r, correct) − expected_count(r, all)
```

Where:
- `expected_count(r, correct)` is how many times rule `r` appears in the
  expected parse (from `expected_rule_labels`).
- `expected_count(r, all)` is the uniform expectation: `1.0 / num_rules`
  for each rule in the simplified loop (full implementation: posterior count
  from forward-backward).

The weight update is:

```
w[r] ← max(0.0, w[r] − learning_rate × gradient[r])
```

Rules appearing more in the correct parse than expected (`gradient > 0`) get
decreased log-weight, increasing their probability. Rules appearing less get
increased log-weight (or stay at 0.0 if already clamped). The `max(0.0, …)`
clamp enforces the semiring constraint.

---

## 6. Training Loop

`RuleWeights::train(examples, epochs)` runs the loop:

```
for epoch in 0..epochs:
    epoch_loss = 0.0
    for example in examples:
        1. compute correct_weight from expected_rule_labels
        2. compute total_weight = log-sum-exp of all weights
        3. accumulate expected_counts for correct and all
        4. compute loss
        5. update weights
    epoch_losses.push(epoch_loss / num_examples)
```

The function returns `TrainingStats` containing the per-epoch loss list,
the final loss, a convergence flag, and the recommended beam width. It does
not return the updated weights separately — they are mutated in-place on
`self`.

---

## 7. Convergence

The `converged` flag in `TrainingStats` is set when:

```
|epoch_losses[last] − epoch_losses[last − 1]| < 1e-6
```

This is the default tolerance for the simplified SGD loop. A production
implementation would expose tolerance as a parameter and support early
stopping.

When calling `to_trained_model`, the `epochs` field of `TrainedModelMetadata`
records how many epochs were actually run (length of `epoch_losses`). The
caller should set `metadata.num_examples` manually before saving, since the
training loop does not know the full corpus size at that point.

---

## 8. Recommended Beam Width

After training, `compute_recommended_beam_width` examines the gap between the
correct parse weight and the best possible path weight across all training
examples:

```
for each example:
    correct_weight = Σ w[r] for r in expected_rule_labels
    best_weight    = Σ min(w[*]) for each step in the correct parse
    gap = correct_weight − best_weight

recommended_beam_width = max(all gaps) + safety_margin (0.5)
```

If the correct path is always the best path (gap = 0 for every example), no
beam width recommendation is made — the model has converged to the point where
beam pruning is unnecessary. In this case, `TrainingStats::recommended_beam_width`
is `None`.

The safety margin of 0.5 ensures that the recommended beam is slightly wider
than the observed gap, accommodating test inputs that fall outside the training
distribution.

---

## 9. Log-Pushing (Mohri Weight Pushing)

After training, weights may be locally unnormalized: the sum of outgoing edge
probabilities at a given state may not equal 1.0. This means beam thresholds
are incomparable across states — a threshold of 1.5 may admit 3 actions at one
state but only 1 at another.

`log_push_weights` normalizes the weights using Mohri's weight-pushing
algorithm:

**Algorithm:**

```
1. Compute backward potentials β[q] for each node q:
   β[q] = ⊕_{paths from q to final} (weight of path)
         = log-sum-exp of all path weights from q to sink

   (computed by backward_scores() in forward_backward.rs)

2. For each edge (p, q, w):
   w' = w + β[q] − β[p]

   (in log semiring: times is +, so w' = w.value() + β[q].value() − β[p].value())
```

After pushing, the outgoing edges at every reachable state sum to probability
1.0 in the log semiring:

```
Σ_q exp(−w'(p→q)) = Σ_q exp(−(w(p→q) + β[q] − β[p]))
                   = exp(β[p]) × Σ_q exp(−w(p→q)) × exp(−β[q])
                   = exp(β[p]) × Σ_q exp(−(w(p→q) + β[q]))
                   = exp(β[p]) × exp(−β[p])    [by definition of β[p]]
                   = 1.0
```

**Path weight preservation:** log-pushing does not change the weight of any
complete path from start to sink. It redistributes weight between edges along
each path, but the total path weight is invariant. The relative ordering of
paths is preserved.

`check_normalization(edges, num_nodes)` verifies the result by summing
outgoing edge probabilities at each node and checking deviation from 1.0.
After a correct log-push, the maximum deviation should be below 1e-6.

---

## 10. TrainedModel Serialization

`TrainedModel` is the serialization-ready output of a training run. It
contains the learned weights, the recommended beam width, and provenance
metadata. It serializes to and from JSON via `serde_json`.

**JSON format:**

```json
{
  "rule_weights": {
    "Add":    0.3,
    "Lit":    0.1,
    "Mul":    0.5,
    "Var":    0.8
  },
  "recommended_beam_width": 1.8,
  "metadata": {
    "epochs": 100,
    "final_loss": 0.001,
    "converged": true,
    "num_examples": 500,
    "learning_rate": 0.01
  }
}
```

Weights are stored as raw `f64` values (not wrapped in `LogWeight`).
`recommended_beam_width` is `null` if the correct path was always optimal.

`TrainedModel::save(path)` writes prettified JSON to the given path.
`TrainedModel::load(path)` reads and deserializes the file.
`TrainedModel::from_embedded(json_str)` deserializes from an in-memory
JSON string — designed for use with `include_str!()` to embed the model
in generated code without runtime file I/O.

The `log_semiring_model_path` option in the `language!` DSL points to a saved
`TrainedModel` JSON file. At compile time, the pipeline loads the model and
uses the rule weights to initialize the prediction WFSTs.

---

## 11. Training Data-Flow Pipeline

```
  Corpus of source files
       │
       ▼
  Vec<TrainingExample>
  { input: String,
    expected_rule_labels: Vec<String> }
       │
       ▼
  RuleWeights::uniform(labels)
  (all weights = LogWeight(0.0) = probability 1.0)
       │
       ▼
  rw.set_learning_rate(lr)
       │
       ▼
  rw.train(examples, epochs)
       │
       ├─ per-epoch SGD:
       │   correct_weight ─── log-semiring ×
       │   total_weight   ─── log-sum-exp
       │   gradient       ─── count(correct) − count(all)
       │   update         ─── w -= lr × gradient, clamp ≥ 0
       │
       ▼
  TrainingStats
  { epoch_losses, final_loss,
    converged, recommended_beam_width }
       │
       ▼
  rw.to_trained_model(&stats)
       │
       ▼
  TrainedModel
  { rule_weights, recommended_beam_width, metadata }
       │
       ├──── [optional] log_push_weights(&mut edges, ...)
       │     ← normalize via backward_scores()
       │
       ▼
  model.save("grammar_weights.json")
       │
       ▼
  grammar_weights.json
  ← loaded at compile time by language! { options {
      log_semiring_model_path: "grammar_weights.json" } }
```

---

## 12. Example: 3-Epoch Trace

A tiny grammar with rules `{Add, Mul, Lit}`, two training examples, learning
rate 0.1, and 3 epochs.

**Initial weights** (all `LogWeight(0.0)` = probability 1.0):

| Rule | Epoch 0 weight |
|------|----------------|
| Add  | 0.0            |
| Mul  | 0.0            |
| Lit  | 0.0            |

**Training examples:**

- Example A: `"1 + 2"` → `[Lit, Add, Lit]`
- Example B: `"3 * 4"` → `[Lit, Mul, Lit]`

**Epoch 1 (after processing both examples):**

For example A:
- `correct_weight = w[Lit] + w[Add] + w[Lit] = 0.0`
- `total_weight = log-sum-exp(0.0, 0.0, 0.0) ≈ −1.099` (ln 3 ≈ 1.099)
- `loss ≈ 0.0 − (−1.099) = 1.099`
- `gradient[Lit] = 2 − 1/3 ≈ 1.667`, `gradient[Add] = 1 − 1/3 ≈ 0.667`
- Update: `w[Lit] ← max(0, 0.0 − 0.1 × 1.667) = 0.0` (clamped)
  - `w[Add] ← max(0, 0.0 − 0.1 × 0.667) = 0.0` (clamped)

For example B (symmetric, Mul updated similarly).

After epoch 1, all weights remain at 0.0 because the clamp prevents them from
going negative. In practice, once some rules drift above 0.0 through different
gradient signs (e.g., rules that appear in "all" but not in "correct"), the
more-correct rules can pull ahead.

**Epoch 2 and 3:** The weights stabilize near 0.0 for this small example
since all rules appear roughly uniformly in the corpus. With a larger corpus
where some rules dominate, weights diverge more clearly.

| Rule | Epoch 1 | Epoch 2 | Epoch 3 |
|------|---------|---------|---------|
| Add  | 0.0     | 0.0     | 0.0     |
| Mul  | 0.0     | 0.0     | 0.0     |
| Lit  | 0.0     | 0.0     | 0.0     |

`converged = true` at epoch 3 (|Δloss| < 1e-6).
`recommended_beam_width = None` (correct path = best path).

This small example shows that the clamp and uniform corpus lead to a "neutral"
model. The training becomes more informative when the corpus has skewed rule
distributions (some rules much more frequent than others).

---

## 13. Source Reference

| Symbol | Location |
|--------|----------|
| `RuleWeights` | `prattail/src/training.rs` |
| `TrainingExample` | `prattail/src/training.rs` |
| `TrainingStats` | `prattail/src/training.rs` |
| `TrainedModel` | `prattail/src/training.rs` |
| `TrainedModelMetadata` | `prattail/src/training.rs` |
| `log_push_weights` | `prattail/src/log_push.rs` |
| `check_normalization` | `prattail/src/log_push.rs` |
| `backward_scores` | `prattail/src/forward_backward.rs` |
| `LogWeight` | `prattail/src/automata/semiring.rs` |

Test counts: 12 (training.rs) + 2 (log_push.rs).

See also:
- [../theory/semirings.md](../theory/semirings.md) — log-probability semiring axioms
- [../theory/viterbi-and-forward-backward.md](../theory/viterbi-and-forward-backward.md) — posterior computation
- [prediction.md](prediction.md) — how trained weights feed the prediction WFST
- [error-recovery.md](error-recovery.md) — recovery cost model (tropical, not log)
