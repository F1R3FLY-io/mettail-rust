# Training Guide

The training subsystem lives in `prattail/src/training.rs` and is gated
behind the `wfst-log` feature. It implements a supervised SGD weight-learning
loop that takes a corpus of annotated parse examples, adjusts rule weights
toward those that appear more often in correct parses than in the average-case
parse, and serializes the result to a `TrainedModel` JSON file. That file can
then be referenced from the `language!` DSL via `log_semiring_model_path`.

> **Feature requirement:** all APIs in this section require
> `--features wfst-log`. If only `--features wfst` is active, the
> `training` module is not compiled.

---

## 1. Conceptual Background

Every grammar rule is assigned a weight in the log-probability semiring.
`LogWeight` stores `−ln(p)`, so lower values correspond to higher
probability. Uniform initialization sets every weight to `LogWeight::one()`
(`−ln(1.0) = 0.0`), meaning all rules start as equally likely.

Training nudges weights via the gradient of the per-example loss:

```
loss(example) = correct_path_weight − total_weight
```

where both quantities are sums of `LogWeight` values (negated log-probabilities).
A gradient step for rule `r` reads:

```
gradient[r] = expected_count(r, correct) − expected_count(r, all)
weight[r]   ← weight[r] − learning_rate × gradient[r]
              (clamped to 0.0 to stay in valid log-probability range)
```

Rules that appear more often in correct parses than in the overall average
receive a smaller (more probable) weight; rules that appear less often are
pushed toward larger (less probable) values.

> **Current status — experimental:** full forward-backward parse-lattice
> construction is a research TODO. The current implementation supplies rule
> counts directly from `TrainingExample::expected_rule_labels` and uses a
> uniform approximation for the "all parses" distribution. The interface and
> serialization format are stable; the accuracy of the learned weights will
> improve as the lattice construction is completed.

---

## 2. End-to-End Workflow

The numbered steps below map directly to the workflow diagram in
[Section 9](#9-workflow-diagram).

### Step 1 — Assemble a training corpus

Collect input strings and the sequence of rule labels that constitute the
correct parse for each. Rule labels are the constructor names defined in the
`terms { }` block of the grammar.

```rust
use mettail_prattail::training::TrainingExample;

let examples = vec![
    TrainingExample {
        input: "1 + 2".to_string(),
        expected_rule_labels: vec!["Num".to_string(), "Add".to_string(), "Num".to_string()],
    },
    TrainingExample {
        input: "3 * 4".to_string(),
        expected_rule_labels: vec!["Num".to_string(), "Mul".to_string(), "Num".to_string()],
    },
    TrainingExample {
        input: "x".to_string(),
        expected_rule_labels: vec!["Var".to_string()],
    },
];
```

### Step 2 — Initialise weights

`RuleWeights::uniform` accepts a slice of rule-label strings and sets every
weight to `LogWeight::one()` (probability 1.0, cost 0.0):

```rust
use mettail_prattail::training::RuleWeights;

let rule_labels: Vec<String> = vec!["Add", "Mul", "Num", "Var"]
    .into_iter()
    .map(String::from)
    .collect();

let mut weights = RuleWeights::uniform(&rule_labels);
```

The label list must include every rule that may appear in the training corpus.
Labels absent from the list are treated as having weight `LogWeight::one()`
by the `get()` accessor but are not updated during training.

### Step 3 — Optionally adjust the learning rate

The default learning rate is `0.1`. A smaller value converges more slowly but
more stably; a larger value converges faster but may oscillate.

```rust
weights.set_learning_rate(0.01);
```

Query the current rate at any time with `weights.learning_rate()`.

### Step 4 — Run the training loop

`RuleWeights::train` runs the full epoch loop and returns a `TrainingStats`
record. The second argument is the number of epochs; the call blocks until
all epochs complete.

```rust
let stats = weights.train(&examples, 100);

println!("Converged:            {}", stats.converged);
println!("Final loss:           {:.6}", stats.final_loss);
println!("Epochs completed:     {}", stats.epoch_losses.len());

if let Some(bw) = stats.recommended_beam_width {
    println!("Recommended beam:     {:.2}", bw.value());
} else {
    println!("Recommended beam:     none (correct path was always optimal)");
}
```

`converged` is `true` when the absolute change in per-example loss between
the last two epochs falls below `1e-6`. You may inspect
`stats.epoch_losses` to plot the learning curve.

The `recommended_beam_width` is a `TropicalWeight` derived as:

```
max over examples of (correct_path_weight − best_single_rule_weight)
                    + 0.5  (safety margin)
```

If the correct path was always the minimum-cost path, this field is `None`.

### Step 5 — Convert to a serializable model

`to_trained_model` packages the trained weights and the stats record into a
`TrainedModel` that can be written to JSON. The `num_examples` field in the
metadata must be set by the caller because `RuleWeights` does not retain the
examples after training.

```rust
use mettail_prattail::training::TrainedModel;

let mut model = weights.to_trained_model(&stats);
model.metadata.num_examples = examples.len();
```

### Step 6 — Save to disk

```rust
model.save("models/calc_model.json").expect("failed to save trained model");
```

`save` serializes to pretty-printed JSON using `serde_json::to_string_pretty`.
The file is written atomically (write to path directly; no temp-file swap in
the current implementation).

To verify the round-trip:

```rust
let loaded = TrainedModel::load("models/calc_model.json")
    .expect("failed to load trained model");

assert_eq!(loaded.rule_weights, model.rule_weights);
```

### Step 7 — Reference in the DSL

```rust
language! {
    name: Calculator,
    options {
        beam_width: auto,
        log_semiring_model_path: "models/calc_model.json",
    }
    // ...
}
```

At macro expansion time the pipeline reads `recommended_beam_width` from the
JSON file and uses it as the effective `BeamWidthConfig::Explicit(w)`. If the
model carries no recommendation (field is `null`), the option degrades to
`BeamWidthConfig::Disabled`.

---

## 3. API Reference

### 3.1 `TrainingExample`

```rust
pub struct TrainingExample {
    pub input: String,
    pub expected_rule_labels: Vec<String>,
}
```

The `input` field is unused by the current training loop (it is stored for
provenance); only `expected_rule_labels` drives the weight update.

### 3.2 `RuleWeights`

| Method                               | Description                                       |
|--------------------------------------|---------------------------------------------------|
| `uniform(labels: &[String]) -> Self` | Initialise all weights to `LogWeight::one()`      |
| `set_learning_rate(lr: f64)`         | Override the default `0.1` learning rate          |
| `learning_rate() -> f64`             | Query the current learning rate                   |
| `get(label: &str) -> LogWeight`      | Look up the weight for a rule                     |
| `set(label: &str, w: LogWeight)`     | Manually override a rule's weight                 |
| `compute_loss(correct, total) -> f64`| Compute per-example loss in the log domain        |
| `update(expected_correct, expected_all)` | One gradient step over pre-computed counts    |
| `train(examples, epochs) -> TrainingStats` | Full epoch loop                             |
| `to_trained_model(stats) -> TrainedModel` | Package weights for serialization           |

### 3.3 `TrainingStats`

```rust
pub struct TrainingStats {
    pub epoch_losses: Vec<f64>,          // loss at end of each epoch
    pub final_loss: f64,                 // == epoch_losses.last()
    pub converged: bool,                 // |loss[n-1] - loss[n]| < 1e-6
    pub recommended_beam_width: Option<TropicalWeight>,
}
```

### 3.4 `TrainedModel`

```rust
pub struct TrainedModel {
    pub rule_weights: BTreeMap<String, f64>,    // rule label → weight value
    pub recommended_beam_width: Option<f64>,    // from training stats
    pub metadata: TrainedModelMetadata,
}
```

```rust
pub struct TrainedModelMetadata {
    pub epochs: usize,
    pub final_loss: f64,
    pub converged: bool,
    pub num_examples: usize,    // must be set by caller after to_trained_model()
    pub learning_rate: f64,
}
```

| Method                         | Description                                 |
|--------------------------------|---------------------------------------------|
| `save(path: &str) -> io::Result<()>`  | Serialize to pretty-printed JSON     |
| `load(path: &str) -> io::Result<Self>`| Deserialize from JSON file           |

---

## 4. Practical Tips

**Start with the default learning rate.** `0.1` is aggressive; if loss
oscillates between epochs rather than decreasing monotonically, drop to
`0.01` or `0.001`.

**More examples improve generalisation.** The current uniform-all-parses
approximation benefits from diversity: include examples that exercise each
rule at least a few times, and vary structural depth.

**Watch `epoch_losses` for plateaus.** If the loss stops decreasing well
before the requested epoch count, the model has converged early. Use
`stats.converged` as a programmatic check or inspect the vector:

```rust
for (epoch, loss) in stats.epoch_losses.iter().enumerate() {
    println!("Epoch {:>4}: {:.6}", epoch + 1, loss);
}
```

**Use `recommended_beam_width` as a starting point.** The value is computed
conservatively (max gap + 0.5 safety margin). If parse speed matters more
than recall, try halving it. If error recovery is missing valid parses, try
increasing it by 0.5.

**Log-pushing is automatic.** The `log_push` module (`wfst-log` tier)
normalizes WFST weights during pipeline construction so that beam pruning
operates on a comparable scale regardless of the absolute magnitude of the
trained weights. You do not need to call log-push explicitly.

**Versioning model files.** Embed metadata provenance in the JSON by
setting `num_examples`, `learning_rate`, and `epochs` accurately. The JSON
schema is stable across patch versions of PraTTaIL; new fields may be added
with defaults to maintain backward compatibility.

---

## 5. Manual Weight Update (Advanced)

`train()` is a convenience wrapper. For custom training loops — early
stopping, learning-rate scheduling, evaluation on a held-out set — use
`compute_loss` and `update` directly:

```rust
let mut best_loss = f64::INFINITY;
let mut patience = 0;
let max_patience = 10;

for epoch in 0..1000 {
    let mut epoch_loss = 0.0;

    for example in &examples {
        // Build expected rule counts from the correct parse
        let mut expected_correct = std::collections::BTreeMap::new();
        for label in &example.expected_rule_labels {
            *expected_correct.entry(label.clone()).or_insert(0.0) += 1.0;
        }

        // Uniform approximation for all-parses distribution
        let n = weights.learning_rate(); // borrow hack — just for illustration
        let _ = n; // silence unused warning in doc example

        // Compute loss and update
        // (In production, supply real forward-backward counts from the lattice)
        weights.update(&expected_correct, &std::collections::BTreeMap::new());
        epoch_loss += 0.0; // placeholder
    }

    // Early stopping
    if epoch_loss < best_loss - 1e-6 {
        best_loss = epoch_loss;
        patience = 0;
    } else {
        patience += 1;
        if patience >= max_patience {
            println!("Early stopping at epoch {}", epoch + 1);
            break;
        }
    }
}
```

---

## 6. Complete Working Example

```rust
#[cfg(feature = "wfst-log")]
fn train_and_save() {
    use mettail_prattail::training::{RuleWeights, TrainingExample};

    // Step 1: corpus
    let examples = vec![
        TrainingExample {
            input: "1 + 2".to_string(),
            expected_rule_labels: vec![
                "Num".to_string(), "Add".to_string(), "Num".to_string(),
            ],
        },
        TrainingExample {
            input: "3 * 4".to_string(),
            expected_rule_labels: vec![
                "Num".to_string(), "Mul".to_string(), "Num".to_string(),
            ],
        },
    ];

    // Step 2: initialise
    let labels: Vec<String> = vec!["Add", "Mul", "Num", "Var"]
        .into_iter()
        .map(String::from)
        .collect();
    let mut weights = RuleWeights::uniform(&labels);

    // Step 3: tune learning rate
    weights.set_learning_rate(0.01);

    // Step 4: train
    let stats = weights.train(&examples, 100);
    assert!(!stats.final_loss.is_nan());

    // Step 5: build model
    let mut model = weights.to_trained_model(&stats);
    model.metadata.num_examples = examples.len();

    // Step 6: save
    model.save("models/calc_model.json")
        .expect("failed to save model");

    // Verify round-trip
    let loaded = mettail_prattail::training::TrainedModel::load("models/calc_model.json")
        .expect("failed to load model");
    assert_eq!(loaded.rule_weights, model.rule_weights);
}
```

---

## 7. Runtime Model Consumption

In addition to compile-time model loading via `log_semiring_model_path`,
trained models can be embedded directly into generated code for runtime
weight override.

### 7.1 `TrainedModel::from_embedded()`

The `from_embedded()` method deserializes a `TrainedModel` from a JSON
string, intended for use with `include_str!()`:

```rust
use mettail_prattail::training::TrainedModel;

let model = TrainedModel::from_embedded(include_str!("models/calc_model.json"))
    .expect("invalid model JSON");
```

### 7.2 Applying Trained Weights at Runtime

Once loaded, the trained model's weights override the heuristic weights
in a `PredictionWfst` via `with_trained_weights()`:

```rust
use mettail_prattail::wfst::PredictionWfst;

let mut wfst = PredictionWfst::from_flat(/* ... */);
wfst.with_trained_weights(&model);
// Now predict() returns results ordered by trained weights
```

This means trained weights affect **runtime dispatch** — not just the next
recompilation. The pipeline embeds both the WFST and the model as static
data, so no file I/O is needed at parse time.

### 7.3 Static Embedding Pattern

The pipeline can generate code like:

```rust
static TRAINED_MODEL: LazyLock<TrainedModel> = LazyLock::new(|| {
    TrainedModel::from_embedded(include_str!("path/to/model.json"))
        .expect("invalid trained model JSON")
});
```

On first use, the model is deserialized and its weights are applied to the
prediction WFST. Subsequent calls to `predict()` use the trained weights
without any additional overhead.

---

## 8. Frequently Asked Questions

**Can I retrain from an existing model?**
Not directly via the current API. Load the JSON, reconstruct `RuleWeights`
by calling `weights.set(label, LogWeight::new(*v))` for each entry in
`rule_weights`, then run `train()` again.

**Does the order of labels passed to `uniform()` matter?**
No. Internally weights are stored in a `BTreeMap<String, LogWeight>`;
iteration order is alphabetical and does not affect correctness.

**What happens if a rule label in a `TrainingExample` is not in the weight map?**
`get()` returns `LogWeight::one()` (weight 0.0) for unknown labels and the
update loop skips them (gradient is zero). This is safe but potentially
wasteful; add all expected labels to the initialisation call.

**Is training thread-safe?**
`RuleWeights` contains a `BTreeMap` and is not `Sync`. Run training
sequentially or use a per-thread copy and merge afterward.

---

## 9. Source Location

All types and functions documented here live in:

```
prattail/src/training.rs
```

The log-push normalisation that complements training is in:

```
prattail/src/log_push.rs
```

Both files are compiled only under `#[cfg(feature = "wfst-log")]`.

---

## 10. Workflow Diagram

The seven numbered steps form a linear pipeline. The horizontal boundary
below the diagram marks the divide between offline training (steps 1–6) and
compile-time DSL consumption (step 7). Dotted verticals (┊) mark where
data crosses that boundary.

```
  ① Corpus                   raw (input, label-sequence) pairs
       │
       ▼
  ② TrainingExamples         Vec<TrainingExample> structs
       │
       ▼
  ③ RuleWeights::uniform()   all weights = LogWeight::one()
       │
       ▼
  ④ train(examples, epochs)  SGD loop → TrainingStats
       │
       ▼
  ⑤ to_trained_model(&stats) TrainedModel { rule_weights, recommended_beam_width, metadata }
       │
       ▼
  ⑥ model.save("model.json") pretty-printed JSON on disk
       ┊
  ╌╌╌╌┊╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌  compile-time boundary  ╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌
       ┊
       ▼
  ⑦ DSL: log_semiring_model_path: "model.json"
         beam_width: auto
         → pipeline reads model → Explicit(recommended_beam_width)
```

---

## 11. Cross-References

- [usage/feature-gates.md](feature-gates.md) — enabling `wfst-log`, test counts per tier
- [usage/dsl-configuration.md](dsl-configuration.md) — `beam_width: auto` and
  `log_semiring_model_path` option semantics
- [theory/viterbi-and-forward-backward.md](../theory/viterbi-and-forward-backward.md) — the forward-backward
  algorithm underlying expected rule counts
- `BeamWidthConfig::Auto` resolution at pipeline time is documented in
  [usage/dsl-configuration.md](dsl-configuration.md)
