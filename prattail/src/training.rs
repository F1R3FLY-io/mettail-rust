//! Experimental weight training loop for PraTTaIL grammars.
//!
//! Provides infrastructure for learning grammar rule weights from a corpus
//! of training examples. The training loop:
//!
//! 1. For each example, builds a lattice of all possible parses (using `LogWeight`).
//! 2. Computes forward-backward scores over the lattice.
//! 3. Extracts expected rule counts for correct parse vs all parses.
//! 4. Updates weights via SGD.
//!
//! ## Trained Model Serialization
//!
//! After training, rule weights and metadata are serialized to JSON via
//! `TrainedModel`. This model can be loaded at compile time by the
//! `language!` DSL via the `log_semiring_model_path` option.
//!
//! ## Experimental Status
//!
//! The interface for constructing "all possible parses" lattices from PraTTaIL's
//! Pratt parser is a research question. The current implementation provides the
//! weight infrastructure; parse-lattice construction is a TODO that returns
//! manually-specified lattices for testing.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::automata::semiring::{LogWeight, Semiring, TropicalWeight};

// ══════════════════════════════════════════════════════════════════════════════
// Training example
// ══════════════════════════════════════════════════════════════════════════════

/// A training example: input text + expected parse result.
#[derive(Debug, Clone)]
pub struct TrainingExample {
    /// The input text to parse.
    pub input: String,
    /// Sequence of rule labels applied in the correct parse.
    pub expected_rule_labels: Vec<String>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Rule weights
// ══════════════════════════════════════════════════════════════════════════════

/// Trainable rule weights: each rule label maps to a `LogWeight`.
///
/// Lower weight = higher probability (since `LogWeight` = negative log probability).
#[derive(Debug, Clone)]
pub struct RuleWeights {
    /// Rule label → weight.
    weights: BTreeMap<String, LogWeight>,
    /// SGD learning rate.
    learning_rate: f64,
}

impl RuleWeights {
    /// Initialize all weights to uniform (`LogWeight::one()` = probability 1.0).
    pub fn uniform(rule_labels: &[String]) -> Self {
        let weights = rule_labels
            .iter()
            .map(|label| (label.clone(), LogWeight::one()))
            .collect();
        RuleWeights { weights, learning_rate: 0.1 }
    }

    /// Set the learning rate for SGD.
    pub fn set_learning_rate(&mut self, lr: f64) {
        self.learning_rate = lr;
    }

    /// Get the current learning rate.
    pub fn learning_rate(&self) -> f64 {
        self.learning_rate
    }

    /// Get the weight for a rule.
    pub fn get(&self, label: &str) -> LogWeight {
        self.weights.get(label).copied().unwrap_or(LogWeight::one())
    }

    /// Set the weight for a rule.
    pub fn set(&mut self, label: &str, weight: LogWeight) {
        self.weights.insert(label.to_string(), weight);
    }

    /// Compute loss for one example: `-log P(correct) / P(all)`.
    ///
    /// In the log semiring:
    /// `loss = correct_path_weight - total_weight`
    /// (since `LogWeight` represents `-ln(p)`, the ratio becomes a difference).
    pub fn compute_loss(&self, correct_path_weight: LogWeight, total_weight: LogWeight) -> f64 {
        if total_weight.is_zero() {
            return f64::INFINITY;
        }
        // loss = -ln(P(correct)/P(all)) = correct - total
        // Since these are negative log probs, correct >= total always
        correct_path_weight.value() - total_weight.value()
    }

    /// Update weights via gradient from forward-backward expected counts.
    ///
    /// For each rule `r`:
    /// ```text
    /// gradient[r] = expected_count(r, correct) - expected_count(r, all)
    /// weight[r] -= learning_rate * gradient[r]
    /// ```
    ///
    /// This pushes weights toward rules that appear more in correct parses
    /// than in all parses.
    pub fn update(
        &mut self,
        expected_correct: &BTreeMap<String, f64>,
        expected_all: &BTreeMap<String, f64>,
    ) {
        for (label, weight) in self.weights.iter_mut() {
            let count_correct = expected_correct.get(label).copied().unwrap_or(0.0);
            let count_all = expected_all.get(label).copied().unwrap_or(0.0);
            let gradient = count_correct - count_all;
            // Update: w -= lr * gradient
            // Negative gradient → more in correct → decrease weight (= increase probability)
            let new_val = weight.value() - self.learning_rate * gradient;
            *weight = LogWeight::new(new_val.max(0.0)); // clamp to non-negative
        }
    }

    /// Train over a corpus for N epochs.
    ///
    /// This is a simplified training loop that uses rule counts directly
    /// (the full forward-backward lattice construction is a TODO).
    ///
    /// For each example, the "correct" counts are the rule labels in the
    /// expected parse, and the "all" counts are uniform (1.0 for every rule).
    pub fn train(&mut self, examples: &[TrainingExample], epochs: usize) -> TrainingStats {
        let mut epoch_losses = Vec::with_capacity(epochs);
        let num_rules = self.weights.len();

        for _epoch in 0..epochs {
            let mut epoch_loss = 0.0;

            for example in examples {
                // Compute correct path weight: sum of weights for expected rules
                let mut correct_weight = LogWeight::one();
                let mut expected_counts: BTreeMap<String, f64> = BTreeMap::new();
                for label in &example.expected_rule_labels {
                    correct_weight = correct_weight.times(&self.get(label));
                    *expected_counts.entry(label.clone()).or_insert(0.0) += 1.0;
                }

                // Simplified "all" path weight: assume uniform over all rules
                // In a real implementation, this would come from forward-backward
                let all_counts: BTreeMap<String, f64> = self
                    .weights
                    .keys()
                    .map(|k| (k.clone(), 1.0 / num_rules as f64))
                    .collect();

                // Total weight approximation (sum of all rule weights for one step)
                let mut total = LogWeight::zero();
                for w in self.weights.values() {
                    total = total.plus(w);
                }

                let loss = self.compute_loss(correct_weight, total);
                epoch_loss += loss;

                self.update(&expected_counts, &all_counts);
            }

            epoch_losses.push(epoch_loss / examples.len() as f64);
        }

        let final_loss = epoch_losses.last().copied().unwrap_or(f64::INFINITY);
        let converged = epoch_losses.len() >= 2
            && (epoch_losses[epoch_losses.len() - 2] - final_loss).abs() < 1e-6;

        // Compute recommended beam width
        let recommended_beam_width = self.compute_recommended_beam_width(examples);

        TrainingStats {
            epoch_losses,
            final_loss,
            converged,
            recommended_beam_width,
        }
    }

    /// Compute recommended beam width from training data.
    ///
    /// `max(correct_path_weight - best_path_weight)` across all examples,
    /// plus a safety margin (default 0.5).
    fn compute_recommended_beam_width(
        &self,
        examples: &[TrainingExample],
    ) -> Option<TropicalWeight> {
        let safety_margin = 0.5;
        let mut max_gap = 0.0_f64;
        let mut any_gap = false;

        for example in examples {
            // Correct path weight
            let mut correct_weight = 0.0;
            for label in &example.expected_rule_labels {
                correct_weight += self.get(label).value();
            }

            // Best path weight = minimum weight rule for each step
            let mut best_weight = 0.0;
            for _ in &example.expected_rule_labels {
                let min_w = self
                    .weights
                    .values()
                    .map(|w| w.value())
                    .fold(f64::INFINITY, f64::min);
                best_weight += min_w;
            }

            let gap = correct_weight - best_weight;
            if gap > 0.0 {
                max_gap = max_gap.max(gap);
                any_gap = true;
            }
        }

        if any_gap {
            Some(TropicalWeight::new(max_gap + safety_margin))
        } else {
            None // correct path was always the best path
        }
    }

    /// Export to a serializable `TrainedModel` after training.
    pub fn to_trained_model(&self, stats: &TrainingStats) -> TrainedModel {
        TrainedModel {
            rule_weights: self
                .weights
                .iter()
                .map(|(k, v)| (k.clone(), v.value()))
                .collect(),
            recommended_beam_width: stats.recommended_beam_width.map(|w| w.value()),
            metadata: TrainedModelMetadata {
                epochs: stats.epoch_losses.len(),
                final_loss: stats.final_loss,
                converged: stats.converged,
                num_examples: 0, // filled by caller
                learning_rate: self.learning_rate,
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Training statistics
// ══════════════════════════════════════════════════════════════════════════════

/// Statistics from a training run.
#[derive(Debug, Clone)]
pub struct TrainingStats {
    /// Loss at the end of each epoch.
    pub epoch_losses: Vec<f64>,
    /// Loss at the final epoch.
    pub final_loss: f64,
    /// Whether the training converged (loss change < threshold).
    pub converged: bool,
    /// Recommended beam width derived from training data.
    ///
    /// Computed as `max(correct_path_weight - best_path_weight)` across all
    /// training examples, plus a configurable safety margin (default 0.5).
    /// `None` if the correct path was always the best path.
    pub recommended_beam_width: Option<TropicalWeight>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Trained model serialization
// ══════════════════════════════════════════════════════════════════════════════

/// Serializable trained model — produced by training, consumed by `language!` DSL.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainedModel {
    /// Learned rule weights: rule label → weight value (f64).
    pub rule_weights: BTreeMap<String, f64>,
    /// Recommended beam width derived from training data.
    pub recommended_beam_width: Option<f64>,
    /// Training metadata for provenance.
    pub metadata: TrainedModelMetadata,
}

/// Metadata about a training run, for provenance tracking.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainedModelMetadata {
    /// Number of epochs trained.
    pub epochs: usize,
    /// Final epoch loss.
    pub final_loss: f64,
    /// Whether training converged.
    pub converged: bool,
    /// Number of training examples.
    pub num_examples: usize,
    /// Learning rate used.
    pub learning_rate: f64,
}

impl TrainedModel {
    /// Save trained model to JSON file.
    pub fn save(&self, path: &str) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(self).map_err(std::io::Error::other)?;
        std::fs::write(path, json)
    }

    /// Load trained model from JSON file.
    pub fn load(path: &str) -> std::io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        serde_json::from_str(&json).map_err(std::io::Error::other)
    }

    /// Deserialize from an embedded JSON string (e.g., from `include_str!`).
    ///
    /// Used in generated code when `log_semiring_model_path` is set:
    /// ```text
    /// static TRAINED_MODEL: LazyLock<TrainedModel> = LazyLock::new(|| {
    ///     TrainedModel::from_embedded(include_str!("path/to/model.json"))
    ///         .expect("embedded model should be valid JSON")
    /// });
    /// ```
    pub fn from_embedded(json_str: &str) -> Result<Self, String> {
        serde_json::from_str(json_str)
            .map_err(|e| format!("failed to deserialize embedded trained model: {}", e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_rule_labels() -> Vec<String> {
        vec!["Add".to_string(), "Mul".to_string(), "Lit".to_string(), "Var".to_string()]
    }

    #[test]
    fn test_uniform_weights() {
        let labels = test_rule_labels();
        let rw = RuleWeights::uniform(&labels);

        for label in &labels {
            assert_eq!(rw.get(label), LogWeight::one());
        }
    }

    #[test]
    fn test_compute_loss_correct_only() {
        let rw = RuleWeights::uniform(&test_rule_labels());

        // When correct path weight equals total weight → loss = 0
        let total = LogWeight::one();
        let correct = LogWeight::one();
        let loss = rw.compute_loss(correct, total);
        assert!((loss - 0.0).abs() < 1e-10, "loss should be 0, got {}", loss);
    }

    #[test]
    fn test_weight_update_direction() {
        let labels = test_rule_labels();
        let mut rw = RuleWeights::uniform(&labels);
        rw.set_learning_rate(0.5);

        // "Correct" parse uses Add more than expected
        let expected_correct: BTreeMap<String, f64> = BTreeMap::from([("Add".to_string(), 2.0)]);
        let expected_all: BTreeMap<String, f64> = BTreeMap::from([("Add".to_string(), 0.5)]);

        let add_before = rw.get("Add").value();
        rw.update(&expected_correct, &expected_all);
        let add_after = rw.get("Add").value();

        // Gradient for Add = 2.0 - 0.5 = 1.5
        // Update: w -= lr * gradient = 0.0 - 0.5 * 1.5 = -0.75, clamped to 0.0
        assert!(
            add_after <= add_before,
            "Add weight should decrease (more probable): {} -> {}",
            add_before,
            add_after
        );
    }

    #[test]
    fn test_train_simple_corpus() {
        let labels = test_rule_labels();
        let mut rw = RuleWeights::uniform(&labels);
        rw.set_learning_rate(0.01);

        let examples = vec![
            TrainingExample {
                input: "1 + 2".to_string(),
                expected_rule_labels: vec!["Lit".to_string(), "Add".to_string(), "Lit".to_string()],
            },
            TrainingExample {
                input: "x * y".to_string(),
                expected_rule_labels: vec!["Var".to_string(), "Mul".to_string(), "Var".to_string()],
            },
        ];

        let stats = rw.train(&examples, 5);

        // Should have 5 epoch losses
        assert_eq!(stats.epoch_losses.len(), 5);
        // Loss should generally decrease (or at least not explode)
        assert!(!stats.final_loss.is_nan(), "loss should not be NaN");
        assert!(!stats.final_loss.is_infinite(), "loss should not be infinite");
    }

    #[test]
    fn test_trained_model_roundtrip() {
        let model = TrainedModel {
            rule_weights: BTreeMap::from([
                ("Add".to_string(), 0.5),
                ("Mul".to_string(), 1.2),
                ("Lit".to_string(), 0.3),
            ]),
            recommended_beam_width: Some(2.0),
            metadata: TrainedModelMetadata {
                epochs: 10,
                final_loss: 0.05,
                converged: true,
                num_examples: 100,
                learning_rate: 0.01,
            },
        };

        // Serialize to JSON and deserialize
        let json = serde_json::to_string_pretty(&model).expect("serialize");
        let loaded: TrainedModel = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(loaded.rule_weights, model.rule_weights);
        assert_eq!(loaded.recommended_beam_width, model.recommended_beam_width);
        assert_eq!(loaded.metadata.epochs, model.metadata.epochs);
        assert!((loaded.metadata.final_loss - model.metadata.final_loss).abs() < 1e-10);
        assert_eq!(loaded.metadata.converged, model.metadata.converged);
    }

    #[test]
    fn test_trained_model_beam_width() {
        let model = TrainedModel {
            rule_weights: BTreeMap::new(),
            recommended_beam_width: Some(1.5),
            metadata: TrainedModelMetadata {
                epochs: 1,
                final_loss: 0.0,
                converged: true,
                num_examples: 0,
                learning_rate: 0.1,
            },
        };

        let json = serde_json::to_string(&model).expect("serialize");
        let loaded: TrainedModel = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(loaded.recommended_beam_width, Some(1.5));
    }

    #[test]
    fn test_trained_model_file_roundtrip() {
        let model = TrainedModel {
            rule_weights: BTreeMap::from([("Add".to_string(), 0.5), ("Lit".to_string(), 0.3)]),
            recommended_beam_width: Some(2.0),
            metadata: TrainedModelMetadata {
                epochs: 5,
                final_loss: 0.02,
                converged: true,
                num_examples: 50,
                learning_rate: 0.01,
            },
        };

        let path = "/tmp/prattail_test_model.json";
        model.save(path).expect("save model");
        let loaded = TrainedModel::load(path).expect("load model");

        assert_eq!(loaded.rule_weights, model.rule_weights);
        assert_eq!(loaded.recommended_beam_width, model.recommended_beam_width);
        assert_eq!(loaded.metadata.epochs, model.metadata.epochs);

        // Clean up
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn test_from_embedded_valid_json() {
        let json = r#"{
            "rule_weights": {"Add": 0.5, "Lit": 0.3},
            "recommended_beam_width": 2.0,
            "metadata": {
                "epochs": 10,
                "final_loss": 0.05,
                "converged": true,
                "num_examples": 100,
                "learning_rate": 0.01
            }
        }"#;

        let model = TrainedModel::from_embedded(json).expect("should parse valid JSON");
        assert_eq!(model.rule_weights.get("Add"), Some(&0.5));
        assert_eq!(model.rule_weights.get("Lit"), Some(&0.3));
        assert_eq!(model.recommended_beam_width, Some(2.0));
        assert_eq!(model.metadata.epochs, 10);
        assert!(model.metadata.converged);
    }

    #[test]
    fn test_from_embedded_invalid_json() {
        let result = TrainedModel::from_embedded("not valid json");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("failed to deserialize"));
    }

    #[test]
    fn test_from_embedded_roundtrip() {
        let model = TrainedModel {
            rule_weights: BTreeMap::from([("Var".to_string(), 1.5), ("Mul".to_string(), 0.7)]),
            recommended_beam_width: None,
            metadata: TrainedModelMetadata {
                epochs: 3,
                final_loss: 0.1,
                converged: false,
                num_examples: 20,
                learning_rate: 0.05,
            },
        };

        let json = serde_json::to_string(&model).expect("serialize");
        let loaded = TrainedModel::from_embedded(&json).expect("from_embedded");

        assert_eq!(loaded.rule_weights, model.rule_weights);
        assert_eq!(loaded.recommended_beam_width, model.recommended_beam_width);
        assert_eq!(loaded.metadata.epochs, model.metadata.epochs);
        assert!(!loaded.metadata.converged);
    }

    #[test]
    fn test_to_trained_model() {
        let labels = vec!["A".to_string(), "B".to_string()];
        let mut rw = RuleWeights::uniform(&labels);
        rw.set("A", LogWeight::new(0.5));
        rw.set("B", LogWeight::new(1.0));

        let stats = TrainingStats {
            epoch_losses: vec![1.0, 0.5],
            final_loss: 0.5,
            converged: false,
            recommended_beam_width: Some(TropicalWeight::new(1.5)),
        };

        let model = rw.to_trained_model(&stats);

        assert_eq!(model.rule_weights.get("A"), Some(&0.5));
        assert_eq!(model.rule_weights.get("B"), Some(&1.0));
        assert_eq!(model.recommended_beam_width, Some(1.5));
        assert_eq!(model.metadata.epochs, 2);
        assert!((model.metadata.final_loss - 0.5).abs() < 1e-10);
        assert!(!model.metadata.converged);
    }
}
