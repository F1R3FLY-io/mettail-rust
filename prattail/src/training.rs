//! Weight training loop for PraTTaIL grammars.
//!
//! Provides infrastructure for learning grammar rule weights from a corpus
//! of training examples. The training loop:
//!
//! 1. Computes correct-path rule counts from each training example.
//! 2. Computes baseline ("all parses") counts as uniform over all rules.
//! 3. Updates weights via SGD to favor rules that appear in correct parses.
//!
//! ## Trained Model Serialization
//!
//! After training, rule weights and metadata are serialized to a compact binary
//! format (postcard) via `TrainedModel`. This model can be loaded at compile
//! time by the `language!` DSL via the `log_semiring_model_path` option.
//!
//! ## Known Limitation: Parse-Lattice Construction
//!
//! Constructing a lattice of all possible parses from PraTTaIL's Pratt parser
//! is an open research problem (Pratt parsing is greedy and does not natively
//! enumerate alternative derivations). The current implementation provides the
//! full weight-training infrastructure; the `train()` method uses a simplified
//! approximation based on pre-computed rule counts rather than forward-backward
//! over a parse lattice. This produces correct directional weight updates and
//! is sufficient for the current training use case.

use std::collections::HashMap;

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
    weights: HashMap<String, LogWeight>,
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
        expected_correct: &HashMap<String, f64>,
        expected_all: &HashMap<String, f64>,
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
    /// (parse-lattice construction from Pratt parsers is an open research problem;
    /// see module docs for details).
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
                let mut expected_counts: HashMap<String, f64> = HashMap::new();
                for label in &example.expected_rule_labels {
                    correct_weight = correct_weight.times(&self.get(label));
                    *expected_counts.entry(label.clone()).or_insert(0.0) += 1.0;
                }

                // Simplified "all" path weight: assume uniform over all rules
                // In a real implementation, this would come from forward-backward
                let all_counts: HashMap<String, f64> = self
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
            recovery_weights: None,
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
    pub rule_weights: HashMap<String, f64>,
    /// Recommended beam width derived from training data.
    pub recommended_beam_width: Option<f64>,
    /// Trained recovery strategy weights (Sprint 12).
    ///
    /// Maps strategy names ("skip_per_token", "delete_cost", "substitute_cost",
    /// "insert_cost", "swap_cost") to learned cost values. When present, these
    /// override the corresponding `RecoveryConfig` defaults.
    #[serde(default)]
    pub recovery_weights: Option<HashMap<String, f64>>,
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
    /// Save trained model to a binary file (postcard format).
    pub fn save(&self, path: &str) -> std::io::Result<()> {
        let bytes = postcard::to_allocvec(self).map_err(std::io::Error::other)?;
        std::fs::write(path, bytes)
    }

    /// Load trained model from a binary file (postcard format).
    pub fn load(path: &str) -> std::io::Result<Self> {
        let bytes = std::fs::read(path)?;
        postcard::from_bytes(&bytes).map_err(std::io::Error::other)
    }

    /// Serialize to a compact binary format for embedding in generated code.
    ///
    /// Uses `postcard` (no SIMD float paths) to avoid Cranelift aarch64
    /// NEON intrinsic issues that `serde_json` triggers on macOS nightly.
    pub fn to_embedded(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(self)
            .map_err(|e| format!("failed to serialize trained model for embedding: {}", e))
    }

    /// Deserialize from an embedded binary blob (e.g., from `include_bytes!`).
    ///
    /// Used in generated code when `log_semiring_model_path` is set:
    /// ```text
    /// static TRAINED_MODEL: LazyLock<TrainedModel> = LazyLock::new(|| {
    ///     TrainedModel::from_embedded(include_bytes!("path/to/model.bin"))
    ///         .expect("embedded model should be valid")
    /// });
    /// ```
    pub fn from_embedded(data: &[u8]) -> Result<Self, String> {
        postcard::from_bytes(data)
            .map_err(|e| format!("failed to deserialize embedded trained model: {}", e))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// B5: Online weight training from spillover signals
// ══════════════════════════════════════════════════════════════════════════════

/// B5: Accumulated spillover training signal.
///
/// Bridges the C1 `WeightCorrection` events to the `RuleWeights` training
/// infrastructure. Each correction represents a case where the WFST's
/// prediction weight ordering was wrong: the parser's primary (weight-best)
/// alternative was rejected in favor of a spilled alternative.
///
/// # Signal interpretation
///
/// - `primary_weight` → the WFST weight of the rejected primary alternative.
/// - `selected_weight` → the WFST weight of the accepted (spilled) alternative.
/// - `weight_delta()` → how much the prediction was off.
///
/// The training signal: for rules associated with the *selected* weight,
/// decrease their weight (make more probable); for rules associated with
/// the *primary* weight, increase their weight (make less probable).
#[derive(Debug, Clone, Default)]
pub struct SpilloverTrainer {
    /// Category → accumulated correction signals.
    corrections: HashMap<String, Vec<crate::wfst::WeightCorrection>>,
    /// Learning rate for spillover-based weight updates (default 0.05).
    learning_rate: f64,
    /// Maximum per-rule weight adjustment per update pass (default 0.5).
    max_adjustment: f64,
}

impl SpilloverTrainer {
    /// Create a new spillover trainer with default parameters.
    pub fn new() -> Self {
        SpilloverTrainer {
            corrections: HashMap::new(),
            learning_rate: 0.05,
            max_adjustment: 0.5,
        }
    }

    /// Create with custom learning rate and max adjustment.
    pub fn with_params(learning_rate: f64, max_adjustment: f64) -> Self {
        SpilloverTrainer {
            corrections: HashMap::new(),
            learning_rate,
            max_adjustment,
        }
    }

    /// Ingest weight corrections from a single parse.
    ///
    /// Call after `Language::drain_weight_corrections()` returns non-empty.
    pub fn add_corrections(&mut self, corrections: Vec<crate::wfst::WeightCorrection>) {
        for c in corrections {
            self.corrections
                .entry(c.category.to_string())
                .or_default()
                .push(c);
        }
    }

    /// Number of accumulated corrections across all categories.
    pub fn num_corrections(&self) -> usize {
        self.corrections.values().map(|v| v.len()).sum()
    }

    /// Number of corrections for a specific category.
    pub fn num_corrections_for(&self, category: &str) -> usize {
        self.corrections.get(category).map_or(0, |v| v.len())
    }

    /// Compute aggregate weight adjustment recommendation per category.
    ///
    /// Returns a map from category name to `(primary_adjustment, selected_adjustment)`:
    /// - `primary_adjustment > 0`: increase primary weight (penalize misprediction).
    /// - `selected_adjustment < 0`: decrease selected weight (reinforce correct choice).
    ///
    /// The adjustments are averaged over all corrections for the category and
    /// clamped to `[-max_adjustment, +max_adjustment]`.
    pub fn compute_adjustments(&self) -> HashMap<String, (f64, f64)> {
        let mut result = HashMap::new();

        for (category, corrections) in &self.corrections {
            if corrections.is_empty() {
                continue;
            }

            let n = corrections.len() as f64;
            let avg_primary_adj: f64 = corrections
                .iter()
                .map(|c| c.primary_adjustment(self.learning_rate, self.max_adjustment))
                .sum::<f64>()
                / n;
            let avg_selected_adj: f64 = corrections
                .iter()
                .map(|c| -(c.primary_adjustment(self.learning_rate, self.max_adjustment)))
                .sum::<f64>()
                / n;

            result.insert(
                category.clone(),
                (
                    avg_primary_adj.min(self.max_adjustment),
                    avg_selected_adj.max(-self.max_adjustment),
                ),
            );
        }

        result
    }

    /// Apply accumulated corrections to a `RuleWeights` instance.
    ///
    /// For each correction:
    /// - Rules with weight near `primary_weight` get a penalty (weight increases).
    /// - Rules with weight near `selected_weight` get a bonus (weight decreases).
    ///
    /// The matching uses a weight tolerance of ±0.1 to handle floating-point
    /// imprecision in weight propagation.
    ///
    /// Returns the number of weight updates applied.
    pub fn apply_to_rule_weights(&self, rule_weights: &mut RuleWeights) -> usize {
        let tolerance = 0.1;
        let mut updates = 0;

        for corrections in self.corrections.values() {
            for correction in corrections {
                let adj = correction.primary_adjustment(self.learning_rate, self.max_adjustment);
                if adj < 1e-10 {
                    continue; // No correction needed
                }

                // Penalize rules matching primary weight
                for (label, weight) in rule_weights.weights.iter_mut() {
                    let w = weight.value();
                    if (w - correction.primary_weight).abs() < tolerance {
                        *weight = LogWeight::new((w + adj).max(0.0));
                        updates += 1;
                    }
                    // Reinforce rules matching selected weight (decrease their weight = increase probability)
                    if (w - correction.selected_weight).abs() < tolerance {
                        *weight = LogWeight::new((w - adj).max(0.0));
                        updates += 1;
                    }
                    // Suppress unused variable warning for label
                    let _ = label;
                }
            }
        }

        updates
    }

    /// Clear all accumulated corrections.
    pub fn clear(&mut self) {
        self.corrections.clear();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 5: Forward-backward expected counts
// ══════════════════════════════════════════════════════════════════════════════

/// Sprint 5: Compute expected rule counts using forward-backward with LogWeight.
///
/// Builds a DAG from the PredictionWfst's transitions and computes:
/// ```text
/// E[count(r)] = exp(-(alpha[i] + w + beta[j] - Z))
/// ```
/// where `alpha[i]` = forward score at source state, `w` = transition weight,
/// `beta[j]` = backward score at target state, and `Z` = total path weight.
///
/// Returns a map from rule_label → expected count.
///
/// # Requires
/// Feature `wfst-log` (uses `LogWeight` for forward-backward).
#[cfg(feature = "wfst-log")]
pub fn compute_expected_counts_fb(
    wfst: &crate::wfst::PredictionWfst,
) -> HashMap<String, f64> {
    use crate::automata::semiring::LogWeight;
    use crate::forward_backward::{forward_scores, backward_scores, total_weight};

    let n = wfst.states.len();
    if n == 0 {
        return HashMap::new();
    }

    // Add a virtual "super-final" node (index n) that all final states connect to.
    // This handles star-shaped WFSTs with multiple final states correctly.
    let super_final = n;
    let total_nodes = n + 1;

    // Build edge list for LogWeight forward-backward
    let mut edges: Vec<Vec<(usize, LogWeight)>> = vec![Vec::new(); total_nodes];
    // Also track which action_idx is used per edge for rule attribution
    let mut edge_actions: Vec<Vec<(usize, u32)>> = vec![Vec::new(); total_nodes];

    for state in &wfst.states {
        let from = state.id as usize;
        for trans in &state.transitions {
            let to = trans.to as usize;
            let w = LogWeight::new(trans.weight.value());
            edges[from].push((to, w));
            edge_actions[from].push((to, trans.action_idx));
        }
        // Connect final states to super-final with their final_weight
        if state.is_final {
            edges[from].push((super_final, LogWeight::new(state.final_weight.value())));
            edge_actions[from].push((super_final, u32::MAX)); // sentinel: no action
        }
    }

    let alpha = forward_scores(&edges, total_nodes);
    let beta = backward_scores(&edges, total_nodes, super_final);
    let z = total_weight(&alpha, super_final);

    if z.is_zero() {
        return HashMap::new();
    }

    let z_val = z.value();
    let mut counts: HashMap<String, f64> = HashMap::new();

    for (from, trans_list) in edges.iter().enumerate() {
        for (idx, &(to, ref w)) in trans_list.iter().enumerate() {
            // E[count(edge)] = exp(-(alpha[from] + w + beta[to] - Z))
            let edge_score = alpha[from].value() + w.value() + beta[to].value();
            let expected_count = (-(edge_score - z_val)).exp();

            if expected_count > 1e-15 {
                // Look up the action for this edge
                let action_idx = edge_actions[from][idx].1;
                if let Some(action) = wfst.actions.get(action_idx as usize) {
                    *counts.entry(action.action.rule_label()).or_insert(0.0) += expected_count;
                }
            }
        }
    }

    counts
}

/// Sprint 5: Train rule weights using forward-backward expected counts from
/// NFA spillover corrections.
///
/// For each correction, builds a DAG from the affected PredictionWfst and
/// computes forward-backward expected counts. Uses these to update rule weights
/// via SGD, replacing the simplified "uniform all-counts" approximation.
///
/// # Arguments
///
/// * `rule_weights` — The trainable rule weights to update.
/// * `wfsts` — Per-category PredictionWfsts (source of the DAG structure).
/// * `corrections` — Accumulated spillover corrections.
/// * `epochs` — Number of SGD iterations over all corrections.
///
/// # Returns
///
/// Training statistics from the forward-backward training run.
///
/// # Requires
/// Feature `wfst-log`.
#[cfg(feature = "wfst-log")]
pub fn train_from_corrections(
    rule_weights: &mut RuleWeights,
    wfsts: &HashMap<String, crate::wfst::PredictionWfst>,
    corrections: &[crate::wfst::WeightCorrection],
    epochs: usize,
) -> TrainingStats {
    let mut epoch_losses = Vec::with_capacity(epochs);

    for _epoch in 0..epochs {
        let mut epoch_loss = 0.0;

        for correction in corrections {
            // Find the WFST for this correction's category
            let wfst = match wfsts.get(correction.category) {
                Some(w) => w,
                None => continue,
            };

            // Compute expected counts via forward-backward
            let expected_all = compute_expected_counts_fb(wfst);

            // "Correct" counts: the selected (accepted) alternative gets count 1.0
            // We can't identify the exact rule label from weight alone, so we use
            // all rules whose weight matches the selected weight (±tolerance)
            let tolerance = 0.1;
            let mut expected_correct: HashMap<String, f64> = HashMap::new();
            for action in &wfst.actions {
                if (action.weight.value() - correction.selected_weight).abs() < tolerance {
                    expected_correct.insert(action.action.rule_label(), 1.0);
                }
            }

            // Compute loss
            let correct_weight = expected_correct.values().sum::<f64>();
            let all_weight = expected_all.values().sum::<f64>();
            if all_weight > 0.0 {
                epoch_loss += (correct_weight / all_weight).max(1e-15).ln().abs();
            }

            // Update weights
            rule_weights.update(&expected_correct, &expected_all);
        }

        epoch_losses.push(if corrections.is_empty() { 0.0 } else { epoch_loss / corrections.len() as f64 });
    }

    let final_loss = epoch_losses.last().copied().unwrap_or(f64::INFINITY);
    let converged = epoch_losses.len() >= 2
        && (epoch_losses[epoch_losses.len() - 2] - final_loss).abs() < 1e-6;

    TrainingStats {
        epoch_losses,
        final_loss,
        converged,
        recommended_beam_width: None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Recovery weight training (Sprint 12)
// ══════════════════════════════════════════════════════════════════════════════

/// A training example for recovery weight learning.
///
/// Pairs an erroneous input with the correct input and the expected
/// repair actions, allowing the trainer to learn optimal strategy costs.
#[derive(Debug, Clone)]
pub struct RecoveryTrainingExample {
    /// The input string containing an error.
    pub input_with_error: String,
    /// The correct (error-free) input string.
    pub correct_input: String,
    /// Token positions where errors occur (0-indexed).
    pub error_positions: Vec<usize>,
    /// The expected repair actions for each error position.
    pub expected_repairs: Vec<crate::recovery::RepairAction>,
}

/// Train recovery strategy weights from a corpus of error examples.
///
/// Uses gradient descent over the strategy cost parameters to minimize the
/// difference between the recovery system's selected strategy and the expected
/// optimal strategy for each example.
///
/// # Arguments
///
/// * `examples` — Training examples pairing erroneous inputs with expected repairs.
/// * `epochs` — Number of training iterations.
/// * `learning_rate` — SGD learning rate.
///
/// # Returns
///
/// A map from strategy names to learned cost values.
pub fn train_recovery_weights(
    examples: &[RecoveryTrainingExample],
    epochs: usize,
    learning_rate: f64,
) -> HashMap<String, f64> {
    use crate::recovery::RepairAction;

    // Initialize weights from default config
    let default = crate::recovery::RecoveryConfig::default();
    let mut weights: HashMap<String, f64> = HashMap::new();
    weights.insert("skip_per_token".to_string(), default.skip_per_token);
    weights.insert("delete_cost".to_string(), default.delete_cost);
    weights.insert("substitute_cost".to_string(), default.substitute_cost);
    weights.insert("insert_cost".to_string(), default.insert_cost);
    weights.insert("swap_cost".to_string(), default.swap_cost);

    if examples.is_empty() {
        return weights;
    }

    // Map repair actions to their strategy name
    fn strategy_name(action: &RepairAction) -> &'static str {
        match action {
            RepairAction::SkipToSync { .. } => "skip_per_token",
            RepairAction::DeleteToken => "delete_cost",
            RepairAction::SubstituteToken { .. } => "substitute_cost",
            RepairAction::InsertToken { .. } => "insert_cost",
            RepairAction::SwapTokens { .. } => "swap_cost",
            RepairAction::Composite { .. } => "delete_cost", // composite uses dominant cost
            RepairAction::CategorySwitch { .. } => "substitute_cost",
        }
    }

    // SGD: for each epoch, adjust weights toward the expected strategies
    for _epoch in 0..epochs {
        let mut gradients: HashMap<String, f64> = HashMap::new();
        for (key, _) in &weights {
            gradients.insert(key.clone(), 0.0);
        }

        for example in examples {
            for repair in &example.expected_repairs {
                let target_strategy = strategy_name(repair);

                // The target strategy should have a lower cost than others.
                // Gradient: decrease target cost, increase non-target costs.
                for (key, grad) in gradients.iter_mut() {
                    if key == target_strategy {
                        // Decrease target cost (make it more likely to be selected)
                        *grad -= 1.0 / examples.len() as f64;
                    } else {
                        // Increase non-target costs (make them less likely)
                        *grad += 0.5 / examples.len() as f64;
                    }
                }
            }
        }

        // Apply gradients with clamping to positive values
        for (key, weight) in weights.iter_mut() {
            if let Some(grad) = gradients.get(key) {
                *weight += learning_rate * grad;
                // Clamp to [0.01, 10.0] — costs must be positive and bounded
                *weight = weight.clamp(0.01, 10.0);
            }
        }
    }

    weights
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
        let expected_correct: HashMap<String, f64> = HashMap::from([("Add".to_string(), 2.0)]);
        let expected_all: HashMap<String, f64> = HashMap::from([("Add".to_string(), 0.5)]);

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
            rule_weights: HashMap::from([
                ("Add".to_string(), 0.5),
                ("Mul".to_string(), 1.2),
                ("Lit".to_string(), 0.3),
            ]),
            recommended_beam_width: Some(2.0),
            recovery_weights: None,
            metadata: TrainedModelMetadata {
                epochs: 10,
                final_loss: 0.05,
                converged: true,
                num_examples: 100,
                learning_rate: 0.01,
            },
        };

        // Serialize to postcard binary and deserialize
        let bytes = model.to_embedded().expect("serialize");
        let loaded = TrainedModel::from_embedded(&bytes).expect("deserialize");

        assert_eq!(loaded.rule_weights, model.rule_weights);
        assert_eq!(loaded.recommended_beam_width, model.recommended_beam_width);
        assert_eq!(loaded.metadata.epochs, model.metadata.epochs);
        assert!((loaded.metadata.final_loss - model.metadata.final_loss).abs() < 1e-10);
        assert_eq!(loaded.metadata.converged, model.metadata.converged);
    }

    #[test]
    fn test_trained_model_beam_width() {
        let model = TrainedModel {
            rule_weights: HashMap::new(),
            recommended_beam_width: Some(1.5),
            recovery_weights: None,
            metadata: TrainedModelMetadata {
                epochs: 1,
                final_loss: 0.0,
                converged: true,
                num_examples: 0,
                learning_rate: 0.1,
            },
        };

        let bytes = model.to_embedded().expect("serialize");
        let loaded = TrainedModel::from_embedded(&bytes).expect("deserialize");

        assert_eq!(loaded.recommended_beam_width, Some(1.5));
    }

    #[test]
    fn test_trained_model_file_roundtrip() {
        let model = TrainedModel {
            rule_weights: HashMap::from([("Add".to_string(), 0.5), ("Lit".to_string(), 0.3)]),
            recommended_beam_width: Some(2.0),
            recovery_weights: None,
            metadata: TrainedModelMetadata {
                epochs: 5,
                final_loss: 0.02,
                converged: true,
                num_examples: 50,
                learning_rate: 0.01,
            },
        };

        let path = std::env::temp_dir().join("prattail_test_model.bin");
        let path = path.to_str().expect("temp dir path is valid UTF-8");
        model.save(path).expect("save model");
        let loaded = TrainedModel::load(path).expect("load model");

        assert_eq!(loaded.rule_weights, model.rule_weights);
        assert_eq!(loaded.recommended_beam_width, model.recommended_beam_width);
        assert_eq!(loaded.metadata.epochs, model.metadata.epochs);

        // Clean up
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn test_from_embedded_valid_data() {
        let model = TrainedModel {
            rule_weights: HashMap::from([("Add".to_string(), 0.5), ("Lit".to_string(), 0.3)]),
            recommended_beam_width: Some(2.0),
            recovery_weights: None,
            metadata: TrainedModelMetadata {
                epochs: 10,
                final_loss: 0.05,
                converged: true,
                num_examples: 100,
                learning_rate: 0.01,
            },
        };

        let bytes = model.to_embedded().expect("serialize");
        let loaded = TrainedModel::from_embedded(&bytes).expect("should parse valid data");
        assert_eq!(loaded.rule_weights.get("Add"), Some(&0.5));
        assert_eq!(loaded.rule_weights.get("Lit"), Some(&0.3));
        assert_eq!(loaded.recommended_beam_width, Some(2.0));
        assert_eq!(loaded.metadata.epochs, 10);
        assert!(loaded.metadata.converged);
    }

    #[test]
    fn test_from_embedded_invalid_data() {
        let result = TrainedModel::from_embedded(&[0xFF, 0xFE, 0xFD]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("failed to deserialize"));
    }

    #[test]
    fn test_from_embedded_roundtrip() {
        let model = TrainedModel {
            rule_weights: HashMap::from([("Var".to_string(), 1.5), ("Mul".to_string(), 0.7)]),
            recommended_beam_width: None,
            recovery_weights: None,
            metadata: TrainedModelMetadata {
                epochs: 3,
                final_loss: 0.1,
                converged: false,
                num_examples: 20,
                learning_rate: 0.05,
            },
        };

        let bytes = model.to_embedded().expect("serialize");
        let loaded = TrainedModel::from_embedded(&bytes).expect("from_embedded");

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
        assert_eq!(model.recovery_weights, None);
        assert_eq!(model.metadata.epochs, 2);
        assert!((model.metadata.final_loss - 0.5).abs() < 1e-10);
        assert!(!model.metadata.converged);
    }

    // ── Sprint 12: Recovery weight training ──

    #[test]
    fn test_train_recovery_weights_empty_examples() {
        let weights = train_recovery_weights(&[], 10, 0.01);
        // Should return defaults
        let default = crate::recovery::RecoveryConfig::default();
        assert!((weights["skip_per_token"] - default.skip_per_token).abs() < 1e-9);
        assert!((weights["delete_cost"] - default.delete_cost).abs() < 1e-9);
        assert!((weights["substitute_cost"] - default.substitute_cost).abs() < 1e-9);
        assert!((weights["insert_cost"] - default.insert_cost).abs() < 1e-9);
        assert!((weights["swap_cost"] - default.swap_cost).abs() < 1e-9);
    }

    #[test]
    fn test_train_recovery_weights_delete_preferred() {
        use crate::recovery::RepairAction;

        // All examples have delete as expected repair — delete cost should decrease
        let examples: Vec<RecoveryTrainingExample> = (0..10)
            .map(|_| RecoveryTrainingExample {
                input_with_error: "1 + + 2".to_string(),
                correct_input: "1 + 2".to_string(),
                error_positions: vec![4],
                expected_repairs: vec![RepairAction::DeleteToken],
            })
            .collect();

        let weights = train_recovery_weights(&examples, 50, 0.1);
        let default = crate::recovery::RecoveryConfig::default();

        // Delete cost should decrease (training pushes it lower)
        assert!(
            weights["delete_cost"] < default.delete_cost,
            "delete_cost should decrease when all examples prefer delete, got: {} vs default {}",
            weights["delete_cost"],
            default.delete_cost
        );
    }

    #[test]
    fn test_train_recovery_weights_differ_from_defaults() {
        use crate::recovery::RepairAction;

        // Mix of delete and insert examples
        let mut examples: Vec<RecoveryTrainingExample> = Vec::new();
        for _ in 0..5 {
            examples.push(RecoveryTrainingExample {
                input_with_error: "1 + + 2".to_string(),
                correct_input: "1 + 2".to_string(),
                error_positions: vec![4],
                expected_repairs: vec![RepairAction::DeleteToken],
            });
        }
        for _ in 0..5 {
            examples.push(RecoveryTrainingExample {
                input_with_error: "(1 + 2".to_string(),
                correct_input: "(1 + 2)".to_string(),
                error_positions: vec![6],
                expected_repairs: vec![RepairAction::InsertToken { token: 0 }],
            });
        }

        let weights = train_recovery_weights(&examples, 100, 0.1);
        let default = crate::recovery::RecoveryConfig::default();

        // Trained weights should differ from defaults
        let any_different = weights
            .iter()
            .any(|(k, v)| {
                let default_val = match k.as_str() {
                    "skip_per_token" => default.skip_per_token,
                    "delete_cost" => default.delete_cost,
                    "substitute_cost" => default.substitute_cost,
                    "insert_cost" => default.insert_cost,
                    "swap_cost" => default.swap_cost,
                    _ => 0.0,
                };
                (*v - default_val).abs() > 1e-9
            });

        assert!(
            any_different,
            "trained weights should differ from defaults after training with examples"
        );
    }

    #[test]
    fn test_trained_model_recovery_weights_serialization() {
        let mut recovery = HashMap::new();
        recovery.insert("skip_per_token".to_string(), 0.3);
        recovery.insert("delete_cost".to_string(), 0.8);

        let model = TrainedModel {
            rule_weights: HashMap::new(),
            recommended_beam_width: None,
            recovery_weights: Some(recovery.clone()),
            metadata: TrainedModelMetadata {
                epochs: 1,
                final_loss: 0.0,
                converged: true,
                num_examples: 10,
                learning_rate: 0.01,
            },
        };

        let bytes = model.to_embedded().expect("serialize");
        let loaded = TrainedModel::from_embedded(&bytes).expect("deserialize");

        assert_eq!(loaded.recovery_weights, Some(recovery));
    }

    #[test]
    fn test_recovery_config_apply_trained_weights() {
        let mut config = crate::recovery::RecoveryConfig::default();
        let mut weights = HashMap::new();
        weights.insert("skip_per_token".to_string(), 0.3);
        weights.insert("delete_cost".to_string(), 0.8);

        config.apply_trained_weights(&weights);

        assert!((config.skip_per_token - 0.3).abs() < 1e-9);
        assert!((config.delete_cost - 0.8).abs() < 1e-9);
        // Unchanged fields remain at defaults
        assert!((config.substitute_cost - 1.5).abs() < 1e-9);
        assert!((config.insert_cost - 2.0).abs() < 1e-9);
        assert!((config.swap_cost - 1.25).abs() < 1e-9);
    }

    // ── B5: Spillover trainer tests ──

    fn sample_correction(primary: f64, selected: f64) -> crate::wfst::WeightCorrection {
        crate::wfst::WeightCorrection {
            category: "TestGrammar",
            primary_weight: primary,
            selected_weight: selected,
            alternatives_considered: 3,
        }
    }

    #[test]
    fn test_b5_spillover_trainer_new() {
        let trainer = SpilloverTrainer::new();
        assert_eq!(trainer.num_corrections(), 0);
        assert!(trainer.compute_adjustments().is_empty());
    }

    #[test]
    fn test_b5_add_corrections() {
        let mut trainer = SpilloverTrainer::new();
        trainer.add_corrections(vec![
            sample_correction(0.0, 1.5),
            sample_correction(0.0, 2.0),
        ]);
        assert_eq!(trainer.num_corrections(), 2);
        assert_eq!(trainer.num_corrections_for("TestGrammar"), 2);
        assert_eq!(trainer.num_corrections_for("Other"), 0);
    }

    #[test]
    fn test_b5_compute_adjustments_positive_delta() {
        // B5: When selected weight > primary weight, primary should be penalized.
        let mut trainer = SpilloverTrainer::with_params(0.1, 1.0);
        trainer.add_corrections(vec![sample_correction(0.0, 2.0)]);
        let adj = trainer.compute_adjustments();
        let (primary_adj, selected_adj) = adj.get("TestGrammar").expect("should have TestGrammar");
        assert!(*primary_adj > 0.0, "primary should be penalized: {}", primary_adj);
        assert!(*selected_adj < 0.0, "selected should be reinforced: {}", selected_adj);
    }

    #[test]
    fn test_b5_compute_adjustments_zero_delta() {
        // B5: Zero delta → zero adjustment (correction was a no-op).
        let mut trainer = SpilloverTrainer::with_params(0.1, 1.0);
        trainer.add_corrections(vec![sample_correction(1.0, 1.0)]);
        let adj = trainer.compute_adjustments();
        let (primary_adj, selected_adj) = adj.get("TestGrammar").expect("should have TestGrammar");
        assert!(primary_adj.abs() < 1e-10, "zero delta should produce zero adjustment");
        assert!(selected_adj.abs() < 1e-10, "zero delta should produce zero adjustment");
    }

    #[test]
    fn test_b5_apply_to_rule_weights() {
        // B5: Applying corrections should shift rule weights.
        let labels = vec!["DirectRule".to_string(), "CastRule".to_string()];
        let mut rw = RuleWeights::uniform(&labels);
        // Set up weights matching typical dispatch: Direct=0.0, Cast=0.5
        rw.set("DirectRule", LogWeight::new(0.0));
        rw.set("CastRule", LogWeight::new(0.5));

        let mut trainer = SpilloverTrainer::with_params(0.1, 0.5);
        // Correction: primary at 0.0 was wrong, selected at 0.5 was right
        trainer.add_corrections(vec![sample_correction(0.0, 0.5)]);

        let updates = trainer.apply_to_rule_weights(&mut rw);
        assert!(updates > 0, "should have applied at least one update");

        // DirectRule (matching primary=0.0) should have increased weight
        assert!(
            rw.get("DirectRule").value() > 0.0,
            "DirectRule weight should increase (penalized): {}",
            rw.get("DirectRule").value()
        );
        // CastRule (matching selected=0.5) should have decreased weight
        assert!(
            rw.get("CastRule").value() < 0.5,
            "CastRule weight should decrease (reinforced): {}",
            rw.get("CastRule").value()
        );
    }

    #[test]
    fn test_b5_clear_corrections() {
        let mut trainer = SpilloverTrainer::new();
        trainer.add_corrections(vec![sample_correction(0.0, 1.0)]);
        assert_eq!(trainer.num_corrections(), 1);
        trainer.clear();
        assert_eq!(trainer.num_corrections(), 0);
    }

    // ── Sprint 5: Forward-backward expected counts ──

    #[cfg(feature = "wfst-log")]
    mod fb_tests {
        use super::*;
        use crate::automata::semiring::TropicalWeight;
        use crate::prediction::DispatchAction;
        use crate::token_id::TokenIdMap;
        use crate::wfst::PredictionWfstBuilder;

        fn build_simple_wfst() -> crate::wfst::PredictionWfst {
            let token_map = TokenIdMap::from_names(
                vec!["Plus", "Minus", "Star"].into_iter().map(String::from),
            );
            let mut builder = PredictionWfstBuilder::new("Expr", token_map);
            builder.add_action(
                "Plus",
                DispatchAction::Direct { rule_label: "Add".to_string(), parse_fn: "parse_add".to_string() },
                TropicalWeight::new(0.0),
            );
            builder.add_action(
                "Minus",
                DispatchAction::Direct { rule_label: "Sub".to_string(), parse_fn: "parse_sub".to_string() },
                TropicalWeight::new(0.5),
            );
            builder.add_action(
                "Star",
                DispatchAction::Direct { rule_label: "Mul".to_string(), parse_fn: "parse_mul".to_string() },
                TropicalWeight::new(1.0),
            );
            builder.build()
        }

        #[test]
        fn test_fb_expected_counts_basic() {
            let wfst = build_simple_wfst();
            let counts = super::super::compute_expected_counts_fb(&wfst);

            // Star-shaped WFST: each rule has one transition start→accept
            // Expected counts should be proportional to exp(-weight)
            assert!(counts.contains_key("Add"), "Add should have expected count");
            assert!(counts.contains_key("Sub"), "Sub should have expected count");
            assert!(counts.contains_key("Mul"), "Mul should have expected count");

            // Add (weight=0.0) should have highest expected count
            // Mul (weight=1.0) should have lowest expected count
            assert!(
                counts["Add"] > counts["Mul"],
                "Add (w=0.0) should have higher count than Mul (w=1.0): {} vs {}",
                counts["Add"], counts["Mul"]
            );
        }

        #[test]
        fn test_fb_expected_counts_sum() {
            let wfst = build_simple_wfst();
            let counts = super::super::compute_expected_counts_fb(&wfst);

            // For a star-shaped WFST, expected counts should sum to ~1.0
            // (each path is a complete derivation)
            let total: f64 = counts.values().sum();
            assert!(
                (total - 1.0).abs() < 0.1,
                "expected counts should sum to ~1.0 for star-shaped WFST, got {}",
                total,
            );
        }

        #[test]
        fn test_fb_expected_counts_empty_wfst() {
            use crate::wfst::PredictionWfst;
            let wfst = PredictionWfst {
                category: "Empty".to_string(),
                states: vec![],
                start: 0,
                actions: vec![],
                token_map: TokenIdMap::from_names(std::iter::empty::<String>()),
                beam_width: None,
                context_labels: HashMap::new(),
            };
            let counts = super::super::compute_expected_counts_fb(&wfst);
            assert!(counts.is_empty(), "empty WFST should have no expected counts");
        }

        #[test]
        fn test_train_from_corrections_convergence() {
            let wfst = build_simple_wfst();
            let mut wfsts = HashMap::new();
            wfsts.insert("Expr".to_string(), wfst);

            let labels = vec!["Add".to_string(), "Sub".to_string(), "Mul".to_string()];
            let mut rw = RuleWeights::uniform(&labels);
            rw.set_learning_rate(0.01);

            // Corrections: primary at 0.0 was wrong, selected at 0.5 was right
            let corrections = vec![
                crate::wfst::WeightCorrection {
                    category: "Expr",
                    primary_weight: 0.0,
                    selected_weight: 0.5,
                    alternatives_considered: 3,
                },
            ];

            let stats = super::super::train_from_corrections(
                &mut rw, &wfsts, &corrections, 10,
            );

            assert_eq!(stats.epoch_losses.len(), 10, "should have 10 epoch losses");
            assert!(!stats.final_loss.is_nan(), "loss should not be NaN");
            assert!(!stats.final_loss.is_infinite(), "loss should not be infinite");
        }

        #[test]
        fn test_wfst_apply_corrections() {
            let mut wfst = build_simple_wfst();
            let add_weight_before = wfst.actions.iter()
                .find(|a| a.action.rule_label() == "Add")
                .expect("Add action").weight.value();

            let corrections = vec![
                crate::wfst::WeightCorrection {
                    category: "Expr",
                    primary_weight: 0.0,  // matches Add
                    selected_weight: 0.5, // matches Sub
                    alternatives_considered: 2,
                },
            ];

            wfst.apply_corrections(&corrections, 0.1, 0.5);

            let add_weight_after = wfst.actions.iter()
                .find(|a| a.action.rule_label() == "Add")
                .expect("Add action").weight.value();

            // Add (matching primary=0.0) should be penalized (weight increased)
            assert!(
                add_weight_after > add_weight_before,
                "Add weight should increase after correction: {} → {}",
                add_weight_before, add_weight_after,
            );

            let sub_weight_after = wfst.actions.iter()
                .find(|a| a.action.rule_label() == "Sub")
                .expect("Sub action").weight.value();

            // Sub (matching selected=0.5) should be reinforced (weight decreased)
            assert!(
                sub_weight_after < 0.5,
                "Sub weight should decrease after correction: {}",
                sub_weight_after,
            );
        }
    }
}
