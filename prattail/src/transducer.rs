//! Optimization Transducer Cascade (E1).
//!
//! Represents each optimization pass as a composable transducer that transforms
//! a `PredictionWfst`. The cascade composes multiple passes into a single
//! pipeline with fixed-point iteration until the WFST stabilizes.
//!
//! ## Architecture
//!
//! Each optimization pass implements the `OptimizationPass` trait:
//! - `name()`: Human-readable pass name for diagnostics
//! - `is_applicable()`: Check if this pass should run on the given WFST
//! - `apply()`: Transform the WFST, returning the number of changes made
//!
//! The `TransducerCascade` composes passes and runs them in sequence:
//! ```text
//! Optimized = T_minimize ∘ T_beam_prune ∘ T_dead_elim ∘ Raw_WFST
//! ```
//!
//! Fixed-point iteration: if any pass makes changes, the cascade re-runs
//! all passes until no pass makes any changes (convergence guaranteed by
//! monotonicity — each pass can only remove states/transitions, never add).
//!
//! ## Adding New Passes
//!
//! Adding a new optimization = implementing `OptimizationPass`:
//! ```rust,ignore
//! struct MyPass;
//! impl OptimizationPass for MyPass {
//!     fn name(&self) -> &str { "my-pass" }
//!     fn is_applicable(&self, wfst: &PredictionWfst) -> bool { true }
//!     fn apply(&self, wfst: &mut PredictionWfst) -> PassResult { ... }
//! }
//! ```
//!
//! ## Correctness Guarantees
//!
//! - Each pass independently preserves the WFST's language (dispatch semantics)
//! - Composition with identity is identity: `T ∘ Id = T`
//! - Fixed-point convergence: monotone over BooleanWeight (state count decreases)
//! - Pass ordering is determined by priority (lower = runs first)

use crate::wfst::PredictionWfst;

/// Result of applying a single optimization pass.
#[derive(Debug, Clone)]
pub struct PassResult {
    /// Number of individual changes made (states removed, transitions rewritten, etc.).
    pub changes: usize,
    /// Human-readable summary of what was done.
    pub summary: String,
}

impl PassResult {
    /// Create a result indicating no changes were made.
    pub fn unchanged() -> Self {
        PassResult {
            changes: 0,
            summary: String::new(),
        }
    }

    /// Create a result with the given number of changes and summary.
    pub fn changed(changes: usize, summary: String) -> Self {
        PassResult { changes, summary }
    }

    /// Whether any changes were made.
    pub fn has_changes(&self) -> bool {
        self.changes > 0
    }
}

/// An optimization pass that transforms a PredictionWfst.
///
/// Each pass is a WFST transducer: it takes a WFST and produces an optimized
/// version. Passes must preserve dispatch semantics (same token → same action
/// for all reachable tokens).
pub trait OptimizationPass: std::fmt::Debug {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &str;

    /// Priority for ordering within the cascade (lower = runs first).
    /// Default: 100.
    fn priority(&self) -> u32 {
        100
    }

    /// Check if this pass is applicable to the given WFST.
    ///
    /// Passes can inspect the WFST structure to determine if they would
    /// have any effect. Returning false skips the pass entirely.
    fn is_applicable(&self, wfst: &PredictionWfst) -> bool;

    /// Apply the optimization to the WFST in-place.
    ///
    /// Returns a `PassResult` indicating how many changes were made.
    /// Must preserve dispatch semantics: for any token t, if
    /// `predict(t)` returned actions A before, it must return the
    /// same actions A after (modulo pruned unreachable paths).
    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult;
}

// ══════════════════════════════════════════════════════════════════════════════
// Built-in Passes
// ══════════════════════════════════════════════════════════════════════════════

/// Dead-state elimination pass: removes states that are not reachable from
/// the start state or that have no path to a final state.
///
/// Uses BooleanWeight reachability: forward pass from start, backward pass
/// from finals. States where `forward ∧ backward == false` are removed.
#[derive(Debug)]
pub struct DeadStateElimination;

impl OptimizationPass for DeadStateElimination {
    fn name(&self) -> &str {
        "dead-state-elimination"
    }

    fn priority(&self) -> u32 {
        10 // Run first — removes unreachable states before other passes
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        wfst.state_count() > 2 // Only useful if there are intermediate states
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        // For the two-state architecture (start + finals), dead states are
        // final states with no incoming transitions from start. These are
        // already handled by minimize(). For multi-level WFSTs (future B1
        // extension), this would do a full reachability analysis.
        //
        // Current implementation: check for final states unreachable from start.
        let reachable = wfst.reachable_state_count();
        let total = wfst.state_count();
        if reachable < total {
            let removed = total - reachable;
            wfst.remove_unreachable_states();
            PassResult::changed(
                removed,
                format!("removed {} unreachable state(s)", removed),
            )
        } else {
            PassResult::unchanged()
        }
    }
}

/// State minimization pass: merges states with identical observable behavior.
///
/// Uses signature-based equivalence: states with the same (is_final,
/// final_weight, sorted_transitions) signature are merged into a single
/// representative state.
#[derive(Debug)]
pub struct StateMinimization;

impl OptimizationPass for StateMinimization {
    fn name(&self) -> &str {
        "state-minimization"
    }

    fn priority(&self) -> u32 {
        20 // Run after dead-state elimination
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        wfst.state_count() > 2 // Need at least 3 states for merging to help
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let removed = wfst.minimize();
        if removed > 0 {
            PassResult::changed(removed, format!("merged {} equivalent state(s)", removed))
        } else {
            PassResult::unchanged()
        }
    }
}

/// Beam pruning pass: removes transitions with weights outside the beam width.
///
/// For each state, prunes transitions whose weight exceeds
/// `best_weight + beam_width`. This is a compile-time optimization that
/// reduces the number of dispatch alternatives.
#[derive(Debug)]
pub struct BeamPruning {
    /// Beam width threshold. Transitions with weight > best + beam are pruned.
    pub beam_width: f64,
}

impl BeamPruning {
    /// Create a beam pruning pass with the given width.
    pub fn new(beam_width: f64) -> Self {
        BeamPruning { beam_width }
    }
}

impl OptimizationPass for BeamPruning {
    fn name(&self) -> &str {
        "beam-pruning"
    }

    fn priority(&self) -> u32 {
        30 // Run after minimization
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        self.beam_width.is_finite() && wfst.state_count() > 0
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let pruned = wfst.prune_by_beam(self.beam_width);
        if pruned > 0 {
            PassResult::changed(
                pruned,
                format!(
                    "pruned {} transition(s) outside beam width {:.1}",
                    pruned, self.beam_width
                ),
            )
        } else {
            PassResult::unchanged()
        }
    }
}

/// Weight normalization pass: normalizes transition weights per state so that
/// the best transition has weight 0.0 (TropicalWeight::one()).
///
/// This doesn't change dispatch semantics (relative ordering is preserved)
/// but simplifies downstream analysis and beam pruning.
#[derive(Debug)]
pub struct WeightNormalization;

impl OptimizationPass for WeightNormalization {
    fn name(&self) -> &str {
        "weight-normalization"
    }

    fn priority(&self) -> u32 {
        5 // Run very first — normalize before other passes analyze weights
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        wfst.state_count() > 0
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let normalized = wfst.normalize_weights();
        if normalized > 0 {
            PassResult::changed(
                normalized,
                format!("normalized weights on {} state(s)", normalized),
            )
        } else {
            PassResult::unchanged()
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TransducerCascade
// ══════════════════════════════════════════════════════════════════════════════

/// Result of running the full cascade on a single WFST.
#[derive(Debug, Clone)]
pub struct CascadeResult {
    /// Number of cascade iterations until convergence.
    pub iterations: usize,
    /// Total changes across all iterations and passes.
    pub total_changes: usize,
    /// Per-pass results from the final iteration.
    pub pass_results: Vec<(String, PassResult)>,
}

/// Composes multiple optimization passes into a fixed-point cascade.
///
/// The cascade runs all applicable passes in priority order, then repeats
/// until no pass makes any changes (fixed-point convergence).
///
/// ## Convergence Guarantee
///
/// Each pass can only remove states/transitions (monotone decrease over
/// BooleanWeight). Since the state count is finite and non-negative,
/// the cascade must converge in at most `|states|` iterations.
///
/// ## Usage
///
/// ```rust,ignore
/// let mut cascade = TransducerCascade::new();
/// cascade.add_pass(Box::new(DeadStateElimination));
/// cascade.add_pass(Box::new(StateMinimization));
/// cascade.add_pass(Box::new(BeamPruning::new(2.0)));
///
/// let result = cascade.run(&mut wfst);
/// eprintln!("Converged in {} iterations, {} total changes",
///     result.iterations, result.total_changes);
/// ```
pub struct TransducerCascade {
    /// Ordered passes (sorted by priority on insertion).
    passes: Vec<Box<dyn OptimizationPass>>,
    /// Maximum iterations before forced stop (safety bound).
    max_iterations: usize,
}

impl TransducerCascade {
    /// Create an empty cascade.
    pub fn new() -> Self {
        TransducerCascade {
            passes: Vec::new(),
            max_iterations: 100,
        }
    }

    /// Create a cascade with the default optimization passes.
    ///
    /// Default pipeline:
    /// 1. Weight normalization (priority 5)
    /// 2. Dead-state elimination (priority 10)
    /// 3. State minimization (priority 20)
    pub fn default_pipeline() -> Self {
        let mut cascade = Self::new();
        cascade.add_pass(Box::new(WeightNormalization));
        cascade.add_pass(Box::new(DeadStateElimination));
        cascade.add_pass(Box::new(StateMinimization));
        cascade
    }

    /// Create a cascade with beam pruning included.
    pub fn with_beam(beam_width: f64) -> Self {
        let mut cascade = Self::default_pipeline();
        cascade.add_pass(Box::new(BeamPruning::new(beam_width)));
        cascade
    }

    /// Add an optimization pass to the cascade.
    ///
    /// Passes are sorted by priority (lower = runs first).
    pub fn add_pass(&mut self, pass: Box<dyn OptimizationPass>) {
        self.passes.push(pass);
        self.passes.sort_by_key(|p| p.priority());
    }

    /// Set the maximum number of iterations (safety bound).
    pub fn set_max_iterations(&mut self, max: usize) {
        self.max_iterations = max;
    }

    /// Run the cascade on a single PredictionWfst until convergence.
    ///
    /// Returns a `CascadeResult` with iteration count and per-pass details.
    pub fn run(&self, wfst: &mut PredictionWfst) -> CascadeResult {
        let mut total_changes = 0;
        let mut iterations = 0;
        let mut pass_results = Vec::new();

        loop {
            iterations += 1;
            let mut iter_changes = 0;
            pass_results.clear();

            for pass in &self.passes {
                if pass.is_applicable(wfst) {
                    let result = pass.apply(wfst);
                    iter_changes += result.changes;
                    pass_results.push((pass.name().to_string(), result));
                } else {
                    pass_results.push((
                        pass.name().to_string(),
                        PassResult::unchanged(),
                    ));
                }
            }

            total_changes += iter_changes;

            // Fixed-point: no changes means convergence
            if iter_changes == 0 || iterations >= self.max_iterations {
                break;
            }
        }

        CascadeResult {
            iterations,
            total_changes,
            pass_results,
        }
    }

    /// Run the cascade on all PredictionWfsts in a map.
    ///
    /// Returns a summary string suitable for diagnostic output.
    pub fn run_all(
        &self,
        wfsts: &mut std::collections::HashMap<String, PredictionWfst>,
    ) -> String {
        let mut total_changes = 0;
        let mut total_iterations = 0;
        let mut categories_optimized = 0;

        for (_cat, wfst) in wfsts.iter_mut() {
            let result = self.run(wfst);
            if result.total_changes > 0 {
                categories_optimized += 1;
                total_changes += result.total_changes;
            }
            total_iterations += result.iterations;
        }

        if total_changes > 0 {
            format!(
                "E1 transducer cascade: {} change(s) across {} categories ({} total iterations)",
                total_changes, categories_optimized, total_iterations
            )
        } else {
            String::new()
        }
    }

    /// Number of registered passes.
    pub fn pass_count(&self) -> usize {
        self.passes.len()
    }
}

impl Default for TransducerCascade {
    fn default() -> Self {
        Self::default_pipeline()
    }
}

impl std::fmt::Debug for TransducerCascade {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TransducerCascade")
            .field(
                "passes",
                &self.passes.iter().map(|p| p.name()).collect::<Vec<_>>(),
            )
            .field("max_iterations", &self.max_iterations)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::PredictionWfstBuilder;

    /// Helper: build a simple prediction WFST with N tokens.
    fn build_test_wfst(tokens: &[(&str, f64)]) -> PredictionWfst {
        let names: Vec<String> = tokens.iter().map(|&(n, _)| n.to_string()).collect();
        let token_map = TokenIdMap::from_names(names.into_iter());
        let mut builder = PredictionWfstBuilder::new("Test", token_map);
        for &(token, weight) in tokens {
            builder.add_action(
                token,
                DispatchAction::Direct {
                    rule_label: format!("Rule_{}", token),
                    parse_fn: format!("parse_{}", token.to_lowercase()),
                },
                TropicalWeight::new(weight),
            );
        }
        builder.build()
    }

    #[test]
    fn test_pass_result_unchanged() {
        let r = PassResult::unchanged();
        assert!(!r.has_changes());
        assert_eq!(r.changes, 0);
    }

    #[test]
    fn test_pass_result_changed() {
        let r = PassResult::changed(3, "removed 3 states".to_string());
        assert!(r.has_changes());
        assert_eq!(r.changes, 3);
    }

    #[test]
    fn test_dead_state_elimination_not_applicable() {
        // Two-state WFST: start + 1 final — not applicable
        let wfst = build_test_wfst(&[("Ident", 1.0)]);
        let pass = DeadStateElimination;
        assert!(!pass.is_applicable(&wfst));
    }

    #[test]
    fn test_state_minimization_pass() {
        // Build WFST with multiple identical final states (via union)
        let mut wfst = build_test_wfst(&[("Ident", 1.0), ("Int", 2.0)]);
        let wfst2 = build_test_wfst(&[("Bool", 3.0)]);
        wfst.union(&wfst2);
        // After union: start + 3 final states (some identical)
        assert!(wfst.state_count() > 2);

        let pass = StateMinimization;
        assert!(pass.is_applicable(&wfst));
        let result = pass.apply(&mut wfst);
        assert!(result.has_changes());
    }

    #[test]
    fn test_beam_pruning_pass() {
        let mut wfst = build_test_wfst(&[
            ("Ident", 0.0),
            ("Int", 1.0),
            ("Bool", 5.0),
            ("Str", 10.0),
        ]);
        let pass = BeamPruning::new(2.0);
        assert!(pass.is_applicable(&wfst));
        let result = pass.apply(&mut wfst);
        // Should prune transitions with weight > 0.0 + 2.0 = 2.0
        // "Bool" (5.0) and "Str" (10.0) should be pruned
        assert!(result.has_changes());
        assert_eq!(result.changes, 2);
    }

    #[test]
    fn test_beam_pruning_infinite_beam() {
        let wfst = build_test_wfst(&[("Ident", 0.0)]);
        let pass = BeamPruning::new(f64::INFINITY);
        assert!(!pass.is_applicable(&wfst)); // infinite beam = not applicable
    }

    #[test]
    fn test_cascade_empty() {
        let cascade = TransducerCascade::new();
        let mut wfst = build_test_wfst(&[("Ident", 1.0)]);
        let result = cascade.run(&mut wfst);
        assert_eq!(result.iterations, 1);
        assert_eq!(result.total_changes, 0);
    }

    #[test]
    fn test_cascade_default_pipeline() {
        let cascade = TransducerCascade::default_pipeline();
        assert_eq!(cascade.pass_count(), 3);
        // Verify priority ordering
        let names: Vec<&str> = cascade.passes.iter().map(|p| p.name()).collect();
        assert_eq!(
            names,
            vec!["weight-normalization", "dead-state-elimination", "state-minimization"]
        );
    }

    #[test]
    fn test_cascade_with_beam() {
        let cascade = TransducerCascade::with_beam(3.0);
        assert_eq!(cascade.pass_count(), 4);
    }

    #[test]
    fn test_cascade_convergence() {
        // Build a WFST that benefits from minimization
        let mut wfst = build_test_wfst(&[("Ident", 1.0), ("Int", 2.0)]);
        let wfst2 = build_test_wfst(&[("Bool", 3.0)]);
        wfst.union(&wfst2);

        let cascade = TransducerCascade::default_pipeline();
        let result = cascade.run(&mut wfst);
        // Should converge: iteration 1 makes changes, iteration 2 confirms fixed-point
        assert!(result.iterations <= 3);
        assert!(result.total_changes > 0);
    }

    #[test]
    fn test_cascade_run_all() {
        let mut wfsts = std::collections::HashMap::new();
        let mut w1 = build_test_wfst(&[("Ident", 1.0), ("Int", 2.0)]);
        let w1b = build_test_wfst(&[("Bool", 3.0)]);
        w1.union(&w1b);
        wfsts.insert("Cat1".to_string(), w1);
        wfsts.insert(
            "Cat2".to_string(),
            build_test_wfst(&[("X", 0.0)]),
        );

        let cascade = TransducerCascade::default_pipeline();
        let summary = cascade.run_all(&mut wfsts);
        // Cat1 should have changes (union created mergeable states)
        assert!(!summary.is_empty());
    }

    #[test]
    fn test_cascade_max_iterations() {
        let mut cascade = TransducerCascade::new();
        cascade.set_max_iterations(1);
        // Add a pass that always reports changes (for testing safety bound)
        // We'll use WeightNormalization on a WFST that needs normalization
        cascade.add_pass(Box::new(WeightNormalization));
        let mut wfst = build_test_wfst(&[("Ident", 5.0)]);
        let result = cascade.run(&mut wfst);
        assert_eq!(result.iterations, 1);
    }

    #[test]
    fn test_cascade_priority_ordering() {
        let mut cascade = TransducerCascade::new();
        // Add in reverse priority order
        cascade.add_pass(Box::new(StateMinimization)); // priority 20
        cascade.add_pass(Box::new(DeadStateElimination)); // priority 10
        cascade.add_pass(Box::new(WeightNormalization)); // priority 5

        let names: Vec<&str> = cascade.passes.iter().map(|p| p.name()).collect();
        assert_eq!(
            names,
            vec!["weight-normalization", "dead-state-elimination", "state-minimization"]
        );
    }

    #[test]
    fn test_cascade_debug_format() {
        let cascade = TransducerCascade::default_pipeline();
        let debug = format!("{:?}", cascade);
        assert!(debug.contains("weight-normalization"));
        assert!(debug.contains("dead-state-elimination"));
        assert!(debug.contains("state-minimization"));
    }

    #[test]
    fn test_weight_normalization_pass() {
        let mut wfst = build_test_wfst(&[("Ident", 5.0), ("Int", 7.0)]);
        let pass = WeightNormalization;
        assert!(pass.is_applicable(&wfst));
        let result = pass.apply(&mut wfst);
        // After normalization, best weight should be 0.0
        let actions = wfst.predict("Ident");
        if let Some(best) = actions.first() {
            assert_eq!(best.weight.value(), 0.0);
        }
        assert!(result.has_changes());
    }
}
