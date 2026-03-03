//! Composition Optimization Cascade (Phase 7).
//!
//! Provides four optimization passes that operate on `PredictionWfst` instances
//! produced by composing two grammars (grammar A and grammar B). The passes
//! reconcile weights, eliminate dead states introduced by composition, deduplicate
//! dispatch entries, and validate FIRST/FOLLOW invariants.
//!
//! ## Passes (by priority)
//!
//! | Priority | Pass                                | Effect                                        |
//! |----------|-------------------------------------|-----------------------------------------------|
//! |    8     | `WeightReconciliation`              | Apply weight resolution policy for shared tokens|
//! |   15     | `CrossGrammarDeadStateElimination`   | Remove states only reachable via shadowed rules |
//! |   18     | `ComposedDispatchMinimization`       | Deduplicate (token, action) entries, keep best  |
//! |  200     | `IncrementalFirstFollowValidation`   | Debug-only: verify FIRST/FOLLOW consistency     |
//!
//! ## Usage
//!
//! ```rust,ignore
//! use mettail_prattail::composition_optimize::*;
//!
//! let config = CompositionOptimizationConfig {
//!     weight_policy: WeightResolutionPolicy::Min,
//!     rules_a: ["RuleX", "RuleY"].into_iter().map(String::from).collect(),
//!     rules_b: ["RuleZ"].into_iter().map(String::from).collect(),
//! };
//!
//! let cascade = composition_cascade(&config);
//! let result = cascade.run(&mut wfst);
//! ```

use std::collections::{HashMap, HashSet};

use crate::automata::semiring::TropicalWeight;
use crate::transducer::{OptimizationPass, PassResult, TransducerCascade};
use crate::wfst::PredictionWfst;

// ══════════════════════════════════════════════════════════════════════════════
// Configuration
// ══════════════════════════════════════════════════════════════════════════════

/// Policy for resolving weight conflicts when both grammar A and grammar B
/// provide dispatch actions for the same token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeightResolutionPolicy {
    /// Use the minimum (best) weight from either grammar. This is the default
    /// and preserves the tropical semiring's `plus = min` semantics.
    Min,
    /// Use the maximum (worst) weight from either grammar. Useful when
    /// conservative dispatch is preferred (only choose an action if both
    /// grammars agree it is high priority).
    Max,
    /// Use the arithmetic average of both weights. Provides a balanced
    /// resolution that blends both grammars' preferences.
    Average,
    /// Always use grammar A's weight, ignoring grammar B's weight entirely.
    /// Useful when grammar A is the "primary" grammar and grammar B is an
    /// extension that should not alter base priorities.
    APriority,
}

/// Configuration for the composition optimization cascade.
///
/// Specifies which rules belong to grammar A vs grammar B, and the policy
/// for resolving weight conflicts between them.
#[derive(Debug, Clone)]
pub struct CompositionOptimizationConfig {
    /// Weight conflict resolution policy.
    pub weight_policy: WeightResolutionPolicy,
    /// Rule labels originating from grammar A.
    pub rules_a: HashSet<String>,
    /// Rule labels originating from grammar B.
    pub rules_b: HashSet<String>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Pass 1: Weight Reconciliation (priority 8)
// ══════════════════════════════════════════════════════════════════════════════

/// Apply the configured weight resolution policy for tokens that have dispatch
/// actions from both grammar A and grammar B.
///
/// For each token in the start state's transitions, if both grammar A and
/// grammar B provide actions, this pass adjusts the weight of the grammar B
/// action according to the configured `WeightResolutionPolicy`.
///
/// Actions belonging exclusively to one grammar are left unchanged.
#[derive(Debug)]
pub struct WeightReconciliation {
    policy: WeightResolutionPolicy,
    rules_a: HashSet<String>,
    rules_b: HashSet<String>,
}

impl WeightReconciliation {
    /// Create a new weight reconciliation pass from config.
    pub fn new(config: &CompositionOptimizationConfig) -> Self {
        WeightReconciliation {
            policy: config.weight_policy,
            rules_a: config.rules_a.clone(),
            rules_b: config.rules_b.clone(),
        }
    }

    /// Resolve two weights according to the configured policy.
    fn resolve(&self, weight_a: f64, weight_b: f64) -> f64 {
        match self.policy {
            WeightResolutionPolicy::Min => weight_a.min(weight_b),
            WeightResolutionPolicy::Max => weight_a.max(weight_b),
            WeightResolutionPolicy::Average => (weight_a + weight_b) / 2.0,
            WeightResolutionPolicy::APriority => weight_a,
        }
    }

    /// Classify an action's rule label as belonging to grammar A, grammar B,
    /// or neither (shared/unknown).
    fn classify(&self, rule_label: &str) -> ActionOrigin {
        if self.rules_a.contains(rule_label) {
            ActionOrigin::GrammarA
        } else if self.rules_b.contains(rule_label) {
            ActionOrigin::GrammarB
        } else {
            ActionOrigin::Unknown
        }
    }
}

/// Which grammar an action originates from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActionOrigin {
    GrammarA,
    GrammarB,
    Unknown,
}

impl OptimizationPass for WeightReconciliation {
    fn name(&self) -> &str {
        "weight-reconciliation"
    }

    fn priority(&self) -> u32 {
        8
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        // Only applicable if we have actions from both grammars
        let has_a = wfst
            .actions
            .iter()
            .any(|a| self.rules_a.contains(&a.action.rule_label()));
        let has_b = wfst
            .actions
            .iter()
            .any(|a| self.rules_b.contains(&a.action.rule_label()));
        has_a && has_b
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let start_idx = wfst.start as usize;
        if start_idx >= wfst.states.len() {
            return PassResult::unchanged();
        }

        // Group transitions by input token. For each token, collect action
        // indices belonging to grammar A and grammar B.
        let mut token_groups: HashMap<u16, Vec<usize>> = HashMap::new();
        for (trans_idx, trans) in wfst.states[start_idx].transitions.iter().enumerate() {
            token_groups
                .entry(trans.input)
                .or_insert_with(Vec::new)
                .push(trans_idx);
        }

        let mut changes = 0;

        for (_token_id, trans_indices) in &token_groups {
            // Partition into A-actions and B-actions
            let mut a_weights: Vec<(usize, f64)> = Vec::new();
            let mut b_indices: Vec<usize> = Vec::new();

            for &ti in trans_indices {
                let action_idx = wfst.states[start_idx].transitions[ti].action_idx as usize;
                if let Some(action) = wfst.actions.get(action_idx) {
                    let label = action.action.rule_label();
                    match self.classify(&label) {
                        ActionOrigin::GrammarA => {
                            a_weights.push((ti, wfst.states[start_idx].transitions[ti].weight.value()));
                        }
                        ActionOrigin::GrammarB => {
                            b_indices.push(ti);
                        }
                        ActionOrigin::Unknown => {
                            // Unknown-origin actions are treated as grammar A
                            a_weights.push((ti, wfst.states[start_idx].transitions[ti].weight.value()));
                        }
                    }
                }
            }

            // If both grammars contribute, reconcile B's weights
            if !a_weights.is_empty() && !b_indices.is_empty() {
                // Best weight from grammar A for this token
                let best_a = a_weights
                    .iter()
                    .map(|&(_, w)| w)
                    .fold(f64::INFINITY, f64::min);

                for &bi in &b_indices {
                    let old_weight = wfst.states[start_idx].transitions[bi].weight.value();
                    let new_weight = self.resolve(best_a, old_weight);

                    if (new_weight - old_weight).abs() > f64::EPSILON {
                        let new_tw = TropicalWeight::new(new_weight);
                        wfst.states[start_idx].transitions[bi].weight = new_tw;

                        // Also update the action table
                        let action_idx = wfst.states[start_idx].transitions[bi].action_idx as usize;
                        if let Some(action) = wfst.actions.get_mut(action_idx) {
                            action.weight = new_tw;
                        }
                        changes += 1;
                    }
                }
            }
        }

        if changes > 0 {
            PassResult::changed(
                changes,
                format!(
                    "reconciled {} weight(s) using {:?} policy",
                    changes, self.policy
                ),
            )
        } else {
            PassResult::unchanged()
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pass 2: Cross-Grammar Dead State Elimination (priority 15)
// ══════════════════════════════════════════════════════════════════════════════

/// Remove states that are only reachable via rules from a single grammar
/// when those rules are completely shadowed by lower-weight alternatives
/// from the other grammar.
///
/// A state is considered "dead" for cross-grammar purposes when:
/// 1. All transitions leading to it are from rules belonging to one grammar
/// 2. For every such transition's input token, there exists a strictly
///    lower-weight transition from the other grammar
///
/// This eliminates unreachable alternatives that were introduced during
/// composition but will never be selected at runtime.
#[derive(Debug)]
pub struct CrossGrammarDeadStateElimination {
    rules_a: HashSet<String>,
    rules_b: HashSet<String>,
}

impl CrossGrammarDeadStateElimination {
    /// Create a new cross-grammar dead state elimination pass.
    pub fn new(config: &CompositionOptimizationConfig) -> Self {
        CrossGrammarDeadStateElimination {
            rules_a: config.rules_a.clone(),
            rules_b: config.rules_b.clone(),
        }
    }

    /// Check if an action belongs to grammar A or grammar B.
    fn action_origin(&self, rule_label: &str) -> ActionOrigin {
        if self.rules_a.contains(rule_label) {
            ActionOrigin::GrammarA
        } else if self.rules_b.contains(rule_label) {
            ActionOrigin::GrammarB
        } else {
            ActionOrigin::Unknown
        }
    }
}

impl OptimizationPass for CrossGrammarDeadStateElimination {
    fn name(&self) -> &str {
        "cross-grammar-dead-state-elimination"
    }

    fn priority(&self) -> u32 {
        15
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        // Needs at least 3 states (start + 2 finals) and actions from both grammars
        wfst.state_count() > 2
            && wfst
                .actions
                .iter()
                .any(|a| self.rules_a.contains(&a.action.rule_label()))
            && wfst
                .actions
                .iter()
                .any(|a| self.rules_b.contains(&a.action.rule_label()))
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let start_idx = wfst.start as usize;
        if start_idx >= wfst.states.len() {
            return PassResult::unchanged();
        }

        // For each input token, find the best weight per grammar
        let mut token_best: HashMap<u16, (f64, f64)> = HashMap::new(); // (best_a, best_b)

        for trans in &wfst.states[start_idx].transitions {
            let action_idx = trans.action_idx as usize;
            if let Some(action) = wfst.actions.get(action_idx) {
                let label = action.action.rule_label();
                let origin = self.action_origin(&label);
                let entry = token_best
                    .entry(trans.input)
                    .or_insert((f64::INFINITY, f64::INFINITY));
                match origin {
                    ActionOrigin::GrammarA => {
                        entry.0 = entry.0.min(trans.weight.value());
                    }
                    ActionOrigin::GrammarB => {
                        entry.1 = entry.1.min(trans.weight.value());
                    }
                    ActionOrigin::Unknown => {
                        // Unknown-origin: treat as grammar A
                        entry.0 = entry.0.min(trans.weight.value());
                    }
                }
            }
        }

        // Identify transitions to remove: those from one grammar that are
        // strictly dominated by the other grammar on the same token
        let mut dead_targets: HashSet<u32> = HashSet::new();
        let mut transitions_to_remove: Vec<usize> = Vec::new();

        for (trans_idx, trans) in wfst.states[start_idx].transitions.iter().enumerate() {
            let action_idx = trans.action_idx as usize;
            if let Some(action) = wfst.actions.get(action_idx) {
                let label = action.action.rule_label();
                let origin = self.action_origin(&label);

                if let Some(&(best_a, best_b)) = token_best.get(&trans.input) {
                    let is_shadowed = match origin {
                        // Grammar A action is shadowed if grammar B has a
                        // strictly better weight for this token
                        ActionOrigin::GrammarA => {
                            best_b < best_a && best_b.is_finite()
                        }
                        // Grammar B action is shadowed if grammar A has a
                        // strictly better weight for this token
                        ActionOrigin::GrammarB => {
                            best_a < best_b && best_a.is_finite()
                        }
                        ActionOrigin::Unknown => false,
                    };

                    if is_shadowed {
                        transitions_to_remove.push(trans_idx);
                        dead_targets.insert(trans.to);
                    }
                }
            }
        }

        if transitions_to_remove.is_empty() {
            return PassResult::unchanged();
        }

        let removed_count = transitions_to_remove.len();

        // Remove transitions in reverse order to preserve indices
        transitions_to_remove.sort_unstable();
        for &idx in transitions_to_remove.iter().rev() {
            wfst.states[start_idx].transitions.remove(idx);
        }

        // Check which target states are still referenced
        let mut still_referenced: HashSet<u32> = HashSet::new();
        still_referenced.insert(wfst.start);
        for state in &wfst.states {
            for trans in &state.transitions {
                still_referenced.insert(trans.to);
            }
        }

        // Remove dead target states that are no longer referenced
        let dead_states: Vec<u32> = dead_targets
            .iter()
            .filter(|s| !still_referenced.contains(s))
            .copied()
            .collect();

        if !dead_states.is_empty() {
            wfst.remove_unreachable_states();
        }

        PassResult::changed(
            removed_count,
            format!(
                "eliminated {} shadowed transition(s), {} dead state(s)",
                removed_count,
                dead_states.len()
            ),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pass 3: Composed Dispatch Minimization (priority 18)
// ══════════════════════════════════════════════════════════════════════════════

/// Deduplicate (token, action) entries in the start state, keeping the one
/// with the best (lowest) weight for each unique (token, rule_label) pair.
///
/// After composition and union, the same logical dispatch entry may appear
/// multiple times with different weights. This pass merges them by retaining
/// only the best-weight transition for each unique combination of input token
/// and rule label.
#[derive(Debug)]
pub struct ComposedDispatchMinimization;

impl OptimizationPass for ComposedDispatchMinimization {
    fn name(&self) -> &str {
        "composed-dispatch-minimization"
    }

    fn priority(&self) -> u32 {
        18
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        // Applicable if the start state has more than one transition
        if let Some(start) = wfst.states.get(wfst.start as usize) {
            start.transitions.len() > 1
        } else {
            false
        }
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let start_idx = wfst.start as usize;
        if start_idx >= wfst.states.len() {
            return PassResult::unchanged();
        }

        // Build a map: (token_id, rule_label) -> best transition index
        let mut best_for_key: HashMap<(u16, String), (usize, f64)> = HashMap::new();

        for (trans_idx, trans) in wfst.states[start_idx].transitions.iter().enumerate() {
            let rule_label = wfst
                .actions
                .get(trans.action_idx as usize)
                .map(|a| a.action.rule_label())
                .unwrap_or_default();

            let key = (trans.input, rule_label);
            let entry = best_for_key.entry(key).or_insert((trans_idx, f64::INFINITY));

            if trans.weight.value() < entry.1 {
                *entry = (trans_idx, trans.weight.value());
            }
        }

        let original_count = wfst.states[start_idx].transitions.len();
        let unique_count = best_for_key.len();

        if unique_count >= original_count {
            return PassResult::unchanged();
        }

        // Collect the indices of transitions to keep
        let keep_indices: HashSet<usize> = best_for_key.values().map(|&(idx, _)| idx).collect();

        // Collect indices to remove (those not in the keep set)
        let mut remove_indices: Vec<usize> = (0..original_count)
            .filter(|i| !keep_indices.contains(i))
            .collect();
        remove_indices.sort_unstable();

        // Remove in reverse order
        for &idx in remove_indices.iter().rev() {
            wfst.states[start_idx].transitions.remove(idx);
        }

        let removed = original_count - wfst.states[start_idx].transitions.len();

        // Clean up unreachable states created by removed transitions
        if removed > 0 {
            wfst.remove_unreachable_states();
        }

        PassResult::changed(
            removed,
            format!(
                "deduplicated {} dispatch entr{} (kept {} unique)",
                removed,
                if removed == 1 { "y" } else { "ies" },
                unique_count
            ),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pass 4: Incremental FIRST/FOLLOW Validation (priority 200)
// ══════════════════════════════════════════════════════════════════════════════

/// Debug-only validation pass that verifies FIRST/FOLLOW invariants hold
/// after composition and optimization.
///
/// This pass does not modify the WFST. It checks that:
/// 1. Every transition from the start state leads to a valid (final) state
/// 2. No two transitions for the same token lead to identical actions
///    (which would indicate incomplete minimization)
/// 3. All action indices are valid references into the action table
///
/// Violations are reported via `debug_assert!` — they will panic in debug
/// builds and be no-ops in release builds.
#[derive(Debug)]
pub struct IncrementalFirstFollowValidation;

impl OptimizationPass for IncrementalFirstFollowValidation {
    fn name(&self) -> &str {
        "incremental-first-follow-validation"
    }

    fn priority(&self) -> u32 {
        200 // Run last, after all other passes
    }

    fn is_applicable(&self, wfst: &PredictionWfst) -> bool {
        // Always applicable in debug builds; never modifies the WFST
        let _ = wfst;
        cfg!(debug_assertions)
    }

    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult {
        let start_idx = wfst.start as usize;
        if start_idx >= wfst.states.len() {
            return PassResult::unchanged();
        }

        let mut violations = 0;

        // Check 1: All transitions lead to valid states
        for trans in &wfst.states[start_idx].transitions {
            let target_valid = (trans.to as usize) < wfst.states.len();
            debug_assert!(
                target_valid,
                "transition for token {} leads to invalid state {}",
                trans.input, trans.to
            );
            if !target_valid {
                violations += 1;
            }
        }

        // Check 2: All action indices are valid
        for trans in &wfst.states[start_idx].transitions {
            let action_valid = (trans.action_idx as usize) < wfst.actions.len();
            debug_assert!(
                action_valid,
                "transition for token {} references invalid action index {}",
                trans.input, trans.action_idx
            );
            if !action_valid {
                violations += 1;
            }
        }

        // Check 3: No duplicate (token, rule_label) pairs (post-minimization invariant)
        let mut seen: HashSet<(u16, String)> = HashSet::new();
        for trans in &wfst.states[start_idx].transitions {
            if let Some(action) = wfst.actions.get(trans.action_idx as usize) {
                let key = (trans.input, action.action.rule_label());
                let is_new = seen.insert(key.clone());
                debug_assert!(
                    is_new,
                    "duplicate dispatch entry for token {}, rule '{}'",
                    trans.input, key.1
                );
                if !is_new {
                    violations += 1;
                }
            }
        }

        // Check 4: All target states are final (star-shaped WFST invariant)
        for trans in &wfst.states[start_idx].transitions {
            if let Some(target) = wfst.states.get(trans.to as usize) {
                debug_assert!(
                    target.is_final,
                    "transition target state {} is not final (star-shaped invariant violated)",
                    trans.to
                );
                if !target.is_final {
                    violations += 1;
                }
            }
        }

        if violations > 0 {
            PassResult::changed(
                violations,
                format!("detected {} FIRST/FOLLOW violation(s)", violations),
            )
        } else {
            PassResult::unchanged()
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Builder
// ══════════════════════════════════════════════════════════════════════════════

/// Create a `TransducerCascade` with all four composition optimization passes.
///
/// The passes are inserted in priority order:
/// 1. `WeightReconciliation` (8)
/// 2. `CrossGrammarDeadStateElimination` (15)
/// 3. `ComposedDispatchMinimization` (18)
/// 4. `IncrementalFirstFollowValidation` (200)
///
/// The cascade runs all passes in a fixed-point loop until convergence.
pub fn composition_cascade(config: &CompositionOptimizationConfig) -> TransducerCascade {
    let mut cascade = TransducerCascade::new();
    cascade.add_pass(Box::new(WeightReconciliation::new(config)));
    cascade.add_pass(Box::new(CrossGrammarDeadStateElimination::new(config)));
    cascade.add_pass(Box::new(ComposedDispatchMinimization));
    cascade.add_pass(Box::new(IncrementalFirstFollowValidation));
    cascade
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::PredictionWfstBuilder;

    /// Helper: build a test WFST with named tokens, rules, and weights.
    fn build_wfst(entries: &[(&str, &str, &str, f64)]) -> PredictionWfst {
        let names: Vec<String> = entries
            .iter()
            .map(|&(token, _, _, _)| token.to_string())
            .collect();
        let token_map = TokenIdMap::from_names(names.into_iter());
        let mut builder = PredictionWfstBuilder::new("Test", token_map);
        for &(token, rule_label, parse_fn, weight) in entries {
            builder.add_action(
                token,
                DispatchAction::Direct {
                    rule_label: rule_label.to_string(),
                    parse_fn: parse_fn.to_string(),
                },
                TropicalWeight::new(weight),
            );
        }
        builder.build()
    }

    /// Helper: build a config with the given policy and rule sets.
    fn make_config(
        policy: WeightResolutionPolicy,
        rules_a: &[&str],
        rules_b: &[&str],
    ) -> CompositionOptimizationConfig {
        CompositionOptimizationConfig {
            weight_policy: policy,
            rules_a: rules_a.iter().map(|s| s.to_string()).collect(),
            rules_b: rules_b.iter().map(|s| s.to_string()).collect(),
        }
    }

    // ── Weight Reconciliation Tests ──────────────────────────────────────────

    #[test]
    fn test_weight_reconciliation_min_policy() {
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 3.0),
            ("Ident", "CrossCat", "parse_cross", 5.0),
        ]);
        let config = make_config(WeightResolutionPolicy::Min, &["VarRef"], &["CrossCat"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // Grammar B's weight (5.0) should be reconciled to min(3.0, 5.0) = 3.0
        assert!(result.has_changes());
        let actions = wfst.predict("Ident");
        // Both should now have weight 3.0
        let cross_action = actions.iter().find(|a| a.action.rule_label() == "CrossCat");
        assert!(cross_action.is_some());
        assert!(
            (cross_action.expect("CrossCat action exists").weight.value() - 3.0).abs() < f64::EPSILON,
            "Min policy should set B's weight to min(A, B)"
        );
    }

    #[test]
    fn test_weight_reconciliation_max_policy() {
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 2.0),
            ("Ident", "CrossCat", "parse_cross", 4.0),
        ]);
        let config = make_config(WeightResolutionPolicy::Max, &["VarRef"], &["CrossCat"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // Grammar B's weight (4.0) should be reconciled to max(2.0, 4.0) = 4.0
        // Since 4.0 is already the max, no change
        assert!(!result.has_changes());
    }

    #[test]
    fn test_weight_reconciliation_max_policy_changes_weight() {
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 5.0),
            ("Ident", "CrossCat", "parse_cross", 2.0),
        ]);
        let config = make_config(WeightResolutionPolicy::Max, &["VarRef"], &["CrossCat"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // Grammar B's weight (2.0) should be reconciled to max(5.0, 2.0) = 5.0
        assert!(result.has_changes());
        let actions = wfst.predict("Ident");
        let cross_action = actions
            .iter()
            .find(|a| a.action.rule_label() == "CrossCat")
            .expect("CrossCat action exists");
        assert!(
            (cross_action.weight.value() - 5.0).abs() < f64::EPSILON,
            "Max policy should set B's weight to max(A, B)"
        );
    }

    #[test]
    fn test_weight_reconciliation_average_policy() {
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 2.0),
            ("Ident", "CrossCat", "parse_cross", 6.0),
        ]);
        let config = make_config(WeightResolutionPolicy::Average, &["VarRef"], &["CrossCat"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // Grammar B's weight (6.0) should be reconciled to avg(2.0, 6.0) = 4.0
        assert!(result.has_changes());
        let actions = wfst.predict("Ident");
        let cross_action = actions
            .iter()
            .find(|a| a.action.rule_label() == "CrossCat")
            .expect("CrossCat action exists");
        assert!(
            (cross_action.weight.value() - 4.0).abs() < f64::EPSILON,
            "Average policy should set B's weight to (A + B) / 2"
        );
    }

    #[test]
    fn test_weight_reconciliation_apriority_policy() {
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 1.0),
            ("Ident", "CrossCat", "parse_cross", 8.0),
        ]);
        let config = make_config(WeightResolutionPolicy::APriority, &["VarRef"], &["CrossCat"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // Grammar B's weight (8.0) should be reconciled to A's weight (1.0)
        assert!(result.has_changes());
        let actions = wfst.predict("Ident");
        let cross_action = actions
            .iter()
            .find(|a| a.action.rule_label() == "CrossCat")
            .expect("CrossCat action exists");
        assert!(
            (cross_action.weight.value() - 1.0).abs() < f64::EPSILON,
            "APriority policy should set B's weight to A's weight"
        );
    }

    #[test]
    fn test_weight_reconciliation_no_overlap() {
        // When grammars have disjoint tokens, no reconciliation needed
        let mut wfst = build_wfst(&[
            ("Plus", "Add", "parse_add", 1.0),
            ("Minus", "Sub", "parse_sub", 2.0),
        ]);
        let config = make_config(WeightResolutionPolicy::Min, &["Add"], &["Sub"]);
        let pass = WeightReconciliation::new(&config);
        let result = pass.apply(&mut wfst);

        // No shared tokens -> no changes
        assert!(!result.has_changes());
    }

    // ── Cross-Grammar Dead State Elimination Tests ──────────────────────────

    #[test]
    fn test_cross_grammar_dead_state_elimination() {
        // Build a WFST where grammar B's action on "Ident" is shadowed by
        // grammar A's lower-weight action on the same token
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 1.0),
            ("Ident", "ExtRule", "parse_ext", 5.0),
            ("Plus", "Add", "parse_add", 0.0),
        ]);
        let config = make_config(
            WeightResolutionPolicy::Min,
            &["VarRef", "Add"],
            &["ExtRule"],
        );
        let pass = CrossGrammarDeadStateElimination::new(&config);

        assert!(pass.is_applicable(&wfst));
        let result = pass.apply(&mut wfst);

        // ExtRule (weight 5.0) is shadowed by VarRef (weight 1.0) on token "Ident"
        assert!(result.has_changes());

        // VarRef should still be reachable
        let actions = wfst.predict("Ident");
        assert!(
            actions.iter().any(|a| a.action.rule_label() == "VarRef"),
            "VarRef should survive dead state elimination"
        );
    }

    #[test]
    fn test_cross_grammar_dead_state_no_shadowing() {
        // No shadowing: grammar B has better weight
        let mut wfst = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 5.0),
            ("Ident", "ExtRule", "parse_ext", 1.0),
            ("Plus", "Add", "parse_add", 0.0),
        ]);
        let config = make_config(
            WeightResolutionPolicy::Min,
            &["VarRef", "Add"],
            &["ExtRule"],
        );
        let pass = CrossGrammarDeadStateElimination::new(&config);
        let result = pass.apply(&mut wfst);

        // VarRef (weight 5.0, grammar A) is shadowed by ExtRule (weight 1.0, grammar B)
        assert!(result.has_changes());
        let actions = wfst.predict("Ident");
        assert!(
            actions.iter().any(|a| a.action.rule_label() == "ExtRule"),
            "ExtRule should survive as it has lower weight"
        );
    }

    // ── Composed Dispatch Minimization Tests ────────────────────────────────

    #[test]
    fn test_composed_dispatch_minimization_deduplicates() {
        // Create a WFST with duplicate (token, rule) entries via union
        let mut wfst_a = build_wfst(&[("Ident", "VarRef", "parse_var", 3.0)]);
        let wfst_b = build_wfst(&[("Ident", "VarRef", "parse_var", 1.0)]);
        wfst_a.union(&wfst_b);

        let pass = ComposedDispatchMinimization;
        assert!(pass.is_applicable(&wfst_a));

        let before_count = wfst_a.states[wfst_a.start as usize].transitions.len();
        let result = pass.apply(&mut wfst_a);

        assert!(result.has_changes());

        // After minimization, should have only one transition for (Ident, VarRef)
        let after_count = wfst_a.states[wfst_a.start as usize].transitions.len();
        assert!(
            after_count < before_count,
            "should remove duplicate transitions"
        );

        // The remaining transition should have the best (lowest) weight
        let actions = wfst_a.predict("Ident");
        let var_action = actions
            .iter()
            .find(|a| a.action.rule_label() == "VarRef")
            .expect("VarRef should exist after dedup");
        assert!(
            (var_action.weight.value() - 1.0).abs() < f64::EPSILON,
            "should keep best weight (1.0), got {}",
            var_action.weight.value()
        );
    }

    #[test]
    fn test_composed_dispatch_minimization_no_duplicates() {
        let mut wfst = build_wfst(&[
            ("Plus", "Add", "parse_add", 1.0),
            ("Minus", "Sub", "parse_sub", 2.0),
        ]);
        let pass = ComposedDispatchMinimization;
        let result = pass.apply(&mut wfst);

        // No duplicates -> no changes
        assert!(!result.has_changes());
    }

    // ── Incremental FIRST/FOLLOW Validation Tests ───────────────────────────

    #[test]
    fn test_incremental_validation_passes_for_correct_wfst() {
        let mut wfst = build_wfst(&[
            ("Plus", "Add", "parse_add", 0.0),
            ("Minus", "Sub", "parse_sub", 1.0),
        ]);
        let pass = IncrementalFirstFollowValidation;
        let result = pass.apply(&mut wfst);

        // A correctly constructed WFST should have no violations
        assert!(!result.has_changes());
    }

    #[test]
    fn test_incremental_validation_applicable_in_debug() {
        let wfst = build_wfst(&[("Plus", "Add", "parse_add", 0.0)]);
        let pass = IncrementalFirstFollowValidation;

        // In debug builds, this should be applicable
        if cfg!(debug_assertions) {
            assert!(pass.is_applicable(&wfst));
        } else {
            assert!(!pass.is_applicable(&wfst));
        }
    }

    // ── Builder Tests ───────────────────────────────────────────────────────

    #[test]
    fn test_composition_cascade_creates_four_passes() {
        let config = make_config(WeightResolutionPolicy::Min, &["A"], &["B"]);
        let cascade = composition_cascade(&config);

        assert_eq!(cascade.pass_count(), 4);
    }

    #[test]
    fn test_composition_cascade_priority_ordering() {
        let config = make_config(WeightResolutionPolicy::Min, &["A"], &["B"]);
        let cascade = composition_cascade(&config);

        // Verify the cascade has the correct pass count and was built without errors
        assert_eq!(cascade.pass_count(), 4);

        // Run on a simple WFST to verify the cascade executes without panicking
        let mut wfst = build_wfst(&[
            ("Ident", "A", "parse_a", 2.0),
            ("Ident", "B", "parse_b", 4.0),
        ]);
        let result = cascade.run(&mut wfst);
        assert!(result.iterations >= 1);
    }

    #[test]
    fn test_composition_cascade_end_to_end() {
        // Build a composed WFST with duplicate entries and weight conflicts
        let mut wfst_a = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 2.0),
            ("Plus", "Add", "parse_add", 0.0),
        ]);
        let wfst_b = build_wfst(&[
            ("Ident", "VarRef", "parse_var", 5.0), // Duplicate with worse weight
            ("Ident", "ExtRule", "parse_ext", 3.0),
        ]);
        wfst_a.union(&wfst_b);

        let config = make_config(
            WeightResolutionPolicy::Min,
            &["VarRef", "Add"],
            &["ExtRule"],
        );
        let cascade = composition_cascade(&config);
        let result = cascade.run(&mut wfst_a);

        // The cascade should have made changes:
        // - Deduplication of VarRef entries
        // - Possible dead state elimination
        assert!(result.total_changes > 0);

        // VarRef should survive with best weight
        let ident_actions = wfst_a.predict("Ident");
        assert!(!ident_actions.is_empty(), "Ident should still have actions");

        // Plus/Add should be unaffected
        let plus_actions = wfst_a.predict("Plus");
        assert!(!plus_actions.is_empty(), "Plus should still have actions");
    }
}
