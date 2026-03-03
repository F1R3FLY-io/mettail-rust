//! Composition Verification Transducer (CVT) for composed WFSTs.
//!
//! Verifies four correctness properties of WFST composition results:
//!
//! 1. **LanguageContainment** — Every `(token, action)` pair in each source WFST
//!    exists in the merged WFST. The merged grammar must accept at least the union
//!    of both source grammars.
//!
//! 2. **NoSpuriousActions** — The merged WFST introduces no phantom actions that
//!    do not originate from either source. Every action in the merged WFST must
//!    have a corresponding action (by rule label) in A or B.
//!
//! 3. **WeightConsistency** — For shared categories, the merged weight for each
//!    action is consistent with the source weight. Specifically, the merged weight
//!    must equal the source weight when the action exists in only one source, and
//!    must equal the minimum (tropical `plus`) when both sources provide it.
//!
//! 4. **DispatchDeterminismPreservation** — Tokens that are deterministic (single
//!    dispatch action) in both source WFSTs remain bounded in the merged WFST.
//!    When merging introduces additional alternatives for a previously-deterministic
//!    token, a warning is emitted (not a failure, since union inherently can
//!    increase ambiguity).
//!
//! ## Architecture
//!
//! ```text
//!   WFSTs A    WFSTs B    WFSTs merged
//!      │          │            │
//!      └──────────┼────────────┘
//!                 ▼
//!     verify_composition(A, B, merged, shared_cats)
//!                 │
//!       ┌─────────┼──────────────────────┐
//!       │         │                      │
//!       ▼         ▼                      ▼
//!   P1: Language  P2: No Spurious   P3: Weight
//!   Containment   Actions           Consistency
//!       │         │                      │
//!       │         └───────────┬──────────┘
//!       │                     │
//!       │              P4: Determinism
//!       │              Preservation
//!       │                     │
//!       └─────────────────────┘
//!                 │
//!                 ▼
//!     CompositionVerificationReport
//! ```
//!
//! ## Theorems
//!
//! See `prattail/docs/theory/wfst/composition-correctness.md` for formal
//! definitions and proofs of each property.

use std::collections::{HashMap, HashSet};

use crate::wfst::PredictionWfst;

// ══════════════════════════════════════════════════════════════════════════════
// Types
// ══════════════════════════════════════════════════════════════════════════════

/// The four correctness properties verified by the CVT.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerificationProperty {
    /// Every (token, action) in source WFSTs exists in the merged WFST.
    LanguageContainment,
    /// No phantom actions introduced by the merge operation.
    NoSpuriousActions,
    /// Shared actions have correct weight resolution (tropical min).
    WeightConsistency,
    /// Tokens deterministic in both sources remain bounded in merged.
    DispatchDeterminismPreservation,
}

impl std::fmt::Display for VerificationProperty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationProperty::LanguageContainment => write!(f, "LanguageContainment"),
            VerificationProperty::NoSpuriousActions => write!(f, "NoSpuriousActions"),
            VerificationProperty::WeightConsistency => write!(f, "WeightConsistency"),
            VerificationProperty::DispatchDeterminismPreservation => {
                write!(f, "DispatchDeterminismPreservation")
            }
        }
    }
}

/// A single violation of a verification property.
#[derive(Debug, Clone)]
pub struct PropertyViolation {
    /// Category where the violation was detected.
    pub category: String,
    /// Token involved (if applicable).
    pub token: Option<String>,
    /// Human-readable description of the violation.
    pub message: String,
    /// Source of the violation: `"A"`, `"B"`, or `"merged"`.
    pub source: String,
}

impl std::fmt::Display for PropertyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.token {
            Some(tok) => write!(
                f,
                "[{}] category '{}', token '{}': {} (source: {})",
                self.source, self.category, tok, self.message, self.source
            ),
            None => write!(
                f,
                "[{}] category '{}': {} (source: {})",
                self.source, self.category, self.message, self.source
            ),
        }
    }
}

/// Result of checking a single verification property.
#[derive(Debug, Clone)]
pub struct PropertyResult {
    /// Which property was checked.
    pub property: VerificationProperty,
    /// Whether the property holds (no violations).
    pub holds: bool,
    /// All violations found (empty if `holds` is true).
    pub violations: Vec<PropertyViolation>,
}

/// Complete verification report for a WFST composition.
#[derive(Debug, Clone)]
pub struct CompositionVerificationReport {
    /// Results for each of the four properties.
    pub results: Vec<PropertyResult>,
    /// Whether all four properties hold.
    pub all_pass: bool,
}

impl std::fmt::Display for CompositionVerificationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Composition Verification Report")?;
        writeln!(f, "  All pass: {}", self.all_pass)?;
        for result in &self.results {
            let status = if result.holds { "PASS" } else { "FAIL" };
            writeln!(f, "  [{}] {}", status, result.property)?;
            for violation in &result.violations {
                writeln!(f, "    - {}", violation)?;
            }
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core verification
// ══════════════════════════════════════════════════════════════════════════════

/// Verify the four correctness properties of a WFST composition.
///
/// # Arguments
///
/// * `wfsts_a` — Per-category prediction WFSTs from grammar A.
/// * `wfsts_b` — Per-category prediction WFSTs from grammar B.
/// * `wfsts_merged` — Per-category prediction WFSTs after union/merge.
/// * `shared_categories` — Categories present in both A and B (from `CompositionSummary`).
///
/// # Returns
///
/// A `CompositionVerificationReport` with results for all four properties.
pub fn verify_composition(
    wfsts_a: &HashMap<String, PredictionWfst>,
    wfsts_b: &HashMap<String, PredictionWfst>,
    wfsts_merged: &HashMap<String, PredictionWfst>,
    shared_categories: &[String],
) -> CompositionVerificationReport {
    let p1 = verify_language_containment(wfsts_a, wfsts_b, wfsts_merged);
    let p2 = verify_no_spurious_actions(wfsts_a, wfsts_b, wfsts_merged);
    let p3 = verify_weight_consistency(wfsts_a, wfsts_b, wfsts_merged, shared_categories);
    let p4 = verify_dispatch_determinism(wfsts_a, wfsts_b, wfsts_merged);

    let all_pass = p1.holds && p2.holds && p3.holds && p4.holds;

    CompositionVerificationReport {
        results: vec![p1, p2, p3, p4],
        all_pass,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P1: Language Containment
// ══════════════════════════════════════════════════════════════════════════════

/// Collect all `(token_name, rule_label)` pairs from a PredictionWfst.
///
/// Enumerates all tokens via the token map's iterator, queries `predict()`
/// for each, and collects the `(token, rule_label)` pairs.
fn collect_token_action_pairs(wfst: &PredictionWfst) -> HashSet<(String, String)> {
    let mut pairs = HashSet::new();
    for (token_name, _token_id) in wfst.token_map.iter() {
        for action in wfst.predict(token_name) {
            pairs.insert((token_name.to_string(), action.action.rule_label()));
        }
    }
    pairs
}

/// **P1: LanguageContainment** — Every `(token, action)` in each source WFST
/// must exist in the merged WFST for the same category.
///
/// For each source WFST (A and B), enumerates all tokens via `token_map.iter()`,
/// queries `predict()` for each token, and checks that every returned action
/// (identified by `rule_label()`) also appears in the merged WFST's predictions
/// for the same token.
fn verify_language_containment(
    wfsts_a: &HashMap<String, PredictionWfst>,
    wfsts_b: &HashMap<String, PredictionWfst>,
    wfsts_merged: &HashMap<String, PredictionWfst>,
) -> PropertyResult {
    let mut violations = Vec::new();

    // Check A ⊆ merged
    check_containment(wfsts_a, wfsts_merged, "A", &mut violations);
    // Check B ⊆ merged
    check_containment(wfsts_b, wfsts_merged, "B", &mut violations);

    PropertyResult {
        property: VerificationProperty::LanguageContainment,
        holds: violations.is_empty(),
        violations,
    }
}

/// Check that every (token, action) in `source_wfsts` exists in `merged_wfsts`.
fn check_containment(
    source_wfsts: &HashMap<String, PredictionWfst>,
    merged_wfsts: &HashMap<String, PredictionWfst>,
    source_label: &str,
    violations: &mut Vec<PropertyViolation>,
) {
    for (category, source_wfst) in source_wfsts {
        let merged_wfst = match merged_wfsts.get(category) {
            Some(w) => w,
            None => {
                // Entire category missing from merged — every action is a violation
                let pairs = collect_token_action_pairs(source_wfst);
                if !pairs.is_empty() {
                    violations.push(PropertyViolation {
                        category: category.clone(),
                        token: None,
                        message: format!(
                            "category missing from merged WFSTs ({} actions lost)",
                            pairs.len()
                        ),
                        source: source_label.to_string(),
                    });
                }
                continue;
            }
        };

        // Collect merged actions per token for efficient lookup
        let merged_pairs = collect_token_action_pairs(merged_wfst);

        // Check each source (token, action) exists in merged
        for (token_name, _token_id) in source_wfst.token_map.iter() {
            for action in source_wfst.predict(token_name) {
                let label = action.action.rule_label();
                if !merged_pairs.contains(&(token_name.to_string(), label.clone())) {
                    violations.push(PropertyViolation {
                        category: category.clone(),
                        token: Some(token_name.to_string()),
                        message: format!(
                            "action '{}' for token '{}' missing from merged WFST",
                            label, token_name
                        ),
                        source: source_label.to_string(),
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P2: No Spurious Actions
// ══════════════════════════════════════════════════════════════════════════════

/// **P2: NoSpuriousActions** — Every action in the merged WFST must originate
/// from A or B. No phantom actions may be introduced by the merge operation.
///
/// For each merged WFST, enumerates all `(token, action)` pairs and verifies
/// that each action's `rule_label()` appears in at least one source WFST's
/// actions for the same category.
fn verify_no_spurious_actions(
    wfsts_a: &HashMap<String, PredictionWfst>,
    wfsts_b: &HashMap<String, PredictionWfst>,
    wfsts_merged: &HashMap<String, PredictionWfst>,
) -> PropertyResult {
    let mut violations = Vec::new();

    for (category, merged_wfst) in wfsts_merged {
        // Collect all rule labels from A and B for this category
        let labels_a: HashSet<String> = wfsts_a
            .get(category)
            .map(|w| {
                collect_token_action_pairs(w)
                    .into_iter()
                    .map(|(_, label)| label)
                    .collect()
            })
            .unwrap_or_default();

        let labels_b: HashSet<String> = wfsts_b
            .get(category)
            .map(|w| {
                collect_token_action_pairs(w)
                    .into_iter()
                    .map(|(_, label)| label)
                    .collect()
            })
            .unwrap_or_default();

        // Check each merged action is traceable to A or B
        for (token_name, _token_id) in merged_wfst.token_map.iter() {
            for action in merged_wfst.predict(token_name) {
                let label = action.action.rule_label();
                if !labels_a.contains(&label) && !labels_b.contains(&label) {
                    violations.push(PropertyViolation {
                        category: category.clone(),
                        token: Some(token_name.to_string()),
                        message: format!(
                            "spurious action '{}' in merged WFST not found in A or B",
                            label
                        ),
                        source: "merged".to_string(),
                    });
                }
            }
        }
    }

    PropertyResult {
        property: VerificationProperty::NoSpuriousActions,
        holds: violations.is_empty(),
        violations,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P3: Weight Consistency
// ══════════════════════════════════════════════════════════════════════════════

/// **P3: WeightConsistency** — For shared categories, the best (minimum)
/// weight for each `(token, action)` pair in the merged WFST must be
/// consistent with the source weights.
///
/// `PredictionWfst::union()` preserves all transitions from both sources,
/// so the merged WFST may contain duplicate `(token, label)` entries with
/// different weights. The check compares the **best** (minimum) merged weight
/// against the expected minimum from the sources:
///
/// - If the action exists in only one source, the best merged weight must
///   equal the source weight.
/// - If the action exists in both sources, the best merged weight must equal
///   `min(weight_A, weight_B)` (tropical `plus`).
///
/// Weight comparison uses a tolerance of `1e-9` to account for floating-point
/// representation.
fn verify_weight_consistency(
    wfsts_a: &HashMap<String, PredictionWfst>,
    wfsts_b: &HashMap<String, PredictionWfst>,
    wfsts_merged: &HashMap<String, PredictionWfst>,
    shared_categories: &[String],
) -> PropertyResult {
    let mut violations = Vec::new();
    const WEIGHT_TOLERANCE: f64 = 1e-9;

    for category in shared_categories {
        let (wfst_a, wfst_b, merged_wfst) = match (
            wfsts_a.get(category),
            wfsts_b.get(category),
            wfsts_merged.get(category),
        ) {
            (Some(a), Some(b), Some(m)) => (a, b, m),
            _ => continue, // Only check categories present in both sources and merged
        };

        // Build (token, label) -> best weight maps for A, B, and merged
        let weights_a = collect_token_action_weights(wfst_a);
        let weights_b = collect_token_action_weights(wfst_b);
        let weights_merged = collect_token_action_weights(merged_wfst);

        // Check each unique (token, label) pair in the merged WFST
        for (key, merged_best_weight) in &weights_merged {
            let weight_a = weights_a.get(key).copied();
            let weight_b = weights_b.get(key).copied();

            let expected = match (weight_a, weight_b) {
                (Some(wa), Some(wb)) => {
                    // Both sources: expect the minimum (tropical plus)
                    wa.min(wb)
                }
                (Some(wa), None) => wa,
                (None, Some(wb)) => wb,
                (None, None) => {
                    // Action not found in either source — this is a P2 issue, skip here
                    continue;
                }
            };

            if (*merged_best_weight - expected).abs() > WEIGHT_TOLERANCE {
                violations.push(PropertyViolation {
                    category: category.clone(),
                    token: Some(key.0.clone()),
                    message: format!(
                        "weight mismatch for action '{}': merged best={}, expected={} \
                         (A={:?}, B={:?})",
                        key.1, merged_best_weight, expected, weight_a, weight_b
                    ),
                    source: "merged".to_string(),
                });
            }
        }
    }

    PropertyResult {
        property: VerificationProperty::WeightConsistency,
        holds: violations.is_empty(),
        violations,
    }
}

/// Collect `(token_name, rule_label) -> weight` for all actions in a WFST.
///
/// For duplicate `(token, label)` pairs (rare but possible with union),
/// keeps the minimum weight, consistent with tropical semantics.
fn collect_token_action_weights(
    wfst: &PredictionWfst,
) -> HashMap<(String, String), f64> {
    let mut weights = HashMap::new();
    for (token_name, _token_id) in wfst.token_map.iter() {
        for action in wfst.predict(token_name) {
            let key = (token_name.to_string(), action.action.rule_label());
            let entry = weights.entry(key).or_insert(f64::INFINITY);
            if action.weight.value() < *entry {
                *entry = action.weight.value();
            }
        }
    }
    weights
}

// ══════════════════════════════════════════════════════════════════════════════
// P4: Dispatch Determinism Preservation
// ══════════════════════════════════════════════════════════════════════════════

/// **P4: DispatchDeterminismPreservation** — Tokens that have exactly one
/// dispatch action in both source WFSTs should remain bounded in the merged
/// WFST.
///
/// This is a soft property: union inherently can increase the number of
/// alternatives for a token (e.g., A has `Plus -> Add` and B has `Plus ->
/// Concat`, so merged has both). The check emits warnings rather than hard
/// failures, because the merged WFST can legitimately have more alternatives
/// than either source.
///
/// Specifically, for each token that is deterministic in at least one source
/// WFST (exactly 1 action), we check whether the merged WFST has more than
/// one action. If so, we record a warning violation.
fn verify_dispatch_determinism(
    wfsts_a: &HashMap<String, PredictionWfst>,
    wfsts_b: &HashMap<String, PredictionWfst>,
    wfsts_merged: &HashMap<String, PredictionWfst>,
) -> PropertyResult {
    let mut violations = Vec::new();

    for (category, merged_wfst) in wfsts_merged {
        let wfst_a = wfsts_a.get(category);
        let wfst_b = wfsts_b.get(category);

        // Collect tokens that are deterministic in A and/or B
        let deterministic_a = wfst_a
            .map(|w| collect_deterministic_tokens(w))
            .unwrap_or_default();
        let deterministic_b = wfst_b
            .map(|w| collect_deterministic_tokens(w))
            .unwrap_or_default();

        // Tokens deterministic in both sources
        let deterministic_both: HashSet<&String> =
            deterministic_a.intersection(&deterministic_b).collect();

        // Check merged WFST: do these tokens remain single-action?
        for token in &deterministic_both {
            let merged_actions = merged_wfst.predict(token);
            if merged_actions.len() > 1 {
                violations.push(PropertyViolation {
                    category: category.clone(),
                    token: Some((*token).clone()),
                    message: format!(
                        "token was deterministic in both A and B but has {} actions in merged",
                        merged_actions.len()
                    ),
                    source: "merged".to_string(),
                });
            }
        }
    }

    // P4 is a soft property — holds is true only if there are no determinism
    // regressions, but violations are warnings, not errors.
    PropertyResult {
        property: VerificationProperty::DispatchDeterminismPreservation,
        holds: violations.is_empty(),
        violations,
    }
}

/// Collect tokens that have exactly one dispatch action in a WFST.
fn collect_deterministic_tokens(wfst: &PredictionWfst) -> HashSet<String> {
    let mut deterministic = HashSet::new();
    for (token_name, _token_id) in wfst.token_map.iter() {
        if wfst.predict(token_name).len() == 1 {
            deterministic.insert(token_name.to_string());
        }
    }
    deterministic
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

    // ── Test helpers ─────────────────────────────────────────────────────────

    /// Build a simple WFST with the given (token, rule_label, weight) triples.
    fn build_wfst(
        category: &str,
        actions: &[(&str, &str, f64)],
    ) -> PredictionWfst {
        let token_names: Vec<String> = actions.iter().map(|(t, _, _)| t.to_string()).collect();
        let token_map = TokenIdMap::from_names(token_names.into_iter());
        let mut builder = PredictionWfstBuilder::new(category, token_map);
        for &(token, label, weight) in actions {
            builder.add_action(
                token,
                DispatchAction::Direct {
                    rule_label: label.to_string(),
                    parse_fn: format!("parse_{}", label.to_lowercase()),
                },
                TropicalWeight::new(weight),
            );
        }
        builder.build()
    }

    /// Build a HashMap of WFSTs from a list of (category, actions) pairs.
    fn build_wfst_map(
        entries: &[(&str, &[(&str, &str, f64)])],
    ) -> HashMap<String, PredictionWfst> {
        entries
            .iter()
            .map(|(cat, actions)| (cat.to_string(), build_wfst(cat, actions)))
            .collect()
    }

    // ── Test 1: All properties pass for disjoint categories ──────────────────

    #[test]
    fn test_all_pass_disjoint_categories() {
        // A has category "Expr", B has category "Stmt" — no overlap
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0), ("Minus", "Sub", 0.0)])]);
        let wfsts_b =
            build_wfst_map(&[("Stmt", &[("If", "IfStmt", 0.0), ("While", "WhileStmt", 0.0)])]);

        // Merged = union of both (disjoint)
        let mut wfsts_merged = wfsts_a.clone();
        for (k, v) in &wfsts_b {
            wfsts_merged.insert(k.clone(), v.clone());
        }

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        assert!(report.all_pass, "Expected all properties to pass for disjoint categories");
        for result in &report.results {
            assert!(
                result.holds,
                "Property {:?} should hold, violations: {:?}",
                result.property, result.violations
            );
        }
    }

    // ── Test 2: All properties pass for shared categories with disjoint rules ─

    #[test]
    fn test_all_pass_shared_categories_disjoint_rules() {
        // Both have "Expr" but with disjoint tokens
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[("Expr", &[("Minus", "Sub", 1.0)])]);

        // Merged via union
        let mut merged_wfst = wfsts_a["Expr"].clone();
        merged_wfst.union(&wfsts_b["Expr"]);
        let wfsts_merged: HashMap<String, PredictionWfst> =
            [("Expr".to_string(), merged_wfst)].into_iter().collect();

        let shared = vec!["Expr".to_string()];
        let report = verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &shared);

        assert!(
            report.all_pass,
            "Expected all properties to pass for shared categories with disjoint rules.\n{}",
            report
        );
    }

    // ── Test 3: P1 fails — action removed from merged ───────────────────────

    #[test]
    fn test_p1_fails_missing_action() {
        let wfsts_a =
            build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0), ("Minus", "Sub", 0.0)])]);
        let wfsts_b = build_wfst_map(&[]);

        // Merged is missing "Sub" action — only has "Plus"
        let wfsts_merged = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let p1 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::LanguageContainment)
            .expect("P1 result should exist");

        assert!(!p1.holds, "P1 should fail when an action is missing from merged");
        assert!(!p1.violations.is_empty(), "P1 should have violations");

        // Check that the violation mentions "Sub"
        let has_sub_violation = p1
            .violations
            .iter()
            .any(|v| v.message.contains("Sub") && v.token.as_deref() == Some("Minus"));
        assert!(
            has_sub_violation,
            "P1 violation should mention action 'Sub' for token 'Minus', got: {:?}",
            p1.violations
        );
    }

    // ── Test 4: P2 fails — phantom action in merged ─────────────────────────

    #[test]
    fn test_p2_fails_spurious_action() {
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[]);

        // Merged has a phantom action "Phantom" not in A or B
        let wfsts_merged =
            build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0), ("Star", "Phantom", 0.5)])]);

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let p2 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::NoSpuriousActions)
            .expect("P2 result should exist");

        assert!(!p2.holds, "P2 should fail when merged has phantom actions");
        assert!(!p2.violations.is_empty(), "P2 should have violations");

        let has_phantom_violation = p2
            .violations
            .iter()
            .any(|v| v.message.contains("Phantom"));
        assert!(
            has_phantom_violation,
            "P2 violation should mention 'Phantom', got: {:?}",
            p2.violations
        );
    }

    // ── Test 5: P3 detects weight mismatch ──────────────────────────────────

    #[test]
    fn test_p3_weight_mismatch() {
        // Both have "Expr" with "Plus" -> "Add", but different weights
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 1.0)])]);
        let wfsts_b = build_wfst_map(&[("Expr", &[("Plus", "Add", 2.0)])]);

        // Build merged with an INCORRECT weight (3.0 instead of min(1.0, 2.0) = 1.0)
        let wfsts_merged = build_wfst_map(&[("Expr", &[("Plus", "Add", 3.0)])]);

        let shared = vec!["Expr".to_string()];
        let report = verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &shared);

        let p3 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::WeightConsistency)
            .expect("P3 result should exist");

        assert!(!p3.holds, "P3 should fail on weight mismatch");
        assert!(!p3.violations.is_empty(), "P3 should have violations");

        let has_weight_violation = p3
            .violations
            .iter()
            .any(|v| v.message.contains("weight mismatch"));
        assert!(
            has_weight_violation,
            "P3 violation should mention weight mismatch, got: {:?}",
            p3.violations
        );
    }

    // ── Test 6: P3 passes with correct weights ──────────────────────────────

    #[test]
    fn test_p3_passes_correct_weights() {
        // Both have "Expr" with "Plus" -> "Add", different weights
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 1.0)])]);
        let wfsts_b = build_wfst_map(&[("Expr", &[("Plus", "Add", 2.0)])]);

        // Correct merged weight: union preserves both, and the weight should
        // be checked per-action. Since union keeps both transitions, the merged
        // WFST will have both weights. We check the A-originating one.
        let mut merged_wfst = wfsts_a["Expr"].clone();
        merged_wfst.union(&wfsts_b["Expr"]);
        let wfsts_merged: HashMap<String, PredictionWfst> =
            [("Expr".to_string(), merged_wfst)].into_iter().collect();

        let shared = vec!["Expr".to_string()];
        let report = verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &shared);

        let p3 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::WeightConsistency)
            .expect("P3 result should exist");

        assert!(
            p3.holds,
            "P3 should pass with correct union weights, violations: {:?}",
            p3.violations
        );
    }

    // ── Test 7: P4 detects determinism regression ───────────────────────────

    #[test]
    fn test_p4_determinism_regression() {
        // Both A and B have "Plus" with exactly one action each, but different rules
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[("Expr", &[("Plus", "Concat", 1.0)])]);

        // Merged via union: "Plus" now has 2 actions
        let mut merged_wfst = wfsts_a["Expr"].clone();
        merged_wfst.union(&wfsts_b["Expr"]);
        let wfsts_merged: HashMap<String, PredictionWfst> =
            [("Expr".to_string(), merged_wfst)].into_iter().collect();

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let p4 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::DispatchDeterminismPreservation)
            .expect("P4 result should exist");

        assert!(
            !p4.holds,
            "P4 should detect determinism regression for 'Plus'"
        );
        assert!(!p4.violations.is_empty(), "P4 should have violations");

        let has_plus_violation = p4
            .violations
            .iter()
            .any(|v| v.token.as_deref() == Some("Plus") && v.message.contains("2 actions"));
        assert!(
            has_plus_violation,
            "P4 should flag 'Plus' as having 2 actions, got: {:?}",
            p4.violations
        );
    }

    // ── Test 8: P4 passes when determinism is preserved ─────────────────────

    #[test]
    fn test_p4_passes_when_preserved() {
        // A has "Plus" -> "Add", B has "Minus" -> "Sub" (disjoint tokens)
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[("Expr", &[("Minus", "Sub", 0.0)])]);

        let mut merged_wfst = wfsts_a["Expr"].clone();
        merged_wfst.union(&wfsts_b["Expr"]);
        let wfsts_merged: HashMap<String, PredictionWfst> =
            [("Expr".to_string(), merged_wfst)].into_iter().collect();

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let p4 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::DispatchDeterminismPreservation)
            .expect("P4 result should exist");

        assert!(
            p4.holds,
            "P4 should pass when tokens are disjoint, violations: {:?}",
            p4.violations
        );
    }

    // ── Test 9: P1 fails when entire category is missing from merged ────────

    #[test]
    fn test_p1_category_missing_from_merged() {
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[]);

        // Merged is empty — missing the "Expr" category entirely
        let wfsts_merged: HashMap<String, PredictionWfst> = HashMap::new();

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let p1 = report
            .results
            .iter()
            .find(|r| r.property == VerificationProperty::LanguageContainment)
            .expect("P1 result should exist");

        assert!(!p1.holds, "P1 should fail when category is missing from merged");
        assert!(
            p1.violations
                .iter()
                .any(|v| v.category == "Expr" && v.message.contains("missing")),
            "P1 violation should mention missing category, got: {:?}",
            p1.violations
        );
    }

    // ── Test 10: Full composition round-trip with all properties ─────────────

    #[test]
    fn test_full_composition_roundtrip() {
        // A: Expr { Plus -> Add(0.0), Integer -> NumLit(0.0) }
        // B: Expr { Minus -> Sub(0.5) }, Stmt { If -> IfStmt(0.0) }
        let wfsts_a =
            build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0), ("Integer", "NumLit", 0.0)])]);
        let wfsts_b = build_wfst_map(&[
            ("Expr", &[("Minus", "Sub", 0.5)]),
            ("Stmt", &[("If", "IfStmt", 0.0)]),
        ]);

        // Merged: Expr = A.Expr union B.Expr, Stmt = B.Stmt
        let mut merged_expr = wfsts_a["Expr"].clone();
        merged_expr.union(&wfsts_b["Expr"]);
        let mut wfsts_merged: HashMap<String, PredictionWfst> = HashMap::new();
        wfsts_merged.insert("Expr".to_string(), merged_expr);
        wfsts_merged.insert("Stmt".to_string(), wfsts_b["Stmt"].clone());

        let shared = vec!["Expr".to_string()];
        let report = verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &shared);

        assert!(
            report.all_pass,
            "Full round-trip should pass all properties.\n{}",
            report
        );
    }

    // ── Test 11: Display formatting ─────────────────────────────────────────

    #[test]
    fn test_report_display() {
        let wfsts_a = build_wfst_map(&[("Expr", &[("Plus", "Add", 0.0)])]);
        let wfsts_b = build_wfst_map(&[]);
        let wfsts_merged: HashMap<String, PredictionWfst> = HashMap::new();

        let report =
            verify_composition(&wfsts_a, &wfsts_b, &wfsts_merged, &[]);

        let display = format!("{}", report);
        assert!(display.contains("Composition Verification Report"));
        assert!(display.contains("FAIL"));
        assert!(display.contains("LanguageContainment"));
    }
}
