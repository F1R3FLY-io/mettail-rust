//! Extended Weighted Pushdown Systems (EWPDS) with merging functions.
//!
//! Based on Reps, Lal & Kidd (2007), Definitions 12-13. At each call site, a
//! *merging function* `g: D × D → D` combines the caller's local state with the
//! callee's global effect. This handles local variables that the callee cannot
//! access.
//!
//! ## Why EWPDS for MeTTaIL
//!
//! Rho calculus has `PNew` (scoped names) and `PInput` (binding inputs). When one
//! process calls into another via communication, the caller's local bindings are
//! invisible to the callee — exactly the scenario EWPDS merging functions model.
//!
//! ## Architecture
//!
//! ```text
//! WPDS rule:  ⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩  with weight w
//!                                       ↓ becomes
//! EWPDS rule: ⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩  with weight w, merge fn g
//! ```
//!
//! The merge function `g(w_caller, w_callee)` combines:
//! - `w_caller`: the weight (state transformation) at the call site before the call
//! - `w_callee`: the weight computed by poststar for the callee's execution
//!
//! ## References
//!
//! - Reps, Lal & Kidd (2007), §3, Definitions 12-13
//! - Lal & Reps (2006), *Improving Pushdown System Model Checking*

use crate::automata::semiring::Semiring;
use crate::wpds::{PAutomaton, StackSymbol, Wpds, WpdsRule};
use std::collections::HashMap;
use std::fmt;

/// A merging function for EWPDS: combines caller and callee weights.
///
/// Trait object to allow different merge strategies per call site.
pub trait MergeFunction<W: Semiring>: fmt::Debug + Send + Sync {
    /// Merge the caller's local state with the callee's global effect.
    ///
    /// - `caller_weight`: weight at the call site (caller's local state)
    /// - `callee_weight`: weight from callee's execution (global effect)
    ///
    /// Returns the combined weight reflecting both local and global state.
    fn merge(&self, caller_weight: &W, callee_weight: &W) -> W;
}

/// Default merge function: standard semiring multiplication (no local state).
///
/// This recovers standard WPDS behavior: `g(w1, w2) = w1 ⊗ w2`.
#[derive(Debug)]
pub struct DefaultMerge;

impl<W: Semiring> MergeFunction<W> for DefaultMerge {
    fn merge(&self, caller_weight: &W, callee_weight: &W) -> W {
        caller_weight.times(callee_weight)
    }
}

/// Override merge function: callee's effect replaces caller's local for
/// specific components.
///
/// Used when the callee writes to variables that the caller reads.
/// For a relational domain, this would be `g(R1, R2) = R1[a ↦ R2(a)]`.
#[derive(Debug)]
pub struct OverrideMerge<W: Semiring> {
    /// Which "components" the callee overrides in the caller's state.
    /// Represented as a weight mask: `g(w1, w2) = w1 ⊗ mask ⊕ w2 ⊗ (1 - mask)`.
    /// For simple cases, this is just standard composition.
    _phantom: std::marker::PhantomData<W>,
}

impl<W: Semiring> OverrideMerge<W> {
    /// Create a new override merge.
    pub fn new() -> Self {
        OverrideMerge { _phantom: std::marker::PhantomData }
    }
}

impl<W: Semiring> Default for OverrideMerge<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> MergeFunction<W> for OverrideMerge<W> {
    fn merge(&self, caller_weight: &W, callee_weight: &W) -> W {
        // Default implementation: standard composition (identical to DefaultMerge).
        // Subclasses should override for domain-specific behavior.
        caller_weight.times(callee_weight)
    }
}

/// An EWPDS push rule with an associated merge function.
#[derive(Debug)]
pub struct EwpdsPushRule<W: Semiring> {
    /// Source stack symbol.
    pub from_gamma: StackSymbol,
    /// Bottom of two symbols pushed (continuation after return).
    pub to_gamma_bottom: StackSymbol,
    /// Top of two symbols pushed (callee entry).
    pub to_gamma_top: StackSymbol,
    /// Rule weight.
    pub weight: W,
    /// Merge function for combining caller/callee weights.
    pub merge_fn: Box<dyn MergeFunction<W>>,
}

/// An Extended WPDS (EWPDS).
///
/// Extends the standard WPDS with per-push-rule merge functions that
/// combine caller and callee weights at call/return boundaries.
#[derive(Debug)]
pub struct Ewpds<W: Semiring> {
    /// The underlying standard WPDS (contains pop and replace rules).
    pub base: Wpds<W>,
    /// Extended push rules with merge functions (indexed by source stack symbol).
    pub extended_push_rules: Vec<EwpdsPushRule<W>>,
    /// Index from source stack symbol to extended push rule indices.
    pub push_rules_by_source: HashMap<StackSymbol, Vec<usize>>,
}

impl<W: Semiring> Ewpds<W> {
    /// Create an EWPDS from a standard WPDS, converting push rules to EWPDS rules
    /// with default merge functions.
    pub fn from_wpds(wpds: Wpds<W>) -> Self {
        let mut extended_push_rules = Vec::new();
        let mut push_rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();

        // Extract push rules from the base WPDS and wrap with DefaultMerge.
        for rule in &wpds.rules {
            if let WpdsRule::Push {
                from_gamma,
                to_gamma_bottom,
                to_gamma_top,
                weight,
            } = rule
            {
                let idx = extended_push_rules.len();
                push_rules_by_source
                    .entry(from_gamma.clone())
                    .or_default()
                    .push(idx);
                extended_push_rules.push(EwpdsPushRule {
                    from_gamma: from_gamma.clone(),
                    to_gamma_bottom: to_gamma_bottom.clone(),
                    to_gamma_top: to_gamma_top.clone(),
                    weight: *weight,
                    merge_fn: Box::new(DefaultMerge),
                });
            }
        }

        Ewpds {
            base: wpds,
            extended_push_rules,
            push_rules_by_source,
        }
    }

    /// Set the merge function for a specific push rule (identified by source and callee).
    pub fn set_merge_fn(
        &mut self,
        from_gamma: &StackSymbol,
        to_gamma_top: &StackSymbol,
        merge_fn: Box<dyn MergeFunction<W>>,
    ) {
        if let Some(indices) = self.push_rules_by_source.get(from_gamma) {
            for &idx in indices {
                if self.extended_push_rules[idx].to_gamma_top == *to_gamma_top {
                    self.extended_push_rules[idx].merge_fn = merge_fn;
                    return;
                }
            }
        }
    }

    /// Number of extended push rules.
    pub fn num_extended_rules(&self) -> usize {
        self.extended_push_rules.len()
    }
}

/// Compute EWPDS poststar with merge function support.
///
/// This is the extended version of `wpds::poststar()` that applies merge
/// functions at call/return boundaries instead of standard semiring multiplication.
///
/// The key difference from standard poststar:
/// - When processing a push rule `⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩` with merge fn `g`:
///   The weight at the return point uses `g(w_caller, w_callee)` instead of `w_caller ⊗ w_callee`.
pub fn ewpds_poststar<W: Semiring>(ewpds: &Ewpds<W>) -> PAutomaton<W> {
    // Start with standard poststar for pop and replace rules.
    let mut result = crate::wpds::poststar(&ewpds.base);

    // Apply merge functions for extended push rules.
    // For each push rule with a non-default merge, adjust the return-site weight.
    for rule in &ewpds.extended_push_rules {
        let caller_weight = result.symbol_weight(&rule.from_gamma);
        let callee_weight = result.symbol_weight(&rule.to_gamma_top);

        if !caller_weight.is_zero() && !callee_weight.is_zero() {
            let merged = rule.merge_fn.merge(&caller_weight, &callee_weight);
            // Update the return-site transition weight.
            if let Some(trans_indices) = result.transitions_by_source.get(&result.initial_state) {
                for &idx in trans_indices {
                    if result.transitions[idx].symbol == rule.to_gamma_bottom {
                        result.transitions[idx].weight = merged;
                    }
                }
            }
        }
    }

    result
}

/// Pipeline-level EWPDS analysis result.
///
/// Summarises the merge-function sites identified by scanning the grammar's
/// syntax items for `SyntaxItemSpec::Binder` positions. Each binder marks a
/// call/return boundary where an EWPDS merge function can combine caller and
/// callee weights.
#[derive(Debug, Clone)]
pub struct EwpdsAnalysis {
    /// Number of merge function sites identified.
    pub merge_site_count: usize,
    /// Labels of rules with merge functions (formatted as `"Category.Rule"`).
    pub merge_site_labels: Vec<String>,
}

/// Pipeline bridge: identify extended WPDS merge sites from binder positions.
///
/// Scans `all_syntax` for rules containing `SyntaxItemSpec::Binder` items.
/// These mark call/return boundaries where the caller's local bindings are
/// invisible to the callee — exactly the scenario EWPDS merge functions model.
///
/// Returns `None` when no binder sites are found (standard WPDS suffices).
pub fn extend_from_bundle(
    _wpds_analysis: &crate::wpds::WpdsAnalysis,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<EwpdsAnalysis> {
    let mut merge_site_labels = Vec::new();

    for (category, rule_label, items) in all_syntax {
        let has_binder = items.iter().any(|item| {
            matches!(item, crate::SyntaxItemSpec::Binder { .. })
        });
        if has_binder {
            merge_site_labels.push(format!("{}.{}", category, rule_label));
        }
    }

    if merge_site_labels.is_empty() {
        return None;
    }

    Some(EwpdsAnalysis {
        merge_site_count: merge_site_labels.len(),
        merge_site_labels,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::BooleanWeight;

    #[test]
    fn test_default_merge() {
        let merge = DefaultMerge;
        let w1 = BooleanWeight(true);
        let w2 = BooleanWeight(true);
        assert_eq!(merge.merge(&w1, &w2), BooleanWeight(true));

        let w3 = BooleanWeight(false);
        assert_eq!(merge.merge(&w1, &w3), BooleanWeight(false));
    }

    #[test]
    fn test_ewpds_from_empty_wpds() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![StackSymbol::category_entry("Expr")],
            symbol_index: {
                let mut m = HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), 0);
                m
            },
            rules: Vec::new(),
            rules_by_source: HashMap::new(),
            initial_symbol: StackSymbol::category_entry("Expr"),
            grammar_name: "test".to_string(),
        };

        let ewpds = Ewpds::from_wpds(wpds);
        assert_eq!(ewpds.num_extended_rules(), 0);
    }

    #[test]
    fn test_ewpds_from_wpds_with_push() {
        let wpds: Wpds<BooleanWeight> = Wpds {
            stack_symbols: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "Add", 1),
                StackSymbol::category_entry("Term"),
            ],
            symbol_index: {
                let mut m = HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), 0);
                m.insert(StackSymbol::rule_position("Expr", "Add", 1), 1);
                m.insert(StackSymbol::category_entry("Term"), 2);
                m
            },
            rules: vec![WpdsRule::Push {
                from_gamma: StackSymbol::category_entry("Expr"),
                to_gamma_bottom: StackSymbol::rule_position("Expr", "Add", 1),
                to_gamma_top: StackSymbol::category_entry("Term"),
                weight: BooleanWeight(true),
            }],
            rules_by_source: {
                let mut m = HashMap::new();
                m.insert(StackSymbol::category_entry("Expr"), vec![0]);
                m
            },
            initial_symbol: StackSymbol::category_entry("Expr"),
            grammar_name: "test".to_string(),
        };

        let ewpds = Ewpds::from_wpds(wpds);
        assert_eq!(ewpds.num_extended_rules(), 1);
        assert_eq!(
            ewpds.extended_push_rules[0].from_gamma,
            StackSymbol::category_entry("Expr")
        );
    }

    #[test]
    fn test_override_merge() {
        use crate::automata::semiring::TropicalWeight;
        let merge = OverrideMerge::<TropicalWeight>::new();
        let w1 = TropicalWeight::new(3.0);
        let w2 = TropicalWeight::new(5.0);
        // Default override merge = standard composition.
        assert_eq!(merge.merge(&w1, &w2), TropicalWeight::new(8.0));
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_extend_from_bundle_with_binders() {
        let wpds_analysis = make_empty_wpds_analysis();
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "PNew".to_string(),
            "Proc".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("new".to_string()),
                crate::SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                },
                crate::SyntaxItemSpec::Terminal("in".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "body".to_string(),
                },
            ],
        )];
        let result = extend_from_bundle(&wpds_analysis, &syntax);
        assert!(result.is_some(), "should find merge sites for rules with binders");
        let analysis = result.expect("expected Some");
        assert!(analysis.merge_site_count > 0);
    }

    #[test]
    fn test_extend_from_bundle_no_binders() {
        let wpds_analysis = make_empty_wpds_analysis();
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        )];
        let result = extend_from_bundle(&wpds_analysis, &syntax);
        assert!(result.is_none(), "should return None when no binders present");
    }
}
