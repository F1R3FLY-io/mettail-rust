//! E-graph joinability analysis integration for generated language tests.
//!
//! Wraps `mettail_prattail::egraph::analyze_trs()` and provides a
//! higher-level interface that works with `LanguageMetadata`.
//!
//! The e-graph equality saturation engine discovers term equivalences that
//! normalization-based confluence checking alone cannot find, providing
//! enhanced joinability results for critical pairs.

use mettail_prattail::confluence::{self, RewriteRule};
use mettail_prattail::egraph::{self, EGraphConfig, EGraphTrsAnalysis};
use mettail_runtime::LanguageMetadata;

/// Result of e-graph joinability analysis on a language.
#[derive(Debug)]
pub struct EGraphResult {
    /// Number of critical pairs that were newly joined by e-graph saturation
    /// (i.e., pairs that normalization could not join but the e-graph did).
    pub newly_joinable_count: usize,
    /// Number of rules whose RHS was simplified by e-graph analysis.
    pub simplified_rule_count: usize,
    /// Number of non-obvious equivalences discovered between distinct terms.
    pub discovered_equivalence_count: usize,
    /// Whether e-graph saturation converged (reached fixpoint).
    pub converged: bool,
    /// Total saturation iterations performed.
    pub iterations: usize,
    /// Human-readable summary.
    pub summary: String,
}

/// Check e-graph joinability of a language's rewrite rules.
///
/// Converts the language's rewrite metadata into `RewriteRule` format,
/// runs confluence analysis to find critical pairs, then applies e-graph
/// equality saturation to discover additional joinability and simplifications.
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite rule definitions
///
/// # Returns
/// An `EGraphResult` summarizing enhanced joinability findings.
pub fn check_egraph_joinability(metadata: &dyn LanguageMetadata) -> EGraphResult {
    let rewrites = metadata.rewrites();

    if rewrites.is_empty() {
        return EGraphResult {
            newly_joinable_count: 0,
            simplified_rule_count: 0,
            discovered_equivalence_count: 0,
            converged: true,
            iterations: 0,
            summary: format!("{}: no rewrite rules, e-graph analysis trivial", metadata.name()),
        };
    }

    // Convert metadata rewrites to prattail RewriteRule format.
    let rules: Vec<RewriteRule> = rewrites
        .iter()
        .filter(|rw| rw.is_base())
        .filter_map(|rw| {
            let lhs = super::confluence::parse_pattern_to_term_pub(rw.lhs)?;
            let rhs = super::confluence::parse_pattern_to_term_pub(rw.rhs)?;
            if let Some(name) = rw.name {
                Some(RewriteRule::labeled(name, lhs, rhs))
            } else {
                Some(RewriteRule::new(lhs, rhs))
            }
        })
        .collect();

    if rules.is_empty() {
        return EGraphResult {
            newly_joinable_count: 0,
            simplified_rule_count: 0,
            discovered_equivalence_count: 0,
            converged: true,
            iterations: 0,
            summary: format!(
                "{}: no parseable base rewrite rules, e-graph analysis skipped",
                metadata.name()
            ),
        };
    }

    // First run confluence analysis to get critical pairs.
    let confluence_analysis = confluence::check_confluence(&rules, 100);

    // Configure e-graph with reasonable limits for language-level analysis.
    let config = EGraphConfig { max_nodes: 5_000, max_iterations: 20 };

    // Run e-graph TRS analysis.
    let egraph_analysis: EGraphTrsAnalysis =
        egraph::analyze_trs(&rules, &confluence_analysis, &config);

    let converged = egraph_analysis.saturation_result.converged;
    let iterations = egraph_analysis.saturation_result.iterations;

    EGraphResult {
        newly_joinable_count: egraph_analysis.newly_joinable.len(),
        simplified_rule_count: egraph_analysis.simplified_rules.len(),
        discovered_equivalence_count: egraph_analysis.discovered_equivalences.len(),
        converged,
        iterations,
        summary: format!(
            "{}: e-graph analysis (newly joinable: {}, simplified: {}, equivalences: {}, \
             converged: {}, iterations: {})",
            metadata.name(),
            egraph_analysis.newly_joinable.len(),
            egraph_analysis.simplified_rules.len(),
            egraph_analysis.discovered_equivalences.len(),
            converged,
            iterations,
        ),
    }
}
