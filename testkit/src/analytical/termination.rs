//! Termination analysis integration for generated language tests.
//!
//! Wraps `mettail_prattail::termination::check_termination()` and provides
//! a higher-level interface that works with `LanguageMetadata` rather than
//! raw `RewriteRule` vectors.

use mettail_prattail::confluence::RewriteRule;
use mettail_prattail::termination::{self, TerminationResult as PrattailTerminationResult};
use mettail_runtime::LanguageMetadata;

/// Result of termination checking on a language.
#[derive(Debug)]
pub struct TerminationResult {
    /// Whether the TRS is terminating.
    pub is_terminating: bool,
    /// Whether the result is conclusive.
    pub is_conclusive: bool,
    /// Human-readable summary.
    pub summary: String,
}

/// Check termination of a language's rewrite rules.
///
/// Converts the language's rewrite metadata into `RewriteRule` format
/// understood by the prattail termination checker, then runs the analysis
/// via dependency pair decomposition and SCC analysis.
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite rule definitions
///
/// # Returns
/// A `TerminationResult` summarizing whether the TRS terminates.
pub fn check_language_termination(metadata: &dyn LanguageMetadata) -> TerminationResult {
    let rewrites = metadata.rewrites();

    if rewrites.is_empty() {
        return TerminationResult {
            is_terminating: true,
            is_conclusive: true,
            summary: format!("{}: no rewrite rules, trivially terminating", metadata.name()),
        };
    }

    // Convert metadata rewrites to prattail RewriteRule format.
    // Re-use the same pattern parser from the confluence module.
    let rules: Vec<RewriteRule> = rewrites
        .iter()
        .filter(|rw| rw.is_base()) // Skip congruence rules
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
        return TerminationResult {
            is_terminating: true,
            is_conclusive: true,
            summary: format!(
                "{}: no base rewrite rules (only congruence), trivially terminating",
                metadata.name()
            ),
        };
    }

    let result: PrattailTerminationResult = termination::check_termination(&rules);

    match &result {
        PrattailTerminationResult::Terminating => TerminationResult {
            is_terminating: true,
            is_conclusive: true,
            summary: format!("{}: terminating", metadata.name()),
        },
        PrattailTerminationResult::PotentiallyNonTerminating { reason, .. } => TerminationResult {
            is_terminating: false,
            is_conclusive: true,
            summary: format!("{}: potentially non-terminating -- {}", metadata.name(), reason),
        },
        PrattailTerminationResult::Unknown { reason } => TerminationResult {
            is_terminating: false,
            is_conclusive: false,
            summary: format!("{}: termination unknown -- {}", metadata.name(), reason),
        },
    }
}
