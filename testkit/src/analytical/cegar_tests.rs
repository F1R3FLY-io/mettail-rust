//! CEGAR (Counterexample-Guided Abstraction Refinement) analysis for generated
//! language tests.
//!
//! Wraps `mettail_prattail::cegar` and provides a higher-level interface that
//! works with `LanguageMetadata`. Constructs a simple WPDS model from the
//! language's rewrite rules and verifies reachability properties using the
//! CEGAR refinement loop.
//!
//! The CEGAR loop starts with a coarse Boolean abstraction (can the error state
//! be reached?), and refines through Counting and Tropical abstractions when
//! counterexamples are found to be spurious.

use std::collections::HashMap;

use mettail_prattail::automata::semiring::{Semiring, TropicalWeight};
use mettail_prattail::cegar::{self, AbstractionLevel, CegarConfig, CegarResult};
use mettail_prattail::wpds::{PAutomaton, PAutomatonStateId, StackSymbol, Wpds, WpdsRule};
use mettail_runtime::LanguageMetadata;

/// Result of CEGAR verification on a language.
#[derive(Debug)]
pub struct CegarTestResult {
    /// Whether the verification concluded that the property holds.
    pub is_verified: bool,
    /// Whether a concrete counterexample was found.
    pub has_counterexample: bool,
    /// Whether the result is inconclusive (max refinements reached).
    pub is_inconclusive: bool,
    /// Number of refinement steps taken.
    pub refinement_steps: usize,
    /// The final abstraction level reached.
    pub final_level: String,
    /// Human-readable summary.
    pub summary: String,
}

/// Run CEGAR verification on a language's rewrite system.
///
/// Constructs a WPDS model where each rewrite rule becomes a pushdown rule,
/// and verifies that no "error" (stuck) configuration is reachable. The "error"
/// configuration is defined as a state where a rewrite rule's LHS matches
/// but no RHS can be produced.
///
/// For languages with no rewrite rules, the property trivially holds.
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite rule definitions
///
/// # Returns
/// A `CegarTestResult` summarizing the verification outcome.
pub fn check_cegar_properties(metadata: &dyn LanguageMetadata) -> CegarTestResult {
    let rewrites = metadata.rewrites();
    let base_rewrites: Vec<_> = rewrites.iter().filter(|rw| rw.is_base()).collect();

    if base_rewrites.is_empty() {
        return CegarTestResult {
            is_verified: true,
            has_counterexample: false,
            is_inconclusive: false,
            refinement_steps: 0,
            final_level: "N/A".to_string(),
            summary: format!(
                "{}: no base rewrite rules, CEGAR verification trivially verified",
                metadata.name()
            ),
        };
    }

    // Build stack symbols: one entry symbol + per-rule LHS/RHS symbols + error symbol.
    let entry_sym = StackSymbol::category_entry("Main");
    let error_sym = StackSymbol::category_entry("ErrorState");

    let mut all_symbols = vec![entry_sym.clone(), error_sym.clone()];
    let mut rules: Vec<WpdsRule<TropicalWeight>> = Vec::new();

    for (i, rw) in base_rewrites.iter().enumerate() {
        let rule_name = rw.name.unwrap_or("anon");
        let lhs_sym = StackSymbol::rule_position("Main", &format!("{}_lhs", rule_name), i as u32);
        let rhs_sym = StackSymbol::rule_position("Main", &format!("{}_rhs", rule_name), i as u32);

        all_symbols.push(lhs_sym.clone());
        all_symbols.push(rhs_sym.clone());

        // Entry -> LHS: dispatch to the rewrite rule.
        rules.push(WpdsRule::Replace {
            from_gamma: entry_sym.clone(),
            to_gamma: lhs_sym.clone(),
            weight: TropicalWeight::new(1.0),
        });

        // LHS -> RHS: apply the rewrite.
        rules.push(WpdsRule::Replace {
            from_gamma: lhs_sym,
            to_gamma: rhs_sym.clone(),
            weight: TropicalWeight::new(1.0),
        });

        // RHS -> pop: rewrite completes successfully.
        rules.push(WpdsRule::Pop {
            from_gamma: rhs_sym,
            weight: TropicalWeight::one(),
        });
    }

    // Build symbol index.
    let symbol_index: HashMap<StackSymbol, usize> = all_symbols
        .iter()
        .enumerate()
        .map(|(i, s)| (s.clone(), i))
        .collect();

    // Build rules-by-source index.
    let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
    for (i, rule) in rules.iter().enumerate() {
        rules_by_source
            .entry(rule.from_gamma().clone())
            .or_default()
            .push(i);
    }

    let wpds = Wpds {
        stack_symbols: all_symbols,
        symbol_index,
        rules,
        rules_by_source,
        initial_symbol: entry_sym,
        grammar_name: format!("{}_cegar", metadata.name()),
    };

    // Build bad-state automaton: accepts only ErrorState symbol.
    let initial_state: PAutomatonStateId = 0;
    let mut bad_auto = PAutomaton::new(initial_state);
    let final_state = bad_auto.add_state();
    bad_auto.mark_final(final_state);
    bad_auto.add_transition(initial_state, error_sym.clone(), final_state, TropicalWeight::one());
    bad_auto.symbol_to_state.insert(error_sym, final_state);

    // Configure CEGAR with reasonable limits.
    let config = CegarConfig {
        max_refinements: 5,
        initial_level: AbstractionLevel::Boolean,
    };

    // Run the CEGAR verification loop.
    let result = cegar::cegar_verify(&wpds, &bad_auto, &config);

    match &result {
        CegarResult::Verified { level, log } => CegarTestResult {
            is_verified: true,
            has_counterexample: false,
            is_inconclusive: false,
            refinement_steps: log.num_steps(),
            final_level: format!("{}", level),
            summary: format!(
                "{}: CEGAR verified at {} ({} steps)",
                metadata.name(),
                level,
                log.num_steps()
            ),
        },
        CegarResult::Refuted { trace, log } => CegarTestResult {
            is_verified: false,
            has_counterexample: true,
            is_inconclusive: false,
            refinement_steps: log.num_steps(),
            final_level: log
                .steps
                .last()
                .map(|s| format!("{}", s.level))
                .unwrap_or_else(|| "unknown".to_string()),
            summary: format!(
                "{}: CEGAR refuted with counterexample {} ({} steps)",
                metadata.name(),
                trace,
                log.num_steps()
            ),
        },
        CegarResult::Inconclusive(log) => CegarTestResult {
            is_verified: false,
            has_counterexample: false,
            is_inconclusive: true,
            refinement_steps: log.num_steps(),
            final_level: log
                .steps
                .last()
                .map(|s| format!("{}", s.level))
                .unwrap_or_else(|| "unknown".to_string()),
            summary: format!(
                "{}: CEGAR inconclusive after {} steps",
                metadata.name(),
                log.num_steps()
            ),
        },
    }
}
