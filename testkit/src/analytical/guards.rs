//! Guard decidability analysis for generated language tests.
//!
//! Wraps `mettail_prattail::symbolic::classify_decidability` and
//! `mettail_prattail::predicate_dispatch` to classify language guards
//! by decidability tier and check satisfiability.
//!
//! Guards in MeTTaIL languages control dispatch: which rewrite rule or
//! parsing path to take based on runtime conditions. This module analyzes
//! whether those guards are decidable at compile time, at runtime, semi-
//! decidable, or undecidable, and provides a summary classification.

use mettail_prattail::symbolic::{classify_decidability, DecidabilityTier, PredicateExpr};
use mettail_runtime::LanguageMetadata;

/// Result of guard decidability analysis on a language.
#[derive(Debug)]
pub struct GuardResult {
    /// Total number of guards analyzed.
    pub total_guards: usize,
    /// Number of guards that are compile-time decidable (T1).
    pub compile_time_decidable: usize,
    /// Number of guards that are runtime decidable (T2).
    pub runtime_decidable: usize,
    /// Number of guards that are semi-decidable (T3).
    pub semi_decidable: usize,
    /// Number of guards that are undecidable (T4).
    pub undecidable: usize,
    /// The highest (worst) decidability tier found among all guards.
    pub worst_tier: String,
    /// Human-readable summary.
    pub summary: String,
}

/// Check guard decidability for a language.
///
/// Constructs predicate expressions from the language's rewrite rules and
/// term constructors, classifies each by decidability tier using the symbolic
/// automata module, and summarizes the results.
///
/// Guards are derived from:
/// - Rewrite rule conditions (freshness conditions)
/// - Rewrite rule premises (congruence guards)
/// - Term constructor field types (type guards)
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite and term definitions
///
/// # Returns
/// A `GuardResult` summarizing the decidability classification.
pub fn check_guard_decidability(metadata: &dyn LanguageMetadata) -> GuardResult {
    let rewrites = metadata.rewrites();
    let terms = metadata.terms();

    let mut guards: Vec<PredicateExpr> = Vec::new();

    // Extract guards from rewrite rule conditions.
    // Each freshness condition "x # P" becomes an atomic predicate.
    for rw in rewrites {
        for &condition in rw.conditions {
            guards.push(PredicateExpr::Atom(condition.to_string()));
        }

        // Congruence rules have premises that serve as guards.
        if let Some((premise_lhs, premise_rhs)) = rw.premise {
            // The premise "(S, T)" means "if S rewrites to T".
            // Model this as a conjunction of two atoms.
            let premise_guard = PredicateExpr::And(
                Box::new(PredicateExpr::Atom(premise_lhs.to_string())),
                Box::new(PredicateExpr::Atom(premise_rhs.to_string())),
            );
            guards.push(premise_guard);
        }
    }

    // Extract type guards from term constructors.
    // A constructor with typed fields implicitly guards on the types.
    for term_def in terms {
        if term_def.fields.len() >= 2 {
            // Construct a conjunction of type assertions for all fields.
            let field_atoms: Vec<PredicateExpr> = term_def
                .fields
                .iter()
                .map(|f| PredicateExpr::Atom(format!("{}:{}", f.name, f.ty)))
                .collect();

            // Build the conjunction tree.
            if let Some(guard) = conjunction_tree(field_atoms) {
                guards.push(guard);
            }
        }

        // Binder fields have a freshness guard.
        for field in term_def.fields {
            if field.is_binder {
                guards.push(PredicateExpr::Atom(format!("binder({})", field.name)));
            }
        }
    }

    if guards.is_empty() {
        return GuardResult {
            total_guards: 0,
            compile_time_decidable: 0,
            runtime_decidable: 0,
            semi_decidable: 0,
            undecidable: 0,
            worst_tier: "N/A".to_string(),
            summary: format!(
                "{}: no guards found, decidability analysis trivially empty",
                metadata.name()
            ),
        };
    }

    // Classify each guard by decidability tier.
    let mut compile_time = 0;
    let mut runtime = 0;
    let mut semi = 0;
    let mut undecidable = 0;
    let mut worst = DecidabilityTier::CompileTimeDecidable;

    for guard in &guards {
        let tier = classify_decidability(guard);
        match tier {
            DecidabilityTier::CompileTimeDecidable => compile_time += 1,
            DecidabilityTier::RuntimeDecidable => {
                runtime += 1;
                if matches!(worst, DecidabilityTier::CompileTimeDecidable) {
                    worst = DecidabilityTier::RuntimeDecidable;
                }
            },
            DecidabilityTier::SemiDecidable => {
                semi += 1;
                if matches!(
                    worst,
                    DecidabilityTier::CompileTimeDecidable | DecidabilityTier::RuntimeDecidable
                ) {
                    worst = DecidabilityTier::SemiDecidable;
                }
            },
            DecidabilityTier::Undecidable => {
                undecidable += 1;
                worst = DecidabilityTier::Undecidable;
            },
        }
    }

    let worst_str = format!("{}", worst);

    GuardResult {
        total_guards: guards.len(),
        compile_time_decidable: compile_time,
        runtime_decidable: runtime,
        semi_decidable: semi,
        undecidable,
        worst_tier: worst_str.clone(),
        summary: format!(
            "{}: guard decidability (total: {}, T1: {}, T2: {}, T3: {}, T4: {}, worst: {})",
            metadata.name(),
            guards.len(),
            compile_time,
            runtime,
            semi,
            undecidable,
            worst_str,
        ),
    }
}

/// Build a balanced conjunction tree from a list of predicate expressions.
///
/// Returns `None` if the list is empty.
fn conjunction_tree(mut exprs: Vec<PredicateExpr>) -> Option<PredicateExpr> {
    if exprs.is_empty() {
        return None;
    }
    if exprs.len() == 1 {
        return Some(exprs.remove(0));
    }

    // Build a balanced binary tree of conjunctions.
    while exprs.len() > 1 {
        let mut next = Vec::with_capacity((exprs.len() + 1) / 2);
        let mut i = 0;
        while i + 1 < exprs.len() {
            let left = exprs[i].clone();
            let right = exprs[i + 1].clone();
            next.push(PredicateExpr::And(Box::new(left), Box::new(right)));
            i += 2;
        }
        if i < exprs.len() {
            next.push(exprs[i].clone());
        }
        exprs = next;
    }

    Some(exprs.remove(0))
}
