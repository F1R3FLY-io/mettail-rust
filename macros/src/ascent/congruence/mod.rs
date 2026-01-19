//! Congruence rule generation for Ascent
//!
//! This module handles EXPLICIT rewrite congruence rules declared in theories.
//! Users control where rewrites propagate by writing rules like:
//!   `if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})`
//!
//! Note: Equality congruences (`eq(x,y) => eq(f(x),f(y))`) are auto-generated
//! in equations.rs since they're always sound for all constructors.

use crate::ast::pattern::Pattern;
use crate::ast::theory::TheoryDef;
use proc_macro2::TokenStream;

pub mod unified;

// Re-export the main entry point
pub use unified::generate_explicit_congruence;

/// Check if a pattern contains collection syntax
pub fn contains_collection_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Collection { .. } => true,
        Pattern::Term(pt) => contains_collection_in_pattern_term(pt),
        Pattern::Map { collection, body, .. } => {
            contains_collection_pattern(collection) || contains_collection_pattern(body)
        }
        Pattern::Zip { collections } => collections.iter().any(contains_collection_pattern),
    }
}

fn contains_collection_in_pattern_term(pt: &crate::ast::pattern::PatternTerm) -> bool {
    use crate::ast::pattern::PatternTerm;
    match pt {
        PatternTerm::Var(_) => false,
        PatternTerm::Apply { args, .. } => args.iter().any(contains_collection_pattern),
        PatternTerm::Lambda { body, .. } => contains_collection_pattern(body),
        PatternTerm::MultiLambda { body, .. } => contains_collection_pattern(body),
        PatternTerm::Subst { term, replacement, .. } => {
            contains_collection_pattern(term) || contains_collection_pattern(replacement)
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            contains_collection_pattern(scope) || replacements.iter().any(contains_collection_pattern)
        }
    }
}

/// Generate all explicit congruence rules for a theory
///
/// Processes `if S => T then LHS => RHS` rules and generates appropriate
/// Ascent clauses based on where the rewrite variable appears.
pub fn generate_all_explicit_congruences(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    
    for rewrite in &theory.rewrites {
        // Only process rules with congruence premise
        if rewrite.premise.is_some() {
            if let Some(rule) = generate_explicit_congruence(rewrite, theory) {
                rules.push(rule);
            }
        }
    }
    
    rules
}
