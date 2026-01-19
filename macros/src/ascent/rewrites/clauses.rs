//! Rewrite clause generation for Ascent Datalog.
//!
//! Generates base rewrite rules using unified rule generation.

use crate::ascent::rules as unified_rules;
use crate::ast::theory::TheoryDef;
use proc_macro2::TokenStream;

/// Generate Ascent clauses for base rewrite rules.
///
/// Uses unified rule generation for all theories.
pub fn generate_rewrite_clauses(theory: &TheoryDef) -> Vec<TokenStream> {
    unified_rules::generate_rewrite_rules(theory)
}
