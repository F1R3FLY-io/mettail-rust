//! Rewrite clause generation for Ascent Datalog.
//!
//! Generates base rewrite rules using unified rule generation.

use crate::logic::rules as unified_rules;
use crate::ast::language::LanguageDef;
use proc_macro2::TokenStream;

/// Generate Ascent clauses for base rewrite rules.
///
/// Uses unified rule generation for all languages.
pub fn generate_rewrite_clauses(language: &LanguageDef) -> Vec<TokenStream> {
    unified_rules::generate_rewrite_rules(language)
}
