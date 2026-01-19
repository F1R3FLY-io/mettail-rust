//! Code generation for theory definitions
//!
//! This module orchestrates the generation of Rust AST types, Display implementations,
//! substitution logic, term generation, and parser integration.

mod ast_gen;
mod display;
mod subst;
pub mod termgen;

pub mod blockly;
pub mod parser;

pub use ast_gen::*;

use crate::ast::{grammar::{GrammarItem, GrammarRule}};
use syn::Ident;

/// Checks if a rule is a Var rule (single item, NonTerminal "Var")
#[allow(clippy::cmp_owned)]
pub fn is_var_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if ident.to_string() == "Var")
}

/// Checks if a rule is an Integer rule (single item, NonTerminal "Integer")
/// Used for native integer type handling in theory definitions
#[allow(clippy::cmp_owned)]
pub fn is_integer_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if ident.to_string() == "Integer")
}

/// Checks if a rule is an Assign rule (Var "=" Category)
/// Example: `Assign . Int ::= Var "=" Int ;`
#[allow(clippy::cmp_owned)]
pub fn is_assign_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 3
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if ident.to_string() == "Var")
        && matches!(&rule.items[1], GrammarItem::Terminal(term) if term == "=")
        && matches!(&rule.items[2], GrammarItem::NonTerminal(ident) if ident == &rule.category)
}

/// Check if a category has an Assign rule in the theory
pub fn has_assign_rule(category: &Ident, theory: &crate::ast::theory::TheoryDef) -> bool {
    theory
        .terms
        .iter()
        .any(|rule| rule.category == *category && is_assign_rule(rule))
}

/// Generate the Var variant label for a category
///
/// Convention: First letter of category + "Var"
/// Examples: Proc -> PVar, Name -> NVar, Int -> IVar
pub fn generate_var_label(category: &Ident) -> Ident {
    let cat_str = category.to_string();
    let first_letter = cat_str
        .chars()
        .next()
        .unwrap_or('V')
        .to_uppercase()
        .collect::<String>();
    quote::format_ident!("{}Var", first_letter)
}

/// Generate the literal variant label for a category with native type
///
/// Convention: "NumLit" for integers, "FloatLit" for floats, "BoolLit" for bools
/// Used for auto-generated literal constructors
pub fn generate_literal_label(native_type: &syn::Type) -> Ident {
    use crate::utils::native_type_to_string;
    let type_str = native_type_to_string(native_type);
    match type_str.as_str() {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => quote::format_ident!("NumLit"),
        "f32" | "f64" => quote::format_ident!("FloatLit"),
        "bool" => quote::format_ident!("BoolLit"),
        _ => quote::format_ident!("Lit"), // Generic fallback
    }
}
