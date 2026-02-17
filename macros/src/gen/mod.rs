//! Code generation for language definitions
//!
//! This module orchestrates the generation of all Rust code from a `LanguageDef`:
//! - AST types (enums with variants)
//! - Syntax operations (Display, parser support)
//! - Term operations (substitution, normalization)
//! - Native type support (eval)
//! - Runtime integration (Language trait, metadata, environments)
//!
//! ## Module Structure
//!
//! - `types/` - AST enum generation
//! - `syntax/` - Parsing and printing (Display, LALRPOP, var inference)
//! - `term_ops/` - Term manipulation (substitution, normalization)
//! - `native/` - Native type support (eval)
//! - `runtime/` - Runtime integration (Language trait, metadata, environments)
//! - `term_gen/` - Test utilities (exhaustive/random term generation)
//! - `blockly/` - Visual block generation

#![allow(clippy::cmp_owned, clippy::single_match)]

pub mod blockly;
pub mod native;
pub mod runtime;
pub mod syntax;
pub mod term_gen;
pub mod term_ops;
pub mod types;

use crate::ast::grammar::{GrammarItem, GrammarRule};
use crate::ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

// Re-export main entry points
pub use blockly::{generate_blockly_definitions, write_blockly_blocks, write_blockly_categories};
pub use runtime::language::generate_language_impl;
pub use runtime::metadata::generate_metadata;
pub use syntax::parser::{generate_lalrpop_grammar, write_grammar_file};

/// Generate all AST-related code for a language definition
///
/// This is the main entry point for code generation. It produces:
/// - Enum definitions for all language types
/// - Display implementations
/// - Substitution methods
/// - Environment types
/// - Term generation utilities
/// - Native type evaluation
/// - Variable inference for parsing
pub fn generate_all(language: &LanguageDef) -> TokenStream {
    use native::eval::generate_eval_method;
    use runtime::environment::generate_environments;
    use syntax::display::generate_display;
    use syntax::var_inference::generate_var_category_inference;
    use term_gen::{generate_random_generation, generate_term_generation};
    use term_ops::normalize::{generate_flatten_helpers, generate_normalize_functions};
    use term_ops::subst::{generate_env_substitution, generate_substitution};
    use types::enums::generate_ast_enums;

    let ast_enums = generate_ast_enums(language);
    let flatten_helpers = generate_flatten_helpers(language);
    let normalize_impl = generate_normalize_functions(language);
    let subst_impl = generate_substitution(language);
    let env_types = generate_environments(language);
    let env_subst_impl = generate_env_substitution(language);
    let display_impl = generate_display(language);
    let generation_impl = generate_term_generation(language);
    let random_gen_impl = generate_random_generation(language);
    let eval_impl = generate_eval_method(language);
    let var_inference_impl = generate_var_category_inference(language);

    // Generate LALRPOP module reference and per-category parse impls (parse must come after parser module)
    let language_name = &language.name;
    let language_name_lower = language_name.to_string().to_lowercase();
    let language_mod = syn::Ident::new(&language_name_lower, proc_macro2::Span::call_site());
    let category_parse_impls = generate_category_parse_impls(language, &language_name_lower);

    quote! {
        use lalrpop_util::lalrpop_mod;

        #ast_enums

        #flatten_helpers

        #normalize_impl

        #subst_impl

        #env_types

        #env_subst_impl

        #display_impl

        #generation_impl

        #random_gen_impl

        #eval_impl

        #var_inference_impl

        #[cfg(not(test))]
        #[allow(unused_imports)]
        lalrpop_util::lalrpop_mod!(pub #language_mod);

        #[cfg(test)]
        #[allow(unused_imports)]
        lalrpop_util::lalrpop_mod!(#language_mod);

        #category_parse_impls
    }
}

/// Generate `impl Cat { pub fn parse(input: &str) -> Result<Cat, String> { ... } }` for each
/// language type so that logic-block rules can seed relations by parsing strings (e.g.
/// `proc(p) <-- let Ok(p) = Proc::parse("^x.{*(x)}");`).
fn generate_category_parse_impls(language: &LanguageDef, parser_mod: &str) -> TokenStream {
    use quote::{format_ident, quote};

    let parser_mod_ident = syn::Ident::new(parser_mod, proc_macro2::Span::call_site());

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let parser_name = format_ident!("{}Parser", cat);
            quote! {
                impl #cat {
                    /// Parse a string as this category. For use in logic-block seeding, e.g.
                    /// `proc(p) <-- let Ok(p) = Proc::parse("...");`
                    pub fn parse(input: &str) -> Result<#cat, std::string::String> {
                        #parser_mod_ident::#parser_name::new()
                            .parse(input)
                            .map_err(|e| format!("{:?}", e))
                    }
                }
            }
        })
        .collect();

    quote! { #(#impls)* }
}

// =============================================================================
// Helper functions used across generation modules
// =============================================================================

/// Checks if a rule is a Var rule (single item, NonTerminal "Var")
#[allow(clippy::cmp_owned)]
pub fn is_var_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if ident.to_string() == "Var")
}

/// Names of nonterminals that represent native literal tokens in the generated grammar.
const LITERAL_NONTERMINALS: &[&str] = &["Integer", "Boolean", "StringLiteral", "FloatLiteral"];

/// Returns true if the given nonterminal name is a known literal type (Integer, Boolean, StringLiteral, FloatLiteral).
pub fn is_literal_nonterminal(name: &str) -> bool {
    LITERAL_NONTERMINALS.contains(&name)
}

/// Checks if a rule is a literal rule (single item, NonTerminal one of Integer/Boolean/StringLiteral/FloatLiteral).
/// Used for native type handling in theory definitions; all native literal types are treated uniformly.
#[allow(clippy::cmp_owned)]
pub fn is_literal_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if is_literal_nonterminal(&ident.to_string()))
}

/// Returns the nonterminal name when the rule is a literal rule (Integer, Boolean, StringLiteral, FloatLiteral).
/// Used for payload-type selection (clone vs copy) and for signed-numeric logic (unary minus).
#[allow(clippy::cmp_owned)]
pub fn literal_rule_nonterminal(rule: &GrammarRule) -> Option<String> {
    match rule.items.first()? {
        GrammarItem::NonTerminal(ident) => {
            let name = ident.to_string();
            if is_literal_nonterminal(&name) {
                Some(name)
            } else {
                None
            }
        }
        _ => None,
    }
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
    use native::native_type_to_string;
    let type_str = native_type_to_string(native_type);
    match type_str.as_str() {
        "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => quote::format_ident!("NumLit"),
        "f32" | "f64" => quote::format_ident!("FloatLit"),
        "bool" => quote::format_ident!("BoolLit"),
        "str" | "String" => quote::format_ident!("StringLit"),
        _ => quote::format_ident!("Lit"), // Generic fallback
    }
}
