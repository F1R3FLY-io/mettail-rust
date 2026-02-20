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
//! - `syntax/` - Parsing and printing (Display, PraTTaIL, var inference)
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
pub use syntax::parser::prattail_bridge::generate_prattail_parser;

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
    use term_ops::ground::generate_is_ground_methods;
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
    let is_ground_impl = generate_is_ground_methods(language);
    let var_inference_impl = generate_var_category_inference(language);

    // Parser code: PraTTaIL (inline)
    let parser_code = {
        let prattail_parser = generate_prattail_parser(language);
        let category_parse_impls = generate_prattail_category_parse_impls(language);
        quote! {
            #prattail_parser
            #category_parse_impls
        }
    };

    quote! {
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

        #is_ground_impl

        #var_inference_impl

        #parser_code
    }
}

/// Generate `impl Cat` parse methods for each language type using PraTTaIL's inline
/// parse functions.
///
/// Generated methods:
/// - `parse(input) -> Result<Cat, String>` — convenience wrapper, flattens error to string
/// - `parse_structured(input) -> Result<Cat, ParseError>` — returns structured error
/// - `parse_with_source(input, source) -> Result<Cat, String>` — includes source context in errors
///
/// PraTTaIL generates `parse_Cat(tokens, pos, min_bp)` functions and a `lex()` function
/// directly in the enclosing scope, so no module qualification is needed.
fn generate_prattail_category_parse_impls(language: &LanguageDef) -> TokenStream {
    use quote::{format_ident, quote};

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let parse_fn = format_ident!("parse_{}", cat);
            let parse_fn_recovering = format_ident!("parse_{}_recovering", cat);
            quote! {
                impl #cat {
                    /// Parse a string as this category.
                    ///
                    /// Returns `Err(String)` with a human-readable error message including
                    /// line:column position on parse failure.
                    pub fn parse(input: &str) -> Result<#cat, std::string::String> {
                        Self::parse_structured(input).map_err(|e| e.to_string())
                    }

                    /// Parse a string as this category, returning a structured `ParseError`.
                    ///
                    /// The `ParseError` carries the exact source position (`Range` with
                    /// `Position { byte_offset, line, column }`) and a descriptive message.
                    /// Use this for programmatic error handling (IDE integration, error recovery).
                    ///
                    /// Zero-copy: the lexer produces `Token<'a>` borrowing from `input`,
                    /// so no String allocations occur during lexing.
                    pub fn parse_structured(input: &str) -> Result<#cat, ParseError> {
                        let tokens = lex(input)?;
                        let mut pos = 0usize;
                        let result = #parse_fn(&tokens, &mut pos, 0)?;
                        // Verify all tokens consumed (except EOF)
                        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                            return Err(ParseError::TrailingTokens {
                                found: format!("{:?}", tokens[pos].0),
                                range: tokens[pos].1,
                            });
                        }
                        Ok(result)
                    }

                    /// Parse a string with source-context error messages.
                    ///
                    /// On error, includes a source snippet with caret pointing to the
                    /// error location (rustc-style). The source is used for display only;
                    /// parsing operates on `input`.
                    pub fn parse_with_source(input: &str) -> Result<#cat, std::string::String> {
                        Self::parse_structured(input).map_err(|e| {
                            let range = e.range();
                            format!("{}\n{}", e, format_error_context(input, &range))
                        })
                    }

                    /// Parse with error recovery, collecting multiple errors.
                    ///
                    /// Unlike `parse()` which stops at the first error, this continues
                    /// parsing after errors using panic-mode recovery with FOLLOW-set-based
                    /// synchronization points.
                    ///
                    /// Returns `(Option<ast>, errors)` where:
                    /// - `Some(ast)` with empty errors: successful parse
                    /// - `Some(ast)` with errors: partial result with recovered errors
                    /// - `None` with errors: unrecoverable (e.g., lex error or prefix failure)
                    pub fn parse_recovering(input: &str) -> (Option<#cat>, Vec<ParseError>) {
                        let tokens = match lex(input) {
                            Ok(t) => t,
                            Err(e) => return (None, vec![ParseError::from(e)]),
                        };
                        let mut pos = 0usize;
                        let mut errors = Vec::new();
                        let result = #parse_fn_recovering(&tokens, &mut pos, 0, &mut errors);
                        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                            errors.push(ParseError::TrailingTokens {
                                found: format!("{:?}", tokens[pos].0),
                                range: tokens[pos].1,
                            });
                        }
                        (result, errors)
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
        },
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
