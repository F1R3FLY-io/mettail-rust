//! MeTTaIL procedural macro for defining formal languages
//!
//! This crate provides the `language!` macro which defines a formal language with:
//! - AST types (Rust enums)
//! - Parser (PraTTaIL-generated Pratt + Recursive Descent)
//! - Rewrite engine (Ascent-based)
//! - Term generation and manipulation
//! - Metadata for REPL introspection
//! - Language implementation struct

mod ast;
mod gen;
mod logic;

use proc_macro::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use syn::parse_macro_input;

use ast::language::LanguageDef;
use ast::validation::validate_language;
use gen::{
    generate_all, generate_blockly_definitions, generate_language_impl,
    generate_metadata, write_blockly_blocks, write_blockly_categories,
};
use logic::{generate_ascent_source, rules::generate_freshness_functions};

#[proc_macro]
#[proc_macro_error]
pub fn language(input: TokenStream) -> TokenStream {
    let language_def = parse_macro_input!(input as LanguageDef);

    if let Err(e) = validate_language(&language_def) {
        let span = e.span();
        let msg = e.message();
        abort!(span, "{}", msg);
    }

    // Generate the Rust AST types and operations
    let ast_code = generate_all(&language_def);

    // Generate freshness functions (needed by Ascent rewrite clauses)
    let freshness_fns = generate_freshness_functions(&language_def);

    // Generate Ascent datalog source (includes rewrites as Ascent clauses)
    let ascent_output = generate_ascent_source(&language_def);
    let ascent_code = ascent_output.full_output;
    let raw_ascent_content = ascent_output.raw_content;
    let core_raw_ascent_content = ascent_output.core_raw_content;

    // Generate metadata for REPL introspection
    let metadata_code = generate_metadata(&language_def);

    // Generate language implementation struct (Term wrapper + Language struct)
    // Pass raw Ascent content for direct inclusion in ascent! { struct Foo; ... }
    // Also pass core content for SCC-split struct (if available)
    let language_code = generate_language_impl(
        &language_def,
        &raw_ascent_content,
        core_raw_ascent_content.as_ref(),
    );

    // Generate Blockly block definitions
    let blockly_output = generate_blockly_definitions(&language_def);
    if let Err(e) = write_blockly_blocks(&language_def.name.to_string(), &blockly_output) {
        eprintln!("Warning: Failed to write Blockly blocks: {}", e);
    }
    if let Err(e) = write_blockly_categories(&language_def.name.to_string(), &blockly_output) {
        eprintln!("Warning: Failed to write Blockly categories: {}", e);
    }

    let combined = quote::quote! {
        #ast_code
        #freshness_fns
        #ascent_code
        #metadata_code
        #language_code
    };

    TokenStream::from(combined)
}
