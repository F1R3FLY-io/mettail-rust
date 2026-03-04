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

use ast::compose::ComposeDef;
use ast::language::LanguageDef;
use ast::merge::{apply_extends, apply_includes, apply_mixins};
use ast::validation::validate_language;
use gen::{
    generate_all, generate_blockly_definitions, generate_language_impl, generate_metadata,
    write_blockly_blocks, write_blockly_categories,
};
use logic::{generate_ascent_source, rules::generate_freshness_functions};

#[proc_macro]
#[proc_macro_error]
pub fn language(input: TokenStream) -> TokenStream {
    // Clone input BEFORE parse_macro_input! consumes it.
    // The clone is safe within the same invocation's bridge session.
    let input_for_registry: proc_macro2::TokenStream = input.clone().into();
    let mut language_def = parse_macro_input!(input as LanguageDef);
    let lang_name = language_def.name.to_string();

    // Store binary-encoded input tokens in registry (no bridge types retained).
    // MUST happen before any processing so consuming grammars get the full
    // unprocessed rule set.
    ast::registry::register_language(&lang_name, &input_for_registry);

    // Apply composition clauses in order:
    // 1. extends — full inheritance (Error on duplicate labels)
    // 2. includes — grammar-only import (Override: local rules win)
    // 3. mixins — fragment import (Override: local rules win)
    if let Err(msg) = apply_extends(&mut language_def) {
        abort!(language_def.name.span(), "extends error:\n{}", msg);
    }

    if let Err(msg) = apply_includes(&mut language_def) {
        abort!(language_def.name.span(), "includes error:\n{}", msg);
    }

    if let Err(msg) = apply_mixins(&mut language_def) {
        abort!(language_def.name.span(), "mixins error:\n{}", msg);
    }

    if let Err(e) = validate_language(&language_def) {
        let span = e.span();
        let msg = e.message();
        abort!(span, "{}", msg);
    }

    // Generate the Rust AST types and operations (also captures WFST pipeline analysis)
    let (ast_code, pipeline_analysis) = generate_all(&language_def);

    // Generate freshness functions (needed by Ascent rewrite clauses)
    let freshness_fns = generate_freshness_functions(&language_def);

    // Generate Ascent datalog source (includes rewrites as Ascent clauses)
    // Thread pipeline analysis for WFST-informed optimizations (DCE, rule ordering, etc.)
    let ascent_output = generate_ascent_source(&language_def, Some(&pipeline_analysis));
    let ascent_code = ascent_output.full_output;
    let raw_ascent_content = ascent_output.raw_content;
    let core_raw_ascent_content = ascent_output.core_raw_content;
    let pre_stratum_content = ascent_output.pre_stratum_content;

    // Generate metadata for REPL introspection
    let metadata_code = generate_metadata(&language_def);

    // Generate language implementation struct (Term wrapper + Language struct)
    // Pass raw Ascent content for direct inclusion in ascent! { struct Foo; ... }
    // Also pass core content for SCC-split struct (if available)
    // Also pass pre-stratum content for ground rewrite pre-computation (Sprint 5)
    let language_code = generate_language_impl(
        &language_def,
        &raw_ascent_content,
        core_raw_ascent_content.as_ref(),
        pre_stratum_content.as_ref(),
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

/// Define a reusable grammar fragment (types + terms only, no equations/rewrites/logic).
///
/// Fragments are stored in the in-process registry and can be mixed into
/// `language!` definitions via `mixins: [FragmentName]`.
///
/// ```ignore
/// language_fragment! {
///     name: ArithOps,
///     types { ![i32] as Int },
///     terms {
///         NumLit . |- Integer : Int;
///         Add . a:Int, b:Int |- a "+" b : Int ![ a + b ] fold;
///     }
/// }
/// ```
#[proc_macro]
#[proc_macro_error]
pub fn language_fragment(input: TokenStream) -> TokenStream {
    // Clone input BEFORE parse_macro_input! consumes it.
    let input_for_registry: proc_macro2::TokenStream = input.clone().into();
    let fragment_def = parse_macro_input!(input as ast::fragment::FragmentDef);

    // Validate: all category references in terms exist in types
    if let Err(msg) = ast::fragment::validate_fragment(&fragment_def) {
        abort!(fragment_def.name.span(), "{}", msg);
    }

    let frag_name = fragment_def.name.to_string();
    ast::registry::register_fragment(&frag_name, &input_for_registry);

    // Fragments generate NO code — the consuming language! generates everything
    TokenStream::new()
}

/// Compose independently defined languages into a single unified language.
///
/// The composed language delegates all operations (parsing, ascent, env, etc.)
/// to the constituent sub-languages. Parsing tries each sub-language in
/// declaration order and returns the first success.
///
/// ```ignore
/// compose_languages! {
///     name: Combined,
///     languages: [calculator::Calculator, rhocalc::RhoCalc],
/// }
/// ```
///
/// This generates:
/// - `CombinedTermInner` enum with one variant per sub-language
/// - `CombinedTerm` wrapper implementing `mettail_runtime::Term`
/// - `CombinedEnv` struct with per-sub-language environments
/// - `CombinedMetadata` aggregating sub-language metadata
/// - `CombinedLanguage` struct implementing `mettail_runtime::Language`
#[proc_macro]
#[proc_macro_error]
pub fn compose_languages(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as ComposeDef);
    let code = gen::compose_gen::generate_composed_language(&def);
    TokenStream::from(code)
}
