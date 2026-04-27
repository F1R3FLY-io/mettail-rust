//! MeTTaIL procedural macro for defining formal languages
//!
//! This crate provides the `language!` macro which defines a formal language with:
//! - AST types (Rust enums)
//! - Parser (PraTTaIL-generated Pratt + Recursive Descent)
//! - Rewrite engine (Ascent-based)
//! - Term generation and manipulation
//! - Metadata for REPL introspection
//! - Language implementation struct

mod gen;
mod logic;

use proc_macro::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use syn::parse_macro_input;

use mettail_ast::compose::ComposeDef;
use mettail_ast::language::LanguageDef;
use mettail_ast::merge::{apply_extends, apply_includes, apply_mixins};
use mettail_ast::validation::validate_language;
use gen::runtime::wpds_codegen::generate_wpds_engine_module;
use gen::{
    generate_all, generate_blockly_definitions, generate_language_impl, generate_metadata,
    write_blockly_blocks, write_blockly_categories,
};
use logic::writer::spill_and_include;
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
    mettail_ast::registry::register_language(&lang_name, &input_for_registry);

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

    // Phase 3F (predicated types): stratification analysis. Walks the
    // language's logic relations and ?guard:Guard predicates to detect
    // negation cycles. Non-stratifiable programs make Ascent's fixpoint
    // semantics undefined, so this is a hard error (STRAT01).
    let strat_report = logic::stratification::analyze(&language_def);
    if strat_report.has_violations() {
        for (_id, msg) in strat_report.diagnostics() {
            abort!(language_def.name.span(), "{}", msg);
        }
    }

    // Stage-instrumentation (gated by `PRATTAIL_MACRO_TRACE=1`): emits a
    // timestamped `[macro-trace] <lang> <stage>` line before each heavy
    // phase so the operator can see exactly which stage exceeds the
    // memory budget when a grammar OOMs. Zero cost when the env var is
    // unset.
    let trace = std::env::var("PRATTAIL_MACRO_TRACE").is_ok();
    macro_rules! stage {
        ($name:literal) => {
            if trace {
                eprintln!("[macro-trace] {} {}", lang_name, $name);
            }
        };
    }

    stage!("generate_all.start");
    // Generate the Rust AST types and operations (also captures WFST pipeline analysis)
    let (ast_code, pipeline_analysis) = generate_all(&language_def);
    stage!("generate_all.done");

    stage!("generate_freshness_functions.start");
    // Generate freshness functions (needed by Ascent rewrite clauses)
    let freshness_fns = generate_freshness_functions(&language_def);
    stage!("generate_freshness_functions.done");

    stage!("generate_ascent_source.start");
    // Generate Ascent datalog source (includes rewrites as Ascent clauses)
    // Thread pipeline analysis for WFST-informed optimizations (DCE, rule ordering, etc.)
    let ascent_output = generate_ascent_source(&language_def, Some(&pipeline_analysis));
    let ascent_code = ascent_output.full_output;
    let raw_ascent_content = ascent_output.raw_content;
    let core_raw_ascent_content = ascent_output.core_raw_content;
    let pre_stratum_content = ascent_output.pre_stratum_content;
    let ground_rewrite_seeds = ascent_output.ground_rewrite_seeds;
    let stratum_contents = ascent_output.stratum_contents;
    stage!("generate_ascent_source.done");

    stage!("generate_metadata.start");
    // Generate metadata for REPL introspection
    let metadata_code = generate_metadata(&language_def);
    stage!("generate_metadata.done");

    stage!("generate_language_impl.start");
    // Generate language implementation struct (Term wrapper + Language struct)
    // Pass raw Ascent content for direct inclusion in ascent! { struct Foo; ... }
    // Also pass core content for SCC-split struct (if available)
    // Also pass pre-stratum content for ground rewrite pre-computation (Sprint 5)
    // Also pass ground rewrite seeds for B-CG04 short-circuit optimization
    let language_code = generate_language_impl(
        &language_def,
        &raw_ascent_content,
        core_raw_ascent_content.as_ref(),
        pre_stratum_content.as_ref(),
        &ground_rewrite_seeds,
        &stratum_contents,
    );
    stage!("generate_language_impl.done");

    // W7 Stage 6: WPDS-runtime engine for the language.
    // Emits a `<Lang>WpdsEngine` struct and `WpdsStepEngine` impl alongside
    // the existing trampoline parser. Coexists harmlessly until Stage 10's
    // hard cutover. See `prattail/docs/design/wpds-migration-survey.md`.
    stage!("generate_wpds_engine_module.start");
    let wpds_engine_code = generate_wpds_engine_module(&language_def);
    stage!("generate_wpds_engine_module.done");

    // Generate test file for cargo test / cargo nextest integration.
    // Gated by `options { emit_tests: true }` (default: true).
    let emit_tests = language_def
        .options
        .get("emit_tests")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    if emit_tests {
        gen::test_gen::write_test_file(&language_def, &pipeline_analysis);
    }

    // Generate per-language simulation CLI binary.
    // Gated by `options { emit_simulator: true }` (default: true).
    gen::test_gen::write_simulation_binary_if_enabled(&language_def);

    // Generate Blockly block definitions.
    // Gated by `options { emit_blockly: true }` (default: true).
    let emit_blockly = language_def
        .options
        .get("emit_blockly")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    if emit_blockly {
        let blockly_output = generate_blockly_definitions(&language_def);
        if let Err(e) = write_blockly_blocks(&language_def.name.to_string(), &blockly_output) {
            eprintln!("Warning: Failed to write Blockly blocks: {}", e);
        }
        if let Err(e) = write_blockly_categories(&language_def.name.to_string(), &blockly_output) {
            eprintln!("Warning: Failed to write Blockly categories: {}", e);
        }
    }

    // Generate public proptest strategies (gated behind `strategies` feature)
    let public_strategies = gen::test_gen::strategies::generate_public_strategies(&language_def);

    // Spill each large emitter to disk and replace with `include!` stubs.
    // Purpose: the proc-macro → rustc bridge ships TokenStreams by value, so a
    // multi-MB returned TokenStream costs 2× that in RSS (proc-macro copy +
    // rustc copy). Writing the content to `target/generated/<lang>/<mod>.rs`
    // and returning `include!("...")` lets rustc load the source directly
    // from disk during expansion, keeping the bridge tiny. It also gives
    // humans readable files to diff and inspect after compilation.
    let ast_include = spill_and_include(&lang_name, "ast", ast_code);
    let freshness_include = spill_and_include(&lang_name, "freshness", freshness_fns);
    let ascent_include = spill_and_include(&lang_name, "ascent", ascent_code);
    let metadata_include = spill_and_include(&lang_name, "metadata", metadata_code);
    let language_include = spill_and_include(&lang_name, "language", language_code);
    let wpds_include = spill_and_include(&lang_name, "wpds", wpds_engine_code);
    let strategies_include = spill_and_include(&lang_name, "strategies", public_strategies);

    let combined = quote::quote! {
        #ast_include
        #freshness_include
        #ascent_include
        #metadata_include
        #language_include
        #wpds_include

        /// Public proptest strategies for generating random well-formed terms.
        ///
        /// Enabled by the `strategies` feature flag. Provides tape-based
        /// iterative term builders and `arb_{cat}(max_depth)` strategy
        /// functions for property-based testing by external crates.
        #[cfg(feature = "strategies")]
        pub mod strategies {
            use super::*;
            use proptest::prelude::*;
            use proptest::strategy::BoxedStrategy;
            #strategies_include
        }
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
    let fragment_def = parse_macro_input!(input as mettail_ast::fragment::FragmentDef);

    // Validate: all category references in terms exist in types
    if let Err(msg) = mettail_ast::fragment::validate_fragment(&fragment_def) {
        abort!(fragment_def.name.span(), "{}", msg);
    }

    let frag_name = fragment_def.name.to_string();
    mettail_ast::registry::register_fragment(&frag_name, &input_for_registry);

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
