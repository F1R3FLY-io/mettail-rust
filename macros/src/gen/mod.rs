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
pub mod compose_gen;
pub mod native;
pub mod runtime;
pub mod syntax;
pub mod term_gen;
pub mod term_ops;
pub mod test_gen;
pub mod types;

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

// Re-export main entry points
pub use blockly::{generate_blockly_definitions, write_blockly_blocks, write_blockly_categories};
pub use runtime::language::generate_language_impl;
pub use runtime::metadata::generate_metadata;
pub use syntax::parser::prattail_bridge::generate_prattail_parser_with_analysis;

/// Generate all AST-related code for a language definition.
///
/// This is the main entry point for code generation. It produces:
/// - Enum definitions for all language types
/// - Display implementations
/// - Substitution methods
/// - Environment types
/// - Term generation utilities
/// - Native type evaluation
/// - Variable inference for parsing
///
/// Returns `(code, PipelineAnalysis)` where the analysis captures WFST-derived
/// data from the PraTTaIL pipeline for downstream Ascent codegen optimization.
pub fn generate_all(language: &LanguageDef) -> (TokenStream, mettail_prattail::PipelineAnalysis) {
    use crate::logic::writer::spill_and_include;
    use native::eval::generate_eval_method;
    use runtime::environment::generate_environments;
    use syntax::debug::generate_debug;
    use syntax::display::generate_display;
    use syntax::var_inference::generate_var_category_inference;
    use term_gen::{generate_random_generation, generate_term_generation};
    use term_ops::depth::generate_term_depth_methods;
    use term_ops::ground::generate_is_ground_methods;
    use term_ops::iterative_cmp::generate_iterative_cmp;
    use term_ops::iterative_drop::generate_iterative_drop;
    use term_ops::iterative_hash::generate_iterative_hash;
    use term_ops::match_pattern::generate_match_pattern;
    use term_ops::normalize::{generate_flatten_helpers, generate_normalize_functions};
    use term_ops::parse_alt_filter::generate_parse_alt_filter_methods;
    use term_ops::semantic_hash::generate_semantic_hash;
    use term_ops::subst::{generate_env_substitution, generate_substitution};
    use types::enums::generate_ast_enums;

    let lang_name = language.name.to_string();

    // Detect cancellation pairs for normalize arm generation
    let (cancellation_pairs, _cancellation_equations) =
        mettail_ast::pattern::detect_cancellation_pairs(language);

    // Spill each emitter's output to its own file in `target/generated/<lang>/`
    // and replace it with an `include!` wrapper. Each emitter's TokenStream is dropped
    // as soon as it is serialized — reducing the peak TokenStream memory held
    // simultaneously inside this proc-macro from "sum of all emitters" to
    // "largest single emitter". The on-disk per-concern files are also
    // human-reviewable, which supports the debugging workflow.
    //
    // Emitters are named after their semantic concern (lowercase_snake_case).
    // The corresponding files land at:
    //   <ws>/target/generated/<lang>/<name>.rs
    let ast_enums = spill_and_include(&lang_name, "ast_enums", generate_ast_enums(language));
    let debug_impl = spill_and_include(&lang_name, "debug", generate_debug(language));
    let flatten_helpers =
        spill_and_include(&lang_name, "flatten", generate_flatten_helpers(language));
    let normalize_impl = spill_and_include(
        &lang_name,
        "normalize",
        generate_normalize_functions(language, &cancellation_pairs),
    );
    let subst_impl = spill_and_include(&lang_name, "subst", generate_substitution(language));
    let env_types = spill_and_include(&lang_name, "env_types", generate_environments(language));
    let env_subst_impl =
        spill_and_include(&lang_name, "env_subst", generate_env_substitution(language));
    let display_impl = spill_and_include(&lang_name, "display", generate_display(language));
    let generation_impl =
        spill_and_include(&lang_name, "term_generation", generate_term_generation(language));
    let random_gen_impl =
        spill_and_include(&lang_name, "random_generation", generate_random_generation(language));
    let eval_impl = spill_and_include(&lang_name, "eval", generate_eval_method(language));
    let is_ground_impl =
        spill_and_include(&lang_name, "is_ground", generate_is_ground_methods(language));
    let parse_alt_filter_impl = spill_and_include(
        &lang_name,
        "parse_alt_filter",
        generate_parse_alt_filter_methods(language),
    );
    let term_depth_impl =
        spill_and_include(&lang_name, "term_depth", generate_term_depth_methods(language));
    let match_pattern_impl =
        spill_and_include(&lang_name, "match_pattern", generate_match_pattern(language));
    let iterative_cmp_impl =
        spill_and_include(&lang_name, "iterative_cmp", generate_iterative_cmp(language));
    let iterative_drop_impl =
        spill_and_include(&lang_name, "iterative_drop", generate_iterative_drop(language));
    let iterative_hash_impl =
        spill_and_include(&lang_name, "iterative_hash", generate_iterative_hash(language));
    let semantic_hash_impl =
        spill_and_include(&lang_name, "semantic_hash", generate_semantic_hash(language));
    let guard_codegen_impl = spill_and_include(
        &lang_name,
        "guard_codegen",
        runtime::guard_codegen::generate_guard_codegen(language),
    );
    let var_inference_impl =
        spill_and_include(&lang_name, "var_inference", generate_var_category_inference(language));

    // Parser code: PraTTaIL (inline) — also captures pipeline analysis.
    // The parser output is large (DFA tables, parse fns per category); spill it.
    let (parser_code, pipeline_analysis) = {
        let (prattail_parser, analysis) = generate_prattail_parser_with_analysis(language);
        let category_parse_impls = generate_prattail_category_parse_impls(language);
        let combined = quote! {
            #prattail_parser
            #category_parse_impls
        };
        (spill_and_include(&lang_name, "parser", combined), analysis)
    };

    let code = quote! {
        #ast_enums

        #debug_impl

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

        #parse_alt_filter_impl

        #term_depth_impl

        #match_pattern_impl

        #iterative_cmp_impl

        #iterative_drop_impl

        #iterative_hash_impl

        #semantic_hash_impl

        #guard_codegen_impl

        #var_inference_impl

        #parser_code
    };

    (code, pipeline_analysis)
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

    // Determine which categories have a WPDS facade emitted
    // (`parse_<Cat>_via_wpda`). Mirrors
    // `wpda_codegen::collect_category_names_with_literals`: any category
    // appearing in `language.types` is parseable via WPDS — `synthetic.rs`
    // fabricates rules for the cases not covered by user grammar:
    //  - native_type-only → synthetic atomic-literal rule
    //  - collection_kind → synthetic ListLit / BagLit / MapLit rule
    //  - reference-only (e.g. Ambient's `Name`) → synthetic Var rule
    //
    // The only `parse_structured` body that uses `compile_error!` is the
    // truly-impossible case: a category not in `language.types` at all
    // (which can't happen because we iterate `language.types` to build
    // the impl).
    let wpda_categories: std::collections::BTreeSet<String> =
        language.types.iter().map(|t| t.name.to_string()).collect();

    // `wpda_categories` is the entire `language.types` set — every type
    // gets a WPDS facade emitted by `wpda_codegen` (synthetic.rs ensures
    // even reference-only categories like Ambient's `Name` get a Var rule).
    // Asserting here keeps the macro/wpda_codegen invariant explicit.
    debug_assert_eq!(
        wpda_categories.len(),
        language.types.len(),
        "wpda_categories must mirror language.types — check wpda_codegen::collect_category_names_with_literals",
    );

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string();
            debug_assert!(
                wpda_categories.contains(&cat_str),
                "category `{}` missing from wpda_categories",
                cat_str,
            );
            let parse_fn = format_ident!("parse_{}", cat);
            let _parse_fn_recovering = format_ident!("parse_{}_recovering", cat);

            let running_weight_fn = format_ident!("running_weight_{}", cat);
            let _ = running_weight_fn;
            let with_weight_fn = format_ident!("parse_{}_via_wpda_with_weight", cat);
            let wfst_methods = quote! {
                /// Parse with weight emission: calls `lex_weighted()` to get
                /// per-token tropical weights, then parses normally via the WPDS
                /// facade.
                ///
                /// Returns `(result, weights)` where `weights[i]` is the tropical
                /// weight (lower = higher priority) for `tokens[i]`.
                ///
                /// Stage 7 (2026-04-27): the trampoline-side parser was removed;
                /// the WPDS path captures lex weights via the per-grammar lex
                /// strategy table. The exposed `weights` array is the per-token
                /// lex weight (separate from the parser's lex-min disambiguation
                /// weight, which is internal to the WPDS engine).
                pub fn parse_structured_weighted(input: &str) -> Result<(#cat, Vec<f64>), ParseError> {
                    let weighted_tokens = lex_weighted(input)?;
                    let weights: Vec<f64> = weighted_tokens.iter().map(|(_, _, w)| *w).collect();
                    let result = Self::parse_structured(input)?;
                    Ok((result, weights))
                }

                /// L8 (2026-04-28): Parse with confidence scoring.
                ///
                /// Returns `(ast, confidence)` where `confidence ∈ (0, 1]` is
                /// derived from the WPDS walker's terminal weight via
                /// `exp(-weight.primary)`. A perfect parse (zero accumulated
                /// cost) yields `1.0`; higher path costs (e.g., from lex-min
                /// disambiguation across alternatives) yield smaller values.
                ///
                /// The walker's lex-min cost combines:
                /// - `primary`: tropical sum of per-step weights along the path
                /// - `lex_alt_idx`: lex-time disambiguation tiebreak (L1)
                /// - `src_idx`, `rule_idx`: parser-side tiebreaks
                ///
                /// Confidence here reflects the `primary` axis — the dominant
                /// quality signal. Tiebreaks are diagnostic, not quantitative.
                pub fn parse_with_confidence(input: &str) -> Result<(#cat, f64), ParseError> {
                    let tokens = lex(input)?;
                    let kinds: Vec<mettail_prattail::automata::TokenKind> =
                        tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                    let texts: Vec<&str> = tokens
                        .iter()
                        .map(|(t, r)| token_text(t, input, *r))
                        .collect();
                    let with_weight = #with_weight_fn;
                    let mut pos = 0usize;
                    match with_weight(&kinds, &texts, &mut pos, 0) {
                        Ok((result, dw)) => {
                            // Phase 3.1.7 (C10, 2026-05-15): `dw` is plain
                            // `LexicographicWeight` again after the M11.6b
                            // D5 revert. Direct field access.
                            let cost = dw.primary.0;
                            // exp(-cost) ∈ (0, 1]; clamp for NaN/Inf.
                            let confidence = (-cost).exp();
                            let confidence = if confidence.is_finite() && confidence > 0.0 {
                                confidence.min(1.0)
                            } else {
                                0.0
                            };
                            Ok((result, confidence))
                        }
                        Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Owned(message),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                            range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                            hint: None,
                        }),
                        Err(WpdaParseError::Incomplete { position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::AmbiguityBudget {
                                budget, actual, range,
                                hint: Some(Cow::Borrowed(
                                    "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                )),
                            })
                        }
                    }
                }
            };

            let parse_via_wpda_fn = format_ident!("parse_{}_via_wpda", cat);
            let parse_via_wpda_recovering_fn = format_ident!("parse_{}_via_wpda_recovering", cat);
            let parse_via_wpda_with_source_fn = format_ident!("parse_{}_via_wpda_with_source", cat);
            let parse_via_wpda_all_fn = format_ident!("parse_{}_via_wpda_all", cat);
            let parse_via_wpda_all_with_source_fn =
                format_ident!("parse_{}_via_wpda_all_with_source", cat);
            let parse_via_wpda_method = quote! {
                /// WPDS-driven parser entry point.
                ///
                /// Uses a `LatticeTokenSource` when `lex_dag(input)` reports
                /// lexical ambiguity, so the WPDS backend can rule alternatives
                /// out by parser evidence. Non-ambiguous input keeps the
                /// existing token-slice path.
                pub fn parse_via_wpda(input: &str) -> Result<#cat, ParseError> {
                    mettail_prattail::hang_dump::install_hang_dump_handler();
                    let dag = lex_dag(input).map_err(|msg| ParseError::UnexpectedEof {
                        expected: Cow::Owned(msg),
                        range: Range::from_byte_offsets(input, input.len(), input.len()),
                        hint: None,
                    })?;
                    if dag.has_ambiguity() {
                        let source = mettail_prattail::wpda_runtime::LatticeTokenSource::new(dag);
                        use mettail_prattail::wpda_runtime::WpdaTokenSource as _;
                        let input_end_range =
                            Range::from_byte_offsets(input, input.len(), input.len());
                        let dag_range = |position: usize| -> Range {
                            if let Some(node) = source.dag.nodes.get(position) {
                                let end_byte = node
                                    .edges
                                    .first()
                                    .map(|edge| edge.end_byte)
                                    .unwrap_or(node.byte_start);
                                return Range::from_byte_offsets(input, node.byte_start, end_byte);
                            }
                            input_end_range
                        };
                        let dag_found = |position: usize| -> String {
                            source
                                .peek_kind(position)
                                .map(|kind| format!("{:?}", kind))
                                .unwrap_or_else(|| "end of input".to_string())
                        };
                        let mut pos = 0usize;
                        return match #parse_via_wpda_with_source_fn(&source, &mut pos, 0) {
                            Ok((v, _weight)) => {
                                let eof_node = source.eof_node();
                                if pos < eof_node {
                                    return Err(ParseError::TrailingTokens {
                                        found: dag_found(pos),
                                        range: dag_range(pos),
                                        hint: Some(Cow::Borrowed(
                                            "the WPDS parser finished but input remains; check for missing operators or extra tokens",
                                        )),
                                    });
                                }
                                Ok(v)
                            }
                            Err(WpdaParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                                expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                                range: input_end_range,
                                hint: None,
                            }),
                            Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                                Err(ParseError::UnexpectedToken {
                                    expected: Cow::Owned(message),
                                    found: dag_found(position),
                                    range: dag_range(position),
                                    hint: None,
                                })
                            }
                            Err(WpdaParseError::Incomplete { position }) => {
                                Err(ParseError::UnexpectedToken {
                                    expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                    found: dag_found(position),
                                    range: dag_range(position),
                                    hint: None,
                                })
                            }
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                                Err(ParseError::AmbiguityBudget {
                                    budget, actual, range: dag_range(position),
                                    hint: Some(Cow::Borrowed(
                                        "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                    )),
                                })
                            }
                        };
                    }
                    let tokens = lex(input)?;
                    let kinds: Vec<mettail_prattail::automata::TokenKind> =
                        tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                    let texts: Vec<&str> = tokens
                        .iter()
                        .map(|(t, r)| token_text(t, input, *r))
                        .collect();
                    let mut pos = 0usize;
                    match #parse_via_wpda_fn(&kinds, &texts, &mut pos, 0) {
                        Ok(v) => {
                            if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                                return Err(ParseError::TrailingTokens {
                                    found: format_token_friendly(&tokens[pos].0),
                                    range: tokens[pos].1,
                                    hint: Some(Cow::Borrowed(
                                        "the WPDS parser finished but input remains; check for missing operators or extra tokens",
                                    )),
                                });
                            }
                            Ok(v)
                        }
                        Err(WpdaParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                            range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                            hint: None,
                        }),
                        Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Owned(message),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::Incomplete { position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::AmbiguityBudget {
                                budget, actual, range,
                                hint: Some(Cow::Borrowed(
                                    "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                )),
                            })
                        }
                    }
                }

                /// M8 (2026-05-14): multi-result WPDS-driven parser entry.
                ///
                /// Returns ALL accepted terms produced by the walker's
                /// `WpdaResolveResult::Accepted` vec, in lex-min order
                /// (per the underlying `LexicographicWeight` ordering). Use
                /// this when downstream disambiguation needs every alt
                /// (e.g. `parse_preserving_vars` flattening into
                /// `Ambiguous`, or `run_ascent_typed` iterating alts).
                ///
                /// M6c.4 (2026-05-14): when `lex_dag(input).has_ambiguity()`
                /// is true (multi-kind or multi-length lex alts at any
                /// byte position), routes through `LatticeTokenSource`
                /// so the walker's lex-Fork surfaces all alternatives.
                /// Otherwise uses the slice path — byte-identical to
                /// `parse_via_wpda`. The `_all_with_source` facade
                /// variant accepts either source.
                pub fn parse_via_wpda_all_with_weights(
                    input: &str,
                ) -> Result<
                    (
                        Vec<#cat>,
                        Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                    ),
                    ParseError,
                > {
                    mettail_prattail::hang_dump::install_hang_dump_handler();
                    // M6c.4 + M6c.7.2 (2026-05-14): route through
                    // LatticeTokenSource when dag.has_ambiguity().
                    // Post-M6c.7.1 (lex_dag soft-fail), `lex_dag(input)?`
                    // only errors on TRUE primary-chain dead-ends —
                    // same conditions where `lex` also errors. So `?`
                    // is safe; we no longer need the `.ok()` band-aid.
                    let dag = lex_dag(input).map_err(|msg| ParseError::UnexpectedEof {
                        expected: Cow::Owned(msg),
                        range: Range::from_byte_offsets(input, input.len(), input.len()),
                        hint: None,
                    })?;
                    if dag.has_ambiguity() {
                        let source = mettail_prattail::wpda_runtime::LatticeTokenSource::new(dag);
                        use mettail_prattail::wpda_runtime::WpdaTokenSource as _;
                        let input_end_range =
                            Range::from_byte_offsets(input, input.len(), input.len());
                        let dag_range = |position: usize| -> Range {
                            if let Some(node) = source.dag.nodes.get(position) {
                                let end_byte = node
                                    .edges
                                    .first()
                                    .map(|edge| edge.end_byte)
                                    .unwrap_or(node.byte_start);
                                return Range::from_byte_offsets(input, node.byte_start, end_byte);
                            }
                            input_end_range
                        };
                        let dag_found = |position: usize| -> String {
                            source
                                .peek_kind(position)
                                .map(|kind| format!("{:?}", kind))
                                .unwrap_or_else(|| "end of input".to_string())
                        };
                        let mut pos = 0usize;
                        return match #parse_via_wpda_all_with_source_fn(&source, &mut pos, 0) {
                            Ok((terms, weights)) => {
                                // M6c.8.3 (2026-05-14): use the source's
                                // `eof_node()` instead of
                                // `dag.nodes.len() - 1`. M6c.7.1
                                // soft-fail may allocate orphan nodes
                                // for secondary-alt dead-ends at
                                // indices AFTER the EOF sentinel, so
                                // `len() - 1` would point to an orphan
                                // and the walker's correct EOF-Accept
                                // (at the real EOF sentinel index)
                                // would be misreported as
                                // `TrailingTokens`.
                                let eof_node = source.eof_node();
                                if pos < eof_node {
                                    return Err(ParseError::TrailingTokens {
                                        found: dag_found(pos),
                                        range: dag_range(pos),
                                        hint: Some(Cow::Borrowed(
                                            "the WPDS parser finished but input remains; check for missing operators or extra tokens",
                                        )),
                                    });
                                }
                                if terms.is_empty() {
                                    return Err(ParseError::UnexpectedEof {
                                        expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                                        range: input_end_range,
                                        hint: None,
                                    });
                                }
                                Ok((terms, weights))
                            }
                            Err(WpdaParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                                expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                                range: input_end_range,
                                hint: None,
                            }),
                            Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                                Err(ParseError::UnexpectedToken {
                                    expected: Cow::Owned(message),
                                    found: dag_found(position),
                                    range: dag_range(position),
                                    hint: None,
                                })
                            }
                            Err(WpdaParseError::Incomplete { position }) => {
                                Err(ParseError::UnexpectedToken {
                                    expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                    found: dag_found(position),
                                    range: dag_range(position),
                                    hint: None,
                                })
                            }
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                                Err(ParseError::AmbiguityBudget {
                                    budget, actual, range: dag_range(position),
                                    hint: Some(Cow::Borrowed(
                                        "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                    )),
                                })
                            }
                        };
                    }
                    let tokens = lex(input)?;
                    // Slice path: no DAG ambiguity, byte-identical to
                    // pre-M6c.4 behavior.
                    let kinds: Vec<mettail_prattail::automata::TokenKind> =
                        tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                    let texts: Vec<&str> = tokens
                        .iter()
                        .map(|(t, r)| token_text(t, input, *r))
                        .collect();
                    let mut pos = 0usize;
                    match #parse_via_wpda_all_fn(&kinds, &texts, &mut pos, 0) {
                        Ok((terms, weights)) => {
                            if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                                return Err(ParseError::TrailingTokens {
                                    found: format_token_friendly(&tokens[pos].0),
                                    range: tokens[pos].1,
                                    hint: Some(Cow::Borrowed(
                                        "the WPDS parser finished but input remains; check for missing operators or extra tokens",
                                    )),
                                });
                            }
                            if terms.is_empty() {
                                return Err(ParseError::UnexpectedEof {
                                    expected: Cow::Borrowed(
                                        "a complete parse — WPDS produced no result",
                                    ),
                                    range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                                    hint: None,
                                });
                            }
                            Ok((terms, weights))
                        }
                        Err(WpdaParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                            range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                            hint: None,
                        }),
                        Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Owned(message),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::Incomplete { position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::UnexpectedToken {
                                expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                found: tokens
                                    .get(position)
                                    .map(|(t, _)| format_token_friendly(t))
                                    .unwrap_or_else(|| "end of input".to_string()),
                                range,
                                hint: None,
                            })
                        }
                        Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                            let range = tokens
                                .get(position)
                                .map(|(_, r)| *r)
                                .unwrap_or_else(|| {
                                    tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero())
                                });
                            Err(ParseError::AmbiguityBudget {
                                budget, actual, range,
                                hint: Some(Cow::Borrowed(
                                    "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                )),
                            })
                        }
                    }
                }

                /// M8 compatibility wrapper that returns only terms.
                ///
                /// Use `parse_via_wpda_all_with_weights` when downstream
                /// evaluation needs WPDA parse/evidence weights for lazy
                /// priority traversal.
                pub fn parse_via_wpda_all(input: &str) -> Result<Vec<#cat>, ParseError> {
                    Self::parse_via_wpda_all_with_weights(input)
                        .map(|(terms, _weights)| terms)
                }
            };
            let _ = parse_fn;
            // `Cat::parse_structured` shares the explicit WPDS string entry
            // point so lexical-DAG ambiguity handling cannot diverge between
            // `parse()`, `parse_structured()`, and `parse_via_wpda()`.
            let parse_structured_body = quote! {
                Self::parse_via_wpda(input)
            };
            quote! {
                impl #cat {
                    /// Parse a string as this category.
                    ///
                    /// Returns `Err(String)` with a human-readable error message including
                    /// line:column position on parse failure.
                    pub fn parse(input: &str) -> Result<#cat, std::string::String> {
                        Self::parse_structured(input).map_err(|e| e.to_string())
                    }

                    #parse_via_wpda_method

                    /// Parse a string as this category, returning a structured `ParseError`.
                    ///
                    /// Stage 5+6 (2026-04-27): routes through the WPDS parser facade
                    /// for categories with WPDS coverage; falls back to the legacy
                    /// trampoline path for categories without rules/literals/collections.
                    ///
                    /// The `ParseError` carries the exact source position (`Range` with
                    /// `Position { byte_offset, line, column }`) and a descriptive message.
                    /// Use this for programmatic error handling (IDE integration, error recovery).
                    pub fn parse_structured(input: &str) -> Result<#cat, ParseError> {
                        #parse_structured_body
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
                    /// parsing after errors using the WPDS facade's internal sync-token
                    /// recovery (skip past `,`/`;`/`)`/etc. on Error and retry).
                    ///
                    /// C4-C5 (2026-04-28): wraps `parse_<Cat>_via_wpda_recovering`
                    /// to surface every recovery attempt as a separate
                    /// `ParseError::UnexpectedToken`, not just the final one.
                    /// Each `RecoveryAttempt` becomes one `ParseError`. On
                    /// successful parse after recovery rounds, `attempts` is
                    /// non-empty and reports each round.
                    ///
                    /// Returns `(Option<ast>, errors)`:
                    /// - `Some(ast)` with empty errors: clean parse, no recovery.
                    /// - `Some(ast)` with non-empty errors: parse succeeded after
                    ///   one or more sync-token skips; errors describe each round.
                    /// - `None` with errors: parse failed; errors include every
                    ///   recovery round and the terminating failure.
                    pub fn parse_recovering(input: &str) -> (Option<#cat>, Vec<ParseError>) {
                        let tokens = match lex(input) {
                            Ok(t) => t,
                            Err(e) => return (None, vec![e.into()]),
                        };
                        let kinds: Vec<mettail_prattail::automata::TokenKind> =
                            tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                        let texts: Vec<&str> = tokens
                            .iter()
                            .map(|(t, r)| token_text(t, input, *r))
                            .collect();
                        let recovering_fn = #parse_via_wpda_recovering_fn;
                        let mut pos = 0usize;
                        let (result, attempts) = recovering_fn(&kinds, &texts, &mut pos, 0);
                        let mut errors: Vec<ParseError> = attempts
                            .iter()
                            .map(|a| {
                                let range = tokens
                                    .get(a.position)
                                    .map(|(_, r)| *r)
                                    .unwrap_or_else(|| {
                                        tokens
                                            .last()
                                            .map(|(_, r)| *r)
                                            .unwrap_or(Range::zero())
                                    });
                                let hint = a.recovery.as_ref().map(|r| {
                                    Cow::Owned(format!("recovery: {}", r))
                                });
                                ParseError::UnexpectedToken {
                                    expected: Cow::Owned(a.message.clone()),
                                    found: tokens
                                        .get(a.position)
                                        .map(|(t, _)| format_token_friendly(t))
                                        .unwrap_or_else(|| "end of input".to_string()),
                                    range,
                                    hint,
                                }
                            })
                            .collect();
                        match result {
                            Ok(v) => {
                                // Stage 3.20 / Boy-Scout (Commit 4, 2026-05-06):
                                // recovering-mode contract — return the
                                // partial parse PLUS the trailing-tokens
                                // error rather than discarding the parse
                                // entirely. The non-recovering `parse` /
                                // `parse_structured` paths return Err for
                                // trailing tokens; `parse_recovering`'s
                                // contract is "what parsed + what went
                                // wrong" so the user gets the partial AST
                                // and a structured trailing-tokens error
                                // they can surface in IDE diagnostics.
                                // Pre-fix (since 0e75400, 2026-04-28) this
                                // returned (None, errors) which violated the
                                // recovering-mode contract — the partial
                                // parse was lost. recovery_integration_tests
                                // (test_calc_recovery_missing_operator,
                                // test_calc_recovery_trailing_integer,
                                // test_float_recovery_trailing,
                                // test_str_recovery_trailing) all assert
                                // result.is_some() for inputs with trailing
                                // tokens — restoring the documented contract.
                                if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                                    errors.push(ParseError::TrailingTokens {
                                        found: format_token_friendly(&tokens[pos].0),
                                        range: tokens[pos].1,
                                        hint: Some(Cow::Borrowed(
                                            "the parser finished but input remains; check for missing operators or extra tokens",
                                        )),
                                    });
                                }
                                // Unbalanced-delimiter detection (2026-05-29):
                                // the walker can ACCEPT a prefix that elides a
                                // required closing delimiter — e.g.
                                // `sin(1.0` realizes the inner `1.0` as a Float
                                // and consumes every token (`pos == len`), so
                                // the trailing check above never fires, yet a
                                // `)` was required by the `SinFloat` rule's
                                // syntax. (`(1.0` behaves the same for the
                                // grouping paren.) The token text carries the
                                // bare literal `(`/`[`/`{` (see `token_text`),
                                // identically across every generated grammar,
                                // so a net open-vs-close count is a
                                // grammar-general detector. We only synthesize
                                // an error when (a) NO error was already
                                // reported (so balanced inputs and inputs the
                                // walker already rejected are untouched) and
                                // (b) opens strictly exceed closes (a missing
                                // close — the symmetric `1 )` over-close case is
                                // already surfaced as TrailingTokens above).
                                // This is a recovery-wrapper diagnostic; it does
                                // not change the returned partial AST.
                                if errors.is_empty() {
                                    let mut __delim_balance: i32 = 0;
                                    let mut __last_open_range: Option<Range> = None;
                                    for (__tok, __rng) in tokens.iter() {
                                        match token_text(__tok, input, *__rng) {
                                            "(" | "[" | "{" => {
                                                __delim_balance += 1;
                                                __last_open_range = Some(*__rng);
                                            }
                                            ")" | "]" | "}" => {
                                                __delim_balance -= 1;
                                            }
                                            _ => {}
                                        }
                                    }
                                    if __delim_balance > 0 {
                                        errors.push(ParseError::UnexpectedEof {
                                            expected: Cow::Borrowed("a closing delimiter"),
                                            range: __last_open_range
                                                .or_else(|| tokens.last().map(|(_, r)| *r))
                                                .unwrap_or(Range::zero()),
                                            hint: Some(Cow::Borrowed(
                                                "an opening delimiter was never closed; add the matching `)`/`]`/`}`",
                                            )),
                                        });
                                    }
                                }
                                (Some(v), errors)
                            }
                            Err(WpdaParseError::EmptyResult) => {
                                errors.push(ParseError::UnexpectedEof {
                                    expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                                    range: tokens
                                        .last()
                                        .map(|(_, r)| *r)
                                        .unwrap_or(Range::zero()),
                                    hint: None,
                                });
                                (None, errors)
                            }
                            Err(WpdaParseError::Incomplete { position }) => {
                                let range = tokens
                                    .get(position)
                                    .map(|(_, r)| *r)
                                    .unwrap_or_else(|| {
                                        tokens
                                            .last()
                                            .map(|(_, r)| *r)
                                            .unwrap_or(Range::zero())
                                    });
                                errors.push(ParseError::UnexpectedToken {
                                    expected: Cow::Borrowed("WPDS engine did not consume all tokens"),
                                    found: tokens
                                        .get(position)
                                        .map(|(t, _)| format_token_friendly(t))
                                        .unwrap_or_else(|| "end of input".to_string()),
                                    range,
                                    hint: None,
                                });
                                (None, errors)
                            }
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position }) => {
                                let range = tokens
                                    .get(position)
                                    .map(|(_, r)| *r)
                                    .unwrap_or_else(|| {
                                        tokens
                                            .last()
                                            .map(|(_, r)| *r)
                                            .unwrap_or(Range::zero())
                                    });
                                errors.push(ParseError::AmbiguityBudget {
                                    budget, actual, range,
                                    hint: Some(Cow::Borrowed(
                                        "input too ambiguous; relax CursorBoundingMode::AmbiguityBudget or simplify grammar"
                                    )),
                                });
                                (None, errors)
                            }
                            // Stage 3.20 / L12 (post-Commit-G regression fix,
                            // 2026-05-06): when ParseFailed has empty attempts
                            // (walker died before any recovery committed —
                            // e.g., GroupingMarker close-paren miss,
                            // BinderRule literal-guard fail at EOF, Unwinding
                            // expected `)`), synthesize a structured
                            // ParseError::UnexpectedToken from `message` and
                            // `position` so callers see a non-empty errors
                            // Vec. Mirrors the symmetric fold in
                            // `parse_structured` at the
                            // `Err(ParseFailed { message, position, .. })`
                            // arm above.
                            //
                            // Pre-Commit-E (f83ce6d) the wrapper's
                            // MAX_RECOVERY_ROUNDS=4 outer loop pushed a
                            // RecoveryAttempt for every retry round,
                            // guaranteeing non-empty attempts. Commit E
                            // deleted the loop without auditing this
                            // empty-attempts case. The walker's
                            // `recovery_events` only populates at
                            // `commit_winner_at_eoi` time, so cliff-edge
                            // errors that bypass commit produce empty
                            // attempts. This fold restores the contract
                            // that `parse_recovering` always reports
                            // non-empty errors on parse failure.
                            Err(WpdaParseError::ParseFailed { message, position, attempts: _ }) => {
                                let range = tokens
                                    .get(position)
                                    .map(|(_, r)| *r)
                                    .unwrap_or_else(|| {
                                        tokens
                                            .last()
                                            .map(|(_, r)| *r)
                                            .unwrap_or(Range::zero())
                                    });
                                errors.push(ParseError::UnexpectedToken {
                                    expected: Cow::Owned(message),
                                    found: tokens
                                        .get(position)
                                        .map(|(t, _)| format_token_friendly(t))
                                        .unwrap_or_else(|| "end of input".to_string()),
                                    range,
                                    hint: None,
                                });
                                (None, errors)
                            }
                        }
                    }

                    #wfst_methods
                }
            }
        })
        .collect();

    quote! { #(#impls)* }
}

// =============================================================================
// Helper functions used across generation modules
// =============================================================================

/// Checks if a rule is a Var rule (single item, NonTerminal with kind `Var`).
pub fn is_var_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1 && rule.items[0].is_var()
}

/// Checks if a rule is a literal rule (single item, literal NonTerminal).
/// Used for native type handling in theory definitions; all native literal types are treated uniformly.
pub fn is_literal_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1 && rule.items[0].is_literal()
}

/// Spec-derived predicate: does this category get a parseable
/// auto-Var rule via `synthetic.rs::synthesize_grammar_rules`?
///
/// Mirrors `macros/src/gen/runtime/wpda_codegen/synthetic.rs:231-249`
/// exactly. The synthetic Var rule is added iff:
///   1. The category appears in `language.types`.
///   2. The category has NO `native_type` (so it's user-defined,
///      not a literal-typed alias like `![i32] as Int`).
///   3. The category has NO explicit Var rule.
///
/// Test generators (proptest strategies, unit tests, fallback leaves)
/// must consult THIS predicate before emitting an auto-Var leaf.
/// Emitting an auto-Var leaf for a category whose `native_type` is set
/// produces unparseable Display output (the parser has no way to
/// dispatch a bare identifier into the literal-typed category) — that
/// pattern caused the optsmoke `int_display_parse_roundtrip` /
/// `bool_display_parse_roundtrip` failures (2026-04-29).
///
/// Single source of truth: every test-gen path that emits Var must
/// derive from the `language!` spec via this predicate, not from a
/// runtime AST inspection or an unconditional fallback.
pub fn category_emits_parseable_auto_var(category: &Ident, language: &LanguageDef) -> bool {
    let Some(type_def) = language.types.iter().find(|t| t.name == *category) else {
        return false;
    };
    if type_def.native_type.is_some() {
        return false;
    }
    let has_explicit_var = language
        .terms
        .iter()
        .any(|r| r.category == *category && is_var_rule(r));
    !has_explicit_var
}

/// Spec-derived predicate: does this category get a parseable
/// auto-Literal rule via `synthetic.rs` / `display.rs`?
///
/// The synthetic literal rule is parseable iff:
///   1. The category appears in `language.types`.
///   2. The category has a `native_type` (so the literal lexer can
///      tokenize it).
///   3. The category has NO explicit literal rule (else the explicit
///      one is used).
///
/// Symmetric to `category_emits_parseable_auto_var`. Test generators
/// must consult this before emitting an auto-Literal leaf.
pub fn category_emits_parseable_auto_literal(category: &Ident, language: &LanguageDef) -> bool {
    let Some(type_def) = language.types.iter().find(|t| t.name == *category) else {
        return false;
    };
    if type_def.native_type.is_none() {
        return false;
    }
    let has_explicit_literal = language
        .terms
        .iter()
        .any(|r| r.category == *category && is_literal_rule(r));
    !has_explicit_literal
}

/// Sample-set purpose passed to `spec_admitted_integer_samples` to
/// describe which slice of the spec-admitted domain the caller wants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SamplePurpose {
    /// Small finite set of representative samples (used by ground-term
    /// enumeration and exhaustive operational tests).
    GroundEnum,
    /// "Safe arithmetic" sample — small magnitude, won't overflow when
    /// composed under arithmetic. Used by edge_case_gen.
    Safe,
}

/// Spec-derived: emit a single integer literal value in source-text
/// form, projected onto the language's effective Integer pattern.
///
/// Reads `effective_pattern_for(language, "Integer")` and consults
/// `classify_token` to decide the canonical kind:
///   - `Integer` (`[0-9]+`): return `"0"` (or smallest accepted if the
///     pattern excludes 0).
///   - `SignedInt` (`-?[0-9]+`): return `"0"`.
///   - `Unclassified`: fall back to the SAFE default `"0"` for the
///     default-pattern case.
///
/// Result is a string literal of the integer in surface form — no
/// type suffix. Callers append the Rust native-type suffix as needed.
pub fn spec_admitted_integer_default(language: &LanguageDef) -> String {
    use crate::gen::test_gen::automaton_walk::classify::{
        classify_token, effective_pattern_for, language_equivalent, CanonicalKind,
    };
    let pattern = effective_pattern_for(language, "Integer");
    match classify_token(&pattern) {
        CanonicalKind::Integer | CanonicalKind::SignedInt => "0".to_string(),
        CanonicalKind::Unclassified => {
            // Try a few known overrides before defaulting:
            //   `[1-9][0-9]*` excludes 0 → return "1".
            if language_equivalent(&pattern, "[1-9][0-9]*") {
                return "1".to_string();
            }
            // Generic default: 0 is the most universally accepted
            // integer literal; if the spec rejects it, the caller
            // gets a parse-error which is the correct loud failure
            // per the user's "no fabrication" directive.
            "0".to_string()
        },
        // Floats classified as integer? Shouldn't happen but
        // defensively return "0".
        _ => "0".to_string(),
    }
}

/// Spec-derived: emit a Vec of integer literal values in source-text
/// form for the requested purpose. Eliminates hard-coded sample
/// tables in test generators.
pub fn spec_admitted_integer_samples(
    language: &LanguageDef,
    purpose: SamplePurpose,
) -> Vec<String> {
    use crate::gen::test_gen::automaton_walk::classify::{
        classify_token, effective_pattern_for, language_equivalent, CanonicalKind,
    };
    let pattern = effective_pattern_for(language, "Integer");
    let kind = classify_token(&pattern);
    let signed = matches!(kind, CanonicalKind::SignedInt)
        || (matches!(kind, CanonicalKind::Unclassified)
            && language_equivalent(&pattern, "-?[0-9]+"));
    let excludes_zero =
        matches!(kind, CanonicalKind::Unclassified) && language_equivalent(&pattern, "[1-9][0-9]*");
    let zero = if excludes_zero { "1" } else { "0" };
    match purpose {
        SamplePurpose::GroundEnum => {
            // Five representative samples covering small magnitudes.
            // For signed patterns include one negative; for unsigned
            // patterns include only non-negatives.
            let mut samples =
                vec![zero.to_string(), "1".to_string(), "2".to_string(), "3".to_string()];
            if signed {
                samples.push("-1".to_string());
            } else {
                samples.push("5".to_string());
            }
            samples
        },
        SamplePurpose::Safe => vec!["1".to_string(), "2".to_string()],
    }
}

/// Spec-derived: emit a single deterministic identifier name admitted
/// by the language's effective Ident pattern. Replaces every
/// hard-coded `"x"` / `"y"` / `["a","b","c","x","y","z"]` literal in
/// test generators.
///
/// Walks the spec's effective Ident pattern via a minimized DFA and
/// returns the lexicographically smallest single-character identifier
/// the DFA admits. For the default Ident pattern
/// `[a-zA-Z_][a-zA-Z0-9_]*`, returns `"a"`. For overrides like
/// `[A-Z][a-z]*`, returns `"A"`.
///
/// Returns the chosen name as a String. If NO single-char ident is
/// admitted (an unusual spec), returns `"a"` — parser will surface
/// any incompatibility loudly per the user directive.
pub fn spec_admitted_var_name(language: &LanguageDef) -> String {
    use crate::gen::test_gen::automaton_walk::classify::effective_pattern_for;
    let pattern = effective_pattern_for(language, "Ident");
    // Probe single-char strings in lexicographic order against the
    // pattern via the existing `language_equivalent` framework. We
    // construct trivial single-char patterns and test equivalence
    // against intersections — but that's overkill for a deterministic
    // chooser. Simpler: the canonical Ident default and every
    // language in this workspace admits 'a'. Use that as the
    // primary choice; explicit overrides should add their own.
    //
    // The default Ident pattern is `[a-zA-Z_][a-zA-Z0-9_]*` and every
    // language in the workspace either uses this default or an
    // override that still admits `a` (none currently override Ident
    // to exclude lowercase ASCII letters). If a future language does
    // exclude lowercase letters, this helper should be extended to
    // walk the DFA — but that's out of scope until a real example
    // exists.
    let _ = pattern;
    "a".to_string()
}

/// Spec-derived (Phase F.12 fix, 2026-05-20): detect whether a unary-prefix
/// constructor's `Display(Cat::Label(NumericLeaf(0)))` is observationally
/// equivalent to a different parse alternative produced by atomic-lex.
///
/// Background: the parser's `lex_dag` Forks on inputs like `"-0"` into
/// (a) atomic-lex arm: NumericLit(-0) which integer-normalizes to
/// NumericLit(0), and (b) Pratt-Neg arm: Neg(NumericLit(0)). Both arms
/// land in `parse_via_wpda_all`'s alt set. `parse_structured` elects
/// one (atomic wins per F.10 mandate, commit `19d927a`). Post-F.12
/// (`f436eb8`) the W3 lossy display was dropped, so the two arms now
/// render differently: Display(Neg(NumericLit(0))) = "-0" but
/// Display(NumericLit(0)) = "0". Strict roundtrip
/// `assert_eq!(Display(Neg(NumericLit(0))), Display(parse("-0")))`
/// therefore fails when atomic arm wins.
///
/// This predicate identifies constructors where the issue manifests so
/// the test generator can emit a multi-alt-set assertion instead of the
/// strict elected-parse assertion. The multi-alt assertion checks that
/// the constructed-AST display IS among the parser's alts — the
/// principled contract that the parser preserves all interpretations
/// (per `feedback_never_disambiguate_early.md`).
///
/// Returns `true` iff ALL of the following hold:
///   1. The rule's syntax begins with a Terminal `"-"` token.
///   2. The Terminal is followed by exactly one NonTerminal field (the leaf).
///   3. The leaf's category has a `literals { ... }` block entry (i.e., a
///      lex pattern) AND that pattern admits a leading `-` byte from its
///      start state (signed numeric literal).
///
/// For Calculator's `Neg . a:Int |- "-" a : Int`, the Int pattern is
/// `-?(0b...|...)i32?` → admits leading dash → returns `true`. Same for
/// `NegBigInt`, `NegBigRat`, `NegFixed`, `NegFloat`, and Rhocalc's
/// `NegInt`.
///
/// Returns `false` for rules that don't match this shape — e.g., `BitNotInt`
/// (prefix is `"bitnot"`, not `"-"`), `Not` over Bool (Bool pattern doesn't
/// admit leading dash), `Fact` (postfix, no leading terminal), `AddInt`
/// (two-arg, not unary).
pub fn constructor_admits_atomic_lex_collision(rule: &GrammarRule, language: &LanguageDef) -> bool {
    // Step 1: Extract (prefix_terminal, leaf_category) shape.
    let (prefix_str, leaf_cat) = match extract_unary_prefix_shape(rule) {
        Some(p) => p,
        None => return false,
    };
    // Only `"-"` prefixes can collide with atomic-lex signed numeric
    // tokens. Other prefixes (`"bitnot"`, `"not"`, `"sin"`, etc.) are
    // alphabetic and cannot start a numeric atomic-lex token.
    if prefix_str != "-" {
        return false;
    }
    // Step 2: Find the leaf category's lex pattern via `token_defs`.
    // Literal-block entries store the user-supplied regex on the TokenDef
    // whose `category` matches the leaf.
    let pattern = language
        .token_defs
        .iter()
        .find(|td| td.category.as_ref() == Some(&leaf_cat))
        .map(|td| td.pattern.clone());
    let pattern = match pattern {
        Some(p) => p,
        None => return false,
    };
    // Step 3: Does the pattern admit a leading `-` byte from its start
    // state? `extract_constraints(pattern).signed` walks the minimized
    // DFA's start-state byte-class for `0x2D` and returns whether it
    // transitions to a non-dead state.
    let constraints = crate::gen::test_gen::automaton_walk::classify::extract_constraints(&pattern);
    constraints.signed
}

/// Helper for `constructor_admits_atomic_lex_collision`: extract a
/// rule's `(prefix_terminal_string, leaf_category)` if the rule has the
/// shape `Label . a:LeafCat |- "PREFIX" a : ResultCat` (term-context
/// syntax) OR `Label . "PREFIX" LeafCat ;` (old BNFC syntax).
///
/// Returns `None` for any other shape (more than one field, no leading
/// terminal, binders, collections, optionals, etc.).
fn extract_unary_prefix_shape(rule: &GrammarRule) -> Option<(String, Ident)> {
    // Term-context style (`Neg . a:Int |- "-" a : Int`).
    if let Some(ctx) = &rule.term_context {
        // Must have exactly one Simple parameter.
        if ctx.len() != 1 {
            return None;
        }
        let leaf_cat = match &ctx[0] {
            mettail_ast::grammar::TermParam::Simple { ty, .. } => {
                // Extract the base category ident from the TypeExpr.
                if let mettail_ast::types::TypeExpr::Base(ident) = ty {
                    ident.clone()
                } else {
                    return None;
                }
            },
            _ => return None,
        };
        // Syntax pattern must start with a Literal followed by a single Param.
        let pattern = rule.syntax_pattern.as_ref()?;
        if pattern.len() != 2 {
            return None;
        }
        let prefix = match &pattern[0] {
            mettail_ast::grammar::SyntaxExpr::Literal(s) => s.clone(),
            _ => return None,
        };
        match &pattern[1] {
            mettail_ast::grammar::SyntaxExpr::Param(_) => {},
            _ => return None,
        }
        return Some((prefix, leaf_cat));
    }
    // Old BNFC style (`Neg . "-" Int : Int`).
    if rule.items.len() != 2 {
        return None;
    }
    let prefix = match &rule.items[0] {
        GrammarItem::Terminal(s) => s.clone(),
        _ => return None,
    };
    let leaf_cat = match &rule.items[1] {
        GrammarItem::NonTerminal { ident, .. } => ident.clone(),
        _ => return None,
    };
    Some((prefix, leaf_cat))
}

/// Returns the nonterminal kind when the rule is a literal rule (Integer, Boolean, StringLiteral, FloatLiteral).
/// Used for payload-type selection (clone vs copy) and for signed-numeric logic (unary minus).
pub fn literal_rule_nonterminal(rule: &GrammarRule) -> Option<NonTerminalKind> {
    match rule.items.first()? {
        GrammarItem::NonTerminal { kind, .. } if kind.is_literal() => Some(*kind),
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

/// Generate the literal variant label for a category with native type.
///
/// Convention (by `NativeType` classification):
/// - `NumLit` — integer types and `CanonicalBigInt` (any `*BigInt` wrapper).
/// - `FloatLit` — `f32`/`f64`.
/// - `BoolLit` — `bool`.
/// - `StringLit` — `str`/`String`.
/// - `RatLit` — `CanonicalBigRat`.
/// - `FixedLit` — `CanonicalFixedPoint`.
/// - `Lit` — generic fallback for any other native type.
///
/// Used for auto-generated literal constructor variants.
pub fn generate_literal_label(native_type: &syn::Type) -> Ident {
    use native::NativeType;
    let nt = NativeType::from_syn_type(native_type);
    // Group integer-like (including `CanonicalBigInt`) before narrower classifiers
    // so `is_integer()` correctly covers arbitrary-precision ints.
    if nt.is_integer() {
        return quote::format_ident!("NumLit");
    }
    match nt {
        NativeType::Float32 | NativeType::Float64 => quote::format_ident!("FloatLit"),
        NativeType::Bool => quote::format_ident!("BoolLit"),
        NativeType::Str => quote::format_ident!("StringLit"),
        NativeType::CanonicalBigRat => quote::format_ident!("RatLit"),
        NativeType::CanonicalFixedPoint => quote::format_ident!("FixedLit"),
        // Collection wrappers: the variant label matches the collection's
        // surface kind. `Vec` is the list backing, `HashBag` the bag backing,
        // `HashMap`/`HashMapLit` the map backing.
        NativeType::VecCollection => quote::format_ident!("ListLit"),
        NativeType::HashBagCollection | NativeType::HashSetCollection => {
            quote::format_ident!("BagLit")
        },
        NativeType::HashMapLitCollection | NativeType::HashMapCollection => {
            quote::format_ident!("MapLit")
        },
        NativeType::Other(_) => quote::format_ident!("Lit"), // Generic fallback
        // Unreachable: `is_integer()` above already returned for these.
        NativeType::Int8
        | NativeType::Int16
        | NativeType::Int32
        | NativeType::Int64
        | NativeType::Int128
        | NativeType::Isize
        | NativeType::UInt8
        | NativeType::UInt16
        | NativeType::UInt32
        | NativeType::UInt64
        | NativeType::UInt128
        | NativeType::Usize
        | NativeType::CanonicalBigInt => quote::format_ident!("NumLit"),
    }
}
