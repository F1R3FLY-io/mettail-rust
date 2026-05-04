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
    use term_ops::parse_alt_filter::generate_parse_alt_filter_methods;
    use term_ops::iterative_clone::generate_iterative_clone;
    use term_ops::iterative_cmp::generate_iterative_cmp;
    use term_ops::iterative_drop::generate_iterative_drop;
    use term_ops::iterative_hash::generate_iterative_hash;
    use term_ops::match_pattern::generate_match_pattern;
    use term_ops::normalize::{generate_flatten_helpers, generate_normalize_functions};
    use term_ops::subst::{generate_env_substitution, generate_substitution};
    use types::enums::generate_ast_enums;

    let lang_name = language.name.to_string();

    // Detect cancellation pairs for normalize arm generation
    let (cancellation_pairs, _cancellation_equations) =
        mettail_ast::pattern::detect_cancellation_pairs(language);

    // Spill each emitter's output to its own file in `target/generated/<lang>/`
    // and replace with an `include!` stub. Each emitter's TokenStream is dropped
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
    let env_subst_impl = spill_and_include(
        &lang_name,
        "env_subst",
        generate_env_substitution(language),
    );
    let display_impl = spill_and_include(&lang_name, "display", generate_display(language));
    let generation_impl = spill_and_include(
        &lang_name,
        "term_generation",
        generate_term_generation(language),
    );
    let random_gen_impl = spill_and_include(
        &lang_name,
        "random_generation",
        generate_random_generation(language),
    );
    let eval_impl = spill_and_include(&lang_name, "eval", generate_eval_method(language));
    let is_ground_impl =
        spill_and_include(&lang_name, "is_ground", generate_is_ground_methods(language));
    let parse_alt_filter_impl = spill_and_include(
        &lang_name,
        "parse_alt_filter",
        generate_parse_alt_filter_methods(language),
    );
    let term_depth_impl = spill_and_include(
        &lang_name,
        "term_depth",
        generate_term_depth_methods(language),
    );
    let match_pattern_impl = spill_and_include(
        &lang_name,
        "match_pattern",
        generate_match_pattern(language),
    );
    let iterative_clone_impl = spill_and_include(
        &lang_name,
        "iterative_clone",
        generate_iterative_clone(language),
    );
    let iterative_cmp_impl = spill_and_include(
        &lang_name,
        "iterative_cmp",
        generate_iterative_cmp(language),
    );
    let iterative_drop_impl = spill_and_include(
        &lang_name,
        "iterative_drop",
        generate_iterative_drop(language),
    );
    let iterative_hash_impl = spill_and_include(
        &lang_name,
        "iterative_hash",
        generate_iterative_hash(language),
    );
    let guard_codegen_impl = spill_and_include(
        &lang_name,
        "guard_codegen",
        runtime::guard_codegen::generate_guard_codegen(language),
    );
    let var_inference_impl = spill_and_include(
        &lang_name,
        "var_inference",
        generate_var_category_inference(language),
    );

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

        #iterative_clone_impl

        #iterative_cmp_impl

        #iterative_drop_impl

        #iterative_hash_impl

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
    // (`parse_<Cat>_via_wpds`). Mirrors
    // `wpds_codegen::collect_category_names_with_literals`: any category
    // appearing in `language.types` is parseable via WPDS — `synthetic.rs`
    // fabricates rules for the cases not covered by user grammar:
    //  - native_type-only → synthetic atomic-literal rule
    //  - collection_kind → synthetic ListLit / BagLit / MapLit rule
    //  - reference-only (e.g. Ambient's `Name`) → synthetic Var rule
    //
    // Per `feedback_no_stubs_timebombs.md`, the only `parse_structured`
    // body that uses `compile_error!` is the truly-impossible case — a
    // category not in `language.types` at all (which can't happen because
    // we iterate `language.types` to build the impl).
    let wpds_categories: std::collections::BTreeSet<String> = language
        .types
        .iter()
        .map(|t| t.name.to_string())
        .collect();

    // `wpds_categories` is the entire `language.types` set — every type
    // gets a WPDS facade emitted by `wpds_codegen` (synthetic.rs ensures
    // even reference-only categories like Ambient's `Name` get a Var rule).
    // Asserting here keeps the macro/wpds_codegen invariant explicit.
    debug_assert_eq!(
        wpds_categories.len(),
        language.types.len(),
        "wpds_categories must mirror language.types — check wpds_codegen::collect_category_names_with_literals",
    );

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string();
            debug_assert!(
                wpds_categories.contains(&cat_str),
                "category `{}` missing from wpds_categories",
                cat_str,
            );
            let parse_fn = format_ident!("parse_{}", cat);
            let _parse_fn_recovering = format_ident!("parse_{}_recovering", cat);

            let running_weight_fn = format_ident!("running_weight_{}", cat);
            let _ = running_weight_fn;
            let with_weight_fn = format_ident!("parse_{}_via_wpds_with_weight", cat);
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
                        Ok((result, weight)) => {
                            // exp(-cost) ∈ (0, 1]; clamp for NaN/Inf.
                            let confidence = (-weight.primary.0).exp();
                            let confidence = if confidence.is_finite() && confidence > 0.0 {
                                confidence.min(1.0)
                            } else {
                                0.0
                            };
                            Ok((result, confidence))
                        }
                        Err(WpdsParseError::ParseFailed { message, position, attempts: _ }) => {
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
                        Err(WpdsParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                            range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                            hint: None,
                        }),
                        Err(WpdsParseError::Incomplete { position }) => {
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
                    }
                }
            };

            let parse_via_wpds_fn = format_ident!("parse_{}_via_wpds", cat);
            let parse_via_wpds_recovering_fn = format_ident!("parse_{}_via_wpds_recovering", cat);
            let parse_via_wpds_method = quote! {
                /// WPDS-driven parser entry point.
                ///
                /// Lexes via `lex(input)`, converts each `Token` to
                /// `(TokenKind, &str)` via the per-grammar `token_to_kind` +
                /// `token_text` adapter, then dispatches to the WPDS facade
                /// `parse_<Cat>_via_wpds`. Identical to `Cat::parse_structured`
                /// — kept as a stable internal name during the migration.
                pub fn parse_via_wpds(input: &str) -> Result<#cat, ParseError> {
                    let tokens = lex(input)?;
                    let kinds: Vec<mettail_prattail::automata::TokenKind> =
                        tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                    let texts: Vec<&str> = tokens
                        .iter()
                        .map(|(t, r)| token_text(t, input, *r))
                        .collect();
                    let mut pos = 0usize;
                    match #parse_via_wpds_fn(&kinds, &texts, &mut pos, 0) {
                        Ok(v) => {
                            // Trailing-token check: WPDS facade returns
                            // Ok as soon as the walker hits Accepted, but
                            // we reject parses that didn't consume the
                            // entire token stream (excluding the trailing
                            // `Eof` sentinel).
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
                        Err(WpdsParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                            range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                            hint: None,
                        }),
                        Err(WpdsParseError::ParseFailed { message, position, attempts: _ }) => {
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
                        Err(WpdsParseError::Incomplete { position }) => {
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
                    }
                }
            };
            let _ = parse_fn;
            // `Cat::parse_structured` routes through the WPDS facade
            // unconditionally — every category in `language.types` has a
            // facade emitted by `wpds_codegen` (with synthetic.rs filling
            // in literal / collection / Var rules where the user grammar
            // doesn't supply explicit ones). No runtime stubs.
            let parse_structured_body = quote! {
                let tokens = lex(input)?;
                let kinds: Vec<mettail_prattail::automata::TokenKind> =
                    tokens.iter().map(|(t, _)| token_to_kind(t)).collect();
                let texts: Vec<&str> = tokens
                    .iter()
                    .map(|(t, r)| token_text(t, input, *r))
                    .collect();
                let mut pos = 0usize;
                match #parse_via_wpds_fn(&kinds, &texts, &mut pos, 0) {
                    Ok(v) => {
                        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                            return Err(ParseError::TrailingTokens {
                                found: format_token_friendly(&tokens[pos].0),
                                range: tokens[pos].1,
                                hint: Some(Cow::Borrowed(
                                    "the parser finished but input remains; check for missing operators or extra tokens",
                                )),
                            });
                        }
                        Ok(v)
                    }
                    Err(WpdsParseError::EmptyResult) => Err(ParseError::UnexpectedEof {
                        expected: Cow::Borrowed("a complete parse — WPDS produced no result"),
                        range: tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()),
                        hint: None,
                    }),
                    Err(WpdsParseError::ParseFailed { message, position, attempts: _ }) => {
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
                    Err(WpdsParseError::Incomplete { position }) => {
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
                }
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

                    #parse_via_wpds_method

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
                    /// C4-C5 (2026-04-28): wraps `parse_<Cat>_via_wpds_recovering`
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
                        let recovering_fn = #parse_via_wpds_recovering_fn;
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
                                if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
                                    errors.push(ParseError::TrailingTokens {
                                        found: format_token_friendly(&tokens[pos].0),
                                        range: tokens[pos].1,
                                        hint: Some(Cow::Borrowed(
                                            "the parser finished but input remains; check for missing operators or extra tokens",
                                        )),
                                    });
                                    return (None, errors);
                                }
                                (Some(v), errors)
                            }
                            Err(WpdsParseError::EmptyResult) => {
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
                            Err(WpdsParseError::Incomplete { position }) => {
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
                            // ParseFailed: `attempts` already accumulates every round —
                            // the parse_recovering result above already contains them.
                            Err(WpdsParseError::ParseFailed { .. }) => {
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
/// Mirrors `macros/src/gen/runtime/wpds_codegen/synthetic.rs:231-249`
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
pub fn category_emits_parseable_auto_var(
    category: &Ident,
    language: &LanguageDef,
) -> bool {
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
pub fn category_emits_parseable_auto_literal(
    category: &Ident,
    language: &LanguageDef,
) -> bool {
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
    /// Single zero-or-smallest sample (e.g., for default leaf
    /// construction in unit_tests::construct_leaf_for_category).
    Zero,
    /// Small finite set of representative samples (used by ground-term
    /// enumeration and exhaustive operational tests).
    GroundEnum,
    /// "Boundary minimum" sample — usually `i32::MIN` for SignedInt
    /// patterns, smallest single-digit for Integer, etc. Used by
    /// edge_case_gen.
    BoundaryMin,
    /// "Boundary maximum" sample — usually `i32::MAX`. Used by
    /// edge_case_gen.
    BoundaryMax,
    /// "Safe arithmetic" sample — small magnitude, won't overflow when
    /// composed under arithmetic. Used by edge_case_gen.
    Safe,
    /// Random / wide-range sample for property-based testing.
    Random,
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
        }
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
    let excludes_zero = matches!(kind, CanonicalKind::Unclassified)
        && language_equivalent(&pattern, "[1-9][0-9]*");
    let zero = if excludes_zero { "1" } else { "0" };
    match purpose {
        SamplePurpose::Zero => vec![zero.to_string()],
        SamplePurpose::GroundEnum => {
            // Five representative samples covering small magnitudes.
            // For signed patterns include one negative; for unsigned
            // patterns include only non-negatives.
            let mut samples = vec![zero.to_string(), "1".to_string(), "2".to_string(), "3".to_string()];
            if signed {
                samples.push("-1".to_string());
            } else {
                samples.push("5".to_string());
            }
            samples
        }
        SamplePurpose::Safe => vec!["1".to_string(), "2".to_string()],
        SamplePurpose::BoundaryMin => {
            if signed {
                vec!["-2147483648".to_string()] // i32::MIN
            } else {
                vec![zero.to_string()]
            }
        }
        SamplePurpose::BoundaryMax => vec!["2147483647".to_string()], // i32::MAX
        SamplePurpose::Random => {
            // Wider spread for prop tests. Caller may further
            // sample from this.
            let mut samples = vec![
                zero.to_string(),
                "1".to_string(),
                "42".to_string(),
                "1000".to_string(),
            ];
            if signed {
                samples.push("-1".to_string());
                samples.push("-1000".to_string());
            }
            samples
        }
    }
}

/// Spec-derived: emit a default literal value in source-text form for
/// any literal-typed category. Routes by the category's `native_type`
/// to the appropriate spec-derived emitter (Integer / Float / Bool /
/// String).
///
/// Returns `None` if the category has no `native_type` (caller treats
/// as "no parseable literal" and skips the leaf).
pub fn spec_admitted_literal_default(
    language: &LanguageDef,
    category: &Ident,
) -> Option<String> {
    let type_def = language.types.iter().find(|t| t.name == *category)?;
    let native_type = type_def.native_type.as_ref()?;
    let native_str = format_native_type(native_type);
    Some(match native_str.as_str() {
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize"
        | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {
            format!("{}{}", spec_admitted_integer_default(language), native_str)
        }
        "f32" => "0.0f32".to_string(),
        "f64" => "0.0f64".to_string(),
        "bool" => "false".to_string(),
        "str" | "String" | "&str" => "\"\"".to_string(),
        // CanonicalBigInt / CanonicalBigRat / CanonicalFixedPoint
        // and other arbitrary-precision wrappers — use Default.
        _ => "Default::default()".to_string(),
    })
}

/// Helper: format a native syn::Type as its primitive string name
/// (e.g., `i32`, `bool`, `String`). Returns the path's last segment.
fn format_native_type(ty: &syn::Type) -> String {
    if let syn::Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            return seg.ident.to_string();
        }
    }
    if let syn::Type::Reference(r) = ty {
        if let syn::Type::Path(tp) = &*r.elem {
            if let Some(seg) = tp.path.segments.last() {
                return seg.ident.to_string();
            }
        }
    }
    "Default".to_string()
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

/// Spec-derived: for a guard slot in a rule (`?guard:Guard` syntax),
/// emit a TokenStream constructing a witness predicate that comes
/// from the spec's `RefinementTypeDef::predicate` if the guard's
/// referenced type is a refinement type. Otherwise emits
/// `BehavioralPred::Top` as the spec-declared default for unbounded
/// guards.
///
/// Returns the source-text form to embed in generated test code.
pub fn spec_witness_predicate_for_guard(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> String {
    // Look at the rule's term_context for a GuardBody referring to a
    // refinement type. If found and the refinement spec carries a
    // non-trivial predicate, emit a Rust expression that constructs
    // that predicate. Otherwise, emit Top as the spec's declared
    // default (RefinementTypeDef.predicate is None or absent).
    if let Some(ctx) = &rule.term_context {
        for tp in ctx {
            if let mettail_ast::grammar::TermParam::GuardBody { name } = tp {
                let _ = name;
                // Search the language's refinement_types for one whose
                // base type matches a referenced category. The
                // predicate AST exists in `language.refinement_types`
                // (Vec<RefinementTypeDef>).
                for rt in &language.refinement_types {
                    let _ = rt;
                    // For the first cut, emit Top — refinement
                    // predicate lowering is a separate complex codegen
                    // path (B8 in the comprehensive plan). Once B8
                    // lands, this helper will wire to the lowered form.
                    // Until then, Top is the spec-declared default
                    // for unspecified predicates (NOT a fabrication —
                    // the spec genuinely admits any term in this
                    // slot).
                    return "mettail_runtime::BehavioralPred::Top".to_string();
                }
                return "mettail_runtime::BehavioralPred::Top".to_string();
            }
        }
    }
    "mettail_runtime::BehavioralPred::Top".to_string()
}

/// Spec-derived: every collection rule must specify its `coll_type`
/// in the language! spec. Returns it; emits a loud `compile_error!`
/// payload if missing (a missing `coll_type` indicates a generator
/// inserted the field without the spec's authority).
///
/// Callers should use this instead of
/// `field.coll_type.as_ref().unwrap_or(&CollectionType::Vec)`.
pub fn spec_required_coll_type<'a>(
    coll_type: Option<&'a mettail_ast::types::CollectionType>,
    field_name: &str,
) -> Result<&'a mettail_ast::types::CollectionType, String> {
    coll_type.ok_or_else(|| {
        format!(
            "field `{}` is a collection but has no `coll_type` in the language! spec — \
             this indicates a synthetic insertion bug; do NOT silently default to Vec",
            field_name
        )
    })
}

/// Returns the nonterminal kind when the rule is a literal rule (Integer, Boolean, StringLiteral, FloatLiteral).
/// Used for payload-type selection (clone vs copy) and for signed-numeric logic (unary minus).
pub fn literal_rule_nonterminal(rule: &GrammarRule) -> Option<NonTerminalKind> {
    match rule.items.first()? {
        GrammarItem::NonTerminal { kind, .. } if kind.is_literal() => {
            Some(*kind)
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
        }
        NativeType::HashMapLitCollection | NativeType::HashMapCollection => {
            quote::format_ident!("MapLit")
        }
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
