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

    // Stage 3 (2026-04-27): determine which categories have a WPDS facade
    // emitted (`parse_<Cat>_via_wpds`). The facade is emitted for every
    // category in `collect_category_names_with_literals` — categories
    // with user-written rules, from_literals TokenDefs, or collection_kind.
    // For categories without a facade, we skip emitting the parallel
    // `Cat::parse_via_wpds` method.
    let wpds_categories: std::collections::BTreeSet<String> = {
        let mut set = std::collections::BTreeSet::new();
        // user rules
        for rule in &language.terms {
            set.insert(rule.category.to_string());
        }
        // from_literals TokenDefs
        for type_def in &language.types {
            let name = type_def.name.to_string();
            let has_lit = language.token_defs.iter().any(|td| {
                td.from_literals
                    && td.category.as_ref().map(|c| c.to_string() == name).unwrap_or(false)
            });
            if has_lit {
                set.insert(name);
            }
        }
        // collection_kind
        for type_def in &language.types {
            if type_def.collection_kind.is_some() {
                set.insert(type_def.name.to_string());
            }
        }
        set
    };

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string();
            let has_wpds_facade = wpds_categories.contains(&cat_str);
            let parse_fn = format_ident!("parse_{}", cat);
            let _parse_fn_recovering = format_ident!("parse_{}_recovering", cat);

            let running_weight_fn = format_ident!("running_weight_{}", cat);
            let _ = running_weight_fn;
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

                /// B4: Parse with confidence scoring.
                ///
                /// Returns `(ast, confidence)`. Stage 7 (2026-04-27): the
                /// confidence value is now always `0.0` because the trampoline's
                /// `running_weight_<Cat>` accumulator was removed. The WPDS
                /// engine maintains its own internal lex-min cost but does not
                /// currently expose a per-parse confidence summary; future work
                /// can wire the engine's terminal weight through.
                pub fn parse_with_confidence(input: &str) -> Result<(#cat, f64), ParseError> {
                    let result = Self::parse_structured(input)?;
                    Ok((result, 0.0))
                }
            };

            let parse_via_wpds_fn = format_ident!("parse_{}_via_wpds", cat);
            let parse_via_wpds_method = if has_wpds_facade {
                quote! {
                    /// Stage 3 (2026-04-27): WPDS-driven parser path.
                    ///
                    /// Lexes via the trampoline-side `lex(input)`, converts each
                    /// `Token` to `(TokenKind, &str)` via the per-grammar
                    /// `token_to_kind` + `token_text` adapter (Stage 2), then
                    /// dispatches to the WPDS facade `parse_<Cat>_via_wpds`.
                    /// Trampoline `Cat::parse` and this method coexist during
                    /// the migration; after Phase 13's atomic swap, this
                    /// becomes the canonical `Cat::parse`.
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
                                // parity with the trampoline `parse_structured`
                                // requires we reject parses that didn't
                                // consume the entire token stream (excluding
                                // the trailing `Eof` sentinel).
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
                            Err(WpdsParseError::ParseFailed { message, position }) => {
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
                }
            } else {
                quote! {}
            };
            let _ = parse_via_wpds_fn;
            let _ = parse_fn;
            // Stage 5+6 (2026-04-27): `Cat::parse` and `Cat::parse_structured`
            // route through the WPDS parser facade. Categories without a WPDS
            // facade (no rules, no from_literals, no collection_kind) emit a
            // diagnostic stub that reports the missing parser at runtime — in
            // practice none of the shipped grammars hit this path; if any do,
            // it indicates a grammar definition oversight (an unused
            // `LangType` declared but never referenced by any rule).
            let parse_structured_body = if has_wpds_facade {
                quote! {
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
                        Err(WpdsParseError::ParseFailed { message, position }) => {
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
            } else {
                // No WPDS facade for this category. Emit a runtime diagnostic
                // explaining that the category has no rules.
                let cat_name_lit = cat.to_string();
                quote! {
                    let _ = input;
                    Err(ParseError::UnexpectedEof {
                        expected: Cow::Owned(format!(
                            "no parser available for category `{}` — the grammar declares this `LangType` but defines no rules, literals, or collection over it",
                            #cat_name_lit,
                        )),
                        range: Range::zero(),
                        hint: Some(Cow::Borrowed(
                            "add a `terms { … : Cat ; }` rule, a `literals { Cat { … } }` block, or a `![Vec<…>] as Cat` collection declaration",
                        )),
                    })
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
                    /// Stage 7 (2026-04-27): the trampoline-side
                    /// `parse_<Cat>_recovering` was removed; this method now wraps
                    /// `parse_structured` and exposes a single recovered error
                    /// when the WPDS path fails.
                    ///
                    /// Returns `(Option<ast>, errors)`:
                    /// - `Some(ast)` with empty errors: successful parse
                    /// - `None` with one error: parse failed (the WPDS facade has
                    ///   already retried up to MAX_RECOVERY_ROUNDS sync-token skips)
                    pub fn parse_recovering(input: &str) -> (Option<#cat>, Vec<ParseError>) {
                        match Self::parse_structured(input) {
                            Ok(v) => (Some(v), Vec::new()),
                            Err(e) => (None, vec![e]),
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

/// Returns true if the given nonterminal name is a known literal type (Integer, Boolean, StringLiteral, FloatLiteral).
/// Kept for backward compatibility at string-based call sites.
pub fn is_literal_nonterminal(name: &str) -> bool {
    NonTerminalKind::classify(name).is_literal()
}

/// Checks if a rule is a literal rule (single item, literal NonTerminal).
/// Used for native type handling in theory definitions; all native literal types are treated uniformly.
pub fn is_literal_rule(rule: &GrammarRule) -> bool {
    rule.items.len() == 1 && rule.items[0].is_literal()
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
