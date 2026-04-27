//! `parse_<Cat>_via_wpds` facade emission (Phase 2 + Phase A.9).
//!
//! Emits per-category wrapper functions that drive the WPDS walker to
//! saturation on a `TokenKind` slice and extract the resulting AST term.
//!
//! ## Signature
//!
//! ```ignore
//! pub fn parse_<Cat>_via_wpds(
//!     kinds: &[TokenKind],
//!     texts: &[&str],
//!     pos: &mut usize,
//!     min_bp: u8,
//! ) -> Result<<Cat>, WpdsParseError>
//! ```
//!
//! The caller is responsible for tokenizing the source input. Parity-test
//! harnesses (`test_gen/parity.rs`) provide a per-grammar `Token → TokenKind`
//! adapter so both engines can run on the same source — see Phase 2 notes
//! in `/home/dylon/.claude/plans/help-me-complete-the-sleepy-cocoa.md`.
//!
//! ## 📌 Long-term recovery note (mandate #8)
//!
//! On `WpdsState::Error`, this facade currently returns an error shape.
//! Phase A.9 wires `mettail_prattail::recovery::find_best_recovery` at the
//! wrapper level with `SYNC_TOKENS_<CAT>` emitted from the category's
//! FOLLOW set. The endgame is to encode recovery as alternate WPDS edges
//! (Skip / Delete / Substitute / Insert rules fanning out from every
//! prefix-dispatch state, selected by `LexicographicWeight` lex-min).
//! When that lands, the wrapper-level recovery plumbing is deleted and
//! recovery becomes first-class WPDS semantics.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Emit per-category `parse_<Cat>_via_wpds` wrappers plus the shared
/// `WpdsParseError` type.
pub(crate) fn emit_parse_fns(
    language: &LanguageDef,
    categories: &[String],
    engine_ident: &proc_macro2::Ident,
) -> TokenStream {
    let mut fns = Vec::new();
    for (cat_src_idx, cat_name) in categories.iter().enumerate() {
        let cat_ident = format_ident!("{}", cat_name);
        let fn_name = format_ident!("parse_{}_via_wpds", cat_name);
        let cat_src_idx_u16 = cat_src_idx as u16;
        fns.push(quote! {
            /// WPDS-runtime parser for the `#cat_ident` category.
            ///
            /// Runs the walker to saturation and extracts the resulting AST
            /// term via `SemanticBuilder::take_result`. On error, returns
            /// `WpdsParseError` — Phase A.9 will add WFST recovery here.
            pub fn #fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<#cat_ident, WpdsParseError> {
                use mettail_prattail::wpds_runtime::{
                    SliceTokenSource, WpdsState,
                };
                use mettail_prattail::wpds_walker::WpdsWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;

                let src = SliceTokenSource::with_texts(kinds, texts);
                // Seed the walker at this category's src_idx (not the
                // primary) so the PrefixDispatch arm guards on the
                // correct `state_cat_src_idx`.
                let mut walker = WpdsWalker::<LexicographicWeight, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                const MAX_STEPS: usize = 1_000_000;
                // Phase 8: outer retry loop wraps the walker. On Error,
                // attempt one round of skip-to-sync recovery (advance pos
                // past the offending token until a sync delimiter is
                // found), then re-seed the walker and retry. Failed
                // recovery surfaces ParseFailed.
                const MAX_RECOVERY_ROUNDS: usize = 4;
                const SYNC_TOKENS: &[&str] = &[")", "}", "]", ";", ","];
                let mut recovery_rounds = 0usize;
                let mut start_pos: usize = 0;
                loop {
                    let mut walker = WpdsWalker::<LexicographicWeight, _>::new_for_category(
                        #engine_ident::default(),
                        #cat_src_idx_u16,
                        min_bp,
                    );
                    // Walker starts at position 0 of the *adjusted* token slice;
                    // for the recovery retry we logically advance start_pos
                    // and reset MAX_STEPS.
                    let kinds_slice: &[mettail_prattail::automata::TokenKind] =
                        &kinds[start_pos..];
                    let texts_slice: &[&str] = &texts[start_pos..];
                    let src = mettail_prattail::wpds_runtime::SliceTokenSource::with_texts(
                        kinds_slice, texts_slice,
                    );
                    match walker.run_to_saturation(MAX_STEPS, &src) {
                        WpdsState::Accepted => {
                            *pos = start_pos + walker.position();
                            return walker
                                .builder_mut()
                                .take_result::<#cat_ident>()
                                .ok_or(WpdsParseError::EmptyResult);
                        }
                        WpdsState::Error { message } => {
                            if recovery_rounds < MAX_RECOVERY_ROUNDS {
                                let err_pos = start_pos + walker.position();
                                // Find the next sync token text after err_pos.
                                let mut next_sync: Option<usize> = None;
                                for i in (err_pos + 1)..kinds.len() {
                                    let text = texts.get(i).copied().unwrap_or("");
                                    if SYNC_TOKENS.iter().any(|s| *s == text) {
                                        next_sync = Some(i + 1);
                                        break;
                                    }
                                }
                                match next_sync {
                                    Some(new_start) => {
                                        recovery_rounds += 1;
                                        start_pos = new_start;
                                        continue;
                                    }
                                    None => {
                                        return Err(WpdsParseError::ParseFailed {
                                            message,
                                            position: err_pos,
                                        });
                                    }
                                }
                            }
                            return Err(WpdsParseError::ParseFailed {
                                message,
                                position: start_pos + walker.position(),
                            });
                        }
                        _ => {
                            return Err(WpdsParseError::Incomplete {
                                position: start_pos + walker.position(),
                            });
                        }
                    }
                }
            }
        });
    }
    let _ = language;
    quote! {
        /// Error returned by `parse_<Cat>_via_wpds` wrappers when the walker
        /// terminates in a non-accepting state.
        #[derive(Debug, Clone)]
        pub enum WpdsParseError {
            /// Walker accepted, but the builder's term stack was empty —
            /// indicates a codegen bug (every successful parse should push
            /// exactly one term).
            EmptyResult,
            /// Walker entered `WpdsState::Error` with a diagnostic message.
            ParseFailed {
                message: std::string::String,
                position: usize,
            },
            /// Walker reached step budget without terminating.
            Incomplete {
                position: usize,
            },
        }

        impl std::fmt::Display for WpdsParseError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    WpdsParseError::EmptyResult => {
                        write!(f, "wpds parser produced no result")
                    }
                    WpdsParseError::ParseFailed { message, position } => {
                        write!(f, "wpds parse failed at position {}: {}", position, message)
                    }
                    WpdsParseError::Incomplete { position } => {
                        write!(f, "wpds parse incomplete at position {}", position)
                    }
                }
            }
        }

        impl std::error::Error for WpdsParseError {}

        #(#fns)*
    }
}
