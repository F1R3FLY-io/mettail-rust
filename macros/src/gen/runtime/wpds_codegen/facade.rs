//! `parse_<Cat>_via_wpds` facade emission.
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
//! adapter so both engines can run on the same source.
//!
//! ## Recovery
//!
//! TODAY: an outer skip-to-sync retry loop (lines 78-145 below) wraps the
//! walker. On `WpdsState::Error`, the loop advances `pos` past the offending
//! token until a sync delimiter (`)`, `}`, `]`, `;`, `,`) is found, re-seeds
//! the walker, and retries up to MAX_RECOVERY_ROUNDS times.
//!
//! LONG-TERM (tracked as #64 / L12): encode recovery as alternate WPDS
//! edges — Skip / Delete / Substitute / Insert branches fanning out from
//! every PrefixDispatch dead-end, selected by `LexicographicWeight` lex-min.
//! When that lands, this wrapper loop is DELETED and recovery becomes
//! first-class WPDS semantics surfaced via `walker.recovery_trace()`.

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
        let recovering_fn_name = format_ident!("parse_{}_via_wpds_recovering", cat_name);
        let with_weight_fn_name = format_ident!("parse_{}_via_wpds_with_weight", cat_name);
        let cat_src_idx_u16 = cat_src_idx as u16;
        fns.push(quote! {
            /// WPDS-runtime parser for the `#cat_ident` category.
            ///
            /// Runs the walker to saturation and extracts the resulting AST
            /// term via `SemanticBuilder::take_result`. On error, the outer
            /// retry loop attempts up to MAX_RECOVERY_ROUNDS sync-token
            /// skips (see #64 / L12 for the principled WPDS-edge replacement).
            ///
            /// On `ParseFailed`, the returned error carries every recovery
            /// attempt (including the final failure) in `attempts`. For
            /// successful parses where recovery rounds were applied, use
            /// `parse_<Cat>_via_wpds_recovering` to inspect the trail.
            pub fn #fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<#cat_ident, WpdsParseError> {
                let (result, _attempts) = #recovering_fn_name(kinds, texts, pos, min_bp);
                result
            }

            /// L8 (2026-04-28): WPDS parser variant that returns the walker's
            /// terminal weight alongside the parse result. The weight's
            /// `primary` field carries the path's accumulated tropical cost;
            /// `parse_with_confidence` exposes this as a confidence score
            /// `exp(-cost)` ∈ (0, 1].
            ///
            /// Does NOT apply recovery — a clean accept yields
            /// `Ok((term, weight))`; any non-Accepted termination yields
            /// `Err(WpdsParseError)` without retries. Use
            /// `parse_<Cat>_via_wpds_recovering` when sync-token skip
            /// recovery is desired.
            pub fn #with_weight_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                ),
                WpdsParseError,
            > {
                use mettail_prattail::wpds_runtime::WpdsResolveResult;
                use mettail_prattail::wpds_walker::WpdsWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via run_to_end_of_input_env_aware.
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdsWalker::<LexicographicWeight, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let src = mettail_prattail::wpds_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                // Stage 3.5b (2026-05-01): WPDS-correct EOI resolution.
                // `run_to_end_of_input` drives until input exhausted /
                // all-cursors-dead / max_steps; `resolve_at_end_of_input`
                // collapses the parked frontier to a single weighted result
                // via Semiring::plus + lex-min selection.
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, &src) {
                    Ok(()) => match walker.resolve_at_end_of_input(&src) {
                        WpdsResolveResult::Accepted { weight, term }
                        | WpdsResolveResult::AcceptedAmbiguous { weight, term, .. } => {
                            *pos = walker.position();
                            // Stage 3.6 / ι Phase 1 (2026-05-01): term is
                            // `Arc<dyn Any + Send + Sync>` (was `Box<dyn Any + Send>`).
                            // `Arc::downcast` returns `Result<Arc<T>, _>`; we
                            // move out via `Arc::try_unwrap` (zero-copy when
                            // unique) and fall back to `(*arc).clone()` when
                            // the Arc has been cloned for fanout.
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdsParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
                            // The walker's accumulated weight `walker.weight()`
                            // is the lex-min winner's weight after EOI
                            // resolution committed. The resolve result
                            // also returns it; both are consistent.
                            Ok((typed, weight))
                        }
                        WpdsResolveResult::ParseError { message, position } => {
                            Err(WpdsParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdsResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdsParseError::Incomplete { position })
                        }
                    },
                    Err(exceeded) => Err(WpdsParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// WPDS-runtime parser variant that exposes the recovery trail
            /// alongside the parse result. Returns
            /// `(Result<#cat_ident, WpdsParseError>, Vec<RecoveryAttempt>)`:
            /// - `Ok` with empty `attempts`: clean parse, no recovery.
            /// - `Ok` with non-empty `attempts`: parse succeeded after
            ///   one or more sync-token skips; the trail records each.
            /// - `Err(ParseFailed)` with non-empty `attempts`: every retry
            ///   round and the final failure surface in the error's own
            ///   `attempts` vec; the returned vec mirrors that data so
            ///   callers don't need to pattern-match the variant.
            ///
            /// (#64 / L12 will replace the wrapper-level retry loop with
            /// principled WPDS-edge recovery — Skip/Delete/Insert/Substitute
            /// Fork branches at PrefixDispatch dead-ends.)
            pub fn #recovering_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> (Result<#cat_ident, WpdsParseError>, Vec<RecoveryAttempt>) {
                use mettail_prattail::wpds_runtime::WpdsResolveResult;
                use mettail_prattail::wpds_walker::WpdsWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;

                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via run_to_end_of_input_env_aware.
                const MAX_STEPS: usize = 1_000_000;
                const MAX_RECOVERY_ROUNDS: usize = 4;
                const SYNC_TOKENS: &[&str] = &[")", "}", "]", ";", ","];
                let mut attempts: Vec<RecoveryAttempt> = Vec::new();
                let mut recovery_rounds = 0usize;
                let mut start_pos: usize = 0;
                loop {
                    let mut walker = WpdsWalker::<LexicographicWeight, _>::new_for_category(
                        #engine_ident::default(),
                        #cat_src_idx_u16,
                        min_bp,
                    );
                    let kinds_slice: &[mettail_prattail::automata::TokenKind] =
                        &kinds[start_pos..];
                    let texts_slice: &[&str] = &texts[start_pos..];
                    let src = mettail_prattail::wpds_runtime::SliceTokenSource::with_texts(
                        kinds_slice, texts_slice,
                    );
                    // Stage 3.5b (2026-05-01): WPDS-correct EOI resolution.
                    // The wrapper-level recovery loop stays in place
                    // pre-Stage-3.20; ParseError surfaces from
                    // resolve_at_end_of_input and the wrapper retries
                    // from the next sync token.
                    let resolve = match walker.run_to_end_of_input_env_aware(MAX_STEPS, &src) {
                        Ok(()) => walker.resolve_at_end_of_input(&src),
                        Err(exceeded) => {
                            return (
                                Err(WpdsParseError::Incomplete {
                                    position: start_pos + exceeded.position,
                                }),
                                attempts,
                            );
                        }
                    };
                    match resolve {
                        WpdsResolveResult::Accepted { term, .. }
                        | WpdsResolveResult::AcceptedAmbiguous { term, .. } => {
                            *pos = start_pos + walker.position();
                            // Stage 3.6 / ι Phase 1 (2026-05-01): Arc downcast.
                            let result = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdsParseError::EmptyResult);
                            return (result, attempts);
                        }
                        WpdsResolveResult::ParseError { message, position } => {
                            let err_pos = start_pos + position;
                            if recovery_rounds < MAX_RECOVERY_ROUNDS {
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
                                        attempts.push(RecoveryAttempt {
                                            message: message.clone(),
                                            position: err_pos,
                                            recovery: Some(format!(
                                                "skipped to position {}",
                                                new_start,
                                            )),
                                        });
                                        recovery_rounds += 1;
                                        start_pos = new_start;
                                        continue;
                                    }
                                    None => {
                                        attempts.push(RecoveryAttempt {
                                            message: message.clone(),
                                            position: err_pos,
                                            recovery: None,
                                        });
                                        return (
                                            Err(WpdsParseError::ParseFailed {
                                                message,
                                                position: err_pos,
                                                attempts: attempts.clone(),
                                            }),
                                            attempts,
                                        );
                                    }
                                }
                            }
                            attempts.push(RecoveryAttempt {
                                message: message.clone(),
                                position: err_pos,
                                recovery: None,
                            });
                            return (
                                Err(WpdsParseError::ParseFailed {
                                    message,
                                    position: err_pos,
                                    attempts: attempts.clone(),
                                }),
                                attempts,
                            );
                        }
                        WpdsResolveResult::MaxStepsExceeded { position } => {
                            return (
                                Err(WpdsParseError::Incomplete {
                                    position: start_pos + position,
                                }),
                                attempts,
                            );
                        }
                    }
                }
            }
        });
    }
    let _ = language;
    quote! {
        /// One round of WPDS-facade recovery — captures the message that
        /// triggered the round, the token position where it surfaced, and
        /// the sync-token-skip action taken (or `None` if recovery
        /// exhausted without finding a sync token).
        #[derive(Debug, Clone)]
        pub struct RecoveryAttempt {
            /// Diagnostic message from the walker's `WpdsState::Error`.
            pub message: std::string::String,
            /// Token position where the error surfaced.
            pub position: usize,
            /// Skip action taken, or `None` if no sync token was found
            /// (terminating round).
            pub recovery: Option<std::string::String>,
        }

        /// Error returned by `parse_<Cat>_via_wpds` wrappers when the walker
        /// terminates in a non-accepting state.
        ///
        /// `ParseFailed` carries the final-error fields plus the full
        /// recovery-attempt trail, so consumers don't need to re-run the
        /// recovering variant to inspect what was tried.
        #[derive(Debug, Clone)]
        pub enum WpdsParseError {
            /// Walker accepted, but the builder's term stack was empty —
            /// indicates a codegen bug (every successful parse should push
            /// exactly one term).
            EmptyResult,
            /// Walker entered `WpdsState::Error` with a diagnostic message.
            /// `attempts` records every recovery round (including the
            /// terminating one).
            ParseFailed {
                message: std::string::String,
                position: usize,
                attempts: Vec<RecoveryAttempt>,
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
                    WpdsParseError::ParseFailed { message, position, attempts } => {
                        if attempts.len() <= 1 {
                            write!(f, "wpds parse failed at position {}: {}", position, message)
                        } else {
                            write!(
                                f,
                                "wpds parse failed at position {}: {} ({} recovery rounds)",
                                position,
                                message,
                                attempts.len(),
                            )
                        }
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
