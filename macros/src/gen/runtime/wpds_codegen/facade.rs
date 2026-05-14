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
                        WpdsResolveResult::Accepted { weights, terms } => {
                            *pos = walker.position();
                            // M7c (2026-05-13): WpdsResolveResult::Accepted
                            // is now multi-result. For backward compat,
                            // pick the FIRST term (M8 will introduce
                            // AmbiguousResult<Cat> for proper multi-result
                            // return).
                            let term = terms
                                .into_iter()
                                .next()
                                .ok_or(WpdsParseError::EmptyResult)?;
                            let weight = weights
                                .into_iter()
                                .next()
                                .ok_or(WpdsParseError::EmptyResult)?;
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdsParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
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
            /// - `Ok` with non-empty `attempts`: parse succeeded but the
            ///   walker dispatched recovery one or more times along the
            ///   way; the trail records each recovery action that the
            ///   lex-min winner committed.
            /// - `Err(ParseFailed)` with non-empty `attempts`: walker
            ///   exhausted all bounded recovery dispatches without
            ///   finding an accepting derivation; the trail records every
            ///   recovery action attempted before failure.
            ///
            /// Stage 3.20 / L12 (Commit E, 2026-05-06): the legacy
            /// wrapper-level skip-to-sync retry loop has been deleted.
            /// Recovery is now intrinsic to the walker via
            /// `recovery_dispatch::emit_recovery_fork`, bounded by
            /// `RecoveryConfig.max_recovery_depth` (default 3) and the
            /// per-cursor `visited_recovery` cycle defense. Each
            /// `RecoveryEvent` the walker logs becomes one
            /// `RecoveryAttempt` in the returned trail.
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
                let mut walker = WpdsWalker::<LexicographicWeight, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let src = mettail_prattail::wpds_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                let resolve = match walker.run_to_end_of_input_env_aware(MAX_STEPS, &src) {
                    Ok(()) => walker.resolve_at_end_of_input(&src),
                    Err(exceeded) => {
                        return (
                            Err(WpdsParseError::Incomplete {
                                position: exceeded.position,
                            }),
                            Vec::new(),
                        );
                    }
                };
                // Stage 3.20 / L12 (Commit E, 2026-05-06): map walker's
                // recovery_trace into RecoveryAttempt for the public API.
                // Each RecoveryEvent the lex-min winner committed appears
                // in the trace; the action_kind discriminator + position
                // + token text describe what the walker did.
                let attempts: Vec<RecoveryAttempt> = walker
                    .recovery_trace()
                    .iter()
                    .map(|ev| RecoveryAttempt {
                        message: format!(
                            "recovery action_kind={} cost={:.3}",
                            ev.action_kind, ev.cost_tropical,
                        ),
                        position: ev.pos,
                        recovery: match ev.action_kind {
                            0 => Some("skip-to-sync".into()),
                            1 => Some("delete-token".into()),
                            2 => Some(format!(
                                "insert-token {:?}",
                                ev.text.as_deref().unwrap_or(""),
                            )),
                            3 => Some(format!(
                                "substitute-token {:?}",
                                ev.text.as_deref().unwrap_or(""),
                            )),
                            5 => Some("composite-recovery".into()),
                            7 => Some(format!(
                                "lex-alternative idx={}",
                                ev.alt_idx.unwrap_or(0),
                            )),
                            _ => None,
                        },
                    })
                    .collect();
                match resolve {
                    WpdsResolveResult::Accepted { terms, .. } => {
                        *pos = walker.position();
                        // M7c (2026-05-13): pick the first term for
                        // backward-compat (M8 returns AmbiguousResult).
                        let result = match terms.into_iter().next() {
                            Some(term) => std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdsParseError::EmptyResult),
                            None => Err(WpdsParseError::EmptyResult),
                        };
                        (result, attempts)
                    }
                    WpdsResolveResult::ParseError { message, position } => {
                        let err = WpdsParseError::ParseFailed {
                            message,
                            position,
                            attempts: attempts.clone(),
                        };
                        (Err(err), attempts)
                    }
                    WpdsResolveResult::MaxStepsExceeded { position } => {
                        (Err(WpdsParseError::Incomplete { position }), attempts)
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
