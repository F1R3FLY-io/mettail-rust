//! `parse_<Cat>_via_wpda` facade emission.
//!
//! Emits per-category wrapper functions that drive the WPDS walker to
//! saturation on a `TokenKind` slice and extract the resulting AST term.
//!
//! ## Signature
//!
//! ```ignore
//! pub fn parse_<Cat>_via_wpda(
//!     kinds: &[TokenKind],
//!     texts: &[&str],
//!     pos: &mut usize,
//!     min_bp: u8,
//! ) -> Result<<Cat>, WpdaParseError>
//! ```
//!
//! The caller is responsible for tokenizing the source input. Parity-test
//! harnesses (`test_gen/parity.rs`) provide a per-grammar `Token → TokenKind`
//! adapter so both engines can run on the same source.
//!
//! ## Recovery
//!
//! Strict parse entry points disable recovery by setting
//! `RecoveryConfig.max_recovery_depth = 0`. The explicit
//! `parse_<Cat>_via_wpda_recovering` entry point keeps the walker's default
//! recovery config and returns the committed recovery trail.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Emit per-category `parse_<Cat>_via_wpda` wrappers plus the shared
/// `WpdaParseError` type.
pub(crate) fn emit_parse_fns(
    language: &LanguageDef,
    categories: &[String],
    engine_ident: &proc_macro2::Ident,
) -> TokenStream {
    let mut fns = Vec::new();
    for (cat_src_idx, cat_name) in categories.iter().enumerate() {
        let cat_ident = format_ident!("{}", cat_name);
        let fn_name = format_ident!("parse_{}_via_wpda", cat_name);
        let recovering_fn_name = format_ident!("parse_{}_via_wpda_recovering", cat_name);
        let with_weight_fn_name = format_ident!("parse_{}_via_wpda_with_weight", cat_name);
        let with_source_fn_name = format_ident!("parse_{}_via_wpda_with_source", cat_name);
        // M8 (2026-05-14): multi-result entry points. `_all_with_source`
        // takes `&dyn WpdaTokenSource` (slice OR lattice) and returns
        // every accepted term from the walker's `WpdaResolveResult::Accepted`
        // vec. `_all` is a `SliceTokenSource` wrapper for backward compat.
        let all_with_source_fn_name = format_ident!("parse_{}_via_wpda_all_with_source", cat_name);
        let all_with_source_bounded_fn_name =
            format_ident!("parse_{}_via_wpda_all_with_source_and_bounding_mode", cat_name);
        let prefix_with_source_fn_name =
            format_ident!("parse_{}_via_wpda_prefix_with_source", cat_name);
        let prefix_with_source_bounded_fn_name =
            format_ident!("parse_{}_via_wpda_prefix_with_source_and_bounding_mode", cat_name);
        let prefix_fn_name = format_ident!("parse_{}_via_wpda_prefix", cat_name);
        let all_fn_name = format_ident!("parse_{}_via_wpda_all", cat_name);
        let cat_src_idx_u16 = cat_src_idx as u16;
        fns.push(quote! {
            /// WPDS-runtime parser for the `#cat_ident` category.
            ///
            /// Runs the walker to saturation and extracts the resulting AST
            /// term with recovery disabled. Use
            /// `parse_<Cat>_via_wpda_recovering` when repair attempts should
            /// be part of the result surface.
            #[allow(non_snake_case)]
            pub fn #fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<#cat_ident, WpdaParseError> {
                #with_weight_fn_name(kinds, texts, pos, min_bp).map(|(term, _)| term)
            }

            /// Source-generic WPDS parser variant that returns the walker's
            /// terminal weight alongside the parse result.
            ///
            /// Does NOT apply recovery — a clean accept yields
            /// `Ok((term, weight))`; any non-Accepted termination yields
            /// `Err(WpdaParseError)` without retries. Use
            /// `parse_<Cat>_via_wpda_recovering` when sync-token skip
            /// recovery is desired.
            #[allow(non_snake_case)]
            pub fn #with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    #cat_ident,
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                // Phase 3.1.7 (C10, 2026-05-15): walker W reverted from
                // M11's DerivationWeight<...> multiset to plain
                // LexicographicWeight. The SPPF arena carries derivation
                // ambiguity (Tomita 1986 §6.3 / Scott-Johnstone 2010 §3 —
                // SPPF is a set of derivations with structural dedup);
                // W carries only the cursor-merge path-cost tiebreak.
                // Public return type reverts to (Cat, LexicographicWeight)
                // — the M11.6b D5 break is undone.
                use mettail_prattail::automata::semiring::SemiringRef;
                type DW = LexicographicWeight;
                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via run_to_end_of_input_env_aware.
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { weights, roots, .. } => {
                            *pos = walker.position();
                            // C7b (Phase 3.1.6, 2026-05-15): realize the
                            // first SPPF root. Packing-fanout produces ALL
                            // derivations of the root Symbol; here we take
                            // the first for backward-compat single-result
                            // return. Callers wanting all derivations should
                            // use `parse_<Cat>_via_wpda_all_with_source`.
                            let root = roots
                                .first()
                                .copied()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let term = walker
                                .realize_root_to_terms(root, Some(1))
                                .into_iter()
                                .next()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let dw = weights
                                .into_iter()
                                .next()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdaParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
                            Ok((typed, dw))
                        }
                        // Cluster H (2026-05-29): valid-prefix parse with
                        // trailing tokens. Return the prefix term + weight
                        // and set `*pos` to the prefix boundary so the
                        // generated wrapper's `pos < tokens.len()` check
                        // emits a structured `TrailingTokens` error.
                        WpdaResolveResult::AcceptedWithTrailing {
                            weights, roots, position, ..
                        } => {
                            *pos = position;
                            let root = roots
                                .first()
                                .copied()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let term = walker
                                .realize_root_to_terms(root, Some(1))
                                .into_iter()
                                .next()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let dw = weights
                                .into_iter()
                                .next()
                                .ok_or(WpdaParseError::EmptyResult)?;
                            let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                .map_err(|_| WpdaParseError::EmptyResult)?;
                            let typed = std::sync::Arc::try_unwrap(arc)
                                .unwrap_or_else(|arc| (*arc).clone());
                            Ok((typed, dw))
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// L8 (2026-04-28): WPDS parser variant that returns the walker's
            /// terminal weight alongside the parse result. The weight's
            /// `primary` field carries the path's accumulated tropical cost;
            /// `parse_with_confidence` exposes this as a confidence score
            /// `exp(-cost)` ∈ (0, 1].
            ///
            /// This slice wrapper preserves the existing public ABI; callers
            /// that need lexical alternatives use `parse_<Cat>_via_wpda_with_source`
            /// with a `LatticeTokenSource`.
            #[allow(non_snake_case)]
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
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #with_source_fn_name(&src, pos, min_bp)
            }

            /// M8 (2026-05-14): multi-result WPDS parser that takes any
            /// `WpdaTokenSource` impl (slice OR lattice). Returns every
            /// term the walker's `WpdaResolveResult::Accepted` carries —
            /// the ambiguity-preserving final state. Use this when you
            /// need to surface ALL parses for downstream disambiguation
            /// at the eval layer (run_ascent_typed's Ambiguous-flatten),
            /// or via `Cat::parse_all`.
            ///
            /// `parse_<Cat>_via_wpda_all_with_source` is the source-generic
            /// entry; `parse_<Cat>_via_wpda_all` wraps it with a
            /// `SliceTokenSource` for slice callers.
            ///
            /// Does NOT apply recovery — a clean accept yields
            /// `Ok((terms, weights))`; non-Accepted termination yields
            /// `Err(WpdaParseError)`.
            #[allow(non_snake_case)]
            pub fn #all_with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                #all_with_source_bounded_fn_name(
                    source,
                    pos,
                    min_bp,
                    mettail_prattail::wpda_runtime::CursorBoundingMode::Unbounded,
                )
            }

            /// Source-generic bounded-prefix parser. Returns at most
            /// `max_alternatives` distinct semantic alternatives in the
            /// same weight-ordered surface shape as `parse_<Cat>_via_wpda_all`.
            ///
            /// This is a demand-bounded API: it asks each accepted SPPF
            /// root only for the raw realization prefix needed to satisfy
            /// the requested semantic prefix, growing the raw probe only
            /// when duplicate semantic realizations consume that demand.
            /// It does not call the eager all-results facade internally.
            #[allow(non_snake_case)]
            pub fn #prefix_with_source_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                #prefix_with_source_bounded_fn_name(
                    source,
                    pos,
                    min_bp,
                    max_alternatives,
                    mettail_prattail::wpda_runtime::CursorBoundingMode::Unbounded,
                )
            }

            /// Source-generic bounded-prefix parser with explicit
            /// cursor-frontier bounding. The cursor budget reports
            /// structured `AmbiguityBudget` overflow without pruning; the
            /// `max_alternatives` demand only limits how many semantic
            /// alternatives are realized for this call.
            #[allow(non_snake_case)]
            pub fn #prefix_with_source_bounded_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
                bounding_mode: mettail_prattail::wpda_runtime::CursorBoundingMode,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use std::collections::HashMap;
                type DW = LexicographicWeight;
                #[derive(Default)]
                struct __MettailWpdaSemanticKeyHasher {
                    bytes: Vec<u8>,
                }
                impl __MettailWpdaSemanticKeyHasher {
                    fn into_key(self) -> Vec<u8> {
                        self.bytes
                    }
                    fn push_raw(&mut self, tag: u8, payload: &[u8]) {
                        self.bytes.push(tag);
                        self.bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
                        self.bytes.extend_from_slice(payload);
                    }
                    fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
                        self.bytes.push(tag);
                        self.bytes.extend_from_slice(payload);
                    }
                }
                impl std::hash::Hasher for __MettailWpdaSemanticKeyHasher {
                    fn finish(&self) -> u64 {
                        let mut h = 0xcbf29ce484222325u64;
                        for b in &self.bytes {
                            h ^= *b as u64;
                            h = h.wrapping_mul(0x100000001b3);
                        }
                        h
                    }
                    fn write(&mut self, bytes: &[u8]) {
                        self.push_raw(0, bytes);
                    }
                    fn write_u8(&mut self, i: u8) {
                        self.push_fixed(1, &[i]);
                    }
                    fn write_u16(&mut self, i: u16) {
                        self.push_fixed(2, &i.to_le_bytes());
                    }
                    fn write_u32(&mut self, i: u32) {
                        self.push_fixed(3, &i.to_le_bytes());
                    }
                    fn write_u64(&mut self, i: u64) {
                        self.push_fixed(4, &i.to_le_bytes());
                    }
                    fn write_u128(&mut self, i: u128) {
                        self.push_fixed(5, &i.to_le_bytes());
                    }
                    fn write_usize(&mut self, i: usize) {
                        self.push_fixed(6, &(i as u128).to_le_bytes());
                    }
                    fn write_i8(&mut self, i: i8) {
                        self.push_fixed(7, &i.to_le_bytes());
                    }
                    fn write_i16(&mut self, i: i16) {
                        self.push_fixed(8, &i.to_le_bytes());
                    }
                    fn write_i32(&mut self, i: i32) {
                        self.push_fixed(9, &i.to_le_bytes());
                    }
                    fn write_i64(&mut self, i: i64) {
                        self.push_fixed(10, &i.to_le_bytes());
                    }
                    fn write_i128(&mut self, i: i128) {
                        self.push_fixed(11, &i.to_le_bytes());
                    }
                    fn write_isize(&mut self, i: isize) {
                        self.push_fixed(12, &(i as i128).to_le_bytes());
                    }
                }
                fn __mettail_wpda_semantic_key(term: &#cat_ident) -> Vec<u8> {
                    let mut hasher = __MettailWpdaSemanticKeyHasher::default();
                    term.semantic_hash(&mut hasher);
                    hasher.into_key()
                }
                fn __mettail_wpda_collect_prefix(
                    walker: &WpdaWalker<DW, #engine_ident>,
                    roots: &[mettail_prattail::sppf::SppfId],
                    max_alternatives: usize,
                    position: usize,
                ) -> Result<
                    (
                        Vec<#cat_ident>,
                        Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                    ),
                    WpdaParseError,
                > {
                    if max_alternatives == 0 {
                        return Ok((Vec::new(), Vec::new()));
                    }
                    const RAW_PREFIX_CAP: usize = 4096;
                    let mut raw_probe_limit = max_alternatives.saturating_add(1).max(1);
                    loop {
                        let mut typed_terms: Vec<#cat_ident> = Vec::new();
                        let mut typed_weights:
                            Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                            Vec::new();
                        let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                        let mut exhausted_all_roots = true;
                        for &root in roots {
                            let realized = walker.realize_root_to_terms_with_weights(
                                root,
                                Some(raw_probe_limit),
                            );
                            if realized.len() >= raw_probe_limit {
                                exhausted_all_roots = false;
                            }
                            for (term, weight) in realized {
                                let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                    .map_err(|_| WpdaParseError::EmptyResult)?;
                                let typed = std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone());
                                let semantic_key = __mettail_wpda_semantic_key(&typed);
                                if let Some(existing_idx) =
                                    seen_terms.get(&semantic_key).copied()
                                {
                                    if weight < typed_weights[existing_idx] {
                                        typed_terms[existing_idx] = typed;
                                        typed_weights[existing_idx] = weight;
                                    }
                                    continue;
                                }
                                seen_terms.insert(semantic_key, typed_terms.len());
                                typed_terms.push(typed);
                                typed_weights.push(weight);
                            }
                        }
                        let mut paired: Vec<_> =
                            typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                        paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                        if paired.len() > max_alternatives {
                            paired.truncate(max_alternatives);
                        }
                        if paired.len() >= max_alternatives || exhausted_all_roots {
                            if paired.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            return Ok((typed_terms, typed_weights));
                        }
                        if raw_probe_limit >= RAW_PREFIX_CAP {
                            return Err(WpdaParseError::AmbiguityBudget {
                                budget: RAW_PREFIX_CAP,
                                actual: RAW_PREFIX_CAP + 1,
                                position,
                            });
                        }
                        raw_probe_limit =
                            raw_probe_limit.saturating_mul(2).min(RAW_PREFIX_CAP);
                    }
                }
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                walker.set_bounding_mode(bounding_mode);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            let completion_position = walker.position();
                            *pos = completion_position;
                            __mettail_wpda_collect_prefix(
                                &walker,
                                &roots,
                                max_alternatives,
                                completion_position,
                            )
                        }
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots, position, ..
                        } => {
                            *pos = position;
                            __mettail_wpda_collect_prefix(
                                &walker,
                                &roots,
                                max_alternatives,
                                position,
                            )
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// Slice-source convenience wrapper for bounded-prefix parsing.
            #[allow(non_snake_case)]
            pub fn #prefix_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
                max_alternatives: usize,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #prefix_with_source_fn_name(&src, pos, min_bp, max_alternatives)
            }

            /// Source-generic all-results parser with explicit cursor-frontier
            /// bounding. The default all-results facade calls this with
            /// `CursorBoundingMode::Unbounded`; callers should pass an
            /// explicit bounded mode only when they want a structured
            /// `AmbiguityBudget` error instead of an unbounded ambiguity
            /// surface.
            #[allow(non_snake_case)]
            pub fn #all_with_source_bounded_fn_name(
                source: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                pos: &mut usize,
                min_bp: u8,
                bounding_mode: mettail_prattail::wpda_runtime::CursorBoundingMode,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use std::collections::HashMap;
                // Phase 3.1.7 (C10, 2026-05-15): walker W = LexicographicWeight.
                // SPPF arena owns derivation ambiguity; W owns path cost.
                type DW = LexicographicWeight;
                #[derive(Default)]
                struct __MettailWpdaSemanticKeyHasher {
                    bytes: Vec<u8>,
                }
                impl __MettailWpdaSemanticKeyHasher {
                    fn into_key(self) -> Vec<u8> {
                        self.bytes
                    }
                    fn push_raw(&mut self, tag: u8, payload: &[u8]) {
                        self.bytes.push(tag);
                        self.bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
                        self.bytes.extend_from_slice(payload);
                    }
                    fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
                        self.bytes.push(tag);
                        self.bytes.extend_from_slice(payload);
                    }
                }
                impl std::hash::Hasher for __MettailWpdaSemanticKeyHasher {
                    fn finish(&self) -> u64 {
                        let mut h = 0xcbf29ce484222325u64;
                        for b in &self.bytes {
                            h ^= *b as u64;
                            h = h.wrapping_mul(0x100000001b3);
                        }
                        h
                    }
                    fn write(&mut self, bytes: &[u8]) {
                        self.push_raw(0, bytes);
                    }
                    fn write_u8(&mut self, i: u8) {
                        self.push_fixed(1, &[i]);
                    }
                    fn write_u16(&mut self, i: u16) {
                        self.push_fixed(2, &i.to_le_bytes());
                    }
                    fn write_u32(&mut self, i: u32) {
                        self.push_fixed(3, &i.to_le_bytes());
                    }
                    fn write_u64(&mut self, i: u64) {
                        self.push_fixed(4, &i.to_le_bytes());
                    }
                    fn write_u128(&mut self, i: u128) {
                        self.push_fixed(5, &i.to_le_bytes());
                    }
                    fn write_usize(&mut self, i: usize) {
                        self.push_fixed(6, &(i as u128).to_le_bytes());
                    }
                    fn write_i8(&mut self, i: i8) {
                        self.push_fixed(7, &i.to_le_bytes());
                    }
                    fn write_i16(&mut self, i: i16) {
                        self.push_fixed(8, &i.to_le_bytes());
                    }
                    fn write_i32(&mut self, i: i32) {
                        self.push_fixed(9, &i.to_le_bytes());
                    }
                    fn write_i64(&mut self, i: i64) {
                        self.push_fixed(10, &i.to_le_bytes());
                    }
                    fn write_i128(&mut self, i: i128) {
                        self.push_fixed(11, &i.to_le_bytes());
                    }
                    fn write_isize(&mut self, i: isize) {
                        self.push_fixed(12, &(i as i128).to_le_bytes());
                    }
                }
                fn __mettail_wpda_semantic_key(term: &#cat_ident) -> Vec<u8> {
                    let mut hasher = __MettailWpdaSemanticKeyHasher::default();
                    term.semantic_hash(&mut hasher);
                    hasher.into_key()
                }
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut recovery_config = mettail_prattail::recovery::RecoveryConfig::default();
                recovery_config.max_recovery_depth = 0;
                walker.set_recovery_config(recovery_config);
                walker.set_bounding_mode(bounding_mode);
                match walker.run_to_end_of_input_env_aware(MAX_STEPS, source) {
                    Ok(()) => match walker.resolve_at_end_of_input(source) {
                        WpdaResolveResult::Accepted { roots, .. } => {
                            // C7b (Phase 3.1.6, 2026-05-15): realize all
                            // SPPF roots; packing-fanout produces the
                            // ambiguity-preserving Vec<Cat>. The public cap
                            // is applied to DISTINCT semantic alternatives:
                            // raw duplicate derivations update the retained
                            // representative's best weight rather than
                            // consuming the ambiguity budget before language
                            // construction can quotient them.
                            const REALIZE_CAP: usize = 64;
                            const RAW_REALIZE_CAP: usize = 4096;
                            let completion_position = walker.position();
                            *pos = completion_position;
                            let mut typed_terms: Vec<#cat_ident> = Vec::new();
                            let mut typed_weights:
                                Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                                Vec::new();
                            let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                            let mut overflowed_realization = false;
                            let mut raw_realization_exhausted_budget = false;
                            for &root in &roots {
                                let mut raw_probe_limit = REALIZE_CAP.saturating_add(1);
                                loop {
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                    );
                                    let exhausted_root = realized.len() < raw_probe_limit;
                                    for (term, weight) in realized {
                                        let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                            .map_err(|_| WpdaParseError::EmptyResult)?;
                                        let typed = std::sync::Arc::try_unwrap(arc)
                                            .unwrap_or_else(|arc| (*arc).clone());
                                        let semantic_key = __mettail_wpda_semantic_key(&typed);
                                        if let Some(existing_idx) =
                                            seen_terms.get(&semantic_key).copied()
                                        {
                                            if weight < typed_weights[existing_idx] {
                                                typed_terms[existing_idx] = typed;
                                                typed_weights[existing_idx] = weight;
                                            }
                                            continue;
                                        }
                                        if typed_terms.len() >= REALIZE_CAP {
                                            overflowed_realization = true;
                                            break;
                                        }
                                        seen_terms.insert(semantic_key, typed_terms.len());
                                        typed_terms.push(typed);
                                        typed_weights.push(weight);
                                    }
                                    if overflowed_realization || exhausted_root {
                                        break;
                                    }
                                    if raw_probe_limit >= RAW_REALIZE_CAP {
                                        raw_realization_exhausted_budget = true;
                                        break;
                                    }
                                    raw_probe_limit =
                                        raw_probe_limit.saturating_mul(2).min(RAW_REALIZE_CAP);
                                }
                                if overflowed_realization || raw_realization_exhausted_budget {
                                    break;
                                }
                            }
                            if raw_realization_exhausted_budget {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: RAW_REALIZE_CAP,
                                    actual: RAW_REALIZE_CAP + 1,
                                    position: completion_position,
                                });
                            }
                            if overflowed_realization {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: REALIZE_CAP,
                                    actual: REALIZE_CAP + 1,
                                    position: completion_position,
                                });
                            }
                            if typed_terms.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let mut paired: Vec<_> =
                                typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                            paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            Ok((typed_terms, typed_weights))
                        }
                        // Cluster H (2026-05-29): valid-prefix parse with
                        // trailing tokens. Realize ALL prefix derivations
                        // (ambiguity-preserving) and set `*pos` to the
                        // prefix boundary so the caller's trailing check
                        // (`pos < eof_node`) surfaces `TrailingTokens`.
                        WpdaResolveResult::AcceptedWithTrailing {
                            roots, position, ..
                        } => {
                            *pos = position;
                            const REALIZE_CAP: usize = 64;
                            const RAW_REALIZE_CAP: usize = 4096;
                            let mut typed_terms: Vec<#cat_ident> = Vec::new();
                            let mut typed_weights:
                                Vec<mettail_prattail::automata::lex_weight::LexicographicWeight> =
                                Vec::new();
                            let mut seen_terms: HashMap<Vec<u8>, usize> = HashMap::new();
                            let mut overflowed_realization = false;
                            let mut raw_realization_exhausted_budget = false;
                            for &root in &roots {
                                let mut raw_probe_limit = REALIZE_CAP.saturating_add(1);
                                loop {
                                    let realized = walker.realize_root_to_terms_with_weights(
                                        root,
                                        Some(raw_probe_limit),
                                    );
                                    let exhausted_root = realized.len() < raw_probe_limit;
                                    for (term, weight) in realized {
                                        let arc = std::sync::Arc::downcast::<#cat_ident>(term)
                                            .map_err(|_| WpdaParseError::EmptyResult)?;
                                        let typed = std::sync::Arc::try_unwrap(arc)
                                            .unwrap_or_else(|arc| (*arc).clone());
                                        let semantic_key = __mettail_wpda_semantic_key(&typed);
                                        if let Some(existing_idx) =
                                            seen_terms.get(&semantic_key).copied()
                                        {
                                            if weight < typed_weights[existing_idx] {
                                                typed_terms[existing_idx] = typed;
                                                typed_weights[existing_idx] = weight;
                                            }
                                            continue;
                                        }
                                        if typed_terms.len() >= REALIZE_CAP {
                                            overflowed_realization = true;
                                            break;
                                        }
                                        seen_terms.insert(semantic_key, typed_terms.len());
                                        typed_terms.push(typed);
                                        typed_weights.push(weight);
                                    }
                                    if overflowed_realization || exhausted_root {
                                        break;
                                    }
                                    if raw_probe_limit >= RAW_REALIZE_CAP {
                                        raw_realization_exhausted_budget = true;
                                        break;
                                    }
                                    raw_probe_limit =
                                        raw_probe_limit.saturating_mul(2).min(RAW_REALIZE_CAP);
                                }
                                if overflowed_realization || raw_realization_exhausted_budget {
                                    break;
                                }
                            }
                            if raw_realization_exhausted_budget {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: RAW_REALIZE_CAP,
                                    actual: RAW_REALIZE_CAP + 1,
                                    position,
                                });
                            }
                            if overflowed_realization {
                                return Err(WpdaParseError::AmbiguityBudget {
                                    budget: REALIZE_CAP,
                                    actual: REALIZE_CAP + 1,
                                    position,
                                });
                            }
                            if typed_terms.is_empty() {
                                return Err(WpdaParseError::EmptyResult);
                            }
                            let mut paired: Vec<_> =
                                typed_terms.into_iter().zip(typed_weights.into_iter()).collect();
                            paired.sort_by(|(_, a), (_, b)| a.cmp(b));
                            let (typed_terms, typed_weights): (Vec<_>, Vec<_>) =
                                paired.into_iter().unzip();
                            Ok((typed_terms, typed_weights))
                        }
                        WpdaResolveResult::ParseError { message, position } => {
                            Err(WpdaParseError::ParseFailed {
                                message,
                                position,
                                attempts: Vec::new(),
                            })
                        }
                        WpdaResolveResult::MaxStepsExceeded { position } => {
                            Err(WpdaParseError::Incomplete { position })
                        }
                        WpdaResolveResult::AmbiguityBudget { budget, actual, position } => {
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position })
                        }
                    },
                    Err(exceeded) => Err(WpdaParseError::Incomplete {
                        position: exceeded.position,
                    }),
                }
            }

            /// M8 wrapper: slice-source convenience for callers that
            /// already have `kinds` + `texts` Vecs. Routes through
            /// `parse_<Cat>_via_wpda_all_with_source` with a
            /// `SliceTokenSource`.
            #[allow(non_snake_case)]
            pub fn #all_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> Result<
                (
                    Vec<#cat_ident>,
                    Vec<mettail_prattail::automata::lex_weight::LexicographicWeight>,
                ),
                WpdaParseError,
            > {
                let src = mettail_prattail::wpda_runtime::SliceTokenSource::with_texts(
                    kinds, texts,
                );
                #all_with_source_fn_name(&src, pos, min_bp)
            }

            /// WPDS-runtime parser variant that exposes the recovery trail
            /// alongside the parse result. Returns
            /// `(Result<#cat_ident, WpdaParseError>, Vec<RecoveryAttempt>)`:
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
            #[allow(non_snake_case)]
            pub fn #recovering_fn_name(
                kinds: &[mettail_prattail::automata::TokenKind],
                texts: &[&str],
                pos: &mut usize,
                min_bp: u8,
            ) -> (Result<#cat_ident, WpdaParseError>, Vec<RecoveryAttempt>) {
                use mettail_prattail::wpda_runtime::WpdaResolveResult;
                use mettail_prattail::wpda_walker::WpdaWalker;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                // Phase 3.1.7 (C10, 2026-05-15): walker W = LexicographicWeight.
                type DW = LexicographicWeight;

                // Stage 6 G6+ (2026-05-02): default 1M; PRATTAIL_MAX_STEPS env
                // var overrides via run_to_end_of_input_env_aware.
                const MAX_STEPS: usize = 1_000_000;
                let mut walker = WpdaWalker::<DW, _>::new_for_category(
                    #engine_ident::default(),
                    #cat_src_idx_u16,
                    min_bp,
                );
                let mut src = mettail_prattail::wpda_runtime::MutableSliceTokenSource::with_texts(
                    kinds, texts,
                );
                walker.set_mutable_token_source(&mut src);
                let resolve = match walker.run_to_end_of_input_env_aware(MAX_STEPS, &src) {
                    Ok(()) => walker.resolve_at_end_of_input(&src),
                    Err(exceeded) => {
                        walker.clear_mutable_token_source();
                        return (
                            Err(WpdaParseError::Incomplete {
                                position: exceeded.position,
                            }),
                            Vec::new(),
                        );
                    }
                };
                walker.clear_mutable_token_source();
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
                    WpdaResolveResult::Accepted { roots, .. } => {
                        *pos = walker.position();
                        // C7b (Phase 3.1.6, 2026-05-15): realize the first
                        // SPPF root for backward-compat single-result return.
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(root, Some(1))
                                    .into_iter()
                                    .next()
                            );
                        let result = match pick {
                            Some(term) => std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdaParseError::EmptyResult),
                            None => Err(WpdaParseError::EmptyResult),
                        };
                        (result, attempts)
                    }
                    // Cluster H (2026-05-29): valid-prefix parse with
                    // trailing tokens. Return the prefix term (`Ok`) and
                    // set `*pos` to the prefix boundary; `parse_recovering`
                    // then appends a `TrailingTokens` error to its trail
                    // while STILL returning the partial AST — the
                    // recovering-mode "what parsed + what went wrong"
                    // contract (recovery_integration_tests assert
                    // `result.is_some()` for trailing-token inputs).
                    WpdaResolveResult::AcceptedWithTrailing { roots, position, .. } => {
                        *pos = position;
                        let pick = roots
                            .first()
                            .and_then(|&root|
                                walker
                                    .realize_root_to_terms(root, Some(1))
                                    .into_iter()
                                    .next()
                            );
                        let result = match pick {
                            Some(term) => std::sync::Arc::downcast::<#cat_ident>(term)
                                .map(|arc| std::sync::Arc::try_unwrap(arc)
                                    .unwrap_or_else(|arc| (*arc).clone()))
                                .map_err(|_| WpdaParseError::EmptyResult),
                            None => Err(WpdaParseError::EmptyResult),
                        };
                        (result, attempts)
                    }
                    WpdaResolveResult::ParseError { message, position } => {
                        let err = WpdaParseError::ParseFailed {
                            message,
                            position,
                            attempts: attempts.clone(),
                        };
                        (Err(err), attempts)
                    }
                    WpdaResolveResult::MaxStepsExceeded { position } => {
                        (Err(WpdaParseError::Incomplete { position }), attempts)
                    }
                    WpdaResolveResult::AmbiguityBudget { budget, actual, position } => {
                        (
                            Err(WpdaParseError::AmbiguityBudget { budget, actual, position }),
                            attempts,
                        )
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
            /// Diagnostic message from the walker's `WpdaState::Error`.
            pub message: std::string::String,
            /// Token position where the error surfaced.
            pub position: usize,
            /// Skip action taken, or `None` if no sync token was found
            /// (terminating round).
            pub recovery: Option<std::string::String>,
        }

        /// Error returned by `parse_<Cat>_via_wpda` wrappers when the walker
        /// terminates in a non-accepting state.
        ///
        /// `ParseFailed` carries the final-error fields plus the full
        /// recovery-attempt trail, so consumers don't need to re-run the
        /// recovering variant to inspect what was tried.
        #[derive(Debug, Clone)]
        pub enum WpdaParseError {
            /// Walker accepted, but the builder's term stack was empty —
            /// indicates a codegen bug (every successful parse should push
            /// exactly one term).
            EmptyResult,
            /// Walker entered `WpdaState::Error` with a diagnostic message.
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
            /// M11.7 (2026-05-14): walker was configured with
            /// `CursorBoundingMode::AmbiguityBudget(budget)` and the live
            /// frontier exceeded that budget. `actual` is the frontier
            /// size that triggered the overflow; `position` is the input
            /// position at the overflow point. Callers can react by
            /// relaxing the budget, switching strategy, or surfacing a
            /// structured "input too ambiguous" error.
            AmbiguityBudget {
                budget: usize,
                actual: usize,
                position: usize,
            },
        }

        impl std::fmt::Display for WpdaParseError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    WpdaParseError::EmptyResult => {
                        write!(f, "wpds parser produced no result")
                    }
                    WpdaParseError::ParseFailed { message, position, attempts } => {
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
                    WpdaParseError::Incomplete { position } => {
                        write!(f, "wpds parse incomplete at position {}", position)
                    }
                    WpdaParseError::AmbiguityBudget { budget, actual, position } => {
                        write!(
                            f,
                            "wpds parse aborted at position {}: ambiguity budget {} exceeded by frontier of {} cursors",
                            position, budget, actual,
                        )
                    }
                }
            }
        }

        impl std::error::Error for WpdaParseError {}

        #(#fns)*
    }
}
