//! Pipeline for lexer+parser code generation.
//!
//! Implements a state machine that:
//! 1. **Extracts** data bundles from `&LanguageSpec`
//! 2. **Generates** lexer and parser code (sequentially)
//! 3. **Finalizes** by concatenating both code strings and parsing into a `TokenStream`
//!
//! This architecture cleanly separates data extraction from code generation,
//! and isolates `!Send` `LanguageSpec` (which contains `proc_macro2::TokenStream`
//! fields) from the generation phase. The Send+Sync bundles enable future
//! parallelism if workload becomes large enough to justify thread overhead.
//!
//! ```text
//! LanguageSpec ──→ [Extract] ──→ Ready ──→ [Generate] ──→ Generated ──→ [Finalize] ──→ Complete
//!                  separate        LexerBundle ──→ lexer_code    concatenate + parse
//!                  bundles         ParserBundle ──→ parser_code   into TokenStream
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use proc_macro2::TokenStream;

use crate::binding_power::{
    analyze_binding_powers, compute_prefix_bp, BindingPowerTable, InfixRuleInfo, MixfixPart,
};
// Stage 10.5 (2026-05-04): trampoline emitter imports DELETED. The legacy
// modules (pratt, recursive, dispatch, trampoline) are being phased out;
// data-type imports re-routed directly through `crate::grammar::ir::*`.
use crate::automata::codegen::{LexerAmbiguityInfo, TokenVariantMap};
use crate::grammar::ir::{CastRule, CrossCategoryRule, RDRuleInfo, RDSyntaxItem};
use crate::lexer::{extract_terminals, generate_lexer_as_string_hybrid, GrammarRuleInfo, TypeInfo};
// Stage 10.5b conclusion (2026-05-05): pratt::write_parser_helpers /
// write_recovery_helpers DELETED. They emitted runtime helpers
// (expect_token, expect_ident, peek_token, peek_ahead, sync_to) that
// were consumed only by trampoline-emitted RD handlers, all gone.
// Walker (parse_<Cat>_via_wpda) has its own error handling via
// WpdaParseError + RecoveryAttempt and doesn't need these helpers.
use crate::lint::DiagnosticId;
use crate::prediction::{
    analyze_cross_category_overlaps, compute_first_sets, compute_first_sets_incremental,
    compute_follow_sets_from_inputs, compute_follow_sets_incremental, generate_sync_predicate,
    FirstItem, FirstSet, FollowSetInput, RuleInfo,
};
use crate::wfst::PredictionWfst;
use crate::{LanguageSpec, LiteralPatterns, SyntaxItemSpec};

mod dead_rules;
pub use dead_rules::*;
mod state;
pub use state::*;
mod analysis;
pub use analysis::*;
mod wfst_emit;
pub(crate) use wfst_emit::*;
mod codegen;
pub(crate) use codegen::*;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proptest_tests;
