//! Unified Parse Dispatch via PathMap Decision Trees
//!
//! Replaces 7 ad-hoc dispatch optimizations (A1 left-factoring, B1 two-token
//! lookahead, G1 Phases 1-4) with a single trie-based mechanism. Each category
//! gets a decision tree where byte-encoded token prefixes map to parse rules.
//!
//! ## Encoding Scheme
//!
//! ```text
//! 0x00..0x7F  Terminal token IDs (from TokenIdMap; max ~100 typical)
//! 0x80        IDENT_CAPTURE — consumes exactly one Ident token
//! 0x81        BINDER_CAPTURE — consumes exactly one Ident (binding)
//! 0x82..0xBF  NonTerminal category IDs (0x82 + category_index)
//! 0xC0        OPTIONAL_START marker
//! 0xC1        OPTIONAL_END marker
//! ```
//!
//! The trie is **split at nonterminal boundaries** into linked segments.
//! At boundaries, FIRST set expansion determines if the decision is
//! deterministic (peek token) or ambiguous (NFA try-all on minimal set).
//!
//! ## Output Format
//!
//! Adaptive: match arms for small/medium grammars (<=256 states),
//! flat table for large grammars. Runtime PathMap is not used —
//! match arms are 4-8x faster per step.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::lint::DiagnosticId;

use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice};
use pathmap::PathMap;

use crate::automata::codegen::terminal_to_variant_name;
use crate::grammar::ir::{CastRule, CrossCategoryRule, RDRuleInfo, RDSyntaxItem};
use crate::prediction::FirstSet;
use crate::token_id::TokenIdMap;
use crate::wfst::PredictionWfst;

mod model;
pub use model::*;
mod builder;
pub use builder::*;
mod cse;
pub use cse::*;
mod emit;
pub use emit::*;
mod reports;
pub(crate) use builder::first_set_of_pattern_suffix;
pub(crate) use emit::dt_diagnostic;
pub(crate) use model::{
    BINDER_CAPTURE, IDENT_CAPTURE, MAX_TERMINAL_ID, NT_BASE, OPTIONAL_END, OPTIONAL_START,
};
pub(crate) use reports::wfst_token_byte;
pub use reports::*;

#[cfg(test)]
mod tests;
