//! Runtime support for MeTTaIL-generated code
//!
//! This crate provides:
//! - Variable binding support (via moniker wrappers)
//! - Collection types (HashBag for associative-commutative operations)
//! - Language metadata types for REPL introspection
//! - Core language traits (Term, AscentResults)
//! - Utility functions for parsing and variable management

// Variable binding support
mod binding;
pub use binding::*;

// Canonical float types for Float category (Eq/Hash/Ord)
mod canonical_float;
pub use canonical_float::{CanonicalFloat32, CanonicalFloat64};

// Overflow-safe / NaN-safe arithmetic used by generated eval and Ascent rules
// to convert panicking Rust arithmetic into Option-returning steps.
mod safe_arith;
pub use safe_arith::{SafeArith, SafeFloat};

// Collection types
mod hashbag;
pub use hashbag::HashBag;

// Language metadata for REPL introspection
mod metadata;
pub use metadata::*;

// Core language traits and types
mod language;
pub use language::*;

// Matchings enumeration for zip+map correlated search (used by generated rewrite clauses)
mod matchings;
pub use matchings::*;

// Hash-consing infrastructure for recursive term types (A-RT01)
mod hash_consing;
pub use hash_consing::*;

// Runtime behavioral predicate AST for source-level predicated types.
// Phase 2A of the predicated-types implementation plan.
//
// This is a passive data type — the design specifies that all relation
// lookups happen via direct Ascent JOIN clauses emitted by the macro
// at compile time. See `docs/design/predicated-types.md` §8 and
// `mettail-macros::logic::rules::compile_guard_to_ascent_clauses`.
pub mod behavioral_pred;
pub use behavioral_pred::{
    BehavioralPred, PredArg, Quantifier, QuantifiedDomain,
    set_pred_fact_snapshot, clear_pred_fact_snapshot,
    evaluate_pred_with_bindings,
};

// T4 user assertion registry — see `t4_assertions` for full lifecycle.
// Phase 7C of the predicated-types implementation plan.
pub mod t4_assertions;
pub use t4_assertions::{
    clear_t4_assertions, register_t4_assertion, t4_assertion_lookup,
    T4Assertion, T4AssertionHandle,
};

// Language-generic parsers for sub-sublanguages embedded inside
// `language!`-defined languages. Currently hosts the predicate
// sublanguage parser (Phase 1B of the predicated-types implementation
// plan).
pub mod parser;
pub use parser::{
    parse_predicate_from_str, ParseError, PredicateParser,
    PredicateParserConfig, TerminatorToken,
};

// Re-export CEK evaluator types when cek-runtime feature is enabled,
// so consumers don't need a direct mettail-prattail dependency.
pub use mettail_prattail::cek_eval::{
    CekEvaluator, EvalFrame, EvalObserver, EvalState, EvalStepEvent, NullEvalObserver,
    StepResult, TracingEvalObserver,
};

// Re-export CESK store types for consumers that need store manipulation.
pub use mettail_prattail::cesk_store::{LocalCeskStore, StoreAddr, StoreValue};

// Re-export GC types for consumers that need GC configuration.
pub use mettail_prattail::gc::{GcStrategy, RefCountGc};

/// Wrapper that provides `Display` for slices/Vecs of `Display` items.
///
/// Renders as a comma-separated list, e.g. `a, b, c`.
/// Used by generated extraction code so `Vec<T>` columns get pretty-printed
/// via `T`'s `Display` impl rather than falling back to `Debug`.
pub struct DisplaySlice<'a, T>(pub &'a [T]);

impl<T: std::fmt::Display> std::fmt::Display for DisplaySlice<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, item) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}
