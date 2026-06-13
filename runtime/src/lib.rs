//! Runtime support for MeTTaIL-generated code
//!
//! This crate provides:
//! - Variable binding support (via moniker wrappers)
//! - Collection types (HashBag for associative-commutative operations)
//! - Language metadata types for REPL introspection
//! - Core language traits and runtime-neutral backend reports
//! - Utility functions for parsing and variable management

// Variable binding support
mod binding;
pub use binding::*;

/// Runtime diagnostics queue (D11 ambiguous-display warnings, etc.).
/// Stage 7 of W7 plan v5.1.
pub mod diagnostics;

// Canonical float types for Float category (Eq/Hash/Ord)
mod canonical_float;
pub use canonical_float::{CanonicalFloat32, CanonicalFloat64};
mod canonical_bigint;
pub use canonical_bigint::CanonicalBigInt;
mod canonical_bigrat;
pub use canonical_bigrat::CanonicalBigRat;
mod canonical_fixed_point;
pub use canonical_fixed_point::CanonicalFixedPoint;

// Numeric literal parsers for fixed-point and float types. These live here
// (not in `mettail-prattail`) because they construct runtime types above and
// because the dep direction is runtime → prattail, not the reverse. Callers
// in generated code use `mettail_runtime::parse_fixed_lit` / `parse_float_lit`.
pub mod fixed_lit;
pub mod float_lit;
pub use fixed_lit::parse_fixed_lit;
pub use float_lit::parse_float_lit;

mod numeric_cast;
mod numeric_cast_dispatch;
pub use numeric_cast::{
    cast_bigint_from_bigrat, cast_bigint_from_f64, cast_bigint_from_fixed, cast_bigrat_from_bigint,
    cast_bigrat_from_f64, cast_bigrat_from_fixed, cast_bigrat_from_i64, cast_bigrat_from_u32,
    cast_fixed_from_bigint, cast_fixed_from_bigrat, cast_fixed_from_f64, cast_fixed_from_fixed,
    cast_float_from_bigint, cast_float_from_bigrat, cast_float_from_f64,
    cast_float_from_f64_allow_nonfinite, cast_float_from_fixed, cast_int_from_bigint,
    cast_int_from_bigrat, cast_int_from_f64, cast_int_from_fixed, cast_int_from_i64,
    cast_int_from_u32, cast_uint_from_bigint, cast_uint_from_bigrat, cast_uint_from_f64,
    cast_uint_from_fixed, cast_uint_from_i64, cast_uint_from_u32, f64_to_exact_rational,
    signed_modular, unsigned_modular, validate_fixed_places, validate_float_width,
    validate_int_uint_width, CastError, FloatCastWidth, MAX_FIXED_PLACES, MAX_INT_UINT_WIDTH,
};
pub use numeric_cast_dispatch::{
    bigint_unary_pipeline, bigint_unary_pipeline_decimal_str, bigrat_unary_pipeline,
    bigrat_unary_pipeline_numeric_str, fixed_bin_pipeline, fixed_bin_pipeline_numeric_str,
    float_bin_pipeline, float_bin_pipeline_parse_f64, int_bin_pipeline_decimal_str_i32,
    int_bin_pipeline_decimal_str_i64, int_bin_pipeline_i32, int_bin_pipeline_i64,
    int_uint_bits_from_width, numeric_try_bigint, numeric_try_bigrat, numeric_try_fixed,
    numeric_try_float, numeric_try_int, numeric_try_uint, uint_bin_pipeline_decimal_str_u32,
    uint_bin_pipeline_u32, NumericInput,
};

// Overflow-safe / NaN-safe arithmetic used by generated eval and Ascent rules
// to convert panicking Rust arithmetic into Option-returning steps.
mod safe_arith;
pub use safe_arith::{SafeArith, SafeFloat};

// Collection types
mod hashbag;
pub use hashbag::HashBag;

mod hashmap_lit;
pub use hashmap_lit::HashMapLit;

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

// Shared iterative-traversal infrastructure — extracted from the seven
// per-op engines previously hand-rolled by the macro per-language.
// See `runtime/src/visitor.rs` docs for scope + non-goals.
pub mod visitor;

// Runtime behavioral predicate AST for source-level predicated types.
// Phase 2A of the predicated-types implementation plan.
//
// This is a passive data type — the design specifies that all relation
// lookups happen via direct Ascent JOIN clauses emitted by the macro
// at compile time. See `docs/design/predicated-types.md` §8 and
// `mettail-macros::logic::rules::compile_guard_to_ascent_clauses`.
pub mod behavioral_pred;
pub use behavioral_pred::{
    clear_pred_fact_snapshot, evaluate_pred_with_bindings, set_pred_fact_snapshot, BehavioralPred,
    PredArg, QuantifiedDomain, Quantifier,
};

// Phase 7: refinement-type predicate registry + evaluator. Generated
// rule action codegen calls `evaluate_refinement_predicate` after
// constructing a candidate term against a refined category to enforce
// the refinement.
pub mod refinement;
pub use refinement::{
    clear_refinement_registry, evaluate_refinement_predicate, register_refinement_predicate,
    RefinementPredicate,
};

// T4 user assertion registry — see `t4_assertions` for full lifecycle.
// Phase 7C of the predicated-types implementation plan.
pub mod t4_assertions;
pub use t4_assertions::{
    clear_t4_assertions, register_t4_assertion, t4_assertion_lookup, T4Assertion, T4AssertionHandle,
};

// Language-generic parsers for sub-sublanguages embedded inside
// `language!`-defined languages. Currently hosts the predicate
// sublanguage parser (Phase 1B of the predicated-types implementation
// plan).
pub mod parser;
pub use parser::{
    parse_predicate_from_str, ParseError, PredicateParser, PredicateParserConfig, TerminatorToken,
};

// Re-export CEK evaluator types when cek-runtime feature is enabled,
// so consumers don't need a direct mettail-prattail dependency.
pub use mettail_prattail::cek_eval::{
    CekEvaluator, EvalFrame, EvalObserver, EvalState, EvalStepEvent, NullEvalObserver, StepResult,
    TracingEvalObserver,
};

// Re-export CESK store types for consumers that need store manipulation.
pub use mettail_prattail::cesk_store::{LocalCeskStore, StoreAddr, StoreValue};

// Re-export GC types for consumers that need GC configuration.
pub use mettail_prattail::gc::{GcStrategy, RefCountGc};

/// `Lift<T>` — autoref-specialization helper used by the macro-generated
/// safeify wrapper around user `![…]` eval blocks.
///
/// **Problem solved:** the safeify pass rewrites `![a + b]` into
/// `(|| -> Option<_> { Some(safe_add(a,b)?) })()` (one level of `Option`).
/// But user evals like `![{ calc_try_int_bin(&a, w) }]` *already* return
/// `Option<i32>`. Wrapping with `Some(...)` produces `Option<Option<i32>>`
/// and the expected type is `Option<i32>`.
///
/// **Solution:** the generated closure body becomes
/// `(&Lift(rewritten)).lift()` where method resolution picks:
///   - the inherent method on `Lift<Option<T>>` (passthrough) when the
///     expression already returns `Option<T>`;
///   - the trait method on `&Lift<T>` (returns `Some(t)`) for plain `T`.
///
/// This is the dtolnay autoref-specialization trick: inherent methods bind
/// without autoref, trait methods bind with autoref, so the inherent
/// passthrough always wins for `Option<T>`.
pub mod lift {
    /// Newtype wrapper used to drive method-resolution dispatch.
    /// Always constructed by-value at the call site and consumed by `.lift()`.
    pub struct Lift<T>(pub T);

    impl<T> Lift<Option<T>> {
        /// Inherent passthrough for already-`Option<T>` values.
        ///
        /// Wins over the trait impl on `&Lift<…>` because no autoref is
        /// needed, and inherent-method resolution outranks trait-method
        /// resolution at equal autoref depth.
        #[inline]
        pub fn lift(self) -> Option<T> {
            self.0
        }
    }

    /// Trait providing `lift()` on `&Lift<T>` for plain (non-`Option`) `T`.
    ///
    /// The autoref step happens via `Lift(x).lift()`; for `Lift<Option<T>>`
    /// the inherent method binds first (no autoref) and this trait is
    /// bypassed. For plain `T`, autoref takes `&Lift<T>` and dispatches here.
    ///
    /// `T: Clone` is required because the receiver is a borrow — we cannot
    /// move `T` out of `&Lift<T>` safely. All numeric/string/canonical types
    /// generated code uses already implement `Clone`, so this is not a
    /// real-world restriction.
    pub trait LiftPlain {
        type Output;
        fn lift(self) -> Self::Output;
    }

    impl<T: Clone> LiftPlain for &Lift<T> {
        type Output = Option<T>;
        #[inline]
        fn lift(self) -> Option<T> {
            Some(self.0.clone())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// Inherent specialization wins for `Option<T>`: passthrough.
        ///
        /// Method resolution: `Lift(x).lift()` finds the inherent
        /// `impl Lift<Option<T>>::lift` without needing autoref, so it
        /// outranks the trait impl on `&Lift<T>`.
        #[test]
        fn lift_option_passes_through_some() {
            let x: Option<i32> = Some(42);
            let out: Option<i32> = Lift(x).lift();
            assert_eq!(out, Some(42));
        }

        #[test]
        fn lift_option_passes_through_none() {
            let x: Option<i32> = None;
            let out: Option<i32> = Lift(x).lift();
            assert_eq!(out, None);
        }

        /// Trait fallback wraps a plain `T` in `Some`.
        ///
        /// `Lift(x).lift()` for `x: i32` finds no inherent on
        /// `Lift<i32>` (only `Lift<Option<T>>` has one), so resolution
        /// autorefs to `&Lift<i32>` and the trait impl `LiftPlain for
        /// &Lift<T>` binds, returning `Some(x)`.
        #[test]
        fn lift_plain_t_wraps_some() {
            let x: i32 = 7;
            let out: Option<i32> = Lift(x).lift();
            assert_eq!(out, Some(7));
        }

        /// Plain `T` with non-`Copy` payload is moved (not cloned).
        #[test]
        fn lift_plain_moves_owned() {
            let s = String::from("hello");
            let out: Option<String> = Lift(s).lift();
            assert_eq!(out.as_deref(), Some("hello"));
        }
    }
}

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
