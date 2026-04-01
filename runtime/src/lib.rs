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
mod canonical_bigint;
pub use canonical_bigint::CanonicalBigInt;
mod canonical_bigrat;
pub use canonical_bigrat::CanonicalBigRat;
mod canonical_fixed_point;
pub use canonical_fixed_point::CanonicalFixedPoint;

mod numeric_cast;
pub use numeric_cast::{
    cast_bigint_from_bigrat, cast_bigint_from_f64, cast_bigint_from_fixed, cast_bigrat_from_bigint,
    cast_bigrat_from_f64, cast_bigrat_from_fixed, cast_bigrat_from_i64, cast_bigrat_from_u32,
    cast_fixed_from_bigrat, cast_fixed_from_bigint, cast_fixed_from_f64, cast_fixed_from_fixed,
    cast_float_from_bigint, cast_float_from_bigrat, cast_float_from_f64, cast_float_from_f64_allow_nonfinite,
    cast_float_from_fixed, cast_int_from_bigint, cast_int_from_bigrat, cast_int_from_f64,
    cast_int_from_fixed, cast_int_from_i64, cast_int_from_u32, cast_uint_from_bigint,
    cast_uint_from_bigrat, cast_uint_from_f64, cast_uint_from_fixed, cast_uint_from_i64,
    cast_uint_from_u32, f64_to_exact_rational, signed_modular, unsigned_modular, CastError,
    FloatCastWidth, MAX_FIXED_PLACES, MAX_INT_UINT_WIDTH, validate_fixed_places, validate_float_width,
    validate_int_uint_width,
};

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
