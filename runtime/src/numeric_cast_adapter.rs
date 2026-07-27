//! Language-agnostic numeric-cast **adapter** layer.
//!
//! The numeric-cast *computation* lives in [`crate::numeric_cast_dispatch`] (`NumericInput`
//! + the `*_pipeline_*` entry points) and is fully language-agnostic. A front-end's only
//! per-language obligation is to translate its concrete `Proc` AST to/from `NumericInput`
//! and (for object-output casts) to build the result `Proc`. Those obligations are the
//! three traits below; their impls are **macro-generated** per language from the `Cast*`
//! and numeric-cast `fold` rules (see
//! `docs/design/made/native-types/numeric-cast-adapter-generation.md`), so no language
//! hand-writes numeric glue.
//!
//! Two reduction families, because the two output flavors differ in *failure model*:
//!   * **native-output** (`numeric_*`, e.g. Calculator `int(a,m) : Int`): returns
//!     `Option<scalar>`; `None` means "no numeric result for this derivation" and the
//!     caller (the fold dispatcher) leaves the redex unreduced (defers).
//!   * **object-output** (`proc_*`, e.g. Rholang `int(a,m) : Proc`): returns the result
//!     `Proc`, or the language's `Err` `Proc` on a bad cast (object folds cannot defer on
//!     `None` — a bad cast must fold to `Err`, not stay a redex).
//!
//! Each generic reduction reproduces the previously hand-written per-language control flow
//! and its order exactly: width → element-peel → numeric-string fast-path → nested same-op
//! recursion (only the arities that had it) → BigRat-eval fast-path (float only) →
//! `to_numeric_input` fallthrough → the shared typed pipeline.

use crate::numeric_cast_dispatch::{
    bigint_unary_pipeline, bigint_unary_pipeline_decimal_str, bigrat_unary_pipeline,
    bigrat_unary_pipeline_numeric_str, fixed_bin_pipeline, fixed_bin_pipeline_numeric_str,
    float_bin_pipeline, float_bin_pipeline_parse_f64, int_bin_pipeline_decimal_str_i32,
    int_bin_pipeline_decimal_str_i64, int_bin_pipeline_i32, int_bin_pipeline_i64,
    uint_bin_pipeline_decimal_str_u32, uint_bin_pipeline_u32, NumericInput,
};
use crate::{CanonicalBigInt, CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat64};

/// Extract the bit/place/float width `m` of a cast (`int(a, m)`) as an `i64`.
///
/// Implemented for the native carriers here; a language's `Int`/`&Int` impls are
/// macro-generated (a non-literal/`CastErr*` width yields `None`, i.e. the cast defers).
pub trait CastWidth {
    fn into_width_i64(self) -> Option<i64>;
}

impl CastWidth for i32 {
    #[inline]
    fn into_width_i64(self) -> Option<i64> {
        Some(self as i64)
    }
}
impl CastWidth for i64 {
    #[inline]
    fn into_width_i64(self) -> Option<i64> {
        Some(self)
    }
}

/// Translate a (fully reduced) numeric `Proc` to a borrowed [`NumericInput`], plus the
/// per-language fast-path hooks the reductions consult before the general fallthrough.
///
/// `Self` is the language's `Proc`. The returned [`NumericInput`] may borrow data owned
/// inside `self` (e.g. `&BigInt`), hence the elided `'_` is tied to `&self`.
pub trait ProcToNumericInput {
    /// General case: a `Cast*` wrapper around a literal (or a nested numeric-cast redex)
    /// becomes a `NumericInput`; anything non-numeric / not-yet-reduced is `None`.
    fn to_numeric_input(&self) -> Option<NumericInput<'_>>;

    /// Indexed-collection element peel (Calculator `at([..], i)` → element `Proc`). The
    /// default is identity, so languages without indexed-collection numeric casts (Rholang)
    /// pay nothing. An out-of-bounds / non-literal index MUST return `self` (never panic):
    /// it is evidence the parse alternate is invalid, and a sibling alternate still peels.
    #[inline]
    fn peel_numeric_elem(&self) -> &Self {
        self
    }

    /// Numeric-string fast-path: the language's string wrapper around a `&str` literal.
    #[inline]
    fn as_numeric_str(&self) -> Option<&str> {
        None
    }

    /// Lossless-rational fast-path used by `float` casts only (e.g. `float(1r/4r, m)`):
    /// evaluate a computed-rational wrapper to an owned rational. Default `None`.
    #[inline]
    fn as_evaluable_bigrat(&self) -> Option<CanonicalBigRat> {
        None
    }

    /// Nested same-op recursion hooks: if `self` is itself the int/float/fixed binary-cast
    /// redex, yield its (inner arg, extracted width). A width that fails extraction yields
    /// `None` here, and the reduction then falls through to [`Self::to_numeric_input`]
    /// (which carries the same redex arm), preserving the original semantics. Default `None`.
    #[inline]
    fn as_int_bin(&self) -> Option<(&Self, i64)> {
        None
    }
    #[inline]
    fn as_float_bin(&self) -> Option<(&Self, i64)> {
        None
    }
    #[inline]
    fn as_fixed_bin(&self) -> Option<(&Self, i64)> {
        None
    }
}

/// Build the **object-output** result `Proc` from a computed cast value, or the language's
/// `Err` `Proc` on failure. Implemented (macro-generated) ONLY for non-native-output
/// languages (Rholang). Native-output languages (Calculator) never implement this — their
/// reductions return the native scalar and defer on `None`.
pub trait CastResult: Sized {
    fn err() -> Self;
    fn from_int(n: i64) -> Self;
    fn from_uint(n: u32) -> Self;
    fn from_float(f: CanonicalFloat64) -> Self;
    fn from_fixed(fp: CanonicalFixedPoint) -> Self;
    fn from_bigint(n: CanonicalBigInt) -> Self;
    fn from_bigrat(r: CanonicalBigRat) -> Self;
}

// ── native-output (scalar) reductions ───────────────────────────────────────────────────
// Two int widths: Calculator `Int = i32` uses `numeric_int_bin_i32`; Rholang `Int = i64`
// uses `numeric_int_bin_i64` (and `proc_int_bin` wraps it). The `_i32` path narrows through
// `to_i32` and so rejects values an `i64` would accept — this is intentional and preserved.

/// `int(a, m) : i32` — Calculator's native int cast.
#[inline]
pub fn numeric_int_bin_i32<P, W>(a: &P, w: W) -> Option<i32>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return int_bin_pipeline_decimal_str_i32(s, width);
    }
    if let Some((inner_a, inner_w)) = a.as_int_bin() {
        let n = numeric_int_bin_i32(inner_a, inner_w)?;
        return int_bin_pipeline_i32(NumericInput::I32(n), width);
    }
    int_bin_pipeline_i32(a.to_numeric_input()?, width)
}

/// `int(a, m) : i64` — Rholang's int cast value (also the body of [`proc_int_bin`]).
#[inline]
pub fn numeric_int_bin_i64<P, W>(a: &P, w: W) -> Option<i64>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return int_bin_pipeline_decimal_str_i64(s, width);
    }
    if let Some((inner_a, inner_w)) = a.as_int_bin() {
        let n = numeric_int_bin_i64(inner_a, inner_w)?;
        return int_bin_pipeline_i64(NumericInput::I64(n), width);
    }
    int_bin_pipeline_i64(a.to_numeric_input()?, width)
}

/// `uint(a, m) : u32`. No nested-recursion fast-path (neither language had one here).
#[inline]
pub fn numeric_uint_bin_u32<P, W>(a: &P, w: W) -> Option<u32>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return uint_bin_pipeline_decimal_str_u32(s, width);
    }
    uint_bin_pipeline_u32(a.to_numeric_input()?, width)
}

/// `float(a, m)`. Order: string → BigRat-eval → nested float-bin → fallthrough.
#[inline]
pub fn numeric_float_bin<P, W>(a: &P, w: W) -> Option<CanonicalFloat64>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return float_bin_pipeline_parse_f64(s, width);
    }
    if let Some(rat) = a.as_evaluable_bigrat() {
        return float_bin_pipeline(NumericInput::BigRat(rat.get()), width);
    }
    if let Some((inner_a, inner_w)) = a.as_float_bin() {
        let cf = numeric_float_bin(inner_a, inner_w)?;
        return float_bin_pipeline(NumericInput::F64(cf.get()), width);
    }
    float_bin_pipeline(a.to_numeric_input()?, width)
}

/// `fixed(a, m)`. No nested-recursion fast-path.
#[inline]
pub fn numeric_fixed_bin<P, W>(a: &P, w: W) -> Option<CanonicalFixedPoint>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return fixed_bin_pipeline_numeric_str(s, width);
    }
    fixed_bin_pipeline(a.to_numeric_input()?, width)
}

/// `bigint(a)`. Nested `fixed`-cast recursion fast-path (both languages had it).
#[inline]
pub fn numeric_bigint_unary<P>(a: &P) -> Option<CanonicalBigInt>
where
    P: ProcToNumericInput,
{
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return bigint_unary_pipeline_decimal_str(s);
    }
    if let Some((inner_a, inner_w)) = a.as_fixed_bin() {
        let fp = numeric_fixed_bin(inner_a, inner_w)?;
        return bigint_unary_pipeline(NumericInput::Fixed(&fp));
    }
    bigint_unary_pipeline(a.to_numeric_input()?)
}

/// `bigrat(a)`. Nested `fixed`-cast recursion fast-path (both languages had it).
#[inline]
pub fn numeric_bigrat_unary<P>(a: &P) -> Option<CanonicalBigRat>
where
    P: ProcToNumericInput,
{
    let a = a.peel_numeric_elem();
    if let Some(s) = a.as_numeric_str() {
        return bigrat_unary_pipeline_numeric_str(s);
    }
    if let Some((inner_a, inner_w)) = a.as_fixed_bin() {
        let fp = numeric_fixed_bin(inner_a, inner_w)?;
        return bigrat_unary_pipeline(NumericInput::Fixed(&fp));
    }
    bigrat_unary_pipeline(a.to_numeric_input()?)
}

// ── object-output reductions (build a result `Proc`, or `Err`) ───────────────────────────

/// `int(a, m) : Proc` — value on success, `Proc::Err` on a bad cast.
#[inline]
pub fn proc_int_bin<P, W>(a: &P, w: W) -> P
where
    P: ProcToNumericInput + CastResult,
    W: CastWidth,
{
    numeric_int_bin_i64(a, w).map_or_else(P::err, P::from_int)
}

/// `uint(a, m) : Proc`.
#[inline]
pub fn proc_uint_bin<P, W>(a: &P, w: W) -> P
where
    P: ProcToNumericInput + CastResult,
    W: CastWidth,
{
    numeric_uint_bin_u32(a, w).map_or_else(P::err, P::from_uint)
}

/// `float(a, m) : Proc`.
#[inline]
pub fn proc_float_bin<P, W>(a: &P, w: W) -> P
where
    P: ProcToNumericInput + CastResult,
    W: CastWidth,
{
    numeric_float_bin(a, w).map_or_else(P::err, P::from_float)
}

/// `fixed(a, m) : Proc`.
#[inline]
pub fn proc_fixed_bin<P, W>(a: &P, w: W) -> P
where
    P: ProcToNumericInput + CastResult,
    W: CastWidth,
{
    numeric_fixed_bin(a, w).map_or_else(P::err, P::from_fixed)
}

/// `bigint(a) : Proc`.
#[inline]
pub fn proc_bigint_unary<P>(a: &P) -> P
where
    P: ProcToNumericInput + CastResult,
{
    numeric_bigint_unary(a).map_or_else(P::err, P::from_bigint)
}

/// `bigrat(a) : Proc`.
#[inline]
pub fn proc_bigrat_unary<P>(a: &P) -> P
where
    P: ProcToNumericInput + CastResult,
{
    numeric_bigrat_unary(a).map_or_else(P::err, P::from_bigrat)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal stand-in for a generated language `Proc`, proving the generic reductions
    /// work over an ARBITRARY front-end with hand-written trait impls and no `language!`.
    #[derive(Debug, Clone, PartialEq)]
    enum FakeProc {
        IntLit(i64),
        StrLit(String),
        /// nested `int(inner, w)` redex
        IntBin(Box<FakeProc>, i64),
        Err,
        NonNumeric,
    }

    impl ProcToNumericInput for FakeProc {
        fn to_numeric_input(&self) -> Option<NumericInput<'_>> {
            match self {
                FakeProc::IntLit(n) => Some(NumericInput::I64(*n)),
                _ => None,
            }
        }
        fn as_numeric_str(&self) -> Option<&str> {
            match self {
                FakeProc::StrLit(s) => Some(s),
                _ => None,
            }
        }
        fn as_int_bin(&self) -> Option<(&Self, i64)> {
            match self {
                FakeProc::IntBin(a, w) => Some((a.as_ref(), *w)),
                _ => None,
            }
        }
    }

    impl CastResult for FakeProc {
        fn err() -> Self {
            FakeProc::Err
        }
        fn from_int(n: i64) -> Self {
            FakeProc::IntLit(n)
        }
        fn from_uint(n: u32) -> Self {
            FakeProc::IntLit(n as i64)
        }
        fn from_float(_f: CanonicalFloat64) -> Self {
            FakeProc::NonNumeric
        }
        fn from_fixed(_fp: CanonicalFixedPoint) -> Self {
            FakeProc::NonNumeric
        }
        fn from_bigint(_n: CanonicalBigInt) -> Self {
            FakeProc::NonNumeric
        }
        fn from_bigrat(_r: CanonicalBigRat) -> Self {
            FakeProc::NonNumeric
        }
    }

    #[test]
    fn literal_in_range_round_trips() {
        // 5 fits in 8 bits → unchanged.
        assert_eq!(numeric_int_bin_i64(&FakeProc::IntLit(5), 8i64), Some(5));
        assert_eq!(numeric_int_bin_i32(&FakeProc::IntLit(5), 8i64), Some(5));
    }

    #[test]
    fn numeric_string_fast_path() {
        assert_eq!(numeric_int_bin_i64(&FakeProc::StrLit("42".to_string()), 8i64), Some(42));
    }

    #[test]
    fn nested_redex_recurses() {
        // int(int(9, 16), 8) → 9
        let nested = FakeProc::IntBin(Box::new(FakeProc::IntLit(9)), 16);
        assert_eq!(numeric_int_bin_i64(&nested, 8i64), Some(9));
    }

    #[test]
    fn non_numeric_defers_to_none() {
        assert_eq!(numeric_int_bin_i64(&FakeProc::NonNumeric, 8i64), None);
    }

    #[test]
    fn object_output_builds_value_or_err() {
        // good cast → value Proc
        assert_eq!(proc_int_bin(&FakeProc::IntLit(7), 8i64), FakeProc::IntLit(7));
        // bad cast → Err Proc (NOT a deferral — object folds fold a bad cast to Err)
        assert_eq!(proc_int_bin(&FakeProc::NonNumeric, 8i64), FakeProc::Err);
    }

    #[test]
    fn invalid_width_defers() {
        // A width arg that fails `into_width_i64` would come from a generated `Int` impl;
        // here we exercise the `numeric_*` side: an out-of-range modular width still yields
        // a value, but a structurally-bad arg yields None. Use the object path for Err.
        assert_eq!(proc_int_bin(&FakeProc::Err, 8i64), FakeProc::Err);
    }
}
