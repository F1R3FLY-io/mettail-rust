//! Language-agnostic numeric casting: [`NumericInput`] carries tagged payloads from any
//! front-end; [`numeric_try_*`] and `*_pipeline_*` implement semantics via [`crate::numeric_cast`].
//!
//! Language crates map their `Proc` (or similar) into [`NumericInput`], then call pipelines here.
//! No `language!` types appear in this module.

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::ToPrimitive;

use crate::{
    canonical_bigrat::CanonicalBigRat, canonical_bigint::CanonicalBigInt,
    canonical_fixed_point::CanonicalFixedPoint, *,
};

/// A numeric value reachable from a language `Proc` injection, for cast builtins.
#[derive(Clone, Copy)]
pub enum NumericInput<'a> {
    I32(i32),
    I64(i64),
    U32(u32),
    BigInt(&'a BigInt),
    BigRat(&'a Ratio<BigInt>),
    Fixed(&'a CanonicalFixedPoint),
    /// Raw `f64` (finite casts use fallible helpers; non-finite is rejected where required).
    F64(f64),
}

/// Validate `width` as an `int`/`uint` bit width and return `m` for [`numeric_cast`].
pub fn int_uint_bits_from_width(width: i64) -> Option<u32> {
    validate_int_uint_width(width).ok()
}

/// Try `int(arg, m)` semantics → mathematical integer as [`BigInt`] before target narrowing.
pub fn numeric_try_int(input: NumericInput<'_>, bits: u32) -> Option<BigInt> {
    let bi = match input {
        NumericInput::I32(n) => cast_int_from_i64(n as i64, bits),
        NumericInput::I64(n) => cast_int_from_i64(n, bits),
        NumericInput::U32(n) => cast_int_from_u32(n, bits),
        NumericInput::BigInt(n) => cast_int_from_bigint(n, bits),
        NumericInput::BigRat(r) => cast_int_from_bigrat(r, bits).ok()?,
        NumericInput::Fixed(fp) => cast_int_from_fixed(fp, bits).ok()?,
        NumericInput::F64(x) => cast_int_from_f64(x, bits).ok()?,
    };
    Some(bi)
}

/// Try `uint(arg, m)` → non-negative modular [`BigInt`] in range of `m` bits.
pub fn numeric_try_uint(input: NumericInput<'_>, bits: u32) -> Option<BigInt> {
    let bi = match input {
        NumericInput::I32(n) => unsigned_modular(&BigInt::from(n), bits),
        NumericInput::I64(n) => unsigned_modular(&BigInt::from(n), bits),
        NumericInput::U32(n) => cast_uint_from_u32(n, bits),
        NumericInput::BigInt(n) => cast_uint_from_bigint(n, bits),
        NumericInput::BigRat(r) => cast_uint_from_bigrat(r, bits).ok()?,
        NumericInput::Fixed(fp) => cast_uint_from_fixed(fp, bits).ok()?,
        NumericInput::F64(x) => cast_uint_from_f64(x, bits).ok()?,
    };
    Some(bi)
}

pub fn numeric_try_float(input: NumericInput<'_>, fw: FloatCastWidth) -> Option<CanonicalFloat64> {
    Some(match input {
        NumericInput::I32(n) => cast_float_from_bigint(&BigInt::from(n), fw),
        NumericInput::I64(n) => cast_float_from_bigint(&BigInt::from(n), fw),
        NumericInput::U32(n) => cast_float_from_bigint(&BigInt::from(n), fw),
        NumericInput::BigInt(n) => cast_float_from_bigint(n, fw),
        NumericInput::BigRat(r) => cast_float_from_bigrat(r, fw),
        NumericInput::Fixed(fp) => cast_float_from_fixed(fp, fw),
        NumericInput::F64(x) => cast_float_from_f64_allow_nonfinite(x, fw),
    })
}

pub fn numeric_try_fixed(input: NumericInput<'_>, places: u32) -> Option<CanonicalFixedPoint> {
    Some(match input {
        NumericInput::I32(n) => cast_fixed_from_bigint(&BigInt::from(n), places),
        NumericInput::I64(n) => cast_fixed_from_bigint(&BigInt::from(n), places),
        NumericInput::U32(n) => cast_fixed_from_bigint(&BigInt::from(n), places),
        NumericInput::BigInt(n) => cast_fixed_from_bigint(n, places),
        NumericInput::BigRat(r) => cast_fixed_from_bigrat(r, places),
        NumericInput::Fixed(fp) => cast_fixed_from_fixed(fp, places),
        NumericInput::F64(x) => cast_fixed_from_f64(x, places).ok()?,
    })
}

pub fn numeric_try_bigint(input: NumericInput<'_>) -> Option<CanonicalBigInt> {
    Some(match input {
        NumericInput::I32(n) => CanonicalBigInt::from(BigInt::from(n)),
        NumericInput::I64(n) => CanonicalBigInt::from(BigInt::from(n)),
        NumericInput::U32(n) => CanonicalBigInt::from(BigInt::from(n)),
        NumericInput::BigInt(n) => CanonicalBigInt::from((*n).clone()),
        NumericInput::BigRat(r) => CanonicalBigInt::from(cast_bigint_from_bigrat(r)),
        NumericInput::Fixed(fp) => CanonicalBigInt::from(cast_bigint_from_fixed(fp)),
        NumericInput::F64(x) => CanonicalBigInt::from(cast_bigint_from_f64(x).ok()?),
    })
}

pub fn numeric_try_bigrat(input: NumericInput<'_>) -> Option<CanonicalBigRat> {
    Some(match input {
        NumericInput::I32(n) => cast_bigrat_from_i64(n as i64),
        NumericInput::I64(n) => cast_bigrat_from_i64(n),
        NumericInput::U32(n) => cast_bigrat_from_u32(n),
        NumericInput::BigInt(n) => cast_bigrat_from_bigint(n),
        NumericInput::BigRat(r) => CanonicalBigRat::from((*r).clone()),
        NumericInput::Fixed(fp) => cast_bigrat_from_fixed(fp),
        NumericInput::F64(x) => cast_bigrat_from_f64(x).ok()?,
    })
}

// ── Width-bearing pipelines (language-agnostic; callers supply `NumericInput`) ──

/// `int(·, m)` for `i32` carriers after [`numeric_try_int`].
#[inline]
pub fn int_bin_pipeline_i32(input: NumericInput<'_>, width_i64: i64) -> Option<i32> {
    let bits = int_uint_bits_from_width(width_i64)?;
    numeric_try_int(input, bits).and_then(|b| b.to_i32())
}

/// `int(·, m)` for `i64` carriers (e.g. RhoCalc `CastInt`).
#[inline]
pub fn int_bin_pipeline_i64(input: NumericInput<'_>, width_i64: i64) -> Option<i64> {
    let bits = int_uint_bits_from_width(width_i64)?;
    numeric_try_int(input, bits).and_then(|b| b.to_i64())
}

/// Parse decimal integer string, then `int(·, m)` → `i32`.
#[inline]
pub fn int_bin_pipeline_decimal_str_i32(s: &str, width_i64: i64) -> Option<i32> {
    let bi: BigInt = s.parse().ok()?;
    int_bin_pipeline_i32(NumericInput::BigInt(&bi), width_i64)
}

#[inline]
pub fn int_bin_pipeline_decimal_str_i64(s: &str, width_i64: i64) -> Option<i64> {
    let bi: BigInt = s.parse().ok()?;
    int_bin_pipeline_i64(NumericInput::BigInt(&bi), width_i64)
}

/// `uint(·, m)` → `u32`.
#[inline]
pub fn uint_bin_pipeline_u32(input: NumericInput<'_>, width_i64: i64) -> Option<u32> {
    let bits = int_uint_bits_from_width(width_i64)?;
    numeric_try_uint(input, bits).and_then(|b| b.to_u32())
}

#[inline]
pub fn uint_bin_pipeline_decimal_str_u32(s: &str, width_i64: i64) -> Option<u32> {
    let bi: BigInt = s.parse().ok()?;
    uint_bin_pipeline_u32(NumericInput::BigInt(&bi), width_i64)
}

/// `float(·, m)` with validated float width.
#[inline]
pub fn float_bin_pipeline(input: NumericInput<'_>, width_i64: i64) -> Option<CanonicalFloat64> {
    let fw = validate_float_width(width_i64).ok()?;
    numeric_try_float(input, fw)
}

#[inline]
pub fn float_bin_pipeline_parse_f64(s: &str, width_i64: i64) -> Option<CanonicalFloat64> {
    let x: f64 = s.parse().ok()?;
    float_bin_pipeline(NumericInput::F64(x), width_i64)
}

/// `fixed(·, m)` with validated place count.
#[inline]
pub fn fixed_bin_pipeline(input: NumericInput<'_>, width_i64: i64) -> Option<CanonicalFixedPoint> {
    let pl = validate_fixed_places(width_i64).ok()?;
    numeric_try_fixed(input, pl)
}

#[inline]
pub fn bigint_unary_pipeline(input: NumericInput<'_>) -> Option<CanonicalBigInt> {
    numeric_try_bigint(input)
}

#[inline]
pub fn bigint_unary_pipeline_decimal_str(s: &str) -> Option<CanonicalBigInt> {
    let bi: BigInt = s.parse().ok()?;
    numeric_try_bigint(NumericInput::BigInt(&bi))
}

#[inline]
pub fn bigrat_unary_pipeline(input: NumericInput<'_>) -> Option<CanonicalBigRat> {
    numeric_try_bigrat(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numeric_try_bigint_from_large_f64() {
        let x = 3.14e100_f64;
        let out = numeric_try_bigint(NumericInput::F64(x));
        assert!(out.is_some(), "bigint from finite huge float should succeed");
    }
}
