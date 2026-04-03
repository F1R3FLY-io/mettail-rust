//! Language-agnostic numeric casting: [`NumericInput`] carries tagged payloads from any
//! front-end; [`numeric_try_*`] and `*_pipeline_*` implement semantics via [`crate::numeric_cast`].
//!
//! Language crates map their `Proc` (or similar) into [`NumericInput`], then call pipelines here.
//! No `language!` types appear in this module.

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{Num, ToPrimitive, Zero};

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
    if let Ok(x) = s.parse::<f64>() {
        return float_bin_pipeline(NumericInput::F64(x), width_i64);
    }
    if let Some(fp) = parse_fixed_point_str(s) {
        return float_bin_pipeline(NumericInput::Fixed(&fp), width_i64);
    }
    if let Some(bi) = parse_bigint_n_suffix_str(s) {
        return float_bin_pipeline(NumericInput::BigInt(&bi), width_i64);
    }
    if let Some(r) = parse_rational_str(s) {
        return float_bin_pipeline(NumericInput::BigRat(&r), width_i64);
    }
    None
}

/// `…n` surface form (optional `_` in digit runs), same radix rules as integer literals.
fn parse_bigint_n_suffix_str(s: &str) -> Option<BigInt> {
    let cleaned: String = s.chars().filter(|&c| c != '_').collect();
    let t = cleaned.trim();
    let body = t.strip_suffix('n')?;
    if body.is_empty() {
        return None;
    }
    parse_bigint_with_optional_sign_and_radix(body)
}

/// Fixed literal / display form: `<mantissa>p<scale>` (decimal mantissa, optional dot).
fn parse_fixed_point_str(s: &str) -> Option<CanonicalFixedPoint> {
    let cleaned: String = s.chars().filter(|&c| c != '_').collect();
    let text = cleaned.as_str();

    let p_pos = text.rfind('p')?;
    if p_pos == 0 {
        return None;
    }

    let scale_str = &text[p_pos + 1..];
    if scale_str.is_empty() || !scale_str.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let scale: u32 = scale_str.parse().ok()?;

    let mantissa = &text[..p_pos];
    if mantissa.is_empty() || mantissa == "." || mantissa == "-" || mantissa == "-." {
        return None;
    }

    let neg = mantissa.starts_with('-');
    let m = mantissa.strip_prefix('-').unwrap_or(mantissa);

    let (whole, frac) = if let Some(dot) = m.find('.') {
        let w = &m[..dot];
        let f = &m[dot + 1..];
        if f.contains('.') {
            return None;
        }
        (w, f)
    } else {
        (m, "")
    };

    if !frac.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    if !whole.is_empty() && !whole.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    if whole.is_empty() && frac.is_empty() {
        return None;
    }

    let whole_bi = if whole.is_empty() {
        BigInt::from(0)
    } else {
        BigInt::from_str_radix(whole, 10).ok()?
    };
    let fd = frac.len() as u32;
    let frac_bi = if frac.is_empty() {
        BigInt::from(0)
    } else {
        BigInt::from_str_radix(frac, 10).ok()?
    };

    let ten = BigInt::from(10u32);
    let unscaled_mantissa = whole_bi * ten.clone().pow(fd) + frac_bi;

    if scale < fd {
        return None;
    }
    let mut unscaled = unscaled_mantissa * ten.pow(scale - fd);
    if neg {
        unscaled = -unscaled;
    }

    Some(CanonicalFixedPoint::new(unscaled, scale))
}

fn parse_rational_str(s: &str) -> Option<Ratio<BigInt>> {
    let cleaned: String = s.chars().filter(|&c| c != '_').collect();
    let t = cleaned.trim();
    if let Some(idx) = t.find('/') {
        let left = &t[..idx];
        let right = &t[idx + 1..];
        let n = parse_rational_side(left)?;
        let d = parse_rational_side(right)?;
        if d.is_zero() {
            return None;
        }
        Some(Ratio::new(n, d))
    } else {
        let n = parse_rational_side(t)?;
        Some(Ratio::new(n, BigInt::from(1)))
    }
}

fn parse_rational_side(side: &str) -> Option<BigInt> {
    let body = side.trim().strip_suffix('r')?;
    parse_bigint_with_optional_sign_and_radix(body)
}

fn parse_bigint_with_optional_sign_and_radix(s: &str) -> Option<BigInt> {
    let (neg, rest) = if let Some(x) = s.strip_prefix('-') {
        (true, x)
    } else if let Some(x) = s.strip_prefix('+') {
        (false, x)
    } else {
        (false, s)
    };
    let (radix, digits) = if let Some(h) = rest.strip_prefix("0x") {
        (16, h)
    } else if let Some(o) = rest.strip_prefix("0o") {
        (8, o)
    } else if let Some(b) = rest.strip_prefix("0b") {
        (2, b)
    } else {
        (10, rest)
    };
    if digits.is_empty() {
        return None;
    }
    let n = BigInt::from_str_radix(digits, radix).ok()?;
    Some(if neg { -n } else { n })
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

    #[test]
    fn float_pipeline_parses_rational_string() {
        let out = float_bin_pipeline_parse_f64("1r/2r", 32).expect("cast");
        assert_eq!(out.get(), 0.5);
    }

    #[test]
    fn float_pipeline_parses_bigint_n_string() {
        let out = float_bin_pipeline_parse_f64("1000n", 64).expect("cast");
        assert_eq!(out.get(), 1000.0);
    }

    #[test]
    fn float_pipeline_parses_fixed_p_string() {
        let out = float_bin_pipeline_parse_f64("1000.1p1", 64).expect("cast");
        assert_eq!(out.get(), 1000.1);
    }
}
