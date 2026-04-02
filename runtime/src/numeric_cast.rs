//! Explicit numeric casts: width validation, rounding, modular narrowing, and errors.
//!
//! See `docs/design/made/native-types/numeric-casting.md`.

use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::{CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat64};

/// Upper bound on `m` (bit width) for `int`/`uint` to avoid huge allocations.
pub const MAX_INT_UINT_WIDTH: u32 = 4096;

/// Upper bound on decimal `places` for `fixed(arg, m)`.
pub const MAX_FIXED_PLACES: i64 = u32::MAX as i64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastError {
    InvalidWidth,
    NonFinite,
    IntegerOverflow,
    UnsupportedFloatWidth,
    InvalidFixedPlaces,
}

/// `m` must be a power of two and at least 8 (per language spec: 2^n, n ≥ 3).
pub fn validate_int_uint_width(m: i64) -> Result<u32, CastError> {
    if m < 8 {
        return Err(CastError::InvalidWidth);
    }
    if m > MAX_INT_UINT_WIDTH as i64 {
        return Err(CastError::InvalidWidth);
    }
    let mu = m as u64;
    if !mu.is_power_of_two() {
        return Err(CastError::InvalidWidth);
    }
    Ok(mu as u32)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatCastWidth {
    F32,
    F64,
}

pub fn validate_float_width(m: i64) -> Result<FloatCastWidth, CastError> {
    match m {
        32 => Ok(FloatCastWidth::F32),
        64 => Ok(FloatCastWidth::F64),
        80 | 128 | 256 => Err(CastError::UnsupportedFloatWidth),
        _ => Err(CastError::InvalidWidth),
    }
}

pub fn validate_fixed_places(m: i64) -> Result<u32, CastError> {
    if !(0..=MAX_FIXED_PLACES).contains(&m) {
        return Err(CastError::InvalidFixedPlaces);
    }
    Ok(m as u32)
}

fn require_finite_f64(x: f64) -> Result<(), CastError> {
    if x.is_finite() {
        Ok(())
    } else {
        Err(CastError::NonFinite)
    }
}

/// Exact value of a finite `f64` as a reduced rational.
pub fn f64_to_exact_rational(x: f64) -> Result<Ratio<num_bigint::BigInt>, CastError> {
    use num_bigint::BigInt;
    require_finite_f64(x)?;
    let bits = x.to_bits();
    let neg = (bits >> 63) != 0;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let mant = bits & 0xfffffffffffff;
    let r = if exp == 0 {
        if mant == 0 {
            Ratio::from_integer(BigInt::zero())
        } else {
            Ratio::new(BigInt::from(mant), BigInt::from(1u32) << 1074)
        }
    } else if exp == 2047 {
        return Err(CastError::NonFinite);
    } else {
        let significand = mant | (1u64 << 52);
        let e = exp - 1075;
        if e >= 0 {
            Ratio::from_integer(BigInt::from(significand) << e as u32)
        } else {
            let den_shift = (-e) as u32;
            Ratio::new(BigInt::from(significand), BigInt::from(1u32) << den_shift)
        }
    };
    let r = if neg { -r } else { r };
    Ok(r)
}

fn floor_ratio(r: &Ratio<num_bigint::BigInt>) -> num_bigint::BigInt {
    r.numer().div_floor(r.denom())
}

fn signed_range_for_bits(bits: u32) -> (num_bigint::BigInt, num_bigint::BigInt) {
    use num_bigint::BigInt;
    if bits == 0 {
        return (BigInt::zero(), BigInt::zero());
    }
    let hi = (BigInt::one() << (bits as usize - 1)) - 1u32;
    let lo = -(BigInt::one() << (bits as usize - 1));
    (lo, hi)
}

fn unsigned_max_for_bits(bits: u32) -> num_bigint::BigInt {
    use num_bigint::BigInt;
    (BigInt::one() << bits as usize) - 1u32
}

fn in_signed_range(k: &num_bigint::BigInt, bits: u32) -> bool {
    let (lo, hi) = signed_range_for_bits(bits);
    k >= &lo && k <= &hi
}

fn in_unsigned_range(k: &num_bigint::BigInt, bits: u32) -> bool {
    k.sign() != num_bigint::Sign::Minus && k <= &unsigned_max_for_bits(bits)
}

/// Two's-complement modular reduction to signed `bits`-bit integer as [`BigInt`] in range.
pub fn signed_modular(n: &num_bigint::BigInt, bits: u32) -> num_bigint::BigInt {
    use num_bigint::BigInt;
    let mask = BigInt::one() << bits as usize;
    let half = BigInt::one() << (bits as usize - 1);
    let mut u = n % &mask;
    if u.sign() == num_bigint::Sign::Minus {
        u += &mask;
    }
    if u >= half {
        u - mask
    } else {
        u
    }
}

/// Unsigned reduction modulo `2^bits` as nonnegative [`BigInt`].
pub fn unsigned_modular(n: &num_bigint::BigInt, bits: u32) -> num_bigint::BigInt {
    use num_bigint::BigInt;
    let mask = BigInt::one() << bits as usize;
    let mut u = n % &mask;
    if u.sign() == num_bigint::Sign::Minus {
        u += &mask;
    }
    u
}

// --- int(arg, m) ---

/// Integer-typed source: modular narrowing.
pub fn cast_int_from_bigint(n: &num_bigint::BigInt, bits: u32) -> num_bigint::BigInt {
    signed_modular(n, bits)
}

pub fn cast_int_from_i64(n: i64, bits: u32) -> num_bigint::BigInt {
    cast_int_from_bigint(&num_bigint::BigInt::from(n), bits)
}

pub fn cast_int_from_u32(n: u32, bits: u32) -> num_bigint::BigInt {
    signed_modular(&num_bigint::BigInt::from(n), bits)
}

/// Float source: floor, then value must fit signed `bits` (no modular).
pub fn cast_int_from_f64(x: f64, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    require_finite_f64(x)?;
    let r = f64_to_exact_rational(x)?;
    let k = floor_ratio(&r);
    if !in_signed_range(&k, bits) {
        return Err(CastError::IntegerOverflow);
    }
    Ok(k)
}

pub fn cast_int_from_bigrat(r: &Ratio<num_bigint::BigInt>, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    if r.denom().is_one() {
        return Ok(signed_modular(r.numer(), bits));
    }
    let k = floor_ratio(r);
    if !in_signed_range(&k, bits) {
        return Err(CastError::IntegerOverflow);
    }
    Ok(k)
}

pub fn cast_int_from_fixed(fp: &CanonicalFixedPoint, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    let r = fp.value_ratio();
    cast_int_from_bigrat(&r, bits)
}

// --- uint(arg, m) ---

pub fn cast_uint_from_bigint(n: &num_bigint::BigInt, bits: u32) -> num_bigint::BigInt {
    unsigned_modular(n, bits)
}

pub fn cast_uint_from_u32(n: u32, bits: u32) -> num_bigint::BigInt {
    unsigned_modular(&num_bigint::BigInt::from(n), bits)
}

pub fn cast_uint_from_i64(n: i64, bits: u32) -> num_bigint::BigInt {
    unsigned_modular(&num_bigint::BigInt::from(n), bits)
}

pub fn cast_uint_from_f64(x: f64, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    require_finite_f64(x)?;
    let r = f64_to_exact_rational(x)?;
    let mut k = floor_ratio(&r);
    if k < num_bigint::BigInt::zero() {
        k = num_bigint::BigInt::zero();
    }
    if !in_unsigned_range(&k, bits) {
        return Err(CastError::IntegerOverflow);
    }
    Ok(k)
}

pub fn cast_uint_from_bigrat(r: &Ratio<num_bigint::BigInt>, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    if r.denom().is_one() {
        return Ok(unsigned_modular(r.numer(), bits));
    }
    let mut k = floor_ratio(r);
    if k < num_bigint::BigInt::zero() {
        k = num_bigint::BigInt::zero();
    }
    if !in_unsigned_range(&k, bits) {
        return Err(CastError::IntegerOverflow);
    }
    Ok(k)
}

pub fn cast_uint_from_fixed(fp: &CanonicalFixedPoint, bits: u32) -> Result<num_bigint::BigInt, CastError> {
    let r = fp.value_ratio();
    cast_uint_from_bigrat(&r, bits)
}

// --- bigint(arg) ---

pub fn cast_bigint_from_f64(x: f64) -> Result<num_bigint::BigInt, CastError> {
    require_finite_f64(x)?;
    // User-facing bigint(float) should align with float display semantics, not raw
    // binary mantissa artifacts. Parse the canonical float string and floor exactly.
    let s = CanonicalFloat64::from(x).to_string();
    floor_decimal_scientific_str_to_bigint(&s)
}

fn floor_decimal_scientific_str_to_bigint(s: &str) -> Result<num_bigint::BigInt, CastError> {
    let s = s.trim();
    if s.is_empty() {
        return Err(CastError::IntegerOverflow);
    }

    let (neg, rest) = if let Some(r) = s.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = s.strip_prefix('+') {
        (false, r)
    } else {
        (false, s)
    };

    let (mantissa, exp10): (&str, i64) = if let Some(i) = rest.find(['e', 'E']) {
        let (m, epart) = rest.split_at(i);
        let e = epart[1..]
            .parse::<i64>()
            .map_err(|_| CastError::IntegerOverflow)?;
        (m, e)
    } else {
        (rest, 0)
    };

    let (int_part, frac_part) = if let Some(dot) = mantissa.find('.') {
        (&mantissa[..dot], &mantissa[dot + 1..])
    } else {
        (mantissa, "")
    };

    if int_part.is_empty() && frac_part.is_empty() {
        return Err(CastError::IntegerOverflow);
    }
    if !int_part.chars().all(|c| c.is_ascii_digit()) || !frac_part.chars().all(|c| c.is_ascii_digit())
    {
        return Err(CastError::IntegerOverflow);
    }

    let mut digits = String::with_capacity(int_part.len() + frac_part.len());
    digits.push_str(int_part);
    digits.push_str(frac_part);
    if digits.is_empty() {
        digits.push('0');
    }
    let coeff = digits
        .parse::<num_bigint::BigInt>()
        .map_err(|_| CastError::IntegerOverflow)?;

    // value = coeff * 10^(exp10 - frac_len)
    let scale = frac_part.len() as i64 - exp10;
    if scale <= 0 {
        let mul = num_bigint::BigInt::from(10u32).pow((-scale) as u32);
        let n = coeff * mul;
        return Ok(if neg { -n } else { n });
    }

    let div = num_bigint::BigInt::from(10u32).pow(scale as u32);
    if neg {
        // floor(-a/b) = -ceil(a/b)
        let q = (&coeff + (&div - 1u32)) / &div;
        Ok(-q)
    } else {
        Ok(coeff / div)
    }
}

pub fn cast_bigint_from_bigrat(r: &Ratio<num_bigint::BigInt>) -> num_bigint::BigInt {
    floor_ratio(r)
}

pub fn cast_bigint_from_fixed(fp: &CanonicalFixedPoint) -> num_bigint::BigInt {
    floor_ratio(&fp.value_ratio())
}

// --- bigrat(arg) ---

pub fn cast_bigrat_from_f64(x: f64) -> Result<CanonicalBigRat, CastError> {
    let r = f64_to_exact_rational(x)?;
    Ok(CanonicalBigRat::from(r))
}

pub fn cast_bigrat_from_fixed(fp: &CanonicalFixedPoint) -> CanonicalBigRat {
    let r = fp.value_ratio();
    CanonicalBigRat::from(r)
}

pub fn cast_bigrat_from_bigint(n: &num_bigint::BigInt) -> CanonicalBigRat {
    CanonicalBigRat::from(Ratio::from_integer(n.clone()))
}

pub fn cast_bigrat_from_u32(n: u32) -> CanonicalBigRat {
    CanonicalBigRat::from(Ratio::from_integer(num_bigint::BigInt::from(n)))
}

pub fn cast_bigrat_from_i64(n: i64) -> CanonicalBigRat {
    CanonicalBigRat::from(Ratio::from_integer(num_bigint::BigInt::from(n)))
}

// --- float(arg, m) ---

pub fn cast_float_from_f64(x: f64, width: FloatCastWidth) -> Result<CanonicalFloat64, CastError> {
    require_finite_f64(x)?;
    Ok(match width {
        FloatCastWidth::F64 => CanonicalFloat64::from(x),
        FloatCastWidth::F32 => {
            let xf = x as f32;
            CanonicalFloat64::from(f64::from(xf))
        }
    })
}

/// Nearest float; allows non-finite (±Inf) when magnitude overflows narrow format.
pub fn cast_float_from_f64_allow_nonfinite(x: f64, width: FloatCastWidth) -> CanonicalFloat64 {
    match width {
        FloatCastWidth::F64 => CanonicalFloat64::from(x),
        FloatCastWidth::F32 => {
            if x.is_nan() {
                CanonicalFloat64::from(f64::from(f32::NAN))
            } else {
                CanonicalFloat64::from(f64::from(x as f32))
            }
        }
    }
}

pub fn cast_float_from_bigint(n: &num_bigint::BigInt, width: FloatCastWidth) -> CanonicalFloat64 {
    let x = n.to_f64().unwrap_or(if n.is_negative() {
        f64::NEG_INFINITY
    } else {
        f64::INFINITY
    });
    cast_float_from_f64_allow_nonfinite(x, width)
}

pub fn cast_float_from_bigrat(r: &Ratio<num_bigint::BigInt>, width: FloatCastWidth) -> CanonicalFloat64 {
    let x = r.to_f64().unwrap_or(f64::NAN);
    cast_float_from_f64_allow_nonfinite(x, width)
}

pub fn cast_float_from_fixed(fp: &CanonicalFixedPoint, width: FloatCastWidth) -> CanonicalFloat64 {
    let n = fp.unscaled();
    let places = fp.places();
    if places == 0 {
        return cast_float_from_bigint(n, width);
    }
    let scale = num_bigint::BigInt::from(10u32).pow(places);
    let r = Ratio::new(n.clone(), scale);
    cast_float_from_bigrat(&r, width)
}

// --- fixed(arg, m) ---

fn pow10_bigint(p: u32) -> num_bigint::BigInt {
    num_bigint::BigInt::from(10u32).pow(p)
}

/// Floor to `places` decimal digits after the point.
pub fn cast_fixed_from_bigrat(r: &Ratio<num_bigint::BigInt>, places: u32) -> CanonicalFixedPoint {
    let pow = pow10_bigint(places);
    let num = r.numer() * &pow;
    let unscaled = num.div_floor(r.denom());
    CanonicalFixedPoint::new(unscaled, places)
}

pub fn cast_fixed_from_f64(x: f64, places: u32) -> Result<CanonicalFixedPoint, CastError> {
    require_finite_f64(x)?;
    let r = f64_to_exact_rational(x)?;
    Ok(cast_fixed_from_bigrat(&r, places))
}

pub fn cast_fixed_from_bigint(n: &num_bigint::BigInt, places: u32) -> CanonicalFixedPoint {
    let pow = pow10_bigint(places);
    let unscaled = n * pow;
    CanonicalFixedPoint::new(unscaled, places)
}

pub fn cast_fixed_from_fixed(fp: &CanonicalFixedPoint, places: u32) -> CanonicalFixedPoint {
    let r = fp.value_ratio();
    cast_fixed_from_bigrat(&r, places)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn validate_int_uint_width_ok() {
        assert_eq!(validate_int_uint_width(8), Ok(8));
        assert_eq!(validate_int_uint_width(64), Ok(64));
    }

    #[test]
    fn validate_int_uint_width_rejects() {
        assert_eq!(validate_int_uint_width(7), Err(CastError::InvalidWidth));
        assert_eq!(validate_int_uint_width(12), Err(CastError::InvalidWidth));
        assert_eq!(validate_int_uint_width(4), Err(CastError::InvalidWidth));
        assert_eq!(validate_int_uint_width(-8), Err(CastError::InvalidWidth));
    }

    #[test]
    fn validate_float_width_cases() {
        assert_eq!(super::validate_float_width(32), Ok(FloatCastWidth::F32));
        assert_eq!(super::validate_float_width(64), Ok(FloatCastWidth::F64));
        assert_eq!(
            super::validate_float_width(128),
            Err(CastError::UnsupportedFloatWidth)
        );
        assert_eq!(
            super::validate_float_width(17),
            Err(CastError::InvalidWidth)
        );
    }

    #[test]
    fn int_from_float_floor() {
        let k = cast_int_from_f64(-3.5, 8).unwrap();
        assert_eq!(k, BigInt::from(-4i32));
    }

    #[test]
    fn int_from_float_overflow() {
        assert_eq!(
            cast_int_from_f64(1e10, 8),
            Err(CastError::IntegerOverflow)
        );
    }

    #[test]
    fn uint_from_float_floor_and_clamp() {
        assert_eq!(cast_uint_from_f64(3.5, 8).unwrap(), BigInt::from(3u32));
        assert_eq!(cast_uint_from_f64(-3.5, 8).unwrap(), BigInt::from(0u32));
    }

    #[test]
    fn uint_modular() {
        assert_eq!(
            cast_uint_from_u32(257, 8),
            BigInt::from(1u32)
        );
    }

    #[test]
    fn uint_negative_bigint_twos_complement() {
        assert_eq!(
            cast_uint_from_bigint(&BigInt::from(-1i32), 8),
            BigInt::from(255u32)
        );
    }

    #[test]
    fn non_finite_to_int() {
        assert_eq!(cast_int_from_f64(f64::NAN, 8), Err(CastError::NonFinite));
        assert_eq!(
            cast_int_from_f64(f64::INFINITY, 8),
            Err(CastError::NonFinite)
        );
    }

    #[test]
    fn float_narrow_to_inf() {
        let v = cast_float_from_f64_allow_nonfinite(1e50, FloatCastWidth::F32);
        assert!(v.get().is_infinite());
        assert!(v.get().is_sign_positive());
    }

    #[test]
    fn bigint_from_float() {
        assert_eq!(
            cast_bigint_from_f64(-3.5).unwrap(),
            BigInt::from(-4)
        );
        assert_eq!(
            cast_bigint_from_f64(1e30).unwrap(),
            "1000000000000000000000000000000"
                .parse::<BigInt>()
                .unwrap()
        );
    }

    #[test]
    fn bigrat_from_float_exact_half() {
        let r = cast_bigrat_from_f64(0.5).unwrap();
        assert_eq!(*r.get().numer(), BigInt::from(1));
        assert_eq!(*r.get().denom(), BigInt::from(2));
    }

    #[test]
    fn fixed_from_bigrat_example() {
        let r = Ratio::new(BigInt::from(349i32), BigInt::from(100i32));
        let fp = cast_fixed_from_bigrat(&r, 1);
        assert_eq!(fp.unscaled(), &BigInt::from(34i32));
        assert_eq!(fp.places(), 1);
    }

    #[test]
    fn fixed_negative_floor() {
        let r = Ratio::new(BigInt::from(-349i32), BigInt::from(100i32));
        let fp = cast_fixed_from_bigrat(&r, 1);
        assert_eq!(fp.unscaled(), &BigInt::from(-35i32));
        assert_eq!(fp.places(), 1);
    }

    #[test]
    fn int_modular_i64() {
        assert_eq!(cast_int_from_i64(257, 8), BigInt::from(1));
    }

    #[test]
    fn int_from_bigrat_integer_uses_modular() {
        let r = Ratio::from_integer(BigInt::from(1000i32));
        assert_eq!(cast_int_from_bigrat(&r, 8).unwrap(), BigInt::from(-24i32));
    }

    #[test]
    fn int_from_bigrat_nonint_uses_floor_range() {
        let r = Ratio::new(BigInt::from(10i32), BigInt::from(3i32));
        assert_eq!(cast_int_from_bigrat(&r, 8).unwrap(), BigInt::from(3i32));
        let r_big = Ratio::new(BigInt::from(1000i32), BigInt::from(3i32));
        assert_eq!(
            cast_int_from_bigrat(&r_big, 8),
            Err(CastError::IntegerOverflow)
        );
    }
}
