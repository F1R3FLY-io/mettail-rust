//! Numeric cast builtins for RhoCalc (`cast_int`, …). Same semantics as
//! [`calc_numeric_cast`](crate::calc_numeric_cast); `Int` literals are `i64` here.
//!
//! HOL blocks return `Option<native>`; the macro maps `None` to per-category `cast_error_*` terms.

use num_traits::ToPrimitive;

use crate::rhocalc::{BigInt, BigRat, Fixed, Float, Int, Proc, UInt32};

fn width_i64(width: i32) -> i64 {
    width as i64
}

/// Fold passes `Int`; `eval` passes `i32` after `eval()`.
pub trait IntoCastWidth {
    fn into_width(self) -> Option<i32>;
}

impl IntoCastWidth for i32 {
    fn into_width(self) -> Option<i32> {
        Some(self)
    }
}

impl IntoCastWidth for i64 {
    fn into_width(self) -> Option<i32> {
        i32::try_from(self).ok()
    }
}

impl IntoCastWidth for Int {
    fn into_width(self) -> Option<i32> {
        match self {
            Int::NumLit(b) => i32::try_from(b).ok(),
            _ => None,
        }
    }
}

impl IntoCastWidth for &Int {
    fn into_width(self) -> Option<i32> {
        match self {
            Int::NumLit(b) => i32::try_from(*b).ok(),
            _ => None,
        }
    }
}

fn bigint_to_i64_strict(bi: &num_bigint::BigInt) -> Option<i64> {
    bi.to_i64()
}

fn bigint_to_u32_strict(bi: &num_bigint::BigInt) -> Option<u32> {
    bi.to_u32()
}

/// `cast_int(proc, width)` → `Option<i64>`.
pub fn try_cast_int_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<i64> {
    let width = w.into_width()?;
    let bits_i64 = width_i64(width);
    let bw = mettail_runtime::validate_int_uint_width(bits_i64).ok()?;
    let bi = match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_int_from_i64(*n, bw),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_int_from_u32(*n, bw),
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_int_from_bigint(n.get(), bw),
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_int_from_bigrat(rat.get(), bw).ok()?,
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_int_from_fixed(fp, bw).ok()?,
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_int_from_f64(cf.get(), bw).ok()?,
            _ => return None,
        },
        _ => return None,
    };
    bigint_to_i64_strict(&bi)
}

/// `cast_uint(proc, width)` → `Option<u32>`.
pub fn try_cast_uint_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<u32> {
    let width = w.into_width()?;
    let bits_i64 = width_i64(width);
    let bw = mettail_runtime::validate_int_uint_width(bits_i64).ok()?;
    let bi = match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::unsigned_modular(
                &num_bigint::BigInt::from(*n),
                bw,
            ),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_uint_from_u32(*n, bw),
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_uint_from_bigint(n.get(), bw),
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_uint_from_bigrat(rat.get(), bw).ok()?,
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_uint_from_fixed(fp, bw).ok()?,
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_uint_from_f64(cf.get(), bw).ok()?,
            _ => return None,
        },
        _ => return None,
    };
    bigint_to_u32_strict(&bi)
}

/// `cast_float(proc, width)` → `Option<CanonicalFloat64>`.
pub fn try_cast_float_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<mettail_runtime::CanonicalFloat64> {
    let width = w.into_width()?;
    let bits_i64 = width_i64(width);
    let fw = mettail_runtime::validate_float_width(bits_i64).ok()?;
    Some(match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_float_from_bigint(
                &num_bigint::BigInt::from(*n),
                fw,
            ),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_float_from_bigint(
                &num_bigint::BigInt::from(*n),
                fw,
            ),
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_float_from_bigint(n.get(), fw),
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_float_from_bigrat(rat.get(), fw),
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_float_from_fixed(fp, fw),
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => {
                mettail_runtime::cast_float_from_f64_allow_nonfinite(cf.get(), fw)
            }
            _ => return None,
        },
        _ => return None,
    })
}

/// `cast_fixed(proc, places)` → `Option<CanonicalFixedPoint>`.
pub fn try_cast_fixed_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<mettail_runtime::CanonicalFixedPoint> {
    let width = w.into_width()?;
    let pl = mettail_runtime::validate_fixed_places(width_i64(width)).ok()?;
    Some(match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_fixed_from_bigint(&num_bigint::BigInt::from(*n), pl),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => {
                mettail_runtime::cast_fixed_from_bigint(&num_bigint::BigInt::from(*n), pl)
            }
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_fixed_from_bigint(n.get(), pl),
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_fixed_from_bigrat(rat.get(), pl),
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_fixed_from_fixed(fp, pl),
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_fixed_from_f64(cf.get(), pl).ok()?,
            _ => return None,
        },
        _ => return None,
    })
}

/// Unary `bigint(proc)`.
pub fn try_cast_bigint_unary(a: &Proc) -> Option<mettail_runtime::CanonicalBigInt> {
    Some(match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(*n)),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(*n)),
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => *n,
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_bigrat(rat.get()),
            ),
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_fixed(fp),
            ),
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_f64(cf.get()).ok()?,
            ),
            _ => return None,
        },
        _ => return None,
    })
}

/// Unary `bigrat(proc)`.
pub fn try_cast_bigrat_unary(a: &Proc) -> Option<mettail_runtime::CanonicalBigRat> {
    Some(match a {
        Proc::CastInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_bigrat_from_i64(*n),
            _ => return None,
        },
        Proc::CastUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_bigrat_from_u32(*n),
            _ => return None,
        },
        Proc::CastBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_bigrat_from_bigint(n.get()),
            _ => return None,
        },
        Proc::CastBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => *rat,
            _ => return None,
        },
        Proc::CastFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_bigrat_from_fixed(&fp),
            _ => return None,
        },
        Proc::CastFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_bigrat_from_f64(cf.get()).ok()?,
            _ => return None,
        },
        _ => return None,
    })
}

pub fn proc_cast_int_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Proc {
    match try_cast_int_bin(a, w) {
        Some(n) => Proc::CastInt(Box::new(Int::NumLit(n))),
        None => Proc::Err,
    }
}

pub fn proc_cast_uint_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Proc {
    match try_cast_uint_bin(a, w) {
        Some(n) => Proc::CastUInt32(Box::new(UInt32::NumLit(n))),
        None => Proc::Err,
    }
}

pub fn proc_cast_float_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Proc {
    match try_cast_float_bin(a, w) {
        Some(cf) => Proc::CastFloat(Box::new(Float::FloatLit(cf))),
        None => Proc::Err,
    }
}

pub fn proc_cast_fixed_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Proc {
    match try_cast_fixed_bin(a, w) {
        Some(fp) => Proc::CastFixed(Box::new(Fixed::FixedLit(fp))),
        None => Proc::Err,
    }
}

pub fn proc_cast_bigint_unary(a: &Proc) -> Proc {
    match try_cast_bigint_unary(a) {
        Some(n) => Proc::CastBigInt(Box::new(BigInt::NumLit(n))),
        None => Proc::Err,
    }
}

pub fn proc_cast_bigrat_unary(a: &Proc) -> Proc {
    match try_cast_bigrat_unary(a) {
        Some(r) => Proc::CastBigRat(Box::new(BigRat::RatLit(r))),
        None => Proc::Err,
    }
}
