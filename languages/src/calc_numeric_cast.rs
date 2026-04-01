//! Numeric cast builtins for Calculator (`cast_int`, `cast_uint`, `cast_float`, `cast_fixed`,
//! `bigint`, `bigrat`). Called from `language!` HOL blocks in `calculator.rs`.
//!
//! HOL blocks return `Option<native>`; the macro maps `None` to per-category `cast_error_*` terms.

use num_traits::ToPrimitive;

use crate::calculator::{BigInt, BigRat, Fixed, Float, Int, Proc, UInt32};

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

impl IntoCastWidth for Int {
    fn into_width(self) -> Option<i32> {
        match self {
            Int::NumLit(b) => Some(b),
            Int::CastErrInt => None,
            _ => None,
        }
    }
}

impl IntoCastWidth for &Int {
    fn into_width(self) -> Option<i32> {
        match self {
            Int::NumLit(b) => Some(*b),
            Int::CastErrInt => None,
            _ => None,
        }
    }
}

fn bigint_to_i32_strict(bi: &num_bigint::BigInt) -> Option<i32> {
    bi.to_i32()
}

fn bigint_to_u32_strict(bi: &num_bigint::BigInt) -> Option<u32> {
    bi.to_u32()
}

/// `cast_int(proc, width)` → `Option<i32>`.
pub fn try_cast_int_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<i32> {
    let width = w.into_width()?;
    let bits_i64 = width_i64(width);
    let bw = mettail_runtime::validate_int_uint_width(bits_i64).ok()?;
    let bi = match a {
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_int_from_i64(*n as i64, bw),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_int_from_u32(*n, bw),
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_int_from_bigint(n.get(), bw),
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_int_from_bigrat(rat.get(), bw).ok()?,
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_int_from_fixed(fp, bw).ok()?,
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_int_from_f64(cf.get(), bw).ok()?,
            Float::CastErrFloat => return None,
            _ => return None,
        },
        _ => return None,
    };
    bigint_to_i32_strict(&bi)
}

/// `cast_uint(proc, width)` → `Option<u32>`.
pub fn try_cast_uint_bin<W: IntoCastWidth>(a: &Proc, w: W) -> Option<u32> {
    let width = w.into_width()?;
    let bits_i64 = width_i64(width);
    let bw = mettail_runtime::validate_int_uint_width(bits_i64).ok()?;
    let bi = match a {
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::unsigned_modular(
                &num_bigint::BigInt::from(*n),
                bw,
            ),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_uint_from_u32(*n, bw),
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_uint_from_bigint(n.get(), bw),
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_uint_from_bigrat(rat.get(), bw).ok()?,
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_uint_from_fixed(fp, bw).ok()?,
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_uint_from_f64(cf.get(), bw).ok()?,
            Float::CastErrFloat => return None,
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
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_float_from_bigint(
                &num_bigint::BigInt::from(*n),
                fw,
            ),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_float_from_bigint(
                &num_bigint::BigInt::from(*n),
                fw,
            ),
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_float_from_bigint(n.get(), fw),
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_float_from_bigrat(rat.get(), fw),
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_float_from_fixed(fp, fw),
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => {
                mettail_runtime::cast_float_from_f64_allow_nonfinite(cf.get(), fw)
            }
            Float::CastErrFloat => return None,
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
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_fixed_from_bigint(&num_bigint::BigInt::from(*n), pl),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => {
                mettail_runtime::cast_fixed_from_bigint(&num_bigint::BigInt::from(*n), pl)
            }
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_fixed_from_bigint(n.get(), pl),
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::cast_fixed_from_bigrat(rat.get(), pl),
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_fixed_from_fixed(fp, pl),
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_fixed_from_f64(cf.get(), pl).ok()?,
            Float::CastErrFloat => return None,
            _ => return None,
        },
        _ => return None,
    })
}

/// Unary `bigint(proc)`.
pub fn try_cast_bigint_unary(a: &Proc) -> Option<mettail_runtime::CanonicalBigInt> {
    Some(match a {
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(*n)),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(*n)),
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => *n,
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_bigrat(rat.get()),
            ),
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_fixed(fp),
            ),
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::CanonicalBigInt::from(
                mettail_runtime::cast_bigint_from_f64(cf.get()).ok()?,
            ),
            Float::CastErrFloat => return None,
            _ => return None,
        },
        _ => return None,
    })
}

/// Unary `bigrat(proc)`.
pub fn try_cast_bigrat_unary(a: &Proc) -> Option<mettail_runtime::CanonicalBigRat> {
    Some(match a {
        Proc::ProcInt(i) => match i.as_ref() {
            Int::NumLit(n) => mettail_runtime::cast_bigrat_from_i64(*n as i64),
            Int::CastErrInt => return None,
            _ => return None,
        },
        Proc::ProcUInt32(u) => match u.as_ref() {
            UInt32::NumLit(n) => mettail_runtime::cast_bigrat_from_u32(*n),
            UInt32::CastErrUInt32 => return None,
            _ => return None,
        },
        Proc::ProcBigInt(b) => match b.as_ref() {
            BigInt::NumLit(n) => mettail_runtime::cast_bigrat_from_bigint(n.get()),
            BigInt::CastErrBigInt => return None,
            _ => return None,
        },
        Proc::ProcBigRat(r) => match r.as_ref() {
            BigRat::RatLit(rat) => *rat,
            BigRat::Err => return None,
            _ => return None,
        },
        Proc::ProcFixed(x) => match x.as_ref() {
            Fixed::FixedLit(fp) => mettail_runtime::cast_bigrat_from_fixed(fp),
            Fixed::CastErrFixed => return None,
            _ => return None,
        },
        Proc::ProcFloat(f) => match f.as_ref() {
            Float::FloatLit(cf) => mettail_runtime::cast_bigrat_from_f64(cf.get()).ok()?,
            Float::CastErrFloat => return None,
            _ => return None,
        },
        _ => return None,
    })
}
