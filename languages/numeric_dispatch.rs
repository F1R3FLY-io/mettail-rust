//! Proc-level numeric cast glue: map each language’s `Proc` to [`mettail_runtime::NumericInput`],
//! then delegate to **language-agnostic** pipelines in [`mettail_runtime::numeric_cast_dispatch`].
//!
//! This file lives next to `src/` (not under `src/`) so `languages/src` stays reserved for `language!` definitions.
//! Adding another language: implement [`PeelForNumericCast`], [`ProcToNumericInput`], and `CastWidth`
//! for its `Proc`, then add thin `try_*` wrappers like the Calculator/RhoCalc ones below.

use mettail_runtime::{
    bigint_unary_pipeline, bigint_unary_pipeline_decimal_str, bigrat_unary_pipeline,
    bigrat_unary_pipeline_numeric_str, fixed_bin_pipeline, fixed_bin_pipeline_numeric_str,
    float_bin_pipeline, float_bin_pipeline_parse_f64, int_bin_pipeline_decimal_str_i32,
    int_bin_pipeline_decimal_str_i64, int_bin_pipeline_i32, int_bin_pipeline_i64,
    uint_bin_pipeline_decimal_str_u32, uint_bin_pipeline_u32, NumericInput,
};

// ---------------------------------------------------------------------------
// Width parameters (`m` in `int(_, m)`)
// ---------------------------------------------------------------------------

pub trait CastWidth {
    fn into_width_i64(self) -> Option<i64>;
}

impl CastWidth for i32 {
    fn into_width_i64(self) -> Option<i64> {
        Some(self as i64)
    }
}

impl CastWidth for i64 {
    fn into_width_i64(self) -> Option<i64> {
        Some(self)
    }
}

// ---------------------------------------------------------------------------
// Calculator
// ---------------------------------------------------------------------------

use crate::calculator::{
    BigInt as CalcBigInt, BigRat as CalcBigRat, Bool as CalcBool, Fixed as CalcFixed,
    Float as CalcFloat, Int as CalcInt, List as CalcList, Proc as CalcProc, Str as CalcStr,
    UInt32 as CalcUInt32,
};

impl CastWidth for CalcInt {
    fn into_width_i64(self) -> Option<i64> {
        match self {
            CalcInt::NumLit(b) => Some(b as i64),
            CalcInt::CastErrInt => None,
            _ => None,
        }
    }
}

impl CastWidth for &CalcInt {
    fn into_width_i64(self) -> Option<i64> {
        match self {
            CalcInt::NumLit(b) => Some(*b as i64),
            CalcInt::CastErrInt => None,
            _ => None,
        }
    }
}

#[inline]
pub(crate) fn calc_peel_list_elem<'a>(p: &'a CalcProc) -> &'a CalcProc {
    match p {
        CalcProc::ElemList(list, index) => {
            let idx = match index.as_ref() {
                CalcInt::NumLit(n) => *n as usize,
                _ => panic!("ElemList: expected Int literal"),
            };
            match list.as_ref() {
                CalcList::ListLit(v) => v.get(idx).expect("ElemList: index out of bounds"),
                _ => panic!("ElemList: list not a literal"),
            }
        },
        _ => p,
    }
}

pub(crate) fn calculator_proc_to_numeric_input(p: &CalcProc) -> Option<NumericInput<'_>> {
    Some(match p {
        CalcProc::ProcBool(b) => match b.as_ref() {
            CalcBool::BoolLit(v) => NumericInput::I32(if *v { 1 } else { 0 }),
            _ => return None,
        },
        CalcProc::ProcInt(i) => match i.as_ref() {
            CalcInt::NumLit(n) => NumericInput::I32(*n),
            CalcInt::IntBin(inner_a, inner_w) => {
                let n = calc_try_int_bin(inner_a, inner_w.as_ref())?;
                NumericInput::I32(n)
            },
            _ => return None,
        },
        CalcProc::ProcUInt32(u) => match u.as_ref() {
            CalcUInt32::NumLit(n) => NumericInput::U32(*n),
            CalcUInt32::UIntBin(inner_a, inner_w) => {
                let n = calc_try_uint_bin(inner_a, inner_w.as_ref())?;
                NumericInput::U32(n)
            },
            _ => return None,
        },
        CalcProc::ProcBigInt(b) => match b.as_ref() {
            CalcBigInt::NumLit(n) => NumericInput::BigInt(n.get()),
            _ => return None,
        },
        CalcProc::ProcBigRat(r) => match r.as_ref() {
            CalcBigRat::RatLit(rat) => NumericInput::BigRat(rat.get()),
            _ => return None,
        },
        CalcProc::ProcFixed(x) => match x.as_ref() {
            CalcFixed::FixedLit(fp) => NumericInput::Fixed(fp),
            CalcFixed::CastErrFixed => return None,
            _ => return None,
        },
        CalcProc::ProcFloat(f) => match f.as_ref() {
            CalcFloat::FloatLit(cf) => NumericInput::F64(cf.get()),
            CalcFloat::FloatBin(inner_a, inner_w) => {
                let cf = calc_try_float_bin(inner_a, inner_w.as_ref())?;
                NumericInput::F64(cf.get())
            },
            CalcFloat::CastErrFloat => return None,
            _ => return None,
        },
        _ => return None,
    })
}

pub(crate) fn calc_try_int_bin<W: CastWidth>(a: &CalcProc, w: W) -> Option<i32> {
    let width = w.into_width_i64()?;
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => int_bin_pipeline_decimal_str_i32(st, width),
            _ => None,
        };
    }
    if let CalcProc::ProcInt(i) = a {
        if let CalcInt::IntBin(inner_a, inner_w) = i.as_ref() {
            let n = calc_try_int_bin(inner_a, inner_w.as_ref())?;
            return int_bin_pipeline_i32(NumericInput::I32(n), width);
        }
    }
    let input = calculator_proc_to_numeric_input(a)?;
    int_bin_pipeline_i32(input, width)
}

pub(crate) fn calc_try_uint_bin<W: CastWidth>(a: &CalcProc, w: W) -> Option<u32> {
    let width = w.into_width_i64()?;
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => uint_bin_pipeline_decimal_str_u32(st, width),
            _ => None,
        };
    }
    let input = calculator_proc_to_numeric_input(a)?;
    uint_bin_pipeline_u32(input, width)
}

pub(crate) fn calc_try_float_bin<W: CastWidth>(
    a: &CalcProc,
    w: W,
) -> Option<mettail_runtime::CanonicalFloat64> {
    let width = w.into_width_i64()?;
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => float_bin_pipeline_parse_f64(st, width),
            _ => None,
        };
    }
    if let CalcProc::ProcBigRat(r) = a {
        // Allow casts from computed BigRat expressions (e.g. 1r/4r), not only RatLit payloads.
        let rat = r.as_ref().eval();
        return float_bin_pipeline(NumericInput::BigRat(rat.get()), width);
    }
    let input = calculator_proc_to_numeric_input(a)?;
    float_bin_pipeline(input, width)
}

pub(crate) fn calc_try_fixed_bin<W: CastWidth>(
    a: &CalcProc,
    w: W,
) -> Option<mettail_runtime::CanonicalFixedPoint> {
    let width = w.into_width_i64()?;
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => fixed_bin_pipeline_numeric_str(st, width),
            _ => None,
        };
    }
    let input = calculator_proc_to_numeric_input(a)?;
    fixed_bin_pipeline(input, width)
}

pub(crate) fn calc_try_bigint_unary(a: &CalcProc) -> Option<mettail_runtime::CanonicalBigInt> {
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => bigint_unary_pipeline_decimal_str(st),
            _ => None,
        };
    }
    if let CalcProc::ProcFixed(x) = a {
        if let CalcFixed::FixedBin(inner_a, inner_w) = x.as_ref() {
            let fp = calc_try_fixed_bin(inner_a, inner_w.as_ref())?;
            return bigint_unary_pipeline(NumericInput::Fixed(&fp));
        }
    }
    let input = calculator_proc_to_numeric_input(a)?;
    bigint_unary_pipeline(input)
}

pub(crate) fn calc_try_bigrat_unary(a: &CalcProc) -> Option<mettail_runtime::CanonicalBigRat> {
    let a = calc_peel_list_elem(a);
    if let CalcProc::ProcStr(s) = a {
        return match s.as_ref() {
            CalcStr::StringLit(st) => bigrat_unary_pipeline_numeric_str(st),
            _ => None,
        };
    }
    if let CalcProc::ProcFixed(x) = a {
        if let CalcFixed::FixedBin(inner_a, inner_w) = x.as_ref() {
            let fp = calc_try_fixed_bin(inner_a, inner_w.as_ref())?;
            return bigrat_unary_pipeline(NumericInput::Fixed(&fp));
        }
    }
    let input = calculator_proc_to_numeric_input(a)?;
    bigrat_unary_pipeline(input)
}

// ---------------------------------------------------------------------------
// RhoCalc
// ---------------------------------------------------------------------------

use crate::rhocalc::{
    BigInt as RhoBigInt, BigRat as RhoBigRat, Bool as RhoBool, Fixed as RhoFixed,
    Float as RhoFloat, Int as RhoInt, Proc as RhoProc, Str as RhoStr, UInt32 as RhoUInt32,
};

impl CastWidth for RhoInt {
    fn into_width_i64(self) -> Option<i64> {
        match self {
            RhoInt::NumLit(b) => i64::try_from(b).ok(),
            _ => None,
        }
    }
}

impl CastWidth for &RhoInt {
    fn into_width_i64(self) -> Option<i64> {
        match self {
            RhoInt::NumLit(b) => i64::try_from(*b).ok(),
            _ => None,
        }
    }
}

pub(crate) fn rhocalc_proc_to_numeric_input(p: &RhoProc) -> Option<NumericInput<'_>> {
    Some(match p {
        RhoProc::CastBool(b) => match b.as_ref() {
            RhoBool::BoolLit(v) => NumericInput::I32(if *v { 1 } else { 0 }),
            _ => return None,
        },
        RhoProc::CastInt(i) => match i.as_ref() {
            RhoInt::NumLit(n) => NumericInput::I64(*n),
            _ => return None,
        },
        RhoProc::CastUInt32(u) => match u.as_ref() {
            RhoUInt32::NumLit(n) => NumericInput::U32(*n),
            _ => return None,
        },
        RhoProc::CastBigInt(b) => match b.as_ref() {
            RhoBigInt::NumLit(n) => NumericInput::BigInt(n.get()),
            _ => return None,
        },
        RhoProc::CastBigRat(r) => match r.as_ref() {
            RhoBigRat::RatLit(rat) => NumericInput::BigRat(rat.get()),
            _ => return None,
        },
        RhoProc::CastFixed(x) => match x.as_ref() {
            RhoFixed::FixedLit(fp) => NumericInput::Fixed(fp),
            _ => return None,
        },
        RhoProc::CastFloat(f) => match f.as_ref() {
            RhoFloat::FloatLit(cf) => NumericInput::F64(cf.get()),
            _ => return None,
        },
        RhoProc::IntBinProc(inner_a, inner_w) => {
            let n = rho_try_int_bin(inner_a, inner_w.as_ref())?;
            NumericInput::I64(n)
        },
        RhoProc::FloatBinProc(inner_a, inner_w) => {
            let cf = rho_try_float_bin(inner_a, inner_w.as_ref())?;
            NumericInput::F64(cf.get())
        },
        _ => return None,
    })
}

pub(crate) fn rho_try_int_bin<W: CastWidth>(a: &RhoProc, w: W) -> Option<i64> {
    let width = w.into_width_i64()?;
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => int_bin_pipeline_decimal_str_i64(st, width),
            _ => None,
        };
    }
    if let RhoProc::IntBinProc(inner_a, inner_w) = a {
        let n = rho_try_int_bin(inner_a, inner_w.as_ref())?;
        return int_bin_pipeline_i64(NumericInput::I64(n), width);
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    int_bin_pipeline_i64(input, width)
}

pub(crate) fn rho_try_uint_bin<W: CastWidth>(a: &RhoProc, w: W) -> Option<u32> {
    let width = w.into_width_i64()?;
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => uint_bin_pipeline_decimal_str_u32(st, width),
            _ => None,
        };
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    uint_bin_pipeline_u32(input, width)
}

pub(crate) fn rho_try_float_bin<W: CastWidth>(
    a: &RhoProc,
    w: W,
) -> Option<mettail_runtime::CanonicalFloat64> {
    let width = w.into_width_i64()?;
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => float_bin_pipeline_parse_f64(st, width),
            _ => None,
        };
    }
    if let RhoProc::CastBigRat(r) = a {
        // Symmetry with Calculator: support casts from computed rational expressions.
        let rat = r.as_ref().eval();
        return float_bin_pipeline(NumericInput::BigRat(rat.get()), width);
    }
    if let RhoProc::FloatBinProc(inner_a, inner_w) = a {
        let cf = rho_try_float_bin(inner_a, inner_w.as_ref())?;
        return float_bin_pipeline(NumericInput::F64(cf.get()), width);
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    float_bin_pipeline(input, width)
}

pub(crate) fn rho_try_fixed_bin<W: CastWidth>(
    a: &RhoProc,
    w: W,
) -> Option<mettail_runtime::CanonicalFixedPoint> {
    let width = w.into_width_i64()?;
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => fixed_bin_pipeline_numeric_str(st, width),
            _ => None,
        };
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    fixed_bin_pipeline(input, width)
}

pub(crate) fn rho_try_bigint_unary(a: &RhoProc) -> Option<mettail_runtime::CanonicalBigInt> {
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => bigint_unary_pipeline_decimal_str(st),
            _ => None,
        };
    }
    if let RhoProc::FixedBinProc(inner_a, inner_w) = a {
        let fp = rho_try_fixed_bin(inner_a, inner_w.as_ref())?;
        return bigint_unary_pipeline(NumericInput::Fixed(&fp));
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    bigint_unary_pipeline(input)
}

pub(crate) fn rho_try_bigrat_unary(a: &RhoProc) -> Option<mettail_runtime::CanonicalBigRat> {
    if let RhoProc::CastStr(s) = a {
        return match s.as_ref() {
            RhoStr::StringLit(st) => bigrat_unary_pipeline_numeric_str(st),
            _ => None,
        };
    }
    if let RhoProc::FixedBinProc(inner_a, inner_w) = a {
        let fp = rho_try_fixed_bin(inner_a, inner_w.as_ref())?;
        return bigrat_unary_pipeline(NumericInput::Fixed(&fp));
    }
    let input = rhocalc_proc_to_numeric_input(a)?;
    bigrat_unary_pipeline(input)
}

pub(crate) fn rho_proc_int_bin<W: CastWidth>(a: &RhoProc, w: W) -> RhoProc {
    match rho_try_int_bin(a, w) {
        Some(n) => RhoProc::CastInt(Box::new(RhoInt::NumLit(n))),
        None => RhoProc::Err,
    }
}

pub(crate) fn rho_proc_uint_bin<W: CastWidth>(a: &RhoProc, w: W) -> RhoProc {
    match rho_try_uint_bin(a, w) {
        Some(n) => RhoProc::CastUInt32(Box::new(RhoUInt32::NumLit(n))),
        None => RhoProc::Err,
    }
}

pub(crate) fn rho_proc_float_bin<W: CastWidth>(a: &RhoProc, w: W) -> RhoProc {
    match rho_try_float_bin(a, w) {
        Some(cf) => RhoProc::CastFloat(Box::new(RhoFloat::FloatLit(cf))),
        None => RhoProc::Err,
    }
}

pub(crate) fn rho_proc_fixed_bin<W: CastWidth>(a: &RhoProc, w: W) -> RhoProc {
    match rho_try_fixed_bin(a, w) {
        Some(fp) => RhoProc::CastFixed(Box::new(RhoFixed::FixedLit(fp))),
        None => RhoProc::Err,
    }
}

pub(crate) fn rho_proc_bigint_unary(a: &RhoProc) -> RhoProc {
    match rho_try_bigint_unary(a) {
        Some(n) => RhoProc::CastBigInt(Box::new(RhoBigInt::NumLit(n))),
        None => RhoProc::Err,
    }
}

pub(crate) fn rho_proc_bigrat_unary(a: &RhoProc) -> RhoProc {
    match rho_try_bigrat_unary(a) {
        Some(r) => RhoProc::CastBigRat(Box::new(RhoBigRat::RatLit(r))),
        None => RhoProc::Err,
    }
}
