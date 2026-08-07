use mettail_runtime::{
    float_bin_pipeline, float_bin_pipeline_parse_f64, int_bin_pipeline_decimal_str_i32,
    int_bin_pipeline_decimal_str_i64, int_bin_pipeline_i32, int_bin_pipeline_i64, CanonicalFloat64,
    CastWidth, NumericInput, ProcToNumericInput,
};

pub(crate) fn int_i32<P, W>(a: &P, w: W) -> Option<i32>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(text) = a.as_numeric_str() {
        return int_bin_pipeline_decimal_str_i32(text, width);
    }
    if let Some((inner, inner_width)) = a.as_int_bin() {
        let value = int_i32(inner, inner_width)?;
        return int_bin_pipeline_i32(NumericInput::I32(value), width);
    }
    int_bin_pipeline_i32(a.to_numeric_input()?, width)
}

pub(crate) fn int_i64<P, W>(a: &P, w: W) -> Option<i64>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(text) = a.as_numeric_str() {
        return int_bin_pipeline_decimal_str_i64(text, width);
    }
    if let Some((inner, inner_width)) = a.as_int_bin() {
        let value = int_i64(inner, inner_width)?;
        return int_bin_pipeline_i64(NumericInput::I64(value), width);
    }
    int_bin_pipeline_i64(a.to_numeric_input()?, width)
}

pub(crate) fn float<P, W>(a: &P, w: W) -> Option<CanonicalFloat64>
where
    P: ProcToNumericInput,
    W: CastWidth,
{
    let width = w.into_width_i64()?;
    let a = a.peel_numeric_elem();
    if let Some(text) = a.as_numeric_str() {
        return float_bin_pipeline_parse_f64(text, width);
    }
    if let Some(rational) = a.as_evaluable_bigrat() {
        return float_bin_pipeline(NumericInput::BigRat(rational.get()), width);
    }
    if let Some((inner, inner_width)) = a.as_float_bin() {
        let value = float(inner, inner_width)?;
        return float_bin_pipeline(NumericInput::F64(value.get()), width);
    }
    float_bin_pipeline(a.to_numeric_input()?, width)
}
