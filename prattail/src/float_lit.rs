//! Floating-point literal parsing: decimal / exponent forms with optional `f32` / `f64` suffix.
//!
//! `f32` is parsed and widened to [`CanonicalFloat64`]. Calculator and RhoCalc only **lex** optional
//! `f64` in their float patterns (no `f32` surface token), but other callers may still pass `f32`
//! strings into [`parse_float_lit`].

use mettail_runtime::CanonicalFloat64;

#[allow(clippy::result_unit_err)]
pub fn parse_float_lit(text: &str) -> Result<CanonicalFloat64, ()> {
    let cleaned: String = text.chars().filter(|&c| c != '_').collect();
    let s = cleaned.as_str();

    if s.ends_with("f128") || s.ends_with("f256") {
        return Err(());
    }

    let (body, as_f32) = if let Some(b) = s.strip_suffix("f64") {
        (b, false)
    } else if let Some(b) = s.strip_suffix("f32") {
        (b, true)
    } else {
        (s, false)
    };

    if body.is_empty() {
        return Err(());
    }

    let v = if as_f32 {
        let f = body.parse::<f32>().map_err(|_| ())?;
        f64::from(f)
    } else {
        body.parse::<f64>().map_err(|_| ())?
    };

    Ok(CanonicalFloat64::from(v))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_f64() {
        let x = parse_float_lit("1.5").unwrap();
        assert_eq!(x.get(), 1.5);
    }

    #[test]
    fn exponent_f32_suffix() {
        let x = parse_float_lit("-1.234e5f32").unwrap();
        assert_eq!(x.get(), -123400.0_f64);
    }

    #[test]
    fn exponent_f64_suffix() {
        let x = parse_float_lit("-1.234e5f64").unwrap();
        assert_eq!(x.get(), -123400.0_f64);
    }

    #[test]
    fn f64_suffix() {
        let x = parse_float_lit("2.0f64").unwrap();
        assert_eq!(x.get(), 2.0);
    }

    #[test]
    fn underscore_stripping() {
        let x = parse_float_lit("1_000.5").unwrap();
        assert_eq!(x.get(), 1000.5);
    }

    #[test]
    fn rejects_extended_suffix() {
        assert!(parse_float_lit("1.0f128").is_err());
        assert!(parse_float_lit("1.0f256").is_err());
    }

    #[test]
    fn leading_dot_and_negative() {
        assert_eq!(parse_float_lit(".5").unwrap().get(), 0.5);
        assert_eq!(parse_float_lit("-.5").unwrap().get(), -0.5);
        assert_eq!(parse_float_lit("-.25e1").unwrap().get(), -2.5);
    }

    #[test]
    fn exponent_forms_no_decimal_point() {
        assert_eq!(parse_float_lit("1e10").unwrap().get(), 1e10);
        assert_eq!(parse_float_lit("1E+10").unwrap().get(), 1e10);
        assert_eq!(parse_float_lit("-2.5e-3").unwrap().get(), -0.0025);
    }

    #[test]
    fn underscores_in_exponent_and_suffix() {
        let x = parse_float_lit("1_0e1_f64").unwrap();
        assert_eq!(x.get(), 100.0);
        assert_eq!(parse_float_lit(".25f64").unwrap().get(), 0.25);
        assert_eq!(parse_float_lit("1_000.0f64").unwrap().get(), 1000.0);
    }

    #[test]
    fn f32_widen_matches_f64_parse_where_exact() {
        let x = parse_float_lit("1.25f32").unwrap();
        assert_eq!(x.get(), 1.25_f64);
    }

    #[test]
    fn invalid_inputs() {
        assert!(parse_float_lit("").is_err());
        assert!(parse_float_lit("f64").is_err());
        assert!(parse_float_lit("1.0e").is_err());
        assert!(parse_float_lit("_").is_err());
    }
}
