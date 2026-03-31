//! Fixed-point literals: `<mantissa>p<scale>` with decimal mantissa (optional dot).

use mettail_runtime::CanonicalFixedPoint;
use num_bigint::BigInt;
use num_traits::Num;

#[allow(clippy::result_unit_err)]
pub fn parse_fixed_lit(text: &str) -> Result<CanonicalFixedPoint, ()> {
    let cleaned: String = text.chars().filter(|&c| c != '_').collect();
    let s = cleaned.as_str();

    let p_pos = s.rfind('p').ok_or(())?;
    if p_pos == 0 {
        return Err(());
    }

    let scale_str = &s[p_pos + 1..];
    if scale_str.is_empty() || !scale_str.chars().all(|c| c.is_ascii_digit()) {
        return Err(());
    }
    let scale: u32 = scale_str.parse().map_err(|_| ())?;

    let mantissa = &s[..p_pos];
    if mantissa.is_empty() || mantissa == "." || mantissa == "-" || mantissa == "-." {
        return Err(());
    }

    let neg = mantissa.starts_with('-');
    let m = mantissa.strip_prefix('-').unwrap_or(mantissa);

    let (whole, frac) = if let Some(dot) = m.find('.') {
        let w = &m[..dot];
        let f = &m[dot + 1..];
        if f.contains('.') {
            return Err(());
        }
        (w, f)
    } else {
        (m, "")
    };

    if !frac.chars().all(|c| c.is_ascii_digit()) {
        return Err(());
    }
    if !whole.is_empty() && !whole.chars().all(|c| c.is_ascii_digit()) {
        return Err(());
    }
    if whole.is_empty() && frac.is_empty() {
        return Err(());
    }

    let whole_bi = if whole.is_empty() {
        BigInt::from(0)
    } else {
        BigInt::from_str_radix(whole, 10).map_err(|_| ())?
    };
    let fd = frac.len() as u32;
    let frac_bi = if frac.is_empty() {
        BigInt::from(0)
    } else {
        BigInt::from_str_radix(frac, 10).map_err(|_| ())?
    };

    let ten = BigInt::from(10u32);
    let unscaled_mantissa = whole_bi * ten.clone().pow(fd) + frac_bi;

    if scale < fd {
        return Err(());
    }
    let mut unscaled = unscaled_mantissa * ten.pow(scale - fd);
    if neg {
        unscaled = -unscaled;
    }

    Ok(CanonicalFixedPoint::new(unscaled, scale))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integral_mantissa() {
        let x = parse_fixed_lit("10p1").unwrap();
        assert_eq!(x.unscaled(), &BigInt::from(100));
        assert_eq!(x.places(), 1);
    }

    #[test]
    fn dot_mantissa() {
        let x = parse_fixed_lit("3.3p1").unwrap();
        assert_eq!(x.unscaled(), &BigInt::from(33));
        assert_eq!(x.places(), 1);
    }

    #[test]
    fn leading_dot() {
        let x = parse_fixed_lit(".5p1").unwrap();
        assert_eq!(x.unscaled(), &BigInt::from(5));
        assert_eq!(x.places(), 1);
    }

    #[test]
    fn div_example_components() {
        let a = parse_fixed_lit("10p1").unwrap();
        let b = parse_fixed_lit("3p1").unwrap();
        let q = a.checked_div(b).expect("q");
        assert_eq!(q.unscaled(), &BigInt::from(33));
        assert_eq!(q.places(), 1);
    }

    #[test]
    fn underscores_zero_negative_large_scale() {
        assert_eq!(parse_fixed_lit("1_0p2").unwrap().unscaled(), &BigInt::from(1000));
        assert_eq!(parse_fixed_lit("0p0").unwrap().unscaled(), &BigInt::from(0));
        assert_eq!(parse_fixed_lit("0p0").unwrap().places(), 0);
        let n = parse_fixed_lit("-1.25p3").unwrap();
        assert_eq!(n.unscaled(), &BigInt::from(-1250));
        assert_eq!(n.places(), 3);
        let wide = parse_fixed_lit("100p2").unwrap();
        assert_eq!(wide.unscaled(), &BigInt::from(10000));
        assert_eq!(wide.places(), 2);
    }

    #[test]
    fn parse_matches_canonical_fixed_point_eq() {
        let a = parse_fixed_lit("10p1").unwrap();
        let b = CanonicalFixedPoint::new(BigInt::from(100), 1);
        assert_eq!(a, b);
    }

    #[test]
    fn invalid_inputs() {
        assert!(parse_fixed_lit("nop").is_err());
        assert!(parse_fixed_lit("p1").is_err());
        assert!(parse_fixed_lit("10p").is_err());
        assert!(parse_fixed_lit("10px").is_err());
        assert!(parse_fixed_lit("10p-1").is_err());
        assert!(parse_fixed_lit(".").is_err());
        assert!(parse_fixed_lit("-.").is_err());
        assert!(parse_fixed_lit("1..2p1").is_err());
        assert!(parse_fixed_lit("1.23p1").is_err());
        assert!(parse_fixed_lit("1.2.3p1").is_err());
        assert!(parse_fixed_lit("").is_err());
    }
}
