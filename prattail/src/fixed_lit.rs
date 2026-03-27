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
}
