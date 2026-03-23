//! Arbitrary-precision rational literal parsing (separate from [`IntLit`](crate::IntLit)).
//!
//! Surface forms (after digit-separator `_` removal):
//! - Composite: `<int>r/<int>r` where each `<int>` uses the same radix prefixes as integer literals (`0x`, `0o`, `0b`, decimal).
//! - Optional whole: `<int>r` (same `<int>` grammar as composite sides) — interpreted as that integer over `1` (no `/1r` required).

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{Num, Zero};

/// Parsed rational literal payload (reduction is left to [`num_rational::Ratio::new`] at use sites / runtime).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RationalLit(pub Ratio<BigInt>);

impl RationalLit {
    pub fn ratio(&self) -> &Ratio<BigInt> {
        &self.0
    }
}

fn split_radix_prefix(s: &str) -> (u32, &str) {
    if let Some(h) = s.strip_prefix("0x") {
        (16, h)
    } else if let Some(o) = s.strip_prefix("0o") {
        (8, o)
    } else if let Some(b) = s.strip_prefix("0b") {
        (2, b)
    } else {
        (10, s)
    }
}

fn parse_bigint_body(body: &str) -> Result<BigInt, ()> {
    let (radix, digits) = split_radix_prefix(body);
    if digits.is_empty() {
        return Err(());
    }
    BigInt::from_str_radix(digits, radix).map_err(|_| ())
}

/// Parse `…r` or `…r/…r` (with optional `_` in digit runs).
pub fn parse_rational_lit(text: &str) -> Result<RationalLit, ()> {
    let cleaned: String = text.chars().filter(|&c| c != '_').collect();
    if let Some(idx) = cleaned.find('/') {
        let left = &cleaned[..idx];
        let right = &cleaned[idx + 1..];
        let left_body = left.strip_suffix('r').ok_or(())?;
        let right_body = right.strip_suffix('r').ok_or(())?;
        let n = parse_bigint_body(left_body)?;
        let d = parse_bigint_body(right_body)?;
        if d.is_zero() {
            return Err(());
        }
        Ok(RationalLit(Ratio::new(n, d)))
    } else {
        let body = cleaned.strip_suffix('r').ok_or(())?;
        let n = parse_bigint_body(body)?;
        Ok(RationalLit(Ratio::new(n, BigInt::from(1))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composite_reduces() {
        let RationalLit(r) = parse_rational_lit("2r/4r").unwrap();
        assert_eq!(*r.numer(), BigInt::from(1));
        assert_eq!(*r.denom(), BigInt::from(2));
    }

    #[test]
    fn whole_form() {
        let RationalLit(r) = parse_rational_lit("7r").unwrap();
        assert_eq!(*r.numer(), BigInt::from(7));
        assert_eq!(*r.denom(), BigInt::from(1));
    }

    #[test]
    fn zero_den_fails() {
        assert!(parse_rational_lit("1r/0r").is_err());
    }

    #[test]
    fn radix_prefixes() {
        let RationalLit(r) = parse_rational_lit("0xFr/0x2r").unwrap();
        assert_eq!(*r.numer(), BigInt::from(15));
        assert_eq!(*r.denom(), BigInt::from(2));
    }

    #[test]
    fn whole_form_with_radix_and_separators() {
        let RationalLit(r) = parse_rational_lit("0xAr").unwrap();
        assert_eq!(*r.numer(), BigInt::from(10));
        assert_eq!(*r.denom(), BigInt::from(1));
        let RationalLit(r2) = parse_rational_lit("1_0r").unwrap();
        assert_eq!(*r2.numer(), BigInt::from(10));
        assert_eq!(*r2.denom(), BigInt::from(1));
    }
}
