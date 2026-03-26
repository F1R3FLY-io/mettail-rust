//! Decimal fixed-point values for use in category enums and Ascent relations.
//!
//! A value is `(unscaled, places)` representing `unscaled / 10^places`.
//! Uses [`CanonicalBigInt`] for the unscaled payload so the pair is `Copy`.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Rem, Sub};

use moniker::{BoundTerm, Var};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::Zero;

use crate::CanonicalBigInt;

/// Decimal fixed-point: exact value `unscaled / 10^places`.
#[derive(Clone, Copy)]
pub struct CanonicalFixedPoint {
    unscaled: CanonicalBigInt,
    places: u32,
}

fn pow10(p: u32) -> BigInt {
    BigInt::from(10u32).pow(p)
}

impl CanonicalFixedPoint {
    /// Constructs from unscaled integer and decimal place count, then normalizes.
    pub fn new(unscaled: BigInt, places: u32) -> Self {
        Self::from_raw(CanonicalBigInt::from(unscaled), places)
    }

    fn from_raw(unscaled: CanonicalBigInt, places: u32) -> Self {
        let mut s = Self { unscaled, places };
        s.normalize_in_place();
        s
    }

    /// Only collapse true zero to `0p0`. Do not strip trailing decimal zeros: `100p1` (ten with
    /// scale 1) must stay distinct from `10p0` for literal-backed scale, while `+`/`-`/`*`/`/`
    /// still align operands by `max(places)`.
    fn normalize_in_place(&mut self) {
        if self.unscaled.get().is_zero() {
            self.places = 0;
        }
    }

    fn value_ratio(&self) -> Ratio<BigInt> {
        Ratio::new(self.unscaled.get().clone(), pow10(self.places))
    }

    #[inline]
    pub fn unscaled(&self) -> &BigInt {
        self.unscaled.get()
    }

    #[inline]
    pub fn places(&self) -> u32 {
        self.places
    }

    /// Align both operands to `P = max(places_a, places_b)`; returns scaled unscaled values.
    fn align_pair(a: Self, b: Self) -> (BigInt, BigInt, u32) {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ua = a.unscaled.get() * scale_a;
        let ub = b.unscaled.get() * scale_b;
        (ua, ub, p)
    }

    /// Shifted integer division: `(ua * 10^P) / ub` at common scale `P`.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let numer = ua * pow10(p);
        let q = numer / ub;
        Some(Self::from_raw(CanonicalBigInt::from(q), p))
    }

    /// Remainder such that `(a / b) * b + (a % b) == a` with truncated quotient.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let q = (ua.clone() * pow10(p)) / &ub;
        let rem = ua - (q * &ub) / pow10(p);
        Some(Self::from_raw(CanonicalBigInt::from(rem), p))
    }

    fn bitwise_aligned<F>(a: Self, b: Self, op: F) -> Self
    where
        F: FnOnce(BigInt, BigInt) -> BigInt,
    {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ia = a.unscaled.get() * scale_a;
        let ib = b.unscaled.get() * scale_b;
        let r = op(ia, ib);
        Self::from_raw(CanonicalBigInt::from(r), p)
    }
}

impl PartialEq for CanonicalFixedPoint {
    fn eq(&self, other: &Self) -> bool {
        self.value_ratio() == other.value_ratio()
    }
}

impl Eq for CanonicalFixedPoint {}

impl PartialOrd for CanonicalFixedPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalFixedPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value_ratio().cmp(&other.value_ratio())
    }
}

impl Hash for CanonicalFixedPoint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let r = self.value_ratio();
        r.numer().hash(state);
        r.denom().hash(state);
    }
}

impl fmt::Debug for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Fixed({}/{})",
            self.unscaled.get(),
            pow10(self.places)
        )
    }
}

impl fmt::Display for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let u = self.unscaled.get();
        let p = self.places as usize;
        if p == 0 {
            return write!(f, "{}p0", u);
        }
        let us = u.to_string();
        let neg = us.starts_with('-');
        let digits = if neg { &us[1..] } else { &us[..] };
        if digits.len() <= p {
            let pad = p - digits.len();
            let frac: String = std::iter::repeat('0').take(pad).chain(digits.chars()).collect();
            if neg {
                write!(f, "-0.{frac}p{}", self.places)
            } else {
                write!(f, "0.{frac}p{}", self.places)
            }
        } else {
            let split = digits.len() - p;
            let (int_part, frac_part) = digits.split_at(split);
            if neg {
                write!(f, "-{int_part}.{frac_part}p{}", self.places)
            } else {
                write!(f, "{int_part}.{frac_part}p{}", self.places)
            }
        }
    }
}

impl BoundTerm<String> for CanonicalFixedPoint {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_free: &impl moniker::OnFreeFn<String>,
    ) {
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&Var<String>)) {}

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut Var<String>)) {}
}

impl Add for CanonicalFixedPoint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua + ub), p)
    }
}

impl Sub for CanonicalFixedPoint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua - ub), p)
    }
}

impl Mul for CanonicalFixedPoint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let numer = self.unscaled.get() * rhs.unscaled.get();
        let places = self.places + rhs.places;
        Self::from_raw(CanonicalBigInt::from(numer), places)
    }
}

impl Div for CanonicalFixedPoint {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self.checked_div(rhs)
            .expect("fixed-point division by zero or overflow path")
    }
}

impl Rem for CanonicalFixedPoint {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        self.checked_rem(rhs)
            .expect("fixed-point remainder: division by zero")
    }
}

impl Neg for CanonicalFixedPoint {
    type Output = Self;
    fn neg(self) -> Self {
        Self::from_raw(CanonicalBigInt::from(-self.unscaled.get().clone()), self.places)
    }
}

impl BitAnd for CanonicalFixedPoint {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a & b)
    }
}

impl BitOr for CanonicalFixedPoint {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a | b)
    }
}

impl BitXor for CanonicalFixedPoint {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a ^ b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp(s_int: i64, s_frac: i64, places: u32) -> CanonicalFixedPoint {
        // helper: value (s_int * 10^p + s_frac) / 10^p for small tests (s_frac < 10^p)
        let ten_p = 10i64.pow(places);
        let u = BigInt::from(s_int) * BigInt::from(ten_p) + BigInt::from(s_frac);
        CanonicalFixedPoint::new(u, places)
    }

    #[test]
    fn div_mod_example() {
        let a = fp(10, 0, 1);
        let b = fp(3, 0, 1);
        let q = a.checked_div(b).expect("div");
        let r = a.checked_rem(b).expect("rem");
        assert_eq!(q.unscaled.get(), &BigInt::from(33));
        assert_eq!(q.places(), 1);
        assert_eq!(r.unscaled.get(), &BigInt::from(1));
        assert_eq!(r.places(), 1);
        let restored = q * b + r;
        assert_eq!(restored, a);
    }

    #[test]
    fn normalize_zero() {
        let z = CanonicalFixedPoint::new(BigInt::from(0), 5);
        assert!(z.unscaled.get().is_zero());
        assert_eq!(z.places(), 0);
    }

    #[test]
    fn bitwise_and_aligned() {
        let a = CanonicalFixedPoint::new(BigInt::from(12), 1);
        let b = CanonicalFixedPoint::new(BigInt::from(10), 1);
        let c = a & b;
        assert_eq!(c.unscaled.get(), &BigInt::from(8));
        assert_eq!(c.places(), 1);
    }
}
