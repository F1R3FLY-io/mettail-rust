//! Canonical complex types for use in Ascent relations and term ASTs.
//!
//! Wrappers over `num_complex::Complex32/Complex64` that preserve MeTTaIL canonical float
//! semantics on each component.

use crate::binding::{BoundTerm, Var};
use crate::{CanonicalFloat32, CanonicalFloat64};
use num_complex::{Complex32, Complex64};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Mul, Neg, Sub};

#[derive(Clone, Copy)]
pub struct CanonicalComplex32(Complex32);

impl CanonicalComplex32 {
    #[inline]
    pub fn new(re: f32, im: f32) -> Self {
        let re = CanonicalFloat32::from(re).get();
        let im = CanonicalFloat32::from(im).get();
        Self(Complex32::new(re, im))
    }

    #[inline]
    pub fn from_parts(re: CanonicalFloat32, im: CanonicalFloat32) -> Self {
        Self(Complex32::new(re.get(), im.get()))
    }

    #[inline]
    pub fn re(self) -> CanonicalFloat32 {
        CanonicalFloat32::from(self.0.re)
    }

    #[inline]
    pub fn im(self) -> CanonicalFloat32 {
        CanonicalFloat32::from(self.0.im)
    }

    #[inline]
    pub fn to_inner(self) -> Complex32 {
        self.0
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        self.re() == CanonicalFloat32::from(0.0) && self.im() == CanonicalFloat32::from(0.0)
    }

    #[inline]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let denom = rhs.0.norm_sqr();
        if denom == 0.0 {
            None
        } else {
            Some(Self::from(self.0 / rhs.0))
        }
    }
}

impl From<Complex32> for CanonicalComplex32 {
    fn from(value: Complex32) -> Self {
        Self::new(value.re, value.im)
    }
}

impl PartialEq for CanonicalComplex32 {
    fn eq(&self, other: &Self) -> bool {
        self.re() == other.re() && self.im() == other.im()
    }
}

impl Eq for CanonicalComplex32 {}

impl Hash for CanonicalComplex32 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.re().hash(state);
        self.im().hash(state);
    }
}

impl PartialOrd for CanonicalComplex32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalComplex32 {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.re().cmp(&other.re()) {
            Ordering::Equal => self.im().cmp(&other.im()),
            o => o,
        }
    }
}

impl fmt::Debug for CanonicalComplex32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CanonicalComplex32({})", self)
    }
}

impl fmt::Display for CanonicalComplex32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let re = self.re();
        let im = self.im();
        // In user-facing languages, `NaN+NaNi` is used as an explicit error sentinel.
        if re.get().is_nan() && im.get().is_nan() {
            return write!(f, "error");
        }
        if im.get().is_sign_negative() {
            write!(f, "{}-{}i", re, CanonicalFloat32::from(-im.get()))
        } else {
            write!(f, "{}+{}i", re, im)
        }
    }
}

impl BoundTerm<String> for CanonicalComplex32 {
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

impl Add for CanonicalComplex32 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::from(self.0 + rhs.0)
    }
}

impl Sub for CanonicalComplex32 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::from(self.0 - rhs.0)
    }
}

impl Mul for CanonicalComplex32 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::from(self.0 * rhs.0)
    }
}

impl Neg for CanonicalComplex32 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

#[derive(Clone, Copy)]
pub struct CanonicalComplex64(Complex64);

impl CanonicalComplex64 {
    #[inline]
    pub fn new(re: f64, im: f64) -> Self {
        let re = CanonicalFloat64::from(re).get();
        let im = CanonicalFloat64::from(im).get();
        Self(Complex64::new(re, im))
    }

    #[inline]
    pub fn from_parts(re: CanonicalFloat64, im: CanonicalFloat64) -> Self {
        Self(Complex64::new(re.get(), im.get()))
    }

    #[inline]
    pub fn re(self) -> CanonicalFloat64 {
        CanonicalFloat64::from(self.0.re)
    }

    #[inline]
    pub fn im(self) -> CanonicalFloat64 {
        CanonicalFloat64::from(self.0.im)
    }

    #[inline]
    pub fn to_inner(self) -> Complex64 {
        self.0
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        self.re() == CanonicalFloat64::from(0.0) && self.im() == CanonicalFloat64::from(0.0)
    }

    #[inline]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let denom = rhs.0.norm_sqr();
        if denom == 0.0 {
            None
        } else {
            Some(Self::from(self.0 / rhs.0))
        }
    }
}

impl From<Complex64> for CanonicalComplex64 {
    fn from(value: Complex64) -> Self {
        Self::new(value.re, value.im)
    }
}

impl PartialEq for CanonicalComplex64 {
    fn eq(&self, other: &Self) -> bool {
        self.re() == other.re() && self.im() == other.im()
    }
}

impl Eq for CanonicalComplex64 {}

impl Hash for CanonicalComplex64 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.re().hash(state);
        self.im().hash(state);
    }
}

impl PartialOrd for CanonicalComplex64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalComplex64 {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.re().cmp(&other.re()) {
            Ordering::Equal => self.im().cmp(&other.im()),
            o => o,
        }
    }
}

impl fmt::Debug for CanonicalComplex64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CanonicalComplex64({})", self)
    }
}

impl fmt::Display for CanonicalComplex64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let re = self.re();
        let im = self.im();
        // In user-facing languages, `NaN+NaNi` is used as an explicit error sentinel.
        if re.get().is_nan() && im.get().is_nan() {
            return write!(f, "error");
        }
        if im.get().is_sign_negative() {
            write!(f, "{}-{}i", re, CanonicalFloat64::from(-im.get()))
        } else {
            write!(f, "{}+{}i", re, im)
        }
    }
}

impl BoundTerm<String> for CanonicalComplex64 {
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

impl Add for CanonicalComplex64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::from(self.0 + rhs.0)
    }
}

impl Sub for CanonicalComplex64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::from(self.0 - rhs.0)
    }
}

impl Mul for CanonicalComplex64 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::from(self.0 * rhs.0)
    }
}

impl Neg for CanonicalComplex64 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    fn hash<T: Hash>(v: &T) -> u64 {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    }

    #[test]
    fn canonicalizes_components_64() {
        let c = CanonicalComplex64::new(-0.0, f64::NAN);
        assert_eq!(c.re(), CanonicalFloat64::from(0.0));
        assert!(c.im().get().is_nan());
    }

    #[test]
    fn canonicalizes_components_32() {
        let c = CanonicalComplex32::new(-0.0, f32::NAN);
        assert_eq!(c.re(), CanonicalFloat32::from(0.0));
        assert!(c.im().get().is_nan());
    }

    #[test]
    fn hash_eq_consistent_64() {
        let a = CanonicalComplex64::new(-0.0, f64::NAN);
        let b = CanonicalComplex64::new(0.0, f64::NAN);
        assert_eq!(a, b);
        assert_eq!(hash(&a), hash(&b));
    }

    #[test]
    fn ord_lexicographic_64() {
        let a = CanonicalComplex64::new(1.0, 2.0);
        let b = CanonicalComplex64::new(1.0, 3.0);
        let c = CanonicalComplex64::new(2.0, -1.0);
        assert!(a < b);
        assert!(b < c);
    }

    #[test]
    fn display_sign_64() {
        assert_eq!(CanonicalComplex64::new(1.0, 2.0).to_string(), "1.0+2.0i");
        assert_eq!(CanonicalComplex64::new(1.0, -2.0).to_string(), "1.0-2.0i");
    }

    #[test]
    fn arithmetic_64() {
        let a = CanonicalComplex64::new(1.0, 2.0);
        let b = CanonicalComplex64::new(3.0, -4.0);
        assert_eq!((a + b).to_string(), "4.0-2.0i");
        assert_eq!((a - b).to_string(), "-2.0+6.0i");
        assert_eq!((a * b).to_string(), "11.0+2.0i");
        assert_eq!((-a).to_string(), "-1.0-2.0i");
    }

    #[test]
    fn checked_div_zero_64() {
        let a = CanonicalComplex64::new(1.0, 2.0);
        let z = CanonicalComplex64::new(0.0, 0.0);
        assert!(a.checked_div(z).is_none());
    }

    #[test]
    fn checked_div_nonzero_64() {
        let a = CanonicalComplex64::new(1.0, 2.0);
        let b = CanonicalComplex64::new(3.0, 4.0);
        let q = a.checked_div(b).expect("non-zero denominator");
        assert_eq!(q.to_string(), "0.44+0.08i");
    }
}
