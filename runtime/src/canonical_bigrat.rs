//! Canonical arbitrary-precision rational wrapper for category enums and Ascent relations.
//!
//! Same rationale as [`CanonicalBigInt`](crate::CanonicalBigInt): `moniker-derive`'s `BoundTerm`
//! needs `Copy` literal payloads; `num_rational::Ratio<BigInt>` is not `Copy`, so we hold a
//! `NonNull` to a leaked, immutable `Ratio<BigInt>`.

use std::{
    fmt,
    hash::{Hash, Hasher},
    ops::{Add, Div, Mul, Neg, Sub},
    ptr::NonNull,
};

use moniker::{BoundTerm, Var};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::Zero;

/// Copy handle to a leaked `Ratio<BigInt>` (canonical reduced form from `Ratio::new`).
#[derive(Clone, Copy)]
pub struct CanonicalBigRat(NonNull<Ratio<BigInt>>);

// SAFETY: Immutable leaked allocation; same as CanonicalBigInt.
unsafe impl Send for CanonicalBigRat {}
unsafe impl Sync for CanonicalBigRat {}

impl CanonicalBigRat {
    /// Build `n/d` in reduced form. Returns `None` if `d == 0`.
    pub fn try_from_nd(n: BigInt, d: BigInt) -> Option<Self> {
        if d.is_zero() {
            return None;
        }
        Some(Self::from(Ratio::new(n, d)))
    }

    pub fn get(&self) -> &Ratio<BigInt> {
        // SAFETY: points at a leaked allocation which is never freed.
        unsafe { self.0.as_ref() }
    }

    fn lcm_pos(a: &BigInt, b: &BigInt) -> BigInt {
        // Denominators produced by Ratio are positive, but keep this helper robust.
        if a.is_zero() || b.is_zero() {
            BigInt::from(0)
        } else {
            let g = a.gcd(b);
            (a / &g) * b
        }
    }

    /// Bitwise AND on rationals by aligning to a common denominator and applying `&` to the
    /// aligned numerators (language-defined semantics).
    pub fn bitand_aligned(self, rhs: Self) -> Self {
        let (n1, d1) = (self.get().numer().clone(), self.get().denom().clone());
        let (n2, d2) = (rhs.get().numer().clone(), rhs.get().denom().clone());
        let d = Self::lcm_pos(&d1, &d2);
        debug_assert!(!d.is_zero());
        let s1 = &d / &d1;
        let s2 = &d / &d2;
        let nn1 = n1 * s1;
        let nn2 = n2 * s2;
        Self::try_from_nd(nn1 & nn2, d).expect("aligned denominator is non-zero")
    }

    /// Bitwise OR on rationals by aligning to a common denominator and applying `|` to the
    /// aligned numerators (language-defined semantics).
    pub fn bitor_aligned(self, rhs: Self) -> Self {
        let (n1, d1) = (self.get().numer().clone(), self.get().denom().clone());
        let (n2, d2) = (rhs.get().numer().clone(), rhs.get().denom().clone());
        let d = Self::lcm_pos(&d1, &d2);
        debug_assert!(!d.is_zero());
        let s1 = &d / &d1;
        let s2 = &d / &d2;
        let nn1 = n1 * s1;
        let nn2 = n2 * s2;
        Self::try_from_nd(nn1 | nn2, d).expect("aligned denominator is non-zero")
    }

    /// Bitwise NOT on rationals: apply `!` to the numerator, keep the denominator.
    pub fn bitnot(self) -> Self {
        let n = self.get().numer().clone();
        let d = self.get().denom().clone();
        Self::try_from_nd(!n, d).expect("denominator is non-zero")
    }
}

impl From<Ratio<BigInt>> for CanonicalBigRat {
    fn from(value: Ratio<BigInt>) -> Self {
        let boxed = Box::new(value);
        let raw = Box::into_raw(boxed);
        Self(NonNull::new(raw).expect("Ratio Box pointer should be non-null"))
    }
}

impl PartialEq for CanonicalBigRat {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}
impl Eq for CanonicalBigRat {}

impl PartialOrd for CanonicalBigRat {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CanonicalBigRat {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(other.get())
    }
}

impl Hash for CanonicalBigRat {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

impl fmt::Debug for CanonicalBigRat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.get(), f)
    }
}

impl fmt::Display for CanonicalBigRat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.get(), f)
    }
}

impl BoundTerm<String> for CanonicalBigRat {
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

impl Add for CanonicalBigRat {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        CanonicalBigRat::from(self.get() + rhs.get())
    }
}

impl Sub for CanonicalBigRat {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        CanonicalBigRat::from(self.get() - rhs.get())
    }
}

impl Mul for CanonicalBigRat {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        CanonicalBigRat::from(self.get() * rhs.get())
    }
}

impl Div for CanonicalBigRat {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        CanonicalBigRat::from(self.get() / rhs.get())
    }
}

impl Neg for CanonicalBigRat {
    type Output = Self;
    fn neg(self) -> Self::Output {
        CanonicalBigRat::from(-self.get().clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn try_from_nd_reduces() {
        let r = CanonicalBigRat::try_from_nd(BigInt::from(4), BigInt::from(6)).unwrap();
        assert_eq!(r.get().numer(), &BigInt::from(2));
        assert_eq!(r.get().denom(), &BigInt::from(3));
    }

    #[test]
    fn try_from_nd_zero_den() {
        assert!(CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(0)).is_none());
    }

    #[test]
    fn add_mul_div() {
        let a = CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(3)).unwrap();
        let b = CanonicalBigRat::try_from_nd(BigInt::from(3), BigInt::from(4)).unwrap();
        let sum = a + b;
        assert_eq!(sum.get().to_string(), "13/12");
        let prod = a * b;
        assert_eq!(prod.get().to_string(), "1/4");
        let q = b / a;
        assert_eq!(q.get().to_string(), "9/4");
    }

    #[test]
    fn hash_eq_consistent() {
        let x = CanonicalBigRat::try_from_nd(BigInt::from(2), BigInt::from(4)).unwrap();
        let y = CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(2)).unwrap();
        assert_eq!(x, y);
        let mut hx = std::collections::hash_map::DefaultHasher::new();
        let mut hy = std::collections::hash_map::DefaultHasher::new();
        x.hash(&mut hx);
        y.hash(&mut hy);
        assert_eq!(hx.finish(), hy.finish());
    }

    #[test]
    fn bitwise_aligned_or_and_not_examples() {
        let a = CanonicalBigRat::try_from_nd(BigInt::from(7), BigInt::from(12)).unwrap();
        let b = CanonicalBigRat::try_from_nd(BigInt::from(11), BigInt::from(16)).unwrap();
        let or = a.bitor_aligned(b);
        assert_eq!(or.get().to_string(), "61/48");

        let a = CanonicalBigRat::try_from_nd(BigInt::from(7), BigInt::from(12)).unwrap();
        let b = CanonicalBigRat::try_from_nd(BigInt::from(13), BigInt::from(16)).unwrap();
        let and = a.bitand_aligned(b);
        assert_eq!(and.get().to_string(), "1/12");

        let z = CanonicalBigRat::try_from_nd(BigInt::from(0), BigInt::from(1)).unwrap();
        assert_eq!(z.bitnot().get().to_string(), "-1");
    }
}
