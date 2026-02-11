//! Canonical float types for use in Ascent relations and term ASTs.
//!
//! Raw `f32`/`f64` do not implement `Eq`, `Hash`, or `Ord` (due to NaN). This module
//! provides wrapper types that canonicalize floats so they can be used in category enums
//! that derive `BoundTerm`, in relations, and in rewrites.
//!
//! # Semantics
//!
//! - **NaN**: All NaN values are canonicalized to a single quiet NaN bit pattern
//!   (`f64::NAN`). Thus `NaN == NaN` for `CanonicalFloat64` (and same for `CanonicalFloat32`).
//! - **Signed zero**: Negative zero (`-0.0`) is canonicalized to positive zero (`+0.0`),
//!   so `-0.0` and `+0.0` are equal.
//! - **Ord**: Total order: all non-NaN values are ordered by their numeric value; NaN
//!   is greater than any finite value (NaN sorts last).
//!
//! See also: `docs/design/exploring/float-support-ascent.md`.

use crate::binding::{BoundTerm, Var};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// Canonical f64 for use in category enums and Ascent relations.
///
/// Wraps `f64` with canonicalization in the constructor so that `Eq`, `Hash`, and `Ord`
/// are well-defined. Use [CanonicalFloat64::from] to construct and [CanonicalFloat64::get]
/// to obtain the raw value for arithmetic or display.
#[derive(Clone, Copy)]
pub struct CanonicalFloat64(f64);

impl CanonicalFloat64 {
    /// The single canonical NaN used for all NaN inputs.
    pub const CANONICAL_NAN: f64 = f64::NAN;

    fn canonicalize(x: f64) -> f64 {
        if x.is_nan() {
            Self::CANONICAL_NAN
        } else if x == 0.0 && x.is_sign_negative() {
            0.0
        } else {
            x
        }
    }
}

impl From<f64> for CanonicalFloat64 {
    fn from(x: f64) -> Self {
        CanonicalFloat64(Self::canonicalize(x))
    }
}

impl CanonicalFloat64 {
    /// Returns the raw f64 value (for native eval, display, or arithmetic outside this type).
    #[inline]
    pub fn get(self) -> f64 {
        self.0
    }
}

impl PartialEq for CanonicalFloat64 {
    fn eq(&self, other: &Self) -> bool {
        let a = self.0;
        let b = other.0;
        if a.is_nan() && b.is_nan() {
            true
        } else {
            a == b
        }
    }
}

impl Eq for CanonicalFloat64 {}

impl Hash for CanonicalFloat64 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.0.is_nan() {
            // All NaNs hash the same
            state.write_u64(Self::CANONICAL_NAN.to_bits());
        } else {
            self.0.to_bits().hash(state);
        }
    }
}

impl PartialOrd for CanonicalFloat64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalFloat64 {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = self.0;
        let b = other.0;
        match (a.is_nan(), b.is_nan()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => a.partial_cmp(&b).unwrap_or(Ordering::Equal),
        }
    }
}

impl fmt::Debug for CanonicalFloat64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for CanonicalFloat64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl BoundTerm<String> for CanonicalFloat64 {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(&mut self, _state: moniker::ScopeState, _on_free: &impl moniker::OnFreeFn<String>) {
        // No variables inside
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
        // No variables inside
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&Var<String>)) {
        // No variables inside
    }

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut Var<String>)) {
        // No variables inside
    }
}

impl std::ops::Add for CanonicalFloat64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::from(self.0 + rhs.0)
    }
}

impl std::ops::Sub for CanonicalFloat64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self::from(self.0 - rhs.0)
    }
}

impl std::ops::Mul for CanonicalFloat64 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::from(self.0 * rhs.0)
    }
}

impl std::ops::Div for CanonicalFloat64 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        Self::from(self.0 / rhs.0)
    }
}

impl std::ops::Rem for CanonicalFloat64 {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        Self::from(self.0 % rhs.0)
    }
}

// ---------------------------------------------------------------------------
// CanonicalFloat32 (optional, for f32 categories)
// ---------------------------------------------------------------------------

/// Canonical f32 for use in category enums and Ascent relations.
///
/// Same semantics as [CanonicalFloat64]: NaN and -0 canonicalized; total Ord with NaN last.
#[derive(Clone, Copy)]
pub struct CanonicalFloat32(f32);

impl CanonicalFloat32 {
    pub const CANONICAL_NAN: f32 = f32::NAN;

    fn canonicalize(x: f32) -> f32 {
        if x.is_nan() {
            Self::CANONICAL_NAN
        } else if x == 0.0_f32 && x.is_sign_negative() {
            0.0_f32
        } else {
            x
        }
    }
}

impl From<f32> for CanonicalFloat32 {
    fn from(x: f32) -> Self {
        CanonicalFloat32(Self::canonicalize(x))
    }
}

impl CanonicalFloat32 {
    #[inline]
    pub fn get(self) -> f32 {
        self.0
    }
}

impl PartialEq for CanonicalFloat32 {
    fn eq(&self, other: &Self) -> bool {
        let a = self.0;
        let b = other.0;
        if a.is_nan() && b.is_nan() {
            true
        } else {
            a == b
        }
    }
}

impl Eq for CanonicalFloat32 {}

impl Hash for CanonicalFloat32 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.0.is_nan() {
            state.write_u32(Self::CANONICAL_NAN.to_bits());
        } else {
            self.0.to_bits().hash(state);
        }
    }
}

impl PartialOrd for CanonicalFloat32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalFloat32 {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = self.0;
        let b = other.0;
        match (a.is_nan(), b.is_nan()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => a.partial_cmp(&b).unwrap_or(Ordering::Equal),
        }
    }
}

impl fmt::Debug for CanonicalFloat32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for CanonicalFloat32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl BoundTerm<String> for CanonicalFloat32 {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(&mut self, _state: moniker::ScopeState, _on_free: &impl moniker::OnFreeFn<String>) {
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

impl std::ops::Add for CanonicalFloat32 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::from(self.0 + rhs.0)
    }
}

impl std::ops::Sub for CanonicalFloat32 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self::from(self.0 - rhs.0)
    }
}

impl std::ops::Mul for CanonicalFloat32 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::from(self.0 * rhs.0)
    }
}

impl std::ops::Div for CanonicalFloat32 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        Self::from(self.0 / rhs.0)
    }
}

impl std::ops::Rem for CanonicalFloat32 {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        Self::from(self.0 % rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq_nan() {
        let a = CanonicalFloat64::from(f64::NAN);
        let b = CanonicalFloat64::from(f64::NAN);
        assert_eq!(a, b);
    }

    #[test]
    fn eq_neg_zero() {
        let a = CanonicalFloat64::from(-0.0);
        let b = CanonicalFloat64::from(0.0);
        assert_eq!(a, b);
    }

    #[test]
    fn hash_consistent_with_eq() {
        use std::collections::hash_map::DefaultHasher;
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut h = DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        assert_eq!(hash(&CanonicalFloat64::from(f64::NAN)), hash(&CanonicalFloat64::from(f64::NAN)));
        assert_eq!(hash(&CanonicalFloat64::from(-0.0)), hash(&CanonicalFloat64::from(0.0)));
    }

    #[test]
    fn ord_nan_last() {
        assert!(CanonicalFloat64::from(1.0) < CanonicalFloat64::from(f64::NAN));
        assert!(CanonicalFloat64::from(f64::INFINITY) < CanonicalFloat64::from(f64::NAN));
        assert_eq!(
            CanonicalFloat64::from(f64::NAN).cmp(&CanonicalFloat64::from(f64::NAN)),
            Ordering::Equal
        );
    }

    #[test]
    fn ord_numeric() {
        assert!(CanonicalFloat64::from(0.0) < CanonicalFloat64::from(1.0));
        assert!(CanonicalFloat64::from(-1.0) < CanonicalFloat64::from(0.0));
    }

    #[test]
    fn roundtrip_normal() {
        let x = 3.14_f64;
        assert_eq!(CanonicalFloat64::from(x).get(), x);
    }

    #[test]
    fn roundtrip_nan() {
        let c = CanonicalFloat64::from(f64::NAN);
        assert!(c.get().is_nan());
    }

    #[test]
    fn arithmetic() {
        let a = CanonicalFloat64::from(2.0);
        let b = CanonicalFloat64::from(3.0);
        assert_eq!((a + b).get(), 5.0);
        assert_eq!((a * b).get(), 6.0);
    }

    #[test]
    fn canonical_f32_smoke() {
        assert_eq!(CanonicalFloat32::from(f32::NAN), CanonicalFloat32::from(f32::NAN));
        assert_eq!(CanonicalFloat32::from(-0.0_f32), CanonicalFloat32::from(0.0_f32));
        assert!(CanonicalFloat32::from(1.0_f32) < CanonicalFloat32::from(f32::NAN));
    }
}
