//! Canonical BigInt wrapper for use in category enums and Ascent relations.
//!
//! Note: `moniker-derive`'s `BoundTerm` implementation performs `match *self`
//! and will attempt to move literal payloads out of borrowed enum variants.
//! For that reason, the payload type used by literal variants must be `Copy`.
//!
//! We store the underlying `BigInt` in a leaked allocation and keep only a
//! pointer-sized handle (`Copy`). This avoids `Copy`-trait limitations of
//! `num_bigint::BigInt` itself.

use std::{fmt, hash::Hash, ptr::NonNull};

use moniker::{BoundTerm, Var};
use num_bigint::BigInt;

#[derive(Clone, Copy)]
pub struct CanonicalBigInt(NonNull<BigInt>);

// SAFETY: `CanonicalBigInt` holds a pointer to a leaked `BigInt` allocation
// that is never mutated after creation, so sharing across threads is safe.
unsafe impl Send for CanonicalBigInt {}
unsafe impl Sync for CanonicalBigInt {}

impl CanonicalBigInt {
    pub fn new(value: BigInt) -> Self {
        Self::from(value)
    }

    pub fn get(&self) -> &BigInt {
        // SAFETY: `CanonicalBigInt` points at a leaked allocation which is never freed.
        unsafe { self.0.as_ref() }
    }
}

impl From<BigInt> for CanonicalBigInt {
    fn from(value: BigInt) -> Self {
        let boxed = Box::new(value);
        let raw = Box::into_raw(boxed);
        Self(NonNull::new(raw).expect("BigInt Box pointer should be non-null"))
    }
}

impl PartialEq for CanonicalBigInt {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}
impl Eq for CanonicalBigInt {}

impl PartialOrd for CanonicalBigInt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CanonicalBigInt {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(other.get())
    }
}

impl Hash for CanonicalBigInt {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.get().hash(state)
    }
}

impl fmt::Debug for CanonicalBigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.get(), f)
    }
}

impl fmt::Display for CanonicalBigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.get(), f)
    }
}

impl BoundTerm<String> for CanonicalBigInt {
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

impl std::ops::Add for CanonicalBigInt {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        CanonicalBigInt::from(self.get() + rhs.get())
    }
}
