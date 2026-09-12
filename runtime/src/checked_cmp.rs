//! Admission for the original native equality, inequality and ordering calls.
//!
//! The source-group contract is AdmittedNativeLeafComparison.v. This module
//! does not define another comparator or equate equality with ordering equality.

use crate::BindingFailure;
use std::cmp::Ordering;

/// Failure before the rejected operation; previously paid inspection is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeComparisonFailure<E> {
    UnsupportedProfile,
    Admission(BindingFailure<E>),
}

/// Whether this build uses the audited compiler/target and trusted prebuilt core.
///
/// This is the same build predicate as checked native hashing, not a dependence
/// on Fx hashing semantics or an attestation of arbitrary toolchain replacements.
/// Ordinary native comparisons remain available on unsupported profiles.
pub const CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE: bool =
    cfg!(mettail_checked_native_comparison_profile);

mod sealed {
    #[derive(Clone, Copy)]
    pub enum ComparisonOperation {
        Eq,
        Ne,
        Cmp,
    }

    pub trait Leaf {
        // Metadata only, called after its reservation. No payload comparison.
        fn execution_work(&self, other: &Self, operation: ComparisonOperation) -> Option<usize>;
    }
}
use sealed::ComparisonOperation;

/// Paid native equality and inequality for audited leaves.
///
/// One logical-work unit precedes metadata inspection and checked arithmetic,
/// followed by the native execution allowance. Both reservations retain zero
/// payload units. Refusal leaves both operands unchanged; previously accepted
/// inspection charges remain spent. Success returns the original native result,
/// not a receipt authorizing another execution.
///
/// This interface is sealed to i64, bool and String. It deliberately does not
/// require Ord: equality-only structural leaves need not acquire an ordering.
pub trait CheckedNativeEqualityLeaf: Eq + sealed::Leaf {
    fn try_native_eq<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<bool, NativeComparisonFailure<E>> {
        admit_comparison(
            self,
            other,
            ComparisonOperation::Eq,
            reserve,
            CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE,
            <Self as PartialEq>::eq,
        )
    }

    /// Invoke the original inequality method, not a substituted ordering test.
    fn try_native_ne<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<bool, NativeComparisonFailure<E>> {
        admit_comparison(
            self,
            other,
            ComparisonOperation::Ne,
            reserve,
            CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE,
            <Self as PartialEq>::ne,
        )
    }
}

/// Paid original Ord::cmp for audited i64, bool and String leaves.
///
/// Admission and failure follow the equality interface's two-stage contract.
/// String work covers both byte ranges supplied to the native byte-comparison
/// primitive, not physical machine loads, CPU instructions or memcmp internals.
/// It borrows the operands without constructing a buffer or retaining a plan.
pub trait CheckedNativeOrderingLeaf: Ord + sealed::Leaf {
    fn try_native_cmp<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Ordering, NativeComparisonFailure<E>> {
        admit_comparison(
            self,
            other,
            ComparisonOperation::Cmp,
            reserve,
            CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE,
            <Self as Ord>::cmp,
        )
    }
}

fn admit_comparison<T: sealed::Leaf + ?Sized, E, R>(
    left: &T,
    right: &T,
    operation: ComparisonOperation,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    supported: bool,
    action: impl FnOnce(&T, &T) -> R,
) -> Result<R, NativeComparisonFailure<E>> {
    if !supported {
        return Err(NativeComparisonFailure::UnsupportedProfile);
    }
    reserve(1, 0)
        .map_err(|error| NativeComparisonFailure::Admission(BindingFailure::Reservation(error)))?;
    let work = left
        .execution_work(right, operation)
        .ok_or(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))?;
    reserve(work, 0)
        .map_err(|error| NativeComparisonFailure::Admission(BindingFailure::Reservation(error)))?;
    Ok(action(left, right))
}

macro_rules! fixed_leaf {
    ($ty:ty) => {
        impl sealed::Leaf for $ty {
            fn execution_work(&self, _: &Self, _: ComparisonOperation) -> Option<usize> {
                // Original method dispatch and its bounded primitive operation.
                Some(2)
            }
        }
        impl CheckedNativeEqualityLeaf for $ty {}
        impl CheckedNativeOrderingLeaf for $ty {}
    };
}
fixed_leaf!(i64);
fixed_leaf!(bool);

// String derives comparison over Vec<u8>; do not replace it with a str call.
// Equality's six fixed groups cover the derived/Vec/slice route and byte
// specialization. Default String ne adds one group. Ordering's nine cover
// forwarding, min-length metadata, byte dispatch and the native sign/tie-break.
// The two byte extents are logical primitive operands, not machine-load counts.
fn string_execution_work(
    left: usize,
    right: usize,
    operation: ComparisonOperation,
) -> Option<usize> {
    let (fixed, extent) = match operation {
        ComparisonOperation::Eq => (6usize, if left == right { left } else { 0 }),
        ComparisonOperation::Ne => (7usize, if left == right { left } else { 0 }),
        ComparisonOperation::Cmp => (9usize, left.min(right)),
    };
    extent.checked_mul(2)?.checked_add(fixed)
}

impl sealed::Leaf for String {
    fn execution_work(&self, other: &Self, operation: ComparisonOperation) -> Option<usize> {
        string_execution_work(self.len(), other.len(), operation)
    }
}
impl CheckedNativeEqualityLeaf for String {}
impl CheckedNativeOrderingLeaf for String {}

#[cfg(test)]
#[path = "checked_cmp_tests.rs"]
mod tests;
