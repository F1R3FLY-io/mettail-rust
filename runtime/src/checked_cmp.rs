//! Admission for the original native equality, inequality and ordering calls.
//!
//! The source-group contract is AdmittedNativeLeafComparison.v. This module
//! does not define another comparator or equate equality with ordering equality.

use crate::{BindingFailure, OrdVar};
use moniker::{Binder, Var};
use std::cmp::Ordering;

/// Failure before the rejected operation; previously paid inspection is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeComparisonFailure<E> {
    UnsupportedProfile,
    /// No admitted implementation exists for this constructor in this profile.
    UnsupportedConstructor {
        category: &'static str,
        constructor: &'static str,
    },
    /// Invalid roster or continuation protocol, distinct from size/budget refusal.
    InvalidCollectionInput(&'static str),
    Admission(BindingFailure<E>),
}

/// Admission at the existing generated equality and ordering worklist sites.
///
/// Success returns the ordinary operation's result. A refusal publishes no
/// result, including when comparison has already found an ordering but pending
/// work has not finished its admitted drain. Tasks borrow immutable inputs;
/// their construction reserves eventual disposal. This is a logical source-work
/// contract, not a physical allocator or arbitrary-callback bound. Constructor
/// support is checked locally, not certified for skipped descendants.
pub trait CheckedIterativeComparison: Ord {
    fn try_eq_iterative<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<bool, NativeComparisonFailure<E>>;

    fn try_cmp_iterative<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Ordering, NativeComparisonFailure<E>>;
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
        fn execution_work<E>(
            &self,
            other: &Self,
            operation: ComparisonOperation,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<usize, super::BindingFailure<E>>;
    }

    pub trait EqualityLeaf {
        fn equality_work<E>(
            &self,
            other: &Self,
            negated: bool,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<usize, super::BindingFailure<E>>;
    }

    // Equality-only leaves never implement Leaf: there is no invented Cmp
    // request or unsupported/overflow stand-in for a nonexistent Binder Ord.
    impl<T: Leaf + ?Sized> EqualityLeaf for T {
        fn equality_work<E>(
            &self,
            other: &Self,
            negated: bool,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<usize, super::BindingFailure<E>> {
            self.execution_work(
                other,
                if negated {
                    ComparisonOperation::Ne
                } else {
                    ComparisonOperation::Eq
                },
                reserve,
            )
        }
    }
}
use sealed::ComparisonOperation;

/// Paid native equality and inequality for audited leaves.
///
/// One logical-work unit precedes metadata inspection and checked arithmetic,
/// followed by the native execution allowance. All reservations retain zero
/// payload units. Refusal leaves both operands unchanged; previously accepted
/// inspection charges remain spent. Success returns the original native result,
/// not a receipt authorizing another execution.
///
/// This interface is sealed to i64, bool, String, OrdVar, Binder<String> and
/// Vec<Binder<String>>, FltNode and Arc<FltNode>. Equality-only binders do not
/// acquire an ordering. Structural FLTs additionally admit each paired metadata
/// advance before inspection; declared template bounds are not size receipts.
pub trait CheckedNativeEqualityLeaf: Eq + sealed::EqualityLeaf {
    /// Inspect the original equality call's work without comparing operands.
    ///
    /// The same paid metadata inspections as `try_native_eq` run, but no
    /// execution reservation or native call follows. The returned allowance
    /// excludes inspection charges and has not been reserved. It applies only
    /// to this operation on the unchanged borrowed operand pair and audited
    /// profile; it grants no replay authority. Retaining the value and executing
    /// the comparison require their own admission. No owned payload is built.
    fn try_inspect_native_eq_work<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, NativeComparisonFailure<E>> {
        inspect_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |reserve| {
            self.equality_work(other, false, reserve)
        })
    }

    /// Inspect inequality's own work, not equality or ordering as a substitute.
    ///
    /// This has the inspection-only contract of `try_inspect_native_eq_work`,
    /// but retains the original inequality operation's metadata allowance.
    fn try_inspect_native_ne_work<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, NativeComparisonFailure<E>> {
        inspect_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |reserve| {
            self.equality_work(other, true, reserve)
        })
    }

    fn try_native_eq<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<bool, NativeComparisonFailure<E>> {
        admit_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |reserve| {
            self.equality_work(other, false, reserve)
        })?;
        Ok(<Self as PartialEq>::eq(self, other))
    }

    /// Invoke the original inequality method, not a substituted ordering test.
    fn try_native_ne<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<bool, NativeComparisonFailure<E>> {
        admit_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |reserve| {
            self.equality_work(other, true, reserve)
        })?;
        Ok(<Self as PartialEq>::ne(self, other))
    }
}

/// Paid original Ord::cmp for audited scalar, identity and structural FLT leaves.
///
/// Admission and failure follow the equality interface's two-stage contract.
/// String work covers both byte ranges supplied to the native byte-comparison
/// primitive, not physical machine loads, CPU instructions or memcmp internals.
/// It borrows the operands without constructing a buffer or retaining a plan.
pub trait CheckedNativeOrderingLeaf: Ord + sealed::Leaf {
    /// Inspect ordering's work without executing or reserving the comparison.
    ///
    /// Metadata and arithmetic are paid exactly as in `try_native_cmp`.
    /// The returned allowance excludes those charges and applies only to the
    /// same unchanged operand pair, operation and audited profile. It is not
    /// permission to execute, retain a plan, or reuse a comparison result.
    fn try_inspect_native_cmp_work<E>(
        &self,
        other: &Self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, NativeComparisonFailure<E>> {
        inspect_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |reserve| {
            self.execution_work(other, ComparisonOperation::Cmp, reserve)
        })
    }

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
    admit_native_work(reserve, supported, |reserve| {
        left.execution_work(right, operation, reserve)
    })?;
    Ok(action(left, right))
}

// Both public interpretations select the same sealed metadata inspector.
// Returning its unreserved work does not execute a comparator or grant authority.
fn inspect_native_work<E, F: FnMut(usize, usize) -> Result<(), E>>(
    reserve: &mut F,
    supported: bool,
    inspect: impl FnOnce(&mut F) -> Result<usize, BindingFailure<E>>,
) -> Result<usize, NativeComparisonFailure<E>> {
    if !supported {
        return Err(NativeComparisonFailure::UnsupportedProfile);
    }
    reserve(1, 0)
        .map_err(|error| NativeComparisonFailure::Admission(BindingFailure::Reservation(error)))?;
    inspect(reserve).map_err(NativeComparisonFailure::Admission)
}

fn admit_native_work<E, F: FnMut(usize, usize) -> Result<(), E>>(
    reserve: &mut F,
    supported: bool,
    inspect: impl FnOnce(&mut F) -> Result<usize, BindingFailure<E>>,
) -> Result<(), NativeComparisonFailure<E>> {
    let work = inspect_native_work(reserve, supported, inspect)?;
    reserve(work, 0)
        .map_err(|error| NativeComparisonFailure::Admission(BindingFailure::Reservation(error)))?;
    Ok(())
}

macro_rules! fixed_leaf {
    ($ty:ty) => {
        impl sealed::Leaf for $ty {
            fn execution_work<E>(
                &self,
                _: &Self,
                _: ComparisonOperation,
                _: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<usize, BindingFailure<E>> {
                // Original method dispatch and its bounded primitive operation.
                Ok(2)
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
    fn execution_work<E>(
        &self,
        other: &Self,
        operation: ComparisonOperation,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        string_execution_work(self.len(), other.len(), operation)
            .ok_or(BindingFailure::SizeOverflow)
    }
}
impl CheckedNativeEqualityLeaf for String {}
impl CheckedNativeOrderingLeaf for String {}

// AdmittedIdentityComparison.v. Equality observes identities, not diagnostic
// names. Ordering retains the actual OrdVar::cmp: fresh DefaultHasher hashes
// for free UIDs and both eager scope/index comparisons for bound variables.
fn ordvar_execution_work(left: &OrdVar, right: &OrdVar, operation: ComparisonOperation) -> usize {
    let (equality, ordering) = match (&left.0, &right.0) {
        (Var::Free(_), Var::Free(_)) => (14, 68),
        (Var::Bound(_), Var::Bound(_)) => (19, 14),
        _ => (7, 5),
    };
    match operation {
        ComparisonOperation::Eq => equality,
        ComparisonOperation::Ne => equality + 1,
        ComparisonOperation::Cmp => ordering,
    }
}
impl sealed::Leaf for OrdVar {
    fn execution_work<E>(
        &self,
        other: &Self,
        operation: ComparisonOperation,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        Ok(ordvar_execution_work(self, other, operation))
    }
}
impl CheckedNativeEqualityLeaf for OrdVar {}
impl CheckedNativeOrderingLeaf for OrdVar {}

impl sealed::EqualityLeaf for Binder<String> {
    fn equality_work<E>(
        &self,
        _: &Self,
        negated: bool,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        Ok(if negated { 9 } else { 8 })
    }
}
impl CheckedNativeEqualityLeaf for Binder<String> {}

fn binder_vector_equality_work(left: usize, right: usize, negated: bool) -> Option<usize> {
    let fixed = if negated { 8 } else { 7 };
    let extent = if left == right { left } else { 0 };
    extent.checked_mul(11)?.checked_add(fixed)
}

impl sealed::EqualityLeaf for Vec<Binder<String>> {
    fn equality_work<E>(
        &self,
        other: &Self,
        negated: bool,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        binder_vector_equality_work(self.len(), other.len(), negated)
            .ok_or(BindingFailure::SizeOverflow)
    }
}
impl CheckedNativeEqualityLeaf for Vec<Binder<String>> {}

fn multi_pattern_order_work(left: usize, right: usize) -> Option<usize> {
    match left == right {
        true => left.checked_mul(80)?.checked_add(27),
        false => Some(5),
    }
}

/// Admit the unchanged generated single-binder hash-pattern ordering expression.
///
/// This is not Binder Ord and does not execute or return a comparator. Generated
/// checked code must immediately run its existing expression on these unchanged
/// operands, once. Scope-body access and task scheduling are separately charged.
/// The 71 execution groups cover two fresh native Binder hashes and comparison,
/// not Fx hashing, arbitrary hashers, retained storage or a reusable receipt.
#[doc(hidden)]
pub fn precharge_generated_single_pattern_order<E>(
    _left: &Binder<String>,
    _right: &Binder<String>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), NativeComparisonFailure<E>> {
    admit_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |_| Ok(71))
}

/// Admit the existing length-first generated multi-binder ordering expression.
///
/// Unequal lengths reserve five execution groups without visiting any binder.
/// Equal lengths reserve 27 setup/terminal groups and 80 per possible visited
/// pair before native iteration; early inequality does not refund admission.
/// Only the lengths are inspected after the metadata reservation. The same
/// immediate, once-only expression contract as the single-binder helper applies.
#[doc(hidden)]
pub fn precharge_generated_multi_pattern_order<E>(
    left: &Vec<Binder<String>>,
    right: &Vec<Binder<String>>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), NativeComparisonFailure<E>> {
    admit_native_work(reserve, CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE, |_| {
        multi_pattern_order_work(left.len(), right.len()).ok_or(BindingFailure::SizeOverflow)
    })
}

#[path = "checked_cmp_flt.rs"]
mod flt;

#[cfg(test)]
#[path = "checked_cmp_flt_tests.rs"]
mod flt_tests;

#[cfg(test)]
#[path = "checked_cmp_tests.rs"]
mod tests;
