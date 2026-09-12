//! Paid flat metadata inspection for the original native FLT comparisons.
//!
//! AdmittedFltComparison.v composes the same paid-fold contract as native
//! hashing. These helpers inspect tags and actual lengths only. They do not
//! validate templates, compare payloads, hash identities, or copy source text.

use super::{
    ordvar_execution_work, sealed, string_execution_work, BindingFailure,
    CheckedNativeEqualityLeaf, CheckedNativeOrderingLeaf, ComparisonOperation,
};
use crate::{FltHole, FltNode, FltTemplatePiece};
use std::sync::Arc;

fn add<E>(left: usize, right: usize) -> Result<usize, BindingFailure<E>> {
    left.checked_add(right).ok_or(BindingFailure::SizeOverflow)
}

fn string_work<E>(
    left: &str,
    right: &str,
    operation: ComparisonOperation,
) -> Result<usize, BindingFailure<E>> {
    string_execution_work(left.len(), right.len(), operation).ok_or(BindingFailure::SizeOverflow)
}

fn hole_work<E>(
    left: &FltHole,
    right: &FltHole,
    operation: ComparisonOperation,
) -> Result<usize, BindingFailure<E>> {
    let category = match (&left.category, &right.category) {
        (Some(left), Some(right)) => add(6, string_work(left, right, operation)?)?,
        _ => 5,
    };
    add(add(16, string_work(&left.name, &right.name, operation)?)?, category)
}

fn piece_work<E>(
    left: &FltTemplatePiece,
    right: &FltTemplatePiece,
    operation: ComparisonOperation,
) -> Result<usize, BindingFailure<E>> {
    match (left, right) {
        (FltTemplatePiece::Text { text: left, .. }, FltTemplatePiece::Text { text: right, .. }) => {
            add(14, string_work(left, right, operation)?)
        },
        (FltTemplatePiece::Hole { .. }, FltTemplatePiece::Hole { .. }) => Ok(18),
        _ => Ok(5),
    }
}

// Only concrete fixed-shape holes/pieces instantiate this private fold. The
// root reservation pays iterator setup; every possible paired next, including
// terminal next, is admitted before it occurs. No pair roster is allocated.
fn inspect_vector<T, E>(
    left: &[T],
    right: &[T],
    operation: ComparisonOperation,
    mut total: usize,
    item_work: fn(&T, &T, ComparisonOperation) -> Result<usize, BindingFailure<E>>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<usize, BindingFailure<E>> {
    let step = match operation {
        ComparisonOperation::Cmp => 4,
        _ if left.len() != right.len() => return Ok(total),
        _ => 3,
    };
    let mut pairs = left.iter().zip(right.iter());
    loop {
        reserve(1, 0).map_err(BindingFailure::Reservation)?;
        let Some((left, right)) = pairs.next() else {
            break;
        };
        total = add(total, add(step, item_work(left, right, operation)?)?)?;
    }
    Ok(total)
}

// Called only after the public runner's root reservation. Ne uses one default
// negation around the whole derived equality, not Ne on each derived field.
// All ten fields are covered: the fixed group includes scalar provenance,
// five bound scalars and both vector headers; actual strings and paired items
// provide the variable extent. Even malformed declared bounds are only scalars.
fn node_work<E>(
    left: &FltNode,
    right: &FltNode,
    operation: ComparisonOperation,
    forwarding: usize,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<usize, BindingFailure<E>> {
    let (base, payload_operation) = match operation {
        ComparisonOperation::Eq => (43, ComparisonOperation::Eq),
        ComparisonOperation::Ne => (44, ComparisonOperation::Eq),
        ComparisonOperation::Cmp => (51, ComparisonOperation::Cmp),
    };
    let mut total = add(base, forwarding)?;
    total = add(total, ordvar_execution_work(&left.selector, &right.selector, payload_operation))?;
    total = add(
        total,
        string_work(&left.selector_name, &right.selector_name, payload_operation)?,
    )?;
    total = add(total, string_work(&left.category, &right.category, payload_operation)?)?;
    total = add(total, string_work(&left.open_src, &right.open_src, payload_operation)?)?;
    total = add(total, string_work(&left.body_src, &right.body_src, payload_operation)?)?;
    total = add(total, string_work(&left.close_src, &right.close_src, payload_operation)?)?;
    total =
        inspect_vector(&left.holes, &right.holes, payload_operation, total, hole_work, reserve)?;
    inspect_vector(&left.pieces, &right.pieces, payload_operation, total, piece_work, reserve)
}

impl sealed::Leaf for FltNode {
    fn execution_work<E>(
        &self,
        other: &Self,
        operation: ComparisonOperation,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        node_work(self, other, operation, 0, reserve)
    }
}
impl CheckedNativeEqualityLeaf for FltNode {}
impl CheckedNativeOrderingLeaf for FltNode {}

impl sealed::Leaf for Arc<FltNode> {
    fn execution_work<E>(
        &self,
        other: &Self,
        operation: ComparisonOperation,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        match operation {
            ComparisonOperation::Eq | ComparisonOperation::Ne if Arc::ptr_eq(self, other) => Ok(3),
            ComparisonOperation::Eq | ComparisonOperation::Ne => {
                node_work(self, other, operation, 4, reserve)
            },
            ComparisonOperation::Cmp => node_work(self, other, operation, 2, reserve),
        }
    }
}
impl CheckedNativeEqualityLeaf for Arc<FltNode> {}
impl CheckedNativeOrderingLeaf for Arc<FltNode> {}
