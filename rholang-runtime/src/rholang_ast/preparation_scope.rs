//! Paid adapters around the existing scope, URI and descriptor semantics.
//!
//! Freshening/opening uses the checked binding worker. URI ordering uses the
//! same stable merge machine as collection operations and keeps whole pairs.
//! Descriptor validation remains owned by CheckedFreshDescriptor; only its
//! borrowed inspection and string-comparison allowance are prepared here.
//! Environment derivation already has its own paid adapter in preparation_env.
//! These logical work/retention charges are not allocator or RSS bounds.

use super::*;
use mettail_runtime::{
    BindingFailure, BindingOperation, CheckedBindingLeaf, CheckedNativeEqualityLeaf,
    CheckedNativeOrderingLeaf, NativeComparisonFailure,
};

/// Reservation failures keep the original lowerer error without recursive
/// boxing; other binding refusals retain their complete structured diagnostic.
pub(super) fn binding_failure(error: BindingFailure<RholangAstLowerError>) -> RholangAstLowerError {
    use BindingFailure::*;
    RholangAstLowerError::Binding(match error {
        Reservation(error) => return error,
        UnsupportedProfile => UnsupportedProfile,
        UnsupportedConstructor { category, constructor } => {
            UnsupportedConstructor { category, constructor }
        },
        InvalidCollectionInput(reason) => InvalidCollectionInput(reason),
        SizeOverflow => SizeOverflow,
        BinderIndexOverflow => BinderIndexOverflow,
        ScopeDepthOverflow => ScopeDepthOverflow,
        MissingBinder { index } => MissingBinder { index },
        Slot(error) => Slot(error),
    })
}

fn native_failure(error: NativeComparisonFailure<RholangAstLowerError>) -> RholangAstLowerError {
    binding_failure(error.into())
}

pub(super) fn reserve_parts(
    work: usize,
    records: usize,
    bytes: usize,
    reserve: &mut StorageReservation<'_>,
) -> Result<(), RholangAstLowerError> {
    mettail_runtime::reserve_binding_parts(work, records, bytes, &mut |w, u| reserve(w, u))
        .map_err(binding_failure)
}

fn copied<T: CheckedBindingLeaf>(
    source: &T,
    reserve: &mut StorageReservation<'_>,
) -> Result<T, RholangAstLowerError> {
    source
        .try_copy_binding(BindingOperation::Clone, &mut |w, u| reserve(w, u))
        .map_err(binding_failure)
}

pub(super) fn open(
    scope: &mettail_runtime::Scope<Vec<Binder<String>>, Arc<Proc>>,
    reserve: &mut StorageReservation<'_>,
) -> Result<(Vec<Binder<String>>, Arc<Proc>), RholangAstLowerError> {
    scope
        .try_unbind(&mut |w, u| reserve(w, u))
        .map_err(binding_failure)
}

pub(super) fn open_uri(
    uris: &[Uri],
    scope: &mettail_runtime::Scope<Vec<Binder<String>>, Arc<Proc>>,
    reserve: &mut StorageReservation<'_>,
) -> Result<(Vec<Binder<String>>, Arc<Proc>, Vec<String>), RholangAstLowerError> {
    // Preserve original validation order: opening, cardinality, envelope,
    // ordering, duplicates, then projections. No URI is parsed a second time.
    let (binders, body) = open(scope, reserve)?;
    reserve_parts(4, 0, 0, reserve)?;
    if binders.len() != uris.len() || binders.is_empty() {
        return Err(RholangAstLowerError::InvalidUriBindings {
            binders: binders.len(),
            uris: uris.len(),
        });
    }
    let count = binders.len();
    let slots = count
        .checked_add(1)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    reserve_parts(3, slots, 0, reserve)?;
    let mut pairs = Vec::with_capacity(count);
    let mut inputs = binders.into_iter().zip(uris);
    loop {
        reserve_parts(2, 0, 0, reserve)?;
        let Some((binder, uri)) = inputs.next() else {
            break;
        };
        reserve_parts(6, 0, 0, reserve)?;
        let text = match uri {
            Uri::UriText(value) => value
                .strip_prefix('`')
                .and_then(|value| value.strip_suffix('`'))
                .filter(|value| !value.is_empty())
                .ok_or(RholangAstLowerError::InvalidUriLiteral)?,
            _ => return Err(RholangAstLowerError::InvalidUriLiteral),
        };
        // The pair slot is already admitted; this pays the new String value
        // and its owned bytes before the native copy and eventual cleanup.
        reserve_parts(2, 1, text.len(), reserve)?;
        pairs.push((text.to_owned(), binder));
    }
    let sorted = mettail_runtime::try_sort_borrowed_by(
        &pairs,
        &mut |w, u| reserve(w, u),
        |left, right, reserve| left.0.try_native_cmp(&right.0, reserve),
    )
    .map_err(native_failure)?;

    reserve_parts(1, 1, 0, reserve)?;
    let mut adjacent = sorted.windows(2);
    loop {
        reserve_parts(2, 0, 0, reserve)?;
        let Some(pair) = adjacent.next() else { break };
        if pair[0]
            .0
            .try_native_eq(&pair[1].0, &mut |w, u| reserve(w, u))
            .map_err(native_failure)?
        {
            return Err(RholangAstLowerError::DuplicateUriBinding(copied(&pair[0].0, reserve)?));
        }
    }
    // Output slots and headers are distinct from the copied leaf records.
    let output_slots = slots
        .checked_mul(2)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    reserve_parts(3, output_slots, 0, reserve)?;
    let mut ordered_binders = Vec::with_capacity(count);
    let mut ordered_uris = Vec::with_capacity(count);
    let mut sorted = sorted.into_iter();
    loop {
        reserve_parts(3, 0, 0, reserve)?;
        let Some(pair) = sorted.next() else { break };
        ordered_uris.push(copied(&pair.0, reserve)?);
        ordered_binders.push(copied(&pair.1, reserve)?);
    }
    Ok((ordered_binders, body, ordered_uris))
}

/// Reserve the comparisons made by the unchanged descriptor validator.
/// Inspection does not compare keys or decide validity; it borrows the same
/// immutable pair and pays its existing native comparator allowance first.
fn admit_order_validation(
    values: &[String],
    reserve: &mut StorageReservation<'_>,
) -> Result<(), RholangAstLowerError> {
    reserve_parts(2, 1, 0, reserve)?;
    let mut pairs = values.windows(2);
    loop {
        // Both this inspection loop and the later validator loop/control.
        reserve_parts(4, 0, 0, reserve)?;
        let Some(pair) = pairs.next() else { break };
        let work = pair[0]
            .try_inspect_native_cmp_work(&pair[1], &mut |w, u| reserve(w, u))
            .map_err(native_failure)?;
        reserve(work, 0)?;
    }
    Ok(())
}

pub(super) fn descriptor(
    shape: FreshShape,
    imports: &imports::CheckedCallerImports,
    reserve: &mut StorageReservation<'_>,
) -> Result<Box<CheckedFreshDescriptor>, RholangAstLowerError> {
    let keys = imports.keys_with_reservation(reserve)?;
    // Layout/count/arity checks, descriptor construction, and its Box owner.
    reserve_parts(12, 2, 0, reserve)?;
    if let FreshShape::Uri { uris, .. } = &shape {
        admit_order_validation(uris, reserve)?;
    }
    admit_order_validation(&keys, reserve)?;
    CheckedFreshDescriptor::new(shape, keys)
        .map(Box::new)
        .map_err(RholangAstLowerError::FreshConstruction)
}

#[cfg(test)]
#[path = "preparation_scope_tests.rs"]
mod tests;
