//! Typed operations for the generated, resource-admitted binding worker.
//!
//! Leaves own their copy contract: there is no blanket `Clone + BoundTerm`
//! fallback that could conceal recursive work. The caller supplies its existing
//! reservation function; this module does not create a budget or fresh names.
//! A copy costs one logical record (four retention units) plus its owned bytes,
//! and one work unit plus those bytes. These are logical charges, not allocator
//! capacity or wall-clock bounds. Variable inspection and each ordered identity
//! comparison are admitted separately, allowing cancellation during lookup.

use crate::{
    Binder, BoundVar, CanonicalBigInt, CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat32,
    CanonicalFloat64, FltNode, FltTemplatePiece, FreeVar, OrdVar, Var,
};
use moniker::{BinderIndex, ScopeState};
use std::sync::Arc;

pub(crate) const BINDING_RECORD_UNITS: usize = 4;

/// A copy or known-roster binding operation; no implicit freshening occurs.
#[derive(Clone, Copy, Debug)]
pub enum BindingOperation<'a> {
    Clone,
    Open {
        state: ScopeState,
        binders: &'a [Binder<String>],
    },
    Close {
        state: ScopeState,
        binders: &'a [Binder<String>],
    },
}

impl<'a> BindingOperation<'a> {
    /// The initial inherited depth; cloning has no binding depth.
    pub fn state(self) -> ScopeState {
        match self {
            Self::Clone => ScopeState::new(),
            Self::Open { state, .. } | Self::Close { state, .. } => state,
        }
    }

    /// Use a work item's inherited depth without copying or replacing its roster.
    pub fn with_state(self, state: ScopeState) -> Self {
        match self {
            Self::Clone => Self::Clone,
            Self::Open { binders, .. } => Self::Open { state, binders },
            Self::Close { binders, .. } => Self::Close { state, binders },
        }
    }

    /// Derive a scope body's operation from its parent, not a preceding sibling.
    ///
    /// Clone keeps its shallow scope-body boundary. Opening/closing increments
    /// exactly once, rejecting overflow before Moniker's unchecked increment.
    /// The worker must admit its traversal step before calling this pure helper.
    pub fn under_scope<E>(self) -> Result<Self, BindingFailure<E>> {
        match self {
            Self::Clone => Ok(Self::Clone),
            Self::Open { state, .. } | Self::Close { state, .. } => {
                checked_scope_successor::<E>(state.depth().0)?;
                Ok(self.with_state(state.incr()))
            },
        }
    }
}

fn checked_scope_successor<E>(depth: u32) -> Result<u32, BindingFailure<E>> {
    depth
        .checked_add(1)
        .ok_or(BindingFailure::ScopeDepthOverflow)
}

/// Refusal before an unadmitted copy or an invalid binding operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingFailure<E> {
    Reservation(E),
    SizeOverflow,
    BinderIndexOverflow,
    ScopeDepthOverflow,
    MissingBinder { index: usize },
    Slot(BindingSlotError),
}

/// A malformed internal result-slot operation, distinct from budget refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingSlotError {
    OutOfBounds { slot: usize, len: usize },
    Occupied { slot: usize },
    Empty { slot: usize },
    WrongCategory { slot: usize },
}

/// Append an admitted range of empty indexed result cells without moving values
/// out of the existing prefix. The returned index starts the new range.
///
/// This reserves cell initialization work and logical cell records, not the
/// category values later stored there. The producer admits those separately.
pub fn append_binding_slots<T, E>(
    slots: &mut Vec<Option<T>>,
    count: usize,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<usize, BindingFailure<E>> {
    let start = slots.len();
    let end = start
        .checked_add(count)
        .ok_or(BindingFailure::SizeOverflow)?;
    reserve_binding_parts(count, count, 0, reserve)?;
    slots.resize_with(end, || None);
    Ok(start)
}

/// Fill exactly one empty slot after checking its category and occupancy.
///
/// `accepts` must be the generated constant-time category-discriminant check.
/// The caller already owns `value` and must have admitted its construction and
/// normal cleanup. Refusal leaves all slots unchanged and drops that value.
pub fn write_binding_slot<T, E>(
    slots: &mut [Option<T>],
    slot: usize,
    value: T,
    accepts: impl FnOnce(&T) -> bool,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    reserve(1, 0).map_err(BindingFailure::Reservation)?;
    if !accepts(&value) {
        return Err(BindingFailure::Slot(BindingSlotError::WrongCategory { slot }));
    }
    let len = slots.len();
    let cell = slots
        .get_mut(slot)
        .ok_or(BindingFailure::Slot(BindingSlotError::OutOfBounds { slot, len }))?;
    if cell.is_some() {
        return Err(BindingFailure::Slot(BindingSlotError::Occupied { slot }));
    }
    *cell = Some(value);
    Ok(())
}

/// Take one ready result, validating its category before removing it.
///
/// A refusal never consumes the cell. Earlier successful takes in an assembly
/// are not rolled back; the owning worker must clean up its admitted partial
/// results. `accepts` must inspect only the generated category discriminant.
pub fn take_binding_slot<T, E>(
    slots: &mut [Option<T>],
    slot: usize,
    accepts: impl FnOnce(&T) -> bool,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<T, BindingFailure<E>> {
    reserve(1, 0).map_err(BindingFailure::Reservation)?;
    let len = slots.len();
    let cell = slots
        .get_mut(slot)
        .ok_or(BindingFailure::Slot(BindingSlotError::OutOfBounds { slot, len }))?;
    let value = cell
        .as_ref()
        .ok_or(BindingFailure::Slot(BindingSlotError::Empty { slot }))?;
    if !accepts(value) {
        return Err(BindingFailure::Slot(BindingSlotError::WrongCategory { slot }));
    }
    Ok(cell
        .take()
        .expect("checked binding result remains present after category validation"))
}

/// Explicit copy/binding contract for a non-category payload.
///
/// Implementations must admit actual owned copies and traversal before doing
/// them, including normal cleanup of returned and private partial results.
/// They preserve the source on failure and use the supplied reservation for
/// cancellation inside loops. Recursive payloads must use their existing
/// explicit worker; being a native field does not imply a constant-time clone.
pub trait CheckedBindingLeaf: Sized {
    fn try_copy_binding<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>>;
}

/// Resource-admitted category traversal over the generated explicit worklist.
///
/// Unlike a native leaf, a category schedules its recursive fields on that
/// worklist. Implementations must not delegate recursive category children to
/// `BoundTerm`, `Clone`, or this trait on each descent. The input stays borrowed
/// and unchanged; every owned result and traversal uses the caller's meter.
pub trait CheckedIterativeBinding: Sized {
    fn try_copy_iterative<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>>;
}

impl CheckedIterativeBinding for OrdVar {
    fn try_copy_iterative<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        self.try_copy_binding(operation, reserve)
    }
}

/// Boundary adapter, not a substitute for scheduling nested category fields.
impl<T: CheckedIterativeBinding> CheckedIterativeBinding for Arc<T> {
    fn try_copy_iterative<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // Standalone wrapper construction/copy, automatic release, and final
        // owner check. A produced child's own cleanup is already admitted.
        // Generated field extraction has a different Arc lifecycle recipe.
        reserve_binding_parts(3, 1, 0, reserve)?;
        match operation {
            BindingOperation::Clone => Ok(Arc::clone(self)),
            BindingOperation::Open { .. } | BindingOperation::Close { .. } => {
                let copied = self.as_ref().try_copy_iterative(operation, reserve)?;
                Ok(Arc::new(copied))
            },
        }
    }
}

/// Admit one leaf record and its owned bytes before copying it.
pub fn reserve_binding_copy<E>(
    owned_bytes: usize,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    reserve_binding_parts(1, 1, owned_bytes, reserve)
}

/// Admit separate work, logical copy records, and owned byte components.
///
/// This shares the leaf charge convention with composite native payloads.
/// All additions and multiplication are checked before invoking the caller.
pub fn reserve_binding_parts<E>(
    work: usize,
    records: usize,
    owned_bytes: usize,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    let work = work
        .checked_add(owned_bytes)
        .ok_or(BindingFailure::SizeOverflow)?;
    let units = records
        .checked_mul(BINDING_RECORD_UNITS)
        .and_then(|units| units.checked_add(owned_bytes))
        .ok_or(BindingFailure::SizeOverflow)?;
    reserve(work, units).map_err(BindingFailure::Reservation)
}

fn reserve_name<E>(
    name: &Option<String>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    reserve_name_record(name, NameRecordAdmission::Reserve, reserve)
}

// Only the binder-vector copy may use Prepaid, after admitting every entry's
// record before with_capacity. This is not a caller-selectable discount and
// does not bypass name work/bytes or change the existing FreeVar copy.
enum NameRecordAdmission {
    Reserve,
    Prepaid,
}

fn reserve_name_record<E>(
    name: &Option<String>,
    admission: NameRecordAdmission,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    reserve_binding_parts(
        1 + usize::from(name.is_some()),
        match admission {
            NameRecordAdmission::Reserve => 1,
            NameRecordAdmission::Prepaid => 0,
        },
        name.as_ref().map_or(0, String::len),
        reserve,
    )
}

fn copy_free_name<E>(
    name: &FreeVar<String>,
    admission: NameRecordAdmission,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<FreeVar<String>, BindingFailure<E>> {
    reserve_name_record(&name.pretty_name, admission, reserve)?;
    Ok(name.clone())
}

impl CheckedBindingLeaf for FreeVar<String> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // Moniker's FreeVar BoundTerm operations are no-ops, unlike Var::Free.
        copy_free_name(self, NameRecordAdmission::Reserve, reserve)
    }
}

fn copy_binder<E>(
    binder: &Binder<String>,
    admission: NameRecordAdmission,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<Binder<String>, BindingFailure<E>> {
    // Transparent wrapper construction and normal flat teardown. The
    // contained FreeVar record is also the Binder's in-place storage.
    reserve_binding_parts(2, 0, 0, reserve)?;
    Ok(Binder(copy_free_name(&binder.0, admission, reserve)?))
}

impl CheckedBindingLeaf for Binder<String> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // Binder BoundPattern open/close are no-ops: never freshen the name
        // or interpret its identity as an occurrence to close against a roster.
        copy_binder(self, NameRecordAdmission::Reserve, reserve)
    }
}

impl CheckedBindingLeaf for Vec<Binder<String>> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        let records = self
            .len()
            .checked_add(1)
            .ok_or(BindingFailure::SizeOverflow)?;
        // Header construction/cleanup and ALL in-place FreeVar records are
        // admitted before allocation. Per-entry name work and bytes remain
        // cancellable; their record component is already paid exactly once.
        reserve_binding_parts(2, records, 0, reserve)?;
        let mut copied = Vec::with_capacity(self.len());
        for binder in self {
            // Logical copy-loop insertion and normal cleanup entry dispatch.
            // Each Binder/FreeVar below additionally pays its own flat work.
            reserve_binding_parts(2, 0, 0, reserve)?;
            copied.push(copy_binder(binder, NameRecordAdmission::Prepaid, reserve)?);
        }
        Ok(copied)
    }
}

impl CheckedBindingLeaf for OrdVar {
    fn try_copy_binding<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        reserve(1, 0).map_err(BindingFailure::Reservation)?;
        match (operation, &self.0) {
            (BindingOperation::Close { state, binders }, Var::Free(free)) => {
                for (index, binder) in binders.iter().enumerate() {
                    reserve(1, 0).map_err(BindingFailure::Reservation)?;
                    if binder.0 == *free {
                        let index = u32::try_from(index)
                            .map_err(|_| BindingFailure::BinderIndexOverflow)?;
                        reserve_name(&free.pretty_name, reserve)?;
                        return Ok(OrdVar(Var::Bound(BoundVar {
                            scope: state.depth(),
                            binder: BinderIndex(index),
                            pretty_name: free.pretty_name.clone(),
                        })));
                    }
                }
                reserve_name(&free.pretty_name, reserve)?;
                Ok(self.clone())
            },
            (BindingOperation::Open { state, binders }, Var::Bound(bound))
                if bound.scope == state.depth() =>
            {
                let index = bound.binder.to_usize();
                let binder = binders
                    .get(index)
                    .ok_or(BindingFailure::MissingBinder { index })?;
                // Opening uses the selected binder's name, not the bound hint.
                Ok(OrdVar(Var::Free(
                    binder
                        .0
                        .try_copy_binding(BindingOperation::Clone, reserve)?,
                )))
            },
            (_, Var::Free(free)) => {
                reserve_name(&free.pretty_name, reserve)?;
                Ok(self.clone())
            },
            (_, Var::Bound(bound)) => {
                reserve_name(&bound.pretty_name, reserve)?;
                Ok(self.clone())
            },
        }
    }
}

macro_rules! fixed_copy_leaves {
    ($($ty:ty),* $(,)?) => {$(
        impl CheckedBindingLeaf for $ty {
            fn try_copy_binding<E>(
                &self,
                _: BindingOperation<'_>,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<Self, BindingFailure<E>> {
                reserve_binding_copy(0, reserve)?;
                Ok(*self)
            }
        }
    )*};
}

// Canonical arbitrary-precision values are existing Copy handles. Their clone
// does not duplicate the numeric magnitude; allocation lifetime is separate.
fixed_copy_leaves!(
    (),
    bool,
    char,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    f32,
    f64,
    CanonicalFloat32,
    CanonicalFloat64,
    CanonicalBigInt,
    CanonicalBigRat,
    CanonicalFixedPoint,
);

impl CheckedBindingLeaf for String {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // One owned buffer copy plus its eventual flat cleanup.
        reserve_binding_parts(2, 1, self.len(), reserve)?;
        Ok(self.clone())
    }
}

impl CheckedBindingLeaf for Vec<u8> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        reserve_binding_parts(2, 1, self.len(), reserve)?;
        Ok(self.clone())
    }
}

impl CheckedBindingLeaf for crate::BehavioralPred {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // Moniker binding is a no-op for this carrier. Its clone is recursive
        // in shape, so reuse its existing explicit worker with the same meter.
        self.try_clone_with(&mut |work, records, bytes| {
            reserve_binding_parts(work, records, bytes, reserve)
        })
    }
}

fn add_copy_component<E>(total: &mut usize, amount: usize) -> Result<(), BindingFailure<E>> {
    *total = total
        .checked_add(amount)
        .ok_or(BindingFailure::SizeOverflow)?;
    Ok(())
}

#[cfg(test)]
mod state_tests {
    use super::{checked_scope_successor, BindingFailure};

    #[test]
    fn scope_successor_guards_the_full_u32_boundary() {
        for depth in [0, 1, 17, u32::MAX - 1] {
            assert_eq!(checked_scope_successor::<()>(depth), Ok(depth + 1));
        }
        assert_eq!(
            checked_scope_successor::<()>(u32::MAX),
            Err(BindingFailure::ScopeDepthOverflow),
        );
    }
}

impl CheckedBindingLeaf for FltNode {
    fn try_copy_binding<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // The caller may supply a programmatically constructed node. Its
        // declared bounds are metadata, never a receipt for actual copy work.
        let inspection = self
            .holes
            .len()
            .checked_add(self.pieces.len())
            .and_then(|entries| entries.checked_add(1))
            .ok_or(BindingFailure::SizeOverflow)?;
        reserve(inspection, 0).map_err(BindingFailure::Reservation)?;
        let mut bytes = 0;
        for field in [
            &self.selector_name,
            &self.category,
            &self.open_src,
            &self.body_src,
            &self.close_src,
        ] {
            add_copy_component(&mut bytes, field.len())?;
        }
        // Node + five String headers + two Vec headers. Entry records and
        // their String headers follow; this is not physical allocator size.
        let mut records = 8;
        for hole in &self.holes {
            reserve(0, 0).map_err(BindingFailure::Reservation)?;
            add_copy_component(&mut records, 2)?;
            add_copy_component(&mut bytes, hole.name.len())?;
            if let Some(category) = &hole.category {
                add_copy_component(&mut records, 1)?;
                add_copy_component(&mut bytes, category.len())?;
            }
        }
        for piece in &self.pieces {
            reserve(0, 0).map_err(BindingFailure::Reservation)?;
            add_copy_component(&mut records, 1)?;
            if let FltTemplatePiece::Text { text, .. } = piece {
                add_copy_component(&mut records, 1)?;
                add_copy_component(&mut bytes, text.len())?;
            }
        }
        // The FLT's concrete flat shape has one teardown event per payload
        // record (FlatBindingLeafReservation.v). This is not a generic native
        // record rule. The selector admits its own copy and cleanup separately.
        let work = records.checked_mul(2).ok_or(BindingFailure::SizeOverflow)?;
        let selector = self.selector.try_copy_binding(operation, reserve)?;
        reserve_binding_parts(work, records, bytes, reserve)?;
        // Only the selector is bound. These flat payload clones preserve
        // structural hole identity/order and literal guest text exactly.
        // Do not invoke a constructor: it would validate or rebuild syntax.
        Ok(Self {
            selector,
            selector_name: self.selector_name.clone(),
            category: self.category.clone(),
            open_src: self.open_src.clone(),
            body_src: self.body_src.clone(),
            holes: self.holes.clone(),
            pieces: self.pieces.clone(),
            close_src: self.close_src.clone(),
            bounds: self.bounds,
            position: self.position,
        })
    }
}

/// Captured FLT payload boundary, not a recursive category-child traversal.
/// Clone shares the source-pinned payload; binding copies only through the
/// existing selector-aware leaf contract, preserving guest text and holes.
impl CheckedBindingLeaf for Arc<FltNode> {
    fn try_copy_binding<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // FlatBindingLeafReservation's standalone wrapper projection. The
        // copied payload independently admits its own construction/cleanup.
        reserve_binding_parts(3, 1, 0, reserve)?;
        match operation {
            BindingOperation::Clone => Ok(Arc::clone(self)),
            BindingOperation::Open { .. } | BindingOperation::Close { .. } => {
                let copied = self.as_ref().try_copy_binding(operation, reserve)?;
                Ok(Arc::new(copied))
            },
        }
    }
}
