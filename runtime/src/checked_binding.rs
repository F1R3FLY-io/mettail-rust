//! Typed leaf operations for the generated, resource-admitted binding worker.
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

/// Refusal before an unadmitted copy or an invalid binding operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingFailure<E> {
    Reservation(E),
    SizeOverflow,
    BinderIndexOverflow,
    MissingBinder { index: usize },
}

/// Explicit copy/binding contract for a non-category payload.
///
/// Implementations must admit actual owned copies and traversal before doing
/// them, preserve the source on failure, and use the supplied reservation for
/// cancellation inside loops. Recursive payloads must use their existing
/// explicit worker; being a native field does not imply a constant-time clone.
pub trait CheckedBindingLeaf: Sized {
    fn try_copy_binding<E>(
        &self,
        operation: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>>;
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
        .checked_mul(4)
        .and_then(|units| units.checked_add(owned_bytes))
        .ok_or(BindingFailure::SizeOverflow)?;
    reserve(work, units).map_err(BindingFailure::Reservation)
}

fn reserve_name<E>(
    name: &Option<String>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<(), BindingFailure<E>> {
    reserve_binding_copy(name.as_ref().map_or(0, String::len), reserve)
}

impl CheckedBindingLeaf for FreeVar<String> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        // Moniker's FreeVar BoundTerm operations are no-ops, unlike Var::Free.
        reserve_name(&self.pretty_name, reserve)?;
        Ok(self.clone())
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
        reserve_binding_copy(self.len(), reserve)?;
        Ok(self.clone())
    }
}

impl CheckedBindingLeaf for Vec<u8> {
    fn try_copy_binding<E>(
        &self,
        _: BindingOperation<'_>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, BindingFailure<E>> {
        reserve_binding_copy(self.len(), reserve)?;
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
        let selector = self.selector.try_copy_binding(operation, reserve)?;
        reserve_binding_parts(records, records, bytes, reserve)?;
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
