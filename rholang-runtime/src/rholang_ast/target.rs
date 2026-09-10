//! Direct interpretation of the initial neutral construction algebra.
//!
//! Values are owned `Par`s, not slots in a persistent node arena. Typed entry
//! points keep the existing lowerer's infallible primitive constructors and
//! binary append allocation behavior. The generic checked entry point shares
//! those exact implementations and rejects malformed arity before construction.

use mettail_rholang_frontend::construction::{
    CheckedBoundReference, ConstructionError, StructuralObservation, ValueOp, ValueTarget,
};
use models::rhoapi::Par;
use models::rust::utils::{
    new_boundvar_par, new_gbool_par, new_gint_par, new_gstring_par, new_wildcard_par,
};

pub(super) struct DirectNodeTarget;

impl DirectNodeTarget {
    pub(super) fn empty() -> Par {
        Par::default()
    }

    pub(super) fn integer(value: i64) -> Par {
        new_gint_par(value, Vec::new(), false)
    }

    pub(super) fn boolean(value: bool) -> Par {
        new_gbool_par(value, Vec::new(), false)
    }

    pub(super) fn text(value: String) -> Par {
        new_gstring_par(value, Vec::new(), false)
    }

    /// Integer/scope validation is carried by the descriptor. Resource
    /// reservation is the caller's separate obligation before invoking this.
    pub(super) fn bound(reference: CheckedBoundReference) -> Par {
        new_boundvar_par(reference.emitted_index(), Vec::new(), false)
    }

    pub(super) fn wildcard(connective: bool) -> Par {
        new_wildcard_par(Vec::new(), connective)
    }

    pub(super) fn append(left: Par, right: Par) -> Par {
        // Preserve the helper as-is: it clones left's vectors, takes right's,
        // then concat clones elements from both temporary sequences. This
        // adapter adds no further child vector or subtree clone.
        left.append(right)
    }

    pub(super) fn observation(value: &Par) -> StructuralObservation<'_> {
        StructuralObservation {
            single_string: super::is_single_gstring_value(value),
            locally_free: &value.locally_free,
            connective_used: value.connective_used,
        }
    }
}

impl ValueTarget for DirectNodeTarget {
    type Value = Par;

    fn construct(
        &mut self,
        operation: ValueOp,
        mut children: Vec<Par>,
    ) -> Result<Par, ConstructionError> {
        if children.len() != operation.arity() {
            return Err(ConstructionError::ChildArity {
                expected: operation.arity(),
                actual: children.len(),
            });
        }
        Ok(match operation {
            ValueOp::Empty => Self::empty(),
            ValueOp::Integer(value) => Self::integer(value),
            ValueOp::Boolean(value) => Self::boolean(value),
            ValueOp::Text(value) => Self::text(value),
            ValueOp::Bound { scope, index } => {
                Self::bound(CheckedBoundReference::new(scope, index)?)
            },
            ValueOp::Wildcard { connective } => Self::wildcard(connective),
            ValueOp::Append => {
                let right = children.pop().expect("validated binary arity: right");
                let left = children.pop().expect("validated binary arity: left");
                Self::append(left, right)
            },
        })
    }

    fn observe<'a>(
        &'a self,
        value: &'a Par,
    ) -> Result<StructuralObservation<'a>, ConstructionError> {
        Ok(Self::observation(value))
    }

    fn forward(&mut self, value: Par) -> Result<Par, ConstructionError> {
        Ok(value)
    }

    fn append(&mut self, left: Par, right: Par) -> Result<Par, ConstructionError> {
        Ok(Self::append(left, right))
    }
}

#[cfg(test)]
#[path = "target_tests.rs"]
mod tests;
