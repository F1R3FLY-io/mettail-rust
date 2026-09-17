//! Checked transport of the existing node caller map, without value conversion.
//!
//! This checks the finite direct import profile, not arbitrary Par normality or
//! language authority. The provider checks opaque tokens at semantic use. The
//! original payloads, including map order/multiplicity and private IDs, survive
//! unchanged. Quoted values have the same carrier; arbitrary quoted executable
//! processes are not accepted by the existing injection reducer.
//!
//! Admission borrows each structural child on an explicit worklist, charging
//! its occurrence before pushing it. Source-New copies reuse the node's
//! generated stack-safe Clone; total preparation/output charging is a separate
//! enclosing obligation, not established by this import-only bound.

use super::*;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rust::rholang::par_children::expr_instance_child_pars;

/// Import-only bounds; these are not semantic gas or process RSS estimates.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ImportLimits {
    pub(crate) entries: usize,
    pub(crate) nodes: usize,
    pub(crate) payload_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImportResource {
    Entries,
    Nodes,
    PayloadBytes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImportShapeError {
    ProcessSidecar,
    OpenMetadata,
    RootNil,
    NotSingleton,
    MissingInstance,
    OpenCollection,
    MissingMapField,
    UnsupportedExpression,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImportAdmissionError {
    Cancelled,
    LimitExceeded(ImportResource),
    AllocationFailed,
    Shape(ImportShapeError),
}

/// Original entries in strict string-key order. Only checked admission or the
/// inherently valid empty table constructs this value.
#[derive(Default)]
pub(crate) struct CheckedCallerImports {
    entries: Vec<(String, Par)>,
}

impl CheckedCallerImports {
    pub(crate) fn admit(
        source: HashMap<String, Par>,
        limits: ImportLimits,
        cancelled: &mut impl FnMut() -> bool,
    ) -> Result<Self, ImportAdmissionError> {
        poll(cancelled)?;
        bounded_add(0, source.len(), limits.entries, ImportResource::Entries)?;
        let mut meter = ImportMeter { limits, nodes: 0, payload_bytes: 0 };
        // Charge before retaining an ordered roster. Values are still borrowed.
        // Key comparison work is bounded by the admitted entry/payload sizes;
        // sort is bracketed by cancellation polls, not a separate resolver.
        for key in source.keys() {
            poll(cancelled)?;
            meter.bytes(key.len())?;
        }
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(source.len())
            .map_err(|_| ImportAdmissionError::AllocationFailed)?;
        entries.extend(source);
        entries.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        poll(cancelled)?;
        // Validate in canonical key order, not randomized HashMap order.
        for (_, value) in &entries {
            validate_value(value, &mut meter, cancelled)?;
        }
        poll(cancelled)?;
        Ok(Self { entries })
    }

    pub(super) fn keys(&self) -> Vec<String> {
        self.entries.iter().map(|(key, _)| key.clone()).collect()
    }

    pub(super) fn keys_with_reservation(
        &self,
        reserve: &mut StorageReservation<'_>,
    ) -> Result<Vec<String>, RholangAstLowerError> {
        use mettail_runtime::{BindingOperation, CheckedBindingLeaf};
        let slots = self
            .entries
            .len()
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        preparation_scope::reserve_parts(3, slots, 0, reserve)?;
        let mut keys = Vec::with_capacity(self.entries.len());
        let mut entries = self.entries.iter();
        loop {
            preparation_scope::reserve_parts(2, 0, 0, reserve)?;
            let Some((key, _)) = entries.next() else {
                break;
            };
            keys.push(
                key.try_copy_binding(BindingOperation::Clone, &mut |w, u| reserve(w, u))
                    .map_err(preparation_scope::binding_failure)?,
            );
        }
        Ok(keys)
    }

    pub(super) fn values(&self) -> Vec<Par> {
        self.entries
            .iter()
            .map(|(_, value)| value.clone())
            .collect()
    }
}

impl BoundEnv {
    /// Install an already admitted map without turning its URI keys into
    /// lexical binders. Scope extension shares the immutable original roster.
    pub(crate) fn with_caller_imports(mut self, imports: CheckedCallerImports) -> Self {
        self.caller_imports = Arc::new(imports);
        self
    }
}

fn poll(cancelled: &mut impl FnMut() -> bool) -> Result<(), ImportAdmissionError> {
    match cancelled() {
        true => Err(ImportAdmissionError::Cancelled),
        false => Ok(()),
    }
}

fn bounded_add(
    used: usize,
    amount: usize,
    limit: usize,
    resource: ImportResource,
) -> Result<usize, ImportAdmissionError> {
    used.checked_add(amount)
        .filter(|next| *next <= limit)
        .ok_or(ImportAdmissionError::LimitExceeded(resource))
}

struct ImportMeter {
    limits: ImportLimits,
    nodes: usize,
    payload_bytes: usize,
}

impl ImportMeter {
    fn nodes(&mut self, count: usize) -> Result<(), ImportAdmissionError> {
        self.nodes = bounded_add(self.nodes, count, self.limits.nodes, ImportResource::Nodes)?;
        Ok(())
    }

    fn bytes(&mut self, count: usize) -> Result<(), ImportAdmissionError> {
        self.payload_bytes = bounded_add(
            self.payload_bytes,
            count,
            self.limits.payload_bytes,
            ImportResource::PayloadBytes,
        )?;
        Ok(())
    }
}

fn shape<T>(error: ImportShapeError) -> Result<T, ImportAdmissionError> {
    Err(ImportAdmissionError::Shape(error))
}

fn closed_par(par: &Par) -> Result<(), ImportAdmissionError> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return shape(ImportShapeError::ProcessSidecar);
    }
    match (par.locally_free.is_empty(), par.connective_used) {
        (true, false) => Ok(()),
        _ => shape(ImportShapeError::OpenMetadata),
    }
}

fn closed_collection(
    locally_free: &[u8],
    connective_used: bool,
    remainder: bool,
) -> Result<(), ImportAdmissionError> {
    match (locally_free.is_empty(), connective_used, remainder) {
        (true, false, false) => Ok(()),
        _ => shape(ImportShapeError::OpenCollection),
    }
}

fn validate_value(
    root: &Par,
    meter: &mut ImportMeter,
    cancelled: &mut impl FnMut() -> bool,
) -> Result<(), ImportAdmissionError> {
    poll(cancelled)?;
    meter.nodes(1)?;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(1)
        .map_err(|_| ImportAdmissionError::AllocationFailed)?;
    pending.push(root);
    let mut at_root = true;
    while let Some(par) = pending.pop() {
        poll(cancelled)?;
        closed_par(par)?;
        match (par.exprs.as_slice(), par.unforgeables.as_slice()) {
            ([], []) => {
                if at_root {
                    return shape(ImportShapeError::RootNil);
                }
            },
            ([], [name]) => {
                let bytes = match name.unf_instance.as_ref() {
                    Some(UnfInstance::GPrivateBody(value)) => value.id.len(),
                    Some(UnfInstance::GDeployIdBody(value)) => value.sig.len(),
                    Some(UnfInstance::GDeployerIdBody(value)) => value.public_key.len(),
                    Some(UnfInstance::GSysAuthTokenBody(_)) => 0,
                    None => return shape(ImportShapeError::MissingInstance),
                };
                meter.bytes(bytes)?;
            },
            ([expr], []) => {
                let instance = expr
                    .expr_instance
                    .as_ref()
                    .ok_or(ImportAdmissionError::Shape(ImportShapeError::MissingInstance))?;
                let children = match instance {
                    ExprInstance::GBool(_) => {
                        meter.bytes(1)?;
                        0
                    },
                    ExprInstance::GInt(_) | ExprInstance::GDouble(_) => {
                        meter.bytes(8)?;
                        0
                    },
                    ExprInstance::GString(value) | ExprInstance::GUri(value) => {
                        meter.bytes(value.len())?;
                        0
                    },
                    ExprInstance::GByteArray(value) => {
                        meter.bytes(value.len())?;
                        0
                    },
                    ExprInstance::EListBody(list) => {
                        closed_collection(
                            &list.locally_free,
                            list.connective_used,
                            list.remainder.is_some(),
                        )?;
                        list.ps.len()
                    },
                    ExprInstance::EMapBody(map) => {
                        closed_collection(
                            &map.locally_free,
                            map.connective_used,
                            map.remainder.is_some(),
                        )?;
                        map.kvs
                            .len()
                            .checked_mul(2)
                            .ok_or(ImportAdmissionError::LimitExceeded(ImportResource::Nodes))?
                    },
                    // No computed expressions, pattern variables, live cursors,
                    // or unsupported collection/numeric families slip through.
                    _ => return shape(ImportShapeError::UnsupportedExpression),
                };
                meter.nodes(children)?;
                if let ExprInstance::EMapBody(map) = instance {
                    for entry in &map.kvs {
                        poll(cancelled)?;
                        match (&entry.key, &entry.value) {
                            (Some(_), Some(_)) => {},
                            _ => return shape(ImportShapeError::MissingMapField),
                        }
                    }
                }
                pending
                    .try_reserve_exact(children)
                    .map_err(|_| ImportAdmissionError::AllocationFailed)?;
                let start = pending.len();
                // Reuse the node's exhaustive structural child table only after
                // checking the supported shape, fields and allocation bound.
                expr_instance_child_pars(instance, &mut pending);
                debug_assert_eq!(pending.len() - start, children);
                pending[start..].reverse();
            },
            _ => return shape(ImportShapeError::NotSingleton),
        }
        at_root = false;
    }
    Ok(())
}

#[cfg(test)]
#[path = "imports_tests.rs"]
mod tests;
