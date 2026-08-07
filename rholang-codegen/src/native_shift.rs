//! Constant-size ABI and iterative implementation for composed de Bruijn shifts.
//!
//! A binder-template slot formerly emitted `k` nested `new/for/^shift` frames. Every nested
//! protobuf `Par` repeated a growing `locally_free` prefix, so a depth-`k` template occupied
//! quadratic bytes and allocation despite stack-safe construction. The replacement is one
//! system-process call carrying `[amount:u128-le, reflected_value, out]`. Its handler applies
//! the same `k` composed `oshift 0` operations in one explicit-work-stack traversal.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use mettail_ast::language::LanguageDef;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::{Par, Send};
use models::rust::utils::{new_elist_par, new_gbytearray_par, new_send_par};
use prost::Message;

use crate::rho_net_flt::bound_var_par;
use crate::rho_net_lower::{
    ground_marker_tag_par, is_marked_object_label, par_carries_ground_marker, parse_reflected_tag,
    reflect_tag, BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use crate::system_process_band::NATIVE_SHIFT_BAND;

const NATIVE_SHIFT_INDEX: u8 = 0;
const AMOUNT_BYTES: usize = size_of::<u128>();

/// Per-language native shift contract registration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeShiftSpec {
    fingerprint: String,
    object_arities: HashMap<String, usize>,
    hashbag_ops: HashSet<String>,
}

impl NativeShiftSpec {
    /// Derive exactly the successful subject domain of the generated in-Rho `^shift`
    /// receiver: its plain object-congruence arms and declared HashBag soup carriers.
    pub fn for_language(def: &LanguageDef, fingerprint: impl Into<String>) -> Self {
        Self::new(
            fingerprint,
            crate::rho_net_subst_trs::object_congruence_constructors(def),
            crate::rho_net_drive::hashbag_collection_ops(def),
        )
    }

    /// Construct an explicit shift domain. This is useful for a minimal binder-only
    /// runtime and keeps tests honest about which reflected constructors are installed.
    pub fn new(
        fingerprint: impl Into<String>,
        object_arities: impl IntoIterator<Item = (String, usize)>,
        hashbag_ops: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            fingerprint: fingerprint.into(),
            object_arities: object_arities.into_iter().collect(),
            hashbag_ops: hashbag_ops.into_iter().collect(),
        }
    }

    pub fn fingerprint(&self) -> &str {
        &self.fingerprint
    }

    fn object_arity(&self, label: &str) -> Option<usize> {
        self.object_arities.get(label).copied()
    }

    fn accepts_hashbag_op(&self, op: &str) -> bool {
        self.hashbag_ops.contains(op)
    }

    fn accepts_nil(&self) -> bool {
        !self.hashbag_ops.is_empty()
    }
}

/// A malformed value on which the in-Rho `^shift` family has no completing arm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeShiftError {
    MalformedAmount,
    AmountNotAddressable,
    MalformedReflectedValue,
    FingerprintMismatch,
    UnsupportedReflectedTerm,
    IndexOverflow,
}

impl std::fmt::Display for NativeShiftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::MalformedAmount => "shift amount is not one fixed-width u128 byte array",
                Self::AmountNotAddressable => "shift amount exceeds this machine's address space",
                Self::MalformedReflectedValue =>
                    "value is not a well-formed reflected term or HashBag soup",
                Self::FingerprintMismatch =>
                    "reflected value belongs to another language fingerprint",
                Self::UnsupportedReflectedTerm => {
                    "reflected term has no installed shift congruence arm"
                },
                Self::IndexOverflow => "shifted de Bruijn index is not addressable",
            }
        )
    }
}

impl std::error::Error for NativeShiftError {}

pub fn native_shift_channel(fingerprint: &str) -> Par {
    NATIVE_SHIFT_BAND.channel(NATIVE_SHIFT_INDEX, fingerprint)
}

pub fn native_shift_body_ref(fingerprint: &str) -> i64 {
    NATIVE_SHIFT_BAND.body_ref(NATIVE_SHIFT_INDEX, fingerprint)
}

pub fn native_shift_urn(fingerprint: &str) -> String {
    format!("mtl:shift:{fingerprint}")
}

/// Fixed-width architecture-independent amount encoding. The generated call stays constant-size
/// for every binder depth and contains no recursively nested numeral.
pub fn native_shift_amount_par(amount: usize) -> Par {
    new_gbytearray_par((amount as u128).to_le_bytes().to_vec(), Vec::new(), false)
}

/// Build the complete one-send shift ABI from already-addressed value/out processes.
/// Keeping this constructor here makes the constant-size property shared by production
/// carrier emission and the allocation/RSS regression binary.
pub fn native_shift_call_par(fingerprint: &str, amount: usize, value: Par, out: Par) -> Par {
    let channel = native_shift_channel(fingerprint);
    let amount = native_shift_amount_par(amount);
    let mut locally_free = channel.locally_free.clone();
    union_locally_free_into(&mut locally_free, &amount.locally_free);
    union_locally_free_into(&mut locally_free, &value.locally_free);
    union_locally_free_into(&mut locally_free, &out.locally_free);
    new_send_par(
        channel,
        vec![amount, value, out],
        false,
        locally_free.clone(),
        false,
        locally_free,
        false,
    )
}

pub fn decode_native_shift_amount(par: &Par) -> Result<usize, NativeShiftError> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.unforgeables.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return Err(NativeShiftError::MalformedAmount);
    }
    let [expr] = par.exprs.as_slice() else {
        return Err(NativeShiftError::MalformedAmount);
    };
    let Some(ExprInstance::GByteArray(bytes)) = expr.expr_instance.as_ref() else {
        return Err(NativeShiftError::MalformedAmount);
    };
    let bytes: [u8; AMOUNT_BYTES] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| NativeShiftError::MalformedAmount)?;
    usize::try_from(u128::from_le_bytes(bytes)).map_err(|_| NativeShiftError::AmountNotAddressable)
}

fn reflected_tag(par: &Par) -> Option<String> {
    if !par.exprs.is_empty()
        || !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return None;
    }
    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(private) => String::decode(private.id.as_slice()).ok(),
        _ => None,
    }
}

fn elist_values(par: &Par) -> Option<&[Par]> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.unforgeables.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return None;
    }
    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() else {
        return None;
    };
    (!list.connective_used && list.remainder.is_none()).then_some(list.ps.as_slice())
}

fn decode_peano(mut par: &Par, fingerprint: &str) -> Option<usize> {
    let zero = reflect_tag(fingerprint, PEANO_ZERO_REFLECT_LABEL);
    let succ = reflect_tag(fingerprint, PEANO_SUCC_REFLECT_LABEL);
    let mut value = 0usize;
    loop {
        let values = elist_values(par)?;
        let (head, children) = values.split_first()?;
        match reflected_tag(head)?.as_str() {
            tag if tag == zero => return children.is_empty().then_some(value),
            tag if tag == succ && children.len() == 1 => {
                value = value.checked_add(1)?;
                par = &children[0];
            },
            _ => return None,
        }
    }
}

fn is_hashbag_soup(par: &Par, spec: &NativeShiftSpec) -> bool {
    if par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.exprs.is_empty()
        || !par.matches.is_empty()
        || !par.unforgeables.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return false;
    }
    let prefix = format!("ac:{}/", spec.fingerprint());
    par.sends.iter().all(|send| {
        if send.persistent || send.data.len() != 1 {
            return false;
        }
        let Some(chan) = send.chan.as_ref() else {
            return false;
        };
        if !chan.sends.is_empty()
            || !chan.receives.is_empty()
            || !chan.news.is_empty()
            || !chan.matches.is_empty()
            || !chan.unforgeables.is_empty()
            || !chan.bundles.is_empty()
            || !chan.connectives.is_empty()
            || !chan.conditionals.is_empty()
        {
            return false;
        }
        let [expr] = chan.exprs.as_slice() else {
            return false;
        };
        let Some(ExprInstance::GString(name)) = expr.expr_instance.as_ref() else {
            return false;
        };
        name.strip_prefix(&prefix)
            .is_some_and(|op| !op.is_empty() && spec.accepts_hashbag_op(op))
    })
}

fn union_locally_free_into(acc: &mut Vec<u8>, next: &[u8]) {
    if acc.len() < next.len() {
        acc.resize(next.len(), 0);
    }
    for (left, right) in acc.iter_mut().zip(next) {
        *left |= *right;
    }
}

fn rebuild_object(head: Par, label: &str, children: Vec<Par>, fingerprint: &str) -> Par {
    let mut elements = Vec::with_capacity(children.len() + 2);
    let mut locally_free = head.locally_free.clone();
    elements.push(head);
    if is_marked_object_label(label) {
        let is_ground = match label {
            BOUND_VAR_REFLECT_LABEL => false,
            FREE_VAR_REFLECT_LABEL => true,
            _ => children
                .iter()
                .all(|child| par_carries_ground_marker(child, fingerprint)),
        };
        elements.push(ground_marker_tag_par(fingerprint, is_ground));
    }
    for child in children {
        union_locally_free_into(&mut locally_free, &child.locally_free);
        elements.push(child);
    }
    new_elist_par(elements, locally_free.clone(), false, None, locally_free, false)
}

/// Apply `amount` composed `oshift 0` operations in one stack-safe pass over a reflected value.
/// HashBag soups are traversed as their order-independent send carriers; arbitrary Rholang
/// processes and reserved terms without a `^shift` arm fail closed.
pub fn shift_reflected_par_by(
    root: &Par,
    amount: usize,
    spec: &NativeShiftSpec,
) -> Result<Par, NativeShiftError> {
    let fingerprint = spec.fingerprint();
    if amount == 0 {
        return Ok(root.clone());
    }

    enum Task<'a> {
        Visit {
            par: &'a Par,
            cutoff: usize,
        },
        AssembleObject {
            head: Par,
            label: String,
            child_count: usize,
        },
        AssembleSoup {
            original: &'a Par,
            child_count: usize,
        },
    }

    let ground_marker = ground_marker_tag_par(fingerprint, true);
    let nonground_marker = ground_marker_tag_par(fingerprint, false);
    let mut tasks = vec![Task::Visit { par: root, cutoff: 0 }];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { par, cutoff } => {
                if par == &Par::default() && spec.accepts_nil() {
                    values.push(par.clone());
                    continue;
                }
                if is_hashbag_soup(par, spec) {
                    tasks.push(Task::AssembleSoup {
                        original: par,
                        child_count: par.sends.len(),
                    });
                    tasks.extend(
                        par.sends
                            .iter()
                            .rev()
                            .map(|send| Task::Visit { par: &send.data[0], cutoff }),
                    );
                    continue;
                }
                let parts = elist_values(par).ok_or(NativeShiftError::MalformedReflectedValue)?;
                let (head, _) = parts
                    .split_first()
                    .ok_or(NativeShiftError::MalformedReflectedValue)?;
                // This is deliberately before head decoding: the old receiver's first
                // ground guard wildcards the head and returns any value carrying this
                // fingerprint's hereditary-ground marker unchanged.
                if parts.get(1) == Some(&ground_marker) {
                    values.push(par.clone());
                    continue;
                }
                let tag = reflected_tag(head).ok_or(NativeShiftError::MalformedReflectedValue)?;
                let (actual_fingerprint, label) =
                    parse_reflected_tag(&tag).ok_or(NativeShiftError::MalformedReflectedValue)?;
                if actual_fingerprint != fingerprint {
                    return Err(NativeShiftError::FingerprintMismatch);
                }
                let child_start = if is_marked_object_label(label) {
                    if parts.get(1) != Some(&nonground_marker) {
                        return Err(NativeShiftError::MalformedReflectedValue);
                    }
                    2
                } else {
                    1
                };
                let children = parts
                    .get(child_start..)
                    .ok_or(NativeShiftError::MalformedReflectedValue)?;
                match label {
                    BOUND_VAR_REFLECT_LABEL => {
                        let [index] = children else {
                            return Err(NativeShiftError::MalformedReflectedValue);
                        };
                        let index = decode_peano(index, fingerprint)
                            .ok_or(NativeShiftError::MalformedReflectedValue)?;
                        values.push(if index >= cutoff {
                            bound_var_par(
                                index
                                    .checked_add(amount)
                                    .ok_or(NativeShiftError::IndexOverflow)?,
                                fingerprint,
                            )
                        } else {
                            par.clone()
                        });
                    },
                    LAMBDA_REFLECT_LABEL => {
                        let [body] = children else {
                            return Err(NativeShiftError::MalformedReflectedValue);
                        };
                        tasks.push(Task::AssembleObject {
                            head: head.clone(),
                            label: label.to_owned(),
                            child_count: 1,
                        });
                        tasks.push(Task::Visit {
                            par: body,
                            cutoff: cutoff
                                .checked_add(1)
                                .ok_or(NativeShiftError::IndexOverflow)?,
                        });
                    },
                    FREE_VAR_REFLECT_LABEL => {
                        let [child] = children else {
                            return Err(NativeShiftError::MalformedReflectedValue);
                        };
                        values.push(rebuild_object(
                            head.clone(),
                            label,
                            vec![child.clone()],
                            fingerprint,
                        ));
                    },
                    _ if spec.object_arity(label) == Some(children.len()) => {
                        tasks.push(Task::AssembleObject {
                            head: head.clone(),
                            label: label.to_owned(),
                            child_count: children.len(),
                        });
                        tasks.extend(children.iter().rev().map(|par| Task::Visit { par, cutoff }));
                    },
                    _ => return Err(NativeShiftError::UnsupportedReflectedTerm),
                }
            },
            Task::AssembleObject { head, label, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .ok_or(NativeShiftError::MalformedReflectedValue)?;
                let children = values.split_off(first);
                values.push(rebuild_object(head, &label, children, fingerprint));
            },
            Task::AssembleSoup { original, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .ok_or(NativeShiftError::MalformedReflectedValue)?;
                let shifted = values.split_off(first);
                let sends = original
                    .sends
                    .iter()
                    .zip(shifted)
                    .map(|(send, value)| Send {
                        chan: send.chan.clone(),
                        data: vec![value],
                        persistent: false,
                        locally_free: Vec::new(),
                        connective_used: false,
                    })
                    .collect();
                values.push(Par::default().with_sends(sends));
            },
        }
    }
    match values.as_mut_slice() {
        [value] => Ok(std::mem::take(value)),
        _ => Err(NativeShiftError::MalformedReflectedValue),
    }
}

thread_local! {
    static PENDING_NATIVE_SHIFT_SPECS: RefCell<Vec<NativeShiftSpec>> = const { RefCell::new(Vec::new()) };
}

pub fn record_pending_native_shift_spec(spec: NativeShiftSpec) {
    PENDING_NATIVE_SHIFT_SPECS.with(|cell| {
        let mut specs = cell.borrow_mut();
        if let Some(existing) = specs
            .iter()
            .find(|existing| existing.fingerprint == spec.fingerprint)
        {
            assert_eq!(
                existing, &spec,
                "one language fingerprint cannot register two native shift domains"
            );
        } else {
            specs.push(spec);
        }
    });
}

pub fn take_pending_native_shift_specs() -> Vec<NativeShiftSpec> {
    PENDING_NATIVE_SHIFT_SPECS.with(|cell| std::mem::take(&mut *cell.borrow_mut()))
}

pub fn clear_pending_native_shift_specs() {
    PENDING_NATIVE_SHIFT_SPECS.with(|cell| cell.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rho_net_lower::{reflect_ground_term_par, GroundTerm, FREE_VAR_REFLECT_LABEL};

    #[test]
    fn amount_abi_is_fixed_width_and_round_trips() {
        for amount in [0usize, 1, 255, 20_000, usize::MAX] {
            let par = native_shift_amount_par(amount);
            assert_eq!(decode_native_shift_amount(&par), Ok(amount));
            let Some(ExprInstance::GByteArray(bytes)) = par.exprs[0].expr_instance.as_ref() else {
                unreachable!();
            };
            assert_eq!(bytes.len(), AMOUNT_BYTES);
        }
    }

    #[test]
    fn pending_registry_deduplicates_one_contract_per_fingerprint() {
        clear_pending_native_shift_specs();
        record_pending_native_shift_spec(NativeShiftSpec::new("fp-a", [], []));
        record_pending_native_shift_spec(NativeShiftSpec::new("fp-a", [], []));
        record_pending_native_shift_spec(NativeShiftSpec::new("fp-b", [], []));
        assert_eq!(take_pending_native_shift_specs().len(), 2);
        assert!(take_pending_native_shift_specs().is_empty());
    }

    #[test]
    fn ground_terms_are_verbatim_and_foreign_terms_fail_closed() {
        let ground = reflect_ground_term_par(
            &GroundTerm::new(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary("x")]),
            "fp-a",
        );
        let fp_a = NativeShiftSpec::new("fp-a", [], []);
        let fp_b = NativeShiftSpec::new("fp-b", [], []);
        assert_eq!(shift_reflected_par_by(&ground, 20_000, &fp_a), Ok(ground.clone()));
        assert_eq!(
            shift_reflected_par_by(&ground, 1, &fp_b),
            Err(NativeShiftError::FingerprintMismatch)
        );
    }
}
