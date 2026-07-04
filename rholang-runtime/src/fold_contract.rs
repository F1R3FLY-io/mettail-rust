//! Tier-3 held-fold trampoline: the Dovetail-backed fold contracts that let a RhoCalc native fold
//! whose operand is bound by a COMM `receive` reduce on the metered Rho machine.
//!
//! A "held fold" is e.g. `int(*(x), 8)` where `x` is bound by `(@("c")?x)`: Dovetail cannot reduce
//! it (the operand is free until the rendezvous fires), and it has no Rholang primitive — so today
//! it is stuck. The trampoline lifts it to a contract call `@"<fold>"!(operand, *ret)` whose
//! Dovetail-backed [`Definition`] runs the *exact* native fold (`proc_int_bin` — the rule's own
//! `![{…}]` body) on the now-ground operand and produces the result on `ret`, so the term reduces
//! on the Rho machine as a first-class, cost-accounted COMM. The whole `Definition` (handler
//! included) is built here, MeTTaIL-side, and injected into f1r3node as data via the existing
//! `extra_system_processes` seam — f1r3node gains no MeTTaIL dependency (the one-way bridge holds).
//!
//! See `docs/architecture/rho-native-integration/10-adaptive-evaluation-model.md` (Tier 3) and the
//! zero-admission proof `formal/rocq/rho_bridge/theories/HeldFoldContractSound.v`.

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use mettail_languages::rhocalc::{Bool, Int, Proc, Str};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance::GPrivateBody;
use models::rhoapi::{GPrivate, GUnforgeable, ListParWithRandom, Par};
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

use crate::rhocalc_ast::{lower_rhocalc_proc, RhocalcAstLowerError};

/// First byte of every held-fold contract's unforgeable channel id `[0xF0, site]` — a reserved
/// MeTTaIL band that cannot collide with f1r3node's std (0–36) or test-framework (101–108) byte
/// names (those are single-byte `GPrivate{id:[b]}`; ours are two-byte).
const MTL_FOLD_CHANNEL_TAG: u8 = 0xF0;
/// Reserved `body_ref` band for held-fold contracts (well clear of std 0–36 / test 101–108, and
/// NOT in `non_deterministic_ops()` — the folds are pure, so dispatch is a `DeterministicCall` and
/// replay reproduces bit-identically).
const MTL_FOLD_BODY_REF_BASE: i64 = 0xF000;

/// Which width/cast native fold a held-fold site runs. Captured *statically* at lift time (the rule
/// + the ground width literal), so the contract handler is a pure function of the runtime operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldKind {
    Int,
    UInt,
    Float,
    Fixed,
}

impl FoldKind {
    /// The fold-channel URN tag (also the human label in the step trace).
    pub fn tag(self) -> &'static str {
        match self {
            FoldKind::Int => "int",
            FoldKind::UInt => "uint",
            FoldKind::Float => "float",
            FoldKind::Fixed => "fixed",
        }
    }
}

/// Convert a *ground value-leaf* operand `Par` (as it arrives after the binding COMM substitutes the
/// received value) into the corresponding RhoCalc value `Proc`, so the native fold can run on it.
/// `None` if the operand is not a single ground value leaf (`GInt`/`GBool`/`GString`) — the fold is
/// then genuinely undefined on a non-value, and the handler reports a clear error rather than
/// silently mis-reducing (the documented Tier-3 boundary).
pub fn par_ground_to_proc(par: &Par) -> Option<Proc> {
    // A value leaf is a Par carrying exactly one ground `Expr` (no sends/receives/news/…).
    let is_bare = par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.unforgeables.is_empty()
        && par.connectives.is_empty();
    if !is_bare {
        return None;
    }
    match par.exprs.as_slice() {
        [expr] => match expr.expr_instance.as_ref()? {
            ExprInstance::GInt(value) => Some(Proc::CastInt(Arc::new(Int::NumLit(*value)))),
            ExprInstance::GBool(value) => Some(Proc::CastBool(Arc::new(Bool::BoolLit(*value)))),
            ExprInstance::GString(value) => {
                Some(Proc::CastStr(Arc::new(Str::StringLit(value.clone()))))
            },
            _ => None,
        },
        _ => None,
    }
}

/// Run a held fold on a ground operand `Par` and return the result `Par` — the contract's core.
///
/// This calls the *identical* native-fold body the rule `![{…}]` runs (`proc_int_bin` etc.), so it
/// is the fold oracle, not an approximation: `int(5, 8) → 5`. The result `Proc` is then lowered back
/// to a closed value-leaf `Par` via the existing [`lower_rhocalc_proc`].
pub fn fold_eval(operand: &Par, kind: FoldKind, width: i64) -> Result<Par, FoldEvalError> {
    let operand_proc = par_ground_to_proc(operand).ok_or(FoldEvalError::OperandNotGround)?;
    let result_proc: Proc = match kind {
        FoldKind::Int => mettail_runtime::proc_int_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::UInt => mettail_runtime::proc_uint_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::Float => mettail_runtime::proc_float_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::Fixed => mettail_runtime::proc_fixed_bin::<Proc, i64>(&operand_proc, width),
    };
    lower_rhocalc_proc(&result_proc).map_err(FoldEvalError::Lower)
}

/// The static spec of one held-fold site: the fold kind + ground width + a per-term site index
/// (0-based) that deterministically keys the contract channel + `body_ref`. Stable for a given term,
/// so replay installs the identical contract on the identical channel.
#[derive(Clone, Debug)]
pub struct FoldSpec {
    pub kind: FoldKind,
    pub width: i64,
    pub site_index: u8,
}

impl FoldSpec {
    /// The unforgeable contract channel `@[0xF0, site]` (the lowered send targets it; the
    /// `Definition` installs on it).
    pub fn channel(&self) -> Par {
        fold_channel(self.site_index)
    }
}

/// The unforgeable held-fold contract channel for a site index (two-byte private name `[0xF0, n]`).
pub fn fold_channel(site_index: u8) -> Par {
    Par::default().with_unforgeables(vec![GUnforgeable {
        unf_instance: Some(GPrivateBody(GPrivate {
            id: vec![MTL_FOLD_CHANNEL_TAG, site_index],
        })),
    }])
}

/// Build the Dovetail-backed system-process [`Definition`] for one held-fold site: a synchronous,
/// deterministic, value-returning contract on the fold channel (arity 2 = `[operand, ack]`) whose
/// handler runs the native fold ([`fold_eval`]) on the received ground operand and `produce`s the
/// result on `ack` — driving the lifted `for(@r <- ret){…}`. Built MeTTaIL-side, injected as data.
pub fn fold_definition(spec: &FoldSpec) -> Definition {
    let kind = spec.kind;
    let width = spec.width;
    let site_index = spec.site_index;
    Definition {
        urn: format!("mtl:fold:{}:{}#{}", kind.tag(), width, site_index),
        fixed_channel: fold_channel(site_index),
        arity: 2,
        body_ref: MTL_FOLD_BODY_REF_BASE + site_index as i64,
        remainder: None,
        handler: Box::new(move |ctx| {
            let space = ctx.space.clone();
            let dispatcher = ctx.dispatcher.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let cc = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = cc.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(
                            "mtl:fold contract: not a single-message contract call".to_string(),
                        ));
                    };
                    let [operand, ack] = payload.as_slice() else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "mtl:fold contract: expected [operand, ack], got arity {}",
                            payload.len()
                        )));
                    };
                    let result = fold_eval(operand, kind, width)
                        .map_err(|err| InterpreterError::IllegalArgumentError(err.to_string()))?;
                    let output = vec![result];
                    produce(&output, ack).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

/// Materialize the contract `Definition`s for a term's held-fold sites (one per site).
pub fn fold_definitions_for(specs: &[FoldSpec]) -> Vec<Definition> {
    specs.iter().map(fold_definition).collect()
}

/// Why a held-fold contract could not produce a result. Both are honest, non-silent failures.
#[derive(Debug)]
pub enum FoldEvalError {
    /// The COMM bound the operand to a non-value (not a single ground `GInt`/`GBool`/`GString`).
    OperandNotGround,
    /// The fold's result `Proc` failed to lower back to a `Par`.
    Lower(RhocalcAstLowerError),
}

impl std::fmt::Display for FoldEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FoldEvalError::OperandNotGround => write!(
                f,
                "held-fold contract: operand is not a ground value leaf (GInt/GBool/GString)"
            ),
            FoldEvalError::Lower(err) => {
                write!(f, "held-fold contract: result failed to lower: {err:?}")
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::Expr;

    fn gint_par(value: i64) -> Par {
        Par {
            exprs: vec![Expr {
                expr_instance: Some(ExprInstance::GInt(value)),
            }],
            ..Default::default()
        }
    }

    #[test]
    fn ground_int_operand_converts_to_proc() {
        let proc = par_ground_to_proc(&gint_par(5)).expect("GInt is a ground value leaf");
        assert!(matches!(proc, Proc::CastInt(_)), "GInt → CastInt(NumLit)");
    }

    #[test]
    fn non_ground_operand_is_rejected() {
        // A send is not a value leaf.
        let send_par = Par {
            sends: vec![models::rhoapi::Send::default()],
            ..Default::default()
        };
        assert!(par_ground_to_proc(&send_par).is_none(), "a process is not a value leaf");
    }

    #[test]
    fn int_fold_runs_the_native_rule_on_a_ground_operand() {
        // int(5, 8) = 5 — the exact `proc_int_bin` reduction, lowered back to GInt(5).
        let result = fold_eval(&gint_par(5), FoldKind::Int, 8).expect("int(5,8) folds");
        match result.exprs.as_slice() {
            [expr] => assert_eq!(expr.expr_instance, Some(ExprInstance::GInt(5)), "int(5,8) → 5"),
            other => panic!("expected a single GInt result, got {other:?}"),
        }
    }
}
