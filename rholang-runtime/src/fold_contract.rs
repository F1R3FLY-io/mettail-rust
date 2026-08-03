//! Tier-3 fold trampoline: the fold contracts that let a Rholang native width/precision fold
//! reduce on the metered Rho machine.
//!
//! Pre-A-S4 this band served only HELD folds — e.g. `int(*(x), 8)` where `x` is bound by
//! `(@("c")?x)`: Dovetail cannot reduce it (the operand is free until the rendezvous fires), and
//! it has no Rholang primitive. A-S4 (lowering purity) routes EVERY fold site through the same
//! trampoline, ground operands included: the host no longer pre-computes `int(5,8) → 5` at
//! lowering time (the deleted Tier-1 in-place fold); instead the lowering lifts the fold to a
//! contract call `@"<fold>"!(operand, *ret)` whose [`Definition`] runs the *exact* native fold
//! (`proc_int_bin` — the rule's own `![{…}]` body) on the machine-delivered ground operand and
//! produces the result on `ret`, so the fold reduces on the Rho machine as a first-class,
//! cost-accounted COMM. Width folds have no Rholang operator (wrap/saturate width semantics are
//! MeTTaIL's), which is exactly why they ride a system process rather than a native `Expr`. The
//! whole `Definition` (handler included) is built here, MeTTaIL-side, and injected into f1r3node
//! as data via the existing `extra_system_processes` seam — f1r3node gains no MeTTaIL dependency
//! (the one-way bridge holds).
//!
//! A-S4 also extends the band with the unary precision casts `bigint(a)` / `bigrat(a)`
//! ([`FoldKind::BigIntCast`] / [`FoldKind::BigRatCast`], `proc_bigint_unary` /
//! `proc_bigrat_unary`): f1r3node's `Expr` algebra has no int→bigint / →bigrat conversion
//! operator, so they are width-cast-band system processes too (arity 2, width parameter unused).
//!
//! See `docs/architecture/rho-native-integration/10-adaptive-evaluation-model.md` (Tier 3) and the
//! zero-admission proof `formal/rocq/rho_bridge/theories/HeldFoldContractSound.v` (the trampoline
//! transition system is agnostic to WHY the operand is ground at fire time — a binding COMM or a
//! statically ground/send-evaluated operand instantiate the same `tramp_init`).

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use mettail_languages::rholang::{BigInt, BigRat, Bool, Fixed, Float, Int, Proc, Str};
// A-S3: the reserved MeTTaIL system-process bands are enumerated in ONE place —
// `mettail_rholang_codegen::native_handler` (held-fold `[0xF0, site]` / `0xF000+site` and
// native-handler `[0xF1, rule]` / `0xF100+rule`, with the collision unit test) — so this module
// IMPORTS its band rather than redeclaring it. The held-fold channel id is two-byte, so it
// cannot collide with f1r3node's std (0–36) or test-framework (101–108) single-byte names.
use mettail_rholang_codegen::{
    check_body_refs_pairwise_distinct, BandAllocationError, HELD_FOLD_BAND,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{ListParWithRandom, Par};
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

use crate::rholang_ast::{lower_rholang_proc, RholangAstLowerError};

/// Which width/precision native cast a fold site runs. Captured *statically* at lift time (the
/// rule + the ground width literal), so the contract handler is a pure function of the runtime
/// operand. `BigIntCast`/`BigRatCast` (A-S4) are the UNARY precision casts `bigint(a)` /
/// `bigrat(a)` — same arity-2 `[operand, ack]` contract shape; their `width` spec field is unused
/// (recorded as 0).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldKind {
    Int,
    UInt,
    Float,
    Fixed,
    BigIntCast,
    BigRatCast,
}

impl FoldKind {
    /// The fold-channel URN tag (also the human label in the step trace).
    pub fn tag(self) -> &'static str {
        match self {
            FoldKind::Int => "int",
            FoldKind::UInt => "uint",
            FoldKind::Float => "float",
            FoldKind::Fixed => "fixed",
            FoldKind::BigIntCast => "bigint",
            FoldKind::BigRatCast => "bigrat",
        }
    }
}

/// Convert a *ground value-leaf* operand `Par` (as it arrives at the contract — either a
/// statically ground operand the send evaluated, or a COMM-substituted received value) into the
/// corresponding Rholang value `Proc`, so the native fold can run on it. `None` if the operand is
/// not a single ground value leaf — the fold is then genuinely undefined on a non-value, and the
/// handler reports a clear error rather than silently mis-reducing (the documented Tier-3
/// boundary).
///
/// A-S4: covers ALL the machine ground numerics the Rholang value lowering emits —
/// `GInt`/`GBool`/`GString` plus `GDouble`/`GBigInt`/`GBigRat`/`GFixedPoint` (the send-time
/// evaluation of a `float`/`fixed`/`bigint`/`bigrat` operand delivers those shapes). Each decode
/// arm is the exact inverse of the corresponding literal lowering arm in
/// `rholang_ast::lower_proc` (`new_gdouble_expr`/`new_gbigint_expr`/`new_gbigrat_expr`/
/// `new_gfixedpoint_expr` over signed big-endian two's-complement bytes).
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
            ExprInstance::GDouble(bits) => Some(Proc::CastFloat(Arc::new(Float::FloatLit(
                mettail_runtime::CanonicalFloat64::from(f64::from_bits(*bits)),
            )))),
            ExprInstance::GBigInt(bytes) => Some(Proc::CastBigInt(Arc::new(BigInt::NumLit(
                mettail_runtime::CanonicalBigInt::new(num_bigint::BigInt::from_signed_bytes_be(
                    bytes,
                )),
            )))),
            ExprInstance::GBigRat(rational) => {
                let numerator = num_bigint::BigInt::from_signed_bytes_be(&rational.numerator);
                let denominator = num_bigint::BigInt::from_signed_bytes_be(&rational.denominator);
                mettail_runtime::CanonicalBigRat::try_from_nd(numerator, denominator)
                    .map(|value| Proc::CastBigRat(Arc::new(BigRat::RatLit(value))))
            },
            ExprInstance::GFixedPoint(fixed_point) => Some(Proc::CastFixed(Arc::new(
                Fixed::FixedLit(mettail_runtime::CanonicalFixedPoint::new(
                    num_bigint::BigInt::from_signed_bytes_be(&fixed_point.unscaled),
                    fixed_point.scale,
                )),
            ))),
            _ => None,
        },
        _ => None,
    }
}

/// Run a fold on a ground operand `Par` and return the result `Par` — the contract's core.
///
/// This calls the *identical* native-fold body the rule `![{…}]` runs (`proc_int_bin` etc.), so it
/// is the fold oracle, not an approximation: `int(5, 8) → 5`. The result `Proc` is then lowered back
/// to a closed value-leaf `Par` via the existing [`lower_rholang_proc`]. The unary precision casts
/// ([`FoldKind::BigIntCast`]/[`FoldKind::BigRatCast`]) ignore `width` (spec-recorded as 0).
pub fn fold_eval(operand: &Par, kind: FoldKind, width: i64) -> Result<Par, FoldEvalError> {
    let operand_proc = par_ground_to_proc(operand).ok_or(FoldEvalError::OperandNotGround)?;
    let result_proc: Proc = match kind {
        FoldKind::Int => mettail_runtime::proc_int_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::UInt => mettail_runtime::proc_uint_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::Float => mettail_runtime::proc_float_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::Fixed => mettail_runtime::proc_fixed_bin::<Proc, i64>(&operand_proc, width),
        FoldKind::BigIntCast => mettail_runtime::proc_bigint_unary::<Proc>(&operand_proc),
        FoldKind::BigRatCast => mettail_runtime::proc_bigrat_unary::<Proc>(&operand_proc),
    };
    lower_rholang_proc(&result_proc).map_err(FoldEvalError::Lower)
}

/// The static spec of one fold site (held or ground): the fold kind + ground width + a per-term
/// site index (0-based) that deterministically keys the contract channel + `body_ref`. Stable for
/// a given term, so replay installs the identical contract on the identical channel. The unary
/// precision casts record width 0 (unused).
#[derive(Clone, Debug)]
pub struct FoldSpec {
    pub kind: FoldKind,
    pub width: i64,
    pub site_index: u8,
    /// ★ #36 S5 — the language fingerprint the site belongs to.
    ///
    /// `FoldSpec` carried NO fingerprint at all, so `site_index` alone keyed both the channel
    /// and the `body_ref`: two co-installed fold-bearing languages each allocate site 0 and
    /// collide on `[0xF0, 0]` / `0xF000`, and f1r3node's `dispatch_table_creator` `HashMap`
    /// silently keeps whichever installed last. Identical defect to the native band, which is
    /// why both now derive from the one allocator (`mettail_rholang_codegen::HELD_FOLD_BAND`).
    pub fingerprint: String,
}

impl FoldSpec {
    /// The unforgeable contract channel (the lowered send targets it; the `Definition` installs
    /// on it). ★ CONSENSUS-VISIBLE — it is a send target in the emitted `Par`.
    pub fn channel(&self) -> Par {
        fold_channel(self.site_index, &self.fingerprint)
    }

    /// The reserved `body_ref` for this site — a DETERMINISTIC function of
    /// `(fingerprint, site_index)`, never an allocation counter. ★ Not state-root visible, but
    /// replay-relevant.
    pub fn body_ref(&self) -> i64 {
        HELD_FOLD_BAND.body_ref(self.site_index, &self.fingerprint)
    }
}

/// The unforgeable held-fold contract channel for a `(site_index, fingerprint)` pair —
/// `GPrivate{id: [0xF0, site] ++ fingerprint.as_bytes()}`, collision-free by construction.
pub fn fold_channel(site_index: u8, language_fingerprint: &str) -> Par {
    HELD_FOLD_BAND.channel(site_index, language_fingerprint)
}

/// Build the system-process [`Definition`] for one fold site (held or ground — A-S4): a
/// synchronous, deterministic, value-returning contract on the fold channel (arity 2 =
/// `[operand, ack]`) whose handler runs the native fold ([`fold_eval`]) on the received ground
/// operand and `produce`s the result on `ack` — driving the lifted `for(@r <- ret){…}`. Built
/// MeTTaIL-side, injected as data.
pub fn fold_definition(spec: &FoldSpec) -> Definition {
    // `kind` and `width` are copied out so the `move` handler captures the `Copy` values
    // instead of borrowing `spec`. `site_index` needed no such copy and was bound without
    // ever being read (`unused_variables` caught it): the only two things that consume it —
    // `spec.channel()` and `spec.body_ref()` — are evaluated EAGERLY in the struct literal
    // below, outside the closure, so the handler never asks which site it serves.
    let kind = spec.kind;
    let width = spec.width;
    Definition {
        urn: fold_urn(spec),
        fixed_channel: spec.channel(),
        arity: 2,
        body_ref: spec.body_ref(),
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
pub fn fold_definitions_for(specs: &[FoldSpec]) -> Result<Vec<Definition>, BandAllocationError> {
    // ★ #36 S5: a `body_ref` must fit ONE `i64` while `(fingerprint, site_index)` is unbounded,
    // so the derivation cannot be collision-free. Checking here converts the residual 48-bit
    // digest collision from a SILENT wrong dispatch (f1r3node keys its dispatch table by
    // `body_ref` in a `HashMap`, so one handler would just shadow the other) into a loud,
    // typed refusal. Within one language a collision is impossible by construction — the site
    // index has its own bit field — so this can only fire across co-installed languages.
    let urns: Vec<String> = specs.iter().map(fold_urn).collect();
    check_body_refs_pairwise_distinct(
        &HELD_FOLD_BAND,
        urns.iter()
            .map(String::as_str)
            .zip(specs.iter().map(FoldSpec::body_ref)),
    )?;
    Ok(specs.iter().map(fold_definition).collect())
}

/// The `Definition` URN of one fold site: `mtl:fold:{kind}:{width}#{site}@{fingerprint}`.
///
/// The fingerprint suffix is #36 S5. The URN is not what f1r3node dispatches on — it keys on
/// `body_ref` — but it IS the identity a band-allocation refusal names, so it must distinguish
/// the two specs a collision is between.
fn fold_urn(spec: &FoldSpec) -> String {
    format!(
        "mtl:fold:{}:{}#{}@{}",
        spec.kind.tag(),
        spec.width,
        spec.site_index,
        spec.fingerprint
    )
}

/// Why a fold contract could not produce a result. Both are honest, non-silent failures.
#[derive(Debug)]
pub enum FoldEvalError {
    /// The operand arrived as a non-value (not a single ground
    /// `GInt`/`GBool`/`GString`/`GDouble`/`GBigInt`/`GBigRat`/`GFixedPoint` leaf).
    OperandNotGround,
    /// The fold's result `Proc` failed to lower back to a `Par`.
    Lower(RholangAstLowerError),
}

impl std::fmt::Display for FoldEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FoldEvalError::OperandNotGround => write!(
                f,
                "fold contract: operand is not a ground value leaf \
                 (GInt/GBool/GString/GDouble/GBigInt/GBigRat/GFixedPoint)"
            ),
            FoldEvalError::Lower(err) => {
                write!(f, "fold contract: result failed to lower: {err:?}")
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::Expr;

    fn gint_par(value: i64) -> Par {
        let mut par = Par::default();
        par.exprs = vec![Expr {
            expr_instance: Some(ExprInstance::GInt(value)),
        }];
        par
    }

    #[test]
    fn ground_int_operand_converts_to_proc() {
        let proc = par_ground_to_proc(&gint_par(5)).expect("GInt is a ground value leaf");
        assert!(matches!(proc, Proc::CastInt(_)), "GInt → CastInt(NumLit)");
    }

    #[test]
    fn non_ground_operand_is_rejected() {
        // A send is not a value leaf.
        let mut send_par = Par::default();
        send_par.sends = vec![models::rhoapi::Send::default()];
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
