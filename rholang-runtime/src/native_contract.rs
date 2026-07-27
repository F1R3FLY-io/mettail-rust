//! A-S3 (native dispatch boundary tightening): the registered NATIVE-HANDLER system-process
//! `Definition`s — the generalization of the Tier-3 held-fold trampoline ([`crate::fold_contract`])
//! to every registrable `fold` native rule (`NativeSystemProcessRewrite` / `NativeFold`).
//!
//! Before A-S3, an admitted rho-net exec of a native rule (BigInt/pow-class compute) forwarded a
//! HOST-computed value: the D-stage evaluated the rule's `![…] fold` body and the value bridge
//! baked the reflected contractum into the call `Par` — the machine only ferried it. A-S3 makes
//! the native contractum DIRECTED COMPUTE the MACHINE dispatches: the generated report-free match
//! body (`rho_net_match_invocation_to`) records one
//! [`NativeHandlerSpec`](mettail_rholang_codegen::NativeHandlerSpec) per located native rule,
//! [`native_definition`] turns each spec into a system-process `Definition` on the reserved
//! channel `[0xF1, rule_index]` (the band enumerated ONCE in
//! `mettail_rholang_codegen::native_handler`, next to the held-fold band, with the collision
//! test), and the invocation-compiler bracket (`backend.rs::drain_pending_fold_definitions`)
//! injects it through the SAME `extra_system_processes` seam the held-fold trampoline uses —
//! the f1r3node registry precedent, one-way data, no back-edge (`BridgeInertness.v`).
//!
//! At COMM time the co-installed contract-call bridge
//! ([`native_locate_contract_bridge_par`](mettail_rholang_codegen::native_locate_contract_bridge_par))
//! sends the automaton's located σ operands `[⟦a₀⟧, …, ⟦a_{k-1}⟧, out]` on the contract channel;
//! the handler DECODES each reflected operand back to a ground term ([`par_to_ground_term`],
//! fingerprint-checked), runs the spec's trusted evaluator (the rule's own `fold` body, compiled
//! by the `language!` macro), and — mirroring the D-stage fold-gate semantics exactly:
//!
//! * `Some(value)` → `produce([⟦value⟧, out])` on the rule's DISPATCH channel, where the
//!   installed σ-receiver `for (result, out <- c) { out!(result) }` consumes the RETURNED value
//!   and emits it on `@out` — the rule fires as machine COMMs end-to-end;
//! * `None` → NO produce (the fold DEFERS: a non-value operand or a safe-arithmetic decline
//!   leaves the redex unreduced, exactly as the D-stage dispatcher's `try_eval()?` /
//!   `__class_is_fold_value` gate reports no firing) — an honest no-fire, never a fabricated
//!   value;
//! * a malformed payload (wrong arity, a non-reflected operand, a fingerprint mismatch) →
//!   [`InterpreterError`] — ABI drift fails loudly, never silently mis-reduces.
//!
//! The evaluator is a pure function of the received σ operands, so dispatch is a
//! `DeterministicCall` (the `body_ref` band `0xF100+rule` is NOT in `non_deterministic_ops()`)
//! and replay reproduces bit-identically.
//!
//! FV: `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v` section 4 (the A-S3
//! dispatch trampoline: the emitted value is EXACTLY the registered handler's output on the
//! machine-captured σ, produced at COMM time — reusing `HeldFoldContractSound.v`'s structure).

use std::future::Future;
use std::pin::Pin;

use mettail_rholang_codegen::{
    check_body_refs_pairwise_distinct, native_contract_body_ref, native_contract_channel,
    reflect_ground_term_par, BandAllocationError, GroundTerm, NativeHandlerSpec,
    NATIVE_HANDLER_BAND,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::Par;
use models::rust::utils::new_gstring_par;
use prost::Message;
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

/// Recover the UTF-8 tag string of a private-name `Par` built by
/// `GPrivateBuilder::new_par_from_string(s)` (the reflected-term head): the builder encodes the
/// string with `<String as prost::Message>`, so `String::decode` is its exact inverse. `None`
/// for any `Par` that is not exactly one `GPrivate` unforgeable (mirrors `run.rs`'s
/// `private_name_tag`, kept local so this module has no dependency on the observation decoder).
///
/// `pub(crate)` because the `[*]` request server ([`crate::speculation::server`]) has to answer
/// the same question this module's decoder asks — *"is this `Par` a reflected constructor term,
/// and of WHICH language?"* — and a second hand-rolled tag reader is exactly the ABI drift
/// `parse_reflected_tag` was consolidated to remove.
pub(crate) fn private_name_tag(par: &Par) -> Option<String> {
    if !par.exprs.is_empty()
        || !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
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

/// Decode a REFLECTED ground-term `Par` (the constructor-reflection ABI
/// `EList[GPrivate("mettail.term.{fingerprint}.{label}"), children…]` — byte-identical to
/// [`reflect_ground_term_par`], and to the spread's collapse values the accept σ slots carry)
/// back to its [`GroundTerm`], checking every node's fingerprint against `expected_fingerprint`.
///
/// The tag layout is `{prefix}{fingerprint}.{label}`: the fingerprint contains no `.`, so the
/// FIRST `.` after the prefix separates it from the label — which may itself contain dots (a
/// literal leaf like `NumLit(8.5)` bakes the value into the label).
///
/// ★ S1: this reader was CORRECT and the other four in the tree were not, but it was still a
/// hand-rolled split. It now calls the single shared inverse
/// [`mettail_rholang_codegen::parse_reflected_tag`], so the ABI has exactly one writer and one
/// reader and the two can no longer drift apart. The invariant that licenses the first-`.` split
/// is asserted at the writer, not restated here.
///
/// Fails typed on anything that is not a positionally reflected term of THIS definition: the
/// handler must never guess at a drifted or foreign operand.
pub fn par_to_ground_term(
    par: &Par,
    expected_fingerprint: &str,
) -> Result<GroundTerm, NativeContractError> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.unforgeables.is_empty()
    {
        return Err(NativeContractError::OperandNotReflectedTerm);
    }
    let [expr] = par.exprs.as_slice() else {
        return Err(NativeContractError::OperandNotReflectedTerm);
    };
    let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() else {
        return Err(NativeContractError::OperandNotReflectedTerm);
    };
    if list.remainder.is_some() || list.connective_used {
        return Err(NativeContractError::OperandNotReflectedTerm);
    }
    let Some((head, children)) = list.ps.split_first() else {
        return Err(NativeContractError::OperandNotReflectedTerm);
    };
    let tag = private_name_tag(head).ok_or(NativeContractError::OperandNotReflectedTerm)?;
    let (fingerprint, label) = mettail_rholang_codegen::parse_reflected_tag(&tag)
        .ok_or(NativeContractError::OperandNotReflectedTerm)?;
    if fingerprint != expected_fingerprint {
        return Err(NativeContractError::FingerprintMismatch {
            expected: expected_fingerprint.to_string(),
            actual: fingerprint.to_string(),
        });
    }
    // E-2-D (reflected-ABI v2): a marked-object node carries the `^gnd`/`^nog` hereditary-ground
    // marker at index 1 — skip it so `par_to_ground_term ∘ reflect_ground_term_par` stays the
    // identity on positional ground terms (the marker is codegen metadata, not a σ operand).
    let children = match children.first() {
        Some(first) if mettail_rholang_codegen::is_ground_marker_par(first, fingerprint) => {
            &children[1..]
        },
        _ => children,
    };
    let children = children
        .iter()
        .map(|child| par_to_ground_term(child, expected_fingerprint))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(GroundTerm::new(label, children))
}

/// Build the system-process [`Definition`] for one registrable native rule: a deterministic,
/// value-returning contract on the reserved channel `[0xF1, rule_index]` (arity `k + 1` =
/// `[σ₀, …, σ_{k-1}, out]`) whose handler decodes the located σ operands, runs the spec's
/// trusted evaluator (the rule's own `fold` body) AT COMM TIME, and `produce`s
/// `[⟦value⟧, out]` on the rule's dispatch channel — driving the installed σ-receiver
/// `for (result, out <- c) { out!(result) }`. Built MeTTaIL-side, injected as data via
/// `extra_system_processes` (the held-fold seam). An evaluator deferral (`None`) produces
/// nothing: the rule does not fire, mirroring the D-stage fold gate.
pub fn native_definition(spec: &NativeHandlerSpec) -> Definition {
    let arity = spec.arity;
    let fingerprint = spec.fingerprint.clone();
    let dispatch_channel = spec.dispatch_channel.clone();
    let evaluator = spec.evaluator.clone();
    let urn = spec.urn.clone();
    Definition {
        urn: spec.urn.clone(),
        fixed_channel: native_contract_channel(spec.rule_index, &spec.fingerprint),
        arity: (arity + 1) as i32,
        body_ref: native_contract_body_ref(spec.rule_index, &spec.fingerprint),
        remainder: None,
        handler: Box::new(move |ctx| {
            let space = ctx.space.clone();
            let dispatcher = ctx.dispatcher.clone();
            let fingerprint = fingerprint.clone();
            let dispatch_channel = dispatch_channel.clone();
            let evaluator = evaluator.clone();
            let urn = urn.clone();
            Box::new(move |args: (Vec<models::rhoapi::ListParWithRandom>, bool, Vec<Par>)| {
                let cc = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let fingerprint = fingerprint.clone();
                let dispatch_channel = dispatch_channel.clone();
                let evaluator = evaluator.clone();
                let urn = urn.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = cc.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{urn}: not a single-message contract call"
                        )));
                    };
                    if payload.len() != arity + 1 {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{urn}: expected [σ₀..σ_{}, out] (arity {}), got arity {}",
                            arity.saturating_sub(1),
                            arity + 1,
                            payload.len()
                        )));
                    }
                    let (operands, out_slice) = payload.split_at(arity);
                    let [out] = out_slice else {
                        // Unreachable after the length check; keep the honest error anyway.
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{urn}: missing out channel argument"
                        )));
                    };
                    // Decode the machine-captured σ operands (the automaton's located captures,
                    // reflected under THIS definition's fingerprint). A drifted operand is an
                    // ABI violation and fails loudly.
                    let mut grounds = Vec::with_capacity(arity);
                    for operand in operands {
                        grounds.push(par_to_ground_term(operand, &fingerprint).map_err(|err| {
                            InterpreterError::IllegalArgumentError(format!(
                                "{urn}: located σ operand did not decode: {err}"
                            ))
                        })?);
                    }
                    // THE A-S3 BOUNDARY: the trusted evaluator (the rule's own `fold` body) runs
                    // HERE, dispatched by the machine's COMM on the located σ — no host
                    // pre-computation rides the call. `None` = the fold DEFERS (no firing, no
                    // produce), exactly the D-stage fold-gate semantics.
                    match evaluator(&grounds) {
                        Some(value) => {
                            let value_par = reflect_ground_term_par(&value, &fingerprint);
                            let output = vec![value_par, out.clone()];
                            let dispatch_par =
                                new_gstring_par(dispatch_channel.clone(), Vec::new(), false);
                            produce(&output, &dispatch_par).await?;
                            Ok(output)
                        },
                        None => Ok(Vec::new()),
                    }
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

/// Materialize the handler `Definition`s for the recorded native-handler specs (one per
/// registrable native rule the report-free compile located).
pub fn native_definitions_for(
    specs: &[NativeHandlerSpec],
) -> Result<Vec<Definition>, BandAllocationError> {
    // ★ #36 S4: a `body_ref` must fit ONE `i64` while `(fingerprint, rule_index)` is unbounded,
    // so the derivation cannot be collision-free — only deterministic. Checking here converts
    // the residual 48-bit digest collision from a SILENT wrong dispatch (f1r3node's
    // `dispatch_table_creator` is a `HashMap` keyed by `body_ref`; the later insert simply
    // wins) into a loud, typed refusal. Within one language this cannot fire — the rule index
    // has its own bit field — so it is strictly a cross-co-installed-language guard.
    check_body_refs_pairwise_distinct(
        &NATIVE_HANDLER_BAND,
        specs.iter().map(|spec| {
            (spec.urn.as_str(), native_contract_body_ref(spec.rule_index, &spec.fingerprint))
        }),
    )?;
    Ok(specs.iter().map(native_definition).collect())
}

/// Why a native-handler contract rejected its payload. Every case is an honest, loud failure —
/// the deferral case (`evaluator → None`) is NOT an error (the rule simply does not fire).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeContractError {
    /// An operand `Par` is not a positionally reflected constructor term
    /// (`EList[GPrivate("mettail.term.…"), …]`) — ABI drift or a foreign value.
    OperandNotReflectedTerm,
    /// An operand was reflected under a DIFFERENT definition fingerprint than the handler was
    /// registered for — cross-definition drift.
    FingerprintMismatch { expected: String, actual: String },
}

impl std::fmt::Display for NativeContractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NativeContractError::OperandNotReflectedTerm => {
                write!(f, "operand is not a reflected constructor term (EList[GPrivate tag, …])")
            },
            NativeContractError::FingerprintMismatch { expected, actual } => write!(
                f,
                "operand reflected under fingerprint {actual}, handler registered for {expected}"
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    const FP: &str = "mettail-langdef-v1:test";

    /// `par_to_ground_term` is the exact inverse of `reflect_ground_term_par` on positional
    /// ground terms — including a dotted literal-leaf label (`NumLit(8.5)`), which `split_once`
    /// keeps whole where an `rsplit` would corrupt it.
    #[test]
    fn reflected_ground_term_round_trips() {
        let term = GroundTerm::new(
            "PowInt",
            vec![
                GroundTerm::new("NumLit(2)", Vec::new()),
                GroundTerm::new("NumLit(8.5)", Vec::new()),
            ],
        );
        let par = reflect_ground_term_par(&term, FP);
        let decoded = par_to_ground_term(&par, FP).expect("the reflected term decodes");
        assert_eq!(decoded, term, "decode ∘ reflect = identity (dotted labels included)");
    }

    #[test]
    fn foreign_fingerprint_fails_typed() {
        let term = GroundTerm::new("NumLit(2)", Vec::new());
        let par = reflect_ground_term_par(&term, "mettail-langdef-v1:other");
        match par_to_ground_term(&par, FP) {
            Err(NativeContractError::FingerprintMismatch { expected, actual }) => {
                assert_eq!(expected, FP);
                assert_eq!(actual, "mettail-langdef-v1:other");
            },
            other => panic!("a cross-definition operand must fail typed, got {other:?}"),
        }
    }

    #[test]
    fn non_reflected_operand_fails_typed() {
        let bare_int = Par {
            exprs: vec![models::rhoapi::Expr {
                expr_instance: Some(ExprInstance::GInt(7)),
            }],
            ..Default::default()
        };
        assert_eq!(
            par_to_ground_term(&bare_int, FP),
            Err(NativeContractError::OperandNotReflectedTerm),
            "a bare scalar is not a reflected constructor term"
        );
    }

    /// The `Definition` shape: reserved channel `[0xF1, rule_index]`, arity `k + 1`, reserved
    /// `body_ref` — deterministic per rule index, so replay installs identically.
    #[test]
    fn native_definition_installs_on_the_reserved_band() {
        let spec = NativeHandlerSpec {
            urn: "mtl:native:fp:Int_PowInt".to_string(),
            fired_rule_label: "Int_PowInt".to_string(),
            bare_label: "PowInt".to_string(),
            arity: 2,
            fingerprint: FP.to_string(),
            rule_index: 3,
            dispatch_channel: "sa:scalar/PowInt".to_string(),
            evaluator: Arc::new(|_args| None),
        };
        let definition = native_definition(&spec);
        assert_eq!(definition.urn, "mtl:native:fp:Int_PowInt");
        assert_eq!(definition.arity, 3, "k + 1 = σ operands plus the out channel");
        assert_eq!(definition.body_ref, native_contract_body_ref(3, FP));
        assert_eq!(definition.fixed_channel, native_contract_channel(3, FP));
    }
}
