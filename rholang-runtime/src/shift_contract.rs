//! Native one-COMM shift-by-k system process for A-S5.8 binder-template reconstruction.
//!
//! The generated call is `[amount:u128-le, reflected_value, out]`. Dispatch performs one
//! stack-safe traversal with [`mettail_rholang_codegen::shift_reflected_par_by`] and produces
//! the result directly on `out`. This uses the same cost-accounted system-process COMM seam as
//! held folds and native rule handlers; no stack-size override or `stacker` trampoline is used.

use std::future::Future;
use std::pin::Pin;

use mettail_rholang_codegen::{
    check_body_refs_pairwise_distinct, decode_native_shift_amount, native_shift_body_ref,
    native_shift_channel, native_shift_urn, shift_reflected_par_by, BandAllocationError,
    NativeShiftSpec, NATIVE_SHIFT_BAND,
};
use models::rhoapi::Par;
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;

pub fn native_shift_definition(spec: &NativeShiftSpec) -> Definition {
    let spec = spec.clone();
    let urn = native_shift_urn(spec.fingerprint());
    Definition {
        urn: urn.clone(),
        fixed_channel: native_shift_channel(spec.fingerprint()),
        arity: 3,
        body_ref: native_shift_body_ref(spec.fingerprint()),
        remainder: None,
        handler: Box::new(move |ctx| {
            let space = ctx.space.clone();
            let dispatcher = ctx.dispatcher.clone();
            let spec = spec.clone();
            let urn = urn.clone();
            Box::new(move |args| {
                let cc = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let spec = spec.clone();
                let urn = urn.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = cc.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{urn}: not a single-message contract call"
                        )));
                    };
                    let [amount, value, out] = payload.as_slice() else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{urn}: expected [amount, value, out], got arity {}",
                            payload.len()
                        )));
                    };
                    let amount = decode_native_shift_amount(amount).map_err(|err| {
                        InterpreterError::IllegalArgumentError(format!("{urn}: {err}"))
                    })?;
                    let Ok(shifted) = shift_reflected_par_by(value, amount, &spec) else {
                        // The in-Rho receiver has no wildcard error arm: malformed/foreign/
                        // unsupported subjects stall and produce nothing. Preserve that failure
                        // behavior rather than converting semantic no-fire into an ABI exception.
                        return Ok(Vec::new());
                    };
                    let output = vec![shifted];
                    produce(&output, out).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

pub fn native_shift_definitions_for(
    specs: &[NativeShiftSpec],
) -> Result<Vec<Definition>, BandAllocationError> {
    let urns: Vec<String> = specs
        .iter()
        .map(|spec| native_shift_urn(spec.fingerprint()))
        .collect();
    check_body_refs_pairwise_distinct(
        &NATIVE_SHIFT_BAND,
        urns.iter().map(String::as_str).zip(
            specs
                .iter()
                .map(|spec| native_shift_body_ref(spec.fingerprint())),
        ),
    )?;
    Ok(specs.iter().map(native_shift_definition).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definition_uses_the_shift_band_and_fixed_arity() {
        let spec = NativeShiftSpec::new("mettail-langdef-v1:00", [], []);
        let definition = native_shift_definition(&spec);
        assert_eq!(definition.urn, native_shift_urn(spec.fingerprint()));
        assert_eq!(definition.fixed_channel, native_shift_channel(spec.fingerprint()));
        assert_eq!(definition.body_ref, native_shift_body_ref(spec.fingerprint()));
        assert_eq!(definition.arity, 3);
    }
}
