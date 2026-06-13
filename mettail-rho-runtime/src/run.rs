//! Run a lowered-MeTTaIL Rholang program on a real in-memory f1r3node-rust
//! `RhoRuntime` and read ground results back — the M-RHO.0.5 execution path and
//! the substrate of the M-RHO.0.4 differential oracle.
//!
//! No disk / RocksDB / network: the runtime is backed by `InMemoryStoreManager`
//! (pure `DashMap`). Threading/scheduling are f1r3node's (RSpace + the reducer);
//! MeTTaIL only emits the `Par` program and reads the resting data.

use std::collections::HashMap;
use std::sync::Arc;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_rho_codegen::ValidatedRhoProgram;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{BindPattern, Expr, ListParWithRandom, Par, TaggedContinuation};
use models::rust::utils::new_freevar_par;

use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};

use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

/// A quoted-name channel `@"<name>"` (a `Par` holding a single `GString`).
fn quoted_channel(name: &str) -> Par {
    Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::GString(name.to_string())),
        }],
        ..Default::default()
    }
}

/// Pull the single ground `i64` out of a `Par` of the form `Par{exprs:[GInt(n)]}`.
fn par_as_i64(par: &Par) -> Option<i64> {
    match par.exprs.as_slice() {
        [e] => match &e.expr_instance {
            Some(ExprInstance::GInt(i)) => Some(*i),
            _ => None,
        },
        _ => None,
    }
}

/// Pull the single ground string out of a `Par` of the form `Par{exprs:[GString(s)]}`.
fn par_as_string(par: &Par) -> Option<String> {
    match par.exprs.as_slice() {
        [e] => match &e.expr_instance {
            Some(ExprInstance::GString(s)) => Some(s.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// A one-value wildcard binding pattern for direct `RhoRuntime::consume_result`
/// checks. This mirrors the host normalizer's `for (@x <- @"c")` shape without
/// routing the receive through source text.
fn one_string_bind_pattern() -> BindPattern {
    BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new())],
        remainder: None,
        free_count: 1,
    }
}

fn matched_strings(data: &[ListParWithRandom]) -> Option<Vec<String>> {
    let mut out = Vec::with_capacity(data.len());
    for item in data {
        let [par] = item.pars.as_slice() else {
            return None;
        };
        out.push(par_as_string(par)?);
    }
    Some(out)
}

async fn build_runtime() -> Result<impl RhoRuntime, String> {
    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .map_err(|e| format!("in-mem store: {e:?}"))?;
    let space: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> =
        RSpace::create(store, Arc::new(Box::new(Matcher))).map_err(|e| format!("rspace: {e:?}"))?;

    Ok(create_rho_runtime(
        space,
        Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
        false,                    // init_registry: not needed for pure arithmetic
        &mut Vec::new(),          // no extra system processes
        ExternalServices::noop(), // inert — no ChromaDB/SBERT/OpenAI
    )
    .await)
}

async fn eval_on_runtime<R: RhoRuntime>(runtime: &mut R, program: &str) -> Result<(), String> {
    let result = runtime
        .evaluate_with_term(program)
        .await
        .map_err(|e| format!("evaluate: {e:?}"))?;
    if !result.errors.is_empty() {
        return Err(format!("evaluation errors: {:?}", result.errors));
    }
    Ok(())
}

async fn inj_on_runtime<R: RhoRuntime>(runtime: &mut R, program: Par) -> Result<(), String> {
    let checkpoint = runtime.create_soft_checkpoint().await;
    let rand = Blake2b512Random::create_from_length(128);
    runtime.cost().set(Cost::unsafe_max());
    match runtime.inj(program, Env::new(), rand).await {
        Ok(()) => Ok(()),
        Err(err) => {
            runtime.revert_to_soft_checkpoint(checkpoint).await;
            Err(format!("inj: {err:?}"))
        },
    }
}

async fn read_ground_from_runtime<R, T>(
    runtime: &R,
    out_channel: &str,
    reader: fn(&Par) -> Option<T>,
) -> Vec<T>
where
    R: RhoRuntime,
{
    let channel = quoted_channel(out_channel);
    let data = runtime.get_data(&channel).await;
    let mut out = Vec::new();
    for datum in data {
        for par in &datum.a.pars {
            if let Some(value) = reader(par) {
                out.push(value);
            }
        }
    }
    out
}

async fn evaluate(program: &str) -> Result<impl RhoRuntime, String> {
    let mut runtime = build_runtime().await?;
    eval_on_runtime(&mut runtime, program).await?;
    Ok(runtime)
}

async fn evaluate_par(program: &Par) -> Result<impl RhoRuntime, String> {
    let mut runtime = build_runtime().await?;
    inj_on_runtime(&mut runtime, program.clone()).await?;
    Ok(runtime)
}

async fn evaluate_validated_program(
    program: &ValidatedRhoProgram,
) -> Result<impl RhoRuntime, String> {
    let Some(par) = program.ast_par() else {
        return Err(format!(
            "unsupported validated Rho artifact kind for this runtime: {:?}",
            program.artifact_kind()
        ));
    };
    evaluate_par(par).await
}

async fn evaluate_validated_program_with_call(
    program: &ValidatedRhoProgram,
    call: &Par,
) -> Result<impl RhoRuntime, String> {
    let Some(par) = program.ast_par() else {
        return Err(format!(
            "unsupported validated Rho artifact kind for this runtime: {:?}",
            program.artifact_kind()
        ));
    };
    evaluate_par(&par.append(call.clone())).await
}

async fn run_and_read_ground<T>(
    program: &str,
    out_channel: &str,
    reader: fn(&Par) -> Option<T>,
) -> Result<Vec<T>, String> {
    let runtime = evaluate(program).await?;
    Ok(read_ground_from_runtime(&runtime, out_channel, reader).await)
}

async fn run_par_and_read_ground<T>(
    program: &Par,
    out_channel: &str,
    reader: fn(&Par) -> Option<T>,
) -> Result<Vec<T>, String> {
    let runtime = evaluate_par(program).await?;
    Ok(read_ground_from_runtime(&runtime, out_channel, reader).await)
}

async fn run_validated_program_and_read_ground<T>(
    program: &ValidatedRhoProgram,
    out_channel: &str,
    reader: fn(&Par) -> Option<T>,
) -> Result<Vec<T>, String> {
    let runtime = evaluate_validated_program(program).await?;
    Ok(read_ground_from_runtime(&runtime, out_channel, reader).await)
}

async fn run_validated_program_with_call_and_read_ground<T>(
    program: &ValidatedRhoProgram,
    call: &Par,
    out_channel: &str,
    reader: fn(&Par) -> Option<T>,
) -> Result<Vec<T>, String> {
    let runtime = evaluate_validated_program_with_call(program, call).await?;
    Ok(read_ground_from_runtime(&runtime, out_channel, reader).await)
}

/// Build an in-memory `RhoRuntime` and evaluate hand-authored Rholang source to
/// quiescence for oracle/regression tests.
///
/// `Err` on a store/rspace failure or when evaluation reports interpreter errors
/// (so a malformed source corpus member surfaces, never silently "succeeds").
pub async fn run_rholang_source_for_oracle(program: &str) -> Result<(), String> {
    evaluate(program).await.map(|_| ())
}

/// Build an in-memory `RhoRuntime` and inject a validated generated artifact to
/// quiescence.
///
/// This is the raw shape-validated artifact path used by oracle/debug helpers.
/// Generated backend execution should prefer `PlannedRhoBackend`, which carries
/// the flip-gated `RhoDefaultBackendPlan`.
pub async fn run_validated_program(program: &ValidatedRhoProgram) -> Result<(), String> {
    evaluate_validated_program(program).await.map(|_| ())
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact
/// composed with a dynamic call process, and evaluate to quiescence.
///
/// The static artifact is shape-validated. The call `Par` is dynamic input
/// supplied by the caller/runtime frontend. Generated backend execution should
/// prefer `PlannedRhoBackend`, which carries the flip-gated
/// `RhoDefaultBackendPlan`.
pub async fn run_validated_program_with_call(
    program: &ValidatedRhoProgram,
    call: &Par,
) -> Result<(), String> {
    evaluate_validated_program_with_call(program, call)
        .await
        .map(|_| ())
}

/// Build an in-memory `RhoRuntime` and inject an already-normalized `Par`
/// program to quiescence for oracle/debug tests.
///
/// This is not the generated-backend entry point because it accepts arbitrary
/// `Par`. Generated backend dispatch must use `run_validated_program`.
pub async fn run_normalized_par_for_oracle(program: &Par) -> Result<(), String> {
    evaluate_par(program).await.map(|_| ())
}

/// Build an in-memory `RhoRuntime`, evaluate hand-authored Rholang source to
/// quiescence, and return every ground integer left resting on the quoted
/// channel `@"<out_channel>"`.
pub async fn run_rholang_source_for_oracle_and_read_ints(
    program: &str,
    out_channel: &str,
) -> Result<Vec<i64>, String> {
    run_and_read_ground(program, out_channel, par_as_i64).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and return every ground integer left resting on the quoted
/// channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_and_read_ints(
    program: &ValidatedRhoProgram,
    out_channel: &str,
) -> Result<Vec<i64>, String> {
    run_validated_program_and_read_ground(program, out_channel, par_as_i64).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact
/// composed with a dynamic call process, and return every ground integer left
/// resting on the quoted channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_with_call_and_read_ints(
    program: &ValidatedRhoProgram,
    call: &Par,
    out_channel: &str,
) -> Result<Vec<i64>, String> {
    run_validated_program_with_call_and_read_ground(program, call, out_channel, par_as_i64).await
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every ground integer left resting on the quoted
/// channel `@"<out_channel>"`.
pub async fn run_normalized_par_for_oracle_and_read_ints(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<i64>, String> {
    run_par_and_read_ground(program, out_channel, par_as_i64).await
}

/// Build an in-memory `RhoRuntime`, evaluate hand-authored Rholang source to
/// quiescence, and return every ground string left resting on the quoted channel
/// `@"<out_channel>"`.
pub async fn run_rholang_source_for_oracle_and_read_strings(
    program: &str,
    out_channel: &str,
) -> Result<Vec<String>, String> {
    run_and_read_ground(program, out_channel, par_as_string).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and return every ground string left resting on the quoted channel
/// `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_and_read_strings(
    program: &ValidatedRhoProgram,
    out_channel: &str,
) -> Result<Vec<String>, String> {
    run_validated_program_and_read_ground(program, out_channel, par_as_string).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact
/// composed with a dynamic call process, and return every ground string left
/// resting on the quoted channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_with_call_and_read_strings(
    program: &ValidatedRhoProgram,
    call: &Par,
    out_channel: &str,
) -> Result<Vec<String>, String> {
    run_validated_program_with_call_and_read_ground(program, call, out_channel, par_as_string).await
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every ground string left resting on the quoted
/// channel `@"<out_channel>"`.
pub async fn run_normalized_par_for_oracle_and_read_strings(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<String>, String> {
    run_par_and_read_ground(program, out_channel, par_as_string).await
}

/// Evaluate hand-authored Rholang source, then directly ask RSpace to consume
/// one ground string from each requested quoted channel.
///
/// `channels` may contain duplicates. That is intentional: it lets the Rho
/// backend verify same-channel joins at the RSpace/ADT boundary even when the
/// source-text parser rejects duplicate receive-channel syntax before evaluation.
pub async fn run_rholang_source_for_oracle_then_consume_strings(
    program: &str,
    channels: &[&str],
) -> Result<Option<Vec<String>>, String> {
    if channels.is_empty() {
        return Err("consume requires at least one channel".to_string());
    }

    let mut runtime = build_runtime().await?;
    eval_on_runtime(&mut runtime, program).await?;

    let channel_pars: Vec<Par> = channels
        .iter()
        .map(|channel| quoted_channel(channel))
        .collect();
    let patterns: Vec<BindPattern> = channels.iter().map(|_| one_string_bind_pattern()).collect();

    let result = runtime
        .consume_result(channel_pars, patterns)
        .await
        .map_err(|e| format!("consume_result: {e:?}"))?;

    match result {
        Some((_continuation, data)) => matched_strings(&data)
            .map(Some)
            .ok_or_else(|| "consume_result matched non-string data".to_string()),
        None => Ok(None),
    }
}

/// Evaluate hand-authored Rholang source programs sequentially on one in-memory
/// `RhoRuntime`, then return every ground string left resting on each requested
/// quoted channel.
///
/// This is used by the M-RHO.1 race oracle: installing a receive first and then
/// submitting sends one at a time makes send-arrival order explicit without
/// relying on host scheduler traces.
pub async fn run_rholang_source_sequence_for_oracle_and_read_strings(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<String>>, String> {
    let mut runtime = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program).await?;
    }

    let mut result = HashMap::new();
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_string).await,
        );
    }
    Ok(result)
}

/// Evaluate hand-authored Rholang source programs sequentially on one in-memory
/// `RhoRuntime`, then return every ground integer left resting on each requested
/// quoted channel.
pub async fn run_rholang_source_sequence_for_oracle_and_read_ints(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<i64>>, String> {
    let mut runtime = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program).await?;
    }

    let mut result = HashMap::new();
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_i64).await,
        );
    }
    Ok(result)
}

#[deprecated(
    note = "use run_rholang_source_for_oracle; generated backend execution should use run_validated_program"
)]
pub async fn run_program(program: &str) -> Result<(), String> {
    run_rholang_source_for_oracle(program).await
}

#[deprecated(
    note = "use run_normalized_par_for_oracle for raw-Par oracle/debug tests; generated backend execution should use run_validated_program"
)]
pub async fn run_par(program: &Par) -> Result<(), String> {
    run_normalized_par_for_oracle(program).await
}

#[deprecated(
    note = "use run_rholang_source_for_oracle_and_read_ints for source oracles; generated backend execution should use run_validated_program_and_read_ints"
)]
pub async fn run_and_read_ints(program: &str, out_channel: &str) -> Result<Vec<i64>, String> {
    run_rholang_source_for_oracle_and_read_ints(program, out_channel).await
}

#[deprecated(
    note = "use run_normalized_par_for_oracle_and_read_ints for raw-Par oracle/debug tests; generated backend execution should use run_validated_program_and_read_ints"
)]
pub async fn run_par_and_read_ints(program: &Par, out_channel: &str) -> Result<Vec<i64>, String> {
    run_normalized_par_for_oracle_and_read_ints(program, out_channel).await
}

#[deprecated(
    note = "use run_rholang_source_for_oracle_and_read_strings for source oracles; generated backend execution should use run_validated_program_and_read_strings"
)]
pub async fn run_and_read_strings(program: &str, out_channel: &str) -> Result<Vec<String>, String> {
    run_rholang_source_for_oracle_and_read_strings(program, out_channel).await
}

#[deprecated(
    note = "use run_normalized_par_for_oracle_and_read_strings for raw-Par oracle/debug tests; generated backend execution should use run_validated_program_and_read_strings"
)]
pub async fn run_par_and_read_strings(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<String>, String> {
    run_normalized_par_for_oracle_and_read_strings(program, out_channel).await
}

#[deprecated(
    note = "use run_rholang_source_for_oracle_then_consume_strings; this helper is for source-text oracle tests"
)]
pub async fn run_program_then_consume_strings(
    program: &str,
    channels: &[&str],
) -> Result<Option<Vec<String>>, String> {
    run_rholang_source_for_oracle_then_consume_strings(program, channels).await
}

#[deprecated(
    note = "use run_rholang_source_sequence_for_oracle_and_read_strings; this helper is for source-text oracle tests"
)]
pub async fn run_sequence_and_read_strings(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<String>>, String> {
    run_rholang_source_sequence_for_oracle_and_read_strings(programs, out_channels).await
}

#[deprecated(
    note = "use run_rholang_source_sequence_for_oracle_and_read_ints; this helper is for source-text oracle tests"
)]
pub async fn run_sequence_and_read_ints(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<i64>>, String> {
    run_rholang_source_sequence_for_oracle_and_read_ints(programs, out_channels).await
}
