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
#[cfg(feature = "runtime-report")]
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::expr::ExprInstance;
#[cfg(feature = "runtime-report")]
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::{BindPattern, Expr, ListParWithRandom, Par, TaggedContinuation};
#[cfg(feature = "runtime-report")]
use models::rust::rholang::implicits::GPrivateBuilder;
#[cfg(feature = "source-oracle")]
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

/// Pull the single ground boolean out of a `Par` of the form `Par{exprs:[GBool(b)]}`.
fn par_as_bool(par: &Par) -> Option<bool> {
    match par.exprs.as_slice() {
        [e] => match &e.expr_instance {
            Some(ExprInstance::GBool(b)) => Some(*b),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(feature = "runtime-report")]
fn par_has_only_ground_value_fields(par: &Par) -> bool {
    par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
        && par.locally_free.is_empty()
        && !par.connective_used
}

#[cfg(feature = "runtime-report")]
fn single_expr_instance(par: &Par) -> Option<&ExprInstance> {
    if !par_has_only_ground_value_fields(par) || !par.unforgeables.is_empty() {
        return None;
    }

    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

#[cfg(feature = "runtime-report")]
fn par_as_unforgeable_observation(par: &Par) -> Option<RuntimeObservationValue> {
    if !par_has_only_ground_value_fields(par) || !par.exprs.is_empty() {
        return None;
    }

    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };

    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => {
            Some(RuntimeObservationValue::PrivateName(value.id.clone()))
        },
        UnfInstance::GDeployIdBody(value) => {
            Some(RuntimeObservationValue::DeployId(value.sig.clone()))
        },
        UnfInstance::GDeployerIdBody(value) => {
            Some(RuntimeObservationValue::DeployerId(value.public_key.clone()))
        },
        UnfInstance::GSysAuthTokenBody(_) => Some(RuntimeObservationValue::SysAuthToken),
    }
}

#[cfg(feature = "runtime-report")]
fn decode_runtime_values(pars: &[Par]) -> Option<Vec<RuntimeObservationValue>> {
    pars.iter().map(par_as_runtime_observation_value).collect()
}

#[cfg(feature = "runtime-report")]
fn decode_runtime_map(
    pairs: &[models::rhoapi::KeyValuePair],
) -> Option<Vec<(RuntimeObservationValue, RuntimeObservationValue)>> {
    let mut out = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let key = par_as_runtime_observation_value(pair.key.as_ref()?)?;
        let value = par_as_runtime_observation_value(pair.value.as_ref()?)?;
        out.push((key, value));
    }
    out.sort();
    Some(out)
}

#[cfg(feature = "runtime-report")]
fn list_body(par: &Par) -> Option<&models::rhoapi::EList> {
    match single_expr_instance(par)? {
        ExprInstance::EListBody(list) if list.remainder.is_none() && !list.connective_used => {
            Some(list)
        },
        _ => None,
    }
}

#[cfg(feature = "runtime-report")]
fn decode_rhocalc_bag(
    list: &models::rhoapi::EList,
) -> Option<Vec<(RuntimeObservationValue, usize)>> {
    let [tag, entries] = list.ps.as_slice() else {
        return None;
    };
    let expected_tag = GPrivateBuilder::new_par_from_string(crate::RHOCALC_BAG_ABI_TAG.to_string());
    if tag != &expected_tag {
        return None;
    }

    let entries = list_body(entries)?;
    let mut counts = std::collections::BTreeMap::<RuntimeObservationValue, usize>::new();
    for entry in &entries.ps {
        let entry = list_body(entry)?;
        let [value, count] = entry.ps.as_slice() else {
            return None;
        };
        let value = par_as_runtime_observation_value(value)?;
        let count = match par_as_runtime_observation_value(count)? {
            RuntimeObservationValue::Int(count) if count >= 0 => usize::try_from(count).ok()?,
            _ => return None,
        };
        let slot = counts.entry(value).or_insert(0);
        *slot = slot.checked_add(count)?;
    }
    Some(counts.into_iter().collect())
}

/// Pull one closed Rho ground value out of a `Par`.
///
/// This deliberately rejects arbitrary process bodies. Runtime observations are
/// public resting data values: scalars, unforgeable names, closed collection
/// bodies, and rhocalc's tagged bag ABI.
#[cfg(feature = "runtime-report")]
pub fn par_as_runtime_observation_value(par: &Par) -> Option<RuntimeObservationValue> {
    if let Some(value) = par_as_unforgeable_observation(par) {
        return Some(value);
    }

    match single_expr_instance(par)? {
        ExprInstance::GBool(value) => Some(RuntimeObservationValue::Bool(*value)),
        ExprInstance::GInt(value) => Some(RuntimeObservationValue::Int(*value)),
        ExprInstance::GString(value) => Some(RuntimeObservationValue::Text(value.clone())),
        ExprInstance::GUri(value) => Some(RuntimeObservationValue::Uri(value.clone())),
        ExprInstance::GByteArray(value) => Some(RuntimeObservationValue::Bytes(value.clone())),
        ExprInstance::GDouble(value) => Some(RuntimeObservationValue::DoubleBits(*value)),
        ExprInstance::GBigInt(value) => Some(RuntimeObservationValue::BigIntBytes(value.clone())),
        ExprInstance::GBigRat(value) => Some(RuntimeObservationValue::BigRationalBytes {
            numerator: value.numerator.clone(),
            denominator: value.denominator.clone(),
        }),
        ExprInstance::GFixedPoint(value) => Some(RuntimeObservationValue::FixedPointBytes {
            unscaled: value.unscaled.clone(),
            scale: value.scale,
        }),
        ExprInstance::EListBody(list) if list.remainder.is_none() && !list.connective_used => {
            if let Some(entries) = decode_rhocalc_bag(list) {
                Some(RuntimeObservationValue::Bag(entries))
            } else {
                Some(RuntimeObservationValue::List(decode_runtime_values(&list.ps)?))
            }
        },
        ExprInstance::ETupleBody(tuple) if !tuple.connective_used => {
            Some(RuntimeObservationValue::Tuple(decode_runtime_values(&tuple.ps)?))
        },
        ExprInstance::ESetBody(set) if set.remainder.is_none() && !set.connective_used => {
            let mut values = decode_runtime_values(&set.ps)?;
            values.sort();
            Some(RuntimeObservationValue::Set(values))
        },
        ExprInstance::EMapBody(map) if map.remainder.is_none() && !map.connective_used => {
            Some(RuntimeObservationValue::Map(decode_runtime_map(&map.kvs)?))
        },
        _ => None,
    }
}

/// A one-value wildcard binding pattern for direct `RhoRuntime::consume_result`
/// checks. This mirrors the host normalizer's `for (@x <- @"c")` shape without
/// routing the receive through source text.
#[cfg(feature = "source-oracle")]
fn one_string_bind_pattern() -> BindPattern {
    BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new())],
        remainder: None,
        free_count: 1,
    }
}

#[cfg(feature = "source-oracle")]
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

fn matched_string_tuple(data: &ListParWithRandom) -> Option<Vec<String>> {
    data.pars.iter().map(par_as_string).collect()
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

#[cfg(feature = "source-oracle")]
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

async fn read_string_tuples_from_runtime<R>(runtime: &R, out_channel: &str) -> Vec<Vec<String>>
where
    R: RhoRuntime,
{
    let channel = quoted_channel(out_channel);
    let data = runtime.get_data(&channel).await;
    let mut out = Vec::new();
    for datum in data {
        if let Some(tuple) = matched_string_tuple(&datum.a) {
            out.push(tuple);
        }
    }
    out
}

#[cfg(feature = "source-oracle")]
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

#[cfg(feature = "source-oracle")]
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
#[cfg(feature = "source-oracle")]
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
#[cfg(feature = "source-oracle")]
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
#[cfg(feature = "source-oracle")]
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

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and return every ground string left resting on each requested
/// quoted channel.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`; tests for generated artifact families use
/// this when one artifact intentionally exposes several observation channels.
pub async fn run_validated_program_and_read_string_channels(
    program: &ValidatedRhoProgram,
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<String>>, String> {
    let runtime = evaluate_validated_program(program).await?;
    let mut result = HashMap::new();
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_string).await,
        );
    }
    Ok(result)
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and read one closed-ground-value channel plus one string trace
/// channel from the same execution.
///
/// This is used by planned call-by-need reports, where the computed payload is
/// typed generated-language data and the evaluation channel is intentionally a
/// textual trace marker.
#[cfg(feature = "runtime-report")]
pub async fn run_validated_program_and_read_runtime_value_and_string_channels(
    program: &ValidatedRhoProgram,
    value_channel: &str,
    string_channel: &str,
) -> Result<(Vec<RuntimeObservationValue>, Vec<String>), String> {
    let runtime = evaluate_validated_program(program).await?;
    let values =
        read_ground_from_runtime(&runtime, value_channel, par_as_runtime_observation_value).await;
    let strings = read_ground_from_runtime(&runtime, string_channel, par_as_string).await;
    Ok((values, strings))
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

/// Build an in-memory `RhoRuntime`, evaluate hand-authored Rholang source to
/// quiescence, and return every ground boolean left resting on the quoted
/// channel `@"<out_channel>"`.
#[cfg(feature = "source-oracle")]
pub async fn run_rholang_source_for_oracle_and_read_bools(
    program: &str,
    out_channel: &str,
) -> Result<Vec<bool>, String> {
    run_and_read_ground(program, out_channel, par_as_bool).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and return every ground boolean left resting on the quoted
/// channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_and_read_bools(
    program: &ValidatedRhoProgram,
    out_channel: &str,
) -> Result<Vec<bool>, String> {
    run_validated_program_and_read_ground(program, out_channel, par_as_bool).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact
/// composed with a dynamic call process, and return every ground boolean left
/// resting on the quoted channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
pub async fn run_validated_program_with_call_and_read_bools(
    program: &ValidatedRhoProgram,
    call: &Par,
    out_channel: &str,
) -> Result<Vec<bool>, String> {
    run_validated_program_with_call_and_read_ground(program, call, out_channel, par_as_bool).await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact to
/// quiescence, and return every closed Rho ground value left resting on the
/// quoted channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
#[cfg(feature = "runtime-report")]
pub async fn run_validated_program_and_read_runtime_values(
    program: &ValidatedRhoProgram,
    out_channel: &str,
) -> Result<Vec<RuntimeObservationValue>, String> {
    run_validated_program_and_read_ground(program, out_channel, par_as_runtime_observation_value)
        .await
}

/// Build an in-memory `RhoRuntime`, inject a validated generated artifact
/// composed with a dynamic call process, and return every closed Rho ground
/// value left resting on the quoted channel `@"<out_channel>"`.
///
/// This is a raw shape-validated artifact helper. Generated backend observation
/// should prefer `PlannedRhoBackend`.
#[cfg(feature = "runtime-report")]
pub async fn run_validated_program_with_call_and_read_runtime_values(
    program: &ValidatedRhoProgram,
    call: &Par,
    out_channel: &str,
) -> Result<Vec<RuntimeObservationValue>, String> {
    run_validated_program_with_call_and_read_ground(
        program,
        call,
        out_channel,
        par_as_runtime_observation_value,
    )
    .await
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every ground boolean left resting on the quoted
/// channel `@"<out_channel>"`.
pub async fn run_normalized_par_for_oracle_and_read_bools(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<bool>, String> {
    run_par_and_read_ground(program, out_channel, par_as_bool).await
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

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every ground string left resting on each
/// requested quoted channel.
pub async fn run_normalized_par_for_oracle_and_read_string_channels(
    program: &Par,
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<String>>, String> {
    let runtime = evaluate_par(program).await?;
    let mut result = HashMap::new();
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_string).await,
        );
    }
    Ok(result)
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every closed Rho ground value left resting on
/// the quoted channel `@"<out_channel>"`.
#[cfg(feature = "runtime-report")]
pub async fn run_normalized_par_for_oracle_and_read_runtime_values(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<RuntimeObservationValue>, String> {
    run_par_and_read_ground(program, out_channel, par_as_runtime_observation_value).await
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every all-string tuple left resting on the
/// quoted channel `@"<out_channel>"`.
pub async fn run_normalized_par_for_oracle_and_read_string_tuples(
    program: &Par,
    out_channel: &str,
) -> Result<Vec<Vec<String>>, String> {
    let runtime = evaluate_par(program).await?;
    Ok(read_string_tuples_from_runtime(&runtime, out_channel).await)
}

/// Evaluate hand-authored Rholang source, then directly ask RSpace to consume
/// one ground string from each requested quoted channel.
///
/// `channels` may contain duplicates. That is intentional: it lets the Rho
/// backend verify same-channel joins at the RSpace/ADT boundary even when the
/// source-text parser rejects duplicate receive-channel syntax before evaluation.
#[cfg(feature = "source-oracle")]
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
#[cfg(feature = "source-oracle")]
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
#[cfg(feature = "source-oracle")]
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

/// Evaluate hand-authored Rholang source programs sequentially on one in-memory
/// `RhoRuntime`, then return every ground boolean left resting on each requested
/// quoted channel.
#[cfg(feature = "source-oracle")]
pub async fn run_rholang_source_sequence_for_oracle_and_read_bools(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<bool>>, String> {
    let mut runtime = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program).await?;
    }

    let mut result = HashMap::new();
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_bool).await,
        );
    }
    Ok(result)
}
