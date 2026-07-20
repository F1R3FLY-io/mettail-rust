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
use mettail_rholang_codegen::ValidatedRhoProgram;
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
#[cfg(feature = "runtime-report")]
use prost::Message;

use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rholang::rust::interpreter::system_processes::Definition;

use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

/// A quoted-name channel `@"<name>"` (a `Par` holding a single `GString`).
pub(crate) fn quoted_channel(name: &str) -> Par {
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

/// Whether `par` is a NON-empty sends-only parallel composition — the AC bag-carrier soup shape
/// (Stage AC2b): at least one `Send` and every other `Par` field empty/closed. Mirrors the exact
/// field set of [`par_has_only_ground_value_fields`], inverted for `sends`.
#[cfg(feature = "runtime-report")]
fn par_is_only_sends(par: &Par) -> bool {
    !par.sends.is_empty()
        && par.exprs.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
        && par.unforgeables.is_empty()
        && par.locally_free.is_empty()
        && !par.connective_used
}

/// The AC bag-carrier operator label `op` a soup send's channel `@"ac:{op}"` carries, when the
/// channel is a quoted `GString` with the reserved `"ac:"` prefix and a non-empty operator.
#[cfg(feature = "runtime-report")]
fn ac_soup_channel_op(chan: &Par) -> Option<&str> {
    match single_expr_instance(chan)? {
        ExprInstance::GString(name) => name.strip_prefix("ac:").filter(|op| !op.is_empty()),
        _ => None,
    }
}

/// Decode the AC bag-carrier process soup — a bag-VALUED AC RHS's OUT value (Stage AC2b) — into a
/// multiset of decoded elements.
///
/// The carrier is a sends-only parallel `Par` in which every send is `@"ac:{op}"!(⟦e⟧)`, the exact
/// shape the codegen `reflect_ac_bag_par` (subject side) and `reflect_hashbag_soup_par` (the AC
/// receiver's bag-RHS body) emit for a `HashBag`: all sends on the SAME `"ac:{op}"` channel, each
/// with exactly one datum, non-persistent, with nothing else present. Each datum decodes through
/// the same [`par_as_runtime_observation_value`], so a bag whose elements are themselves reflected
/// terms (e.g. `Wrap(A)`) decodes recursively. Returns `None` for any `Par` that is not exactly
/// such a soup — a tagged-`EList` term, a scalar, an unforgeable, a `for`-carrying process, or a
/// mixed-operator soup — so this never mis-claims another observation shape (the `"ac:"` channel
/// prefix + sends-only shape are disjoint from every other decoder's head).
#[cfg(feature = "runtime-report")]
fn decode_ac_bag_soup(par: &Par) -> Option<Vec<(RuntimeObservationValue, usize)>> {
    if !par_is_only_sends(par) {
        return None;
    }
    let mut op: Option<&str> = None;
    let mut counts = std::collections::BTreeMap::<RuntimeObservationValue, usize>::new();
    for send in &par.sends {
        if send.persistent {
            return None;
        }
        let send_op = ac_soup_channel_op(send.chan.as_ref()?)?;
        match op {
            None => op = Some(send_op),
            Some(existing) if existing == send_op => {},
            // Mixed operators are not a single AC bag — fail closed rather than merge two bags.
            Some(_) => return None,
        }
        let [datum] = send.data.as_slice() else {
            return None;
        };
        let value = par_as_runtime_observation_value(datum)?;
        let slot = counts.entry(value).or_insert(0);
        *slot = slot.checked_add(1)?;
    }
    Some(counts.into_iter().collect())
}

/// Recover the UTF-8 tag string carried by a private-name `Par`, when that name
/// was built by `GPrivateBuilder::new_par_from_string(s)`.
///
/// That builder sets the unforgeable's `id` to `s.encode_to_vec()`, i.e.
/// `<String as prost::Message>` — protobuf field 1, length-delimited. `String::
/// decode` is that builder's exact inverse, so this needs no direct knowledge of
/// the wire layout. Returns `None` for any `Par` that is not exactly one
/// `GPrivate` unforgeable, or whose `id` is not a valid encoded string (e.g. a
/// `GPrivate` created by `new_par` from a random UUID still decodes, but its tag
/// simply will not carry the reflected-term prefix).
#[cfg(feature = "runtime-report")]
fn private_name_tag(par: &Par) -> Option<String> {
    if !par_has_only_ground_value_fields(par) || !par.exprs.is_empty() {
        return None;
    }
    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => String::decode(value.id.as_slice()).ok(),
        _ => None,
    }
}

/// Decode a reflected constructor term list into a structural
/// [`RuntimeObservationValue::Term`], mirroring [`decode_rhocalc_bag`].
///
/// The reflected-term ABI (codegen `reflect_ground_term_par` / the RHS reflector)
/// is `EList[GPrivate("mettail.term.{fingerprint}.{label}"), children…]`. This
/// returns `None` unless the list's head is a private name whose tag carries the
/// shared [`crate::REFLECTED_TERM_ABI_PREFIX`]. The fingerprint
/// (`mettail-langdef-v1:<hex>`) contains no `.` and a constructor label is a
/// dot-free identifier, so the final `.` of the remainder separates fingerprint
/// from label. Each child is decoded through the same
/// [`par_as_runtime_observation_value`] entry point, so a nested reflected term
/// (a σ argument that is itself a constructor) decodes recursively.
#[cfg(feature = "runtime-report")]
fn decode_reflected_term(list: &models::rhoapi::EList) -> Option<RuntimeObservationValue> {
    let (head, children) = list.ps.split_first()?;
    let tag = private_name_tag(head)?;
    let suffix = tag.strip_prefix(crate::REFLECTED_TERM_ABI_PREFIX)?;
    let (_fingerprint, label) = suffix.rsplit_once('.')?;
    if label.is_empty() {
        return None;
    }
    let children = children
        .iter()
        .map(par_as_runtime_observation_value)
        .collect::<Option<Vec<_>>>()?;
    Some(RuntimeObservationValue::Term { constructor: label.to_string(), children })
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

    // Stage AC2b: a bag-VALUED AC RHS lands on OUT as the bare process-soup carrier
    // (`@"ac:{op}"!(⟦e⟧) | …`) — the SAME shape a `HashBag` reflects to — not an `EList`. Decode
    // it to a multiset `Bag`. The `"ac:"` channel + sends-only shape are disjoint from every
    // `single_expr_instance` head below, so this claims only the AC carrier.
    if let Some(entries) = decode_ac_bag_soup(par) {
        return Some(RuntimeObservationValue::Bag(entries));
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
            // Try the reflected-term ABI first (head = a `mettail.term.` private
            // name), then the rhocalc bag ABI (head = the bag tag), else a plain
            // list. The three head shapes are disjoint, so ordering only decides
            // which decoder claims a match, never correctness.
            if let Some(term) = decode_reflected_term(list) {
                Some(term)
            } else if let Some(entries) = decode_rhocalc_bag(list) {
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

thread_local! {
    // Tier-3: held-fold contract `Definition`s for the CURRENT exec on THIS worker thread. The exec
    // path spawns a fresh worker (`backend::run_rho_invocation_blocking`) that calls
    // `set_pending_fold_definitions` before `block_on`, and `build_runtime` (running inside that
    // `block_on`, same thread) drains them here. Worker threads are fresh per invocation and `take`
    // clears, so nothing leaks across runs. Empty unless the term lifted a held fold.
    static PENDING_FOLD_DEFINITIONS: std::cell::RefCell<Vec<Definition>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Stash the held-fold contract `Definition`s for the next [`build_runtime`] on THIS thread (the
/// exec worker). See `backend::run_rho_invocation_blocking`.
pub(crate) fn set_pending_fold_definitions(definitions: Vec<Definition>) {
    PENDING_FOLD_DEFINITIONS.with(|cell| *cell.borrow_mut() = definitions);
}

/// Take (and clear) the pending held-fold contract `Definition`s for this thread.
fn take_pending_fold_definitions() -> Vec<Definition> {
    PENDING_FOLD_DEFINITIONS.with(|cell| std::mem::take(&mut *cell.borrow_mut()))
}

async fn build_runtime() -> Result<impl RhoRuntime, String> {
    // Tier-3 / A-S3 contracts for this exec (empty for every term without a held fold or an
    // admitted native rule, so the common path is byte-identical to the prior `&mut Vec::new()`).
    build_runtime_with_definitions(take_pending_fold_definitions()).await
}

/// Build an in-memory `RhoRuntime` with EXPLICIT extra system-process `Definition`s (the
/// MeTTaIL-injected held-fold / A-S3 native-handler contracts) instead of the thread-local
/// pending slot. The explicit variant exists so a caller that already HOLDS the definitions —
/// e.g. the A-S3 trusted-handler probes, which drain the recorded
/// [`NativeHandlerSpec`](mettail_rholang_codegen::NativeHandlerSpec)s themselves — can thread
/// them without relying on same-thread thread-local discipline.
async fn build_runtime_with_definitions(
    mut extra_system_processes: Vec<Definition>,
) -> Result<impl RhoRuntime, String> {
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
        &mut extra_system_processes, // held-fold + native-handler contracts (usually none)
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

/// Build an in-memory `RhoRuntime`, inject an installed Rho-net program composed
/// with a dynamic σ-injection call, and return every closed Rho ground value left
/// resting on the quoted channel `@"<out_channel>"`.
///
/// This is the runtime side of the Epic 4 injection bridge's CRITICAL composition
/// step. A language's base-rewrite σ-receivers live in its **installed Rho-net
/// program** (`RhoDefaultBackendPlan::installed_rho_net_program_par`), NOT in the
/// scalar `validated_program`, so a σ injection only fires when it is composed
/// against the installed program (`installed.append(call)` — mirroring
/// `run_validated_program_with_call`'s `par.append(call)` and the reactive
/// stepper's `contracts.append(call)`). Without this composition the injection
/// would reach no contract and OUT would be empty — a silent false pass. It
/// mirrors [`run_validated_program_with_call_and_read_runtime_values`] but takes
/// the raw installed program `Par` rather than a `ValidatedRhoProgram`.
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_and_read_runtime_values(
    installed_program: &Par,
    call: &Par,
    out_channel: &str,
) -> Result<Vec<RuntimeObservationValue>, String> {
    let composed = installed_program.append(call.clone());
    run_par_and_read_ground(&composed, out_channel, par_as_runtime_observation_value).await
}

/// [`run_installed_program_with_call_and_read_runtime_values`] with EXPLICIT extra
/// system-process `Definition`s (the MeTTaIL-injected held-fold / A-S3 native-handler
/// contracts) installed on the runtime before the composed program runs.
///
/// The production exec path threads its definitions through the worker-thread pending slot
/// (`backend::run_rho_invocation_blocking` → [`set_pending_fold_definitions`]); this explicit
/// variant serves callers that hold the definitions directly — the A-S3 trusted-handler probes,
/// which corrupt the call `Par` between compile and run and therefore drive the run themselves.
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_definitions_and_read_runtime_values(
    installed_program: &Par,
    call: &Par,
    definitions: Vec<Definition>,
    out_channel: &str,
) -> Result<Vec<RuntimeObservationValue>, String> {
    let composed = installed_program.append(call.clone());
    let runtime = {
        let mut runtime = build_runtime_with_definitions(definitions).await?;
        inj_on_runtime(&mut runtime, composed).await?;
        runtime
    };
    Ok(read_ground_from_runtime(&runtime, out_channel, par_as_runtime_observation_value).await)
}

/// The four observation channels of one in-Rho quiescence-driver execution
/// (A-S5.2, plan v2 §4.5 / F7): the resting-term channel plus the three reserved
/// GString observation channels the generated `^drive` receiver family emits on.
///
/// All four are **GString names** (host readback uses the proven `get_data`
/// path — the E-6a multi-channel precedent); every in-Rho-only rendezvous
/// (`^drive` itself, the fresh per-node returns, the σ-ABI accepts) stays
/// `GPrivate` and is deliberately NOT readable here. The names are derived from
/// the language fingerprint by the codegen naming helpers
/// (`mettail_rholang_codegen::drive_fired_channel` et al.); this struct carries
/// them as plain strings so the runtime surface stays codegen-shape-agnostic.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DriveObservationChannels {
    /// The quoted channel the driver's quiescent resting term lands on (the
    /// `ret` threaded from the seed).
    pub out: String,
    /// The firing ledger `@"^fired:{fp}"` — one GString rule label per firing.
    pub fired: String,
    /// The typed fail-close channel `@"^drive-err:{fp}"` — an unrecognized
    /// driven head rests here (never silently normal).
    pub err: String,
    /// The typed fuel-exhaustion channel `@"^drive-fuel:{fp}"` — the stuck
    /// redex node rests here when a firing arm sees fuel 0.
    pub fuel: String,
}

/// The decoded observation set of one in-Rho quiescence-driver execution
/// (A-S5.2, plan v2 §4.5): decoded OUT values plus the RAW resting data of the
/// three reserved observation channels.
///
/// OUT is decoded through [`par_as_runtime_observation_value`] (fail-loud at
/// the read: an undecodable OUT datum is an error, never silently dropped).
/// The ledger / error / fuel channels are kept as raw `Par` data: their
/// payloads are diagnostic (a GString rule label; the offending reflected
/// node), and the always-on cross-check wants to see EXACTLY what rested there
/// — including malformed data, which is itself a violation.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq)]
pub struct DriveObservationSet {
    /// Decoded closed ground values resting on the OUT channel.
    pub out_values: Vec<RuntimeObservationValue>,
    /// Raw firing-ledger data (`@"^fired:{fp}"`) — expected: one GString rule
    /// label per firing.
    pub fired_data: Vec<Par>,
    /// Raw typed-error data (`@"^drive-err:{fp}"`) — expected EMPTY on a green
    /// drive.
    pub err_data: Vec<Par>,
    /// Raw fuel-exhaustion data (`@"^drive-fuel:{fp}"`) — expected EMPTY on a
    /// green drive.
    pub fuel_data: Vec<Par>,
}

#[cfg(feature = "runtime-report")]
impl DriveObservationSet {
    /// The firing-ledger rule labels, decoded from [`fired_data`](Self::fired_data).
    /// `Err` (naming the ledger channel shape) if any ledger datum is not a
    /// single ground GString — a malformed ledger is a driver defect, never
    /// silently skipped.
    pub fn fired_labels(&self) -> Result<Vec<String>, String> {
        let mut labels = Vec::with_capacity(self.fired_data.len());
        for par in &self.fired_data {
            match par_as_string(par) {
                Some(label) => labels.push(label),
                None => {
                    return Err(format!(
                        "drive firing-ledger datum is not a single ground GString rule label: {par:?}"
                    ));
                },
            }
        }
        Ok(labels)
    }
}

/// A raw pass-through reader for [`read_ground_from_runtime`] — captures every
/// resting datum verbatim (never `None`), so the observation-channel readback
/// cannot silently drop malformed data.
#[cfg(feature = "runtime-report")]
fn par_verbatim(par: &Par) -> Option<Par> {
    Some(par.clone())
}

/// Build an in-memory `RhoRuntime`, inject an installed Rho-net program composed
/// with a dynamic call (the `^drive` seed), run to quiescence, and read back the
/// FULL drive observation set — decoded OUT values plus the raw resting data of
/// the three reserved GString observation channels — from ONE execution.
///
/// This is the A-S5.2 (F7) multi-channel readback surface: the single-channel
/// observe seam ([`run_installed_program_with_call_and_read_runtime_values`])
/// reads only OUT, which cannot see the driver's firing ledger or its typed
/// fail-close channels. Composition mirrors the single-channel path
/// (`installed.append(call)`); the four reads share one runtime (the
/// [`run_validated_program_and_read_string_channels`] / E-6a `get_data`
/// multi-channel precedent).
///
/// Fail-loud decode: an OUT datum that does not decode as a closed runtime
/// observation value is an `Err` naming the OUT channel — never a silent drop
/// (the drive cross-check depends on OUT being fully accounted for).
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_and_read_observation_set(
    installed_program: &Par,
    call: &Par,
    channels: &DriveObservationChannels,
) -> Result<DriveObservationSet, String> {
    let composed = installed_program.append(call.clone());
    let runtime = evaluate_par(&composed).await?;

    let out_raw = read_ground_from_runtime(&runtime, &channels.out, par_verbatim).await;
    let mut out_values = Vec::with_capacity(out_raw.len());
    for par in &out_raw {
        match par_as_runtime_observation_value(par) {
            Some(value) => out_values.push(value),
            None => {
                return Err(format!(
                    "drive OUT channel {:?} datum did not decode as a closed runtime \
                     observation value: {par:?}",
                    channels.out,
                ));
            },
        }
    }

    let fired_data = read_ground_from_runtime(&runtime, &channels.fired, par_verbatim).await;
    let err_data = read_ground_from_runtime(&runtime, &channels.err, par_verbatim).await;
    let fuel_data = read_ground_from_runtime(&runtime, &channels.fuel, par_verbatim).await;

    Ok(DriveObservationSet {
        out_values,
        fired_data,
        err_data,
        fuel_data,
    })
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

#[cfg(all(test, feature = "runtime-report"))]
mod tests {
    use super::*;
    use mettail_rholang_codegen::{reflect_ground_term_par, CollectionType, GroundTerm};
    use models::rust::utils::{new_elist_par, new_gint_par, new_gstring_par};

    /// The R-1 ABI round-trip (no Rho machine): reflecting a ground constructor
    /// term and decoding it back through the public observation entry point
    /// reconstructs the exact structural `Term`. This is the decoder counterpart
    /// of codegen's `reflect_ground_term_par_reflects_ground_pair_to_tagged_elist`.
    #[test]
    fn reflect_then_decode_round_trips_ground_pair() {
        let fp = "mettail-langdef-v1:0011223344556677";
        // Pair(B, A) over nullary A, B — the Swap→Pair demo's normal form.
        let pair =
            GroundTerm::new("Pair", vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")]);
        let par = reflect_ground_term_par(&pair, fp);

        let decoded = par_as_runtime_observation_value(&par)
            .expect("a reflected ground term must decode to a structural Term");
        assert_eq!(
            decoded,
            RuntimeObservationValue::Term {
                constructor: "Pair".to_string(),
                children: vec![
                    RuntimeObservationValue::Term {
                        constructor: "B".to_string(),
                        children: Vec::new(),
                    },
                    RuntimeObservationValue::Term {
                        constructor: "A".to_string(),
                        children: Vec::new(),
                    },
                ],
            }
        );
    }

    /// A nullary reflected term (a lone head tag, no children) decodes to a
    /// childless `Term`, and does NOT get misread as a 1-element list or a bag.
    #[test]
    fn reflect_then_decode_round_trips_nullary_constructor() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let par = reflect_ground_term_par(&GroundTerm::nullary("A"), fp);
        assert_eq!(
            par_as_runtime_observation_value(&par),
            Some(RuntimeObservationValue::Term {
                constructor: "A".to_string(),
                children: Vec::new(),
            })
        );
    }

    /// The reflected-term hook does not disturb the plain-list decode path: an
    /// `EList` whose head is an ordinary ground value (not a `mettail.term.`
    /// private name) still decodes as a `List`.
    #[test]
    fn plain_list_is_not_misread_as_a_reflected_term() {
        let list = new_elist_par(
            vec![
                new_gint_par(1, Vec::new(), false),
                new_gstring_par("two".to_string(), Vec::new(), false),
            ],
            Vec::new(),
            false,
            None,
            Vec::new(),
            false,
        );
        assert_eq!(
            par_as_runtime_observation_value(&list),
            Some(RuntimeObservationValue::List(vec![
                RuntimeObservationValue::Int(1),
                RuntimeObservationValue::Text("two".to_string()),
            ]))
        );
    }

    /// Stage AC2b: the AC bag-carrier round-trip. A `HashBag` ground term reflects to the
    /// process-soup carrier (`@"ac:{op}"!(⟦e⟧) | …`, via `reflect_ac_bag_par`), the SAME shape a
    /// bag-VALUED AC RHS lands on OUT as. Decoding it through the public observation entry point
    /// reconstructs the multiset `Bag`, elements decoded recursively (so `Wrap(A)` is a nested
    /// `Term`). This is the decoder counterpart of `reflect_hashbag_soup_par`.
    #[test]
    fn reflect_then_decode_round_trips_hashbag_soup() {
        let fp = "mettail-langdef-v1:0011223344556677";
        // PPar{Wrap(A), B, C} — a transformed bag: one wrapped element + two bare elements.
        let bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![
                GroundTerm::new("Wrap", vec![GroundTerm::nullary("A")]),
                GroundTerm::nullary("B"),
                GroundTerm::nullary("C"),
            ],
        );
        let soup = reflect_ground_term_par(&bag, fp);
        // A HashBag reflects to a bare sends-only soup (not a tagged EList head).
        assert!(
            soup.exprs.is_empty() && soup.sends.len() == 3,
            "a HashBag reflects to a bare 3-send soup, got {soup:?}"
        );

        let decoded = par_as_runtime_observation_value(&soup)
            .expect("the AC bag-carrier soup must decode to a Bag");
        let term = |constructor: &str, children: Vec<RuntimeObservationValue>| {
            RuntimeObservationValue::Term {
                constructor: constructor.to_string(),
                children,
            }
        };
        let mut expected = vec![
            (term("Wrap", vec![term("A", Vec::new())]), 1usize),
            (term("B", Vec::new()), 1),
            (term("C", Vec::new()), 1),
        ];
        expected.sort();
        assert_eq!(
            decoded,
            RuntimeObservationValue::Bag(expected),
            "the soup decodes to the transformed-bag multiset"
        );
    }

    /// A multiplicity > 1 bag `PPar{A, A, B}` decodes to a multiset with the correct counts —
    /// the soup carrier is multiplicity-preserving (one send per element).
    #[test]
    fn ac_bag_soup_decode_preserves_multiplicity() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        );
        let soup = reflect_ground_term_par(&bag, fp);
        let term = |constructor: &str| RuntimeObservationValue::Term {
            constructor: constructor.to_string(),
            children: Vec::new(),
        };
        let mut expected = vec![(term("A"), 2usize), (term("B"), 1)];
        expected.sort();
        assert_eq!(
            par_as_runtime_observation_value(&soup),
            Some(RuntimeObservationValue::Bag(expected)),
            "duplicate elements accumulate multiplicity in the decoded bag"
        );
    }
}
