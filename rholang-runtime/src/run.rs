//! Run a lowered-MeTTaIL Rholang program on a real in-memory f1r3node-rust
//! `RhoRuntime` and read ground results back — the M-RHO.0.5 execution path and
//! the substrate of the M-RHO.0.4 differential oracle.
//!
//! No disk / RocksDB / network: the runtime is backed by `InMemoryStoreManager`
//! (pure `DashMap`). Threading/scheduling are f1r3node's (RSpace + the reducer);
//! MeTTaIL only emits the `Par` program and reads the resting data.

use std::collections::HashMap;
use std::sync::Arc;

use crate::guard_par_substrate::{GuardRefusalLedger, SubstrateGuardMatcher};
use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_rholang_codegen::ValidatedRhoProgram;
// The decoder and the refusal-reporting helper are unconditional: both are used by the minimal
// runtime surface as well as by `runtime-report` adapters.
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{BindPattern, Expr, ListParWithRandom, Par, TaggedContinuation};
#[cfg(feature = "source-oracle")]
use models::rust::utils::new_freevar_par;

/// The `Par` → [`RuntimeObservationValue`] inverse, re-exported from its own module so every
/// existing call site — and [`crate`]'s public surface — is unchanged by the extraction.
///
/// It moved to [`crate::observation`] because it had to become **unconditional**: the `[*]`
/// request server renders `Par`s into data it `produce`s onto the live tuplespace, and a
/// feature-gated decoder there would mean two builds writing different bytes for one deploy.
/// See that module's header.
pub use crate::observation::par_as_runtime_observation_value;

use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};
use rholang::rust::interpreter::system_processes::Definition;

use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

/// A quoted-name channel `@"<name>"` (a `Par` holding a single `GString`).
pub(crate) fn quoted_channel(name: &str) -> Par {
    let mut par = Par::default();
    par.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::GString(name.to_string())),
    }];
    par
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
///
/// Gated to match its **only** caller, `backend::run_rho_invocation_blocking`, which is
/// `#[cfg(feature = "runtime-report")]`. Without the gate this is dead code in a
/// `--no-default-features` build — invisible until that configuration was made to compile at
/// all (see [`par_verbatim`]). `take_pending_fold_definitions` stays ungated: `build_runtime`
/// drains the slot in every configuration, and finding it empty is the correct behaviour when
/// nothing can fill it.
#[cfg(feature = "runtime-report")]
pub(crate) fn set_pending_fold_definitions(definitions: Vec<Definition>) {
    PENDING_FOLD_DEFINITIONS.with(|cell| *cell.borrow_mut() = definitions);
}

/// Take (and clear) the pending held-fold contract `Definition`s for this thread.
fn take_pending_fold_definitions() -> Vec<Definition> {
    PENDING_FOLD_DEFINITIONS.with(|cell| std::mem::take(&mut *cell.borrow_mut()))
}

/// Build an in-memory `RhoRuntime`, and hand back the **guard-refusal ledger** its
/// `SubstrateGuardMatcher` writes into.
///
/// ★ The ledger is returned rather than kept private because a `where` guard the substrate
/// cannot DECIDE has nowhere else to go: `Match::check_commit` answers a `bool`, so the decider
/// physically cannot raise, and without a driver that reads this ledger an undecidable guard
/// blocks a COMM in total silence — indistinguishable from a guard that was evaluated and
/// refuted. See [`crate::guard_par_substrate::GuardRefusalLedger`].
async fn build_runtime() -> Result<(impl RhoRuntime, GuardRefusalLedger), String> {
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
) -> Result<(impl RhoRuntime, GuardRefusalLedger), String> {
    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .map_err(|e| format!("in-mem store: {e:?}"))?;
    // ★ THE `where` → Dovetail/SFT WIRE, run-time half. `RSpace::create` takes the `Match` trait
    // object that will decide every `where` guard at COMM time (`space_matcher.rs` →
    // `Match::check_commit`), so the decider is chosen HERE, by whoever constructs the space —
    // no f1r3node change. `SubstrateGuardMatcher` delegates `get` to f1r3node's `Matcher`
    // verbatim (spatial matching is untouched) and decides `check_commit` with the substrate.
    let guards = SubstrateGuardMatcher::new();
    // The handle is taken BEFORE the decider is boxed into the space, which is the only moment
    // it is reachable: `RSpace` keeps an `Arc<Box<dyn Match<…>>>` and the trait exposes no way
    // back to the concrete type.
    let refusals = guards.refusals();
    let space: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> =
        RSpace::create(store, Arc::new(Box::new(guards))).map_err(|e| format!("rspace: {e:?}"))?;

    Ok((
        create_rho_runtime(
            space,
            Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
            false,                    // init_registry: not needed for pure arithmetic
            &mut extra_system_processes, // held-fold + native-handler contracts (usually none)
            ExternalServices::noop(), // inert — no ChromaDB/SBERT/OpenAI
        )
        .await,
        refusals,
    ))
}

/// Evaluate Rholang source, then **raise on any guard the substrate could not decide**.
///
/// The second half is not an add-on. A `where` guard that reaches
/// [`GuardRefusalClass::DeciderGap`](crate::guard_par_substrate::GuardRefusalClass::DeciderGap)
/// blocked a COMM without ever being decided, and before this call existed the program compiled,
/// ran, exited cleanly, admitted nothing and reported nothing — the same observation a guard
/// that was evaluated and refuted produces.
#[cfg(feature = "source-oracle")]
async fn eval_on_runtime<R: RhoRuntime>(
    runtime: &mut R,
    program: &str,
    refusals: &GuardRefusalLedger,
) -> Result<(), String> {
    eval_on_runtime_unchecked(runtime, program).await?;
    refusals.refuse_decider_gaps()
}

/// [`eval_on_runtime`] without the guard-refusal check, for the callers that report the refusals
/// themselves alongside the tuplespace readings — see
/// [`run_rholang_source_and_read_ints_with_guard_refusals`].
#[cfg(feature = "source-oracle")]
async fn eval_on_runtime_unchecked<R: RhoRuntime>(
    runtime: &mut R,
    program: &str,
) -> Result<(), String> {
    let result = runtime
        .evaluate_with_term(program)
        .await
        .map_err(|e| format!("evaluate: {e:?}"))?;
    if !result.errors.is_empty() {
        return Err(format!("evaluation errors: {:?}", result.errors));
    }
    Ok(())
}

/// The domain separator for [`deploy_rand`]. Its only job is to make an interpreter seed
/// impossible to confuse with a deploy-envelope seed, whose preimage is a `DeployDataProto`.
const INTERPRETER_RAND_DOMAIN: &[u8] = b"mettail.rholang-runtime.inj.v1";

/// The injection randomness, **derived from the program** rather than drawn from OS entropy.
///
/// ## Why this is not `Blake2b512Random::create_from_length(128)`
///
/// That constructor's name reads like a fixed-width seed. It is not: `crypto`'s
/// `create_from_length` fills its buffer with `rand::thread_rng()`, i.e. **fresh OS entropy per
/// process**. This was the crate's only entropy-seeded injection — [`crate::step`] and the
/// bench harnesses all use `create_from_bytes` with a constant — and it made the interpreter's
/// own output irreproducible in a way that took a renderer fix to become visible.
///
/// The chain, because it is six links long and none of them is obvious:
///
/// 1. the seed is split positionally across the injected program's data;
/// 2. every staged datum carries a `random_state` derived from it;
/// 3. `models`' `event_hash_bytes_list_par_with_random` **hashes `random_state` into** the
///    `Produce` / `Consume` event hashes;
/// 4. `speculation::RendezvousName::of` copies exactly those hashes;
/// 5. [`speculation::delivery::step_digest`](crate::speculation::delivery::step_digest) folds
///    them, and `trace_digest` folds the step digests;
/// 6. so a `^spec-success` / `^spec-failure` / `^spec-truncated` entry — and every FIPS
///    collection — carried a fresh random value on every run.
///
/// Measured before the fix: twenty runs of `demos/flt-lookahead/04-divergence.rho` produced
/// **twenty distinct trace digests, zero repeats**, which is the entropy signature and not the
/// small-permutation signature a scheduling or iteration-order cause would give.
///
/// ## Why a content hash, and why domain-separated
///
/// This mirrors what the **on-chain** path already does — `casper`'s `Tools::unforgeable_name_rng`
/// seeds from `DeployDataProto{deployer, timestamp, …}.encode_to_vec()`, both consensus-visible —
/// so the interpreter now has the reproducibility property a validator already had, by the same
/// mechanism rather than by accident.
///
/// The cost is that unforgeable names become predictable from the source. On chain they already
/// are (from a public key and a timestamp); here there is no adversary and no chain. The domain
/// tag is what keeps the two preimage spaces disjoint regardless.
fn deploy_rand(program: &Par) -> Blake2b512Random {
    use prost::Message;
    let mut preimage = Vec::with_capacity(INTERPRETER_RAND_DOMAIN.len() + program.encoded_len());
    preimage.extend_from_slice(INTERPRETER_RAND_DOMAIN);
    program
        .encode(&mut preimage)
        .expect("encoding a Par into a Vec cannot fail");
    let digest = rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash::new(&preimage);
    Blake2b512Random::create_from_bytes(digest.bytes().as_slice())
}

async fn inj_on_runtime<R: RhoRuntime>(
    runtime: &mut R,
    program: Par,
    refusals: &GuardRefusalLedger,
) -> Result<(), String> {
    inj_on_runtime_unchecked(runtime, program).await?;
    refusals.refuse_decider_gaps()
}

/// [`inj_on_runtime`] without the guard-refusal check.
///
/// ⚠ **The reduction is NOT rolled back when a guard is refused**, and that is deliberate. The
/// refusal reports a decision that was never *made*; it is not a failed mutation. The space is
/// exactly what the program produced — in particular the datum the undecidable guard declined to
/// consume is still resting and still observable — which is the whole separation being reported:
///
/// ```text
///   guard FALSE       → no error, rests
///   guard UNDECIDABLE → error raised, rests   ← same space, different report
/// ```
///
/// Reverting would erase the second column of that table. An `inj` **error** still reverts, as
/// it always did, because that is a genuinely partial mutation.
async fn inj_on_runtime_unchecked<R: RhoRuntime>(
    runtime: &mut R,
    program: Par,
) -> Result<(), String> {
    let checkpoint = runtime.create_soft_checkpoint().await;
    let rand = deploy_rand(&program);
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
    let (mut runtime, refusals) = build_runtime().await?;
    eval_on_runtime(&mut runtime, program, &refusals).await?;
    Ok(runtime)
}

async fn evaluate_par(program: &Par) -> Result<impl RhoRuntime, String> {
    let (mut runtime, refusals) = build_runtime().await?;
    inj_on_runtime(&mut runtime, program.clone(), &refusals).await?;
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
        let (mut runtime, refusals) = build_runtime_with_definitions(definitions).await?;
        inj_on_runtime(&mut runtime, composed, &refusals).await?;
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

#[cfg(feature = "runtime-report")]
impl DriveObservationChannels {
    /// The channel set of one language's drive execution: `out` as given, the three
    /// observation names derived from the language fingerprint by the codegen naming
    /// helpers — BYTE-COHERENT with the names the installed `^drive` receiver family
    /// emits on (both sides call the same `drive_*_channel` functions).
    pub fn for_fingerprint(language_fingerprint: &str, out: impl Into<String>) -> Self {
        Self {
            out: out.into(),
            fired: mettail_rholang_codegen::drive_fired_channel(language_fingerprint),
            err: mettail_rholang_codegen::drive_err_channel(language_fingerprint),
            fuel: mettail_rholang_codegen::drive_fuel_channel(language_fingerprint),
        }
    }

    /// The channel set of one generated drive invocation
    /// ([`mettail_rholang_codegen::RhoNetDriveInvocation`]) — carries the invocation's
    /// four channel names verbatim.
    pub fn from_invocation(invocation: &mettail_rholang_codegen::RhoNetDriveInvocation) -> Self {
        Self {
            out: invocation.out_channel.clone(),
            fired: invocation.fired_channel.clone(),
            err: invocation.err_channel.clone(),
            fuel: invocation.fuel_channel.clone(),
        }
    }
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
///
/// ★ UNGATED, correcting a pre-existing mismatch found while extracting
/// [`crate::observation`]: this was `#[cfg(feature = "runtime-report")]` while
/// [`run_normalized_par_for_oracle_and_read_par_channels`] — one of its callers, and a
/// member of the crate's UNCONDITIONAL public surface — was not, so
/// `cargo check -p rholang-runtime --no-default-features` did not compile. The function
/// itself has no `runtime-report` dependency whatsoever; it is one `clone`.
fn par_verbatim(par: &Par) -> Option<Par> {
    Some(par.clone())
}

/// A typed violation of the ALWAYS-ON drive cross-check (A-S5.2, plan v2 §4.7)
/// — each variant names the observation channel it was found on.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq)]
pub enum DriveCrossCheckError {
    /// The typed fail-close channel `^drive-err:{fp}` is non-empty: the driver
    /// met an unrecognized head.
    ErrChannel {
        /// The err channel name.
        channel: String,
        /// The number of resting error data.
        count: usize,
    },
    /// The fuel channel `^drive-fuel:{fp}` is non-empty: some firing path
    /// exhausted its per-path bound. The report carries BOTH bounds (plan v2
    /// §4.2 / F10, AM-5 wording): the per-path fuel the seed threaded and the
    /// GLOBAL fired count the ledger recorded.
    FuelChannel {
        /// The fuel channel name.
        channel: String,
        /// The number of resting exhaustion data.
        count: usize,
        /// The per-path fuel bound the seed threaded.
        per_path_fuel: i64,
        /// The global fired count read from the ledger.
        global_fired: usize,
    },
    /// OUT did not rest exactly one value (a quiescent drive publishes exactly
    /// its resting term).
    OutCount {
        /// The OUT channel name.
        channel: String,
        /// The observed OUT value count.
        count: usize,
    },
    /// The host NF-scan (the static mirror of the driver's redex arms) found a
    /// redex in an OUT value — the driver claimed quiescence on a non-normal
    /// term.
    OutNotNormal {
        /// The OUT channel name.
        channel: String,
        /// The offending decoded value.
        value: RuntimeObservationValue,
    },
    /// A firing-ledger datum did not decode as a GString rule label.
    LedgerDecode {
        /// The ledger channel name.
        channel: String,
        /// The decode failure detail.
        detail: String,
    },
    /// Ledger consistency violated: `fired ≥ 1 ⟺ the subject had a redex`.
    Ledger {
        /// The ledger channel name.
        channel: String,
        /// The global fired count.
        fired_count: usize,
        /// Whether the subject had a redex (the host-side scan of the SUBJECT).
        subject_had_redex: bool,
    },
}

#[cfg(feature = "runtime-report")]
impl std::fmt::Display for DriveCrossCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DriveCrossCheckError::ErrChannel { channel, count } => write!(
                f,
                "drive cross-check: the typed error channel {channel:?} holds {count} datum(s) \
                 — the driver met an unrecognized head"
            ),
            DriveCrossCheckError::FuelChannel {
                channel,
                count,
                per_path_fuel,
                global_fired,
            } => write!(
                f,
                "drive cross-check: fuel exhausted — channel {channel:?} holds {count} \
                 exhaustion datum(s) after the per-path bound of {per_path_fuel} firing(s) \
                 along some causal chain; the ledger records {global_fired} firing(s) globally"
            ),
            DriveCrossCheckError::OutCount { channel, count } => write!(
                f,
                "drive cross-check: OUT channel {channel:?} rests {count} value(s) — a \
                 quiescent drive publishes exactly one resting term"
            ),
            DriveCrossCheckError::OutNotNormal { channel, value } => write!(
                f,
                "drive cross-check: OUT channel {channel:?} rests a NON-NORMAL term (the host \
                 redex scan found a redex): {value:?}"
            ),
            DriveCrossCheckError::LedgerDecode { channel, detail } => write!(
                f,
                "drive cross-check: firing-ledger channel {channel:?} datum did not decode: \
                 {detail}"
            ),
            DriveCrossCheckError::Ledger { channel, fired_count, subject_had_redex } => write!(
                f,
                "drive cross-check: ledger channel {channel:?} consistency violated — \
                 fired_count = {fired_count} but subject_had_redex = {subject_had_redex} \
                 (fired ≥ 1 ⟺ the subject had a redex)"
            ),
        }
    }
}

#[cfg(feature = "runtime-report")]
impl std::error::Error for DriveCrossCheckError {}

/// The ALWAYS-ON fired-vs-observed drive cross-check (A-S5.2, plan v2 §4.7),
/// over one decoded [`DriveObservationSet`]:
///
/// 1. the typed `^drive-err` channel is EMPTY;
/// 2. the `^drive-fuel` channel is EMPTY (violation reports BOTH the per-path
///    bound and the ledger's global fired count — F10/AM-5 wording);
/// 3. OUT rests exactly ONE value, and the host NF-scan — `redex_scan`, the
///    static host mirror of the driver's redex arms over the decoded term (a
///    predicate, no evaluation; for Lambda no flattening is needed) — finds NO
///    redex in it;
/// 4. ledger consistency: `fired ≥ 1 ⟺ subject_had_redex` (the caller scans
///    the SUBJECT with the same mirror).
///
/// Consumed by the driver firing tests now and by the A-S5.6 exec path. Every
/// violation is a typed [`DriveCrossCheckError`] naming the channel.
#[cfg(feature = "runtime-report")]
pub fn drive_cross_check(
    set: &DriveObservationSet,
    channels: &DriveObservationChannels,
    subject_had_redex: bool,
    per_path_fuel: i64,
    redex_scan: &dyn Fn(&RuntimeObservationValue) -> bool,
) -> Result<(), DriveCrossCheckError> {
    if !set.err_data.is_empty() {
        return Err(DriveCrossCheckError::ErrChannel {
            channel: channels.err.clone(),
            count: set.err_data.len(),
        });
    }
    if !set.fuel_data.is_empty() {
        let global_fired = set.fired_data.len();
        return Err(DriveCrossCheckError::FuelChannel {
            channel: channels.fuel.clone(),
            count: set.fuel_data.len(),
            per_path_fuel,
            global_fired,
        });
    }
    if set.out_values.len() != 1 {
        return Err(DriveCrossCheckError::OutCount {
            channel: channels.out.clone(),
            count: set.out_values.len(),
        });
    }
    for value in &set.out_values {
        if redex_scan(value) {
            return Err(DriveCrossCheckError::OutNotNormal {
                channel: channels.out.clone(),
                value: value.clone(),
            });
        }
    }
    let fired = set
        .fired_labels()
        .map_err(|detail| DriveCrossCheckError::LedgerDecode {
            channel: channels.fired.clone(),
            detail,
        })?;
    if (!fired.is_empty()) != subject_had_redex {
        return Err(DriveCrossCheckError::Ledger {
            channel: channels.fired.clone(),
            fired_count: fired.len(),
            subject_had_redex,
        });
    }
    Ok(())
}

/// The host mirror of a BINDER-APPLY β redex arm over a decoded observation
/// value (A-S5.2, plan v2 §4.7): `true` iff a node
/// `apply_label(^lambda(_), _)` is present anywhere in the term — the static
/// NF-scan predicate for a Lambda-shaped language (`apply_label = "App"`), with
/// the reflected-binder constructor name fixed by the reflection ABI
/// (`^lambda`). The explicit DFS visits every structured observation shape;
/// scalar leaves carry no redex.
#[cfg(feature = "runtime-report")]
pub fn binder_apply_redex_present(apply_label: &str, value: &RuntimeObservationValue) -> bool {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            RuntimeObservationValue::Term { constructor, children } => {
                if constructor == apply_label
                    && matches!(
                        children.first(),
                        Some(RuntimeObservationValue::Term { constructor, .. })
                            if constructor == "^lambda"
                    )
                {
                    return true;
                }
                work.extend(children.iter().rev());
            },
            RuntimeObservationValue::List(items)
            | RuntimeObservationValue::Tuple(items)
            | RuntimeObservationValue::Set(items) => work.extend(items.iter().rev()),
            RuntimeObservationValue::Bag(entries) => {
                work.extend(entries.iter().rev().map(|(value, _)| value));
            },
            RuntimeObservationValue::Map(entries) => {
                for (key, value) in entries.iter().rev() {
                    work.push(value);
                    work.push(key);
                }
            },
            _ => {},
        }
    }
    false
}

/// The host value-level flatten over a decoded observation value — the mirror of the
/// host's `add_flattened_bag` (`dovetail/src/rules.rs:707` semantics: splice any bag
/// member that is itself a bag, multiplicity-preserving; driver values are trees, so no
/// cycle guard is needed) — plan v2 §4.7's canonicalization step. One splice level per
/// recursion suffices because the recursion flattens each member BEFORE splicing
/// (identical to the A-S5.5 test-tier mirror it is promoted from,
/// `rho_net_ambient_full.rs`).
///
/// A-S5.6: promoted into the runtime so the PRODUCTION exec cross-check (the
/// [`crate::RhoMachineInvocation`] drive arm) and the test tier share one flatten.
#[cfg(feature = "runtime-report")]
pub fn flatten_observation_value(value: &RuntimeObservationValue) -> RuntimeObservationValue {
    enum Work<'a> {
        Visit(&'a RuntimeObservationValue),
        Bag {
            entries: &'a [(RuntimeObservationValue, usize)],
            index: usize,
            value_base: usize,
        },
        Term {
            constructor: &'a str,
            children: &'a [RuntimeObservationValue],
            index: usize,
            value_base: usize,
        },
    }

    let mut work = vec![Work::Visit(value)];
    let mut values = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            Work::Visit(value) => match value {
                RuntimeObservationValue::Bag(entries) if !entries.is_empty() => {
                    let value_base = values.len();
                    work.push(Work::Bag { entries, index: 0, value_base });
                    work.push(Work::Visit(&entries[0].0));
                },
                RuntimeObservationValue::Bag(_) => {
                    values.push(RuntimeObservationValue::Bag(Vec::new()));
                },
                RuntimeObservationValue::Term { constructor, children } if !children.is_empty() => {
                    let value_base = values.len();
                    work.push(Work::Term {
                        constructor,
                        children,
                        index: 0,
                        value_base,
                    });
                    work.push(Work::Visit(&children[0]));
                },
                RuntimeObservationValue::Term { constructor, .. } => {
                    values.push(RuntimeObservationValue::Term {
                        constructor: constructor.clone(),
                        children: Vec::new(),
                    });
                },
                other => values.push(other.clone()),
            },
            Work::Bag { entries, index, value_base } => {
                let next = index + 1;
                if next < entries.len() {
                    work.push(Work::Bag { entries, index: next, value_base });
                    work.push(Work::Visit(&entries[next].0));
                    continue;
                }

                let elements = values.split_off(value_base);
                let mut flat = Vec::with_capacity(entries.len());
                for (element, (_, count)) in elements.into_iter().zip(entries) {
                    for _ in 0..*count {
                        match &element {
                            RuntimeObservationValue::Bag(inner) => {
                                for (inner_element, inner_count) in inner {
                                    for _ in 0..*inner_count {
                                        flat.push((inner_element.clone(), 1));
                                    }
                                }
                            },
                            other => flat.push((other.clone(), 1)),
                        }
                    }
                }
                values.push(RuntimeObservationValue::Bag(flat));
            },
            Work::Term { constructor, children, index, value_base } => {
                let next = index + 1;
                if next < children.len() {
                    work.push(Work::Term {
                        constructor,
                        children,
                        index: next,
                        value_base,
                    });
                    work.push(Work::Visit(&children[next]));
                } else {
                    let children = values.split_off(value_base);
                    values.push(RuntimeObservationValue::Term {
                        constructor: constructor.to_owned(),
                        children,
                    });
                }
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("observation flatten PDA: missing root value")
}

/// The DATA-shaped host NF-scan of one drive-admitted language (A-S5.6, plan v2 §4.7 /
/// §6.1): the static mirror of the driver's redex-arm FAMILY over a decoded observation
/// value, carried inside the production drive invocation
/// ([`crate::RhoMachineInvocation::RunRhoNetDriveAndReadObservationSet`]) so the
/// always-on exec cross-check can run without language-specific closures. Two arm
/// families exist today, parameterized by their constructor labels (never by language
/// name):
///
/// * [`BinderApply`](Self::BinderApply) — the β family: `apply_label(^lambda(_), _)`
///   anywhere ([`binder_apply_redex_present`]; production `Lambda`, `apply_label =
///   "App"`).
/// * [`GuardedAcMobilityTrio`](Self::GuardedAcMobilityTrio) — the guarded AC mobility
///   family (C-G In/Out/Open with cross-level name-equality guards) over `HashBag` soups
///   (production `Ambient`) — the host mirror of ALL three driver redex arms, evaluated
///   over the FLATTENED term (plan v2 §4.7's canonicalization; the flatten is applied
///   inside [`redex_present`](Self::redex_present) so no caller can forget it).
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveNfScan {
    /// The β arm family: a redex is `apply_label(^lambda(_), _)` anywhere.
    BinderApply {
        /// The application constructor label (`"App"` for the production Lambda).
        apply_label: String,
    },
    /// The guarded AC mobility trio (C-G Red In / Red Out / Red Open shapes with their
    /// cross-level name-equality guards) over bag soups.
    GuardedAcMobilityTrio {
        /// The ambient/membrane constructor label (`"PAmb"`).
        amb_label: String,
        /// The `in` capability constructor label (`"PIn"`).
        in_label: String,
        /// The `out` capability constructor label (`"POut"`).
        out_label: String,
        /// The `open` capability constructor label (`"POpen"`).
        open_label: String,
    },
}

#[cfg(feature = "runtime-report")]
impl DriveNfScan {
    /// `true` iff the language's static redex mirror finds a redex anywhere in `value`.
    /// The value is FLATTENED first (plan v2 §4.7: the NF-scan runs over the
    /// canonicalized, flattened term; a no-op for bag-free languages).
    pub fn redex_present(&self, value: &RuntimeObservationValue) -> bool {
        let canonical = flatten_observation_value(value);
        match self {
            DriveNfScan::BinderApply { apply_label } => {
                binder_apply_redex_present(apply_label, &canonical)
            },
            DriveNfScan::GuardedAcMobilityTrio {
                amb_label,
                in_label,
                out_label,
                open_label,
            } => guarded_ac_trio_redex_present(
                amb_label, in_label, out_label, open_label, &canonical,
            ),
        }
    }
}

/// The bag elements of a decoded value, multiplicity-expanded, or `None` when the value
/// is not a bag.
#[cfg(feature = "runtime-report")]
fn observation_bag_elements(
    value: &RuntimeObservationValue,
) -> Option<impl Iterator<Item = &RuntimeObservationValue> + Clone> {
    match value {
        RuntimeObservationValue::Bag(entries) => Some(
            entries
                .iter()
                .flat_map(|(element, count)| std::iter::repeat_n(element, *count)),
        ),
        _ => None,
    }
}

/// The guarded-AC-mobility-trio redex scan over an (already flattened) decoded value —
/// the host mirror of the three driver redex arms, guards included (A-S5.6; the boolean
/// projection of the A-S5.5 test-tier rule mirrors in `rho_net_ambient_full.rs`):
///
/// * **Open**: some top-level bag holds `open_label(n, _)` and a SIBLING `amb_label(n, _)`
///   with the SAME name `n` (decoded-value equality — `^free` atoms compare by content).
/// * **In**: some top-level bag holds `amb_label(n, body)` whose bag body holds
///   `in_label(m, _)`, and a SIBLING `amb_label(m, _)`.
/// * **Out**: some node is `amb_label(m, body)` whose bag body holds `amb_label(n, inner)`
///   whose bag `inner` holds `out_label(m, _)` — the single-rooted (Red Out) shape.
///
/// The explicit DFS visits every structured observation shape, so under-binder (`^lambda`)
/// and nested-membrane redexes are found wherever the driver's descent arms would reach them.
#[cfg(feature = "runtime-report")]
fn guarded_ac_trio_redex_present(
    amb_label: &str,
    in_label: &str,
    out_label: &str,
    open_label: &str,
    value: &RuntimeObservationValue,
) -> bool {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        // (Out) — single-rooted at an ambient node.
        if let RuntimeObservationValue::Term { constructor, children } = value {
            if constructor == amb_label && children.len() == 2 {
                let outer_name = &children[0];
                if let Some(body) = observation_bag_elements(&children[1]) {
                    for element in body {
                        let RuntimeObservationValue::Term { constructor, children } = element
                        else {
                            continue;
                        };
                        if constructor != amb_label || children.len() != 2 {
                            continue;
                        }
                        let Some(mut inner) = observation_bag_elements(&children[1]) else {
                            continue;
                        };
                        let out_here = inner.any(|inner_element| {
                            matches!(
                                inner_element,
                                RuntimeObservationValue::Term { constructor, children }
                                    if constructor == out_label
                                        && children.first() == Some(outer_name)
                            )
                        });
                        if out_here {
                            return true;
                        }
                    }
                }
            }
        }
        // (Open) + (In) — pair-rooted at a bag's top level.
        if let Some(elements) = observation_bag_elements(value) {
            for (index, element) in elements.clone().enumerate() {
                let RuntimeObservationValue::Term { constructor, children } = element else {
                    continue;
                };
                let sibling_amb_named = |name: &RuntimeObservationValue| {
                    elements.clone().enumerate().any(|(sibling_index, sibling)| {
                        sibling_index != index
                            && matches!(
                                sibling,
                                RuntimeObservationValue::Term { constructor, children }
                                    if constructor == amb_label && children.first() == Some(name)
                            )
                    })
                };
                // (Open): open(n, _) beside n[_].
                if constructor == open_label
                    && children.len() == 2
                    && sibling_amb_named(&children[0])
                {
                    return true;
                }
                // (In): n[{in(m, _), …}] beside m[_].
                if constructor == amb_label && children.len() == 2 {
                    if let Some(mut body) = observation_bag_elements(&children[1]) {
                        let in_fires = body.any(|body_element| {
                            matches!(
                                body_element,
                                RuntimeObservationValue::Term { constructor, children }
                                    if constructor == in_label
                                        && children.len() == 2
                                        && sibling_amb_named(&children[0])
                            )
                        });
                        if in_fires {
                            return true;
                        }
                    }
                }
            }
        }
        // Congruence descent — every structured child position, in the recursive
        // oracle's original left-to-right depth-first order.
        match value {
            RuntimeObservationValue::Term { children, .. } => {
                work.extend(children.iter().rev());
            },
            RuntimeObservationValue::List(items)
            | RuntimeObservationValue::Tuple(items)
            | RuntimeObservationValue::Set(items) => work.extend(items.iter().rev()),
            RuntimeObservationValue::Bag(entries) => {
                work.extend(entries.iter().rev().map(|(element, _)| element));
            },
            RuntimeObservationValue::Map(entries) => {
                for (key, value) in entries.iter().rev() {
                    work.push(value);
                    work.push(key);
                }
            },
            _ => {},
        }
    }
    false
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
async fn read_drive_observation_set<R: RhoRuntime>(
    runtime: &R,
    channels: &DriveObservationChannels,
) -> Result<DriveObservationSet, String> {
    let out_raw = read_ground_from_runtime(runtime, &channels.out, par_verbatim).await;
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

    let fired_data = read_ground_from_runtime(runtime, &channels.fired, par_verbatim).await;
    let err_data = read_ground_from_runtime(runtime, &channels.err, par_verbatim).await;
    let fuel_data = read_ground_from_runtime(runtime, &channels.fuel, par_verbatim).await;

    Ok(DriveObservationSet {
        out_values,
        fired_data,
        err_data,
        fuel_data,
    })
}

#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_and_read_observation_set(
    installed_program: &Par,
    call: &Par,
    channels: &DriveObservationChannels,
) -> Result<DriveObservationSet, String> {
    let mut sets = run_installed_program_with_call_and_read_observation_sets(
        installed_program,
        call,
        std::slice::from_ref(channels),
    )
    .await?;
    Ok(sets
        .pop()
        .expect("one requested drive observation channel set yields one result"))
}

/// Execute one co-installed driver network once and read each language's disjoint
/// firing/error/fuel ledger from that same RSpace state. Results preserve `channels`
/// order. Sharing the execution is load-bearing: evaluating once per fingerprint would
/// not prove that the drivers coexist or partition one mixed reduction.
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_and_read_observation_sets(
    installed_program: &Par,
    call: &Par,
    channels: &[DriveObservationChannels],
) -> Result<Vec<DriveObservationSet>, String> {
    let composed = installed_program.append(call.clone());
    let runtime = evaluate_par(&composed).await?;
    let mut sets = Vec::with_capacity(channels.len());
    for channel_set in channels {
        sets.push(read_drive_observation_set(&runtime, channel_set).await?);
    }
    Ok(sets)
}

/// Execute one co-installed driver network with the complete set of generated
/// language-scoped system-process definitions, then read every fingerprint-disjoint
/// observation ledger from the same RSpace state.
///
/// Co-installation must install the union of the participating languages' definitions:
/// omitting (for example) Ambient's native shift definition leaves a generated carrier
/// call resting forever and makes a valid driver appear non-terminating.  The definitions
/// are supplied explicitly so one evaluation cannot accidentally consume only one
/// thread-local language registration.
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_definitions_and_read_observation_sets(
    installed_program: &Par,
    call: &Par,
    definitions: Vec<Definition>,
    channels: &[DriveObservationChannels],
) -> Result<Vec<DriveObservationSet>, String> {
    let composed = installed_program.append(call.clone());
    let runtime = {
        let (mut runtime, refusals) = build_runtime_with_definitions(definitions).await?;
        inj_on_runtime(&mut runtime, composed, &refusals).await?;
        runtime
    };
    let mut sets = Vec::with_capacity(channels.len());
    for channel_set in channels {
        sets.push(read_drive_observation_set(&runtime, channel_set).await?);
    }
    Ok(sets)
}

/// [`run_installed_program_with_call_and_read_observation_set`] with explicit injected
/// system-process definitions. This is the direct-test/debug seam for a drive program whose
/// generated carrier calls the native shift contract; production threads the same Definition
/// through the invocation compiler's pending-definition bracket.
#[cfg(feature = "runtime-report")]
pub async fn run_installed_program_with_call_definitions_and_read_observation_set(
    installed_program: &Par,
    call: &Par,
    definitions: Vec<Definition>,
    channels: &DriveObservationChannels,
) -> Result<DriveObservationSet, String> {
    let mut sets = run_installed_program_with_call_definitions_and_read_observation_sets(
        installed_program,
        call,
        definitions,
        std::slice::from_ref(channels),
    )
    .await?;
    Ok(sets
        .pop()
        .expect("one requested drive observation channel set yields one result"))
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
/// each requested quoted channel — from ONE execution.
///
/// The multi-channel twin of
/// [`run_normalized_par_for_oracle_and_read_runtime_values`], and the
/// `RuntimeObservationValue` twin of
/// [`run_normalized_par_for_oracle_and_read_string_channels`]. It reads the full
/// typed observation rather than one ground carrier, so a single call can report
/// a `Bool` verdict on one channel and a `Text`/`BigIntBytes` datum on another.
///
/// Reading SEVERAL channels from ONE execution is what makes a guard-FAILURE
/// assertion possible at all: "the body did not fire" (`@"OUT"` empty) and "the
/// rejected datum is still resting" (`@"c"` still holds it) are two facts about
/// the SAME quiescent store. Observing them in two separate runs would establish
/// each separately but never that they hold TOGETHER — which is precisely the
/// content of the fail-shut contract (`GuardedCommSoundness.v`).
#[cfg(feature = "runtime-report")]
pub async fn run_normalized_par_for_oracle_and_read_runtime_value_channels(
    program: &Par,
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<RuntimeObservationValue>>, String> {
    let runtime = evaluate_par(program).await?;
    let mut result = HashMap::with_capacity(out_channels.len());
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_runtime_observation_value).await,
        );
    }
    Ok(result)
}

/// ★ [`run_normalized_par_for_oracle_and_read_runtime_value_channels`] reporting the `where`
/// guards the substrate could not decide **alongside** the readings, instead of raising on them.
///
/// The `Par`-path twin of [`run_rholang_source_and_read_ints_with_guard_refusals`], and it exists
/// for the same reason: a run whose guard was refused still has a tuplespace, and for the rows
/// that matter — a guard that blocked without being decided — the tuplespace is *identical* to
/// the one a refuted guard leaves. Only the refusal column separates them, so a caller that
/// needs both has to be able to get both.
pub async fn run_normalized_par_and_read_runtime_value_channels_with_guard_refusals(
    program: &Par,
    out_channels: &[&str],
) -> Result<(HashMap<String, Vec<RuntimeObservationValue>>, Vec<String>), String> {
    let (mut runtime, refusals) = build_runtime().await?;
    inj_on_runtime_unchecked(&mut runtime, program.clone()).await?;

    let mut result = HashMap::with_capacity(out_channels.len());
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_runtime_observation_value).await,
        );
    }
    let reported = refusals
        .take()
        .iter()
        .map(|refusal| refusal.to_string())
        .collect();
    Ok((result, reported))
}

/// **Run `program` with the `[*]` / `[n]` request server installed**, and read back every
/// requested quoted channel VERBATIM from the one quiescent store.
///
/// This is the entry a lookahead-bearing program needs, and the only one: without the two
/// `^spec-*` system processes a `[*]` request has nothing to consume it, so it rests and
/// `crate::lookahead::unserved_requests` reports it. The reads are verbatim `Par`s because a
/// speculative result is an arbitrary datum — a reflected foreign term, an `ESet` of
/// `EList`s, a reified process — and every typed reader FILTERS, which would turn "the
/// engine delivered something I cannot decode" into "the engine delivered nothing".
///
/// The ordering inside is forced and is the whole reason this is a function rather than two
/// lines at each call site:
///
/// 1. build the `Definition`s (the runtime does not exist yet);
/// 2. `create_rho_runtime` with them installed;
/// 3. **bind the runtime's budget into the engine** — the handlers cannot fund a sandbox from
///    a budget that did not exist when they were built;
/// 4. inject, and run to rest.
///
/// Step 3 is not optional: an engine with no bound budget refuses every request typed, on
/// `^spec-err`, rather than running an unfunded (silently empty) exploration.
#[cfg(feature = "runtime-report")]
pub async fn run_normalized_par_with_lookahead_engine(
    program: &Par,
    engine: &crate::speculation::server::LookaheadEngine,
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<Par>>, String> {
    use rholang::rust::interpreter::accounting::has_cost::HasCost;

    let mut definitions = take_pending_fold_definitions();
    definitions.extend(engine.definitions());
    let (mut runtime, refusals) = build_runtime_with_definitions(definitions).await?;
    // The budget is the RUNTIME's, and `RuntimeBudget` is a handle over shared atomics — so
    // this clone observes `inj_on_runtime`'s later `set`, rather than a snapshot taken before
    // the deploy was funded.
    engine.bind_host(runtime.cost().clone());
    inj_on_runtime(&mut runtime, program.clone(), &refusals).await?;

    let mut result = HashMap::with_capacity(out_channels.len());
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_verbatim).await,
        );
    }
    Ok(result)
}

/// Build an in-memory `RhoRuntime`, inject normalized `program` for an
/// oracle/debug test, and return every datum resting on each requested quoted
/// channel VERBATIM, as the `Par` it is — from ONE execution.
///
/// The most general of the multi-channel readers, and the only one adequate to a
/// **fail-shut** assertion over an arbitrary datum. The typed readers
/// (`par_as_i64`, `par_as_string`, `par_as_runtime_observation_value`) all FILTER:
/// a datum they cannot decode is dropped, so an empty result means "nothing
/// readable rests here", which is indistinguishable from "nothing rests here".
/// That distinction is exactly what a spatial guard test needs, because the
/// interesting datum for a spatial match is a PROCESS (`{ @"a"!(1) | @"b"!(2) }`),
/// which no ground reader decodes. Reading verbatim `Par`s makes "the rejected
/// datum is still resting" checkable for every datum shape, and lets the test
/// compare against the lowered datum for identity rather than for a projection.
pub async fn run_normalized_par_for_oracle_and_read_par_channels(
    program: &Par,
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<Par>>, String> {
    let runtime = evaluate_par(program).await?;
    let mut result = HashMap::with_capacity(out_channels.len());
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_verbatim).await,
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

    let (mut runtime, refusals) = build_runtime().await?;
    eval_on_runtime(&mut runtime, program, &refusals).await?;

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
    let (mut runtime, refusals) = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program, &refusals).await?;
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

/// ★ Evaluate Rholang source and report **both** the tuplespace readings and every `where`
/// guard the substrate could not decide.
///
/// The ordinary entry points turn a decider-gap refusal into the run's `Err`, which is the right
/// default — a program whose guard was never decided has not done what its author asked — but an
/// `Err` carries no tuplespace. This variant reports the two independently, which is what makes
/// the separation *measurable* rather than merely asserted:
///
/// ```text
///   guard          refusals   OUT   c        reading
///   x > 0          []         [5]   []       TRUE:        fired
///   x > 100        []         []    [5]      FALSE:       rests, silently and correctly
///   x + 1          [1 gap]    []    [5]      UNDECIDABLE: rests, and SAYS SO
/// ```
///
/// Rows 2 and 3 leave the identical space; only the third column separates them, and before the
/// substrate lane had a refusal vocabulary that column did not exist.
///
/// The returned strings are [`GuardRefusal`](crate::guard_par_substrate::GuardRefusal)'s
/// `Display`: a pure function of the guard term and the recorded cause, so two nodes deciding
/// the same guard render the same text.
#[cfg(feature = "source-oracle")]
pub async fn run_rholang_source_and_read_ints_with_guard_refusals(
    program: &str,
    out_channels: &[&str],
) -> Result<(HashMap<String, Vec<i64>>, Vec<String>), String> {
    let (mut runtime, refusals) = build_runtime().await?;
    eval_on_runtime_unchecked(&mut runtime, program).await?;

    let mut result = HashMap::with_capacity(out_channels.len());
    for channel in out_channels {
        result.insert(
            (*channel).to_string(),
            read_ground_from_runtime(&runtime, channel, par_as_i64).await,
        );
    }
    let reported = refusals
        .take()
        .iter()
        .map(|refusal| refusal.to_string())
        .collect();
    Ok((result, reported))
}

/// Evaluate hand-authored Rholang source programs sequentially on one in-memory
/// `RhoRuntime`, then return every ground integer left resting on each requested
/// quoted channel.
#[cfg(feature = "source-oracle")]
pub async fn run_rholang_source_sequence_for_oracle_and_read_ints(
    programs: &[&str],
    out_channels: &[&str],
) -> Result<HashMap<String, Vec<i64>>, String> {
    let (mut runtime, refusals) = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program, &refusals).await?;
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
    let (mut runtime, refusals) = build_runtime().await?;
    for program in programs {
        eval_on_runtime(&mut runtime, program, &refusals).await?;
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
