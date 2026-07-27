//! X6 — the probe the `[*]` request server is built on: **can a reflected λ term be explored
//! by the speculation engine and yield its normal form?**
//!
//! `LookaheadRequest::prelude` exists because a reflected guest term is inert on its own. The
//! `s2_ambient_open_race` suite already measures the composition for Ambient
//! (`installed_rho_net_program_par() | rho_net_drive_call_par(…)` explored under
//! `TraceMode::IndependenceReduced`); this file measures it for **Lambda**, whose drive is a
//! far longer COMM chain, because that is the guest the acceptance program uses and a
//! mechanism that works for one guest and explodes on another is not a mechanism.
//!
//! Nothing here is a shortcut: the drive seed is the guest's *evaluator*, injected into the
//! **sandbox**, where every COMM is enumerated by BFS over `E(S)`. It is not the host-side
//! single-path `^drive` run that `x5_lookahead_lowering.rs` forbids the LOWERING from emitting.
#![cfg(all(feature = "rholang-runtime", feature = "lambda-runtime"))]

use std::sync::Arc;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, rho_net_drive_call_par,
    suggest_rejected_rule_dispositions, FltRegistry, FltResolve, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::speculation::search::{Lookahead, TraceMode};
use mettail_rholang_runtime::speculation::service::{
    LeafProjection, LookaheadRequest, LookaheadService,
};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver, par_as_runtime_observation_value, PlannedRhoBackend,
};
use mettail_runtime::{clear_var_cache, Language};
use models::rhoapi::Par;
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const LEAF: &str = "^spec-leaf";

fn lambda_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("LambdaLanguage definition_source must reconstruct as a LanguageDef");
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("production Lambda must plan its Rho-default backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lambda", Box::new(LambdaLanguage)))
}

fn lower_source(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("probe source must parse: {source}\n{err}"));
    lower_rholang_proc_with_resolver(&proc, guest_resolver())
        .unwrap_or_else(|err| panic!("probe source must lower: {source}\n{err:?}"))
}

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "x6 probe host deploy"));
    budget
}

async fn probe(label: &str, source: &str) {
    let (backend, fingerprint) = lambda_backend();
    let prelude = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("the installed Lambda Rho-net program must lower");
    let subject = rho_net_drive_call_par(&fingerprint, lower_source(source), LEAF);

    let host = host_budget(40_000_000);
    let started = std::time::Instant::now();
    let response = LookaheadService::serve(
        LookaheadRequest::new(subject, Lookahead::Unbounded)
            .with_prelude(prelude)
            .with_projection(LeafProjection::resting_on(LEAF))
            .with_trace_mode(TraceMode::IndependenceReduced),
        Blake2b512Random::create_from_length(128),
        &host,
    )
    .await
    .expect("the service must serve the λ request");

    let rendered: Vec<String> = response
        .reply
        .iter()
        .map(|par| match par_as_runtime_observation_value(par) {
            Some(value) => format!("{value:?}"),
            None => "<undecodable>".to_string(),
        })
        .collect();
    eprintln!(
        "[{label}] elapsed={:?} success={} truncated={} failure={} error={} consumed={}",
        started.elapsed(),
        response.exploration.success.len(),
        response.truncated.len(),
        response.failure.len(),
        response.error.is_some(),
        response.consumed.value,
    );
    eprintln!("[{label}] stats={:?}", response.exploration.stats);
    for (index, value) in rendered.iter().enumerate() {
        eprintln!("[{label}] reply[{index}] = {value}");
    }
    assert!(
        response.failure.is_empty(),
        "[{label}] nothing may abort: {:?}",
        response.failure
    );
    assert!(response.error.is_none(), "[{label}] the request itself must be served");
    assert_eq!(response.reply.len(), 1, "[{label}] λ is confluent: exactly one normal form");
}

#[tokio::test]
async fn plus_two_three_reduces_under_the_speculation_engine() {
    probe(
        "plus",
        "lambda`((lam m. lam n. lam f. lam x. ((m, f), ((n, f), x)), lam f. lam x. (f, (f, x))), \
         lam f. lam x. (f, (f, (f, x))))`",
    )
    .await;
}

#[tokio::test]
async fn a_short_beta_chain_reduces_under_the_speculation_engine() {
    probe("ik", "lambda`(lam x. x, lam a. lam b. a)`").await;
}
