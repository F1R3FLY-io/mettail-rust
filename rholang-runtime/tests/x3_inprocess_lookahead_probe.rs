//! X3 — the **in-process drive** probe: can a `[*]` lookahead evaluate a Foreign Language Term
//! from INSIDE a Rholang process and deliver the computed normal form to a channel a receive in
//! the same program is waiting on?
//!
//! This file measures the mechanism the `[*]` lowering needs, BEFORE any grammar or lowering
//! change, so the surface work is built on a measured substrate rather than an assumed one.
//!
//! ## The question
//!
//! Today `rholang` dispatches on the lowered program's shape: a **bare term** (no send/receive/new)
//! evaluates to its normal form through the in-Rho `^drive` quiescence driver; anything with
//! process structure runs to rest with the driver **absent**. So an FLT inside a process is inert,
//! and a program cannot collect results it computed — only results someone transcribed.
//!
//! ## The hypothesis under test
//!
//! `H`: the drive seed is an ordinary `Par`. Composing it into a user program and running that
//! whole program as the **call** against the Lambda backend's installed `^drive` receiver family
//! makes the driver available in-process, so `⟦P⟧` reduces and its resting term is delivered to an
//! arbitrary quoted channel — where an ordinary Rholang `for` can consume it.
//!
//! ## The second question, which the coordinator flagged as the collision risk
//!
//! A par of two FLTs in TERM mode fails (one drive per program — `^drive` meets an unrecognized
//! `PPar` head). That is a statement about ONE drive over a par-shaped *subject*. `[*]` seeds one
//! drive **per send**, which is a different shape: two independent seeds, two independent subjects.
//! [`two_inprocess_drives_in_one_program_both_deliver`] measures whether those collide.
#![cfg(all(feature = "rholang-runtime", feature = "lambda-runtime"))]

use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, rho_net_drive_call_par,
    suggest_rejected_rule_dispositions, FltRegistry, FltResolve, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver, DriveObservationChannels, PlannedRhoBackend,
};
use mettail_runtime::{clear_var_cache, Language};
use models::rhoapi::Par;

// ── the shared Lambda Rho-default backend (identical derivation to `flt_from_source.rs`) ────────

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

/// Parse Rholang source through the PRODUCTION entry and lower it under the FLT registry.
fn lower_source(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("probe source must parse: {source}\n{err}"));
    lower_rholang_proc_with_resolver(&proc, guest_resolver())
        .unwrap_or_else(|err| panic!("probe source must lower: {source}\n{err:?}"))
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Probe 1 — ONE in-process drive, delivering to a channel an ordinary `for` consumes
// ════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn one_inprocess_drive_delivers_a_computed_normal_form_to_a_waiting_receive() {
    let (backend, fingerprint) = lambda_backend();

    // ⟦App(I, K)⟧ — the reflected subject, obtained by lowering the FLT surface itself.
    let subject = lower_source("lambda`(lam x. x, lam a. lam b. a)`");

    // The lowering `x!(P)[*]` is to become: drive ⟦P⟧, deliver the resting term to `x`.
    let seed = rho_net_drive_call_par(&fingerprint, subject, "results");

    // An ORDINARY Rholang receive on that channel, republishing to @"OUT".
    let collector = lower_source(r#"for(@x <- @"results") { @"OUT"!(x) }"#);

    let program = seed.append(collector);
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&program, &channels)
        .await
        .expect("the composed program must run");

    println!(
        "PROBE-1 out={} err={} fuel={}",
        set.out_values.len(),
        set.err_data.len(),
        set.fuel_data.len()
    );
    for (i, v) in set.out_values.iter().enumerate() {
        println!("PROBE-1 OUT[{i}] = {v:?}");
    }
    assert!(set.err_data.is_empty(), "PROBE-1 ^drive-err must be empty: {:?}", set.err_data);
    assert!(
        set.fuel_data.is_empty(),
        "PROBE-1 ^drive-fuel must be empty: {:?}",
        set.fuel_data
    );
    assert_eq!(
        set.out_values.len(),
        1,
        "PROBE-1 expected exactly one computed normal form republished on @\"OUT\""
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Probe 2 — TWO in-process drives in ONE program (the collision risk)
// ════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn two_inprocess_drives_in_one_program_both_deliver() {
    let (backend, fingerprint) = lambda_backend();

    // Two DIFFERENT subjects, so a single delivery cannot masquerade as two.
    let subject_a = lower_source("lambda`(lam x. x, lam a. lam b. a)`"); // (I K) ⟶ K = λ.λ.1
    let subject_b = lower_source("lambda`(lam x. x, lam a. a)`"); // (I I) ⟶ I = λ.0

    let seed_a = rho_net_drive_call_par(&fingerprint, subject_a, "results");
    let seed_b = rho_net_drive_call_par(&fingerprint, subject_b, "results");

    // TWO receives on the same channel, each republishing — the collecting shape the demo needs.
    let collector = lower_source(
        r#"for(@x <- @"results") { @"OUT"!(x) } | for(@y <- @"results") { @"OUT"!(y) }"#,
    );

    let program = seed_a.append(seed_b).append(collector);
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&program, &channels)
        .await
        .expect("the composed two-drive program must run");

    println!(
        "PROBE-2 out={} err={} fuel={}",
        set.out_values.len(),
        set.err_data.len(),
        set.fuel_data.len()
    );
    for (i, v) in set.out_values.iter().enumerate() {
        println!("PROBE-2 OUT[{i}] = {v:?}");
    }
    println!("PROBE-2 err = {:?}", set.err_data);
    assert!(set.err_data.is_empty(), "PROBE-2 ^drive-err must be empty: {:?}", set.err_data);
    assert!(
        set.fuel_data.is_empty(),
        "PROBE-2 ^drive-fuel must be empty: {:?}",
        set.fuel_data
    );
    assert_eq!(
        set.out_values.len(),
        2,
        "PROBE-2 expected BOTH computed normal forms on @\"OUT\""
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Probe 3 — Ω under an in-process drive still populates the FAILURE side
// ════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn omega_under_an_inprocess_drive_reports_fuel_exhaustion() {
    let (backend, fingerprint) = lambda_backend();
    let subject = lower_source("lambda`(lam x. (x, x), lam x. (x, x))`");
    let seed = rho_net_drive_call_par(&fingerprint, subject, "results");
    let collector = lower_source(r#"for(@x <- @"results") { @"OUT"!(x) }"#);

    let program = seed.append(collector);
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&program, &channels)
        .await
        .expect("the composed Ω program must run");

    println!(
        "PROBE-3 out={} err={} fuel={}",
        set.out_values.len(),
        set.err_data.len(),
        set.fuel_data.len()
    );
    assert!(
        !set.fuel_data.is_empty(),
        "PROBE-3 Ω must exhaust fuel and SAY SO on ^drive-fuel (out={:?}, err={:?})",
        set.out_values.len(),
        set.err_data
    );
}
