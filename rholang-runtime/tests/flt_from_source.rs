//! L9-6b — the Foreign Exchange, driven FROM SOURCE. The sibling
//! `flt_abi_over_rspace.rs` hand-builds every reflected pattern/construction with the
//! `models` builders; here the SAME observables are produced by lowering Rholang FLT
//! surface syntax (`lambda:Term`(…, …)``) through the `PFlt` arms (`lower_proc` construction →
//! `reflect_flt_construction`; the receive-pattern path → `reflect_flt_pattern`), with a
//! `FltRegistry` mapping the opener tag `"lambda"` → `LambdaLanguage`.
//!
//! Beats reproduced: 0 (the construction reflects byte-identically to the hand-built
//! `⟦App(id, K)⟧`), 1 (the typed hole binds the function position), 2 (the ground `⟦K⟧`
//! subpattern vetoes a foreign argument), 3 (the 4-element `GString`-tagged counterfeit is
//! rejected — pure No-Injection), and 4 (fill the holes and RUN to β-NF `⟦K⟧`).
#![cfg(feature = "lambda-runtime")]

use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{
    ground_marker_tag_par, lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par, rho_net_drive_call_par, suggest_rejected_rule_dispositions,
    FltRegistry, FltResolve, GroundTerm, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, BOUND_VAR_REFLECT_LABEL, DRIVE_DEFAULT_FUEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    drive_cross_check, lower_rholang_proc_with_resolver,
    run_normalized_par_for_oracle_and_read_runtime_values, DriveObservationChannels,
    PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};
use models::rhoapi::Par;
use models::rust::utils::{new_elist_par, new_gstring_par, new_send_par};

// ── the shared Lambda Rho-default backend (identical to flt_abi_over_rspace.rs) ────────────────

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

// ── reflected-term (GroundTerm) builders — the hand-built ground truth ──────────────────────────
fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = g_node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    g_node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}
fn g_lambda(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}
/// `id = lam x. x`.
fn g_id() -> GroundTerm {
    g_lambda(g_bound(0))
}
/// `K = lam a. lam b. a`.
fn g_k() -> GroundTerm {
    g_lambda(g_lambda(g_bound(1)))
}
fn g_app(fun: GroundTerm, arg: GroundTerm) -> GroundTerm {
    g_node("App", vec![fun, arg])
}

/// The `"lambda"` → `LambdaLanguage` FLT resolver every from-source lowering installs.
fn lambda_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lambda", Box::new(LambdaLanguage)))
}

/// The guest-body surface for `App(id, K)` in Lambda's own syntax (`App` is spelled
/// `(fun, arg)`; the combinators are spelled out, so they reflect GROUND).
const APP_ID_K_BODY: &str = "lambda:Term`(lam x. x, lam a. lam b. a)`";

// ── Beat 0 (from source) — the FLT construction reflects to ⟦App(id, K)⟧ ────────────────────────

/// The `lambda:Term`(…, …)`` FLT, lowered in construction position, reflects BYTE-FOR-BYTE to the
/// hand-built `⟦App(id, K)⟧` — the wire format, produced by the source path. Also pins the
/// coherence the whole demo rests on: `metadata().definition_fingerprint()` (what the `PFlt`
/// arm reflects with) equals the backend plan's fingerprint (what it drives against).
#[test]
fn beat0_from_source_construction_reflects_app_id_k() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();

    // Coherence: the reflector fingerprint the PFlt arm uses == the backend's.
    assert_eq!(
        LambdaLanguage.metadata().definition_fingerprint(),
        Some(fp.as_str()),
        "the guest metadata fingerprint must equal the backend plan fingerprint"
    );

    let proc = Proc::parse(APP_ID_K_BODY).expect("the FLT construction parses as a Rholang Proc");
    let lowered = lower_rholang_proc_with_resolver(&proc, lambda_resolver())
        .expect("the PFlt construction arm lowers via the lam-registered guest");

    assert_eq!(
        lowered,
        reflect_ground_term_par(&g_app(g_id(), g_k()), &fp),
        "the source-lowered FLT is byte-for-byte ⟦App(id, K)⟧"
    );
}

// ── decoded-observation builders (mirror flt_abi_over_rspace.rs) ────────────────────────────────
fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}
fn onullary(constructor: &str) -> RuntimeObservationValue {
    oterm(constructor, Vec::new())
}
fn opeano(n: usize) -> RuntimeObservationValue {
    let mut peano = onullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..n {
        peano = oterm(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    peano
}
fn obound(n: usize) -> RuntimeObservationValue {
    oterm(BOUND_VAR_REFLECT_LABEL, vec![opeano(n)])
}
fn olambda(body: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm(LAMBDA_REFLECT_LABEL, vec![body])
}
/// The decoded identity `id = λ.0`.
fn oid() -> RuntimeObservationValue {
    olambda(obound(0))
}

/// Lower a from-source Rholang FLT program (installing the `lambda` guest) and run it to rest,
/// reading the `RuntimeObservationValue`s published to `@"OUT"`.
async fn out_values_from_source(program_src: &str) -> Vec<RuntimeObservationValue> {
    let proc = Proc::parse(program_src).expect("the from-source FLT program parses");
    let program = lower_rholang_proc_with_resolver(&proc, lambda_resolver())
        .expect("the from-source FLT program lowers via the lam-registered guest");
    run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the from-source FLT program runs to rest on the reducer")
}

// ── Beat 1 (from source) — ship an FLT, destructure it with a typed hole ────────────────────────

/// `@"fltX"!(lambda:Term`(id, K)`) | for( @lambda:Term`(${f}, K)` <- @"fltX" ){ @"OUT"!(f) }`, written in FLT
/// surface syntax and lowered end-to-end: the send's `PFlt` reflects to `⟦App(id, K)⟧`, the
/// receive's `PFlt` reflects to the typed-hole pattern `[⌜App⌝, _, ${f}, ⟦K⟧]`, and the body's
/// `f` resolves to the captured hole — so OUT de-reflects to `id = λ.0`. Reproduces
/// `flt_abi_over_rspace::beat1_typed_hole_binds_the_function_position` from source.
#[tokio::test]
async fn beat1_from_source_typed_hole_binds_the_function_position() {
    mettail_runtime::clear_var_cache();
    let fired = out_values_from_source(
        "@\"fltX\"!(lambda:Term`(lam x. x, lam a. lam b. a)`) | \
         for( @lambda:Term`(${f}, lam a. lam b. a)` <- @\"fltX\" ){ @\"OUT\"!(f) }",
    )
    .await;
    assert_eq!(fired, vec![oid()], "the ${{f}} hole binds ⟦id⟧ — OUT de-reflects to λ.0");
}

fn oapp(fun: RuntimeObservationValue, arg: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm("App", vec![fun, arg])
}
/// The decoded `K = λ.λ.1`.
fn okonst() -> RuntimeObservationValue {
    olambda(olambda(obound(1)))
}

// ── Beat 2 (from source) — the ground `⟦K⟧` subpattern vetoes a foreign argument ────────────────

/// Against the source pattern `for( @lambda:Term`(${f}, K)` <- … )`, `⟦App(id, K)⟧` matches (arg = ⟦K⟧,
/// OUT = [⟦id⟧]) while `⟦App(id, id)⟧` fails (arg ⟦id⟧ ≠ ⟦K⟧, OUT empty — veto, zero effects).
#[tokio::test]
async fn beat2_from_source_ground_subpattern_vetoes() {
    mettail_runtime::clear_var_cache();
    let matches = out_values_from_source(
        "@\"fltX\"!(lambda:Term`(lam x. x, lam a. lam b. a)`) | \
         for( @lambda:Term`(${f}, lam a. lam b. a)` <- @\"fltX\" ){ @\"OUT\"!(f) }",
    )
    .await;
    assert_eq!(matches, vec![oid()], "⟦App(id, K)⟧ satisfies the ⟦K⟧ argument subpattern");

    mettail_runtime::clear_var_cache();
    let vetoed = out_values_from_source(
        "@\"fltX\"!(lambda:Term`(lam x. x, lam x. x)`) | \
         for( @lambda:Term`(${f}, lam a. lam b. a)` <- @\"fltX\" ){ @\"OUT\"!(f) }",
    )
    .await;
    assert!(
        vetoed.is_empty(),
        "⟦App(id, id)⟧ has ⟦id⟧ ≠ ⟦K⟧ at the argument — veto, OUT empty"
    );
}

// ── Beat 4 (from source, re-quote) — capture the holes, re-quote, reconstruct ⟦App(id, K)⟧ ──────

/// The full-arity FLT rendezvous: a receiver captures BOTH holes `${f}`,`${k}` from `⟦App(id, K)⟧`
/// and its body RE-QUOTES `lambda:Term`(${f}, ${k})`` (a construction-position `PFlt` whose holes are the
/// captured bound vars — `lower_flt_construction` fills them with `^bound` and C2 forces `⌜^nog⌝`).
/// After the COMM substitutes the captured `⟦id⟧`/`⟦K⟧`, OUT rests at the reconstructed
/// `⟦App(id, K)⟧` — the hole-filling construction path, from source.
#[tokio::test]
async fn beat4_from_source_requote_reconstructs_app() {
    mettail_runtime::clear_var_cache();
    let out = out_values_from_source(
        "@\"fltX\"!(lambda:Term`(lam x. x, lam a. lam b. a)`) | \
         for( @lambda:Term`(${f}, ${k})` <- @\"fltX\" ){ @\"OUT\"!(lambda:Term`(${f}, ${k})`) }",
    )
    .await;
    assert_eq!(
        out,
        vec![oapp(oid(), okonst())],
        "the re-quote from the captured holes reconstructs ⟦App(id, K)⟧"
    );
}

// ── Beat 4 (from source, THE WOW) — the source FLT subject drives to β-NF ⟦K⟧ ────────────────────

/// `(λx.x) K` — the FLT subject `lambda:Term`(id, K)`` built FROM SOURCE — is seeded to the backend's
/// installed `^drive` quiescence family and drives fully in-Rho to β-NF `K = λ.λ.1`: `^fired`
/// records exactly `["Beta"]`, both fail-close channels stay empty. Reproduces
/// `flt_abi_over_rspace::beat4_app_id_k_drives_to_konst_in_rho`, its subject from source.
#[tokio::test]
async fn beat4_from_source_subject_drives_to_konst() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let proc = Proc::parse(APP_ID_K_BODY).expect("the FLT subject parses");
    let subject = lower_rholang_proc_with_resolver(&proc, lambda_resolver())
        .expect("the FLT subject lowers from source");
    let seed = rho_net_drive_call_par(&fp, subject, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the source FLT subject drives to quiescence on the reducer");

    assert_eq!(set.out_values, vec![okonst()], "(λx.x) K rests at K = λ.λ.1 — β fired in-Rho");
    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string()],
        "exactly one Beta firing"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head");
    assert!(set.fuel_data.is_empty(), "terminated by quiescence, not fuel");
    drive_cross_check(&set, &channels, true, DRIVE_DEFAULT_FUEL, &|value| {
        mettail_rholang_runtime::binder_apply_redex_present("App", value)
    })
    .expect("the always-on drive cross-check is green");
}

// ── Beat 3 (from source pattern) — the counterfeit is rejected: tags are unforgeable ────────────

/// The SOURCE receive pattern `for( @lambda:Term`(${f}, K)` <- … )` requires the unforgeable `GPrivate`
/// `⌜App⌝` head. A 4-element `GString`-tagged counterfeit `["App", ⌜^nog⌝, ⟦id⟧, ⟦K⟧]` — byte-for-
/// byte `⟦App(id, K)⟧` EXCEPT a ground string `"App"` head — matches the arity, the wildcarded
/// marker slot, and the ground `⟦K⟧`, so the ONLY discriminant is the head tag: it never matches,
/// OUT stays empty. Pure No-Injection — no surface spells a `GPrivate`. The counterfeit datum is
/// necessarily hand-built (no surface produces a `GString`-tagged fake); the PATTERN is from source.
#[tokio::test]
async fn beat3_from_source_pattern_rejects_counterfeit() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();

    // The hand-built 4-element counterfeit: a ground `"App"` GString head where the genuine
    // subject carries the `GPrivate` ⌜App⌝, the genuine ⌜^nog⌝ marker, and ground ⟦id⟧/⟦K⟧.
    let counterfeit = new_elist_par(
        vec![
            new_gstring_par("App".to_string(), Vec::new(), false),
            ground_marker_tag_par(&fp, false),
            reflect_ground_term_par(&g_id(), &fp),
            reflect_ground_term_par(&g_k(), &fp),
        ],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    let producer = new_send_par(
        new_gstring_par("fltX".to_string(), Vec::new(), false),
        vec![counterfeit],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    // The receive pattern, FROM SOURCE.
    let receive_proc =
        Proc::parse("for( @lambda:Term`(${f}, lam a. lam b. a)` <- @\"fltX\" ){ @\"OUT\"!(f) }")
            .expect("the source receive parses");
    let receive = lower_rholang_proc_with_resolver(&receive_proc, lambda_resolver())
        .expect("the source receive lowers");
    let program: Par = producer.append(receive);

    let rested = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the counterfeit rendezvous runs to rest");
    assert!(
        rested.is_empty(),
        "the GString-tagged counterfeit ≠ the GPrivate ⌜App⌝ tag — no match, OUT empty"
    );
}

// ── #14 (from source) — an FLT hole and a moniker binder co-bind in one `&`-join ────────────────

/// A `&`-join whose FIRST bind is an FLT typed-hole pattern (`@lambda:Term`(${f}, K)` <- fltX`) and whose
/// SECOND is an ordinary moniker binder (`@g <- other`): the FLT hole `f` (bound by NAME) and the
/// moniker `g` (bound by its `FreeVar`) share ONE coherent de-Bruijn numbering, so the body's `f`
/// and `g` BOTH resolve — `f ← ⟦id⟧` (from the FLT), `g ← ⟦K⟧` (from `@"other"`). Closes the L9-6b
/// `&`-join deferral (was fail-closed). Order on OUT is nondeterministic, so assert as a set.
#[tokio::test]
async fn join14_from_source_flt_hole_and_moniker_binder_co_bind() {
    mettail_runtime::clear_var_cache();
    let mut out = out_values_from_source(
        "@\"fltX\"!(lambda:Term`(lam x. x, lam a. lam b. a)`) | @\"other\"!(lambda:Term`lam a. lam b. a`) | \
         for( @lambda:Term`(${f}, lam a. lam b. a)` <- @\"fltX\" & @g <- @\"other\" ){ \
         @\"OUT\"!(f) | @\"OUT\"!(g) }",
    )
    .await;
    out.sort_by_key(|value| format!("{value:?}"));
    let mut expected = vec![oid(), okonst()];
    expected.sort_by_key(|value| format!("{value:?}"));
    assert_eq!(
        out, expected,
        "the FLT hole f binds ⟦id⟧ and the moniker g binds ⟦K⟧ — both resolve in the join body"
    );
}
