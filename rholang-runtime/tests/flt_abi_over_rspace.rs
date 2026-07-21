//! The Foreign Exchange — pinning-test twin for `demos/flt-foreign-exchange/RUN-SHEET.md`
//! (phase-now, ABI level). The task-#8 integration pattern: each SOLID beat asserts its
//! observable on a fresh in-memory f1r3node RSpace, so a recording and a live run match.
//!
//! This suite is the drive/ABI half of the demo. It reuses the proven machinery of the
//! sibling `rho_net_lambda_firing.rs` (the production `Lambda` driven to quiescence FULLY
//! in-Rho by the generated `^drive` receiver family): the reflected-term ABI, the drive seed,
//! and the four observation channels ([`DriveObservationChannels`]).
//!
//! ── What is SOLID here (asserted as fact) ────────────────────────────────────────────────
//!   * Beat 0 — the wire format: the reflected tagged-EList forms of `id` / `K` round-trip
//!     through `par_as_runtime_observation_value`, and the per-language tag string is the
//!     `mettail.term.{fp}.{label}` unforgeable-`GPrivate` name (rho_net_lower.rs:1710-1715).
//!   * Beat 4 (core) — fill-holes-and-RUN: the subject `App(id, K)` drives to β-NF `K` in-Rho,
//!     the `^fired` ledger records exactly `["Beta"]`, and `^drive-err`/`^drive-fuel` stay
//!     empty. (Byte-for-byte the shape of `single_beta_drives_to_nf_in_rho`.)
//!   * Beat 5 (Ω) — fuel exhaustion is typed and fail-closed: Ω fires exactly per-path-fuel
//!     times, the stuck redex rests on `^drive-fuel`, and OUT never claims an NF.
//!
//! ── What is NOT wireable phase-now (Beats 1/2/3, see the ignored ledger test below) ───────
//!   The FLT receive-with-typed-hole (`for( @[⌜App⌝, ${f}, ⟦K⟧] <- @"fltX" ){…}`) needs a
//!   receive whose `BindPattern` is a reflected EList carrying a `FreeVar` at the hole and a
//!   GROUND reflected subterm elsewhere. The only reflector that admits variables in a pattern,
//!   `reflect_term_par_env` (rho_net_lower.rs:3607), is PRIVATE, and no public "`^free` leaf →
//!   match `FreeVar`" transformation is exported (`lib.rs` exports only the GROUND
//!   `reflect_ground_term_par`). So the run sheet's hole convention is not wireable from the
//!   public surface today; those observables stay VALIDATE, not asserted. Details in the
//!   ignored test.
#![cfg(feature = "lambda-runtime")]

use mettail_languages::lambda::LambdaLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par, reflected_tag_string, rho_net_drive_call_par,
    rho_net_drive_call_par_with_fuel, suggest_rejected_rule_dispositions, GroundTerm,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    BOUND_VAR_REFLECT_LABEL, DRIVE_DEFAULT_FUEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    binder_apply_redex_present, drive_cross_check, par_as_runtime_observation_value,
    DriveObservationChannels, PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};

// ── the shared Lambda Rho-default backend (identical derivation to rho_net_lambda_firing.rs) ──

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

// ── decoded-observation builders (mirror rho_net_lambda_firing.rs) ─────────────────────────
fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children }
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
fn oapp(fun: RuntimeObservationValue, arg: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm("App", vec![fun, arg])
}
/// The decoded identity `id = λ.0` (the α-erased image of `lam x. x`).
fn oid() -> RuntimeObservationValue {
    olambda(obound(0))
}
/// The decoded `K = λ.λ.1` (the α-erased image of `lam a. lam b. a` — the committed golden).
fn okonst() -> RuntimeObservationValue {
    olambda(olambda(obound(1)))
}

// ── reflected-term (GroundTerm) builders, for the direct-seed subjects ─────────────────────
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

/// The Lambda NF-scan for the always-on drive cross-check: `true` iff an `App(^lambda(_), _)`
/// redex is present.
fn lambda_redex_scan(value: &RuntimeObservationValue) -> bool {
    binder_apply_redex_present("App", value)
}

// ── Beat 0 — the wire format existed before the syntax ─────────────────────────────────────

/// The reflected tagged-EList forms of `id` and `K` round-trip through the ABI decoder, and the
/// per-language tag is the unforgeable `mettail.term.{fp}.{label}` GPrivate name — the
/// foreign-language-term wire format, asserted directly (no run).
#[test]
fn beat0_wire_format_reflects_and_tags_are_unforgeable_private_names() {
    let (_backend, fp) = lambda_backend();

    // The reflected ground forms decode back to the canonical de-Bruijn observation shapes.
    assert_eq!(
        par_as_runtime_observation_value(&reflect_ground_term_par(&g_id(), &fp)),
        Some(oid()),
        "⟦id⟧ round-trips to λ.0"
    );
    assert_eq!(
        par_as_runtime_observation_value(&reflect_ground_term_par(&g_k(), &fp)),
        Some(okonst()),
        "⟦K⟧ round-trips to λ.λ.1"
    );

    // The label tag is the deterministic per-fingerprint unforgeable name (no surface syntax
    // spells a GPrivate — the No-Injection substrate).
    let app_tag = reflected_tag_string(&fp, "App");
    assert!(
        app_tag.starts_with("mettail.term.") && app_tag.ends_with(".App"),
        "the App tag is the mettail.term.<fp>.App private name, got {app_tag:?}"
    );
    assert_eq!(app_tag, format!("mettail.term.{fp}.App"), "the tag is fingerprint-deterministic");
}

// ── Beat 4 (core) — fill the holes and RUN it: quotation to β-normal form ──────────────────

/// The subject `App(id, K)` drives to its β-NF `K = λ.λ.1` fully in-Rho (the driver's Beta arm
/// fires through the σ ABI + the installed subst TRS, and the re-driven contractum quiesces),
/// with the `^fired` ledger recording exactly `["Beta"]` and both fail-close channels empty.
///
/// This is the RUN outcome of Beat 4's re-quote-and-drive. The FLT-rendezvous WRAPPER that
/// captures `f`/`k` from a typed hole and feeds this drive is the non-wireable part (see the
/// ignored ledger test); the drive itself — the "wow" — is proven here.
#[tokio::test]
async fn beat4_app_id_k_drives_to_konst_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let subject = g_app(g_id(), g_k());
    let seed = rho_net_drive_call_par(&fp, reflect_ground_term_par(&subject, &fp), "OUT");
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the App(id, K) drive runs to quiescence on the reducer");

    assert_eq!(set.out_values, vec![okonst()], "(λx.x) K rests at K = λ.λ.1 — β fired, contractum re-drove");
    assert_eq!(set.fired_labels().expect("ledger decodes"), vec!["Beta".to_string()], "exactly one Beta firing");
    assert!(set.err_data.is_empty(), "no unrecognized head — the err channel stays empty");
    assert!(set.fuel_data.is_empty(), "the drive terminated by quiescence, not fuel");
    drive_cross_check(&set, &channels, true, DRIVE_DEFAULT_FUEL, &lambda_redex_scan)
        .expect("the always-on drive cross-check is green");
}

// ── Beat 5 (Ω) — fuel exhaustion typed, fail-closed ────────────────────────────────────────

/// `Ω = (λx.(x x))(λx.(x x))` diverges; a small per-path fuel (3) exhausts: exactly `fuel`
/// firings ledger, the typed `^drive-fuel` datum carries the stuck redex (Ω itself), OUT stays
/// EMPTY (exhaustion never claims an NF), and `^drive-err` stays empty. This is the Ω fuel
/// witness of Beat 5's honest behavioral-predicate negative.
#[tokio::test]
async fn beat5_omega_exhausts_fuel_with_the_typed_datum() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let omega_half = g_lambda(g_app(g_bound(0), g_bound(0)));
    let omega = g_app(omega_half.clone(), omega_half);
    let seed = rho_net_drive_call_par_with_fuel(&fp, reflect_ground_term_par(&omega, &fp), 3, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the Ω drive terminates BY FUEL on the reducer");

    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string(); 3],
        "Ω fires exactly per-path-fuel = 3 times before exhaustion"
    );
    assert_eq!(set.fuel_data.len(), 1, "exactly one typed exhaustion datum rests on ^drive-fuel");
    let omega_decoded = oapp(
        olambda(oapp(obound(0), obound(0))),
        olambda(oapp(obound(0), obound(0))),
    );
    assert_eq!(
        par_as_runtime_observation_value(&set.fuel_data[0]),
        Some(omega_decoded),
        "the exhaustion datum is the stuck redex node (Ω) — typed, never an NF claim"
    );
    assert!(set.out_values.is_empty(), "exhaustion NEVER claims a visible NF");
    assert!(set.err_data.is_empty(), "no unrecognized head — the err channel stays empty");
}

// ── Beats 1/2/3 — the typed-hole FLT rendezvous (NOT wireable from the public surface) ──────

/// LEDGER (ignored): Beats 1, 2, and 3 all pivot on a `for`-comprehension whose receive pattern
/// is a reflected tagged-EList carrying a TYPED HOLE — a `FreeVar` at the function position —
/// plus (Beat 1) a ground `⟦K⟧` subpattern, (Beat 2) a `where a == ⟦K⟧` guard on `Receive.
/// condition`, and (Beat 3) the string-tagged counterfeit that must NOT match.
///
/// The run sheet's hole convention ("a free variable in the guest pattern source … its `^free`
/// leaf transformed to a match `FreeVar`") has NO public realization today:
///   * `reflect_ground_term_par` (the only public reflector) is GROUND-ONLY — it cannot place a
///     `FreeVar` at a hole.
///   * `reflect_term_par_env` (rho_net_lower.rs:3607), which DOES admit pattern variables, is a
///     private `fn` inside rholang-codegen; no "`^free` → `FreeVar`" transformer is exported.
///   * There is therefore no public builder for an FLT receive `BindPattern`, and no test/helper
///     precedent for a hand-built mixed `FreeVar`+ground reflected-EList receive.
///
/// Consequently the Beat 1/2/3 OBSERVABLES stay VALIDATE — they must not be asserted as fact
/// from the current public surface. To land them, EITHER expose the pattern reflector +
/// `^free`→`FreeVar` transform from rholang-codegen (a production-code change, out of scope for
/// this phase-now demo), OR hand-construct the `Receive`/`ReceiveBind`/`EList`/`Var(FreeVar)` by
/// hand against the spatial-matcher contract and VALIDATE the observable on the running reducer
/// before pinning it. This ignored test is the standing record of that gap.
#[test]
#[ignore = "VALIDATE: FLT typed-hole receive pattern (^free → FreeVar) has no public builder; see body"]
fn beats_1_2_3_flt_typed_hole_rendezvous_await_free_var_pattern_builder() {
    // Intentionally unimplemented: asserting any observable here would be a guess, which the
    // task forbids. The intended programs (narrated by the demo bin) are, per the run sheet:
    //   Beat 1:  @"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, ${f}, ⟦K⟧] <- @"fltX" ){ @"OUT"!(f) }
    //            expected (VALIDATE): OUT [⟦id⟧] (de-reflected `lam x. x`); wrong-shape rests.
    //   Beat 2:  for( @[⌜App⌝, ${f}, ${a}] <- @"fltX" where a == ⟦K⟧ ){ @"OUT"!(f) }
    //            expected (VALIDATE): match ⟦App(id,K)⟧ → OUT [⟦id⟧]; ⟦App(id,id)⟧ → veto, rests.
    //   Beat 3:  send the GString-tagged fake ["App", ⟦id⟧, ⟦K⟧] at the same receive
    //            expected (VALIDATE): no match; the datum rests (tags compared by identity).
    panic!("unreachable: ignored ledger test documenting the non-wireable FLT hole mechanism");
}
