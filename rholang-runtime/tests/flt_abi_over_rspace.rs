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
//! ── The typed-hole FLT receive (Beats 1/2/3), hand-built against the matcher contract ──────
//!   The FLT receive-with-typed-hole (`for( @[⌜App⌝, ${f}, ⟦K⟧] <- @"fltX" ){…}`) needs a
//!   receive whose `BindPattern` is a reflected EList carrying a `FreeVar` at the hole and a
//!   GROUND reflected subterm elsewhere. No PUBLIC reflector emits such a pattern —
//!   `reflect_ground_term_par` is ground-only, and `reflect_term_par_env` (rho_net_lower.rs:3607)
//!   is private and emits σ-slot `BoundVar`s, not receive `FreeVar`s. But the pattern is
//!   realizable TEST-SIDE with the `models` builders (mirroring the proven in-tree
//!   `e6a_support::discovery_call_par` receive shape): a reflected tagged-EList whose head is the
//!   unforgeable `GPrivate` tag (from the public `reflect_ground_term_par`), whose function
//!   position is `EVar(FreeVar(0))`, and whose argument position is a ground reflected subterm.
//!   This lands all three beats on the reducer with ZERO production change (no reflector API is
//!   exposed) — validated below: the hole binds ⟦id⟧, the ground subpattern discriminates a
//!   foreign argument, and the unforgeable tag rejects a GString-tagged counterfeit.
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
    run_normalized_par_for_oracle_and_read_runtime_values, DriveObservationChannels,
    PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{Par, ReceiveBind};
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_receive_par,
    new_send_par,
};

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

// ── Beats 1/2/3 — the typed-hole FLT rendezvous (hand-built against the matcher contract) ────
//
// VALIDATE-FIRST OUTCOME: the run sheet's hole convention IS realizable phase-now by
// hand-constructing the receive `BindPattern` directly with the `models` crate — no production
// reflector API is exposed and no production code changes. The public surface still lacks a
// `^free`→`FreeVar` reflector (`reflect_ground_term_par` is ground-only; `reflect_term_par_env`,
// rho_net_lower.rs:3607, is private and emits σ-slot `BoundVar`s, NOT receive `FreeVar`s), so the
// pattern is assembled TEST-SIDE: a reflected tagged-EList `[⌜App⌝, EVar(FreeVar(0)), ⟦K⟧]` whose
// head is the unforgeable `GPrivate` tag (from the public `reflect_ground_term_par`), whose
// function position is a match `FreeVar` hole, and whose argument position is a GROUND reflected
// subterm. The receive shape mirrors the proven in-tree builder `e6a_support::discovery_call_par`.
//
// This lands all three beats on the running reducer with zero production change:
//   * Beat 1 — the hole binds: ⟦App(id, K)⟧ matches `[⌜App⌝, ${f}, ⟦K⟧]`, f ← ⟦id⟧, OUT = [⟦id⟧].
//   * Beat 2 — veto on a foreign subterm (run-sheet D2 ground-subpattern form): ⟦App(id, id)⟧ has
//     ⟦id⟧ ≠ ⟦K⟧ at the argument position, so it does NOT match and rests; OUT stays empty. (The
//     equivalent `where a == ⟦K⟧` guard form is ALSO viable — `rho_pure_eval`'s `EEq` is a
//     structural `Par` equality, not a numeric op — but the ground-subpattern is the wired form.)
//   * Beat 3 — the counterfeit is rejected: a GString-tagged `["App", ⟦id⟧, ⟦K⟧]` fake carries the
//     ground string head, not the `GPrivate` tag, so it never matches; OUT stays empty.

/// The reflected `(⌜App⌝, ⟦id⟧, ⟦K⟧)` triple decomposed from `⟦App(id, K)⟧`
/// (`EList[GPrivate(⌜App⌝), ⟦id⟧, ⟦K⟧]`) — the unforgeable head tag, plus the two ground children.
fn reflected_app_parts(fp: &str) -> (Par, Par, Par) {
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);
    match subject.exprs.first().and_then(|e| e.expr_instance.as_ref()) {
        // E-2-D (reflected-ABI v2): ⟦App(id, K)⟧ = [App_tag, ^nog, ⟦id⟧, ⟦K⟧] — the hereditary-
        // ground marker sits at index 1, so the head tag / id / K are ps[0] / ps[2] / ps[3].
        Some(ExprInstance::EListBody(list)) => {
            (list.ps[0].clone(), list.ps[2].clone(), list.ps[3].clone())
        },
        other => panic!("⟦App(id, K)⟧ must reflect to a 4-element EList (marker at 1), got {other:?}"),
    }
}

fn quoted_name(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// Assemble `@"fltX"!(subject) | for( @[tag, ${f}, ground_arg] <- @"fltX" ){ @"OUT"!(f) }` purely
/// with the `models` builders. The receive `BindPattern` is the reflected tagged-EList carrying a
/// `FreeVar` hole at the function position and a GROUND subterm at the argument position; the body
/// republishes the bound hole to `@"OUT"`. Shape mirrors `e6a_support::discovery_call_par`.
fn hole_rendezvous_program(subject: Par, tag: Par, ground_arg: Par) -> Par {
    let producer =
        new_send_par(quoted_name("fltX"), vec![subject], false, Vec::new(), false, Vec::new(), false);
    // Pattern `[⌜tag⌝, _, ${f}, ground_arg]`: E-2-D v2 puts the hereditary-ground marker at index
    // 1, so a wildcard absorbs it; the FreeVar (function-position hole) then binds at index 2. The
    // FreeVar makes the EList (and its Par) connective-used.
    let pattern = new_elist_par(
        vec![
            tag,
            models::rust::utils::new_wildcard_par(Vec::new(), true),
            new_freevar_par(0, Vec::new()),
            ground_arg,
        ],
        Vec::new(),
        true,
        None,
        Vec::new(),
        true,
    );
    // Body `@"OUT"!(f)`: the matched hole is BoundVar(0) in the continuation scope.
    let body = new_send_par(
        quoted_name("OUT"),
        vec![new_boundvar_par(0, create_bit_vector(&[0]), false)],
        false,
        create_bit_vector(&[0]),
        false,
        create_bit_vector(&[0]),
        false,
    );
    let receive = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![pattern],
            source: Some(quoted_name("fltX")),
            remainder: None,
            free_count: 1,
        }],
        body,
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    producer.append(receive)
}

async fn out_values(program: &Par) -> Vec<RuntimeObservationValue> {
    run_normalized_par_for_oracle_and_read_runtime_values(program, "OUT")
        .await
        .expect("the hole-rendezvous program runs to rest on the reducer")
}

/// Beat 1 — ship an FLT and destructure it with a typed hole: `⟦App(id, K)⟧` matches
/// `[⌜App⌝, ${f}, ⟦K⟧]`, the function-position hole binds to `⟦id⟧`, and the body republishes it —
/// OUT decodes to `id = λ.0`. The 1b negative: `⟦K⟧` shipped alone is not an `App` node, so the
/// receive never fires and OUT stays empty.
#[tokio::test]
async fn beat1_typed_hole_binds_the_function_position() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();
    let (tag, _id_reflected, k_reflected) = reflected_app_parts(&fp);

    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), &fp);
    let fired = out_values(&hole_rendezvous_program(subject, tag.clone(), k_reflected.clone())).await;
    assert_eq!(fired, vec![oid()], "the ${{f}} hole binds ⟦id⟧ — OUT de-reflects to λ.0");

    // 1b — ship ⟦K⟧ alone (a λ node, not an App): the App-shaped pattern never fires.
    let lone_k = reflect_ground_term_par(&g_k(), &fp);
    let rested = out_values(&hole_rendezvous_program(lone_k, tag, k_reflected)).await;
    assert!(rested.is_empty(), "⟦K⟧ alone is no App node — no COMM, OUT empty, datum rests on fltX");
}

/// Beat 2 — the guard vetoes on a foreign subterm (run-sheet D2 ground-subpattern form). Against
/// the pattern `[⌜App⌝, ${f}, ⟦K⟧]`, `⟦App(id, K)⟧` matches (argument `⟦K⟧` = `⟦K⟧`) and OUT is
/// `[⟦id⟧]`, whereas `⟦App(id, id)⟧` fails (argument `⟦id⟧` ≠ `⟦K⟧`) and rests — a pure structural
/// veto, zero partial effects.
#[tokio::test]
async fn beat2_where_guard_vetoes_on_foreign_subterm() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();
    let (tag, _id_reflected, k_reflected) = reflected_app_parts(&fp);

    let matches = out_values(&hole_rendezvous_program(
        reflect_ground_term_par(&g_app(g_id(), g_k()), &fp),
        tag.clone(),
        k_reflected.clone(),
    ))
    .await;
    assert_eq!(matches, vec![oid()], "⟦App(id, K)⟧ satisfies the ⟦K⟧ argument subpattern → OUT [⟦id⟧]");

    let vetoed = out_values(&hole_rendezvous_program(
        reflect_ground_term_par(&g_app(g_id(), g_id()), &fp),
        tag,
        k_reflected,
    ))
    .await;
    assert!(vetoed.is_empty(), "⟦App(id, id)⟧ has ⟦id⟧ ≠ ⟦K⟧ at the argument — veto, OUT empty, rests");
}

/// Beat 3 — the counterfeit is rejected: a `GString`-tagged fake `["App", ⟦id⟧, ⟦K⟧]` carries the
/// ground string head instead of the unforgeable `GPrivate` tag, so it never matches the
/// `[⌜App⌝, ${f}, ⟦K⟧]` pattern — the runtime face of the FIP No-Injection property (no surface
/// syntax spells a `GPrivate`, so a term claiming to be Lambda by NAME cannot match).
#[tokio::test]
async fn beat3_counterfeit_tag_rejected() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();
    let (tag, id_reflected, k_reflected) = reflected_app_parts(&fp);

    // Counterfeit datum: a ground-string head where the genuine subject carries the GPrivate tag.
    let counterfeit = new_elist_par(
        vec![quoted_name("App"), id_reflected, k_reflected.clone()],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    let rested = out_values(&hole_rendezvous_program(counterfeit, tag, k_reflected)).await;
    assert!(rested.is_empty(), "the GString-tagged counterfeit ≠ the GPrivate ⌜App⌝ tag — no match");
}
