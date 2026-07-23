//! The Foreign Exchange — pinning-test twin for `demos/flt-foreign-exchange/RUN-SHEET.md`
//! (phase-now, ABI level). The task-#8 integration pattern: each SOLID beat asserts its
//! observable on a fresh in-memory f1r3node RSpace, so a recording and a live run match.
//!
//! This suite is the drive/ABI half of the demo. It reuses the proven machinery of the
//! sibling `rho_net_lambda_firing.rs` (the production `Lambda` driven to quiescence FULLY
//! in-Rho by the generated `^drive` receiver family): the reflected-term ABI, the drive seed,
//! and the four observation channels ([`DriveObservationChannels`]).
//!
//! ── What is SOLID here (asserted as fact) — every PRIMARY beat RUNS + is pinned ─────────────
//!   * Beat 0 — the wire format: the reflected tagged-EList forms of `id` / `K` round-trip
//!     through `par_as_runtime_observation_value`, and the per-language tag string is the
//!     `mettail.term.{fp}.{label}` unforgeable-`GPrivate` name (rho_net_lower.rs:1710-1715).
//!   * Beats 1/2/3 — the typed-hole FLT receive (see the matcher-contract note below): the hole
//!     binds ⟦id⟧ (Beat 1), the ground `⟦K⟧` subpattern vetoes a foreign argument (Beat 2, the D2
//!     marker-wildcarded form), and the unforgeable `⌜App⌝` tag rejects a 4-element GString-tagged
//!     counterfeit that differs ONLY at the head (Beat 3 — pure No-Injection).
//!   * Beat 4 (core) — fill-holes-and-RUN, direct seed: the subject `App(id, K)` drives to β-NF
//!     `K` in-Rho, the `^fired` ledger records exactly `["Beta"]`, and `^drive-err`/`^drive-fuel`
//!     stay empty. (Byte-for-byte the shape of `single_beta_drives_to_nf_in_rho`.)
//!   * Beat 4 (re-quote from holes) — the SAME NF, but the drive seed is BUILT FROM THE CAPTURED
//!     HOLES: a receiver captures `f`,`k`, re-quotes `[⌜App⌝, ⌜^nog⌝, f, k]` (marker forced ⌜^nog⌝,
//!     the C2 semantic fix), seeds `^drive`, and drives to ⟦K⟧ with `^fired = ["Beta"]`.
//!   * Beat 5 (positive) — the same-language inter-FLT re-ship: `⟦App(id, K)⟧` driven to its λ-NF
//!     and re-shipped, then destructured + re-wrapped by a second consumer — OUT rests at ⟦K⟧.
//!   * Beat 5 (Ω) — fuel exhaustion is typed and fail-closed: Ω fires exactly per-path-fuel
//!     times, the stuck redex rests on `^drive-fuel`, and OUT never claims an NF.
//!
//! ── The typed-hole FLT receive, hand-built against the matcher contract ─────────────────────
//!   The FLT receive-with-typed-hole (`for( @[⌜App⌝, _, ${f}, ⟦K⟧] <- @"fltX" ){…}`, E-2-D v2 —
//!   the `_` wildcards the index-1 groundness marker) needs a receive whose `BindPattern` is a
//!   reflected EList carrying a `FreeVar` at the hole and a GROUND reflected subterm elsewhere. No
//!   PUBLIC reflector emits such a pattern — `reflect_ground_term_par` is ground-only, and
//!   `reflect_term_par_env` (rho_net_lower.rs:3607) is private and emits σ-slot `BoundVar`s, not
//!   receive `FreeVar`s. But the pattern is realizable TEST-SIDE with the `models` builders
//!   (mirroring the proven in-tree `e6a_support::discovery_call_par` receive shape): a reflected
//!   tagged-EList whose head is the unforgeable `GPrivate` tag (built via [`reserved_tag_par`], the
//!   production `tag_par` construction reached through the public `reflected_tag_string`), whose
//!   marker slot is a `Wildcard`, whose hole positions are `EVar(FreeVar(_))`, and whose ground
//!   positions are ground reflected subterms. This lands every beat on the reducer with ZERO
//!   production change (no reflector API is exposed) — the honest phase-now bridge; the refined
//!   `${x}` syntax GENERATES this same shape through a public reflector API in phase-2.
#![cfg(feature = "lambda-runtime")]

use std::collections::BTreeMap;

use mettail_languages::lambda::LambdaLanguage;
use mettail_rholang_codegen::{
    ground_marker_tag_par, lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_flt_construction, reflect_ground_term_par, reflected_tag_string, rho_net_drive_call_par,
    rho_net_drive_call_par_with_fuel, suggest_rejected_rule_dispositions, GroundTerm,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    BOUND_VAR_REFLECT_LABEL, DRIVE_DEFAULT_FUEL, DRIVE_RESERVED_LABEL, FREE_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, NONGROUND_MARK_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
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
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gint_par, new_gstring_par,
    new_receive_par, new_send_par, new_wildcard_par,
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
/// A `^free(name)` hole/free leaf — exactly as the guest `Term → GroundTerm` reflector emits it
/// (and as the public `reflect_flt_*` reflectors consume it).
fn g_free(name: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(name)])
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

/// The reflected `(⌜App⌝, ⌜^nog⌝, ⟦id⟧, ⟦K⟧)` quadruple decomposed from `⟦App(id, K)⟧`
/// (`EList[GPrivate(⌜App⌝), GPrivate(⌜^nog⌝), ⟦id⟧, ⟦K⟧]`) — the unforgeable head tag, the E-2-D
/// index-1 hereditary-ground MARKER (`⌜^nog⌝`, since `App(id, K)` is a closed λ-term), and the two
/// ground children.
fn reflected_app_parts(fp: &str) -> (Par, Par, Par, Par) {
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);
    match subject.exprs.first().and_then(|e| e.expr_instance.as_ref()) {
        // E-2-D (reflected-ABI v2): ⟦App(id, K)⟧ = [App_tag, ^nog, ⟦id⟧, ⟦K⟧] — the hereditary-
        // ground marker sits at index 1, so the head tag / marker / id / K are ps[0..4].
        Some(ExprInstance::EListBody(list)) => (
            list.ps[0].clone(),
            list.ps[1].clone(),
            list.ps[2].clone(),
            list.ps[3].clone(),
        ),
        other => panic!("⟦App(id, K)⟧ must reflect to a 4-element EList (marker at 1), got {other:?}"),
    }
}

/// The reserved unforgeable `GPrivate` tag `⌜label⌝` for fingerprint `fp` — assembled the SAME way
/// the production emitter does (`rho_net_subst_trs::tag_par` =
/// `GPrivateBuilder::new_par_from_string(reflect_tag(fp, label))`), reached here through the PUBLIC
/// [`reflected_tag_string`]. This is the honest phase-now hand-build of the tags a `${x}`-syntax
/// reflector emits in phase-2 — `⌜App⌝`, `⌜^lambda⌝`, the `⌜^nog⌝` marker, and the `⌜^drive⌝`
/// rendezvous — byte-identical to what the installed driver family matches and seeds on.
fn reserved_tag_par(fp: &str, label: &str) -> Par {
    GPrivateBuilder::new_par_from_string(reflected_tag_string(fp, label))
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
    let (tag, _marker, _id_reflected, k_reflected) = reflected_app_parts(&fp);

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
    let (tag, _marker, _id_reflected, k_reflected) = reflected_app_parts(&fp);

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

/// Beat 3 — the counterfeit is rejected: a 4-element `GString`-tagged fake
/// `["App", ⌜^nog⌝, ⟦id⟧, ⟦K⟧]` is byte-for-byte the genuine `⟦App(id, K)⟧` EXCEPT the head — a
/// ground string `"App"` where the real subject carries the unforgeable `⌜App⌝` `GPrivate`. It
/// matches the marked pattern's 4-element arity, its wildcarded marker slot (index 1), and the
/// ground `⟦K⟧` at the argument, so the ONLY discriminant is the head tag: the rejection is a PURE
/// unforgeable-tag failure, not an incidental arity/shape mismatch — the runtime face of the FIP
/// No-Injection property (no surface syntax spells a `GPrivate`, so a term claiming to be Lambda by
/// NAME cannot match).
#[tokio::test]
async fn beat3_counterfeit_tag_rejected() {
    mettail_runtime::clear_var_cache();
    let (_backend, fp) = lambda_backend();
    let (tag, marker, id_reflected, k_reflected) = reflected_app_parts(&fp);

    // The 4-element counterfeit `["App", ⌜^nog⌝, ⟦id⟧, ⟦K⟧]`: the genuine `⌜^nog⌝` marker (so the
    // wildcarded marker slot matches), the ground `⟦id⟧`/`⟦K⟧` children, and a GString `"App"` head
    // in place of the `GPrivate` `⌜App⌝`. Everything but index 0 is byte-identical to the real
    // subject, isolating the rejection to the unforgeable tag.
    let counterfeit = new_elist_par(
        vec![quoted_name("App"), marker, id_reflected, k_reflected.clone()],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    let rested = out_values(&hole_rendezvous_program(counterfeit, tag, k_reflected)).await;
    assert!(rested.is_empty(), "the GString-tagged counterfeit ≠ the GPrivate ⌜App⌝ tag — no match");
}

// ── Beat 4 (re-quote from holes) — fill the holes and RUN: capture f,k, re-quote, drive to β-NF ──
//
// The FULL run-sheet Beat 4 wired end-to-end: a receiver captures the two App holes `f`,`k` (the
// marker slot wildcarded), RE-QUOTES `[⌜App⌝, ⌜^nog⌝, f, k]` at CONSTRUCTION position, then seeds
// the installed `^drive` quiescence driver, which fires β and re-drives the contractum to the β-NF
// ⟦K⟧. Two E-2-D correctness constraints make the re-quote SEMANTIC, not cosmetic (RUN-SHEET §Beat
// 4 / design §6 C2): (1) a 3-element `[⌜App⌝, f, k]` omitting the index-1 marker slot would not
// match the driver's marked App redex arm (`pat_tagged`, which expects `[tag, marker, args…]`), so
// β never fires; (2) hard-coding `⌜^gnd⌝` over the holes would let the hereditary-ground guard
// short-circuit subst to the identity, so β silently would not fire on a binder-carrying fill.
// Forcing `⌜^nog⌝` is both necessary and conservatively sound (a fill only makes a node LESS
// ground — `InRhoCreeperTrace.oground`). The direct-seed `beat4_app_id_k_drives_to_konst_in_rho`
// proves the SAME NF from a hand-built seed; here the seed is BUILT FROM THE CAPTURED HOLES.

/// Assemble `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${f}, ${k}] <- @"fltX" ){
/// ⌜^drive⌝!( [⌜App⌝, ⌜^nog⌝, f, k], fuel, "OUT" ) }`. The receive binds two holes — `${f}` =
/// `FreeVar(0)` (index 2), `${k}` = `FreeVar(1)` (index 3), the marker slot (index 1) absorbed by a
/// wildcard — so in the continuation `f` = `BoundVar(1)` and `k` = `BoundVar(0)` (the innermost free
/// var is `BoundVar(0)`: the [`Env::root`] convention the codegen drivers share with the reducer).
/// The body re-quotes the App with the marker slot forced to `⌜^nog⌝` and seeds `⌜^drive⌝` with the
/// production per-path fuel and the "OUT" return label.
fn requote_and_drive_program(fp: &str) -> Par {
    let app_tag = reserved_tag_par(fp, "App");
    let nog = reserved_tag_par(fp, NONGROUND_MARK_REFLECT_LABEL);
    let drive_chan = reserved_tag_par(fp, DRIVE_RESERVED_LABEL);
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);

    let producer =
        new_send_par(quoted_name("fltX"), vec![subject], false, Vec::new(), false, Vec::new(), false);

    // Pattern `[⌜App⌝, _, ${f}, ${k}]` — wildcard the E-2-D marker (index 1); FreeVar(0)=f at index
    // 2, FreeVar(1)=k at index 3. The wildcard + FreeVars make the EList (and its Par) connective-used.
    let pattern = new_elist_par(
        vec![
            app_tag.clone(),
            new_wildcard_par(Vec::new(), true),
            new_freevar_par(0, Vec::new()),
            new_freevar_par(1, Vec::new()),
        ],
        Vec::new(),
        true,
        None,
        Vec::new(),
        true,
    );
    // Re-quote `[⌜App⌝, ⌜^nog⌝, f, k]` — a CONSTRUCTION (not a pattern): `f`=BoundVar(1),
    // `k`=BoundVar(0), so its free-set is {0, 1}; no connective.
    let requote = new_elist_par(
        vec![
            app_tag,
            nog,
            new_boundvar_par(1, create_bit_vector(&[1]), false),
            new_boundvar_par(0, create_bit_vector(&[0]), false),
        ],
        create_bit_vector(&[0, 1]),
        false,
        None,
        create_bit_vector(&[0, 1]),
        false,
    );
    // Body `⌜^drive⌝!( <re-quote>, fuel, "OUT" )` — the SAME seed shape as
    // `rho_net_drive_call_par(fp, ⟦App(id, K)⟧, "OUT")`, but its subject is built from the holes.
    let body = new_send_par(
        drive_chan,
        vec![
            requote,
            new_gint_par(DRIVE_DEFAULT_FUEL, Vec::new(), false),
            new_gstring_par("OUT".to_string(), Vec::new(), false),
        ],
        false,
        create_bit_vector(&[0, 1]),
        false,
        create_bit_vector(&[0, 1]),
        false,
    );
    let receive = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![pattern],
            source: Some(quoted_name("fltX")),
            remainder: None,
            free_count: 2,
        }],
        body,
        false,
        false,
        2,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    producer.append(receive)
}

/// Beat 4 (re-quote from holes) — the FLT rendezvous fills the holes and RUNS: a receiver captures
/// `f`,`k` from `⟦App(id, K)⟧`, re-quotes `[⌜App⌝, ⌜^nog⌝, f, k]`, and seeds the installed driver,
/// which fires β and re-drives the contractum to β-NF `⟦K⟧` — `^fired` records exactly `["Beta"]`
/// and both fail-close channels stay empty. Composed as the dynamic `call` on the backend's
/// installed `^drive` receiver family, exactly like the direct-seed Beat-4 core.
#[tokio::test]
async fn beat4_requote_from_holes_drives_to_konst_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let program = requote_and_drive_program(&fp);
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&program, &channels)
        .await
        .expect("the re-quote-from-holes rendezvous drives to quiescence on the reducer");

    assert_eq!(set.out_values, vec![okonst()], "the hole-filled App re-quote drives to K = λ.λ.1");
    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string()],
        "exactly one Beta firing — the re-quote matched the marked App redex arm and fired"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head — the ⌜^nog⌝ re-quote is well-formed v2");
    assert!(set.fuel_data.is_empty(), "the drive terminated by quiescence, not fuel");
    drive_cross_check(&set, &channels, true, DRIVE_DEFAULT_FUEL, &lambda_redex_scan)
        .expect("the always-on drive cross-check is green");
}

// ── Beat 4 (P2 construction) — reflect_flt_construction drives β: the C2 forced-^nog, on RSpace ──
//
// The Phase-2 PUBLIC construction reflector `reflect_flt_construction` GENERATES the same
// hole-filled App value the hand-built Beat-4 re-quote staples by hand — but with the E-2-D marker
// RECOMPUTED (C2) from the FILLED subtree's own ground bit, never a template `^gnd`. Both fills
// (⟦id⟧, ⟦K⟧) carry `^bound`, so the App marker recomputes to `⌜^nog⌝` and the subject is
// byte-for-byte the direct-seed `⟦App(id, K)⟧`, so it drives β to the β-NF ⟦K⟧. The negative probe
// staples the stale `⌜^gnd⌝` back over the SAME children and shows the drive no longer reaches ⟦K⟧ —
// the operational proof that recompute is NECESSARY, not cosmetic.

/// Beat 4 (P2) — `reflect_flt_construction(App(${f}, ${k}), {f: ⟦id⟧, k: ⟦K⟧})` recomputes the App
/// marker to `⌜^nog⌝` and drives to β-NF `K = λ.λ.1` fully in-Rho, `^fired = ["Beta"]`, both
/// fail-close channels empty — the public reflector reproducing the direct-seed Beat-4 core.
#[tokio::test]
async fn beat4_flt_construction_forces_nog_and_drives_beta() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let fills: BTreeMap<String, Par> = [
        ("f".to_string(), reflect_ground_term_par(&g_id(), &fp)),
        ("k".to_string(), reflect_ground_term_par(&g_k(), &fp)),
    ]
    .into_iter()
    .collect();
    let template = g_node("App", vec![g_free("f"), g_free("k")]);
    let subject =
        reflect_flt_construction(&template, &fills, &fp).expect("the FLT App construction reflects");

    // C2: the RECOMPUTED App marker is ⌜^nog⌝ (both fills carry ^bound).
    match subject.exprs.first().and_then(|e| e.expr_instance.as_ref()) {
        Some(ExprInstance::EListBody(list)) => assert_eq!(
            list.ps[1],
            ground_marker_tag_par(&fp, false),
            "the constructed App marker must be recomputed ⌜^nog⌝, not a stale ⌜^gnd⌝"
        ),
        other => panic!("the constructed App must be a 4-element EList, got {other:?}"),
    }
    // Byte-for-byte the direct-seed subject (the Stage-2 round-trip, asserted on the reducer side).
    assert_eq!(
        subject,
        reflect_ground_term_par(&g_app(g_id(), g_k()), &fp),
        "the FLT construction is byte-identical to ⟦App(id, K)⟧"
    );

    let seed = rho_net_drive_call_par(&fp, subject, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the FLT-constructed App drives to quiescence on the reducer");

    assert_eq!(set.out_values, vec![okonst()], "the ⌜^nog⌝ construction drives to K = λ.λ.1");
    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string()],
        "exactly one Beta firing — the recomputed ⌜^nog⌝ App matched the marked redex arm and fired"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head — the construction is well-formed v2");
    assert!(set.fuel_data.is_empty(), "the drive terminated by quiescence, not fuel");
    drive_cross_check(&set, &channels, true, DRIVE_DEFAULT_FUEL, &lambda_redex_scan)
        .expect("the always-on drive cross-check is green");
}

/// Beat 4 (P2, C2 NECESSITY) — the reducer mechanism C2's recompute guards against, on RSpace.
///
/// A `^gnd`/`^nog` marker only GOVERNS a reduction when its node is a `^subst`/`^shift` TARGET —
/// i.e. a marked node NESTED inside a β-redex's lambda body (a TOP-LEVEL redex node's marker is
/// wildcarded by the driver's redex arm and is inert). The minimal such witness:
/// `App(^lambda(App(^bound(0), K)), id)` — the outer β substitutes `id` into the inner body
/// `App(^bound(0), K)`, whose marker MUST be `^nog` (it carries `^bound`) for the substitution to
/// reach the `^bound(0)`.
///
///   * CORRECT (`^nog` inner App, what `reflect_flt_construction` recomputes): the substitution
///     replaces `^bound(0)` with `id`, giving `App(id, K)`, which re-drives to β-NF `K`.
///   * STALE `^gnd` inner App (the C2 bug the recompute prevents): the hereditary-ground guard
///     short-circuits `^subst` to the IDENTITY, so `^bound(0)` is NOT replaced — the drive rests at
///     the dangling `App(^bound(0), K)`, never `K`.
///
/// `reflect_flt_construction` recomputes exactly these `^nog` markers (proven `^nog` +
/// β-firing in [`beat4_flt_construction_forces_nog_and_drives_beta`] and structurally in the
/// codegen `reflect_flt_construction_recomputes_marker_from_the_fill` test), so it never emits the
/// stale-`^gnd` term whose divergence this test pins.
#[tokio::test]
async fn beat4_flt_construction_c2_marker_governs_nested_beta() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    // `App(^lambda(App(^bound(0), K)), id)` — all markers correct (^nog wherever ^bound occurs).
    let nested = g_app(g_lambda(g_app(g_bound(0), g_k())), g_id());
    let correct = reflect_ground_term_par(&nested, &fp);

    let correct_set = backend
        .run_rho_net_with_call_and_read_observation_set(
            &rho_net_drive_call_par(&fp, correct.clone(), "OUT"),
            &DriveObservationChannels::for_fingerprint(&fp, "OUT"),
        )
        .await
        .expect("the correct nested term drives to quiescence");
    assert_eq!(
        correct_set.out_values,
        vec![okonst()],
        "the ^nog inner App lets the outer β reach ^bound(0): App(id, K) → K = λ.λ.1"
    );

    // The SAME term with the inner body App's marker stapled back to the stale ⌜^gnd⌝.
    let mut corrupted = correct;
    *nested_marker_mut(&mut corrupted, &[2, 2]) = ground_marker_tag_par(&fp, true);

    let corrupted_set = backend
        .run_rho_net_with_call_and_read_observation_set(
            &rho_net_drive_call_par(&fp, corrupted, "OUT"),
            &DriveObservationChannels::for_fingerprint(&fp, "OUT"),
        )
        .await
        .expect("the stale-^gnd term drives to rest");
    assert_ne!(
        corrupted_set.out_values,
        vec![okonst()],
        "a stale ⌜^gnd⌝ on the substitution-target App short-circuits ^subst — β never reaches K"
    );
}

/// Descend a reflected-object `Par` along `path` of child indices into its `EList.ps`, returning a
/// mutable handle to the DEEPEST node's index-1 E-2-D marker slot. `path` names the child index at
/// each level (index 0 = head tag, 1 = marker, ≥2 = children).
fn nested_marker_mut<'a>(par: &'a mut Par, path: &[usize]) -> &'a mut Par {
    fn ps_mut(par: &mut Par) -> &mut Vec<Par> {
        match par.exprs.first_mut().and_then(|e| e.expr_instance.as_mut()) {
            Some(ExprInstance::EListBody(list)) => &mut list.ps,
            other => panic!("expected a reflected EList node, got {other:?}"),
        }
    }
    let mut node = par;
    for &index in path {
        node = &mut ps_mut(node)[index];
    }
    &mut ps_mut(node)[1]
}

// ── Beat 5 (positive) — the same-language inter-FLT re-ship: NF produced by one FLT, matched by ──
//   another. Producer ships `⟦App(id, K)⟧`; consumer 1 drives it to its λ-NF and RE-SHIPS on `nf`;
//   consumer 2 destructures the λ (marker wildcarded), RE-WRAPS it (marker forced `⌜^nog⌝` — the
//   same E-2-D physics as Beat 4: a 3-element `[⌜^lambda⌝, b]` neither matches the marked `^lambda`
//   layout nor re-ships as a well-formed reflected λ), and publishes to `OUT`. Honest scope: this
//   is a same-language, same-binder-depth identity re-wrap; the hard cross-language binder hole is
//   the phase-3 co-install spike, not this beat.

/// Assemble `@"fltX"!(⟦App(id, K)⟧) | for(@${t} <- @"fltX"){ ⌜^drive⌝!(t, fuel, "nf") } |
/// for(@[⌜^lambda⌝, _, ${b}] <- @"nf"){ @"OUT"!([⌜^lambda⌝, ⌜^nog⌝, b]) }`. Consumer 1's whole-term
/// hole `${t}` = `FreeVar(0)` ⟹ `BoundVar(0)` in its body; the driver publishes the NF to the GString
/// `@"nf"` (its "nf" return label). Consumer 2's `${b}` = `FreeVar(0)` (the λ body) ⟹ `BoundVar(0)`.
fn inter_flt_reship_program(fp: &str) -> Par {
    let lambda_tag = reserved_tag_par(fp, LAMBDA_REFLECT_LABEL);
    let nog = reserved_tag_par(fp, NONGROUND_MARK_REFLECT_LABEL);
    let drive_chan = reserved_tag_par(fp, DRIVE_RESERVED_LABEL);
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);

    // Producer: @"fltX"!(⟦App(id, K)⟧).
    let producer =
        new_send_par(quoted_name("fltX"), vec![subject], false, Vec::new(), false, Vec::new(), false);

    // Consumer 1: for(@${t} <- @"fltX"){ ⌜^drive⌝!(t, fuel, "nf") } — capture the WHOLE FLT (a bare
    // FreeVar(0)), then seed the driver with the "nf" return label. In the body t = BoundVar(0).
    let consumer1 = {
        let drive_seed = new_send_par(
            drive_chan,
            vec![
                new_boundvar_par(0, create_bit_vector(&[0]), false),
                new_gint_par(DRIVE_DEFAULT_FUEL, Vec::new(), false),
                new_gstring_par("nf".to_string(), Vec::new(), false),
            ],
            false,
            create_bit_vector(&[0]),
            false,
            create_bit_vector(&[0]),
            false,
        );
        new_receive_par(
            vec![ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(quoted_name("fltX")),
                remainder: None,
                free_count: 1,
            }],
            drive_seed,
            false,
            false,
            1,
            Vec::new(),
            false,
            Vec::new(),
            false,
        )
    };

    // Consumer 2: for(@[⌜^lambda⌝, _, ${b}] <- @"nf"){ @"OUT"!([⌜^lambda⌝, ⌜^nog⌝, b]) } — match the
    // λ NF (marker wildcarded at index 1, ${b}=FreeVar(0) the body at index 2), re-wrap with the
    // marker forced ⌜^nog⌝, publish to OUT. In the body b = BoundVar(0).
    let consumer2 = {
        let pattern = new_elist_par(
            vec![
                lambda_tag.clone(),
                new_wildcard_par(Vec::new(), true),
                new_freevar_par(0, Vec::new()),
            ],
            Vec::new(),
            true,
            None,
            Vec::new(),
            true,
        );
        let rewrap = new_elist_par(
            vec![lambda_tag, nog, new_boundvar_par(0, create_bit_vector(&[0]), false)],
            create_bit_vector(&[0]),
            false,
            None,
            create_bit_vector(&[0]),
            false,
        );
        let body = new_send_par(
            quoted_name("OUT"),
            vec![rewrap],
            false,
            create_bit_vector(&[0]),
            false,
            create_bit_vector(&[0]),
            false,
        );
        new_receive_par(
            vec![ReceiveBind {
                patterns: vec![pattern],
                source: Some(quoted_name("nf")),
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
        )
    };

    producer.append(consumer1).append(consumer2)
}

/// Beat 5 (positive) — the SAME-LANGUAGE inter-FLT re-ship: `⟦App(id, K)⟧` shipped on `fltX`, driven
/// to its λ-NF and re-shipped on `nf` by consumer 1, then destructured, re-wrapped, and published to
/// `OUT` by consumer 2. OUT rests at `⟦K⟧` — a normal form produced by one FLT interaction, matched
/// and re-emitted by another (the runtime-mandate's inter-FLT communication, live). Consumer 1's
/// drive fires exactly one Beta with both fail-close channels empty.
#[tokio::test]
async fn beat5_inter_flt_reship_positive() {
    mettail_runtime::clear_var_cache();
    let (backend, fp) = lambda_backend();

    let program = inter_flt_reship_program(&fp);
    let channels = DriveObservationChannels::for_fingerprint(&fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&program, &channels)
        .await
        .expect("the inter-FLT re-ship runs to rest on the reducer");

    assert_eq!(set.out_values, vec![okonst()], "the re-shipped λ-NF rests at K = λ.λ.1 on OUT");
    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string()],
        "consumer 1's drive fired exactly one Beta"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head on consumer 1's drive");
    assert!(set.fuel_data.is_empty(), "consumer 1's drive terminated by quiescence, not fuel");
}
