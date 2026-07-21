//! The Foreign Exchange — phase-now ABI demo (decision D1: `repl/src/bin/flt_demo.rs`).
//!
//! One beat per section, a FRESH in-memory Rho machine per drive, deterministic (the reflected
//! seed is a pure function of the subject + fingerprint; `clear_var_cache` resets binder
//! interning), `SurfaceRenderer` de-reflection for display. Zero production-code changes to the
//! semantics — this bin only READS the public reflect + drive + de-reflection surface.
//!
//! ┌───────────────────────────────────────────────────────────────────────────────────────┐
//! │ REQUIRED Cargo wiring before this bin compiles (see the staging VALIDATION CHECKLIST):  │
//! │   repl/Cargo.toml [dependencies]:  tokio = { workspace = true }   (the drive API is     │
//! │     async; repl has no tokio dep today)                                                 │
//! │   repl/Cargo.toml, an explicit bin stanza so `--no-default-features` builds don't try   │
//! │     to compile it without the de-reflection renderer:                                   │
//! │       [[bin]] name = "flt_demo"  path = "src/bin/flt_demo.rs"                            │
//! │       required-features = ["rho-languages"]                                             │
//! └───────────────────────────────────────────────────────────────────────────────────────┘
//!
//! HONESTY BANNER — what actually runs vs. what is narrated:
//!   * Beat 0 (wire format) and Beats 4/5 (drive to β-NF; Ω fuel witness) RUN on the reducer.
//!   * Beats 1/2/3 (the FLT receive with a typed hole `${f}`, the ground `⟦K⟧` subpattern, the
//!     `where a == ⟦K⟧` guard, the counterfeit rejection) are NARRATED: the `^free`→match-
//!     `FreeVar` hole transform has no public builder today (the pattern reflector
//!     `reflect_term_par_env` is private; only ground `reflect_ground_term_par` is exported), so
//!     their observables are printed as VALIDATE, never claimed as fact. This matches the run
//!     sheet's own framing ("the terminal shows only landed notation; slides narrate the syntax").

use mettail_languages::lambda::LambdaLanguage;
use mettail_repl::observation_surface::SurfaceRenderer;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par, reflected_tag_string, rho_net_drive_call_par,
    rho_net_drive_call_par_with_fuel, suggest_rejected_rule_dispositions, GroundTerm,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    par_as_runtime_observation_value, DriveObservationChannels, PlannedRhoBackend,
};
use mettail_runtime::{clear_var_cache, Language, RuntimeObservationValue};

/// The production `Lambda` Rho-default backend + its definition fingerprint (identical
/// derivation to `rho_net_lambda_firing.rs::lambda_backend`, so the installed program and the
/// reflected tags share one fingerprint).
fn lambda_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaLanguage must expose its definition_source");
    let def =
        reconstruct_language_def(source).expect("LambdaLanguage definition_source must reconstruct");
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

// ── reflected-term (GroundTerm) builders ───────────────────────────────────────────────────
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
/// `K = lam a. lam b. a` (the committed golden).
fn g_k() -> GroundTerm {
    g_lambda(g_lambda(g_bound(1)))
}
fn g_app(fun: GroundTerm, arg: GroundTerm) -> GroundTerm {
    g_node("App", vec![fun, arg])
}

/// De-reflect a ground term to surface syntax (α-fresh binder names — the EXACT spelling is
/// renderer-chosen, hence VALIDATE for goldens; the STRUCTURE is exact).
fn show(renderer: &SurfaceRenderer, fp: &str, term: &GroundTerm) -> String {
    let par = reflect_ground_term_par(term, fp);
    match par_as_runtime_observation_value(&par) {
        Some(value) => renderer
            .render(&value)
            .unwrap_or_else(|err| format!("<de-reflection error: {err}>")),
        None => "<undecodable reflected Par>".to_string(),
    }
}

/// De-reflect an already-decoded observation value (a driver OUT datum) to surface syntax.
fn show_value(renderer: &SurfaceRenderer, value: &RuntimeObservationValue) -> String {
    renderer
        .render(value)
        .unwrap_or_else(|err| format!("<de-reflection error: {err}>"))
}

#[tokio::main]
async fn main() -> Result<(), String> {
    clear_var_cache();
    let (backend, fp) = lambda_backend();
    let renderer = SurfaceRenderer::for_definition_source(
        LambdaLanguage
            .metadata()
            .definition_source()
            .expect("LambdaLanguage exposes its definition_source"),
    )?;

    println!("╔══════════════════════════════════════════════════════════════════════════╗");
    println!("║  The Foreign Exchange — Lambda FLTs over F1r3node RSpace (phase-now, ABI)  ║");
    println!("╚══════════════════════════════════════════════════════════════════════════╝");
    println!("Language fingerprint: {fp}\n");

    beat0_wire_format(&renderer, &fp);
    beat1_ship_and_destructure(&renderer, &fp);
    beat2_where_guard_on_foreign_subterm();
    beat3_counterfeit_rejected(&fp);
    beat4_fill_holes_and_run(&backend, &renderer, &fp).await?;
    beat5_behavioral_predicate_and_omega(&backend, &renderer, &fp).await?;

    Ok(())
}

/// Beat 0 — the wire format existed before the syntax (no run): print `id`, `K`, their reflected
/// tagged-EList head tag, and the de-reflected surface forms.
fn beat0_wire_format(renderer: &SurfaceRenderer, fp: &str) {
    println!("── Beat 0 — the wire format existed before the syntax ──────────────────────");
    println!("  ⌜App⌝  (unforgeable GPrivate tag) = {}", reflected_tag_string(fp, "App"));
    println!("  ⌜^lambda⌝                          = {}", reflected_tag_string(fp, LAMBDA_REFLECT_LABEL));
    println!("  id = ⟦{}⟧   (reflected: EList[GPrivate(⌜^lambda⌝), EList[GPrivate(⌜^bound⌝), Z]])", show(renderer, fp, &g_id()));
    println!("  K  = ⟦{}⟧   (reflected: nested tagged EList, head ⌜^lambda⌝)", show(renderer, fp, &g_k()));
    println!("  (VALIDATE: exact α-fresh binder spelling is renderer-chosen; the STRUCTURE is exact)\n");
}

/// Beat 1 — ship a Lambda FLT; destructure it with a typed hole. NARRATED (the hole receive has
/// no public builder). The subject and the expected observable are printed as VALIDATE.
fn beat1_ship_and_destructure(renderer: &SurfaceRenderer, fp: &str) {
    println!("── Beat 1 — ship an FLT; destructure with a typed hole (NARRATED) ──────────");
    println!("  program: @\"fltX\"!(⟦App(id, K)⟧) | for( @[⌜App⌝, ${{f}}, ⟦K⟧] <- @\"fltX\" ){{ @\"OUT\"!(f) }}");
    println!("    subject shipped:  ⟦App({}, {})⟧", show(renderer, fp, &g_id()), show(renderer, fp, &g_k()));
    println!("    VALIDATE observable:  OUT [⟦id⟧] de-reflected `{}`", show(renderer, fp, &g_id()));
    println!("    VALIDATE negative 1b: ship ⟦K⟧ alone → 0 COMMs, OUT [], datum RESTS on fltX");
    println!("  NOTE: the `${{f}}` typed hole is a match FreeVar at the function position; the");
    println!("        `^free`→FreeVar transform + FLT receive-pattern builder are not public");
    println!("        (only ground reflect_ground_term_par is exported) — see the pinning test.\n");
}

/// Beat 2 — the where-guard vetoes on a foreign subterm. NARRATED (D2: EEq over reflected Pars,
/// or the ground-subpattern fallback from Beat 1).
fn beat2_where_guard_on_foreign_subterm() {
    println!("── Beat 2 — the where-guard vetoes on a foreign subterm (NARRATED) ─────────");
    println!("  program: for( @[⌜App⌝, ${{f}}, ${{a}}] <- @\"fltX\" where a == ⟦K⟧ ){{ @\"OUT\"!(f) }}");
    println!("    VALIDATE: ship ⟦App(id, id)⟧ → OUT [], datum resting (guard veto, zero effects)");
    println!("    VALIDATE: ship ⟦App(id, K)⟧  → OUT [⟦id⟧]");
    println!("  Fallback (D2): if EEq over reflected Pars misbehaves, use the ground-subpattern");
    println!("        form (`…${{f}}, ⟦K⟧]` vs `…${{f}}, ⟦id⟧]`) — identical veto via pure shape.\n");
}

/// Beat 3 — the counterfeit is rejected: tags are unforgeable. NARRATED.
fn beat3_counterfeit_rejected(fp: &str) {
    println!("── Beat 3 — the counterfeit is rejected: tags are unforgeable (NARRATED) ───");
    println!("  A GString-tagged fake [\"App\", ⟦id⟧, ⟦K⟧] at the same receive.");
    println!("    the genuine head is the private name  {}", reflected_tag_string(fp, "App"));
    println!("    the counterfeit head is the ground string  \"App\"  — a DIFFERENT Par shape");
    println!("    VALIDATE: no match; the datum rests (tags compared by identity, not spelling).");
    println!("  This is the runtime face of the FIP No-Injection property: no syntax spells a");
    println!("        GPrivate, so a term claiming to be Lambda by NAME cannot match.\n");
}

/// Beat 4 (core) — fill the holes and RUN it: the subject `App(id, K)` drives to β-NF `K` fully
/// in-Rho. RUNS. The FLT-rendezvous wrapper that would capture `f`/`k` from a hole and feed this
/// drive is the narrated (non-wireable) part; the drive itself is the "wow".
async fn beat4_fill_holes_and_run(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 4 — fill the holes and RUN it: quotation to β-normal form (RUNS) ───");
    let subject = g_app(g_id(), g_k());
    let seed = rho_net_drive_call_par(fp, reflect_ground_term_par(&subject, fp), "OUT");
    let channels = DriveObservationChannels::for_fingerprint(fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await?;

    for value in &set.out_values {
        println!("  OUT observes ⟦{}⟧   (β-normal form of App(id, K))", show_value(renderer, value));
    }
    println!("  ^fired ledger: {:?}", set.fired_labels()?);
    println!("  ^drive-err: {} datum(a) | ^drive-fuel: {} datum(a)  (both expected empty)", set.err_data.len(), set.fuel_data.len());
    println!("  → drives to K = `lam a. lam b. a` (VALIDATE exact spelling), fired [\"Beta\"].\n");
    Ok(())
}

/// Beat 5 — the behavioral predicate, honestly; the Ω fuel witness. RUNS the Ω half (fuel
/// exhaustion typed + fail-closed); NARRATES the drive-then-match re-ship (needs the hole receive).
async fn beat5_behavioral_predicate_and_omega(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 5 — the behavioral predicate, honestly; the Ω witness ──────────────");
    println!("  NARRATED positive: producer ⟦App(id,K)⟧ | consumer1 drives to nf | consumer2");
    println!("        matches @[⌜^lambda⌝, ${{b}}] → VALIDATE OUT [⟦K⟧] (inter-FLT re-ship).");

    // The Ω negative RUNS: a small per-path fuel exhausts, typed and fail-closed.
    let omega_half = g_lambda(g_app(g_bound(0), g_bound(0)));
    let omega = g_app(omega_half.clone(), omega_half);
    let seed = rho_net_drive_call_par_with_fuel(fp, reflect_ground_term_par(&omega, fp), 3, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await?;

    println!("  Ω = (λx.x x)(λx.x x), per-path fuel 3 (RUNS):");
    println!("    ^fired ledger: {:?}  (exactly per-path-fuel firings)", set.fired_labels()?);
    println!("    ^drive-fuel: {} typed exhaustion datum (the stuck redex Ω)", set.fuel_data.len());
    if let Some(stuck) = set.fuel_data.first().and_then(par_as_runtime_observation_value) {
        println!("      stuck redex = ⟦{}⟧", show_value(renderer, &stuck));
    }
    println!("    OUT: {} value(s)  (exhaustion NEVER claims an NF)", set.out_values.len());
    println!("  → fuel exhaustion is typed, fail-closed; nf empty; consumer2 never fires, OUT [].\n");
    Ok(())
}
