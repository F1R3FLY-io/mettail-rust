//! The Foreign Exchange — phase-now ABI demo (decision D1: `repl/src/bin/flt_demo.rs`).
//!
//! One beat per section, a FRESH in-memory Rho machine per drive (`clear_var_cache` resets binder
//! interning before each), deterministic (the reflected seed is a pure function of the subject +
//! fingerprint), `SurfaceRenderer` de-reflection for display. Zero production-code changes to the
//! semantics — this bin only READS the public reflect + drive + de-reflection surface and
//! HAND-BUILDS the FLT receive patterns with the `models` `Par` builders.
//!
//! HONESTY BANNER — what runs vs. what is deferred:
//!   * Every PRIMARY beat RUNS LIVE on the reducer: Beat 0 (the wire format), Beats 1/2/3 (the
//!     typed-hole FLT receive, the D2 ground-subpattern veto, the unforgeable-tag rejection),
//!     Beat 4 (fill the holes and drive to β-NF), Beat 5-positive (the inter-FLT re-ship), and the
//!     Beat-5 Ω fuel witness. The receive patterns are HAND-BUILT here with the `models` builders —
//!     the SAME honest technique the pinning twin (`rholang-runtime/tests/flt_abi_over_rspace.rs`)
//!     uses; the refined `${x}` syntax GENERATES this same reflected shape through a public
//!     reflector API in phase-2 (`f` here is what that syntax spells `${f}` — same AST position,
//!     different ink). No `^free`→`FreeVar` reflector is exposed, so nothing here is faked: the
//!     patterns are assembled directly against the matcher contract.
//!   * DEFERRED to after the primary demo (USER decision 1): the live-trace Beat 4b (StepSession +
//!     the τ-classifier) and the secondary openers (the stock-Rholang strawman cameo; the
//!     Settlement Desk bridge). They are NOT stubbed or faked — see `deferred_after_primary`.

use mettail_languages::lambda::LambdaLanguage;
use mettail_repl::observation_surface::SurfaceRenderer;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par, reflected_tag_string, rho_net_drive_call_par_with_fuel,
    suggest_rejected_rule_dispositions, GroundTerm, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence, BOUND_VAR_REFLECT_LABEL,
    DRIVE_DEFAULT_FUEL, DRIVE_RESERVED_LABEL, LAMBDA_REFLECT_LABEL, NONGROUND_MARK_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    par_as_runtime_observation_value, DriveObservationChannels, DriveObservationSet,
    PlannedRhoBackend,
};
use mettail_runtime::{clear_var_cache, Language, RuntimeObservationValue};
use models::create_bit_vector;
use models::rhoapi::{Par, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gint_par, new_gstring_par,
    new_receive_par, new_send_par, new_wildcard_par,
};

/// The production `Lambda` Rho-default backend + its definition fingerprint (identical
/// derivation to `rho_net_lambda_firing.rs::lambda_backend`, so the installed program and the
/// reflected tags share one fingerprint).
fn lambda_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("LambdaLanguage definition_source must reconstruct");
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

// ── hand-built FLT-receive builders — IDENTICAL to the pinning twin's, the same honest phase-now ──
//   technique (the `models` `Par` builders against the matcher contract). See
//   `rholang-runtime/tests/flt_abi_over_rspace.rs`, which PINS the observables these RUN.

/// The reserved unforgeable `GPrivate` tag `⌜label⌝` for fingerprint `fp` — assembled the SAME way
/// the production emitter does (`rho_net_subst_trs::tag_par` =
/// `GPrivateBuilder::new_par_from_string(reflect_tag(fp, label))`), reached here through the PUBLIC
/// [`reflected_tag_string`]. `⌜App⌝`, `⌜^lambda⌝`, the `⌜^nog⌝` marker, and the `⌜^drive⌝`
/// rendezvous are byte-identical to what the installed driver family matches and seeds on.
fn reserved_tag_par(fp: &str, label: &str) -> Par {
    GPrivateBuilder::new_par_from_string(reflected_tag_string(fp, label))
}

fn quoted_name(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// `@"fltX"!(subject) | for( @[⌜App⌝, _, ${f}, ground_arg] <- @"fltX" ){ @"OUT"!(f) }` — the receive
/// `BindPattern` is the reflected tagged-EList wildcarding the E-2-D marker (index 1), a `FreeVar`
/// hole at the function position (index 2), and a GROUND subterm at the argument (index 3); the body
/// republishes the bound hole (`BoundVar(0)`) to `@"OUT"`. Serves Beats 1, 2 (D2), and 3.
fn hole_rendezvous_program(subject: Par, tag: Par, ground_arg: Par) -> Par {
    let producer = new_send_par(
        quoted_name("fltX"),
        vec![subject],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    let pattern = new_elist_par(
        vec![
            tag,
            new_wildcard_par(Vec::new(), true),
            new_freevar_par(0, Vec::new()),
            ground_arg,
        ],
        Vec::new(),
        true,
        None,
        Vec::new(),
        true,
    );
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

/// `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${f}, ${k}] <- @"fltX" ){
/// ⌜^drive⌝!( [⌜App⌝, ⌜^nog⌝, f, k], fuel, "OUT" ) }`. Two holes — `${f}`=`FreeVar(0)` (index 2),
/// `${k}`=`FreeVar(1)` (index 3), the marker slot wildcarded — so in the continuation `f`=`BoundVar(1)`
/// and `k`=`BoundVar(0)` (the innermost free var is `BoundVar(0)`). The body re-quotes with the
/// marker forced `⌜^nog⌝` (the C2 semantic fix: a 3-element re-quote or a hard-coded `⌜^gnd⌝` would
/// silently NOT β-fire) and seeds `⌜^drive⌝` with the production fuel + the "OUT" return label.
fn requote_and_drive_program(fp: &str) -> Par {
    let app_tag = reserved_tag_par(fp, "App");
    let nog = reserved_tag_par(fp, NONGROUND_MARK_REFLECT_LABEL);
    let drive_chan = reserved_tag_par(fp, DRIVE_RESERVED_LABEL);
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);

    let producer = new_send_par(
        quoted_name("fltX"),
        vec![subject],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
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

/// `@"fltX"!(⟦App(id, K)⟧) | for(@${t} <- @"fltX"){ ⌜^drive⌝!(t, fuel, "nf") } |
/// for(@[⌜^lambda⌝, _, ${b}] <- @"nf"){ @"OUT"!([⌜^lambda⌝, ⌜^nog⌝, b]) }` — consumer 1 drives the
/// shipped FLT to its λ-NF and re-ships it on `@"nf"`; consumer 2 destructures the λ (marker
/// wildcarded), re-wraps it (marker forced `⌜^nog⌝`), and publishes to `@"OUT"`.
fn inter_flt_reship_program(fp: &str) -> Par {
    let lambda_tag = reserved_tag_par(fp, LAMBDA_REFLECT_LABEL);
    let nog = reserved_tag_par(fp, NONGROUND_MARK_REFLECT_LABEL);
    let drive_chan = reserved_tag_par(fp, DRIVE_RESERVED_LABEL);
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);

    let producer = new_send_par(
        quoted_name("fltX"),
        vec![subject],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    // Consumer 1: capture the WHOLE FLT (a bare FreeVar(0) ⟹ BoundVar(0)), seed the driver with "nf".
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

    // Consumer 2: match the λ NF (marker wildcarded, ${b}=FreeVar(0)⟹BoundVar(0) the body), re-wrap
    // with the marker forced ⌜^nog⌝, publish to OUT.
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

/// Run `program` composed on the backend's installed `^drive` receiver family, a FRESH in-memory
/// RSpace, and read the full drive observation set (OUT + the `^fired`/`^drive-err`/`^drive-fuel`
/// channels). The install is idle for the non-drive beats (1/2/3) — harmless; their OUT lands the
/// same way.
async fn observe(
    backend: &PlannedRhoBackend,
    program: &Par,
    fp: &str,
) -> Result<DriveObservationSet, String> {
    let channels = DriveObservationChannels::for_fingerprint(fp, "OUT");
    backend
        .run_rho_net_with_call_and_read_observation_set(program, &channels)
        .await
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
    println!("Language fingerprint: {fp}");
    println!("(every primary beat RUNS live; receive patterns HAND-BUILT — phase-2 `${{x}}` generates them)\n");

    beat0_wire_format(&renderer, &fp);
    beat1_ship_and_destructure(&backend, &renderer, &fp).await?;
    beat2_where_guard_on_foreign_subterm(&backend, &renderer, &fp).await?;
    beat3_counterfeit_rejected(&backend, &fp).await?;
    beat4_fill_holes_and_run(&backend, &renderer, &fp).await?;
    beat5_positive_inter_flt_reship(&backend, &renderer, &fp).await?;
    beat5_omega_witness(&backend, &renderer, &fp).await?;
    deferred_after_primary();

    Ok(())
}

/// Beat 0 — the wire format existed before the syntax (no run): the tags, the reflected v2
/// (E-2-D marker) layout, and the de-reflected surface forms.
fn beat0_wire_format(renderer: &SurfaceRenderer, fp: &str) {
    println!("── Beat 0 — the wire format existed before the syntax ──────────────────────");
    println!("  ⌜App⌝      (unforgeable GPrivate tag)  = {}", reflected_tag_string(fp, "App"));
    println!(
        "  ⌜^lambda⌝                              = {}",
        reflected_tag_string(fp, LAMBDA_REFLECT_LABEL)
    );
    println!(
        "  ⌜^nog⌝      (E-2-D groundness marker)   = {}",
        reflected_tag_string(fp, NONGROUND_MARK_REFLECT_LABEL)
    );
    println!("  id = ⟦{}⟧", show(renderer, fp, &g_id()));
    println!("       reflected v2:  [⌜^lambda⌝, ⌜^nog⌝, [⌜^bound⌝, ⌜^nog⌝, Z]]");
    println!("  K  = ⟦{}⟧", show(renderer, fp, &g_k()));
    println!(
        "       reflected v2:  [⌜^lambda⌝, ⌜^nog⌝, [⌜^lambda⌝, ⌜^nog⌝, [⌜^bound⌝, ⌜^nog⌝, S(Z)]]]"
    );
    println!("  ⟦App(id, K)⟧ = [⌜App⌝, ⌜^nog⌝, ⟦id⟧, ⟦K⟧]");
    println!(
        "       every marked-object node is [head-tag, groundness-marker, args…]: the marker at"
    );
    println!(
        "       index 1 is what every pattern below WILDCARDS (`_`) and every re-quote RE-EMITS."
    );
    println!(
        "       All three tops are ⌜^nog⌝ — a closed λ hereditarily carries a bound variable."
    );
    println!(
        "  (VALIDATE: exact α-fresh binder spelling is renderer-chosen; the STRUCTURE is exact)\n"
    );
}

/// Beat 1 — ship a Lambda FLT; destructure it with a typed hole. RUNS.
async fn beat1_ship_and_destructure(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 1 — ship an FLT; destructure with a typed hole (RUNS) ───────────────");
    println!("  program: @\"fltX\"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${{f}}, ⟦K⟧] <- @\"fltX\" ){{ @\"OUT\"!(f) }}");
    println!(
        "           (`${{f}}` is a match FreeVar at the function position — hand-built here; the"
    );
    println!("            refined `${{f}}` syntax generates this receive in phase-2)");
    let tag = reserved_tag_par(fp, "App");
    let k_reflected = reflect_ground_term_par(&g_k(), fp);

    clear_var_cache();
    let subject = reflect_ground_term_par(&g_app(g_id(), g_k()), fp);
    let set =
        observe(backend, &hole_rendezvous_program(subject, tag.clone(), k_reflected.clone()), fp)
            .await?;
    for value in &set.out_values {
        println!(
            "  OUT observes ⟦{}⟧   (the ${{f}} hole bound ⟦id⟧ at the function position)",
            show_value(renderer, value)
        );
    }

    // 1b — ship ⟦K⟧ alone (a λ node, not an App): the App-shaped pattern never fires.
    clear_var_cache();
    let lone_k = reflect_ground_term_par(&g_k(), fp);
    let rested = observe(backend, &hole_rendezvous_program(lone_k, tag, k_reflected), fp).await?;
    println!(
        "  1b: ship ⟦K⟧ alone → OUT {} value(s) — no App node, no COMM, the datum RESTS on fltX\n",
        rested.out_values.len()
    );
    Ok(())
}

/// Beat 2 — the guard vetoes on a foreign subterm (D2 ground-subpattern form). RUNS.
async fn beat2_where_guard_on_foreign_subterm(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 2 — the guard vetoes on a foreign subterm (D2, RUNS) ────────────────");
    println!("  program: for( @[⌜App⌝, _, ${{f}}, ⟦K⟧] <- @\"fltX\" ){{ @\"OUT\"!(f) }}");
    println!(
        "           (two structurally-valid Apps, discriminated by the argument subterm alone)"
    );
    let tag = reserved_tag_par(fp, "App");
    let k_reflected = reflect_ground_term_par(&g_k(), fp);

    clear_var_cache();
    let matched = observe(
        backend,
        &hole_rendezvous_program(
            reflect_ground_term_par(&g_app(g_id(), g_k()), fp),
            tag.clone(),
            k_reflected.clone(),
        ),
        fp,
    )
    .await?;
    for value in &matched.out_values {
        println!(
            "  ship ⟦App(id, K)⟧ → OUT ⟦{}⟧   (argument ⟦K⟧ = ⟦K⟧ — matches)",
            show_value(renderer, value)
        );
    }

    clear_var_cache();
    let vetoed = observe(
        backend,
        &hole_rendezvous_program(
            reflect_ground_term_par(&g_app(g_id(), g_id()), fp),
            tag,
            k_reflected,
        ),
        fp,
    )
    .await?;
    println!("  ship ⟦App(id, id)⟧ → OUT {} value(s)  (argument ⟦id⟧ ≠ ⟦K⟧ — veto, zero partial effects)", vetoed.out_values.len());
    println!(
        "  (the refined syntax spells this `where a == ⟦K⟧`; the marker-sensitive EEq guard is"
    );
    println!("   deferred to guard-lowering — D2 rides the marker-wildcarded PATTERN, the sound v1 form)\n");
    Ok(())
}

/// Beat 3 — the counterfeit is rejected: tags are unforgeable. RUNS.
async fn beat3_counterfeit_rejected(backend: &PlannedRhoBackend, fp: &str) -> Result<(), String> {
    println!("── Beat 3 — the counterfeit is rejected: tags are unforgeable (RUNS) ────────");
    println!(
        "  a 4-element GString-tagged fake [\"App\", ⌜^nog⌝, ⟦id⟧, ⟦K⟧] at the same receive —"
    );
    println!(
        "  byte-identical to ⟦App(id, K)⟧ EXCEPT the head (ground \"App\" vs the GPrivate ⌜App⌝)."
    );
    clear_var_cache();
    let tag = reserved_tag_par(fp, "App");
    let nog = reserved_tag_par(fp, NONGROUND_MARK_REFLECT_LABEL);
    let id_reflected = reflect_ground_term_par(&g_id(), fp);
    let k_reflected = reflect_ground_term_par(&g_k(), fp);
    let counterfeit = new_elist_par(
        vec![quoted_name("App"), nog, id_reflected, k_reflected.clone()],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    let set = observe(backend, &hole_rendezvous_program(counterfeit, tag, k_reflected), fp).await?;
    println!(
        "    genuine head     = {}   (GPrivate, compared by identity)",
        reflected_tag_string(fp, "App")
    );
    println!("    counterfeit head = ground string \"App\"   — a DIFFERENT Par value");
    println!(
        "  → OUT {} value(s): no match, the datum rests (tags by identity, not spelling)",
        set.out_values.len()
    );
    println!("  the runtime face of the FIP No-Injection property.\n");
    Ok(())
}

/// Beat 4 — fill the holes and RUN it: the receiver captures `f`,`k`, re-quotes with the marker
/// forced `⌜^nog⌝`, seeds the driver, and the App drives to β-NF `K` fully in-Rho. RUNS.
async fn beat4_fill_holes_and_run(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 4 — fill the holes and RUN it: re-quote to β-normal form (RUNS) ─────");
    println!(
        "  program: @\"fltX\"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${{f}}, ${{k}}] <- @\"fltX\" ){{"
    );
    println!("             ⌜^drive⌝!( [⌜App⌝, ⌜^nog⌝, f, k], fuel, \"OUT\" ) }}");
    println!(
        "           (the marker slot is FORCED ⌜^nog⌝ over the holes — the E-2-D semantic fix:"
    );
    println!("            a 3-element re-quote or a hard-coded ⌜^gnd⌝ would silently NOT β-fire)");
    clear_var_cache();
    let set = observe(backend, &requote_and_drive_program(fp), fp).await?;
    for value in &set.out_values {
        println!(
            "  OUT observes ⟦{}⟧   (β-normal form of App(id, K))",
            show_value(renderer, value)
        );
    }
    println!("  ^fired ledger: {:?}", set.fired_labels()?);
    println!(
        "  ^drive-err: {} datum(a) | ^drive-fuel: {} datum(a)  (both expected empty)",
        set.err_data.len(),
        set.fuel_data.len()
    );
    println!("  one visible COMM (the foreign term changing hands), then a cascade of τ-steps:");
    println!("  the driver matching, β firing through the substitution calculus, the contractum re-driving.\n");
    Ok(())
}

/// Beat 5 (positive) — the same-language inter-FLT re-ship: a NF produced by one FLT interaction,
/// re-shipped and re-matched by another. RUNS.
async fn beat5_positive_inter_flt_reship(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 5 (positive) — the inter-FLT re-ship (RUNS) ─────────────────────────");
    println!("  program: @\"fltX\"!(⟦App(id,K)⟧)");
    println!("           | for(@t <- @\"fltX\"){{ ⌜^drive⌝!(t, fuel, \"nf\") }}");
    println!("           | for( @[⌜^lambda⌝, _, ${{b}}] <- @\"nf\" ){{ @\"OUT\"!([⌜^lambda⌝, ⌜^nog⌝, b]) }}");
    clear_var_cache();
    let set = observe(backend, &inter_flt_reship_program(fp), fp).await?;
    for value in &set.out_values {
        println!(
            "  OUT observes ⟦{}⟧   (a NF produced by one FLT interaction, re-matched by another)",
            show_value(renderer, value)
        );
    }
    println!("  consumer 1's drive ^fired: {:?}", set.fired_labels()?);
    println!(
        "  honest scope: same-language, same-binder-depth re-wrap; the cross-language binder hole"
    );
    println!("  is the phase-3 co-install spike (D7), not this beat.\n");
    Ok(())
}

/// Beat 5 (Ω negative) — fuel exhaustion, typed + fail-closed. RUNS (direct-seed fuel witness).
async fn beat5_omega_witness(
    backend: &PlannedRhoBackend,
    renderer: &SurfaceRenderer,
    fp: &str,
) -> Result<(), String> {
    println!("── Beat 5 (Ω negative) — fuel exhaustion, typed + fail-closed (RUNS) ────────");
    clear_var_cache();
    let omega_half = g_lambda(g_app(g_bound(0), g_bound(0)));
    let omega = g_app(omega_half.clone(), omega_half);
    let seed = rho_net_drive_call_par_with_fuel(fp, reflect_ground_term_par(&omega, fp), 3, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(fp, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await?;

    println!("  Ω = (λx.x x)(λx.x x), per-path fuel 3:");
    println!("    ^fired ledger: {:?}  (exactly per-path-fuel firings)", set.fired_labels()?);
    println!(
        "    ^drive-fuel: {} typed exhaustion datum (the stuck redex Ω)",
        set.fuel_data.len()
    );
    if let Some(stuck) = set
        .fuel_data
        .first()
        .and_then(par_as_runtime_observation_value)
    {
        println!("      stuck redex = ⟦{}⟧", show_value(renderer, &stuck));
    }
    println!("    OUT: {} value(s)  (exhaustion NEVER claims an NF)\n", set.out_values.len());
    Ok(())
}

/// The secondary demos, DEFERRED to after the primary demo is complete (USER decision 1). These are
/// separate demos — NOT stubbed or faked here; each is built once the primary beats above are green
/// and recorded.
fn deferred_after_primary() {
    println!("── Deferred — later, after the primary demo (USER decision 1) ───────────────");
    println!(
        "  * Beat 4b — the live StepSession τ-trace: step 1 is the USER-level FLT rendezvous COMM"
    );
    println!(
        "    on fltX; each subsequent step classifies [τ drive]/[τ subst]; terminal [Rho output]."
    );
    println!(
        "  * Secondary openers — the stock-Rholang \"stringly-typed strawman\" cameo that Beat 3"
    );
    println!("    then kills, and the Guarded Settlement Desk Beat-2 bridge.");
    println!("  Deferred, NOT stubbed: they are separate demos, built once the primary beats are");
    println!("  green + recorded. Until then Beats 0/1/4 also narrate from the pinned twin facts.");
}
