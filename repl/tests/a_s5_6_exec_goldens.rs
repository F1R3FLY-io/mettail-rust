//! A-S5.6 (production flip) — the exec GOLDEN corpus for Lambda + Ambient.
//!
//! F6 (plan v2 §6.3, amendment AM-6c): goldens are α-EQUIVALENCE, NOT byte equality —
//! reflection erases surface names to de Bruijn, and the Dovetail-era display renders the
//! original binder hints, so byte-identical pretty output is unachievable for binder NFs.
//! Each golden subject is therefore compared as: parse(de-reflected pretty output of the
//! flipped exec) `BoundTerm::term_eq` parse(Dovetail-era NF display) — α-aware structural
//! equality on the language's REAL category values.
//!
//! THE FIXTURE-CAPTURE PATH (documented, load-bearing): the Dovetail-era side is NOT a
//! frozen string — [`dovetail_era_language`] constructs the pre-flip wrapper LIVE
//! (`mettail_dovetail_runtime::dovetail_backed`, exactly what `lambda_backed`/
//! `ambient_backed` returned before A-S5.6), so the golden recomputes the Dovetail NF on
//! every run. The pre-flip capture of these displays (run at HEAD `a9193914`, before any
//! wrapper edit) is teed to `scratchpad/as56_preflip_goldens.log`.
#![cfg(feature = "rho-languages")]

use mettail_dovetail_runtime::dovetail_backed;
use mettail_languages::ambient::AmbientLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_runtime::{Language, RuntimeBackend, RuntimeBackendOutput};

/// The DOVETAIL-ERA wrapper for one production language — the exact construction
/// `repl::rho_backends::{lambda,ambient}_backed` used before the A-S5.6 flip. This is the
/// golden fixture-capture path: the Dovetail NF is recomputed live, never frozen.
fn dovetail_era_language(which: &str) -> Box<dyn Language> {
    match which {
        "Lambda" => dovetail_backed(LambdaLanguage, LambdaLanguage::dovetail_compiler_stage())
            .expect("the Dovetail-era Lambda wrapper installs"),
        "Ambient" => dovetail_backed(AmbientLanguage, AmbientLanguage::dovetail_compiler_stage())
            .expect("the Dovetail-era Ambient wrapper installs"),
        other => panic!("no Dovetail-era wrapper for {other}"),
    }
}

/// The Dovetail-era exec NF display for one subject: run the Dovetail backend report and
/// mirror the REPL's exec display selection (`runtime_graph_view` Dovetail arm — the
/// single-root entry term's `source_display` if reconstructed, else `op_display`).
fn dovetail_era_nf_display(language: &dyn Language, source: &str) -> String {
    let term = language
        .parse_term(source)
        .unwrap_or_else(|err| panic!("{} must parse {source:?}: {err}", language.name()));
    let report = language
        .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
        .unwrap_or_else(|err| panic!("{} Dovetail exec of {source:?}: {err}", language.name()));
    let RuntimeBackendOutput::Dovetail(dovetail) = report.output() else {
        panic!("{} Dovetail exec must yield a Dovetail report", language.name());
    };
    let [root] = dovetail.root_ordinals.as_slice() else {
        panic!(
            "{} Dovetail exec of {source:?} must have exactly one root, got {:?}",
            language.name(),
            dovetail.root_ordinals
        );
    };
    let record = &dovetail.terms[*root];
    record.source_display.clone().unwrap_or_else(|| record.op_display.clone())
}

/// The golden corpus (the A-S5.6 task list): Lambda — single β, a 4-chain, an
/// under-binder redex, a normal form; Ambient — open, in, the redeclared 3-element out,
/// singleton out, a 2-step cascade.
fn golden_corpus() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        ("Lambda", "single β", "(lam x. x, lam a. lam b. a)"),
        (
            "Lambda",
            "4-chain",
            "(lam x. x, (lam x. x, (lam x. x, (lam x. x, lam a. lam b. a))))",
        ),
        ("Lambda", "under-binder redex", "lam y. (lam x. x, y)"),
        ("Lambda", "normal form", "lam a. lam b. a"),
        ("Ambient", "open", "{open(n, a[{0}]) | n[{b[{0}]}]}"),
        ("Ambient", "in", "{n[{in(m, 0)}] | m[{c[{0}]}]}"),
        (
            "Ambient",
            "redeclared 3-element out",
            "m[{n[{out(m, 0)}] | a[{0}] | b[{0}]}]",
        ),
        ("Ambient", "singleton out", "m[{n[{out(m, 0)}]}]"),
        ("Ambient", "2-step cascade", "{n[{in(m, 0)}] | m[{open(n, c[{0}])}]}"),
    ]
}

/// PRE-FLIP CAPTURE (item 1 of the A-S5.6 change set): print every golden subject's
/// Dovetail-era NF evidence. Run BEFORE the wrapper flip and teed to
/// `scratchpad/as56_preflip_goldens.log`; kept as the live fixture-capture probe.
///
/// PINNED REALITY (design-vs-reality, F6): the Dovetail-era `exec` DISPLAY for both
/// languages is the derivation ROOT's `op_display` — an OP NAME (`Lambda::Term::Lam`,
/// `Ambient::Proc::PPar`), never a pretty NF (exec reports carry no `source_display`).
/// So the byte-golden `pretty(driver NF) == pretty(dovetail NF)` was never available even
/// pre-flip, exactly as F6 judged. The recoverable Dovetail-era NF TERM per language:
///
/// * **Lambda** (typed path): `LambdaLanguage::dovetail_normal_term` — the REAL reduced
///   Dovetail NF as a term; this is the live α-golden fixture.
/// * **Ambient** (untyped path): NO normal-term surface exists (`dovetail_normal_term` /
///   `dovetail_step_graph` are typed-path-only; verified against `target/generated/ambient`).
///   The α-golden fixture is the DECLARED C-G expected NF source, cross-validated by the
///   host firing-count pins (`ambient_out_rule_host_semantics.rs`) and the A-S5.5 in-Rho
///   suite (`rho_net_ambient_full.rs`, itself host-mirror-checked).
#[test]
fn capture_dovetail_era_golden_nf_displays() {
    for (language_name, label, source) in golden_corpus() {
        let language = dovetail_era_language(language_name);
        let nf_display = dovetail_era_nf_display(language.as_ref(), source);
        let parse_back = match language.parse_term(&nf_display) {
            Ok(term) => format!("parses (display: {term})"),
            Err(err) => format!("DOES NOT PARSE: {err}"),
        };
        println!("GOLDEN [{language_name} / {label}]");
        println!("  subject: {source}");
        println!("  dovetail-era exec NF display (op name — pinned reality): {nf_display}");
        println!("  parse-back: {parse_back}");
        if language_name == "Lambda" {
            let term = language.parse_term(source).expect("the subject parses");
            let nf = mettail_languages::lambda::LambdaLanguage::dovetail_normal_term(
                term.as_ref(),
                64,
                1_000_000,
            )
            .expect("the Dovetail-era Lambda NF term reconstructs");
            println!("  dovetail_normal_term (the α-golden fixture): {nf}");
        }
    }
}

/// The DECLARED Ambient golden NF sources (C-G semantics over the redeclared rules; the
/// Dovetail-era untyped path exposes no NF-term surface — see the capture probe above).
/// Each is justified rule-by-rule in the comment and parsed live as the α-golden term.
fn ambient_declared_golden_nf(label: &str) -> &'static str {
    match label {
        // OpenRule: {open(n,P), n[Q], ...rest} → {P, Q, ...rest}; P = a[{0}], Q = {b[{0}]}
        // (bag-valued Q splices flat — host `add_flattened_bag`).
        "open" => "{a[{0}] | b[{0}]}",
        // InRule: {n[{in(m,0)}], m[{c[{0}]}]} → {m[{n[{0}], {c[{0}]}}]} → (flatten R)
        // {m[{n[{0}], c[{0}]}]}.
        "in" => "{m[{n[{0}] | c[{0}]}]}",
        // The A-S5.4b C-G (Red Out) redeclaration: the residual {a[{0}], b[{0}]} stays
        // INSIDE m: m[{n[{out(m,0)}], a[{0}], b[{0}]}] → {n[{0}], m[{a[{0}], b[{0}]}]}.
        "redeclared 3-element out" => "{n[{0}] | m[{a[{0}] | b[{0}]}]}",
        // Empty rest is legal post-A-S5.4b: m[{n[{out(m,0)}]}] → {n[{0}], m[{}]}.
        "singleton out" => "{n[{0}] | m[{}]}",
        // In fires (R = m's whole body splices flat), creating the Open redex inside m;
        // Open fires: → {m[{c[{0}], 0}]}.
        "2-step cascade" => "{m[{c[{0}] | 0}]}",
        other => panic!("no declared Ambient golden for {other}"),
    }
}

/// PRE-FLIP CAPTURE (Ambient term fixtures): every declared golden NF source parses, and
/// its structure is printed for the log record.
#[test]
fn capture_ambient_declared_golden_terms() {
    let language = dovetail_era_language("Ambient");
    for (language_name, label, source) in golden_corpus() {
        if language_name != "Ambient" {
            continue;
        }
        let declared = ambient_declared_golden_nf(label);
        let term = language
            .parse_term(declared)
            .unwrap_or_else(|err| panic!("declared golden {declared:?} must parse: {err}"));
        println!("GOLDEN-TERM [Ambient / {label}]");
        println!("  subject: {source}");
        println!("  declared C-G NF source: {declared}");
        println!("  parsed term display: {term}");
    }
}

// ─── the A-S5.6 α-EQUIVALENCE GOLDENS (F6) ─────────────────────────────────────────────
//
// Post-flip, `exec` returns the OBSERVATIONS shape (the reflected resting NF). Each
// golden: (1) exec the subject through the FLIPPED production wrapper; (2) DE-REFLECT
// the observed NF into surface syntax (`observation_surface::SurfaceRenderer` — the same
// renderer the REPL display uses); (3) PARSE the surface text back through the language
// parser; (4) compare `mettail_runtime::BoundTerm::term_eq` (α-aware; multiset bags)
// against the Dovetail-era golden TERM — Lambda's from the live `dovetail_normal_term`
// fixture, Ambient's from the declared C-G NF source. Display hints may differ (the
// de-reflected binders are GENERATED fresh names); α-equality is the F6-mandated form.
//
// ⚠ NewComm ≤6 canonical-ordering cap: any claim that a displayed NF is THE canonical
// form rides `binder_congruence.rs`'s exhaustive binder-permutation ordering, which
// applies only to runs of ≤6 consecutive `new` binders (encounter order beyond). The
// goldens here assert α-EQUALITY of terms, not display canonicality, so the cap does
// not bound them — noted for any future canonical-NF display claim. Bag print order IS
// pinned (sorted rendering in the renderer).

use mettail_repl::observation_surface::SurfaceRenderer;
use mettail_repl::rho_backends::{ambient_backed, lambda_backed};
use mettail_runtime::BoundTerm;

/// Exec one subject through the FLIPPED wrapper and de-reflect the single OUT resting
/// value into surface syntax.
fn flipped_exec_surface(language: &dyn Language, source: &str) -> String {
    let renderer = SurfaceRenderer::for_definition_source(
        language
            .metadata()
            .definition_source()
            .expect("the production language exposes its definition source"),
    )
    .expect("the production language's definition source reconstructs");
    // The cache-PRESERVING parse (`parse_term_for_env` = the generated
    // `parse_preserving_vars`): free variables are INTERNED BY NAME in the process
    // var cache, so every parse in one golden shares its free `FreeVar` identities —
    // `parse_term` would CLEAR the cache per call, making identity-based `term_eq`
    // vacuously false across parses of OPEN terms. This is also exactly the REPL
    // exec input-formation parse.
    let term = language
        .parse_term_for_env(source)
        .unwrap_or_else(|err| panic!("{} must parse {source:?}: {err}", language.name()));
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .unwrap_or_else(|err| panic!("{} in-Rho exec of {source:?}: {err}", language.name()));
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values.len(),
        1,
        "one quiescent resting term for {source:?}: {:?}",
        out.values
    );
    renderer
        .render(&out.values[0])
        .unwrap_or_else(|err| panic!("the resting NF of {source:?} de-reflects: {err}"))
}

/// α-golden (Lambda): for every Lambda subject, the de-reflected flipped-exec NF parses
/// back α-equal (`BoundTerm::term_eq` on the inner `Term`) to the LIVE Dovetail-era
/// `dovetail_normal_term` fixture.
#[test]
fn lambda_flipped_exec_nfs_are_alpha_equal_to_the_dovetail_era_nfs() {
    use mettail_languages::lambda::LambdaTerm;
    mettail_runtime::clear_var_cache();
    let language = lambda_backed().expect("the flipped Lambda wrapper installs");
    for (language_name, label, source) in golden_corpus() {
        if language_name != "Lambda" {
            continue;
        }
        // The Dovetail-era golden TERM (the live fixture-capture path). Every parse in
        // this test is the cache-preserving `parse_term_for_env` (see
        // `flipped_exec_surface`) so free-variable identities are shared by name.
        let subject = language.parse_term_for_env(source).expect("the subject parses");
        let dovetail_nf = mettail_languages::lambda::LambdaLanguage::dovetail_normal_term(
            subject.as_ref(),
            64,
            1_000_000,
        )
        .expect("the Dovetail-era Lambda NF reconstructs");
        let dovetail_inner = &dovetail_nf
            .as_any()
            .downcast_ref::<LambdaTerm>()
            .expect("a LambdaTerm")
            .0;

        // The flipped side: exec in-Rho → de-reflect → parse back.
        let surface = flipped_exec_surface(language.as_ref(), source);
        let parsed_back = language
            .parse_term_for_env(&surface)
            .unwrap_or_else(|err| panic!("[{label}] de-reflected NF {surface:?} parses: {err}"));
        let parsed_inner = &parsed_back
            .as_any()
            .downcast_ref::<LambdaTerm>()
            .expect("a LambdaTerm")
            .0;

        assert!(
            BoundTerm::term_eq(dovetail_inner, parsed_inner),
            "[{label}] the flipped exec NF must be α-EQUAL to the Dovetail-era NF\n  \
             subject: {source}\n  de-reflected: {surface}\n  dovetail NF: {dovetail_nf}\n  \
             parsed back: {parsed_back}"
        );
        println!(
            "α-GOLDEN [Lambda / {label}]: subject {source:?} → de-reflected {surface:?} \
             α-eq dovetail {dovetail_nf}"
        );
    }
}

/// α-golden (Ambient): for every Ambient subject, the de-reflected flipped-exec NF
/// parses back α-equal (`BoundTerm::term_eq` on the inner `Proc` — multiset bags) to the
/// DECLARED C-G NF term (the Dovetail-era untyped path exposes no NF-term surface; the
/// declared sources are cross-validated by the host firing pins and the A-S5.5 in-Rho
/// suite — see the capture probe's doc).
#[test]
fn ambient_flipped_exec_nfs_are_alpha_equal_to_the_declared_cg_nfs() {
    use mettail_languages::ambient::{AmbientTerm, AmbientTermInner};
    mettail_runtime::clear_var_cache();
    let language = ambient_backed().expect("the flipped Ambient wrapper installs");
    let ambient_proc = |term: &dyn mettail_runtime::Term| {
        match &term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .expect("an AmbientTerm")
            .0
        {
            AmbientTermInner::Proc(proc) => proc.clone(),
            other => panic!("the golden term is a Proc, got {other:?}"),
        }
    };
    for (language_name, label, source) in golden_corpus() {
        if language_name != "Ambient" {
            continue;
        }
        // The declared C-G golden TERM. Parsed with the cache-PRESERVING
        // `parse_term_for_env` in the SAME var-cache session as the parse-back below,
        // so shared free names (n/m/a/b/c) resolve to the SAME `FreeVar`s — `term_eq`
        // compares free occurrences by variable identity (`parse_term` clears the
        // cache per call and can never satisfy that for open terms).
        let declared_source = ambient_declared_golden_nf(label);
        let declared = language
            .parse_term_for_env(declared_source)
            .expect("the declared golden parses");
        let declared_proc = ambient_proc(declared.as_ref());

        // The flipped side: exec in-Rho → de-reflect → parse back.
        let surface = flipped_exec_surface(language.as_ref(), source);
        let parsed_back = language
            .parse_term_for_env(&surface)
            .unwrap_or_else(|err| panic!("[{label}] de-reflected NF {surface:?} parses: {err}"));
        let parsed_proc = ambient_proc(parsed_back.as_ref());

        assert!(
            BoundTerm::term_eq(&declared_proc, &parsed_proc),
            "[{label}] the flipped exec NF must be α-EQUAL to the declared C-G NF\n  \
             subject: {source}\n  de-reflected: {surface}\n  declared: {declared_source}\n  \
             parsed back: {parsed_back}"
        );
        println!(
            "α-GOLDEN [Ambient / {label}]: subject {source:?} → de-reflected {surface:?} \
             α-eq declared {declared_source:?}"
        );
    }
}

/// Item 7 (cross-check surfacing): the ALWAYS-ON §4.7 drive cross-check runs INSIDE the
/// production exec path, and its violations surface as TYPED exec errors naming the
/// offending channel. Executable witness: Ω = `(λx.xx)(λx.xx)` β-reduces to itself
/// forever, so the in-Rho drive exhausts the default per-path fuel
/// (`DRIVE_DEFAULT_FUEL` = 64) and rests a datum on `^drive-fuel:{fp}` — the exec
/// returns `Err` naming that channel, BOTH bounds (per-path fuel + the global ledger
/// count), never a silent or wrong result.
#[test]
fn omega_exec_surfaces_the_fuel_cross_check_as_a_typed_error_naming_the_channel() {
    mettail_runtime::clear_var_cache();
    let language = lambda_backed().expect("the flipped Lambda wrapper installs");
    let term = language
        .parse_term_for_env("((lam x. (x,x)), (lam x. (x,x)))")
        .expect("Ω parses");
    let err = language
        .run_backend_report(mettail_runtime::RuntimeBackend::RhoMachine, term.as_ref())
        .expect_err("Ω must exhaust the per-path fuel — never a silent result");
    assert!(
        err.contains("cross-check") && err.contains("^drive-fuel"),
        "the fuel violation surfaces as a typed cross-check error NAMING the channel: {err}"
    );
    assert!(
        err.contains("64"),
        "the error names the per-path fuel bound (DRIVE_DEFAULT_FUEL = 64): {err}"
    );
    println!("Ω typed fuel error: {err}");
}

/// The AM-6c display-hazard pin, exec-tier: the F1 float subject's NF carries a residual
/// binder AND a distinct free `x` — the de-reflected surface must NOT re-capture the
/// free `x` (the renderer's fresh binder names avoid every rendered free name), so the
/// parse-back keeps `x` FREE.
#[test]
fn f1_subject_dereflected_nf_never_recaptures_the_free_variable() {
    use mettail_languages::ambient::{AmbientTerm, AmbientTermInner};
    mettail_runtime::clear_var_cache();
    let language = ambient_backed().expect("the flipped Ambient wrapper installs");
    let source = "{new(x, n[{in(m, 0)}]) | m[{x[{0}]}]}";
    let surface = flipped_exec_surface(language.as_ref(), source);
    let parsed_back = language
        .parse_term_for_env(&surface)
        .unwrap_or_else(|err| panic!("the F1 de-reflected NF {surface:?} parses: {err}"));
    let AmbientTermInner::Proc(proc) = &parsed_back
        .as_any()
        .downcast_ref::<AmbientTerm>()
        .expect("an AmbientTerm")
        .0
    else {
        panic!("the F1 NF is a Proc");
    };
    let free = BoundTerm::free_vars(proc);
    assert!(
        free.iter().any(|var| var.pretty_name.as_deref() == Some("x")),
        "the residual free `x` survives FREE in the de-reflected NF (never captured by \
         the generated binder name): {surface}"
    );
    println!("AM-6c pin: F1 subject de-reflected to {surface:?}; free vars: {free:?}");
}
