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
