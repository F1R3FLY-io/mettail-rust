//! A-S5.6 — the `step` ROUTING PINS (F5: pin CURRENT behavior, change nothing about
//! generation) + probe P4.
//!
//! The REPL `step` routing for a RhoMachine-default language (`repl/src/repl.rs`, the
//! step-mode branch) is two-layered:
//!
//! * **Layer 1** — ask `Language::run_step_backend_report` (the wrapper's step slot) for
//!   the Dovetail one-step REWRITE graph; KEEP it iff `graph_kind == Rewrite` and it has
//!   at least one derivation edge.
//! * **Layer 2** — otherwise refine to the live reactive COMM reduction trace
//!   (`run_reduction_trace_report` → `StepSession`), one operational schedule on the real
//!   Rho machine.
//!
//! F5 split pin: **Lambda is TYPED-path** (`has_substitution_rewrite` ∈ the
//! `needs_typed_dovetail_path` disjunction) — its step slot is the generated
//! `dovetail_step_graph`, whose β-edged rewrite graph satisfies the Layer-1 keep
//! condition. **Ambient is genuinely UNTYPED** (its `PNew` binder + `new`-float equations
//! keep `should_emit_binder_congruence` true, so both structural-AC typed gates are off)
//! — NO `dovetail_step_graph` is generated; its step slot is `dovetail_report_for`, whose
//! DERIVATION graph fails the Layer-1 keep condition (probe P4), so `step` falls through
//! to the Layer-2 COMM trace.
#![cfg(feature = "rho-languages")]

use mettail_repl::rho_backends::{ambient_backed, lambda_backed};
use mettail_runtime::{Language, RuntimeBackendOutput, RuntimeDovetailGraphKind};

/// The REPL's Layer-1 keep condition (`repl.rs` step-mode routing): a step-slot report is
/// kept iff it is a REWRITE-kind Dovetail graph with at least one edge.
fn layer_1_keeps(report: &mettail_runtime::RuntimeBackendReport) -> bool {
    report
        .as_dovetail()
        .map(|dovetail| {
            dovetail.graph_kind == RuntimeDovetailGraphKind::Rewrite
                && !dovetail.derivation_edges.is_empty()
        })
        .unwrap_or(false)
}

/// F5 pin (Lambda = Layer 1): the flipped Lambda wrapper's step slot yields the TYPED
/// one-step rewrite graph — β edges present on a redex subject — so REPL `step` keeps the
/// Layer-1 navigable rewrite graph exactly as before the flip.
#[test]
fn lambda_step_slot_yields_the_layer_1_typed_rewrite_graph() {
    let language = lambda_backed().expect("Lambda lazy backend installs");
    let term = language
        .parse_term("(lam x. x, lam a. lam b. a)")
        .expect("the β subject parses");
    let report = language
        .run_step_backend_report(term.as_ref())
        .expect("the Lambda step slot produces the generated dovetail_step_graph");
    let dovetail = report.as_dovetail().expect("a Dovetail step report");
    assert_eq!(
        dovetail.graph_kind,
        RuntimeDovetailGraphKind::Rewrite,
        "Lambda's step slot is the one-step REWRITE graph (typed path)"
    );
    assert!(
        !dovetail.derivation_edges.is_empty(),
        "the β subject has at least one rewrite successor (a β edge)"
    );
    assert!(layer_1_keeps(&report), "REPL step routing KEEPS Lambda's Layer-1 graph");
}

/// ★ Probe P4 (F5, Ambient = Layer 2): the flipped Ambient wrapper's step slot yields a
/// graph that FAILS the Layer-1 keep condition — the untyped `dovetail_report_for` report
/// is a DERIVATION graph (graph-emptiness evidence: kind ≠ Rewrite, so the rewrite-edge
/// set the routing tests is empty) — and the routing therefore falls through to Layer 2.
#[test]
fn p4_ambient_step_slot_graph_has_no_rewrite_edges_so_routing_falls_through() {
    let language = ambient_backed().expect("Ambient lazy backend installs");
    let term = language
        .parse_term("{open(n, a[{0}]) | n[{b[{0}]}]}")
        .expect("the open subject parses");
    let report = language
        .run_step_backend_report(term.as_ref())
        .expect("the Ambient step slot produces the untyped dovetail_report_for report");
    let dovetail = report.as_dovetail().expect("a Dovetail report");
    assert_ne!(
        dovetail.graph_kind,
        RuntimeDovetailGraphKind::Rewrite,
        "P4: Ambient's untyped step-slot report is a DERIVATION graph, not a rewrite graph"
    );
    assert!(
        !layer_1_keeps(&report),
        "P4: the Layer-1 keep condition fails — REPL step routing falls through to the \
         Layer-2 live COMM trace"
    );
}

/// PROBE (evidence capture for the τ classifier): print the Ambient Layer-2 reduction
/// trace for the open subject — every step's kind, display, and raw COMM channel
/// rendering — teed to `scratchpad/as56_step_probe.log`.
#[test]
fn probe_ambient_layer_2_trace_content() {
    let language = ambient_backed().expect("Ambient lazy backend installs");
    let term = language
        .parse_term("{open(n, a[{0}]) | n[{b[{0}]}]}")
        .expect("the open subject parses");
    match language.run_reduction_trace_report(term.as_ref()) {
        Ok(report) => {
            let RuntimeBackendOutput::ReductionTrace(trace) = report.output() else {
                panic!("expected a reduction trace, got {:?}", report.output().kind_name());
            };
            println!("AMBIENT LAYER-2 TRACE: {} step(s)", trace.step_count());
            for step in &trace.steps {
                println!("  [{}] kind={:?}", step.ordinal, step.kind);
                println!("      display: {}", step.display);
                if let Some(comm) = &step.comm {
                    println!("      channels: {:?}", comm.channels);
                }
            }
        },
        Err(err) => println!("AMBIENT LAYER-2 TRACE ERROR: {err}"),
    }
}

/// The τ-classifier trace-level pin (A-S5.6, plan v2 §6.4): the CURRENT Ambient Layer-2
/// trace rides the report-carrying MATCH fallback — its COMMs fire on the legacy
/// `ac:loc:`-style automaton channels, NOT on the reserved `^…` drive/subst/carrier
/// families — so every step is UNCLASSIFIED (`tau == None`) and the default τ filter
/// hides NOTHING today (F5: current behavior pinned; the classifier activates exactly
/// when drive-seeded COMMs enter a trace). The trace still ends with unfiltered
/// terminal Output steps.
#[test]
fn ambient_layer_2_trace_steps_are_unclassified_today_and_survive_the_default_filter() {
    let language = ambient_backed().expect("Ambient lazy backend installs");
    let term = language
        .parse_term("{open(n, a[{0}]) | n[{b[{0}]}]}")
        .expect("the open subject parses");
    let report = language
        .run_reduction_trace_report(term.as_ref())
        .expect("the Ambient Layer-2 trace runs");
    let RuntimeBackendOutput::ReductionTrace(trace) = report.output() else {
        panic!("expected a reduction trace, got {:?}", report.output().kind_name());
    };
    assert!(trace.step_count() >= 1, "the Layer-2 trace has at least one step");
    for step in &trace.steps {
        assert_eq!(
            step.tau, None,
            "today's match-fallback trace carries NO reserved-channel COMMs — step {} \
             ({}) must be unclassified",
            step.ordinal, step.display
        );
    }
    assert!(
        trace
            .steps
            .iter()
            .any(|step| step.kind == mettail_runtime::RuntimeReductionKind::Output),
        "the trace ends with terminal Output steps (never τ, never filtered)"
    );
}

/// PROBE: the Lambda Layer-2 surface is NOT selected by routing (Layer 1 wins), but
/// capture what the live trace would show, for the τ-classifier record.
#[test]
fn probe_lambda_layer_2_trace_content() {
    let language = lambda_backed().expect("Lambda lazy backend installs");
    let term = language
        .parse_term("(lam x. x, lam a. lam b. a)")
        .expect("the β subject parses");
    match language.run_reduction_trace_report(term.as_ref()) {
        Ok(report) => {
            let RuntimeBackendOutput::ReductionTrace(trace) = report.output() else {
                panic!("expected a reduction trace, got {:?}", report.output().kind_name());
            };
            println!("LAMBDA LAYER-2 TRACE: {} step(s)", trace.step_count());
            for step in &trace.steps {
                println!("  [{}] kind={:?}", step.ordinal, step.kind);
                println!("      display: {}", step.display);
                if let Some(comm) = &step.comm {
                    println!("      channels: {:?}", comm.channels);
                }
            }
        },
        Err(err) => println!("LAMBDA LAYER-2 TRACE ERROR: {err}"),
    }
}
