//! A-S2 (D-stage demotion) — the ZERO-D-STAGE exec instrumentation suite.
//!
//! The lazy production wrappers (`install_dovetail_rho_runtime_backend_lazy`) must run an
//! ADMITTED exec with ZERO Dovetail work: the report-free F2 compile produces the Rho
//! invocation directly, and `checked_complete_dovetail_report` (the D-stage build+check) never
//! runs. Only a typed deferral — a semantic predicate or a gate reject — may build the report,
//! LAZILY. This suite asserts both directions with the `dstage-instrumentation` counter
//! (`mettail_rholang_runtime::dstage_instrumentation`, a process-global count of
//! `checked_complete_dovetail_report` invocations):
//!
//! - admitted SwapDemo (in-Rho locate-all match), Calculator (E3 fold dataflow), and RhoCalc
//!   (direct AST lowering) execs: counter delta 0, with the exact pre-A-S2 observations;
//! - a semantic-predicate-blocked exec (Calculator `5 / 0`): counter delta ≥ 1 and the checked
//!   Dovetail report as the observational payload (today's outcome, lazily produced);
//! - a gate-rejected shape (Calculator free-variable term, not lowerable to scalar dataflow):
//!   counter delta ≥ 1 and the eager pipeline's exact rejection text.
//!
//! Counter discipline: the counter is process-global, so every assertion is a DELTA around this
//! test's own calls. Under `cargo nextest` each test runs in its own process, so deltas are
//! exact; under in-process `cargo test` the deltas remain sound for the 0-assertions because
//! they bracket only this test's exec (other tests' D-stage runs can only INCREASE a
//! non-bracketed counter — which is why each admitted assertion reads the counter immediately
//! around its own exec and every deferred assertion is `≥ 1`).
#![cfg(feature = "rho-languages")]

use mettail_repl::rho_backends::{calculator_backed, rhocalc_backed, swapdemo_backed};
use mettail_rholang_runtime::dstage_instrumentation::dovetail_report_invocations;
use mettail_runtime::{RuntimeBackend, RuntimeBackendArtifact, RuntimeObservationValue};

fn term_obs(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}

#[test]
fn admitted_swapdemo_exec_builds_no_dovetail_report() {
    let language = swapdemo_backed().expect("SwapDemo lazy backend installs");
    let term = language
        .parse_term("swap(A, B)")
        .expect("swap(A, B) parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted SwapDemo exec runs report-free in Rho");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED SwapDemo exec must build ZERO Dovetail reports (the D-stage is demoted)"
    );
    // Byte-identical exec result: the located Swap(A, B) redex fired in Rho → Pair(B, A).
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values,
        vec![term_obs("Pair", vec![term_obs("B", Vec::new()), term_obs("A", Vec::new())])],
        "the report-free match fires Swap(A, B) → Pair(B, A) exactly as the eager pipeline did"
    );
}

#[test]
fn admitted_swapdemo_multi_redex_exec_builds_no_dovetail_report() {
    // The locate-all surface stays report-free too: nested + multiple redexes are LOCATED by
    // the automaton from the reflected subject, never from report σ.
    let language = swapdemo_backed().expect("SwapDemo lazy backend installs");
    let term = language
        .parse_term("pair(swap(A, B), swap(B, A))")
        .expect("the two-redex term parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the multi-redex SwapDemo exec runs report-free in Rho");
    let after = dovetail_report_invocations();

    assert_eq!(after - before, 0, "locate-all admitted execs build ZERO Dovetail reports");
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(out.observed_count(), 2, "both located redexes fired (got {:?})", out.values);
    let pair_b_a = term_obs("Pair", vec![term_obs("B", Vec::new()), term_obs("A", Vec::new())]);
    let pair_a_b = term_obs("Pair", vec![term_obs("A", Vec::new()), term_obs("B", Vec::new())]);
    assert!(out.values.contains(&pair_b_a) && out.values.contains(&pair_a_b));
}

#[test]
fn admitted_calculator_exec_builds_no_dovetail_report() {
    let language = calculator_backed().expect("Calculator lazy backend installs");
    let term = language.parse_term("2 + 3").expect("2 + 3 parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted Calculator exec runs report-free on the Rho dataflow");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED Calculator exec must build ZERO Dovetail reports (E3 dataflow is report-free)"
    );
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Int(5)],
        "2 + 3 computes 5 on the Rho machine exactly as the eager pipeline did"
    );
}

#[test]
fn admitted_rhocalc_exec_builds_no_dovetail_report() {
    let language = rhocalc_backed().expect("RhoCalc lazy backend installs");
    // The single-channel COMM example (`rho_rhocalc_ast.rs` precedent): the receiver binds the
    // sent process and drops it, emitting "p" on OUT. Lowerable DIRECTLY by the AST mapper, so
    // the report-free F2 admits it.
    let term = language
        .parse_term(r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#)
        .expect("the RhoCalc COMM example parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted RhoCalc exec runs report-free on the Rho machine");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED RhoCalc exec must build ZERO Dovetail reports (direct AST lowering)"
    );
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Text("p".to_string())],
        "the COMM fired and the dropped process emitted \"p\", exactly as the eager pipeline did"
    );
}

#[test]
fn semantic_predicate_blocked_calculator_exec_builds_the_lazy_report() {
    // `5 / 0` is structurally lowerable but safe-arithmetic declines (`safe_div` → None): the
    // report-free F2 defers `SemanticPredicate`, and the wrapper LAZILY builds the checked
    // Dovetail report as the observational payload — today's exact outcome, now the ONLY place
    // the D-stage runs.
    let language = calculator_backed().expect("Calculator lazy backend installs");
    let term = language.parse_term("5 / 0").expect("5 / 0 parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the semantic-predicate deferral resolves to the checked Dovetail report");
    let after = dovetail_report_invocations();

    assert!(
        after - before >= 1,
        "a semantic-predicate-blocked exec must LAZILY build the Dovetail report \
         (delta {} < 1)",
        after - before
    );
    assert_eq!(
        report.backend(),
        RuntimeBackend::Dovetail,
        "the predicate payload is the checked Dovetail report"
    );
    assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
}

#[test]
fn gate_rejected_calculator_exec_builds_the_lazy_report_and_keeps_the_rejection_text() {
    // A free-variable scalar term is NOT lowerable to the Rho dataflow (no value for `x`): the
    // report-free F2 defers `GateReject`, the wrapper LAZILY builds the checked report, and the
    // report-carrying fallback re-derives today's exact rejection — so the exec fails with the
    // SAME message the eager pipeline produced, having built the report on the deferral path
    // only.
    let language = calculator_backed().expect("Calculator lazy backend installs");
    let term = language
        .parse_term("x + 1")
        .expect("the free-variable term parses");

    let before = dovetail_report_invocations();
    let err = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect_err("a non-lowerable term still fails at the Rho-default boundary");
    let after = dovetail_report_invocations();

    assert!(
        after - before >= 1,
        "a gate-rejected exec must LAZILY build the Dovetail report (delta {} < 1)",
        after - before
    );
    assert!(
        err.contains("Calculator term is not lowerable to Rho scalar dataflow"),
        "the deferral path preserves the eager pipeline's rejection text: {err}"
    );
}
