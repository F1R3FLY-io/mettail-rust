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
//!
//! A-S3 (native dispatch boundary tightening): the zero-D-stage NATIVE exec MECHANISM probes
//! live in the RUNTIME suites (`rholang-runtime/tests/rho_net_native_firing.rs`
//! `a_s3_admitted_native_exec_builds_no_dovetail_report` — delta 0 with the machine-invoked
//! registered handler's value — and `rho_net_native_fold_firing.rs`
//! `a_s3_multi_site_native_exec_admits_and_fires_each_site`). Since A-S6 NativeDemo /
//! NativeFoldDemo ARE REPL-registered backends, so the registered-wrapper native exec is
//! additionally pinned zero-D-stage HERE (`a_s6_admitted_nativefolddemo_exec…` below).
//!
//! A-S5.6 (the production flip): Lambda + Ambient join the admitted set — their default exec
//! path is the in-Rho QUIESCENCE DRIVER (`rho_net_drive_invocation_to` seeding the installed
//! `^drive` receiver family), so an admitted exec builds ZERO Dovetail reports while the whole
//! reduction (β chains / guarded AC mobility firings, contractum re-drives, quiescence) runs as
//! COMMs on the Rho machine, cross-checked by the always-on §4.7 ledger/NF-scan.
//!
//! A-S6 (the demo flip): every rho_net demo joins the admitted set on the report-free
//! set-automaton match path — pinned below for one AC demo (AcDemo), one base-rewrite demo
//! (CtxDemo's root-position `Flip`), and one native demo (NativeFoldDemo).
#![cfg(feature = "rho-languages")]

use mettail_languages::calculator::CalculatorLanguage;
// Task #11 (extended 2026-07-26): `swapdemo_backed`, `acdemo_backed` and `ctxdemo_backed`
// are gone — SwapDemo and the eleven rho_net DEMONSTRATION grammars are de-productionized
// out of the REPL (USER: "I don't want REPL integration for the non-production grammars!").
// The four PRODUCTION wrappers keep the zero-D-stage lock unchanged.
use mettail_repl::rho_backends::{
    ambient_backed, calculator_backed, lambda_backed, rholang_backed,
};
use mettail_rholang_codegen::{
    RhoFoldDataflowDisposition, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::dstage_instrumentation::dovetail_report_invocations;
use mettail_runtime::{Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeObservationValue};
use models::rhoapi::Par;
use prost::Message;

fn term_obs(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}

// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test asserted the
// zero-D-stage property of a *REPL-REGISTERED* wrapper. Per the USER decision "I don't
// want REPL integration for the non-production grammars!" the wrapper no longer exists,
// so the property it names has no subject in the REPL. It is NOT relocatable: the
// subject was the registration, not the language.
// Covered: SwapDemo's single-redex zero-D-stage lock. The property is unchanged and is asserted directly against the same in-Rho path by `rholang-runtime/tests/rho_net_equivalence.rs`.
// #[test]
// fn admitted_swapdemo_exec_builds_no_dovetail_report() {
//     let language = swapdemo_backed().expect("SwapDemo lazy backend installs");
//     let term = language
//         .parse_term("swap(A, B)")
//         .expect("swap(A, B) parses");
//
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .expect("the admitted SwapDemo exec runs report-free in Rho");
//     let after = dovetail_report_invocations();
//
//     assert_eq!(
//         after - before,
//         0,
//         "an ADMITTED SwapDemo exec must build ZERO Dovetail reports (the D-stage is demoted)"
//     );
//     // Byte-identical exec result: the located Swap(A, B) redex fired in Rho → Pair(B, A).
//     assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
//     let out = report
//         .observations_for_channel("OUT")
//         .expect("an OUT observation");
//     assert_eq!(
//         out.values,
//         vec![term_obs("Pair", vec![term_obs("B", Vec::new()), term_obs("A", Vec::new())])],
//         "the report-free match fires Swap(A, B) → Pair(B, A) exactly as the eager pipeline did"
//     );
// }
//
// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test asserted the
// zero-D-stage property of a *REPL-REGISTERED* wrapper. Per the USER decision "I don't
// want REPL integration for the non-production grammars!" the wrapper no longer exists,
// so the property it names has no subject in the REPL. It is NOT relocatable: the
// subject was the registration, not the language.
// Covered: SwapDemo's MULTI-redex zero-D-stage lock. Same successor: `rholang-runtime/tests/rho_net_equivalence.rs` drives the multi-redex subject on the machine without the registry.
// #[test]
// fn admitted_swapdemo_multi_redex_exec_builds_no_dovetail_report() {
//     // The locate-all surface stays report-free too: nested + multiple redexes are LOCATED by
//     // the automaton from the reflected subject, never from report σ.
//     let language = swapdemo_backed().expect("SwapDemo lazy backend installs");
//     let term = language
//         .parse_term("pair(swap(A, B), swap(B, A))")
//         .expect("the two-redex term parses");
//
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .expect("the multi-redex SwapDemo exec runs report-free in Rho");
//     let after = dovetail_report_invocations();
//
//     assert_eq!(after - before, 0, "locate-all admitted execs build ZERO Dovetail reports");
//     let out = report
//         .observations_for_channel("OUT")
//         .expect("an OUT observation");
//     assert_eq!(out.observed_count(), 2, "both located redexes fired (got {:?})", out.values);
//     let pair_b_a = term_obs("Pair", vec![term_obs("B", Vec::new()), term_obs("A", Vec::new())]);
//     let pair_a_b = term_obs("Pair", vec![term_obs("A", Vec::new()), term_obs("B", Vec::new())]);
//     assert!(out.values.contains(&pair_b_a) && out.values.contains(&pair_a_b));
// }
//
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
fn admitted_rholang_exec_builds_no_dovetail_report() {
    let language = rholang_backed().expect("RhoCalc lazy backend installs");
    // The single-channel COMM example (`rho_rholang_ast.rs` precedent): the receiver binds the
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

/// A-S5.6: an ADMITTED Lambda exec drives the whole β-chain to NF fully in-Rho — ZERO
/// Dovetail reports; the observed resting term is the reflected NF (K = `^lambda(^lambda
/// (^bound 1))` for `(λx.x) K`).
#[test]
fn a_s5_6_admitted_lambda_exec_builds_no_dovetail_report() {
    let language = lambda_backed().expect("Lambda lazy backend installs");
    let term = language
        .parse_term("(lam x. x, lam a. lam b. a)")
        .expect("the single-β subject parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted Lambda exec drives to NF in-Rho");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED Lambda exec must build ZERO Dovetail reports (the in-Rho quiescence \
         driver is the default exec path)"
    );
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    // K = λ.λ.1 — the α-erased de Bruijn image of `lam a. lam b. a` (Peano depth `^S(^Z)`).
    // The tags come from the codegen CONSTANTS, never re-spelled: #36 S3 moved the Peano
    // numerals into the `^` namespace, and a literal spelling would have kept asserting the
    // OLD ABI while the runtime emitted the new one.
    let konst = term_obs(
        LAMBDA_REFLECT_LABEL,
        vec![term_obs(
            LAMBDA_REFLECT_LABEL,
            vec![term_obs(
                BOUND_VAR_REFLECT_LABEL,
                vec![term_obs(
                    PEANO_SUCC_REFLECT_LABEL,
                    vec![term_obs(PEANO_ZERO_REFLECT_LABEL, Vec::new())],
                )],
            )],
        )],
    );
    assert_eq!(
        out.values,
        vec![konst],
        "(λx.x) K rests at K fully in-Rho — β fired through the σ ABI + subst TRS"
    );
}

/// A-S5.6: an ADMITTED Ambient exec fires the guarded AC redex fully in-Rho — ZERO Dovetail
/// reports; `{open(n, a[{0}]) | n[{b[{0}]}]}` rests at the flat bag `{a[{0}], b[{0}]}`.
#[test]
fn a_s5_6_admitted_ambient_exec_builds_no_dovetail_report() {
    let language = ambient_backed().expect("Ambient lazy backend installs");
    let term = language
        .parse_term("{open(n, a[{0}]) | n[{b[{0}]}]}")
        .expect("the open subject parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted Ambient exec drives to quiescence in-Rho");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED Ambient exec must build ZERO Dovetail reports (the in-Rho quiescence \
         driver is the default exec path)"
    );
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(out.observed_count(), 1, "one quiescent resting term: {:?}", out.values);
    // The resting term is a FLAT two-element bag of ambients `a[{0}]` / `b[{0}]` — free
    // Ambient names decode as `^free(<moniker debug>)` leaves whose exact strings are
    // gensym-dependent, so this pins the structure (flat multiset of two 2-child PAmb
    // nodes), not name bytes; the α-exact golden lives in `a_s5_6_exec_goldens.rs`.
    let RuntimeObservationValue::Bag(entries) = &out.values[0] else {
        panic!("the Ambient resting term decodes as a bag soup: {:?}", out.values[0]);
    };
    let element_count: usize = entries.iter().map(|(_, count)| count).sum();
    assert_eq!(element_count, 2, "open fired: {{a[{{0}}], b[{{0}}]}} is FLAT: {entries:?}");
    for (element, _) in entries {
        let RuntimeObservationValue::Term { constructor, children } = element else {
            panic!("each resting element is an ambient node: {element:?}");
        };
        assert_eq!(constructor, "PAmb", "each resting element is an ambient: {element:?}");
        assert_eq!(children.len(), 2, "PAmb(name, body): {element:?}");
    }
}

// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test asserted the
// zero-D-stage property of a *REPL-REGISTERED* wrapper. Per the USER decision "I don't
// want REPL integration for the non-production grammars!" the wrapper no longer exists,
// so the property it names has no subject in the REPL. It is NOT relocatable: the
// subject was the registration, not the language.
// Covered: AcDemo's AC-family zero-D-stage lock. Successor: `rholang-runtime/tests/rho_net_ac_firing.rs`.
// /// A-S6: an ADMITTED AC-demo exec locates and fires the bag redex fully in-Rho — ZERO
// /// Dovetail reports; `#{A | B | C}#` fires `AcStep . {x, ...rest} ~> wrap(x)` for one
// /// located pick.
// #[test]
// fn a_s6_admitted_acdemo_exec_builds_no_dovetail_report() {
//     let language = acdemo_backed().expect("AcDemo lazy backend installs");
//     let term = language
//         .parse_term("#{A | B | C}#")
//         .expect("the AC bag subject parses");
//
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .expect("the admitted AcDemo exec runs report-free in Rho");
//     let after = dovetail_report_invocations();
//
//     assert_eq!(
//         after - before,
//         0,
//         "an ADMITTED AcDemo exec must build ZERO Dovetail reports (the report-free \
//          set-automaton match is the default exec path — A-S6)"
//     );
//     assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
//     let out = report
//         .observations_for_channel("OUT")
//         .expect("an OUT observation");
//     assert_eq!(out.observed_count(), 1, "one located AC firing (got {:?})", out.values);
//     assert!(
//         matches!(
//             &out.values[0],
//             RuntimeObservationValue::Term { constructor, .. } if constructor == "Wrap"
//         ),
//         "AcStep fired {{x, ...rest}} ~> wrap(x): {:?}",
//         out.values
//     );
// }
//
// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test asserted the
// zero-D-stage property of a *REPL-REGISTERED* wrapper. Per the USER decision "I don't
// want REPL integration for the non-production grammars!" the wrapper no longer exists,
// so the property it names has no subject in the REPL. It is NOT relocatable: the
// subject was the registration, not the language.
// Covered: CtxDemo's root-position base-rewrite zero-D-stage lock. Successor: `rholang-runtime/tests/rho_net_contextual_firing.rs`.
// /// A-S6: an ADMITTED base-rewrite demo exec fires in-Rho with ZERO Dovetail reports —
// /// CtxDemo's `swap(A, B)` at the ROOT fires the flat base rewrite `Flip` (`~> pair(B, A)`),
// /// exactly the SwapDemo family shape.
// #[test]
// fn a_s6_admitted_ctxdemo_base_flip_exec_builds_no_dovetail_report() {
//     let language = ctxdemo_backed().expect("CtxDemo lazy backend installs");
//     let term = language.parse_term("swap(A, B)").expect("the flat Flip subject parses");
//
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .expect("the admitted CtxDemo exec runs report-free in Rho");
//     let after = dovetail_report_invocations();
//
//     assert_eq!(
//         after - before,
//         0,
//         "an ADMITTED CtxDemo exec must build ZERO Dovetail reports (A-S6)"
//     );
//     assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
//     let out = report
//         .observations_for_channel("OUT")
//         .expect("an OUT observation");
//     assert_eq!(
//         out.values,
//         vec![term_obs("Pair", vec![term_obs("B", Vec::new()), term_obs("A", Vec::new())])],
//         "Flip fired swap(A, B) ~> pair(B, A) in Rho"
//     );
// }
//
// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test asserted the
// zero-D-stage property of NativeFoldDemo's *REPL-REGISTERED* wrapper. Per the USER
// decision "I don't want REPL integration for the non-production grammars!",
// NativeFoldDemo is no longer REPL-registered and `nativefolddemo_backed` no longer
// exists, so the property this test names has no subject in the REPL any more. It is
// NOT relocatable: the subject was the registration itself, not the language. The
// underlying in-Rho native-scalar-fold firing stays covered end-to-end by
// `rholang-runtime/tests/rho_net_native_fold_firing.rs`. The remaining production
// languages in this file keep the zero-D-stage lock unchanged.
// /// A-S6: an ADMITTED native-demo exec through the REGISTERED wrapper computes on the
// /// machine with ZERO Dovetail reports — the located AddInt site registers its machine-side
// /// handler (the wrapper's clear/drain bracket) and the dispatch COMM computes `2 + 3 = 5`
// /// at COMM time (closing the A-S3 note above: the native demos are REPL backends now).
// #[test]
// fn a_s6_admitted_nativefolddemo_exec_builds_no_dovetail_report() {
//     let language = nativefolddemo_backed().expect("NativeFoldDemo lazy backend installs");
//     let term = language.parse_term("2 + 3").expect("the native redex parses");
//
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .expect("the admitted NativeFoldDemo exec runs report-free on the machine");
//     let after = dovetail_report_invocations();
//
//     assert_eq!(
//         after - before,
//         0,
//         "an ADMITTED NativeFoldDemo exec must build ZERO Dovetail reports (A-S6)"
//     );
//     assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
//     let out = report
//         .observations_for_channel("OUT")
//         .expect("an OUT observation");
//     assert_eq!(
//         out.values,
//         vec![term_obs("NumLit(5)", Vec::new())],
//         "the registered handler computed 2 + 3 = 5 at COMM time"
//     );
// }

/// A-S3/A-S4 probe helper: whether the prost-encoded bytes of `par` contain `needle`.
fn par_bytes_contain(par: &Par, needle: &[u8]) -> bool {
    let bytes = par.encode_to_vec();
    bytes.windows(needle.len()).any(|window| window == needle)
}

/// The byte needle for "the ground `GInt` literal `value` rides this `Par`" (a `Par` embedded in
/// any message field serializes its own content contiguously).
fn gint_par_needle(value: i64) -> Vec<u8> {
    models::rust::utils::new_gint_par(value, Vec::new(), false).encode_to_vec()
}

/// A-S4 deliverable-3 probe (Calculator `2 + 3 * 4`): the RAW parse tree lowers to the E3
/// metered-expression dataflow — the injected call `Par` carries the OPERANDS (2, 3, 4) but NOT
/// the result literal 14 (byte-level, A-S3 style; the single-literal dataflow of `14` is the
/// contrastive control proving needle sensitivity) — and the exec through the production wrapper
/// computes 14 ON the machine with zero D-stage.
#[test]
fn a_s4_calculator_call_par_does_not_embed_the_result_literal() {
    // The injected call: the report-free E3 dataflow of the RAW tree.
    let term = CalculatorLanguage
        .parse_term("2 + 3 * 4")
        .expect("2 + 3 * 4 parses");
    let invocation = match CalculatorLanguage::rho_fold_dataflow_invocation_to(term.as_ref(), "OUT")
    {
        Ok(RhoFoldDataflowDisposition::Run(invocation)) => invocation,
        other => panic!("the raw arithmetic tree must lower to a Run dataflow, got {other:?}"),
    };
    assert!(
        par_bytes_contain(&invocation.call, &gint_par_needle(2)),
        "operand 2 rides the call"
    );
    assert!(
        par_bytes_contain(&invocation.call, &gint_par_needle(3)),
        "operand 3 rides the call"
    );
    assert!(
        par_bytes_contain(&invocation.call, &gint_par_needle(4)),
        "operand 4 rides the call"
    );
    assert!(
        !par_bytes_contain(&invocation.call, &gint_par_needle(14)),
        "A-S4: no host-pre-computed value may ride the injected call Par"
    );

    // Contrastive control: the single-literal dataflow of `14` DOES embed the literal — the
    // needle is sensitive.
    let literal = CalculatorLanguage.parse_term("14").expect("14 parses");
    let control = match CalculatorLanguage::rho_fold_dataflow_invocation_to(literal.as_ref(), "OUT")
    {
        Ok(RhoFoldDataflowDisposition::Run(invocation)) => invocation,
        other => panic!("the literal must lower to a Run dataflow, got {other:?}"),
    };
    assert!(
        par_bytes_contain(&control.call, &gint_par_needle(14)),
        "the needle detects an embedded result literal (control)"
    );

    // The MACHINE computes 14 (zero D-stage): the production wrapper execs the same raw tree.
    let language = calculator_backed().expect("Calculator lazy backend installs");
    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the raw arithmetic exec runs report-free on the Rho dataflow");
    let after = dovetail_report_invocations();
    assert_eq!(after - before, 0, "the admitted raw-tree exec builds ZERO Dovetail reports");
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Int(14)],
        "2 + 3 * 4 computes 14 on the Rho machine (E3 metered exprs)"
    );
}

/// A-S4 (RhoCalc): raw Proc-level arithmetic execs through the PURE lowering (the E2
/// fold-normalization fallback is deleted) — the machine's metered `EPlus` computes the value;
/// zero Dovetail reports. Plain rholang literals are arbitrary-precision (`GBigInt`), so the
/// observed value is `BigIntBytes`.
#[test]
fn a_s4_admitted_rholang_arithmetic_exec_computes_on_machine_with_no_dovetail_report() {
    let language = rholang_backed().expect("RhoCalc lazy backend installs");
    let term = language.parse_term("1 + 2").expect("1 + 2 parses");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the raw RhoCalc arithmetic exec runs report-free on the Rho machine");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "A-S4: the raw arithmetic exec lowers directly (metered EPlus) — ZERO Dovetail reports \
         (pre-A-S4 this shape rode the E2 dovetail_normal_term fallback)"
    );
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Int(3)],
        // ★ `Int`, not `BigIntBytes` (divergence I, 2026-07-25). A plain RhoCalc numeral is
        // f1r3node's `GInt` — `normalize_ground` says so — and RhoCalc's grammar now agrees, so
        // bare literals ride the wire as `GInt`. This is a DELIBERATE wire re-baseline; no
        // persisted rspace state exists on this branch (the demos build in-memory runtimes per
        // invocation).
        "1 + 2 computes 3 on the Rho machine (plain literals are GInt)"
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
