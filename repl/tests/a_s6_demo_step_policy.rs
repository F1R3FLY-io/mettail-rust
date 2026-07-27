// ─────────────────────────────────────────────────────────────────────────────
// Task #11 (extended 2026-07-26) — TURNED OFF IN FULL, not deleted.
//
// Every test in this file resolves its language through the REPL REGISTRY (or through a
// `*_backed()` wrapper, which is the registry's constructor). Per the USER decision "I
// don't want REPL integration for the non-production grammars!", SwapDemo and the eleven
// rho_net DEMONSTRATION grammars are no longer registered and their wrappers no longer
// exist, so the SUBJECT of every assertion below is gone. The subject was the
// REGISTRATION, not the language: none of these is relocatable into a language-scoped
// test, because what each one asserts is "the REPL registry exposes this demo and execs
// it on the machine".
//
// The BEHAVIOUR they covered is unaffected and stays covered directly, one file per
// family, in `rholang-runtime/tests/`: rho_net_equivalence (SwapDemo), rho_net_ac_firing
// (AcDemo), rho_net_ac_bag_firing (AcBagDemo), rho_net_nl_ac_firing (NlAcDemo),
// rho_net_ambient_firing (AmbDemo + AmbNewDemo), rho_net_inout_firing (InOutDemo),
// rho_net_comm_firing (CommDemo), rho_net_contextual_firing (CtxDemo),
// rho_net_bicong_firing (BiCongDemo), rho_net_beta_firing (LambdaDemo),
// rho_net_native_firing (NativeDemo) — each driving the same in-Rho path this file
// reached through the registry.
//
// Commented out rather than dropped silently so the A-S6 coverage matrix stays readable
// and so restoring it is a one-step edit if the REPL ever regains a demo profile.
// ─────────────────────────────────────────────────────────────────────────────

// //! A-S6 — the DEMO step-policy pins (the F5 discipline extended registry-wide).
// //!
// //! The runtime split after the demo flip: `dovetail_step_graph` is KEPT everywhere as
// //! LABELED HOST INTROSPECTION — the REPL `step` Layer-1 display evidence (rewrite-graph
// //! evidence (host)) — and NO exec result ever flows from it (production `exec` never
// //! reaches the step slot; pinned by the zero-D-stage suite). The Layer-2 `StepSession`
// //! COMM trace is the ONLY executable stepper.
// //!
// //! Per-demo routing (probed 2026-07-20, `scratchpad/as6_step_probe2.log`):
// //!
// //! * TYPED-path demos (AmbDemo/AmbNewDemo/InOutDemo/CommDemo/LambdaDemo/NativeDemo/
// //!   NativeFoldDemo) generate `dovetail_step_graph`; on a redex subject its REWRITE
// //!   graph has edges, so REPL `step` keeps the Layer-1 navigable graph (the Lambda
// //!   shape) — pinned here on LambdaDemo.
// //! * UNTYPED demos (AcDemo/AcBagDemo/NlAcDemo/CtxDemo/BiCongDemo) serve the D-stage
// //!   report in the step slot (the SwapDemo pattern); its DERIVATION graph fails the
// //!   Layer-1 keep condition, so `step` falls through to the Layer-2 live COMM trace
// //!   (the Ambient shape) — pinned here on AcDemo.
// //! * Demo Layer-2 traces ride the legacy `sa:`/`loc:`/`ac:` automaton channel families,
// //!   which the A-S5.6 τ-classifier deliberately does NOT classify (only the reserved
// //!   `^…` drive/subst/carrier families are τ) — every step is UNCLASSIFIED-VISIBLE and
// //!   the default τ filter hides nothing. Pinned here on AcDemo's trace.
// //! * The drive-variant composition stays Lambda/Ambient-ONLY: demos seed the machine
// //!   through `rho_net_match_invocation_to`, never `^drive` (`DRIVE_OPT_IN` pinned).
// #![cfg(feature = "rho-languages")]
//
// use mettail_repl::rho_backends::{acdemo_backed, lambdademo_backed};
// use mettail_runtime::{RuntimeBackendOutput, RuntimeDovetailGraphKind};
//
// /// The REPL's Layer-1 keep condition (`repl.rs` step-mode routing): a step-slot report is
// /// kept iff it is a REWRITE-kind Dovetail graph with at least one edge.
// fn layer_1_keeps(report: &mettail_runtime::RuntimeBackendReport) -> bool {
//     report
//         .as_dovetail()
//         .map(|dovetail| {
//             dovetail.graph_kind == RuntimeDovetailGraphKind::Rewrite
//                 && !dovetail.derivation_edges.is_empty()
//         })
//         .unwrap_or(false)
// }
//
// /// TYPED demo = Layer 1: LambdaDemo's step slot is the generated `dovetail_step_graph`,
// /// whose β-edged REWRITE graph satisfies the Layer-1 keep condition — host introspection,
// /// display-only (exec runs the in-Rho match path, zero D-stage — `zero_dstage_exec.rs`).
// #[test]
// fn a_s6_lambdademo_step_slot_yields_the_layer_1_typed_rewrite_graph() {
//     let language = lambdademo_backed().expect("LambdaDemo lazy backend installs");
//     let term = language.parse_term("(lam x. f(x), A)").expect("the β subject parses");
//     let report = language
//         .run_step_backend_report(term.as_ref())
//         .expect("the LambdaDemo step slot produces the generated dovetail_step_graph");
//     let dovetail = report.as_dovetail().expect("a Dovetail step report");
//     assert_eq!(
//         dovetail.graph_kind,
//         RuntimeDovetailGraphKind::Rewrite,
//         "LambdaDemo's step slot is the one-step REWRITE graph (typed path)"
//     );
//     assert!(
//         !dovetail.derivation_edges.is_empty(),
//         "the β subject has at least one rewrite successor (a β edge)"
//     );
//     assert!(layer_1_keeps(&report), "REPL step routing KEEPS LambdaDemo's Layer-1 graph");
// }
//
// /// UNTYPED demo = Layer-2 fall-through: AcDemo's step slot serves the D-stage report — a
// /// DERIVATION graph that fails the Layer-1 keep condition — so REPL `step` refines to the
// /// Layer-2 live COMM trace (the only executable stepper).
// #[test]
// fn a_s6_acdemo_step_slot_graph_fails_layer_1_so_routing_falls_through() {
//     let language = acdemo_backed().expect("AcDemo lazy backend installs");
//     let term = language
//         .parse_term("#{A | B | C}#")
//         .expect("the AC bag subject parses");
//     let report = language
//         .run_step_backend_report(term.as_ref())
//         .expect("the AcDemo step slot produces the untyped dovetail_report_for report");
//     let dovetail = report.as_dovetail().expect("a Dovetail report");
//     assert_ne!(
//         dovetail.graph_kind,
//         RuntimeDovetailGraphKind::Rewrite,
//         "AcDemo's untyped step-slot report is a DERIVATION graph, not a rewrite graph"
//     );
//     assert!(
//         !layer_1_keeps(&report),
//         "the Layer-1 keep condition fails — REPL step routing falls through to the \
//          Layer-2 live COMM trace"
//     );
// }
//
// /// The demo Layer-2 trace pin: AcDemo's machine-backed trace carries the located-match
// /// COMM on the legacy `ac:loc:` automaton channel family — deliberately UNCLASSIFIED by
// /// the τ-classifier (`tau == None`, so the default τ filter hides NOTHING; only the
// /// reserved `^…` drive/subst/carrier families classify) — and ends with the unfiltered
// /// terminal Output step observing the fired contractum.
// #[test]
// fn a_s6_acdemo_layer_2_trace_is_unclassified_visible_with_the_legacy_ac_channels() {
//     let language = acdemo_backed().expect("AcDemo lazy backend installs");
//     let term = language
//         .parse_term("#{A | B | C}#")
//         .expect("the AC bag subject parses");
//     let report = language
//         .run_reduction_trace_report(term.as_ref())
//         .expect("the AcDemo Layer-2 trace runs on the machine");
//     let RuntimeBackendOutput::ReductionTrace(trace) = report.output() else {
//         panic!("expected a reduction trace, got {:?}", report.output().kind_name());
//     };
//     assert!(trace.step_count() >= 2, "locate-COMM + Output: {} step(s)", trace.step_count());
//     for step in &trace.steps {
//         assert_eq!(
//             step.tau, None,
//             "the legacy sa:/loc:/ac: channel families are unclassified-VISIBLE by design — \
//              step {} ({}) must not be τ-classified",
//             step.ordinal, step.display
//         );
//     }
//     assert!(
//         trace.steps.iter().any(|step| {
//             step.kind == mettail_runtime::RuntimeReductionKind::Comm
//                 && step
//                     .comm
//                     .as_ref()
//                     .is_some_and(|comm| {
//                         comm.channels.iter().any(|channel| channel.contains("ac:loc:"))
//                     })
//         }),
//         "the located AC match fires as a COMM on the legacy ac:loc: channel family: {:?}",
//         trace
//             .steps
//             .iter()
//             .map(|step| (&step.kind, &step.comm))
//             .collect::<Vec<_>>()
//     );
//     assert!(
//         trace
//             .steps
//             .iter()
//             .any(|step| step.kind == mettail_runtime::RuntimeReductionKind::Output),
//         "the trace ends with terminal Output steps (never τ, never filtered)"
//     );
// }
//
// /// The drive-variant composition stays Lambda/Ambient-ONLY: the demo flip did NOT extend
// /// the `^drive` opt-in — demos seed the machine through the single-shot
// /// `rho_net_match_invocation_to` locate-and-fire path.
// #[test]
// fn a_s6_drive_opt_in_stays_lambda_ambient_only() {
//     assert_eq!(
//         mettail_rholang_codegen::DRIVE_OPT_IN,
//         ["Lambda", "Ambient"],
//         "the quiescence-driver opt-in is exactly {{Lambda, Ambient}} — demos are match-path"
//     );
// }
//
