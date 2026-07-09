//! Stage 4 (S-contextual, sub-slice 2) end-to-end: a GENERATED language's 2-ARY (n > 1) CONGRUENCE
//! (contextual) rewrite fires end-to-end as an atomic 2-premise JOIN COMM on the live f1r3node
//! Rholang interpreter, each hole matched + reduced IN RHO and routed to its OWN premise channel.
//!
//! `BiCongDemo` is a generated `language!` whose congruence rewrite `NodeCong: | S0 ~> T0, S1 ~> T1
//! |- Node(S0, S1) ~> Node(T0, T1)` closes the context `Node(_, _)` around TWO inner premises, whose
//! mechanism is the base rewrite `Flip: Swap(x, y) ~> Pair(y, x)`. This is the N-ARY generalization
//! of `rho_net_contextual_firing`'s unary `CtxDemo`:
//!
//!  1. [`BiCongDemoLanguage::dovetail_report_for`] saturates `Node(Swap(A, B), Swap(C, D))`: the TWO
//!     inner premise `Flip`s fire (`Swap(A, B) ~> Pair(B, A)` and `Swap(C, D) ~> Pair(D, C)`) and the
//!     e-graph congruence closure closes `Node(_, _)` IMPLICITLY — so `NodeCong` fires no explicit
//!     Dovetail rule;
//!  2. the generated [`BiCongDemoLanguage::rho_net_contextual_invocation_from_dovetail_to`] MATCHES
//!     IN RHO: the base automaton LOCATES each hole's premise redex from the ONE spread of the
//!     structurally reflected subject (M-reflect), fires each IN RHO, and routes each reduced hole to
//!     its OWN join premise channel `c(ℓ_i)` (hole `Node.0` → premise channel 0, `Node.1` → premise
//!     channel 1 — the hole↔channel correspondence);
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node RhoRuntime,
//!     where the installed 2-premise contextual JOIN (`contextual_join_receiver_par`, n = 2) binds
//!     BOTH reduced holes and emits `⟦Node(Pair(B, A), Pair(D, C))⟧` on `@OUT` — one atomic JOIN COMM.
//!
//! Because `Pair(B, A) ≠ Pair(D, C)`, `Node(Pair(B, A), Pair(D, C))` is NON-SYMMETRIC: observing
//! exactly this value is non-vacuous evidence that BOTH holes fired IN RHO and that each reduced hole
//! landed at its CORRECT context position (a swapped routing would land `Node(Pair(D, C), Pair(B,
//! A))`). `Node(Swap(A, B), Swap(C, D)) ≠ Node(Pair(B, A), Pair(D, C))`, so it is also non-vacuous
//! against the input.
//!
//! FV: `formal/rocq/rho_bridge/theories/ContextualAtomicJoinPlugging.v`'s n-ary matching-side arm
//! (`routed_nary_join_reassembles_located_holes` — the n located holes route to the n premise
//! channels and feed the proven n-ary join, which emits `plug(located_holes)`, report-absent).
#![cfg(feature = "bicong-demo-runtime")]

use std::sync::Arc;

use mettail_languages::bicongdemo::{BiCongDemoLanguage, BiCongDemoTerm, Proc};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct BiCongDemo's augmented `LanguageDef` and plan its Rho-default backend (the `Flip`
/// base σ-receiver AND the `NodeCong` 2-premise contextual join install alongside the structural
/// constructors), exactly as the Rho/Dovetail installer does.
fn bicong_demo_backend() -> (PlannedRhoBackend, String) {
    let source = BiCongDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated BiCongDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("BiCongDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("BiCongDemo (2-ary congruence) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The concrete subject `Node(Swap(A, B), Swap(C, D))`, built through the generated typed AST.
fn subject() -> BiCongDemoTerm {
    BiCongDemoTerm(Proc::Node(
        Arc::new(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B))),
        Arc::new(Proc::Swap(Arc::new(Proc::C), Arc::new(Proc::D))),
    ))
}

fn nullary(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}

fn pair(a: RuntimeObservationValue, b: RuntimeObservationValue) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: "Pair".to_string(), children: vec![a, b] }
}

/// The generated N-ARY CONTEXTUAL σ-injection fires the installed `NodeCong` atomic 2-premise JOIN
/// as ONE COMM, landing `Node(Pair(B, A), Pair(D, C))` — the reduced context — on OUT, each reduced
/// hole placed at its correct context position by the in-Rho hole routing.
#[tokio::test]
async fn bicongdemo_nary_contextual_rewrite_fires_as_a_join_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = bicong_demo_backend();

    assert_eq!(
        BiCongDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    let term = subject();

    // (1) DOVETAIL REPORT SEMANTICS: the TWO inner premise `Flip`s fire and the e-graph congruence
    // closure closes `Node(_, _)` implicitly, so the reduction is Complete with the two Flip premise
    // firings (NodeCong fires no explicit rule).
    let report = BiCongDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("BiCongDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic Node(Swap(A,B), Swap(C,D)) reduction reports Complete: {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        2,
        "two premises (both Flip) fire for Node(Swap(A,B), Swap(C,D)); NodeCong closes by congruence, got {:?}",
        report.rewrite_justifications
    );
    for justification in &report.rewrite_justifications {
        assert_eq!(justification.rule_label, "Flip", "each fired premise is the base rewrite Flip");
    }

    // (2) The generated N-ARY CONTEXTUAL σ-injection LOCATES each hole's premise redex IN RHO and
    // routes each reduced hole to its OWN join premise channel.
    let invocation =
        BiCongDemoLanguage::rho_net_contextual_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("BiCongDemo n-ary contextual injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // (3) RHO-MACHINE EXECUTION: run the installed program (Flip σ-receiver ∥ NodeCong 2-premise
    // contextual join) ∥ call, and observe OUT. The join binds BOTH reduced holes and emits
    // ⟦Node(Pair(B, A), Pair(D, C))⟧ on @OUT — one atomic 2-premise JOIN COMM.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the n-ary contextual injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the 2-premise contextual join must fire once (got {:?})",
        observation.values
    );

    // The reduced context: Node(Pair(B, A), Pair(D, C)) — each reduced hole at its CORRECT context
    // position (hole Node.0 → Pair(B,A), hole Node.1 → Pair(D,C)). A swapped routing would land
    // Node(Pair(D,C), Pair(B,A)), so exact equality here is non-vacuous evidence of correct routing.
    let node_pairs = RuntimeObservationValue::Term {
        constructor: "Node".to_string(),
        children: vec![pair(nullary("B"), nullary("A")), pair(nullary("D"), nullary("C"))],
    };
    assert_eq!(
        observation.values[0], node_pairs,
        "the 2-premise contextual join reassembled Node(Pair(B, A), Pair(D, C)) — both holes fired \
         in Rho and each landed at its correct context position"
    );
}

/// Stage 4 (S-contextual, sub-slice 2) — the N-ARY reassembled context is produced by the
/// automaton's IN-RHO NESTED FIRINGS at BOTH hole positions, NOT the host report σ. The n-ary
/// analogue of `s_contextual_holes_reassembled_in_rho_not_the_report`.
///
/// We take a real, complete report for `Node(Swap(A, B), Swap(C, D))` and CORRUPT BOTH premise
/// firings' σ to nonsense, leaving the rule labels (`Flip`) valid so the gate admits. If the
/// contextual injection reconstructed the holes from σ (the retired host-σ path), OUT would be the
/// corrupted `Node(Pair(Pair(...), ...), Pair(Pair(...), ...))`. It is instead the CORRECT
/// `Node(Pair(B, A), Pair(D, C))`, because the base automaton LOCATES + FIRES each hole's premise
/// redex from the spread of the structurally reflected `term` (M-reflect) and routes THOSE reduced
/// holes to the join — so BOTH reassembled holes are fed by the automaton's nested firings, never
/// the report σ.
#[tokio::test]
async fn s_contextual_nary_holes_reassembled_in_rho_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = bicong_demo_backend();
    let term = subject();

    let mut report = BiCongDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("BiCongDemo Dovetail report must compile");
    assert_eq!(
        report.rewrite_justifications.len(),
        2,
        "two premises (both Flip) fire for Node(Swap(A,B), Swap(C,D))"
    );

    // Deliberately WRONG σ on BOTH premise firings: were it read via the retired
    // `reconstruct_contractum`, OUT would carry the corrupted nested Pairs.
    let wrong = |c: &str| RuntimeReflectedSubterm {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeReflectedSubterm { constructor: c.to_string(), children: Vec::new() },
            RuntimeReflectedSubterm { constructor: c.to_string(), children: Vec::new() },
        ],
    };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("x".to_string(), wrong("A")), ("y".to_string(), wrong("B"))];
        assert_eq!(justification.rule_label, "Flip", "the fired premise labels stay valid");
    }

    let invocation =
        BiCongDemoLanguage::rho_net_contextual_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the n-ary contextual MATCH path admits the subject with a corrupted report σ");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho n-ary contextual match + join executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "the 2-premise contextual join fired once (got {:?})",
        observation.values
    );

    // The reduced context is Node(Pair(B, A), Pair(D, C)) — BOTH reduced holes came from the sa:
    // nested firings (the reflected term spread), NOT the corrupted report σ.
    let node_pairs = RuntimeObservationValue::Term {
        constructor: "Node".to_string(),
        children: vec![pair(nullary("B"), nullary("A")), pair(nullary("D"), nullary("C"))],
    };
    assert_eq!(
        observation.values[0], node_pairs,
        "both reduced holes were reassembled from the in-Rho nested firings, NOT reconstruct_contractum"
    );
    // Non-vacuity: a value carrying the corrupted σ's nested Pairs is demonstrably absent.
    assert_ne!(
        observation.values[0],
        RuntimeObservationValue::Term {
            constructor: "Node".to_string(),
            children: vec![
                pair(pair(nullary("B"), nullary("B")), pair(nullary("A"), nullary("A"))),
                pair(pair(nullary("B"), nullary("B")), pair(nullary("A"), nullary("A"))),
            ],
        },
        "the host report σ was demonstrably NOT used to reassemble either hole"
    );
}
