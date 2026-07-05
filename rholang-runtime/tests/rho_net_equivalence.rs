//! Epic 4 (R-5) end-to-end equivalence: **Dovetail report semantics** vs
//! **RhoNet/Rho-machine execution**, driven entirely through the GENERATED path
//! (pgmcp #2010).
//!
//! Where the hand-built `rho_net_injection_demo` (R-2) supplies σ directly as the
//! call arguments, this test derives σ from the generated
//! [`SwapDemoLanguage::dovetail_report_for`] — the report producer that resolves +
//! bare-ifies σ provenance (R-4) — then feeds that report to the generated
//! [`SwapDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection F-function,
//! bridges it through [`build_rho_net_injection_invocation_from_contract`] (the
//! Epic-4 injection adapter), and runs it against the language's INSTALLED
//! σ-receiver program on the real in-memory f1r3node Rho machine.
//!
//! The equivalence claim is checked against the report's OWN σ, not a hard-coded
//! oracle: the Rho machine must land exactly `RHS(SwapStep) = Pair(y, x)` with the
//! substitution the Dovetail report computed applied — `Pair(σ[y], σ[x])`. Because
//! `Swap(A, B) ≠ Pair(B, A)`, a positive OUT observation is non-vacuous evidence
//! the base rewrite fired with Dovetail's σ, and the two engines agree.
//!
//! Fingerprint coherence is asserted explicitly: the planned backend (reconstructed
//! from the generated `definition_source`, exactly as the production installer does)
//! must carry the same `definition_fingerprint` the generated metadata exposes, so
//! the σ-receiver's reflected RHS constructors and the σ-injection's reflected σ
//! arguments tag identically — otherwise the receiver would never fire.
#![cfg(feature = "swap-demo-runtime")]

use std::collections::HashMap;
use std::sync::Arc;

use mettail_languages::swapdemo::{Proc, SwapDemoLanguage, SwapDemoTerm};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, RhoNetRuleKind,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct SwapDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` (the macro-time def, composition + auto-injection),
/// exactly as the Rho/Dovetail installer does for a real language, then plan its
/// Rho-default backend. Returns the planned backend and the plan's definition
/// fingerprint (which must equal the generated metadata fingerprint).
fn swap_demo_backend() -> (PlannedRhoBackend, String) {
    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated SwapDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("SwapDemoLanguage definition_source must reconstruct as a LanguageDef");

    // The four non-scalar `Proc` constructors are rejected by scalar lowering and
    // covered by the language-derived structural dispositions; SwapDemo has no
    // guards, so the flip gate passes with `NoGuardObligations`.
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("Swap→Pair language must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// Rebuild a runtime-neutral report σ sub-term into the structural observation
/// value it must equal on OUT (both are the same `{ constructor, children }`
/// shape). Used to derive the expected Rho output from the report's OWN σ.
fn reflected_to_observation(subterm: &RuntimeReflectedSubterm) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: subterm.constructor.clone(),
        children: subterm.children.iter().map(reflected_to_observation).collect(),
    }
}

/// A bare nullary σ sub-term, e.g. `A` or `B`, as the report carries it post-R-4.
fn nullary_subterm(constructor: &str) -> RuntimeReflectedSubterm {
    RuntimeReflectedSubterm { constructor: constructor.to_string(), children: Vec::new() }
}

#[tokio::test]
async fn dovetail_report_semantics_match_rho_machine_execution_for_swap() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = swap_demo_backend();

    // Fingerprint coherence: the σ-receiver (installed from the reconstructed def)
    // and the σ-injection (which reflects with `metadata().definition_fingerprint()`)
    // must agree, or the receiver could not recognize the reflected σ.
    assert_eq!(
        SwapDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete term `Swap(A, B)`, built directly through the generated term
    // wrapper (no parse — sidesteps any keyword-`A`/`B` vs auto-`PVar` ambiguity).
    // `Swap(A, B) ≠ Pair(B, A)`, so a positive OUT observation is non-vacuous
    // evidence the rewrite fired.
    let term = SwapDemoTerm(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B)));

    // (1) DOVETAIL REPORT SEMANTICS. The generated producer resolves + bare-ifies σ
    // (R-4); `Swap(A, B) → Pair(B, A)` saturates acyclically, so the report is
    // Complete.
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("SwapDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic Swap→Pair reduction must report Complete, got {:?}",
        report.completeness
    );

    // Dovetail's structural match result: exactly one firing, rule `SwapStep`, with
    // σ = {x ↦ A, y ↦ B} — each constructor bare-ified to its source identity (R-4),
    // so it reflects identically to the σ-receiver's compiled RHS constructors.
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one base rewrite fires for Swap(A, B)"
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "SwapStep", "the fired rule is SwapStep");
    let sigma: HashMap<&str, &RuntimeReflectedSubterm> = justification
        .sigma
        .iter()
        .map(|(name, subterm)| (name.as_str(), subterm))
        .collect();
    assert_eq!(*sigma["x"], nullary_subterm("A"), "Dovetail bound the LHS variable x ↦ A");
    assert_eq!(*sigma["y"], nullary_subterm("B"), "Dovetail bound the LHS variable y ↦ B");

    // (2) The generated σ-injection F-function reads that report and assembles the
    // closed injection `call` (reordering σ into the σ-receiver's LHS variable order
    // and reflecting each sub-term with the metadata fingerprint).
    let invocation = SwapDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect("SwapDemo σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge adapter selects the INSTALLED-σ-receiver observation shape
    // (not the scalar `program()` shape), so the base rewrite actually fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the Rho-net injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION. Run the installed σ-receiver program ∥ call and
    // observe closed Rho ground values on OUT.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the σ injection must execute on the Rho runtime");

    // Non-vacuity (the R-2 vacuity trap): the σ-receiver fired exactly once and left
    // exactly one value on OUT. A composition that reached no contract would be empty.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the σ-receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE, checked against the report's OWN σ (not a hard-coded oracle): the
    // Rho machine must land `RHS(SwapStep) = Pair(y, x)` with Dovetail's σ applied,
    // i.e. `Pair(σ[y], σ[x])`. This is precisely "Dovetail report semantics" realized
    // by "Rho-machine execution".
    let expected_from_report = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![reflected_to_observation(sigma["y"]), reflected_to_observation(sigma["x"])],
    };
    assert_eq!(
        observation.values[0], expected_from_report,
        "Rho execution must equal Pair(σ[y], σ[x]) — the report's RHS under its own σ"
    );

    // …and that normal form is concretely `Pair(B, A)`, non-vacuous against the input
    // `Swap(A, B)`.
    let pair_b_a = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        ],
    };
    assert_eq!(
        observation.values[0], pair_b_a,
        "the Rho machine reduced Swap(A, B) to the reflected normal form Pair(B, A)"
    );
}

#[tokio::test]
async fn injection_fails_closed_when_no_rewrite_fires() {
    mettail_runtime::clear_var_cache();

    // `Pair(A, B)` is already a normal form — no base rewrite matches it, so the
    // complete report carries no rewrite justification.
    let term = SwapDemoTerm(Proc::Pair(Arc::new(Proc::A), Arc::new(Proc::B)));
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("a normal-form term still produces a complete report");
    assert!(report.is_complete(), "a normal form saturates immediately");
    assert!(
        report.rewrite_justifications.is_empty(),
        "no redex ⇒ no firing ⇒ no σ justification (got {:?})",
        report.rewrite_justifications
    );

    // With nothing to inject, the generated F-function must fail closed rather than
    // fabricate a call against the σ-receiver.
    let error = SwapDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect_err("with no firing the injection must fail closed");
    assert!(
        error.contains("no rewrite justification to fire"),
        "the fail-closed error must name the missing justification, got: {error}"
    );
}

#[test]
fn swap_demo_exposes_its_rho_net_program_directly() {
    // Epic 6 #2030: a generated language exposes its RhoNet planning artifact —
    // planned channels + rule identities — DIRECTLY via `rho_net_program()`,
    // without the caller reconstructing the `LanguageDef` by hand.
    let program =
        SwapDemoLanguage::rho_net_program().expect("SwapDemo exposes its RhoNet program");
    let swap_rule = program
        .rules
        .iter()
        .find(|rule| rule.label.as_deref() == Some("SwapStep"))
        .expect("the SwapStep base rewrite is a planned RhoNet rule");
    assert_eq!(swap_rule.kind, RhoNetRuleKind::BaseRewrite);
    assert!(
        !swap_rule.input_channels.is_empty(),
        "the planned σ-receiver rule carries a source channel"
    );
    assert!(!program.channels.is_empty(), "the program plans at least one channel");
}
