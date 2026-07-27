//! Epic 4 R-2 empirical validation: a base rewrite reduces on the Rho machine.
//!
//! This hand-builds a σ-injection for the base rewrite `Swap(a, b) ~> Pair(b, a)`
//! (nullary `A`, `B`), installs that rewrite's σ-receiver via the planned Rho
//! backend, injects `Swap(A, B)` as the two σ arguments in first-occurrence order,
//! and observes that the Rho machine leaves the reflected normal form `Pair(B, A)`
//! resting on `@"OUT"`.
//!
//! No Dovetail report is involved — σ = {a ↦ A, b ↦ B} is supplied directly as the
//! two call arguments — so the test isolates exactly the R-2 claim: the compiled
//! σ-receiver fires and the reflected RHS (with σ applied) lands on the out
//! channel. That is the model executing on Rho.
//!
//! The vacuity trap (design risk R2) is guarded explicitly: OUT is asserted
//! non-empty, so a composition that reached no contract (the bug the R-2
//! composition fix exists to prevent) fails loudly instead of passing silently.

use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reflect_ground_term_par,
    suggest_rejected_rule_dispositions, term_contract_call, GroundTerm, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::RuntimeObservationValue;

/// Swap→Pair over nullary `A`/`B`. `Swap(A, B) ≠ Pair(B, A)`, so a positive OUT
/// observation is non-vacuous evidence the rewrite actually fired.
const SWAP_DEMO_FRAGMENT: &str = r#"
    name: SwapInjectionDemo,
    options {
        emit_simulator: false,
        emit_blockly: false,
    },
    types {
        Proc
    },
    terms {
        A . |- "A" : Proc ;
        B . |- "B" : Proc ;
        Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
        Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
    },
    equations {},
    rewrites {
        SwapStep . |- (Swap x y) ~> (Pair y x) ;
    }
"#;

/// The Pair(B, A) normal form as a structural observation value.
fn expected_pair_b_a() -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term {
                constructor: "B".to_string(),
                children: Vec::new(),
            },
            RuntimeObservationValue::Term {
                constructor: "A".to_string(),
                children: Vec::new(),
            },
        ],
    }
}

#[tokio::test]
async fn sigma_injection_reduces_swap_to_pair_on_the_rho_machine() {
    let def = syn::parse_str::<mettail_ast::language::LanguageDef>(SWAP_DEMO_FRAGMENT)
        .expect("Swap demo fragment must parse");

    // Plan the Rho-default backend. The four non-scalar `Proc` constructors are
    // rejected by scalar lowering and covered by the language-derived structural
    // dispositions, so the flip gate passes.
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

    // Derive the σ-receiver's source channel from the base rewrite itself
    // (`input_channels.first()`), exactly as the σ-receiver lowering resolves it —
    // never hard-coded, since it is a content fingerprint.
    let swap_rule = plan
        .rho_net_program()
        .rules
        .iter()
        .find(|rule| rule.label.as_deref() == Some("SwapStep"))
        .expect("SwapStep base rewrite must be planned");
    let sigma_channel = swap_rule
        .input_channels
        .first()
        .expect("Swap σ-receiver must have a source channel")
        .clone();

    // Hand-build the injection: σ = {a ↦ A, b ↦ B}, the two reflected ground
    // arguments in first-occurrence (a, b) order, plus the OUT channel appended
    // last. `A`/`B` reflect with the plan's fingerprint so their tags match the
    // language the σ-receiver was compiled for.
    let arg_a = reflect_ground_term_par(&GroundTerm::nullary("A"), &fingerprint);
    let arg_b = reflect_ground_term_par(&GroundTerm::nullary("B"), &fingerprint);
    let call = term_contract_call(&sigma_channel, vec![arg_a, arg_b], "OUT");

    // Install the σ-receiver program ∥ call and observe OUT on the real in-memory
    // f1r3node Rho machine (the R-2 composition fix: without installing the
    // σ-receiver program, the injection would reach no contract and OUT would be
    // empty — the vacuity trap the next assertion guards).
    let backend = PlannedRhoBackend::from_plan(plan);
    let report = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("σ injection must execute on the Rho runtime");

    // Non-vacuity: the σ-receiver fired exactly once and left one value on OUT.
    assert_eq!(
        report.observed_count(),
        1,
        "OUT must carry exactly one value — the σ-receiver must fire (got {:?})",
        report.values
    );

    // The milestone: the Rho machine reduced Swap(A, B) to the reflected normal
    // form Pair(B, A) — the RHS `Pair(b, a)` with σ = {a ↦ A, b ↦ B} applied.
    assert_eq!(
        report.values[0],
        expected_pair_b_a(),
        "OUT must carry Pair(B, A) — the reflected RHS with σ applied"
    );
}
