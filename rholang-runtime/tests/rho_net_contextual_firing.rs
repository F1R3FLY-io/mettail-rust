//! Stage 3a end-to-end: a GENERATED language's UNARY CONGRUENCE (contextual) rewrite fires
//! end-to-end as an atomic JOIN COMM on the live f1r3node Rholang interpreter.
//!
//! `CtxDemo` is a generated `language!` whose congruence rewrite `WrapCong: | S ~> T |-
//! Wrap(S) ~> Wrap(T)` closes the context `Wrap(_)` around the inner premise `S ~> T`, whose
//! mechanism is the base rewrite `Flip: Swap(x, y) ~> Pair(y, x)`. The pipeline exercised here
//! is the CONTEXTUAL analogue of the base-rewrite σ-injection proven in `rho_net_equivalence.rs`
//! and the AC firing in `rho_net_ac_firing.rs`:
//!
//!  1. [`CtxDemoLanguage::dovetail_report_for`] saturates `Wrap(Swap(A, B))`: the inner premise
//!     `Flip` fires (`Swap(A, B) ~> Pair(B, A)`) and the e-graph congruence closure closes
//!     `Wrap(_)` IMPLICITLY — so the congruence rule `WrapCong` itself fires no explicit Dovetail
//!     rule, and the sole `rewrite_justifications` entry is the `Flip` premise firing (σ = {x ↦ A,
//!     y ↦ B});
//!  2. the generated [`CtxDemoLanguage::rho_net_contextual_invocation_from_dovetail_to`] F-function
//!     (the third arm of the σ-injection family — base | AC | contextual) reconstructs the reduced
//!     hole `T = RHS(Flip)[σ] = Pair(B, A)`, reflects it, and assembles
//!     `c_ctx!(⟦Pair(B, A)⟧, @OUT)` via `contextual_contract_call`, where `c_ctx` is `WrapCong`'s
//!     premise location channel;
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node RhoRuntime,
//!     where the installed contextual JOIN (`contextual_join_receiver_par`) binds the delivered
//!     reduced hole and emits `⟦Wrap(Pair(B, A))⟧` on `@OUT` — one atomic JOIN COMM (INV-6).
//!
//! `Wrap(Swap(A, B))` reduces to `Wrap(Pair(B, A))` (the reduced context), and
//! `Wrap(Swap(A, B)) ≠ Wrap(Pair(B, A))`, so a positive OUT observation is non-vacuous evidence
//! the contextual rewrite fired as a COMM with the σ Dovetail computed. The reduced hole is
//! host-reconstructed from the premise firing (model-b — matching host-side, exactly as the base
//! and AC arms), and the CONTEXTUAL JOIN itself fires on the reducer.
//!
//! FV: `formal/rocq/rho_bridge/theories/ContextualAtomicJoinPlugging.v` (INV-6 atomic n-ary join
//! + INV-2 plugging-stability, generalizing `LinearCommCorrespondence`'s `SameChannelJoin` 2→n).
#![cfg(feature = "ctx-demo-runtime")]

use std::collections::HashMap;
use std::sync::Arc;

use mettail_languages::ctxdemo::{CtxDemoLanguage, CtxDemoTerm, Proc};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct CtxDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `Flip` base σ-receiver AND the
/// `WrapCong` contextual join install alongside the structural constructors), exactly as the
/// Rho/Dovetail installer does. Returns the planned backend and the plan's definition
/// fingerprint (which must equal the generated metadata fingerprint the contextual injection
/// reflects σ with).
fn ctx_demo_backend() -> (PlannedRhoBackend, String) {
    let source = CtxDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated CtxDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("CtxDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("CtxDemo (unary congruence) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The concrete subject `Wrap(Swap(A, B))`, built through the generated typed AST (no parse —
/// sidesteps the keyword-`A`/`B` vs auto-`VarProc` ambiguity). `Wrap(Swap(A, B)) ≠
/// Wrap(Pair(B, A))`, so a positive OUT observation is non-vacuous evidence the contextual
/// rewrite fired.
fn subject() -> CtxDemoTerm {
    CtxDemoTerm(Proc::Wrap(Arc::new(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B)))))
}

fn nullary(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}

/// The generated CONTEXTUAL σ-injection fires the installed `WrapCong` atomic JOIN as ONE COMM,
/// landing `Wrap(Pair(B, A))` — the reduced context — on OUT. This is the contextual analogue of
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap` (base) and
/// `acdemo_ac_rewrite_fires_as_a_comm_on_the_reducer` (AC): INV-6, a contextual rewrite firing
/// as an atomic join on the reducer.
#[tokio::test]
async fn ctxdemo_contextual_rewrite_fires_as_a_join_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ctx_demo_backend();

    // Fingerprint coherence: the installed contextual join (from the reconstructed def) and the
    // contextual σ-injection (which reflects the reduced hole with `metadata().definition_
    // fingerprint()`) must agree, or the receiver's context tags and the hole's tags would
    // decode inconsistently.
    assert_eq!(
        CtxDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    let term = subject();

    // (1) DOVETAIL REPORT SEMANTICS: the inner premise `Flip: Swap(A, B) ~> Pair(B, A)` fires and
    // the e-graph congruence closure closes `Wrap(_)` implicitly, so the acyclic reduction is
    // Complete with EXACTLY the single Flip premise firing (WrapCong fires no explicit rule).
    let report = CtxDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("CtxDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic Wrap(Swap(A, B)) reduction reports Complete: {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one premise (Flip) fires for Wrap(Swap(A, B)); WrapCong closes by congruence, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "Flip", "the fired premise is the base rewrite Flip");
    let sigma: HashMap<&str, &RuntimeReflectedSubterm> = justification
        .sigma
        .iter()
        .map(|(name, subterm)| (name.as_str(), subterm))
        .collect();
    assert_eq!(sigma["x"].constructor, "A", "Flip bound the premise LHS variable x ↦ A");
    assert_eq!(sigma["y"].constructor, "B", "Flip bound the premise LHS variable y ↦ B");

    // (2) The generated CONTEXTUAL σ-injection F-function reconstructs the reduced hole
    // T = RHS(Flip)[σ] = Pair(σ[y], σ[x]) = Pair(B, A) and assembles c_ctx!(⟦Pair(B, A)⟧, @OUT)
    // for WrapCong's join (via `contextual_contract_call`).
    let invocation =
        CtxDemoLanguage::rho_net_contextual_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("CtxDemo contextual injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the join fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the contextual injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed program (Flip σ-receiver ∥ WrapCong contextual
    // join) ∥ call, and observe OUT. The join binds the delivered reduced hole and emits
    // ⟦Wrap(Pair(B, A))⟧ on @OUT — one atomic JOIN COMM (INV-6).
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the contextual injection must execute on the Rho runtime");

    // Non-vacuity: the contextual join fired exactly once (the only injection is on WrapCong's
    // premise channel; the Flip σ-receiver stays dormant with no injection on its trace channel).
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the contextual join must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE, checked against the firing's OWN σ: the reduced context the join landed is
    // Wrap(Pair(σ[y], σ[x])) = Wrap(Pair(B, A)), non-vacuous against the input Wrap(Swap(A, B)).
    let wrap_pair_b_a = RuntimeObservationValue::Term {
        constructor: "Wrap".to_string(),
        children: vec![RuntimeObservationValue::Term {
            constructor: "Pair".to_string(),
            children: vec![nullary("B"), nullary("A")],
        }],
    };
    assert_eq!(
        observation.values[0], wrap_pair_b_a,
        "the contextual join emitted the reduced context Wrap(Pair(B, A)) as a COMM on the reducer"
    );
}
