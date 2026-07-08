//! Stage 3e end-to-end: a GENERATED integer calculator's NATIVE SYSTEM PROCESS fires end-to-end
//! as a COMM on the live f1r3node Rholang interpreter, emitting the value a TRUSTED native handler
//! computed.
//!
//! `NativeDemo` is a generated `language!` whose only reducing rule is the native exponentiation
//! `PowInt(a, b) ~> a^b` (written `a "^" b` in the DSL, a `![a.pow(b as u32)] fold` HOL term). The
//! `^` operator has no in-Rho scalar contract, so the Rho scalar lowering REJECTS it and classifies
//! it as a `RhoNetRuleKind::NativeSystemProcess` (the native-dispatch family, D2(e)) — its value is
//! computed by the host's TRUSTED native handler (the Dovetail `fold` body), not by an in-Rho
//! scalar contract. The pipeline exercised here is the NATIVE-DISPATCH analogue of the base-rewrite
//! σ-injection (`rho_net_equivalence.rs`), the AC firing (`rho_net_ac_firing.rs`), the contextual
//! join (`rho_net_contextual_firing.rs`), and the binder/β-substitution (`rho_net_beta_firing.rs`):
//!
//!  1. [`NativeDemoLanguage::dovetail_report_for`] saturates the redex `2 ^ 3`: the `Int_PowInt`
//!     native rule fires and the host (Dovetail, model-b) matches `PowInt(2, 3)` AND computes the
//!     native value `8` via its trusted `fold` handler, so the sole `rewrite_justifications` entry
//!     is the `Int_PowInt` firing whose CONTRACTUM is the reduced value `8` (`NumLit(8)`);
//!  2. the generated [`NativeDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection
//!     F-function (its native arm — base | AC | contextual | subst | native) reflects that
//!     contractum and assembles `c_pow!(⟦NumLit(8)⟧, @OUT)` via `term_contract_call`, where `c_pow`
//!     is the `PowInt` dispatch receiver's source channel;
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node
//!     RhoRuntime, where the installed `NativeSystemProcessRewrite` dispatch receiver
//!     (`for([result, out] <- c_pow){ out!(result) }`) forwards the delegated value on `@OUT` —
//!     one atomic COMM (INV-3).
//!
//! `2 ^ 3` reduces to `8`, and `2 ^ 3 ≠ 8` structurally, so a positive OUT observation is
//! non-vacuous evidence the native system process fired as a COMM with the value the trusted
//! handler computed (the computation is host-side — model-b — exactly as the base/AC/contextual/
//! binder arms, and the firing itself runs on the reducer). The structural rendezvous (the COMM on
//! `PowInt`'s dedicated dispatch channel) is real; only the PAYLOAD is delegated to the handler.
//!
//! FV: `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v` (the native dispatch is
//! total-or-reject, and the emitted payload is exactly the trusted handler's value — the encoder
//! delegates, never fabricates) + the trust boundary `RhoHostObligationBoundary.v` + the inherited
//! flat-receiver correspondence (`LinearCommCorrespondence.v`) and install boundary
//! (`RhoLoweringTotalOrRejects.v`).
#![cfg(feature = "native-demo-runtime")]

use mettail_languages::nativedemo::NativeDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct NativeDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `PowInt`
/// `NativeSystemProcessRewrite` dispatch receiver installs, its rejected native disposition
/// covered), exactly as the Rho/Dovetail installer does. Returns the planned backend and the
/// plan's definition fingerprint (which must equal the generated metadata fingerprint the native
/// injection reflects the contractum with).
fn native_demo_backend() -> (PlannedRhoBackend, String) {
    let source = NativeDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated NativeDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("NativeDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("NativeDemo (PowInt native system process) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The generated native σ-injection fires the installed `PowInt` dispatch receiver as ONE COMM,
/// landing the trusted handler's value `8` on OUT. This is the NATIVE-DISPATCH analogue of
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap` (base) and
/// `lambdademo_beta_reduction_fires_as_a_comm_on_the_reducer` (binder): INV-3, a native system
/// process firing as a COMM on the reducer with a host-computed native value.
#[tokio::test]
async fn nativedemo_native_system_process_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = native_demo_backend();

    // Fingerprint coherence: the installed `PowInt` dispatch receiver (from the reconstructed def)
    // and the native σ-injection (which reflects the contractum with
    // `metadata().definition_fingerprint()`) must agree, or the forwarded value would decode
    // inconsistently.
    assert_eq!(
        NativeDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete redex `2 ^ 3` = `PowInt(2, 3)`, parsed through the generated parser. `8 ≠ 2^3`
    // structurally, so a positive OUT observation is non-vacuous evidence the native process fired.
    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    // (1) DOVETAIL REPORT SEMANTICS: the `Int_PowInt` native rule fires and the host computes the
    // native value via its trusted `fold` handler, so the acyclic reduction is Complete with
    // EXACTLY the single `Int_PowInt` firing, whose CONTRACTUM is the reduced value `8`.
    let report = NativeDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("NativeDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic native reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one native firing fires for 2 ^ 3, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(
        justification.rule_label, "Int_PowInt",
        "the fired rule is the PowInt native process (op-variant identity Int_PowInt)"
    );

    // The firing's contractum IS the host-computed native value `8` — the whole point of model-b:
    // the value is computed host-side by the TRUSTED native handler and handed to the σ-injection.
    let eight = RuntimeReflectedSubterm { constructor: "NumLit(8)".to_string(), children: Vec::new() };
    assert_eq!(
        justification.contractum.as_ref(),
        Some(&eight),
        "the PowInt firing's contractum is the reduced value 8 the trusted handler computed, got {:?}",
        justification.contractum
    );

    // (2) The generated σ-injection F-function (native arm) reflects the contractum and assembles
    // `c_pow!(⟦NumLit(8)⟧, @OUT)` for the `PowInt` dispatch receiver.
    let invocation =
        NativeDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("NativeDemo native injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the receiver fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the native injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed program (the `PowInt` dispatch receiver) ∥ call,
    // and observe OUT. The receiver binds the delivered value and forwards it on `@OUT` — one
    // atomic COMM (INV-3).
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the native injection must execute on the Rho runtime");

    // Non-vacuity: the dispatch receiver fired exactly once and left exactly one value on OUT.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the native dispatch receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE: the Rho machine landed the reduced value `8` (its reflected `NumLit(8)` image),
    // the native normal form, non-vacuous against the input `2 ^ 3`.
    let eight_value = RuntimeObservationValue::Term {
        constructor: "NumLit(8)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], eight_value,
        "the native system process fired as a COMM on the reducer and landed the value 8"
    );
}
