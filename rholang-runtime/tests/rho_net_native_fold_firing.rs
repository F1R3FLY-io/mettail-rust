//! Stage 3f end-to-end: a GENERATED integer calculator's NATIVE SCALAR FOLD fires end-to-end as a
//! COMM on the live f1r3node Rholang interpreter, emitting the reduced value the host computed.
//!
//! `NativeFoldDemo` is a generated `language!` whose only reducing rule is the native scalar
//! addition `AddInt(a, b) ~> a + b` (written `a "+" b` in the DSL, a `![a + b] fold` HOL term).
//! Unlike `^` (which has no in-Rho scalar contract, so the Rho scalar lowering REJECTS it and
//! classifies it as a `RhoNetRuleKind::NativeSystemProcess` — Stage 3e / `rho_net_native_firing`),
//! the `+` operator DOES lower to an in-Rho scalar contract, so it is classified as a
//! `RhoNetRuleKind::NativeFold` (the scalar-fold family, D2(f)). By the fold-vs-equation criterion
//! (D3, INV-9) a native COMPUTE is directed motion changing a CLTS barb, so the campaign fires it
//! as a COMM (a lossless iso coercion / `NormCast` would instead be compile-time congruence — see
//! the D3 codegen tests in `rholang-codegen`). The pipeline exercised here is the scalar-fold
//! analogue of the Stage 3e native SYSTEM PROCESS firing (`rho_net_native_firing.rs`) — the SAME
//! contractum lane:
//!
//!  1. [`NativeFoldDemoLanguage::dovetail_report_for`] saturates the redex `2 + 3`: the `Int_AddInt`
//!     native-fold rule fires and the host (Dovetail, model-b) matches `AddInt(2, 3)` AND computes
//!     the reduced value `5` via its trusted `fold` handler, so the sole `rewrite_justifications`
//!     entry is the `Int_AddInt` firing whose CONTRACTUM is the reduced value `5` (`NumLit(5)`);
//!  2. the generated [`NativeFoldDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection
//!     F-function (its native-fold arm — base | AC | contextual | subst | native | native-fold)
//!     reflects that contractum and assembles `c_add!(⟦NumLit(5)⟧, @OUT)` via `term_contract_call`,
//!     where `c_add` is the `AddInt` dispatch receiver's source channel (`sa:scalar/AddInt`);
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node RhoRuntime,
//!     where the installed `NativeFold` dispatch receiver (`for([result, out] <- c_add){
//!     out!(result) }`) forwards the delegated value on `@OUT` — one atomic COMM (INV-3).
//!
//! `2 + 3` reduces to `5`, and `2 + 3 ≠ 5` structurally, so a positive OUT observation is
//! non-vacuous evidence the native scalar fold fired as a COMM with the value the host computed
//! (the computation is host-side — model-b — exactly as the base/AC/contextual/binder/native arms,
//! and the firing itself runs on the reducer). The structural rendezvous (the COMM on `AddInt`'s
//! dedicated dispatch channel) is real; only the PAYLOAD is delegated to the trusted handler.
//!
//! FV: `formal/rocq/rho_bridge/theories/FoldMotionVsCongruence.v` (a computing fold changes a barb
//! ⇒ COMM, while a lossless iso preserves all barbs ⇒ congruence — the D3 boundary this fold sits
//! on the FIRING side of) + `NativeSystemProcessBoundary.v` (the native dispatch is total-or-reject,
//! and the emitted payload is exactly the trusted handler's value — the encoder delegates, never
//! fabricates) + the trust boundary `RhoHostObligationBoundary.v` + the inherited flat-receiver
//! correspondence (`LinearCommCorrespondence.v`) and install boundary (`RhoLoweringTotalOrRejects.v`).
#![cfg(feature = "native-fold-demo-runtime")]

// Task #11 (extended 2026-07-26): `NativeFoldDemo` is TEST-HOSTED — its definition lives in
// `languages/tests/definitions/nativefolddemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `nativefolddemo_generated_tests!` wrapper the expansion also
// defines is deliberately NOT invoked: this binary is a consumer, not the definition's
// designated host (`languages/tests/nativefolddemo.rs` is), so the generated suite stays
// single-instanced across the workspace.
#[path = "../../languages/tests/definitions/nativefolddemo.rs"]
mod nativefolddemo;

use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};
use nativefolddemo::NativeFoldDemoLanguage;

/// Reconstruct NativeFoldDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `AddInt` `NativeFold` dispatch
/// receiver installs; there are NO rejected rules — the `+` op lowers to an in-Rho scalar
/// contract), exactly as the Rho/Dovetail installer does. Returns the planned backend and the
/// plan's definition fingerprint (which must equal the generated metadata fingerprint the
/// native-fold injection reflects the contractum with).
fn native_fold_demo_backend() -> (PlannedRhoBackend, String) {
    let source = NativeFoldDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated NativeFoldDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("NativeFoldDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("NativeFoldDemo (AddInt native scalar fold) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The generated native-fold σ-injection fires the installed `AddInt` dispatch receiver as ONE
/// COMM, landing the host-computed reduced value `5` on OUT. This is the scalar-fold analogue of
/// `nativedemo_native_system_process_fires_as_a_comm_on_the_reducer` (native system process) and
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap` (base): INV-3, a native scalar
/// fold firing as a COMM on the reducer with a host-computed value.
#[tokio::test]
async fn nativefolddemo_native_scalar_fold_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = native_fold_demo_backend();

    // Fingerprint coherence: the installed `AddInt` dispatch receiver (from the reconstructed def)
    // and the native-fold σ-injection (which reflects the contractum with
    // `metadata().definition_fingerprint()`) must agree, or the forwarded value would decode
    // inconsistently.
    assert_eq!(
        NativeFoldDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete redex `2 + 3` = `AddInt(2, 3)`, parsed through the generated parser. `5 ≠ 2 + 3`
    // structurally, so a positive OUT observation is non-vacuous evidence the native fold fired.
    let term = NativeFoldDemoLanguage
        .parse_term("2 + 3")
        .expect("NativeFoldDemo must parse the native scalar redex 2 + 3");

    // (1) DOVETAIL REPORT SEMANTICS: the `Int_AddInt` native-fold rule fires and the host computes
    // the reduced value via its trusted `fold` handler, so the acyclic reduction is Complete with
    // EXACTLY the single `Int_AddInt` firing, whose CONTRACTUM is the reduced value `5`.
    let report = NativeFoldDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("NativeFoldDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic native-fold reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one native fold fires for 2 + 3, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(
        justification.rule_label, "Int_AddInt",
        "the fired rule is the AddInt native scalar fold (op-variant identity Int_AddInt)"
    );

    // The firing's contractum IS the host-computed reduced value `5` — the whole point of model-b:
    // the value is computed host-side by the trusted `fold` handler and handed to the σ-injection.
    let five = RuntimeReflectedSubterm {
        constructor: "NumLit(5)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        justification.contractum.as_ref(),
        Some(&five),
        "the AddInt firing's contractum is the reduced value 5 the trusted handler computed, got {:?}",
        justification.contractum
    );

    // (2) The generated σ-injection F-function (native-fold arm) reflects the contractum and
    // assembles `c_add!(⟦NumLit(5)⟧, @OUT)` for the `AddInt` dispatch receiver.
    let invocation =
        NativeFoldDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("NativeFoldDemo native-fold injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the receiver fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the native-fold injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed program (the `AddInt` dispatch receiver) ∥ call,
    // and observe OUT. The receiver binds the delivered value and forwards it on `@OUT` — one
    // atomic COMM (INV-3).
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the native-fold injection must execute on the Rho runtime");

    // Non-vacuity: the dispatch receiver fired exactly once and left exactly one value on OUT.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the native-fold dispatch receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE: the Rho machine landed the reduced value `5` (its reflected `NumLit(5)` image),
    // the native normal form, non-vacuous against the input `2 + 3`.
    let five_value = RuntimeObservationValue::Term {
        constructor: "NumLit(5)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], five_value,
        "the native scalar fold fired as a COMM on the reducer and landed the value 5"
    );
}

/// A-S3 ≥2-site native admission: `1 + 2 + 3` locates TWO `AddInt` sites (the nested redex and
/// the root), and the REPORT-FREE compile ADMITS them — the report path's single-native-firing
/// fail-close does not apply to the admitted path, because each located site's accept drives its
/// OWN contract call against the shared handler `Definition` (the bridges are identical
/// value-free forwarders, so no cross-talk is possible). Each site's machine-invoked handler
/// computes ITS OWN located σ's value — the nested `1 + 2 = 3` and the root
/// `(1 + 2) + 3 = 3 + 3 = 6` (the root's captured operand is the reflected SUBTREE, which the
/// ground evaluator folds recursively, exactly like the D-stage's recursive `try_eval`) — so OUT
/// collects BOTH values, mirroring the locate-all multi-firing semantics base rewrites already
/// have (and the same value multiset today's σ-replay deferral produces for this term).
#[tokio::test]
async fn a_s3_multi_site_native_exec_admits_and_fires_each_site() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = native_fold_demo_backend();

    let term = NativeFoldDemoLanguage
        .parse_term("1 + 2 + 3")
        .expect("NativeFoldDemo must parse the two-site native redex 1 + 2 + 3");

    // The REPORT-FREE compile ADMITS ≥2 located native sites (A-S3 lifts the deferral).
    mettail_rholang_codegen::clear_pending_native_handler_specs();
    let invocation = NativeFoldDemoLanguage::rho_net_match_invocation_to(term.as_ref(), "OUT")
        .expect("A-S3: the report-free match must ADMIT a ≥2-site native term");
    let specs = mettail_rholang_codegen::take_pending_native_handler_specs();
    assert_eq!(
        specs.len(),
        1,
        "both sites share ONE rule → ONE handler spec (the Definition serves every site)"
    );
    assert_eq!(specs[0].fired_rule_label, "Int_AddInt");

    let definitions = mettail_rholang_runtime::native_definitions_for(&specs)
        .expect("#36 S4/S5: the band allocation is pairwise distinct for a single language");
    let observation = backend
        .run_rho_net_with_call_definitions_and_observe_runtime_values(
            &invocation.call,
            definitions,
            &invocation.out_channel,
        )
        .await
        .expect("the ≥2-site admitted native call executes with the registered handler");

    assert_eq!(
        observation.observed_count(),
        2,
        "BOTH located sites fire their own machine-invoked handler (got {:?})",
        observation.values
    );
    let three = RuntimeObservationValue::Term {
        constructor: "NumLit(3)".to_string(),
        children: Vec::new(),
    };
    let six = RuntimeObservationValue::Term {
        constructor: "NumLit(6)".to_string(),
        children: Vec::new(),
    };
    assert!(
        observation.values.contains(&three) && observation.values.contains(&six),
        "the nested site computes 1 + 2 = 3 and the root site computes (1 + 2) + 3 = 6 \
         (recursive ground evaluation of the captured subtree), got {:?}",
        observation.values
    );
}
