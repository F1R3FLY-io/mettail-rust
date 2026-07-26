//! End-to-end Rho-default backend planning for the REAL `GuardedRho` language
//! under the LIVE guard-quality wiring (`mettail_rholang_codegen::guard_quality`).
//!
//! `GuardedRho` is the project's guarded smoke-test language: its
//! `guards { channels { channel Name; join PGuardedInput(ch: Name); } }` block
//! plus the `?guard:Guard` slot on `PGuardedInput` induce four guard
//! obligations. This test reconstructs the exact augmented `LanguageDef` from
//! the generated `definition_source()` (the same path the production installer
//! uses), supplies exact rejected-rule and guard coverage, and proves the
//! language plans end-to-end with every substrate quality non-`Unknown` — so the
//! fail-closed `RhoFlipBlocker::GuardQuality` gate (doc-08: "`Unknown` quality ⇒
//! production-default refused") never fires for a real, fully-covered guarded
//! language. The behavioral-predicate legs are recorded as `RejectSafeApprox`
//! (the M7 mixed-guard / Heyting reject-safe case), not `Unknown`.

// Task #11 (extended 2026-07-26): the `guarded-rho` LIBRARY FEATURE is gone (the definition
// is test-hosted now), so naming it in this gate would make the gate unsatisfiable and
// SILENTLY delete the whole Rho-default-backend suite. Only the `rho-codegen` half remains a
// real condition; the definition itself is `#[path]`-included unconditionally below.
#![cfg(feature = "rho-codegen")]

// Task #11 (extended 2026-07-26): `GuardedRho` is a PROTOTYPE grammar whose definition lives in
// `languages/tests/definitions/guarded_rho.rs`, not in the `languages` library, so it is
// `#[path]`-included here. This binary is a CONSUMER, not the definition's designated host
// (`languages/tests/guarded_rho_tests.rs` is), so it deliberately does NOT invoke the
// `guardedrho_generated_tests!` wrapper — the generated suite stays single-instanced.
#[path = "definitions/guarded_rho.rs"]
mod guardedrho;

use guardedrho::GuardedRhoLanguage;
use mettail_rholang_codegen::guard_quality::{derive_guard_qualities, RhoGuardQuality};
use mettail_rholang_codegen::{
    audit_rho_default_backend, collect_guard_obligations, lower_language_def,
    plan_rho_default_backend, reconstruct_language_def, suggest_rejected_rule_dispositions,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    RhoGuardDisposition, RhoGuardDispositionKind, RhoGuardObligationKind,
    RhoRejectedRuleDisposition,
};
use mettail_runtime::Language;

/// Reconstruct the REAL `GuardedRho` augmented `LanguageDef` from the generated
/// metadata's `definition_source()` (the macro-time def, composition +
/// auto-injection), exactly as the Rho/Dovetail installer does for Calculator.
fn guarded_rho_def() -> mettail_ast::language::LanguageDef {
    let source = GuardedRhoLanguage
        .metadata()
        .definition_source()
        .expect("generated GuardedRhoLanguage must expose its definition_source");
    reconstruct_language_def(source)
        .expect("GuardedRhoLanguage definition_source must reconstruct as a LanguageDef")
}

/// Exactly-once Rho-machine dispositions for every rule the scalar lowering
/// rejects. GuardedRho is structural, so the production classifier supplies
/// the verified Rho AST/native-process boundary each rejected constructor needs.
fn rho_machine_rejected_rule_dispositions(
    def: &mettail_ast::language::LanguageDef,
) -> Vec<RhoRejectedRuleDisposition> {
    let lowering = lower_language_def(def);
    let dispositions = suggest_rejected_rule_dispositions(def, &lowering);
    assert_eq!(
        dispositions.len(),
        lowering.rejected.len(),
        "GuardedRho must have one Rho-machine disposition per rejected scalar-lowering rule"
    );
    dispositions
}

/// Gate-compatible dispositions that exactly cover GuardedRho's four guard
/// obligations: the two Rho-native-join surfaces via `RhoNativeJoin`, and the
/// two behavioral-predicate legs via an effective Boolean algebra.
fn guard_dispositions() -> Vec<RhoGuardDisposition> {
    vec![
        RhoGuardDisposition::new("channel:Name", RhoGuardDispositionKind::RhoNativeJoin),
        RhoGuardDisposition::new("join:PGuardedInput", RhoGuardDispositionKind::RhoNativeJoin),
        RhoGuardDisposition::new(
            "predicate:standard-builtins",
            RhoGuardDispositionKind::EffectiveBooleanAlgebra,
        ),
        RhoGuardDisposition::new(
            "term:PGuardedInput:guard:guard",
            RhoGuardDispositionKind::EffectiveBooleanAlgebra,
        ),
    ]
}

#[test]
fn guarded_rho_induces_guard_obligations_with_non_unknown_qualities() {
    let def = guarded_rho_def();
    let obligations = collect_guard_obligations(&def);

    // GuardedRho genuinely induces guard obligations (it is a guarded language).
    assert!(
        !obligations.is_empty(),
        "GuardedRho must induce guard obligations from its channels/join/guard slots"
    );
    assert!(
        obligations
            .iter()
            .any(|o| o.kind == RhoGuardObligationKind::RhoNativeJoin),
        "GuardedRho's channel/join block induces RhoNativeJoin obligations"
    );
    assert!(
        obligations
            .iter()
            .any(|o| o.kind == RhoGuardObligationKind::BehavioralPredicate),
        "GuardedRho's ?guard slot induces a behavioral-predicate obligation"
    );

    // Every substrate-derived quality is usable (non-Unknown), and the
    // behavioral leg lands on the reject-safe quality (never Unknown).
    let qualities = derive_guard_qualities(&def);
    assert_eq!(
        qualities.len(),
        obligations.len(),
        "the substrate emits one quality per induced obligation"
    );
    assert!(
        qualities
            .iter()
            .all(|q| !q.quality.refuses_production_default()),
        "no GuardedRho guard obligation may classify to Unknown (fail-closed quality)"
    );
    assert!(
        qualities
            .iter()
            .any(|q| q.quality == RhoGuardQuality::RejectSafeApprox),
        "GuardedRho's behavioral-predicate legs are reject-safe, not Unknown"
    );
}

#[test]
fn guarded_rho_plans_end_to_end_with_all_qualities_non_unknown() {
    let def = guarded_rho_def();

    // Without external coverage the audit must block (guard obligations are
    // uncovered) — the gate is genuinely engaged for this language.
    let audit = audit_rho_default_backend(&def);
    assert!(
        !audit.can_plan_without_external_coverage(),
        "GuardedRho's guard obligations require explicit coverage evidence"
    );

    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(
            rho_machine_rejected_rule_dispositions(&def),
        ),
        guard_coverage: RhoGuardCoverageEvidence::CoveredGuardObligations(guard_dispositions()),
    };

    let plan = plan_rho_default_backend(&def, requirements)
        .expect("fully-covered GuardedRho must pass the Rho-default flip gate end-to-end");

    assert_eq!(plan.language_name(), "GuardedRho");
    assert_eq!(plan.guard_obligation_dispositions.len(), 4);

    // The plan carries one substrate quality per guard obligation, all
    // non-Unknown ⇒ no fail-closed `RhoFlipBlocker::GuardQuality` fired.
    let qualities = plan.guard_obligation_qualities();
    assert_eq!(qualities.len(), 4, "plan must carry a quality tag per guard obligation");
    assert!(
        qualities
            .iter()
            .all(|q| !q.quality.refuses_production_default()),
        "a flipped GuardedRho plan must carry no production-default-refusing (Unknown) quality"
    );

    let quality_for = |obligation: &str| -> RhoGuardQuality {
        qualities
            .iter()
            .find(|q| q.obligation == obligation)
            .unwrap_or_else(|| panic!("plan must carry a quality for {obligation}"))
            .quality
    };
    assert_eq!(quality_for("channel:Name"), RhoGuardQuality::RuntimeObservation);
    assert_eq!(quality_for("join:PGuardedInput"), RhoGuardQuality::RuntimeObservation);
    assert_eq!(quality_for("predicate:standard-builtins"), RhoGuardQuality::RejectSafeApprox);
    assert_eq!(quality_for("term:PGuardedInput:guard:guard"), RhoGuardQuality::RejectSafeApprox);
}
