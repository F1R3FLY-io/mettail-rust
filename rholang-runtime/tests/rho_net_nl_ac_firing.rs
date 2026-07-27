//! Stage 4 S-AC (AC3) end-to-end: a GENERATED language's NON-LINEAR HashBag associative-commutative
//! (AC) rewrite `PPar{x, x, ...rest} ~> Wrap(x)` matches + fires IN RHO from the SPREAD of the
//! reflected subject — the repeated bare element var `x` carrying the `Receive.condition`
//! consistency guard `EEq(slot0, slot1)`.
//!
//! `NlAcDemo` is the non-linear analogue of `AcDemo`: its only rewrite requires TWO EQUAL elements
//! of the operand bag (the `N ≡ N` shape a repeated bare var expresses), binds `rest`, and emits
//! `Wrap(x)` for the shared element `x` — so, unlike the structured Ambient/Comm rules whose reducts
//! are host-computed, the WHOLE match AND fire is in Rho: the co-installed
//! `ac_sigma_receiver_par_with_condition` picks two equal elements under the guard and produces the
//! RHS referencing the bound `x`.
//!
//! The subject `{A | A | B}` has a UNIQUE non-linear match — only `A` occurs twice, so `x = A`,
//! `rest = {B}`, and OUT is `Wrap(A)` deterministically. This is the AC3 slice's decisive evidence:
//! the guarded, non-linear pick happens on the reducer, over the subject spread (not the report σ).

// Task #11 (extended 2026-07-26): `NlAcDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/nlacdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `nlacdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/nlacdemo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/nlacdemo.rs"]
mod nlacdemo;

use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};
use nlacdemo::{NlAcDemoLanguage, NlAcDemoTerm, NlAcDemoTermInner, Proc};

/// Reconstruct NlAcDemo's augmented `LanguageDef` from the generated metadata's `definition_source()`
/// and plan its Rho-default backend (the non-linear AC receiver installs alongside the structural
/// constructors). Returns the planned backend and the plan's definition fingerprint.
fn nl_ac_demo_backend() -> (PlannedRhoBackend, String) {
    let source = NlAcDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated NlAcDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("NlAcDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("NlAcDemo (non-linear HashBag AC rewrite) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The concrete subject `PPar{A | A | B}` — two `A`s (multiplicity 2) and one `B` — built through
/// the generated typed AST. The non-linear `{x, x, ...rest}` LHS matches ONLY `x = A` (the sole
/// element with multiplicity ≥ 2), `rest = {B}`.
fn subject_bag() -> NlAcDemoTerm {
    let bag = mettail_runtime::HashBag::from_iter([Proc::A, Proc::A, Proc::B]);
    NlAcDemoTerm(NlAcDemoTermInner::Proc(Proc::PPar(bag)))
}

/// Assert `value` is `Wrap(A)` — the unique non-linear match's RHS.
fn assert_wraps_a(value: &RuntimeObservationValue) {
    match value {
        RuntimeObservationValue::Term { constructor, children } => {
            assert_eq!(constructor, "Wrap", "the AC RHS is Wrap(element), got {value:?}");
            assert_eq!(children.len(), 1, "Wrap is unary, got {value:?}");
            match &children[0] {
                RuntimeObservationValue::Term {
                    constructor: elem,
                    children: grandchildren,
                } => {
                    assert!(
                        grandchildren.is_empty(),
                        "the wrapped element is nullary, got {value:?}"
                    );
                    assert_eq!(
                        elem, "A",
                        "the UNIQUE non-linear match is x = A (the only element with multiplicity ≥ 2)"
                    );
                },
                other => panic!("expected Wrap(nullary constructor), got Wrap({other:?})"),
            }
        },
        other => panic!("expected Wrap(...), got {other:?}"),
    }
}

/// The non-linear AC rewrite fires as ONE COMM on the reducer: the guarded receiver picks the two
/// `A`s (the `EEq(slot0, slot1)` consistency guard holds only for the equal pair), binds `rest = {B}`,
/// and lands `Wrap(A)` on OUT.
#[tokio::test]
async fn nlacdemo_nonlinear_ac_rewrite_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = nl_ac_demo_backend();

    let term = subject_bag();
    let report = NlAcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("NlAcDemo Dovetail report must compile");
    assert!(report.is_complete(), "the acyclic non-linear AC reduction reports Complete");
    assert!(
        report
            .rewrite_justifications
            .iter()
            .any(|j| j.rule_label == "NlAcStep"),
        "the non-linear AC rewrite NlAcStep must surface a firing justification"
    );

    let invocation =
        NlAcDemoLanguage::rho_net_match_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the in-Rho MATCH path admits the non-linear AC redex");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho non-linear AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the guarded non-linear pick fires once (got {:?})",
        observation.values
    );
    assert_wraps_a(&observation.values[0]);
}

/// S-AC (Stage 4, AC3) — the DECISIVE probe that the NON-LINEAR AC match happens IN RHO over the
/// SPREAD of the subject (not the report σ) AND the consistency guard is enforced on the reducer.
/// The non-linear analogue of `s_ac_bag_is_produced_by_the_spread_not_the_report`.
///
/// We corrupt the report σ to nonsense, leaving the rule label (`NlAcStep`) valid so the gate admits
/// the match path. The match driver re-sources the operand bag `{A, A, B}` from the reflected
/// subject, and the co-installed guarded receiver picks the two `A`s (the `EEq` guard holds only for
/// the equal pair — a mismatched pair like `{A, B}` would be rejected by the condition ON the
/// reducer) and fires `Wrap(A)`. A host-σ matcher would have used the nonsense σ. So a correct
/// `Wrap(A)` is non-vacuous evidence the non-linear match ran in Rho over the subject, not the report.
///
/// FV: `InRhoAcMatchMultiset.v` (located bag = subject operand bag) + `AcNonLinearConsistency.v`
/// (the repeated-var occurrences bind name-equal — the guard is sound + complete for the non-linear
/// selection).
#[tokio::test]
async fn s_ac_nonlinear_guard_fires_in_rho_from_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = nl_ac_demo_backend();

    let term = subject_bag();
    let mut report = NlAcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("NlAcDemo Dovetail report must compile");
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the non-linear AC rewrite must surface at least one firing justification"
    );

    // Deliberately WRONG σ on every firing: the match path must not read it. The rule labels stay
    // valid so the in-Rho match gate admits the path.
    let nonsense = RuntimeReflectedSubterm {
        constructor: "Z_NONSENSE".to_string(),
        children: Vec::new(),
    };
    let nonsense_rest = RuntimeReflectedSubterm {
        constructor: "PPar".to_string(),
        children: vec![nonsense.clone()],
    };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("x".to_string(), nonsense.clone()), ("rest".to_string(), nonsense_rest.clone())];
    }

    let invocation =
        NlAcDemoLanguage::rho_net_match_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the MATCH path admits the non-linear AC redex with a corrupted report σ");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho non-linear AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the guarded pick fires once (got {:?})",
        observation.values
    );
    // `Wrap(A)`, from the SPREAD subject under the reducer-enforced guard — never the corrupted σ's
    // `Z_NONSENSE`, and never a mismatched pair (the `EEq` guard rejects those).
    assert_wraps_a(&observation.values[0]);
}
