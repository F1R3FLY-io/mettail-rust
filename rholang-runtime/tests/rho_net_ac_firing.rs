//! Stage AC-U3 end-to-end: a GENERATED language's HashBag associative-commutative (AC) rewrite
//! fires end-to-end as a COMM on the live f1r3node Rholang interpreter.
//!
//! `AcDemo` is a generated `language!` whose only rewrite is the linear with-rest HashBag AC base
//! rewrite `PPar{x, ...rest} ~> Wrap(x)` over nullary `A`/`B`/`C`. The pipeline exercised here is
//! the AC analogue of the base-rewrite σ-injection proven in `rho_net_equivalence.rs`:
//!
//!  1. [`AcDemoLanguage::dovetail_report_for`] saturates the AC redex, resolving + bare-ifying
//!     each firing's σ — the matched element `x` and the residual `rest` (the canonical `PPar`
//!     node over the multiset complement); the report producer's AC gate populates
//!     `rewrite_justifications` (Stage AC-U3, the `rho_net_ac_injection_sites` gate).
//!  2. the generated `rho_net_invocation_from_dovetail_to{,_firing}` / `_replay_` F-function reads
//!     a firing, RECONSTRUCTS the whole operand bag `[σ[x]] ⊎ σ[rest].children`, reflects it to the
//!     process-soup carrier, and assembles `c_ac!(⟦bag⟧, @out)` via `ac_contract_call`;
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node RhoRuntime,
//!     where the installed AC receiver (`ac_sigma_receiver_par`) matches the soup ORDER-
//!     INDEPENDENTLY (native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders)
//!     inside one atomic `consume` and
//!     fires `Wrap(element)` on `@out`.
//!
//! The AC matcher picks ONE element of the bag, so `OUT = Wrap(e)` for some `e` in the operand bag
//! (`RHS[σ]` up to the receiver's re-pick). A positive OUT observation is non-vacuous evidence the
//! AC rule fired as a COMM with the σ Dovetail computed.

use std::collections::HashMap;

// Task #11 (extended 2026-07-26): `AcDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/acdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `acdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/acdemo_ac_firing_report.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/acdemo.rs"]
mod acdemo;

use acdemo::{AcDemoLanguage, AcDemoTerm, AcDemoTermInner, Proc};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract,
    build_rho_net_replay_invocation_from_contracts, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{
    Language, RuntimeObservationValue, RuntimeReflectedSubterm, RuntimeRewriteJustification,
};

/// Reconstruct AcDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the AC receiver installs alongside the
/// structural constructors), exactly as the Rho/Dovetail installer does. Returns the planned
/// backend and the plan's definition fingerprint (which must equal the generated metadata
/// fingerprint the AC injection reflects σ with).
fn ac_demo_backend() -> (PlannedRhoBackend, String) {
    let source = AcDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated AcDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("AcDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("AcDemo (HashBag AC rewrite) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The concrete subject `PPar{A | B | C}`, built through the generated typed AST (no parse —
/// sidesteps the keyword-`A`/`B`/`C` vs auto-`VarProc` ambiguity the linter reports).
fn subject_bag() -> AcDemoTerm {
    let bag = mettail_runtime::HashBag::from_iter([Proc::A, Proc::B, Proc::C]);
    AcDemoTerm(AcDemoTermInner::Proc(Proc::PPar(bag)))
}

/// The elements of the whole operand bag a firing reconstructs: `[σ[x]] ⊎ σ[rest].children`.
/// This is EXACTLY what the generated AC injection reflects onto the AC channel, so `OUT` must
/// wrap one of these.
fn reconstructed_bag_elements(justification: &RuntimeRewriteJustification) -> Vec<String> {
    let sigma: HashMap<&str, &RuntimeReflectedSubterm> = justification
        .sigma
        .iter()
        .map(|(name, subterm)| (name.as_str(), subterm))
        .collect();
    let x = sigma
        .get("x")
        .expect("the AC firing binds the element variable x");
    let rest = sigma
        .get("rest")
        .expect("the AC firing binds the residual variable rest");
    let mut elements = Vec::with_capacity(1 + rest.children.len());
    elements.push(x.constructor.clone());
    elements.extend(rest.children.iter().map(|child| child.constructor.clone()));
    elements
}

/// Assert `value` is `Wrap(e)` where `e` is a nullary constructor drawn from `bag_elements`, and
/// return the wrapped element. This is the AC RHS `Wrap(σ[picked])` where the receiver picked one
/// element of the operand bag.
fn assert_wraps_a_bag_element(value: &RuntimeObservationValue, bag_elements: &[String]) -> String {
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
                    assert!(
                        bag_elements.contains(elem),
                        "OUT must wrap an element of the reconstructed bag {bag_elements:?}, got Wrap({elem})"
                    );
                    elem.clone()
                },
                other => panic!("expected Wrap(nullary constructor), got Wrap({other:?})"),
            }
        },
        other => panic!("expected Wrap(...), got {other:?}"),
    }
}

/// The single-firing AC σ-injection fires the installed AC receiver as ONE COMM, landing
/// `Wrap(element)` on OUT — where `element` is one of the whole operand bag the firing's σ
/// reconstructs. This is the AC analogue of
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap`.
#[tokio::test]
async fn acdemo_ac_rewrite_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ac_demo_backend();

    // Fingerprint coherence: the installed AC receiver (from the reconstructed def) and the AC
    // σ-injection (which reflects the bag carrier with `metadata().definition_fingerprint()`)
    // must agree, or the receiver could not recognize the reflected soup.
    assert_eq!(
        AcDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    let term = subject_bag();

    // (1) DOVETAIL REPORT SEMANTICS: the AC redex saturates acyclically (Complete), and the AC
    // gate populates the firing σ provenance the injection reads.
    let report = AcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic AC reduction reports Complete: {:?}",
        report.completeness
    );
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the AC rewrite must surface at least one firing justification"
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "AcStep", "the fired rule is the AC rewrite AcStep");
    let bag_elements = reconstructed_bag_elements(justification);

    // (2) The generated AC σ-injection F-function reconstructs the whole bag from σ and assembles
    // `c_ac!(⟦bag⟧, @OUT)` via `ac_contract_call`.
    let invocation = AcDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect("AcDemo AC σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the AC rule fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the AC injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed AC receiver program ∥ call and observe OUT.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the AC injection must execute on the Rho runtime");

    // Non-vacuity: the AC receiver fired exactly once (one atomic consume of one carrier value).
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the AC receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE, checked against the firing's OWN σ: the AC receiver landed `Wrap(picked)` where
    // `picked` is an element of the operand bag `[σ[x]] ⊎ σ[rest].children` the injection sent.
    let picked = assert_wraps_a_bag_element(&observation.values[0], &bag_elements);
    assert!(
        matches!(picked.as_str(), "A" | "B" | "C"),
        "the AC receiver wrapped a concrete bag element, got {picked}"
    );
}

/// The multi-firing replay drives EVERY AC firing the report enumerates as its own atomic COMM
/// (host `collect_ac_matches` enumerates ALL AC matches; the persistent receiver re-fires per
/// firing). Each lands `Wrap(element)` on its own out channel. The AC analogue of
/// `generated_replay_wiring_fires_every_firing_as_a_comm`.
#[tokio::test]
async fn acdemo_ac_replay_fires_every_ac_match_as_a_comm() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ac_demo_backend();

    let term = subject_bag();
    let report = AcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcDemo multi-match Dovetail report must compile");

    // Every AC firing's reconstructed bag elements (the universe OUT_i may wrap), by firing index.
    let per_firing_bags: Vec<Vec<String>> = report
        .rewrite_justifications
        .iter()
        .map(reconstructed_bag_elements)
        .collect();

    // Generated wiring: one AC injection per firing (distinct out channel), then the replay bridge.
    let injections =
        AcDemoLanguage::rho_net_replay_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the generated replay method must build one AC injection per firing");
    assert_eq!(
        injections.len(),
        report.rewrite_justifications.len(),
        "one AC injection per firing"
    );
    assert!(!injections.is_empty(), "the AC redex must fire at least once");

    let firings = match build_rho_net_replay_invocation_from_contracts(injections) {
        RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings } => firings,
        other => panic!("the replay bridge must map to RunRhoNetReplay…, got {other:?}"),
    };

    let observation = backend
        .run_rho_net_replay_and_observe_runtime_values(&firings)
        .await
        .expect("the generated AC replay wiring must execute on the Rho runtime");

    // Every firing fired as a COMM: one observation per firing.
    assert_eq!(
        observation.observed_count(),
        per_firing_bags.len(),
        "every AC firing fires as its own COMM (got {:?})",
        observation.values
    );

    // Every observed value is `Wrap(e)` for a concrete bag element `e ∈ {A, B, C}` — the AC RHS
    // under the receiver's per-firing pick. (The values arrive in nondeterministic order across
    // the parallel out channels, so this is a set-level assertion.)
    let universe: Vec<String> = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    for value in &observation.values {
        assert_wraps_a_bag_element(value, &universe);
    }
}

/// S-AC (Stage 4, AC1) — the DECISIVE probe that the AC operand BAG is re-sourced from the SPREAD
/// of the reflected subject, NOT the host report σ. The AC analogue of the base
/// `m_reflect_sigma_is_produced_by_the_automaton_not_the_report` and the native
/// `s_native_location_is_produced_by_the_automaton_not_the_report`.
///
/// We take a real, complete report for `PPar{A | B | C}` and CORRUPT its σ (the matched element `x`
/// and the residual `rest` — the SAME σ the host-σ AC arm reconstructs `whole_bag = [σ[x]] ⊎
/// σ[rest].children` from) to nonsense, leaving the rule label (`AcStep`) valid so the in-Rho match
/// GATE still admits the path. The Stage-4 `rho_net_match_invocation_from_dovetail_to` STRUCTURALLY
/// reflects the WHOLE subject `PPar{A | B | C}` (M-reflect, NOT the report σ); the match driver
/// (`ac_match_call_par`) LOCATES that bag, publishes its process-soup carrier on the SITE-KEYED
/// `ac:` channel from the SUBJECT's ground elements, and the co-installed `ac_sigma_receiver_par`
/// picks ONE element + binds `rest` ON the reducer (one atomic native `sub_pars` consume) and fires
/// `Wrap(x)`.
///
/// Because the operand bag — and hence the picked element — is built from `term`, not the corrupted
/// σ, OUT is `Wrap(e)` for a REAL element `e ∈ {A, B, C}`. A host-σ AC arm would have reconstructed
/// the bag from the nonsense σ and wrapped `Z_NONSENSE`. So a positive, correct OUT is non-vacuous
/// evidence the bag came from the spread of the subject, not the report — AC matching is a genuine
/// in-Rho replacement (the σ-replay duplicate matcher is retired), and the site-keyed carrier
/// eliminates cross-bag intermingle. The AC firing carries NO host-supplied residue (unlike
/// S-native): the whole match AND fire is in Rho.
///
/// FV: `InRhoAcMatchMultiset.v` (the located bag = the subject operand bag; the carrier-agnostic
/// atomic k-of-n pick) + `AcRestReconstruction.v` (`rest` = the residual soup) +
/// `AcAtomicNoPartialConsume.v` (one atomic consume, no partial commit).
#[tokio::test]
async fn s_ac_bag_is_produced_by_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ac_demo_backend();

    let term = subject_bag();

    let mut report = AcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcDemo Dovetail report must compile");
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the AC rewrite must surface at least one firing justification"
    );

    // Deliberately WRONG σ: a report-σ AC arm would reconstruct the operand bag from these bindings
    // and wrap `Z_NONSENSE`. The rule label (`AcStep` — the location-independent identity) stays
    // valid so the in-Rho match gate admits the path; ONLY the σ (the bag source) is corrupted.
    let nonsense = RuntimeReflectedSubterm {
        constructor: "Z_NONSENSE".to_string(),
        children: Vec::new(),
    };
    let nonsense_rest = RuntimeReflectedSubterm {
        constructor: "PPar".to_string(),
        children: vec![nonsense.clone(), nonsense.clone()],
    };
    for justification in &mut report.rewrite_justifications {
        assert_eq!(
            justification.rule_label, "AcStep",
            "the fired rule label (the location-independent identity) stays valid"
        );
        justification.sigma =
            vec![("x".to_string(), nonsense.clone()), ("rest".to_string(), nonsense_rest.clone())];
    }

    // The MATCH path admits the AC redex despite the corrupted σ, and RE-SOURCES the operand bag
    // from the reflected subject `term` (the spread), never the report σ.
    let invocation =
        AcDemoLanguage::rho_net_match_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the MATCH path admits PPar{A|B|C} with a corrupted report σ");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho AC match + firing executes on the reducer");

    // Non-vacuity: the co-installed AC receiver fired exactly once (one atomic consume of one bag).
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the located AC redex must fire (got {:?})",
        observation.values
    );

    // The AC receiver wrapped a REAL bag element `e ∈ {A, B, C}` from the SPREAD subject — never the
    // corrupted σ's `Z_NONSENSE`. `assert_wraps_a_bag_element` panics if OUT wraps anything outside
    // the universe, so a nonsense-sourced bag would fail here.
    let universe: Vec<String> = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let picked = assert_wraps_a_bag_element(&observation.values[0], &universe);
    assert!(
        matches!(picked.as_str(), "A" | "B" | "C"),
        "the AC bag was re-sourced from the spread (not the corrupted report σ), got Wrap({picked})"
    );
}
