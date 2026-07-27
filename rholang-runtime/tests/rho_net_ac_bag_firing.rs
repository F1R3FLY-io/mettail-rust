//! Stage AC2b end-to-end: a GENERATED language's HashBag associative-commutative (AC) rewrite
//! whose RHS is ITSELF A NESTED BAG fires end-to-end as a COMM on the live f1r3node Rholang
//! interpreter, landing the TRANSFORMED BAG on OUT.
//!
//! `AcBagDemo` is a generated `language!` whose only rewrite is the linear with-rest HashBag AC
//! base rewrite `PPar{x, ...rest} ~> PPar{Mark(x), ...rest}` over nullary `A`/`B`/`C` — a
//! bag-TRANSFORMING rule (one fixed element marked, the residual `rest` carried). This is the
//! bag-VALUED-RHS analogue of `rho_net_ac_firing.rs` (whose RHS `Wrap(x)` is a plain term):
//!
//!  1. [`AcBagDemoLanguage::dovetail_report_for`] saturates the AC redex, resolving + bare-ifying
//!     each firing's σ — the matched element `x` and the residual `rest` (the canonical `PPar` node
//!     over the multiset complement); the AC gate populates `rewrite_justifications`.
//!  2. the generated `rho_net_invocation_from_dovetail_to` AC σ-injection RECONSTRUCTS the whole
//!     operand bag `[σ[x]] ⊎ σ[rest].children`, reflects it to the process-soup carrier, and
//!     assembles `c_ac!(⟦bag⟧, @out)` via `ac_contract_call` (byte-identical to the plain-RHS path
//!     — only the installed receiver's BODY differs);
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node RhoRuntime,
//!     where the installed AC receiver (`ac_sigma_receiver_par`) matches the soup ORDER-
//!     INDEPENDENTLY inside one atomic `consume` and fires the bag-soup RHS
//!     `⟦PPar{Mark(x), ...rest}⟧σ` = `@"ac:PPar"!(⟦Mark(picked)⟧) | rest` on `@out` — the `rest`
//!     σ-slot splices the residual sends (the flat transformed bag), which `decode_ac_bag_soup`
//!     reads back as a `Bag`.
//!
//! The AC matcher picks ONE element to mark, so `OUT = PPar{Mark(e), <the rest>}` for some `e` in
//! the operand bag. A positive OUT observation of the transformed bag — the fixed element marked,
//! the rest intact — is non-vacuous evidence a bag-RHS AC rule fired as a COMM.

use std::collections::HashMap;

// Task #11 (extended 2026-07-26): `AcBagDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/acbagdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `acbagdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/acbagdemo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/acbagdemo.rs"]
mod acbagdemo;

use acbagdemo::{AcBagDemoLanguage, AcBagDemoTerm, AcBagDemoTermInner, Proc};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{
    Language, RuntimeObservationValue, RuntimeReflectedSubterm, RuntimeRewriteJustification,
};

/// Reconstruct AcBagDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the AC receiver installs alongside the
/// structural constructors), exactly as the Rho/Dovetail installer does. Returns the planned
/// backend and the plan's definition fingerprint (which must equal the generated metadata
/// fingerprint the AC injection reflects σ with).
fn ac_bag_demo_backend() -> (PlannedRhoBackend, String) {
    let source = AcBagDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated AcBagDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("AcBagDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("AcBagDemo (HashBag bag-transforming AC rewrite) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The concrete subject `PPar{A | B | C}`, built through the generated typed AST (no parse).
fn subject_bag() -> AcBagDemoTerm {
    let bag = mettail_runtime::HashBag::from_iter([Proc::A, Proc::B, Proc::C]);
    AcBagDemoTerm(AcBagDemoTermInner::Proc(Proc::PPar(bag)))
}

/// The elements of the whole operand bag a firing reconstructs: `[σ[x]] ⊎ σ[rest].children`.
/// This is EXACTLY what the generated AC injection reflects onto the AC channel, so the transformed
/// OUT bag must be this multiset with ONE element marked.
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

/// Assert `value` is the TRANSFORMED bag `PPar{Mark(e), <the rest>}`: a multiset over the operand
/// `bag_elements` in which EXACTLY ONE element `e` is marked in `Mark(_)` and every other operand
/// element is carried intact (bare), each with multiplicity 1. Returns the marked element `e`.
///
/// This is the bag-RHS `⟦PPar{Mark(x), ...rest}⟧σ` under the receiver's per-firing element pick:
/// the fixed element `x` transformed to `Mark(x)`, the residual `rest` spliced back flat.
fn assert_transformed_bag(value: &RuntimeObservationValue, bag_elements: &[String]) -> String {
    let RuntimeObservationValue::Bag(entries) = value else {
        panic!("OUT must be the transformed bag (a multiset carrier), got {value:?}");
    };
    let total: usize = entries.iter().map(|(_, count)| *count).sum();
    assert_eq!(
        total,
        bag_elements.len(),
        "the transformed bag has the operand bag's cardinality, got {value:?}"
    );

    let mut marked: Option<String> = None;
    let mut bare: Vec<String> = Vec::new();
    for (element, count) in entries {
        assert_eq!(*count, 1, "each transformed-bag element has multiplicity 1, got {value:?}");
        match element {
            RuntimeObservationValue::Term { constructor, children } if constructor == "Mark" => {
                assert_eq!(children.len(), 1, "Mark is unary, got {value:?}");
                match &children[0] {
                    RuntimeObservationValue::Term {
                        constructor: inner,
                        children: grandchildren,
                    } if grandchildren.is_empty() => {
                        assert!(
                            marked.replace(inner.clone()).is_none(),
                            "exactly one element is marked, got {value:?}"
                        );
                    },
                    other => panic!("the marked element is nullary, got Mark({other:?})"),
                }
            },
            RuntimeObservationValue::Term { constructor, children } if children.is_empty() => {
                bare.push(constructor.clone());
            },
            other => {
                panic!(
                    "a transformed-bag element is a bare constructor or Mark(bare), got {other:?}"
                )
            },
        }
    }

    let marked = marked.expect("the transformed bag marks exactly one element");
    assert!(
        bag_elements.contains(&marked),
        "the marked element {marked} is an element of the operand bag {bag_elements:?}"
    );
    // The rest is intact: (bare elements) ⊎ {marked} == the operand bag, as multisets.
    let mut reconstructed = bare;
    reconstructed.push(marked.clone());
    reconstructed.sort();
    let mut expected = bag_elements.to_vec();
    expected.sort();
    assert_eq!(
        reconstructed, expected,
        "the fixed element is marked and the rest carried intact: {value:?}"
    );
    marked
}

/// The single-firing bag-RHS AC σ-injection fires the installed AC receiver as ONE COMM, landing
/// the TRANSFORMED BAG `PPar{Mark(e), <the rest>}` on OUT — where `e` is one element of the whole
/// operand bag the firing's σ reconstructs. This is the bag-VALUED-RHS analogue of
/// `acdemo_ac_rewrite_fires_as_a_comm_on_the_reducer` and the direct prerequisite shape for
/// Rholang's `Comm` rule (whose RHS `PPar{P[Q/y], ...rest}` is likewise a bag).
#[tokio::test]
async fn acbagdemo_bag_rhs_ac_rewrite_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ac_bag_demo_backend();

    // Fingerprint coherence: the installed AC receiver (from the reconstructed def) and the AC
    // σ-injection (which reflects the bag carrier with `metadata().definition_fingerprint()`) must
    // agree, or the receiver could not recognize the reflected soup.
    assert_eq!(
        AcBagDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    let term = subject_bag();

    // (1) DOVETAIL REPORT SEMANTICS: the AC redex saturates acyclically (Complete), and the AC
    // gate populates the firing σ provenance the injection reads. The Dovetail engine instantiates
    // the `AcApp` RHS (`instantiate` → `add_flattened_bag`), so the report's contractum is the
    // flat transformed bag; the injection nonetheless reconstructs the OPERAND bag and lets the
    // installed receiver produce the RHS.
    let report = AcBagDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcBagDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic AC reduction reports Complete: {:?}",
        report.completeness
    );
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the bag-transforming AC rewrite must surface at least one firing justification"
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(
        justification.rule_label, "AcBagStep",
        "the fired rule is the bag-transforming AC rewrite AcBagStep"
    );
    let bag_elements = reconstructed_bag_elements(justification);

    // (2) The generated AC σ-injection F-function reconstructs the whole operand bag from σ and
    // assembles `c_ac!(⟦bag⟧, @OUT)` via `ac_contract_call`.
    let invocation = AcBagDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect("AcBagDemo AC σ-injection must assemble from a complete report");
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
        .expect("the bag-RHS AC injection must execute on the Rho runtime");

    // Non-vacuity: the AC receiver fired exactly once (one atomic consume of one carrier value),
    // landing ONE transformed bag on OUT.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the transformed bag (got {:?})",
        observation.values
    );

    // EQUIVALENCE, checked against the firing's OWN σ: OUT is the transformed bag `PPar{Mark(e),
    // <the rest>}` where the operand bag is `[σ[x]] ⊎ σ[rest].children` the injection sent.
    let picked = assert_transformed_bag(&observation.values[0], &bag_elements);
    assert!(
        matches!(picked.as_str(), "A" | "B" | "C"),
        "the AC receiver marked a concrete bag element, got {picked}"
    );
}

/// S-AC (Stage 4, AC2) — the DECISIVE probe that the operand bag AND its residual `rest` are
/// re-sourced from the SPREAD of the reflected subject, NOT the host report σ, for a bag-VALUED RHS.
/// The `rest`/bag-RHS analogue of `s_ac_bag_is_produced_by_the_spread_not_the_report` (AC1).
///
/// The bag RHS `PPar{Mark(x), ...rest}` carries the residual `rest` through: the transformed OUT bag
/// is `{Mark(e)} ⊎ rest`, so a WRONG `rest` would corrupt the OUT bag's non-marked elements (and its
/// cardinality). We take a real, complete report for `PPar{A | B | C}` and CORRUPT its σ — both the
/// matched element `x` AND the residual `rest` (the SAME σ the host-σ AC arm reconstructs
/// `whole_bag = [σ[x]] ⊎ σ[rest].children` from) — to nonsense, leaving the rule label (`AcBagStep`)
/// valid so the gate admits the MATCH path. The Stage-4 `rho_net_match_invocation_from_dovetail_to`
/// re-sources the WHOLE bag from the SPREAD of the subject; the co-installed `ac_sigma_receiver_par`
/// picks one element to mark and binds `rest` to the residual SPREAD soup (`ac_bag_pattern`'s
/// remainder), and the bag-RHS `⟦PPar{Mark(x), ...rest}⟧σ` splices `Mark(picked) | rest` flat
/// (`add_flattened_bag` byte-identity, reused verbatim from the installed receiver).
///
/// Because BOTH the marked element and the residual `rest` come from `term`, not the corrupted σ,
/// OUT is `PPar{Mark(e), <the real rest>}` over `{A, B, C}` — never a `Z_NONSENSE` element and never
/// the wrong cardinality. A host-σ AC arm would have reconstructed the bag (and hence `rest`) from
/// the nonsense σ. So a correct transformed-bag OUT is non-vacuous evidence the bag AND its `rest`
/// came from the spread, not the report.
///
/// FV: `InRhoAcMatchMultiset.v` (located bag = subject operand bag) + `AcRestReconstruction.v`
/// (`rest` = the residual complement; the RHS flatten reproduces `add_flattened_bag`).
#[tokio::test]
async fn s_ac_rest_and_bag_rhs_are_produced_by_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ac_bag_demo_backend();

    let term = subject_bag();

    let mut report = AcBagDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcBagDemo Dovetail report must compile");
    assert_eq!(
        report
            .rewrite_justifications
            .first()
            .map(|j| j.rule_label.as_str()),
        Some("AcBagStep"),
        "the bag-transforming AC rewrite AcBagStep is the first firing"
    );

    // Deliberately WRONG σ on EVERY firing (the saturation also surfaces `MarkIdem` normalizations,
    // whose σ is equally irrelevant to the MATCH path): a report-σ AC arm would reconstruct the
    // operand bag AND its `rest` from these and land a nonsense transformed bag. The rule labels
    // (the location-independent identities) stay valid so the in-Rho match gate admits the path;
    // ONLY the σ (the bag + rest source) is corrupted.
    let nonsense = RuntimeReflectedSubterm {
        constructor: "Z_NONSENSE".to_string(),
        children: Vec::new(),
    };
    let nonsense_rest = RuntimeReflectedSubterm {
        constructor: "PPar".to_string(),
        children: vec![nonsense.clone(), nonsense.clone()],
    };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("x".to_string(), nonsense.clone()), ("rest".to_string(), nonsense_rest.clone())];
    }

    // The MATCH path admits the AC redex despite the corrupted σ, and re-sources the whole bag (and
    // its `rest`) from the reflected subject `term`.
    let invocation =
        AcBagDemoLanguage::rho_net_match_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the MATCH path admits PPar{A|B|C} with a corrupted report σ");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho bag-RHS AC match + firing executes on the reducer");

    // Non-vacuity: the co-installed AC receiver fired exactly once, landing ONE transformed bag.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the transformed bag (got {:?})",
        observation.values
    );

    // OUT is the transformed bag `PPar{Mark(e), <the real rest>}` over the REAL universe {A,B,C} —
    // never `Z_NONSENSE` and never the wrong cardinality. `assert_transformed_bag` panics if the
    // marked element or the residual `rest` is outside the universe or the cardinality differs, so a
    // σ-sourced (corrupted) bag/rest would fail here.
    let universe: Vec<String> = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let picked = assert_transformed_bag(&observation.values[0], &universe);
    assert!(
        matches!(picked.as_str(), "A" | "B" | "C"),
        "the bag AND its rest were re-sourced from the spread (not the corrupted σ), marked {picked}"
    );
}
